import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0050
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0012
import Development.WeilBound.CoreStatements.FlagImmersions.ArithmeticIntersectionDivisorSupport
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0033
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0011
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenFibreExists
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0008
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0097

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.AmpleGenericFibreOfCombination
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt.Ample

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem coneTangent {P : Ideal (MRing J)} {e : ℕ}
    {τ : (Fin e → ℂ) → (Σ k, J k) → ℂ} {y : Fin e → ℂ} (hτ : DifferentiableAt ℂ τ y)
    (hm : ∀ᶠ y' in 𝓝 y, τ y' ∈ mcPts P) (w : Fin e → ℂ) :
    IsConeTangent (Int.castRingHom ℂ) P (τ y) (fderiv ℂ τ y w) := by
  intro f hf
  set F := MvPolynomial.map (Int.castRingHom ℂ) f
  have h0 : (fun y' => MvPolynomial.eval (τ y') F) =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hm] with y' hy'
    exact hy'.2 f hf
  have hD := (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_hasFDerivAt_eval F (τ y)).comp y hτ.hasFDerivAt
  have hD0 : HasFDerivAt (fun y' => MvPolynomial.eval (τ y') F) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq h0
  have h1 := congrArg (fun L => L w) (hD.unique hD0)
  simpa [smul_eq_mul, mul_comm] using h1

theorem maDensity_one (f : (Fin 1 → ℂ) → ℝ) (y : Fin 1 → ℂ) :
    maDensity (fun _ : Fin 1 => f) y = 2 / Real.pi * levi f y (Pi.single 0 1) := by
  have hU : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  have hne : (∅ : Finset (Fin 1)) ≠ {0} := by decide
  have key : (cxHessian f y 0 0).re = levi f y (Pi.single 0 1) := by
    simp only [cxHessian, levi]
    generalize fderiv ℝ (fderiv ℝ f) y = H
    generalize H (Pi.single 0 1) (Pi.single 0 1) + H (Complex.I • Pi.single 0 1) (Complex.I • Pi.single 0 1) = u
    simp
  have hm : mixedDisc (fun _ : Fin 1 => cxHessian f y) = cxHessian f y 0 0 := by
    unfold mixedDisc
    rw [hU, Finset.sum_pair hne]
    simp [Matrix.det_unique]
  unfold maDensity
  rw [hm, key]
  simp

theorem geomDeg_nonneg {P W : Ideal (MRing J)} {N : HermLine J} (hN : IsSemipositiveH P N) (hW : P ≤ W) :
    0 ≤ geomDeg W N 1 := by
  classical
  unfold geomDeg ptsIntegral
  split_ifs with hΨ
  · refine MeasureTheory.integral_nonneg fun y => finsum_nonneg fun w => finsum_nonneg fun _ => ?_
    unfold sheetDensity
    split_ifs with hg
    · have hev := hg.choose_spec.2
      set gm := hg.choose
      have hP : ∀ᶠ y' in 𝓝 y, gm y' ∈ mcPts P := hev.mono fun y' h => ⟨h.2.1.1, fun f hf => h.2.1.2 f (hW hf)⟩
      have hz := hP.self_of_nhds
      have han : AnalyticAt ℂ gm y :=
        GroundTheory.Heights₂.Heights.Inter.analyticAt_of_eventually_differentiableAt (hev.mono fun _ h => h.1)
      have hlog : ContDiffAt ℝ 2 (fun z => Real.log (N.h z)) (gm y) :=
        ((hN.1.contDiffAt (StokesStep.isOpen_multicone.mem_nhds hz.1)).of_le
          (WithTop.coe_le_coe.2 le_top)).log (N.pos _ hz.1).ne'
      have h1 := ReciprocityTheory.AnForm.levi_comp (Pi.single 0 1) han hlog
      have h2 := hN.2 _ hz _ (coneTangent han.differentiableAt hP (Pi.single 0 1))
      have h3 := maDensity_one ((fun z => Real.log (N.h z)) ∘ gm) y
      rw [h1] at h3
      rw [_root_.one_mul]
      exact le_of_le_of_eq (mul_nonneg (by positivity) h2) h3.symm
    · exact le_rfl
  · exact le_rfl

end LevelTowerAlt.Ample

theorem LevelTowerAlt.ample_generic_fibre_of_combination : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (N A : HermLine J) (a' : K → ℤ) (m p : ℕ), IsSemipositiveH P N → IsSmoothHerm A → (∀ k, 0 < a' k) → 1 ≤ m → 1 ≤ p → (m : ℤ) • A.a = N.a + (p : ℤ) • a' → AmpleOnGenericFibre P A := by
  intro hI II hII K _ J _ P N A a' m p hN hA ha' hm hp heq W d hd hW hPW
  classical
  have hK : Nonempty K := hW.1
  have hDG := GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system ⟨II, hII⟩)
  have hF := GroundTheory.Heights₂.Heights.NumbersDVR.IntNumIsFieldIntersection.full ℚ K J
  have hPos := GroundTheory.Heights₂.Heights.Targets.Positivity.full ℚ J _ hF
  let fs : (K → ℤ) → HermLine J := fun b => HermLine.ofMetrics (fun k => fsMetric (J k)) b
  have hfs : ∀ b, IsSmoothHerm (fs b) := fun b => GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs b
  have hfsn : ∀ b : K → ℤ, (∀ k, 0 ≤ b k) → ∀ W', IsArithVar W' 2 → 0 ≤ geomDeg W' (fs b) 1 := by
    intro b hb W' hW'
    have h1 := hDG K J W' 1 (fun _ => fs b) hW' fun _ => hfs b
    have h2 := (hPos _ 1 (GroundTheory.Heights₂.Heights.HilbertSamuel.isProjVarF_map_of_isArithVar hW')).1
      (fun _ => b) fun _ k => hb k
    show 0 ≤ ptsIntegral W' (pot fun _ : Fin 1 => fs b) (fun _ => 1)
    rw [h1]
    exact_mod_cast h2
  let ℓ : Fin 3 → HermLine J := ![N, fs ((p : ℤ) • a' - 1), fs 1]
  have hℓ : ∀ j, IsSmoothHerm (ℓ j) := fun j => by
    fin_cases j
    · exact hN.1
    · exact hfs _
    · exact hfs _
  have hnef : ∀ j W', IsArithVar W' 2 → W ≤ W' → 0 ≤ geomDeg W' (ℓ j) 1 := fun j W' h1 h2 => by
    fin_cases j
    · exact LevelTowerAlt.Ample.geomDeg_nonneg hN (hPW.trans h2)
    · refine hfsn _ (fun k => ?_) W' h1
      have h3 := ha' k
      have h4 : (1 : ℤ) ≤ p := by exact_mod_cast hp
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply]
      nlinarith
    · exact hfsn _ (fun _ => zero_le_one) W' h1
  have e1 := (GlobalTheory.T.log_integral_multilinear II hII K J W d (Fin 3) ℓ (fun _ _ => 1) hW hℓ).1
  have e2 := (GlobalTheory.T.log_integral_multilinear II hII K J W d Unit (fun _ => A) (fun _ _ => (m : ℤ)) hW fun _ => hA).1
  have e3 := (GlobalTheory.T.log_integral_multilinear II hII K J W d Unit (fun _ => A) (fun _ _ => (m : ℤ)) hW fun _ => hA).2
    (fun _ => Top.combLine ℓ fun _ => 1) (fun _ => Top.combLine (fun _ : Unit => A) fun _ => (m : ℤ)) (Equiv.refl _)
    (fun _ => (GlobalTheory.T.hermitian_combination_smooth_conj K J _ ℓ _).1 hℓ) (fun _ => (GlobalTheory.T.hermitian_combination_smooth_conj K J _ _ _).1 fun _ => hA) fun _ => by
      show ∑ _ : Unit, (m : ℤ) • A.a = ∑ j, (1 : ℤ) • (ℓ j).a
      rw [Fin.sum_univ_three]
      simp only [Finset.univ_unique, Finset.sum_singleton, one_smul, heq]
      show _ = N.a + ((p : ℤ) • a' - 1) + 1
      abel
  rw [e1, e2] at e3
  have hpos : 0 < ∑ w : Fin d → Fin 3, (∏ k : Fin d, ((1 : ℤ) : ℝ)) *
      ptsIntegral W (fun k z => Real.log ((ℓ (w k)).h z)) (fun _ => 1) := by
    simp only [Int.cast_one, Finset.prod_const_one, _root_.one_mul]
    refine Finset.sum_pos' (fun w _ => ?_) ⟨fun _ => 2, Finset.mem_univ _, ?_⟩
    · exact GlobalTheory.T.ptsIntegral_log_nonneg hI.kleimanNefF (fun K _ J _ => (PB.Known.fieldNumbers ℚ K J).1) PB.Known.divSuppArith II hII K J W d (fun k => ℓ (w k)) hW
        (fun k => hℓ _) fun k => hnef _
    · have h1 := hDG K J W d (fun _ => fs 1) hW fun _ => hfs _
      have h2 := (hPos _ d (GroundTheory.Heights₂.Heights.HilbertSamuel.isProjVarF_map_of_isArithVar hW)).2
      show 0 < ptsIntegral W (pot fun _ : Fin d => fs 1) (fun _ => 1)
      rw [h1]
      exact_mod_cast h2
  rw [← e3, Fintype.sum_unique] at hpos
  have hc : (0 : ℝ) ≤ ∏ k : Fin d, ((m : ℤ) : ℝ) := Finset.prod_nonneg fun _ _ => by positivity
  exact (pos_iff_pos_of_mul_pos hpos).1 (lt_of_le_of_ne hc fun h => by
    rw [← h, zero_mul] at hpos
    exact lt_irrefl _ hpos)
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.DeterminantLatticeGradedTensor
section
open AlgebraicGeometry CategoryTheory Matrix
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

namespace N1

section

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem gen_ratio {Λ : Lat ξ Ω} {p : Cpt ξ} {s t : Ω} (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) :
    s / t ∈ regAt ξ p := by
  have : s ∈ Submodule.span (regAt ξ p) {t} := by rw [← ht.2, hs.2]; exact Submodule.mem_span_singleton_self s
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
  have : s / t = a := by rw [← ha, div_eq_iff ht.1]; rfl
  rw [this]; exact a.2

theorem tens_gen {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} (a : I → ℤ) {p : Cpt ξ} {s : I → Ω}
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) : (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  have h0 : ∏ i, s i ^ a i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hs i).1
  refine ⟨h0, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2
    (Set.singleton_subset_iff.2 (Submodule.subset_span ⟨s, hs, rfl⟩)))⟩
  rintro _ ⟨s', hs', rfl⟩
  have hm : ∏ i, (s' i / s i) ^ a i ∈ regAt ξ p := by
    refine prod_mem fun i _ => ?_
    rcases Int.eq_nat_or_neg (a i) with ⟨n, h | h⟩
    · rw [h, zpow_natCast]; exact pow_mem (gen_ratio (hs' i) (hs i)) n
    · rw [h, _root_.zpow_neg, ← _root_.inv_zpow, inv_div, zpow_natCast]; exact pow_mem (gen_ratio (hs i) (hs' i)) n
  refine Submodule.mem_span_singleton.2 ⟨⟨_, hm⟩, ?_⟩
  show (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i = _
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [← mul_zpow, div_mul_cancel₀ _ (hs i).1]

end

end N1

open N1

theorem determinant_lattice_graded_tensor : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (b₀ : Fin r → V), LinearIndependent Ω b₀ → L.IsFlagVBOn Set.univ b₀ → detLat L b₀ = Lat.tens (fun i => L.gr b₀ i) (fun _ => 1) := by
  intro X Ω _ ξ V _ _ L r b₀ h₀ hL
  funext p
  obtain ⟨U, hU, b, hfl, hb⟩ := hL p trivial
  replace hb := hb p trivial hU
  have hmem : ∀ k : Fin r, ∃ c : Fin r → Ω, (∀ k', k < k' → c k' = 0) ∧ b k = ∑ k', c k' • b₀ k' := by
    intro k
    have h1 : b k ∈ flagStep Ω b₀ (k + 1) := by
      rw [← hfl]; exact Submodule.subset_span ⟨k, Nat.lt_succ_self _, rfl⟩
    obtain ⟨c, hc, e⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).1 h1
    refine ⟨c, fun k' h => (Finsupp.mem_supported' Ω c).1 hc k' (by simp only [Set.mem_ofPred_eq, not_lt]; exact h), ?_⟩
    rw [← e, Finsupp.linearCombination_apply]
    exact Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)
  choose c hc0 hc using hmem
  let T : Matrix (Fin r) (Fin r) Ω := Matrix.of fun k' k => c k k'
  have hT : T.BlockTriangular id := fun k' k h => hc0 k k' h
  have h1 := determinant_lattice_generator X Ω ξ V L r b₀ b T p h₀ hb hc
  have h2 : ∀ i, (L.gr b₀ i).IsGenAt p (T i i) := fun i => by
    refine FlagGrGen.gr_isGenAt X Ω ξ V L r b₀ b p i _ h₀ hfl hb ?_
    rw [hc i, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    show c i i • b₀ i + _ - c i i • b₀ i ∈ _
    rw [add_sub_cancel_left]
    refine Submodule.sum_mem _ fun k' hk' => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hk') with h | h
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k', h, rfl⟩)
    · rw [hc0 i k' h, zero_smul]; exact Submodule.zero_mem _
  have h3 := tens_gen (Λ := fun i => L.gr b₀ i) (fun _ => 1) h2
  rw [h1.2, h3.2, Matrix.det_of_isUpperTriangular hT]
  simp

end LevelTowerAlt
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.PhiTransport
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section
namespace LevelTowerAlt.Val

theorem phi_transport {E : Type} [Field E] [NumberField E] {V V' A : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [Fintype A] (ρ : 𝓞 E →+* Module.End ℂ V) (ρ' : 𝓞 E →+* Module.End ℂ V')
    (Ψ : V ≃ₗ[ℂ] V') (hρ : ∀ a x, ρ' a (Ψ x) = Ψ (ρ a x)) (hb : V → V → ℂ) (hb' : V' → V' → ℂ) (κ : ℝ)
    (hh : ∀ x x', hb x x' = κ * hb' (Ψ x) (Ψ x')) (I : AddSubgroup V) (I' : AddSubgroup V')
    (hI : I' = I.map Ψ.toLinearMap.toAddMonoidHom) (σ : A → (𝓞 E →+* ℂ)) {m : ℕ} (b : A → Fin m → V)
    (b' : A → Fin m → V') (c : ℂ) (hc : c ≠ 0) (hbb : ∀ τ j, Ψ (b τ j) = c • b' τ j) (ν : ℝ)
    (h : PhiNormSq ρ hb I κ σ b ν) :
    ∃ ν', PhiNormSq ρ' hb' I' 1 σ b' ν' ∧ ν = (κ * ‖c‖ ^ 2) ^ (m * Fintype.card A) * ν' := by
  subst hI
  have heig : ∀ (s₀ : 𝓞 E →+* ℂ) (x : V),
      Ψ (GlobalTheory.CompanionTheory.Ar.Cusp.eigComp ρ s₀ x) = GlobalTheory.CompanionTheory.Ar.Cusp.eigComp ρ' s₀ (Ψ x) := by
    intro s₀ x
    obtain ⟨c₀, hc₀⟩ := GlobalTheory.T.exists_eigenComponent_polynomial E s₀
    rw [(hc₀ V ρ).1 x, (hc₀ V' ρ').1 (Ψ x), map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, hρ]
  have hmem : ∀ (s₀ : 𝓞 E →+* ℂ) (x : V), x ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ s₀ →
      Ψ x ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ' s₀ := by
    intro s₀ x hx
    unfold GlobalTheory.CompanionTheory.Ar.eigSp at hx ⊢
    rw [Submodule.mem_iInf] at hx ⊢
    intro a
    have hx' := hx a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx'
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hρ,
      ← map_smul Ψ, ← map_sub Ψ, hx', map_zero Ψ]
  have hspan : ∀ {r : ℕ} (v : Fin r → V), GlobalTheory.CompanionTheory.Ar.Cusp.oSpan ρ' (fun i => Ψ (v i)) =
      (GlobalTheory.CompanionTheory.Ar.Cusp.oSpan ρ v).map Ψ.toLinearMap.toAddMonoidHom := by
    intro r v
    unfold GlobalTheory.CompanionTheory.Ar.Cusp.oSpan
    rw [AddMonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨a, i, rfl⟩
      exact ⟨ρ a (v i), ⟨a, i, rfl⟩, (hρ a (v i)).symm⟩
    · rintro ⟨y, ⟨a, i, rfl⟩, rfl⟩
      exact ⟨a, i, (hρ a (v i)).symm⟩
  obtain ⟨r, k, hrk, v, q, T, hint, hq, hT, hdet, hν⟩ := h
  refine ⟨_, ⟨r, k, hrk, fun i => Ψ (v i), fun τ j => Ψ (q τ j), fun τ => c • T τ, ?_, ?_, ?_, ?_,
    rfl⟩, ?_⟩
  · obtain ⟨hvI, hind, hidx⟩ := hint
    refine ⟨fun i => AddSubgroup.mem_map_of_mem _ (hvI i), fun a ha => hind a ?_, ?_⟩
    · apply Ψ.injective
      rw [map_sum, map_zero]
      simp only [← hρ]
      exact ha
    · rw [hspan v, AddSubgroup.relIndex_map_map_of_injective (f := Ψ.toLinearMap.toAddMonoidHom)
        _ _ Ψ.injective]
      exact hidx
  · exact fun τ j => hmem _ _ (hq τ j)
  · intro τ i
    have h1 : Fin.append (fun a => GlobalTheory.CompanionTheory.Ar.Cusp.eigComp ρ' (σ τ) (Ψ (v a))) (fun j => Ψ (q τ j)) i =
        Ψ (Fin.append (fun a => GlobalTheory.CompanionTheory.Ar.Cusp.eigComp ρ (σ τ) (v a)) (q τ) i) := by
      refine Fin.addCases (fun l => ?_) (fun l => ?_) i
      · rw [Fin.append_left, Fin.append_left, heig]
      · rw [Fin.append_right, Fin.append_right]
    refine h1.trans ?_
    rw [hT τ i, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hbb, smul_smul]
    congr 1
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  · intro τ
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hc) (hdet τ)
  · have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    have hmat : ∀ τ, (Matrix.of fun i j => hb (q τ i) (q τ j)) =
        (κ : ℂ) • Matrix.of (fun i j => hb' (Ψ (q τ i)) (Ψ (q τ j))) := by
      intro τ
      ext i j
      rw [Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply, hh, smul_eq_mul]
    rw [hν, hspan v, AddSubgroup.relIndex_map_map_of_injective
      (f := Ψ.toLinearMap.toAddMonoidHom) _ _ Ψ.injective, pow_mul, ← Finset.card_univ,
      ← Finset.prod_const, mul_left_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hY : ‖(T τ).det‖ ≠ 0 := norm_ne_zero_iff.mpr (hdet τ)
    rw [hmat τ]
    simp only [Matrix.det_smul, Fintype.card_fin]
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, norm_mul, norm_pow]
    have hκ : κ ^ r * κ ^ k = κ ^ m := by rw [← pow_add, hrk]
    rw [← mul_assoc, hκ]
    field_simp
    ring

theorem herm_unique {g : ℕ} (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ) (h₁ : H₁.IsHermitian) (h₂ : H₂.IsHermitian)
    (S N : Set (Fin g → ℂ)) (hS : ∀ x ∈ S, ∀ y ∈ S, (x ⬝ᵥ H₁ *ᵥ star y).im = (x ⬝ᵥ H₂ *ᵥ star y).im)
    (n₁ : ∀ y ∈ N, H₁ *ᵥ star y = 0) (n₂ : ∀ y ∈ N, H₂ *ᵥ star y = 0)
    (hall : ∀ p, ∃ r ∈ Submodule.span ℝ S, p - r ∈ N) : H₁ = H₂ := by
  set D := H₁ - H₂ with hD
  have hDh : D.IsHermitian := h₁.sub h₂
  have hS' : ∀ x ∈ S, ∀ y ∈ S, (x ⬝ᵥ D *ᵥ star y).im = 0 := by
    intro x hx y hy
    rw [hD, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_im, hS x hx y hy, sub_self]
  have hN : ∀ y ∈ N, D *ᵥ star y = 0 := by
    intro y hy
    rw [hD, Matrix.sub_mulVec, n₁ y hy, n₂ y hy, sub_zero]
  have hNl : ∀ x ∈ N, ∀ q, x ⬝ᵥ D *ᵥ star q = 0 := by
    intro x hx q
    have hx0 : x ᵥ* D = 0 := by
      have h := congrArg star (hN x hx)
      rwa [Matrix.star_mulVec, star_star, hDh.eq, star_zero] at h
    rw [Matrix.dotProduct_mulVec, hx0, zero_dotProduct]
  have hspan : ∀ x ∈ Submodule.span ℝ S, ∀ y ∈ Submodule.span ℝ S,
      (x ⬝ᵥ D *ᵥ star y).im = 0 := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      induction hx using Submodule.span_induction with
      | mem x hx' => exact hS' x hx' y hy'
      | zero => simp
      | add x x' _ _ h h' => rw [add_dotProduct, Complex.add_im, h, h', add_zero]
      | smul a x _ h => rw [smul_dotProduct, Complex.smul_im, h, smul_zero]
    | zero => simp
    | add y y' _ _ h h' =>
      rw [star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im, h, h', add_zero]
    | smul a y _ h =>
      rw [star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im, h,
        smul_zero]
  have hall' : ∀ p q : Fin g → ℂ, (p ⬝ᵥ D *ᵥ star q).im = 0 := by
    intro p q
    obtain ⟨r, hr, hpr⟩ := hall p
    obtain ⟨r', hr', hqr⟩ := hall q
    rw [show p = r + (p - r) by abel, add_dotProduct, hNl _ hpr, add_zero,
      show q = r' + (q - r') by abel, star_add, Matrix.mulVec_add, hN _ hqr, add_zero]
    exact hspan r hr r' hr'
  have hzero : ∀ p q : Fin g → ℂ, p ⬝ᵥ D *ᵥ star q = 0 := by
    intro p q
    have h1 := hall' p q
    have h2 := hall' (Complex.I • p) q
    rw [smul_dotProduct, smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im] at h2
    apply Complex.ext
    · simpa using h2
    · simpa using h1
  have hD0 : D = 0 := by
    ext i j
    have h0 := hzero (Pi.single i 1) (Pi.single j 1)
    rw [← Pi.single_star, star_one, single_dotProduct, one_mul] at h0
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h0
  rw [hD] at hD0
  exact sub_eq_zero.mp hD0

end LevelTowerAlt.Val
end
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.SymmetricChartsCutoffFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt

section

open Set GroundTheory.Heights₂.Heights.Regular
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm.M.PLAux (chartPush chartPush_eq_zero isCompact_symm_image smooth_chartPush contDiffOn_compat)
open scoped ContDiff

theorem cutoff_of_bumps {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] {D : ℕ} {A : FinHolAtlas D X}
    (P : PotentialCharts A) (g : Fin P.N → (Fin D → ℂ) → ℝ) (hgs : ∀ j, ContDiff ℝ ∞ (g j))
    (hg01 : ∀ j y, 0 ≤ g j y ∧ g j y ≤ 1) (hg1 : ∀ j, ∀ x ∈ P.inner j, g j (P.chart j x) = 1)
    (hgc : ∀ j, IsCompact (tsupport (g j))) (hgt : ∀ j, tsupport (g j) ⊆ P.chartMid j) :
    ∃ C : ℝ, P.IsCutoffFamily (fun j x => chartPush (P.chart j) (g j) x - 1) C := by
  have hgt' : ∀ j, tsupport (g j) ⊆ (P.chart j).target := fun j => (hgt j).trans inter_subset_left
  have hcp : ∀ j x, 0 ≤ chartPush (P.chart j) (g j) x ∧ chartPush (P.chart j) (g j) x ≤ 1 := by
    intro j x
    unfold chartPush
    by_cases hx : x ∈ (P.chart j).source
    · rw [indicator_of_mem hx]; exact hg01 j _
    · rw [indicator_of_notMem hx]; exact ⟨le_rfl, zero_le_one⟩
  have hsm : ∀ j, A.Smooth (fun x => chartPush (P.chart j) (g j) x - 1) := by
    intro j a
    exact ContDiffOn.sub (f := chartPush (P.chart j) (g j) ∘ (A.chart a).symm)
      (smooth_chartPush (P.compat j) (hgs j) (hgc j) (hgt' j) a) contDiffOn_const
  have hC : ∀ j k, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ P.chart k '' closure (P.mid k), ∀ w,
      -C * ‖w‖ ^ 2 ≤ levi ((fun x => chartPush (P.chart j) (g j) x - 1) ∘ (P.chart k).symm) y w := by
    intro j k
    have h := contDiffOn_compat (P.compat k) isOpen_univ (hsm j)
    rw [preimage_univ, inter_univ] at h
    refine levi_lower_bound_of_isCompact (P.chart k).open_target (h.of_le (WithTop.coe_le_coe.2 le_top))
      (isClosed_closure.isCompact.image_of_continuousOn
        ((P.chart k).continuousOn.mono (P.closure_mid k))) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (P.chart k).map_source (P.closure_mid k hx)
  choose C hC0 hC using hC
  refine ⟨∑ j, ∑ k, C j k, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro j a
    exact (hsm j a).mono (inter_subset_inter_right _ (preimage_mono (subset_univ _)))
  · intro j x _
    constructor <;> linarith [hcp j x]
  · intro j x hx
    have hs : x ∈ (P.chart j).source := P.mid_subset_source j (P.inner_subset_mid j hx)
    have h1 : chartPush (P.chart j) (g j) x = 1 := by
      unfold chartPush
      rw [indicator_of_mem hs]
      exact hg1 j x hx
    simp [h1]
  · intro j
    refine ⟨(P.chart j).symm '' tsupport (g j), (isCompact_symm_image (hgc j) (hgt' j)).isClosed,
      ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact (hgt j hy).2
    · intro x hx
      simp [chartPush_eq_zero (P.chart j) hx.2]
  · intro j k x hx w
    have h := hC j k (P.chart k x) ⟨x, subset_closure hx.2, rfl⟩ w
    have hle : C j k ≤ ∑ j, ∑ k, C j k :=
      (Finset.single_le_sum (fun k _ => hC0 j k) (Finset.mem_univ k)).trans
        (Finset.single_le_sum (f := fun j => ∑ k, C j k)
          (fun j _ => Finset.sum_nonneg fun k _ => hC0 j k) (Finset.mem_univ j))
    have h2 : 0 ≤ ‖w‖ ^ 2 := by positivity
    nlinarith

theorem exists_bumps {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] {D : ℕ} {A : FinHolAtlas D X}
    (P : PotentialCharts A) (j : Fin P.N) : ∃ g : (Fin D → ℂ) → ℝ, ContDiff ℝ ∞ g ∧ (∀ y, 0 ≤ g y ∧ g y ≤ 1) ∧
      (∀ y ∈ P.chart j '' closure (P.inner j), g y = 1) ∧ IsCompact (tsupport g) ∧
      tsupport g ⊆ P.chartMid j := by
  have hcl : closure (P.inner j) ⊆ (P.chart j).source :=
    (P.closure_inner j).trans (P.mid_subset_source j)
  refine exists_smooth_bump_of_isCompact
    (isClosed_closure.isCompact.image_of_continuousOn ((P.chart j).continuousOn.mono hcl))
    ((P.chart j).continuousOn_symm.isOpen_inter_preimage (P.chart j).open_target
      (P.isOpen_mid j)) ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨(P.chart j).map_source (hcl hx), by
    rw [mem_preimage, (P.chart j).left_inv (hcl hx)]; exact P.closure_inner j hx⟩

end

end LevelTowerAlt
end

