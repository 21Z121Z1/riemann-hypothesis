import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0704
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0275
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0590
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0703
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0706
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0708
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0692
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0712
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0709
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFrameChangeLocalBoundsStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicFrameChange_local_bounds : ∀ (n : ℕ) (K : Type) [Fintype K] [DecidableEq K] (P : ReciprocityTheory.L2DbarEstimates.V n → Matrix K K ℂ) (r : ℝ), 0 < r → (∀ i k, DifferentiableOn ℂ (fun u => P u i k) (Metric.ball 0 r)) → IsUnit (P 0).det → ∃ r' : ℝ, 0 < r' ∧ r' ≤ r ∧ ∃ B : ℝ, ∀ v : ReciprocityTheory.L2DbarEstimates.V n, ‖v‖ < r' → IsUnit (P v).det ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => P u i k) v) ∧ (∀ᶠ u in nhds v, ∀ η, GlobalTheory.HermFrame.mdbar P u η = 0) ∧ (∀ i k, ‖P v i k‖ ≤ B) ∧ (∀ i k, ‖(P v)⁻¹ i k‖ ≤ B) ∧ (∀ a i k, ‖GlobalTheory.HermFrame.mdel P v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) ∧ (∀ a b i k, ‖GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.mdel P u (GlobalTheory.GoodMetric.coordVec b)) v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) := by
  first | exact @GlobalTheory.HermFrame.holoFrame_local_bounds | exact GlobalTheory.HermFrame.holoFrame_local_bounds | (intros; apply GlobalTheory.HermFrame.holoFrame_local_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFrameFamilyChartCoordinatesHolomorphi
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase

theorem isHol_chart_framePt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), ∀ (c' : AlgChart X.str (σ.comp e.toRingHom) X.dim) (k : U.Comp) (n : ℕ) (W : Set (V n)) (ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q)), IsOpen W → (∀ w ∈ W, ψ w ∈ (U.X k).dom) → (∀ τ i i', DifferentiableOn ℂ (fun w => mat (ψ w) τ i i') W) → ∃ q : V n → CxPts X.str (σ.comp e.toRingHom), IsOpen {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} ∧ (∀ w ∈ W, ∀ h : ψ w ∈ (U.X k).dom, (∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)) → q w ∈ c'.e.source ∧ cxOf e σ hj (q w) = cxPt T.Z (U.un k ⟨ψ w, h⟩)) ∧ DifferentiableOn ℂ (fun w => c'.e (q w)) {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _hσ hU X j hji hj c' k n W ψ hW hψW hψd
  classical
  haveI := hji
  have hU' : Formalism.L2.Pj.IsUnf U.toPj := (Formalism.L2.PjFree.isUnf_ofPj U.toPj).1 hU
  by_cases hne : ((U.X k).dom).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    let sf : Frame (U.X k).Ψ (Dw.p + Dw.q) → (U.X k).dom := fun x =>
      if h : x ∈ (U.X k).dom then ⟨x, h⟩ else ⟨x₀, hx₀⟩
    have hsf : ∀ x (h : x ∈ (U.X k).dom), sf x = ⟨x, h⟩ := fun x h => dif_pos h
    have h1 := BdArc.Leave.isHolTo_ptC (U := U.toPj) hU' k sf fun x h => by rw [hsf x h]
    have h2 := LocLift.isHolTo_comp_hom h1 T.Z.jQ
    have hψ : DifferentiableOn ℂ ψ W :=
      differentiableOn_pi.2 fun τ => differentiableOn_pi.2 fun a => differentiableOn_pi.2 fun b => hψd τ a b
    have h3 := LocLift.isHolTo_comp h2 hW hψ hψW
    let P : V n → CxPts (genStr T.Z) σ := fun w => cxPt T.Z (U.un k (sf (ψ w)))
    have h4 : IsHolTo W fun w => (P w).1 := h3
    have hP : ∀ w, ∀ h : ψ w ∈ (U.X k).dom, cxPt T.Z (U.un k ⟨ψ w, h⟩) = P w := fun w h => by
      simp only [P, hsf _ h]
    have hc : ContinuousOn P W := GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo h4
    have hκ : Topology.IsOpenEmbedding (cxOf e σ hj) := isOpenEmbedding_cxOf e σ hj
    have hS : {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source,
        cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} = W ∩ P ⁻¹' (cxOf e σ hj '' c'.e.source) := by
      ext w
      constructor
      · rintro ⟨hw, h, y', hy', he⟩
        exact ⟨hw, y', hy', he.trans (hP w h)⟩
      · rintro ⟨hw, y', hy', he⟩
        exact ⟨hw, hψW w hw, y', hy', he.trans (hP w _).symm⟩
    let q : V n → CxPts X.str (σ.comp e.toRingHom) := fun w =>
      if h : ∃ y' ∈ c'.e.source, cxOf e σ hj y' = P w then h.choose else c'.e.symm 0
    have hq : ∀ w, (∃ y' ∈ c'.e.source, cxOf e σ hj y' = P w) →
        q w ∈ c'.e.source ∧ cxOf e σ hj (q w) = P w := fun w h => by
      simp only [q, dif_pos h]
      exact h.choose_spec
    refine ⟨q, ?_, fun w _ h hex => ?_, ?_⟩
    · rw [hS]
      exact hc.isOpen_inter_preimage hW (hκ.isOpenMap _ c'.e.open_source)
    · rw [hP w h] at hex ⊢
      exact hq w hex
    · rw [hS, differentiableOn_euclidean]
      intro a
      have hd := (h4 (j ''ᵁ c'.U) ((j.appIso c'.U).inv.hom (c'.x a))).2
      refine (hd.mono fun w hw => ⟨hw.1, ?_⟩).congr fun w hw => ?_
      · obtain ⟨hq1, hq2⟩ := hq w (by obtain ⟨y', hy', he⟩ := hw.2; exact ⟨y', hy', he⟩)
        show ⊤ ≤ (P w).1 ⁻¹ᵁ _
        rw [← hq2]
        exact le_preimage_cxOf e σ hj c'.U (c'.source_subset hq1)
      · obtain ⟨hq1, hq2⟩ := hq w (by obtain ⟨y', hy', he⟩ := hw.2; exact ⟨y', hy', he⟩)
        show c'.e (q w) a = valAt' (P w).1 _ _
        rw [c'.apply_eq _ hq1 a, ev_eq_valAt'_cxOf e σ hj _ _ (c'.source_subset hq1), hq2]
  · have hS : {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source,
        cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun w hw => hne ⟨_, hw.2.1⟩
    refine ⟨fun _ => c'.e.symm 0, ?_, fun w _ h _ => absurd ⟨_, h⟩ hne, ?_⟩
    · rw [hS]
      exact isOpen_empty
    · rw [hS]
      exact differentiableOn_empty

end GlobalTheory.LieBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeCellOfInFaceOfCellFormCMField
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark.FaceIn

section Lattice

variable {X : Type} [AddCommGroup X]

theorem inRCone_of_nsmul_eq {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X} {k : ℕ}
    {c : Fin m → ℕ} (hk : 0 < k) (h : k • β = ∑ i, c i • γ i) : InRCone γ β := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨fun i => (c i : ℝ) / k, fun i => by positivity, LinearMap.ext₂ fun a b => ?_⟩
  have h1 : (k : ℤ) * β a b = ∑ i, (c i : ℤ) * γ i a b := by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ h a b
  have h2 : (k : ℝ) * β a b = ∑ i, (c i : ℝ) * γ i a b := by exact_mod_cast h1
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [← mul_right_inj' hk', h2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by field_simp

theorem inRCone_face {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {s : Fin m' ↪ Fin m}
    {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (hcut : IsFaceCut γ s h) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone γ β)
    (h0 : h β = 0) : InRCone (fun j => γ (s j)) β := by
  obtain ⟨c, hc, e⟩ := hβ
  have e1 := apply_eq_of_toReal_eq e h
  rw [h0, Int.cast_zero] at e1
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
    mul_nonneg (hc j) (show (0 : ℝ) ≤ h (γ j) by exact_mod_cast hcut.1 j)).1 e1.symm
  have hc0 : ∀ j, j ∉ Set.range s → c j = 0 := fun j hj => by
    have hne : (h (γ j) : ℝ) ≠ 0 := fun h0 => hj ((hcut.2 j).1 (by exact_mod_cast h0))
    exact (mul_eq_zero.1 (hz j (Finset.mem_univ _))).resolve_right hne
  refine ⟨fun i => c (s i), fun i => hc _, ?_⟩
  rw [e]
  classical
  rw [← Finset.sum_map Finset.univ s (fun j => c j • toReal (γ j))]
  refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
  rw [hc0 j fun ⟨i, hi⟩ => hj (by simp [← hi]), zero_smul]

theorem apply_eq_zero_of_genRank_le {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {s : Fin m' → Fin m}
    {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (h0 : ∀ j, h (γ (s j)) = 0) (hr : genRank γ ≤ genRank fun j => γ (s j))
    (j : Fin m) : h (γ j) = 0 := by
  unfold genRank at hr
  set B := Submodule.span ℤ (Set.range γ) with hB
  set A := Submodule.span ℤ (Set.range fun j => γ (s j)) with hA
  haveI : Module.Finite ℤ B := Module.Finite.span_of_finite ℤ (Set.finite_range γ)
  have hAB : A ≤ B := Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨s j, rfl⟩)
  have hAk : A ≤ LinearMap.ker h := Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact h0 j)
  set K : Submodule ℤ B := LinearMap.ker (h.domRestrict B) with hK
  have h1 : Module.finrank ℤ A ≤ Module.finrank ℤ K := by
    rw [← (Submodule.comapSubtypeEquivOfLe hAB).finrank_eq]
    exact Submodule.finrank_mono fun y hy => hAk hy
  have h2 := Submodule.finrank_quotient_add_finrank K
  have h3 : Module.finrank ℤ (B ⧸ K) = 0 := by omega
  obtain ⟨a, ha, e⟩ := Module.finrank_eq_zero_iff.1 h3
    (Submodule.Quotient.mk ⟨γ j, Submodule.subset_span ⟨j, rfl⟩⟩)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at e
  have e' : a * h (γ j) = 0 := by simpa [hK] using e
  exact (mul_eq_zero.1 e').resolve_left ha

end Lattice

theorem apply_eq_of_inRCone {O : Type} [CommRing O] {ψ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : ψ.LinearOn γ) {N : ℕ}
    {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (h1 : ∀ i, (ℓ (γ i) : ℝ) = N * ψ.evalZ (γ i)) {β : LinearMap.BilinForm ℤ X}
    (hβ : InRCone γ β) : (ℓ β : ℝ) = N * ψ.evalZ β := by
  obtain ⟨c, hc, e⟩ := hβ
  rw [apply_eq_of_toReal_eq e ℓ, ← evalR_toReal, e, (linearOn_iff ψ γ).1 hγ c hc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [h1]; ring

theorem inRCone_of_add : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ lab : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCarrierDim H.bar q ψ lab → ∀ (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
    Dominates H.bar X → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → ∀ β ∈ balForms H.bar X,
    (∀ y, 0 ≤ β y y) → InRCone v β → ∀ x ∈ balForms H.bar X, (∀ y, 0 ≤ x y y) →
    ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x → lab.evalZ (β + x) = lab.evalZ β → InRCone v x := by
  intro E _ _ _ H q ψ lab hψ hlab X _ _ _ _ hX hD m v hv β hβ hβp hvβ x hx hxp hadd hl
  classical
  have hs : β + x ∈ balForms H.bar X := Submodule.add_mem _ hβ hx
  have hsp : ∀ y, 0 ≤ (β + x) y y := fun y => add_nonneg (hβp y) (hxp y)
  have hne : {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ (β + x) ∧
      genRank γ = k}.Nonempty := by
    have hR : toReal (β + x) ∈ psdCone H.bar X := by
      simpa using GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 ![β + x] ![1] (by simp [hs])
        (by simpa using hsp) (by simp)
    obtain ⟨S, -, hcov⟩ := (hψ X hX).finite
    obtain ⟨e, mm, γ, c, hγ, -, hc, hsum⟩ := hcov _ hR
    refine ⟨_, mm, fun i => pull e.symm.toLinearMap (γ i), CarDim.isCell_pull_equiv hγ e.symm, ⟨c, hc, ?_⟩, rfl⟩
    exact LinearMap.ext₂ fun a b => by
      have := LinearMap.congr_fun₂ hsum (e.symm a) (e.symm b)
      simpa [LinearMap.sum_apply] using this
  obtain ⟨n, γ, hγ, hγs, hrk⟩ := Nat.sInf_mem hne
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  obtain ⟨N', ℓ', hN', h1', h2', h3'⟩ := hv.strict
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN'r : (0 : ℝ) < N' := by exact_mod_cast hN'
  have e0 := apply_eq_of_inRCone hγ.linear h1 hγs
  rw [map_add, Int.cast_add, hadd, mul_add] at e0
  have eβ : (N : ℝ) * ψ.evalZ β = ℓ β := by linarith [h2 β hβ hβp, h2 x hx hxp]
  have ex : (N : ℝ) * ψ.evalZ x = ℓ x := by linarith [h2 β hβ hβp, h2 x hx hxp]
  have hγβ : InRCone γ β := by
    obtain ⟨k, c, hk, hc⟩ := h3 β hβ hβp eβ
    exact inRCone_of_nsmul_eq hk hc
  obtain ⟨cx, -, hcx⟩ : InRCone γ x := by
    obtain ⟨k, c, hk, hc⟩ := h3 x hx hxp ex
    exact inRCone_of_nsmul_eq hk hc
  set h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := (N : ℤ) • ℓ' - (N' : ℤ) • ℓ with hh
  have happ : ∀ u, (h u : ℝ) = N * ℓ' u - N' * ℓ u := fun u => by simp [hh]
  let Z : Finset (Fin n) := Finset.univ.filter fun j => h (γ j) = 0
  let s : Fin Z.card ↪ Fin n := (Z.orderEmbOfFin rfl).toEmbedding
  have hcut : IsFaceCut γ s h := by
    refine ⟨fun j => ?_, fun j => ?_⟩
    · have : (0 : ℝ) ≤ h (γ j) := by
        rw [happ, h1]
        have := mul_le_mul_of_nonneg_left (h2' _ (hγ.mem j) (hγ.nonneg j)) hNr.le
        linarith
      exact_mod_cast this
    · have : Set.range s = Z := Z.range_orderEmbOfFin rfl
      rw [this]
      simp [Z]
  have hface := isCell_face_of_isFaceCut E H q ψ hψ X hX hD n γ hγ _ s h hcut
  have hβ0 : h β = 0 := by
    have : (h β : ℝ) = 0 := by
      rw [happ, apply_eq_of_inRCone hv.linear h1' hvβ, ← eβ]; ring
    exact_mod_cast this
  have hle : genRank γ ≤ genRank fun j => γ (s j) := by
    rw [hlab X hX _ hs hsp, hlab X hX _ hβ hβp, Nat.cast_inj] at hl
    rw [hrk, hl]
    exact Nat.sInf_le ⟨_, _, hface, inRCone_face hcut hγβ hβ0, rfl⟩
  have hall := apply_eq_zero_of_genRank_le (h := h) (fun j => (hcut.2 _).2 ⟨j, rfl⟩) hle
  have hx0 : (h x : ℝ) = 0 := by
    rw [apply_eq_of_toReal_eq hcx h]
    simp [hall]
  rw [happ, ← ex] at hx0
  have ex' : (N' : ℝ) * ψ.evalZ x = ℓ' x := by
    have : (N : ℝ) * (N' * ψ.evalZ x - ℓ' x) = 0 := by linarith
    linarith [(mul_eq_zero.1 this).resolve_left hNr.ne']
  obtain ⟨k, c, hk, hc⟩ := h3' x hx hxp ex'
  exact inRCone_of_nsmul_eq hk hc

end GlobalTheory.PolFan.Mark.FaceIn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeCellOfLinearPieceThroughCellPoint
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

theorem inRCone_of_interior_linearOn {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] {m k : ℕ}
    (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin k → LinearMap.BilinForm ℤ X) (hγ : IsCell bar φ γ)
    (hmem : ∀ i, γ' i ∈ balForms bar X) (hpos : ∀ i y, 0 ≤ γ' i y y) (hlin : φ.LinearOn γ')
    (β : LinearMap.BilinForm ℤ X) (a : Fin m → ℝ) (b : Fin k → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ i, 0 < b i)
    (e1 : toReal β = ∑ j, a j • toReal (γ j)) (e2 : toReal β = ∑ i, b i • toReal (γ' i)) (i : Fin k) :
    InRCone γ (γ' i) := by
  have hev : ∀ {p : ℕ} (δ : Fin p → LinearMap.BilinForm ℤ X) (c : Fin p → ℝ), (∀ j, 0 ≤ c j) → φ.LinearOn δ →
      toReal β = ∑ j, c j • toReal (δ j) → φ.evalZ β = ∑ j, c j * φ.evalZ (δ j) := by
    intro p δ c hc hl e
    rw [← hl c hc]
    unfold InvFun.evalZ
    congr 1
    funext x y
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ e x y
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  have ea := hev γ a ha hγ.linear e1
  have eb := hev γ' b (fun i => (hb i).le) hlin e2
  have la := apply_eq_of_toReal_eq e1 ℓ
  have lb := apply_eq_of_toReal_eq e2 ℓ
  have hsum : ∑ i, b i * ((ℓ (γ' i) : ℝ) - N * φ.evalZ (γ' i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← lb, sub_eq_zero, la]
    have e3 : ∑ i, b i * ((N : ℝ) * φ.evalZ (γ' i)) = N * φ.evalZ β := by
      rw [eb, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e3, ea, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [h1 j]; ring
  have hnn : ∀ i, 0 ≤ b i * ((ℓ (γ' i) : ℝ) - N * φ.evalZ (γ' i)) := fun i =>
    mul_nonneg (hb i).le (sub_nonneg.2 (h2 _ (hmem i) (hpos i)))
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).1 hsum i (Finset.mem_univ _)
  have heq : (N : ℝ) * φ.evalZ (γ' i) = ℓ (γ' i) := by
    have := (mul_eq_zero.1 hz).resolve_left (hb i).ne'
    linarith
  obtain ⟨kk, c, hk, hc⟩ := h3 _ (hmem i) (hpos i) heq
  have hkR : (kk : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨fun j => (c j : ℝ) / kk, fun j => by positivity, LinearMap.ext₂ fun x y => ?_⟩
  have h4 := LinearMap.congr_fun₂ hc x y
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at h4
  have h5 : (kk : ℝ) * (γ' i x y : ℝ) = ∑ j, (c j : ℝ) * (γ j x y : ℝ) := by exact_mod_cast h4
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have h6 : (γ' i x y : ℝ) = (∑ j, (c j : ℝ) * (γ j x y : ℝ)) / kk := by
    rw [eq_div_iff hkR, ← h5]; ring
  rw [h6, Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem inRCone_of_interior_linearOn' : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {m k : ℕ}
  (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin k → LinearMap.BilinForm ℤ X), IsCell bar φ γ → (∀ i, γ' i ∈ balForms bar X) →
  (∀ i y, 0 ≤ γ' i y y) → φ.LinearOn γ' →
  ∀ (β : LinearMap.BilinForm ℤ X) (a : Fin m → ℝ) (b : Fin k → ℝ), (∀ j, 0 ≤ a j) → (∀ i, 0 < b i) →
    toReal β = ∑ j, a j • toReal (γ j) → toReal β = ∑ i, b i • toReal (γ' i) → ∀ i, InRCone γ (γ' i) :=
by
  intro O _ bar φ X _ _ _ m k γ γ' hγ hmem hpos hlin β a b ha hb e1 e2 i
  exact inRCone_of_interior_linearOn bar φ γ γ' hγ hmem hpos hlin β a b ha hb e1 e2 i

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSummandsOfEvalZAdditiveCell
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

noncomputable section

namespace GlobalTheory.PolFan.Mark

theorem inRCone_of_evalZ_sum_le (O : Type) [CommRing O] (bar : O → O) (ψ : InvFun O) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (hγ : IsCell bar ψ γ) (k : ℕ)
    (u : Fin k → LinearMap.BilinForm ℤ X) (hu : ∀ j, u j ∈ balForms bar X) (hp : ∀ j y, 0 ≤ u j y y)
    (hs : InRCone γ (∑ j, u j)) (hle : ψ.evalZ (∑ j, u j) ≤ ∑ j, ψ.evalZ (u j)) : ∀ j, InRCone γ (u j) := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  obtain ⟨c, hc, e⟩ := hs
  have hsum : ψ.evalZ (∑ j, u j) = ∑ i, c i * ψ.evalZ (γ i) := by
    rw [← hγ.linear c hc]
    unfold InvFun.evalZ
    congr 1
    funext a b
    have := LinearMap.congr_fun₂ e a b
    simpa [LinearMap.sum_apply] using this
  have hℓ : (ℓ (∑ j, u j) : ℝ) = N * ψ.evalZ (∑ j, u j) := by
    rw [apply_eq_of_toReal_eq e ℓ, hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1 i]; ring
  have hd : ∀ j, 0 ≤ (ℓ (u j) : ℝ) - N * ψ.evalZ (u j) := fun j => sub_nonneg.2 (h2 _ (hu j) (hp j))
  have hz : ∑ j, ((ℓ (u j) : ℝ) - N * ψ.evalZ (u j)) = 0 := by
    refine le_antisymm ?_ (Finset.sum_nonneg fun j _ => hd j)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have e1 : (∑ j, (ℓ (u j) : ℝ)) = ℓ (∑ j, u j) := by rw [map_sum]; push_cast; rfl
    rw [e1, hℓ]
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith [mul_le_mul_of_nonneg_left hle h0]
  intro j
  have hj := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hd j).1 hz j (Finset.mem_univ _)
  obtain ⟨n, c', hn, hc'⟩ := h3 _ (hu j) (hp j) (by linarith)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨fun i => (c' i : ℝ) / n, fun i => by positivity, LinearMap.ext₂ fun a b => ?_⟩
  have h4 := LinearMap.congr_fun₂ hc' a b
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul] at h4
  have h5 : (n : ℝ) * u j a b = ∑ i, (c' i : ℝ) * γ i a b := by exact_mod_cast h4
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [show ∑ i, (c' i : ℝ) / n * (γ i a b : ℝ) = (∑ i, (c' i : ℝ) * γ i a b) / n by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring, ← h5]
  field_simp

end GlobalTheory.PolFan.Mark
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvFunEvalZAddOfLinearOnRealCone
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark

theorem evalZ_eq_sum_of_toReal_eq_addcone {O : Type} [CommRing O] (ψ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} {v : Fin m → LinearMap.BilinForm ℤ X} (hv : ψ.LinearOn v)
    {β : LinearMap.BilinForm ℤ X} {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i)
    (h : toReal β = ∑ i, c i • toReal (v i)) : ψ.evalZ β = ∑ i, c i * ψ.evalZ (v i) := by
  rw [← hv c hc]
  unfold InvFun.evalZ
  congr 1
  funext a b
  have := LinearMap.congr_fun₂ h a b
  simpa [LinearMap.sum_apply] using this

theorem evalZ_add_of_linearOn_inRCone (O : Type) [CommRing O] (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X) (hv : ψ.LinearOn v)
    (β x : LinearMap.BilinForm ℤ X) (hβ : InRCone v β) (hx : InRCone v x) :
    ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x := by
  obtain ⟨a, ha, hβ⟩ := hβ
  obtain ⟨b, hb, hx⟩ := hx
  have hs : toReal (β + x) = ∑ i, (a i + b i) • toReal (v i) := by
    have : toReal (β + x) = toReal β + toReal x := LinearMap.ext₂ fun s t => by simp
    rw [this, hβ, hx, ← Finset.sum_add_distrib]
    simp only [add_smul]
  rw [evalZ_eq_sum_of_toReal_eq_addcone ψ hv (fun i => add_nonneg (ha i) (hb i)) hs,
    evalZ_eq_sum_of_toReal_eq_addcone ψ hv ha hβ, evalZ_eq_sum_of_toReal_eq_addcone ψ hv hb hx,
    ← Finset.sum_add_distrib]
  simp only [add_mul]

end GlobalTheory.PolFan.Mark
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAuxiliaryHeckeCharacterToricListOfGridAlt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridLambdaData

theorem isAuxiliaryHeckeCharacter_toricListOfGrid : ∀ (D : D7) {T : Type} (L : Formalism.IndefR.Links.LevCh D T) (sc : GlobalTheory.ChiGrid.Consts) (G : GlobalTheory.ChiGrid.GridData L sc) (w0 : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.LamTie.PlacesOk D.host (AbsolutelyIrreducibleSpan.q0 D) w0 → ∀ a : Fin D.R.m, GlobalTheory.LamTie.IsAuxiliaryHeckeCharacter D.host (G.pl.w G.pl.v0) ((GlobalTheory.BigTop.Fun.lamOf G).c a) ((GlobalTheory.BigTop.Fun.lamOf G).chi a) := by
  intro D T L sc G _ _ a
  have hw0 : (G.pl.w G.pl.v0).under (𝓞 D.host.F) = G.pl.v0 := G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
  have hS1 : ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.LamTie.Over4 D.host w → w.under (𝓞 D.host.F) ∈ GlobalTheory.ChiGrid.S1 D := by
    intro w h
    rw [GlobalTheory.ChiGrid.S1_mem_OmF]
    rcases h with ⟨k, hk⟩ | hk | hk
    · fin_cases k
      · exact Or.inl (GlobalTheory.BigTop.Fun.natCast_mem_under hk)
      · exact Or.inr (Or.inl (GlobalTheory.BigTop.Fun.natCast_mem_under hk))
    · exact Or.inr (Or.inr (Or.inl (GlobalTheory.BigTop.Fun.natCast_mem_under hk)))
    · exact Or.inr (Or.inr (Or.inr (GlobalTheory.BigTop.Fun.natCast_mem_under hk)))
  have hOv : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∈ GlobalTheory.ChiGrid.S1 D → GlobalTheory.LamTie.Over4 D.host w := by
    intro w h
    rcases (GlobalTheory.ChiGrid.S1_mem_OmF D).1 h with h | h | h | h
    · exact Or.inl ⟨0, GlobalTheory.BigTop.Fun.natCast_mem_of_under h⟩
    · exact Or.inl ⟨1, GlobalTheory.BigTop.Fun.natCast_mem_of_under h⟩
    · exact Or.inr (Or.inl (GlobalTheory.BigTop.Fun.natCast_mem_of_under h))
    · exact Or.inr (Or.inr (GlobalTheory.BigTop.Fun.natCast_mem_of_under h))
  have a1 : 1 ≤ a.1 + 1 := by omega
  have a2 : a.1 + 1 ≤ D.R.m := a.2
  refine ⟨GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (G.ch.chi_eq _ a1 a2), G.ch.triv _ a1 a2,
    GlobalTheory.BigTop.Fun.lamOf_hasInfQ G a, fun w h4 h0 => ?_, fun w h4 => ?_, fun w he => ?_⟩
  · refine G.ch.unr _ a1 a2 w fun hw => ?_
    rcases G.pl.mem_S0_of_sum_eq.1 hw with h | h
    · exact h0 (h.trans hw0.symm)
    · exact h4 (hOv w h)
  · obtain ⟨l2, l1⟩ := G.ch.lev1 _ a1 a2 w (hS1 w h4)
    exact GlobalTheory.LamTie.GridCharacters.expAt_succ (n := 1) l2 l1
  · have e : w.under (𝓞 D.host.F) = G.pl.v0 :=
      (show w.under (𝓞 D.host.F) = (G.pl.w G.pl.v0).under (𝓞 D.host.F) from he).trans hw0
    obtain ⟨l1, l0⟩ := G.ch.lev0 _ a1 a2 w e
    exact GlobalTheory.LamTie.GridCharacters.expAt_succ (n := 0) l1 fun h => l0 (((G.ch.chiH _).unrAt_iff w).2 h)

example : ∀ (D : D7) {T : Type} (L : Formalism.IndefR.Links.LevCh D T) (sc : GlobalTheory.ChiGrid.Consts) (G : GlobalTheory.ChiGrid.GridData L sc) (w0 : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.LamTie.PlacesOk D.host (AbsolutelyIrreducibleSpan.q0 D) w0 → ∀ a : Fin D.R.m, GlobalTheory.LamTie.IsAuxiliaryHeckeCharacter D.host (G.pl.w G.pl.v0) ((GlobalTheory.BigTop.Fun.lamOf G).c a) ((GlobalTheory.BigTop.Fun.lamOf G).chi a) := isAuxiliaryHeckeCharacter_toricListOfGrid

end GlobalTheory.GridLambdaData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMonHomOfSquaredDegenerationDataFunctionalEquat
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PsiFourth

theorem key : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (D D' : DegData R (maximalIdeal R)), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ (mu α : D.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D.toPre.P.A) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → sval (f (α + 2 • mu)) y.left z J = sval (f α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (mu α : D'.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D'.toPre.P.A) (z : T.left) (J : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D'.toPre.P.L z J → sval (f' (α + 2 • mu)) y.left z J = sval (f' α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D'.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D'.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (β : D'.toPre.X) (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → sval (f (xe (2 • β))) (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ).val * sval (f' (2 • β)) ρ z J' ^ 2) → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → ∀ (Ω : (T ⟶ D'.toPre.P.A) → (T.left.presheaf.stalk z)ˣ), Ω = (fun x => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) x.left) → ∀ (a b c : T ⟶ D'.toPre.P.A), cubV D.toPre.cub z J (a ≫ Φ.hom) (b ≫ Φ.hom) (c ≫ Φ.hom) ^ 2 = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * cubV D'.toPre.cub z J' a b c ^ 2) → (¬ ∀ j, (f 0).f j = 0) → ∀ (y : D'.toPre.X) (r r' : R), PsiCoord D.toPre (xe (2 • y)) r → PsiCoord D'.toPre (2 • y) r' → Associated (r ^ 4) (r' ^ 4) := by
  intro R _ _ _ hR D D' Φ w hw hΦ xe hc f f' hf hf' hcorr hcub hne y r r' hr hr'
  have := D.toPre.P.isAb.smooth
  have := D.toPre.P.isAb.geomConnected
  haveI : IsIntegral (DegPre.BF D.toPre (FractionRing R)).left :=
    (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres D.toPre.P.A.hom).geometrically_isIntegral
      (TF (R := R) (FractionRing R)).hom _ _ (IsPullback.of_hasPullback _ D.toPre.P.A.hom).flip
  have ne : ∀ J, Geo.Tor.Good D.toPre.P.L (genericPoint (DegPre.BF D.toPre (FractionRing R)).left) J →
      sval (f 0) (DegPre.prB D.toPre (FractionRing R)).left (genericPoint (DegPre.BF D.toPre (FractionRing R)).left) J ≠ 0 := by
    intro J hJ h0
    apply hne
    have hL := D.toPre.P.isLB
    have inj := PullIntegral.prB_app_injective D.toPre (FractionRing R)
    have e₀ := ThetaScalar.eq_zero_of_germ (H1.SectionArithmetic.pullSec (f 0) (DegPre.prB D.toPre (FractionRing R)).left) _ hJ
      (by rw [H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ, Category.id_comp, h0])
    exact fun j => PullIntegral.sec_ext_of_inj hL _ inj (s' := ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secZero) (fun y J hJ => by
      have := ThetaScalar.sval_eq_zero _ e₀ (𝟙 _) y hJ
      rw [H1.SectionArithmetic.sval_pullSec _ _ _ y hJ] at this
      rw [this]
      exact (ThetaScalar.sval_eq_zero ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secZero (fun _ => rfl) _ y hJ).symm) j
  exact GlobalTheory.T.psi_coordinates_fourthPower_associated R D D' Φ w hw (xe (2 • y)) (2 • y) _
    (fun J J' hJ hJ' => GlobalTheory.T.weightTwoFactor_sq_values_correspond R D D' Φ w hΦ xe hc f f' hf hf' hcorr hcub y _ J J' hJ hJ'
      inferInstance (ne J hJ)) r r' hr hr'

end GlobalTheory.PsiFourth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyFanFaceCutByIntLinearFormIsCellStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyFan_face_cut_by_intLinearForm_isCell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → Dominates H.bar X → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut v s h → IsCell H.bar ψ (fun j => v (s j)) := by
  first | exact @GlobalTheory.PolFan.isCell_face_of_isFaceCut | exact GlobalTheory.PolFan.isCell_face_of_isFaceCut | (intros; apply GlobalTheory.PolFan.isCell_face_of_isFaceCut <;> assumption)
end

