import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0028
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0021
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0031
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0035
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurablePhi
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CurvAndMarginClosed
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.CurvMarginClosed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem curv_and_margin_closed :
    (CurvGGStatement (E := E)) ∧ (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (m : ℝ), (∀ τ (i j : Fin r), i ≤ j → (j : ℕ) < X.p0 → la τ j ≤ la τ i) → (∀ τ (i j : Fin r), X.p0 ≤ (i : ℕ) → i ≤ j → la τ j ≤ la τ i) → (∀ τ (i j : Fin r), (i : ℕ) < X.p0 → X.p0 ≤ (j : ℕ) → m ≤ (la τ j : ℝ) - (la τ i : ℝ)) → ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, m * leviRh X x0 z ξ ≤ leviO X x0 (phla X la) z ξ) := by
  have hdiag := GlobalTheory.T.leviForm_weightMetric_orthonormal_diagonal (E := E)
  have htrans := GlobalTheory.LeviTransfer.levi_transfer (E := E) GlobalTheory.FrameMeasureClosed.kapGG_holds
    GlobalTheory.NormFactor.nfac_transform
  exact GlobalTheory.CurvMargin.curv_and_margin hdiag htrans

end GlobalTheory.CurvMarginClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EventuallySplit
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FiniteZeroOrbits

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cpt_origin {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) : cpt X x 0 = x := by
  have : nmat X 0 = ExtFPf.oneF X := by
    funext τ a b
    simp only [nmat, ExtFPf.oneF, Matrix.one_apply]
    split_ifs with h1 h2 h3
    · exact absurd h2 (ne_of_gt h1)
    · rfl
    · rfl
    · rfl
  rw [cpt, this, ExtFPf.rmul_oneF]

theorem eventually_split {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ y in 𝓝 x, y ∈ X.dom ∧ ∃ z ∈ Metric.closedBall (0 : V (nd X)) δ, ∃ b ∈ Bor X.Ψ r,
      y = rmul (cpt X x z) b := by
  have hu : ∀ τ, IsUnit (mat x τ).det := fun τ => isUnit_iff_ne_zero.mpr (hx τ).1
  have hM : ∀ τ, LUPf.Mx X x x τ = 1 := fun τ => Matrix.nonsing_inv_mul _ (hu τ)
  have hΔ : LUPf.DeltaF X x x ≠ 0 := by
    have : LUPf.DeltaF X x x = 1 := by
      unfold LUPf.DeltaF
      refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun k _ => ?_
      rw [hM]
      exact LUPf.lminor_one k
    rw [this]; exact one_ne_zero
  have hL : LUPf.Lm (1 : Matrix (Fin r) (Fin r) ℂ) = 1 := by
    refine (LUPf.Lm_unique 1 1 (fun k => by rw [LUPf.lminor_one]; exact one_ne_zero)
      (fun i k h => Matrix.one_apply_ne (ne_of_lt h)) (fun i => Matrix.one_apply_eq i) fun i j h => ?_).symm
    rw [Matrix.one_mul]; exact Matrix.one_apply_ne (ne_of_gt h)
  have hz0 : LUPf.zF X x x = 0 := by
    ext k
    set p := (Fintype.equivFin (Ent X)).symm k with hp
    show ((LUPf.Lm (LUPf.Mx X x x p.1))⁻¹ : Matrix (Fin r) (Fin r) ℂ) p.2.1.1 p.2.1.2 = 0
    rw [hM, hL, inv_one]
    exact Matrix.one_apply_ne (ne_of_gt p.2.2)
  have hopen : IsOpen {y | y ∈ X.dom ∧ LUPf.DeltaF X x y ≠ 0} :=
    (FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun (LUPf.Delta_diff (X := X) (x0 := x)).continuous continuous_const)
  have hn := hopen.mem_nhds (show x ∈ {y | y ∈ X.dom ∧ LUPf.DeltaF X x y ≠ 0} from ⟨hx, hΔ⟩)
  have hc : ContinuousAt (LUPf.zF X x) x :=
    (LUPf.zF_diffOn (X := X) (x0 := x)).continuousOn.continuousAt hn
  have hb : ∀ᶠ y in 𝓝 x, LUPf.zF X x y ∈ Metric.closedBall (0 : V (nd X)) δ :=
    hc.preimage_mem_nhds (by rw [hz0]; exact Metric.closedBall_mem_nhds _ hδ)
  filter_upwards [hn, hb] with y hy hyb
  refine ⟨hy.1, _, hyb, _, LUPf.bF_mem hy.1 hy.2, ?_⟩
  funext τ
  show y τ = (mat x τ * mat (nmat X (LUPf.zF X x y)) τ *
    (LUPf.Lm (LUPf.Mx X x y τ) * LUPf.Mx X x y τ) : Matrix (Fin r) (Fin r) ℂ)
  rw [LUPf.nmat_zF]
  show y τ = (mat x τ * (LUPf.Lm (LUPf.Mx X x y τ))⁻¹ * (LUPf.Lm (LUPf.Mx X x y τ) * ((mat x τ)⁻¹ * mat y τ)) :
    Matrix (Fin r) (Fin r) ℂ)
  have hL' : IsUnit (LUPf.Lm (LUPf.Mx X x y τ)).det := by rw [LUPf.Lm_det]; exact isUnit_one
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (LUPf.Lm (LUPf.Mx X x y τ))⁻¹, Matrix.nonsing_inv_mul _ hL',
    Matrix.one_mul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu τ), Matrix.one_mul]
  rfl

theorem isolated_of_det {n : ℕ} {f : V n → V n} (hdet : (fderiv ℂ f 0).det ≠ 0) (h0 : f 0 = 0) :
    ∃ δ > 0, ∀ y ∈ Metric.closedBall (0 : V n) δ, f y = 0 → y = 0 := by
  by_cases hd : DifferentiableAt ℂ f 0
  · exact HE.iso_zero hd.hasFDerivAt hdet h0
  · refine ⟨1, one_pos, fun y _ _ => ?_⟩
    have hk := HE.ker_bot_of_det hdet
    rw [fderiv_zero_of_not_differentiableAt hd] at hk
    have : y ∈ LinearMap.ker ((0 : V n →L[ℂ] V n) : V n →ₗ[ℂ] V n) := by simp
    rw [hk] at this
    exact (Submodule.mem_bot ℂ).1 this

def orbitSetoid {r : ℕ} (X : Data E r) : Setoid (Frame X.Ψ r) where
  r x y := ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, y = lact γ (rmul x b)
  iseqv := by
    refine ⟨fun x => ⟨1, X.Γ.one_mem, ExtFPf.oneF X, ExtFPf.oneF_mem X, ?_⟩, ?_, ?_⟩
    · rw [FundSetPf.lact_one, ExtFPf.rmul_oneF]
    · rintro x y ⟨γ, hγ, b, hb, rfl⟩
      refine ⟨γ⁻¹, X.Γ.inv_mem hγ, ExtFPf.invF X b, ExtFPf.invF_mem X hb, ?_⟩
      rw [← FundSetPf.lact_rmul, FundSetPf.lact_inv, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb,
        ExtFPf.rmul_oneF]
    · rintro x y z ⟨γ, hγ, b, hb, rfl⟩ ⟨γ', hγ', b', hb', rfl⟩
      refine ⟨γ' * γ, X.Γ.mul_mem hγ' hγ, rmul b b', ExtFPf.mul_mem X hb hb', ?_⟩
      rw [FundSetPf.lact_mul, ← FundSetPf.lact_rmul, ExtFPf.rmul_assoc]

theorem finite_orbits : ∀ (r : ℕ) (X : Data E r) (L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ),
    X.IsSec L w0 → (∀ k, X.IsSec L (s k)) →
    (∀ x ∈ X.dom, (∀ k, s k x = 0) → w0 x ≠ 0 ∧ (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      s k (cpt X x z) / w0 (cpt X x z) : V (nd X))) 0).det ≠ 0) →
    ∀ C : Set (Frame X.Ψ r), IsCompact C → C ⊆ X.dom →
    (∀ x ∈ X.dom, (∀ k, s k x = 0) → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ C) →
    ∃ (δ : ℕ) (xs : Fin δ → Frame X.Ψ r), (∀ j, xs j ∈ X.dom) ∧
      (∀ x ∈ X.dom, (∀ k, s k x = 0) ↔ ∃ j, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (xs j) b)) ∧
      ∀ j j', ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, xs j' = lact γ (rmul (xs j) b) → j = j' := by
  classical
  intro r X L w0 s _ hs hsimp C hC hCd hmeet
  set S := orbitSetoid X with hS

  have hstab : ∀ x y, S.r x y → (x ∈ X.dom ∧ ∀ k, s k x = 0) → (y ∈ X.dom ∧ ∀ k, s k y = 0) := by
    rintro x y ⟨γ, hγ, b, hb, rfl⟩ ⟨hx, h0⟩
    have hxb := OntoS.dom_rmul X hx hb
    refine ⟨OntoS.dom_lact X hγ hxb, fun k => ?_⟩
    rw [(hs k).2.2 γ hγ _ hxb, (hs k).2.1 x hx b hb, h0 k, mul_zero, mul_zero]

  have hloc : ∀ x ∈ X.dom, (∀ k, s k x = 0) → ∀ᶠ y in 𝓝 x, (∀ k, s k y = 0) → S.r x y := by
    intro x hx h0
    obtain ⟨δ, hδ, hiso⟩ := isolated_of_det (hsimp x hx h0).2 (by
      ext k
      simp [cpt_origin, h0 k])
    filter_upwards [eventually_split X hx hδ] with y ⟨hy, z, hz, b, hb, he⟩ hy0
    have hR : S.r (cpt X x z) y := ⟨1, X.Γ.one_mem, b, hb, by rw [FundSetPf.lact_one]; exact he⟩
    have h1 := (hstab _ _ (S.iseqv.symm hR) ⟨hy, hy0⟩).2
    have hz0 : z = 0 := hiso z hz (by
      ext k
      simp [h1 k])
    rwa [hz0, cpt_origin] at hR
  have hK : IsCompact (C ∩ {x | ∀ k, s k x = 0}) := by
    have hcont : ContinuousOn (fun x k => s k x) C :=
      continuousOn_pi.2 fun k => (hs k).1.continuousOn.mono hCd
    have hcl := hcont.preimage_isClosed_of_isClosed hC.isClosed (isClosed_singleton (x := 0))
    have he : C ∩ {x | ∀ k, s k x = 0} = C ∩ (fun x k => s k x) ⁻¹' {0} := by
      ext x; simp [funext_iff]
    rw [he]
    exact hC.of_isClosed_subset hcl Set.inter_subset_left
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => {y | (∀ k, s k y = 0) → S.r x y})
    (fun x hx => hloc x (hCd hx.1) hx.2)
  set T : Finset (Quotient S) := t.image (Quotient.mk S) with hT
  have hout : ∀ q ∈ T, q.out ∈ X.dom ∧ ∀ k, s k q.out = 0 := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hq
    exact hstab x _ (S.iseqv.symm (Quotient.mk_out x)) ⟨hCd (htK x hx).1, (htK x hx).2⟩
  refine ⟨T.card, fun j => (T.equivFin.symm j).1.out, fun j => (hout _ (T.equivFin.symm j).2).1,
    fun x hx => ⟨fun h0 => ?_, ?_⟩, ?_⟩
  · obtain ⟨γ, hγ, b, hb, hc⟩ := hmeet x hx h0
    have hR : S.r x (lact γ (rmul x b)) := ⟨γ, hγ, b, hb, rfl⟩
    have h1 := (hstab _ _ hR ⟨hx, h0⟩).2
    obtain ⟨u, hu, hy⟩ := Set.mem_iUnion₂.1 (hcov ⟨hc, h1⟩)
    refine ⟨T.equivFin ⟨Quotient.mk S u, Finset.mem_image_of_mem _ hu⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact S.iseqv.trans (Quotient.mk_out u) (S.iseqv.trans (hy h1) (S.iseqv.symm hR))
  · rintro ⟨j, hj⟩
    exact (hstab _ x hj (hout _ (T.equivFin.symm j).2)).2
  · intro j j' γ hγ b hb h
    have hR : S.r (T.equivFin.symm j).1.out (T.equivFin.symm j').1.out := ⟨γ, hγ, b, hb, h⟩
    have := Quotient.sound (s := S) hR
    rw [Quotient.out_eq, Quotient.out_eq] at this
    exact T.equivFin.symm.injective (Subtype.ext this)

end GlobalTheory.FiniteZeroOrbits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsFiniteMeasureCoverUnitaryLatticeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.exists_finite_measure_cover_unitary_lattice : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure], ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∃ w ∈ Ω, ∀ τ : X.Ψ, (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (((w : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) := by
  first | exact @GlobalTheory.FiniteCovolume.exists_finite_measure_cover | exact GlobalTheory.FiniteCovolume.exists_finite_measure_cover | (intros; apply GlobalTheory.FiniteCovolume.exists_finite_measure_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsInvariantGe
section
namespace GlobalTheory.FinVolModes

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.CMTypeLowModes (IsInvariant TwoBounds PointBound NoModesBelow LowModes Inputs)

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def Covers (X : Data E r) (x y : Frame X.Ψ r) : Prop :=
  y ∈ X.dom ∧ X.la1 y = X.la1 x ∧ ∀ ξ, X.IsIso ξ → ∃ ξ', X.IsIso ξ' ∧ X.tt ξ' y = X.tt ξ x

theorem Covers.trans {X : Data E r} {x y z : Frame X.Ψ r} (h : Covers X x y) (h' : Covers X y z) :
    Covers X x z := by
  refine ⟨h'.1, h'.2.1.trans h.2.1, fun ξ hξ => ?_⟩
  obtain ⟨ξ1, h1, e1⟩ := h.2.2 ξ hξ
  obtain ⟨ξ2, h2, e2⟩ := h'.2.2 ξ1 h1
  exact ⟨ξ2, h2, e2.trans e1⟩

def hull (X : Data E r) (ps : Frame X.Ψ r → ℝ) (x : Frame X.Ψ r) : ℝ :=
  sSup (ps '' {y | Covers X x y})

end

end GlobalTheory.FinVolModes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.KaUnfoldOfUnfoldOfKappa
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem kaUnfold_of_unfold_of_kappa :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ ψ : Frame X.Ψ r → ℝ≥0∞, Measurable ψ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) → ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 = ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ bb : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → ∃ κ : Frame X.Ψ r → ℝ, Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → (KaUnfoldStatement (E := E)) := by
  intro hU hK r X x0 ho hP FF hFF bb hbb
  obtain ⟨κ, hκm, hκ1, hκB, hκka, ⟨C, hC, hsum⟩, -⟩ := hK r X x0 ho hP bb hbb
  refine ⟨C, hC, fun φ hφm hφB hφΓ => ?_⟩
  have h1 : ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * φ (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z, ENNReal.ofReal (κ (cpt X x0 z)) * φ (cpt X x0 z) ∂muF X x0 :=
    lintegral_congr_ae ((OntoH.ae_mem_Om X x0).mono fun z hz => by simp only [hκka z hz])
  have h2 := hU r X x0 ho FF hFF (fun x => ENNReal.ofReal (κ x) * φ x)
    (hκm.ennreal_ofReal.mul hφm) (fun x hx b hb => by simp only [hκB x hx b hb, hφB x hx b hb])
  rw [h1, h2, ← lintegral_const_mul' _ _ hC.ne]
  refine setLIntegral_mono' hFF.1 fun z hz => ?_
  have hx : cpt X x0 z ∈ X.dom := hFF.2.1 hz
  calc ∑' γ : X.Γ, ENNReal.ofReal (κ (lact γ.1 (cpt X x0 z))) * φ (lact γ.1 (cpt X x0 z))
      ≤ ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 (cpt X x0 z)))) * φ (cpt X x0 z) := by
        refine ENNReal.tsum_le_tsum fun γ => ?_
        rw [hφΓ γ.1 γ.2 _ hx]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        obtain ⟨h0, h1⟩ := hκ1 _ (OntoS.dom_lact X γ.2 hx)
        rw [Real.le_sqrt h0.le h0.le]
        nlinarith
    _ = (∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 (cpt X x0 z))))) * φ (cpt X x0 z) :=
        ENNReal.tsum_mul_right
    _ ≤ C * φ (cpt X x0 z) := mul_le_mul' (hsum _ hx) le_rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralLtTopOfCutoff
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.KronValue

theorem lintegral_ball_lt_top {n : ℕ} {Ω : Set (V n)} (hΩ : IsOpen Ω) {d w g H : V n → ℝ}
    (hd : ContinuousOn d Ω) (hdpos : ∀ z ∈ Ω, 0 < d z)
    (hw : ContinuousOn w Ω) (hwpos : ∀ z ∈ Ω, 0 < w z) {ρ : ℝ} (hρ : 0 < ρ)
    (hB : Metric.closedBall (0 : V n) ρ ⊆ Ω) (hg : ∀ z, 0 ≤ g z)
    (hH : ∀ z ∈ Metric.ball (0 : V n) ρ, H z = g z * w z)
    (hfin : ∫⁻ z, ENNReal.ofReal (H z)
      ∂((volume.restrict Ω).withDensity fun z => ENNReal.ofReal (d z)) < ⊤) :
    ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (g z) < ⊤ := by
  have hm : AEMeasurable (fun z => ENNReal.ofReal (d z)) (volume.restrict Ω) :=
    (hd.aemeasurable hΩ.measurableSet).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hfin
  obtain ⟨z0, hz0, hmin⟩ := (isCompact_closedBall (0 : V n) ρ).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self hρ.le⟩ ((hd.mul hw).mono hB)
  set c := d z0 * w z0 with hc
  have hcpos : 0 < c := mul_pos (hdpos _ (hB hz0)) (hwpos _ (hB hz0))
  have hsub : Metric.ball (0 : V n) ρ ⊆ Ω := Metric.ball_subset_closedBall.trans hB
  calc ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (g z)
      ≤ ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal c⁻¹ *
          ((fun z => ENNReal.ofReal (d z)) * fun z => ENNReal.ofReal (H z)) z := by
        refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
        have h1 : c ≤ d z * w z := hmin (Metric.ball_subset_closedBall hz)
        simp only [Pi.mul_apply]
        rw [← ENNReal.ofReal_mul (hdpos z (hsub hz)).le, ← ENNReal.ofReal_mul (inv_pos.2 hcpos).le,
          hH z hz]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [le_inv_mul_iff₀ hcpos]
        nlinarith [mul_le_mul_of_nonneg_right h1 (hg z)]
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ z in Metric.ball (0 : V n) ρ,
          ((fun z => ENNReal.ofReal (d z)) * fun z => ENNReal.ofReal (H z)) z :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((lintegral_mono_set hsub).trans_lt hfin)

theorem lintegral_lt_top_of_cutoff {n : ℕ} {Ω : Set (V n)} (hΩ : IsOpen Ω) {d w S : V n → ℝ}
    {χ F : V n → ℂ} (hd : ContinuousOn d Ω)
    (hw : ContinuousOn w Ω) (hwpos : ∀ z ∈ Ω, 0 < w z) {δ : ℝ}
    (hB : Metric.closedBall (0 : V n) δ ⊆ Ω) (hχ : Continuous χ) (hχ0 : ∀ z, δ ≤ ‖z‖ → χ z = 0)
    {M : ℝ} (hM : ∀ z ∈ Ω, S z ≤ M) (hS : ∀ᵐ z ∂(volume.restrict Ω), 0 < S z) {p : ℝ} (hp : 0 ≤ p)
    (hfin : ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * w z * S z ^ (-p))
      ∂((volume.restrict Ω).withDensity fun z => ENNReal.ofReal (d z)) < ⊤) :
    ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 * w z)
      ∂((volume.restrict Ω).withDensity fun z => ENNReal.ofReal (d z)) < ⊤ := by
  set μ := (volume.restrict Ω).withDensity fun z => ENNReal.ofReal (d z) with hμ
  have hK := isCompact_closedBall (0 : V n) δ
  have hKm : MeasurableSet (Metric.closedBall (0 : V n) δ) := hK.measurableSet
  have hμK : μ (Metric.closedBall 0 δ) < ⊤ := by
    rw [hμ, withDensity_apply _ hKm, Measure.restrict_restrict hKm, Set.inter_eq_left.2 hB]
    exact Integrable.lintegral_lt_top ((hd.mono hB).integrableOn_compact hK)
  obtain ⟨B, hBd⟩ := hK.exists_bound_of_continuousOn
    (f := fun z => 2 * (‖χ z‖ ^ 2 * w z))
    (continuousOn_const.mul ((hχ.norm.pow 2).continuousOn.mul (hw.mono hB)))
  have hac : μ ≪ volume.restrict Ω := withDensity_absolutelyContinuous _ _
  have hae : ∀ᵐ z ∂μ, ENNReal.ofReal (‖F z‖ ^ 2 * w z) ≤
      (Metric.closedBall (0 : V n) δ).indicator (fun _ => ENNReal.ofReal B) z +
        ENNReal.ofReal (2 * M ^ p) * ENNReal.ofReal (‖χ z - F z‖ ^ 2 * w z * S z ^ (-p)) := by
    filter_upwards [hac.ae_le hS, hac.ae_le (ae_restrict_mem hΩ.measurableSet)] with z hz hzΩ
    have hz : 0 < S z := hz
    have hzΩ : z ∈ Ω := hzΩ
    have hMpos : 0 < M := hz.trans_le (hM z hzΩ)
    have hwz := hwpos z hzΩ
    have h1 : ENNReal.ofReal (2 * (‖χ z‖ ^ 2 * w z)) ≤
        (Metric.closedBall (0 : V n) δ).indicator (fun _ => ENNReal.ofReal B) z := by
      by_cases hzK : z ∈ Metric.closedBall (0 : V n) δ
      · rw [Set.indicator_of_mem hzK]
        exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hBd z hzK))
      · have : δ ≤ ‖z‖ := by
          rw [mem_closedBall_zero_iff, not_le] at hzK; exact hzK.le
        simp [hχ0 z this]
    have h2 : 1 ≤ M ^ p * S z ^ (-p) := by
      rw [Real.rpow_neg hz.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hz p)]
      exact Real.rpow_le_rpow hz.le (hM z hzΩ) hp
    have h3 : ‖F z‖ ^ 2 ≤ 2 * ‖χ z‖ ^ 2 + 2 * ‖χ z - F z‖ ^ 2 := by
      have : ‖F z‖ ≤ ‖χ z‖ + ‖χ z - F z‖ := by
        simpa using norm_sub_le (χ z) (χ z - F z)
      nlinarith [norm_nonneg (F z), norm_nonneg (χ z), norm_nonneg (χ z - F z),
        sq_nonneg (‖χ z‖ - ‖χ z - F z‖)]
    have hA : 0 ≤ ‖χ z - F z‖ ^ 2 * w z := by positivity
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine le_trans ?_ (add_le_add_left h1 _)
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_add (by positivity)
      (mul_nonneg (by positivity) (mul_nonneg hA (Real.rpow_nonneg hz.le _)))).le
    nlinarith [mul_le_mul_of_nonneg_right h3 hwz.le, mul_le_mul_of_nonneg_right h2 hA]
  refine (lintegral_mono_ae hae).trans_lt ?_
  rw [lintegral_add_left (measurable_const.indicator hKm), lintegral_indicator_const hKm,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμK,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem pnorm_eq {r : ℕ} (X : Data E r) (L : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm L P x = ‖P x‖ * X.nfac L x := rfl

theorem value_and_integrability : (VanishAtSStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (la L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (ψ : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r) (bb ε δ : ℝ) (χ F : V (nd X) → ℂ), 0 < nd X → IsOrth X x0 → X.IsBddSec L w0 → (∀ k, X.IsBddSec L (s k)) → ContinuousOn ψ X.dom → (∃ C : ℝ, ∀ x ∈ X.dom, ψ x ≤ C) → 0 ≤ bb → 0 < ε → Metric.closedBall (0 : V (nd X)) δ ⊆ OmF X x0 → Continuous χ → (∀ z, ‖z‖ ≤ ε → χ z = 1) → (∀ z, δ ≤ ‖z‖ → χ z = 0) → DifferentiableOn ℂ F (OmF X x0) → ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z * (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X : ℝ))) ∂muF X x0 < ⊤ → w0 x0 ≠ 0 → (∀ k, s k x0 = 0) → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (x0) z) / w0 (cpt X (x0) z) : V (nd X))) 0).det ≠ 0 → F 0 = 1 ∧ InAt X x0 (X.dom.indicator fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) bb F ∧ ∀ C : Set (Frame X.Ψ r), IsCompact C → C ⊆ X.dom → ∫⁻ z in sat X x0 C, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ∂muF X x0 < ⊤) := by
  intro hV r X la L w0 s ψ x0 bb ε δ χ F hn ho hw0 hs hψ hψC hbb hε hB hχ hχ1 hχ0 hF hfin hw0x hsx hdet
  have hΩ := OntoB.isOpen_OmF X x0
  have h0 : (0 : V (nd X)) ∈ OmF X x0 := IW.zero_mem_OmF X x0 ho
  have hcpt : Continuous (cpt X x0) := (OntoB.cd_cpt X x0).continuous
  set w : V (nd X) → ℝ := fun z =>
    Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z with hwdef
  have hka : ∀ z, 0 < kaF X x0 bb z := fun z => Real.exp_pos _
  have hwpos : ∀ z ∈ OmF X x0, 0 < w z := fun z _ => div_pos (Real.exp_pos _) (hka z)
  have hw : ContinuousOn w (OmF X x0) := by
    have h1 := OntoE.expPhla_cont X x0 la
    have h2 : ContinuousOn (fun z => Real.exp (-ψ (cpt X x0 z))) (OmF X x0) :=
      Real.continuous_exp.comp_continuousOn (hψ.comp hcpt.continuousOn fun _ hz => hz).neg
    have h3 : ContinuousOn (kaF X x0 bb) (OmF X x0) := fun z hz =>
      (OntoB.ka_contDiffAt bb hz).continuousAt.continuousWithinAt
    refine ((h1.mul h2).div h3 fun z _ => (hka z).ne').congr fun z _ => ?_
    simp only [hwdef, Pi.div_apply, Pi.mul_apply]
    rw [← Real.exp_add, neg_add]
  have hfin' : ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * w z *
      (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X : ℝ))) ∂muF X x0 < ⊤ := by
    simpa only [hwdef, mul_div_assoc] using hfin
  have hS : ∀ z, ∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2 =
      (∑ k, ‖s k (cpt X x0 z)‖ ^ 2) * X.nfac L (cpt X x0 z) ^ 2 := fun z => by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [pnorm_eq, mul_pow]
  have hsd : ∀ k, DifferentiableOn ℂ (fun z => s k (cpt X x0 z)) (OmF X x0) := fun k =>
    OntoB.hol_comp X x0 (hs k).1.1
  have hmain : ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 * w z) ∂muF X x0 < ⊤ := by
    choose C hC using fun k => (hs k).2
    refine lintegral_lt_top_of_cutoff hΩ OntoB.densF_continuousOn hw hwpos hB hχ hχ0
      (M := ∑ k, C k ^ 2) (fun z hz => Finset.sum_le_sum fun k _ => ?_) ?_ (Nat.cast_nonneg _) hfin'
    · have hp : 0 ≤ X.pnorm L (s k) (cpt X x0 z) := by
        rw [pnorm_eq]; exact mul_nonneg (norm_nonneg _) (OntoE.nfac_pos X x0 hz).le
      exact pow_le_pow_left₀ hp (hC k _ hz) 2
    · obtain ⟨k, hk⟩ := HE.coord_ne_of_det hn hdet
      have hne : ∃ z ∈ OmF X x0, s k (cpt X x0 z) ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hk
        filter_upwards [hΩ.mem_nhds h0] with z hz
        simp [hall z hz]
      have hnull := OntoD.null_zero hΩ (OmFConnStatement_holds r X x0 ho) (hsd k) hne
      rw [ae_restrict_iff' hΩ.measurableSet]
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with z hz hzΩ
      have hsk : s k (cpt X x0 z) ≠ 0 := fun h => hz ⟨hzΩ, h⟩
      rw [hS]
      refine mul_pos ?_ (pow_pos (OntoE.nfac_pos X x0 hzΩ) 2)
      exact Finset.sum_pos' (fun _ _ => by positivity)
        ⟨k, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hsk) 2⟩
  have haeΩ : ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hΩ.measurableSet)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨Δ, zOf, bOf, -, -, -, -, -, hLU⟩ := lu_holds r X x0 ho
    have hz : ∀ z ∈ OmF X x0, zOf (cpt X x0 z) = z := fun z hz => by
      have := (hLU z hz _ (ExtFPf.oneF_mem X)).2.1
      rwa [ExtFPf.rmul_oneF] at this
    obtain ⟨ρ0, hρ0, hρB⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hΩ.mem_nhds h0)
    set ρ := min ρ0 ε
    have hρ : 0 < ρ := lt_min hρ0 hε
    have hcB : Metric.closedBall (0 : V (nd X)) ρ ⊆ OmF X x0 :=
      (Metric.closedBall_subset_closedBall (min_le_left _ _)).trans hρB
    have hbB : Metric.ball (0 : V (nd X)) ρ ⊆ OmF X x0 := Metric.ball_subset_closedBall.trans hcB
    have key := hV r X x0 hn ho (IW.orth_mem_dom X x0 ho) (fun y => 1 - F (zOf y)) w0 s ρ hρ
      (((differentiableOn_const (1 : ℂ)).sub (hF.mono hbB)).congr fun z hz' => by
        simp [hz z (hbB hz')])
      (fun k => (hsd k).mono hbB) ((OntoB.hol_comp X x0 hw0.1.1).mono hbB) hw0x hsx hdet ?_
    · have h00 : zOf x0 = 0 := by simpa [IW.cpt_zero] using hz 0 h0
      simp only [h00] at key
      exact (sub_eq_zero.1 key).symm
    · refine lintegral_ball_lt_top hΩ OntoB.densF_continuousOn (fun z => OntoB.densF_pos)
        (w := fun z => w z * (X.nfac L (cpt X x0 z) ^ 2) ^ (-(nd X : ℝ))) ?_ ?_ hρ hcB ?_ ?_ hfin'
      · exact hw.mul (((OntoE.nfac_cont X x0 L).pow 2).rpow_const fun z hz' =>
          Or.inl (pow_pos (OntoE.nfac_pos X x0 hz') 2).ne')
      · exact fun z hz' => mul_pos (hwpos z hz')
          (Real.rpow_pos_of_pos (pow_pos (OntoE.nfac_pos X x0 hz') 2) _)
      · intro z; positivity
      · intro z hz'
        have : ‖z‖ ≤ ε := (mem_ball_zero_iff.1 hz').le.trans (min_le_right _ _)
        rw [hS, Real.mul_rpow (by positivity) (by positivity), hχ1 z this, hz z (hbB hz')]
        ring
  · unfold InAt
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hmain
    filter_upwards [haeΩ] with z hz
    have hz' : cpt X x0 z ∈ X.dom := hz
    rw [Set.indicator_of_mem hz', ← ENNReal.ofReal_mul (div_nonneg (by positivity) (hka z).le)]
    congr 1
    simp only [hwdef]; ring
  · intro C _ _
    obtain ⟨A, hA⟩ := hψC
    refine (lintegral_mono' Measure.restrict_le_self le_rfl).trans_lt ?_
    refine lt_of_le_of_lt (lintegral_mono_ae (g := fun z => ENNReal.ofReal (Real.exp A) *
      ENNReal.ofReal (‖F z‖ ^ 2 * w z)) ?_) ?_
    · filter_upwards [haeΩ] with z hz
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      simp only [hwdef, kaF]
      rw [← Real.exp_sub, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      nlinarith [hA _ hz, mul_nonneg hbb (ExF.rhF_nonneg X x0 ho hz)]
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmain

end GlobalTheory.KronValue
end

