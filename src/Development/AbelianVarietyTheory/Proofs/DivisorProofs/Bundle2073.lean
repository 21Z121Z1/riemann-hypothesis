import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import ReciprocityTheory.SemistableReduction.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0150
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0125
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0890
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NullOfFiniteCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2055
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SumRangeBlocks
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockDetGe
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsMixedProj
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DivisionWithBasisOfDivision
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoinConvBdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0237
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0050
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0046
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2063
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCuspFormsDefiniteUnitaryFlagDom
section
set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.DefiniteFin

theorem finiteDimensional_span_of_slices (ι : Type) [Fintype ι] [DecidableEq ι] (A : ι → Type) (D : ∀ i, Set (A i))
    (W : ∀ i, Submodule ℂ (A i → ℂ)) (hW : ∀ i, FiniteDimensional ℂ (W i)) (Dom : Set (∀ i, A i))
    (hDom : Dom = Set.univ.pi D) (S : Set ((∀ i, A i) → ℂ))
    (hS : ∀ g ∈ S, ∀ x ∈ Dom, ∀ i, ∃ w ∈ W i, ∀ t ∈ D i, g (Function.update x i t) = w t) :
    FiniteDimensional ℂ (Submodule.span ℂ ((fun g : (∀ i, A i) → ℂ => fun x : Dom => g x) '' S)) := by
  subst hDom
  have hT : ∀ i, ∃ T : Set (A i), T ⊆ D i ∧ T.Finite ∧
      ∀ w ∈ W i, (∀ t ∈ T, w t = 0) → ∀ t ∈ D i, w t = 0 := by
    intro i
    let ev : A i → Module.Dual ℂ (W i) := fun t =>
      (LinearMap.proj t : (A i → ℂ) →ₗ[ℂ] ℂ).comp (W i).subtype
    obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent ℂ (ev '' D i)
    have hbfin : b.Finite := hli.setFinite
    obtain ⟨T, hTD, hTfin, hTb⟩ := Set.exists_subset_image_finite_and.1 ⟨b, hb, hbfin, rfl⟩
    refine ⟨T, hTD, hTfin, fun w hw h0 t ht => ?_⟩
    have hmem : ev t ∈ Submodule.span ℂ b := by
      rw [hspan]; exact Submodule.subset_span ⟨t, ht, rfl⟩
    have hall : ∀ φ ∈ Submodule.span ℂ b, φ ⟨w, hw⟩ = 0 := by
      intro φ hφ
      induction hφ using Submodule.span_induction with
      | mem φ hφ =>
        rw [hTb] at hφ
        obtain ⟨s, hs, rfl⟩ := hφ
        exact h0 s hs
      | zero => rfl
      | add φ ψ _ _ h1 h2 => simp [h1, h2]
      | smul c φ _ h => simp [h]
    exact hall _ hmem
  choose T hTD hTfin hTz using hT
  let G : Set (∀ i, A i) := Set.univ.pi T
  have hGfin : G.Finite := Set.Finite.pi (fun i => hTfin i)
  have hGD : G ⊆ Set.univ.pi D := Set.pi_mono (fun i _ => hTD i)
  let V : Submodule ℂ ((∀ i, A i) → ℂ) :=
    { carrier := {g | ∀ x ∈ Set.univ.pi D, ∀ i, ∃ w ∈ W i, ∀ t ∈ D i, g (Function.update x i t) = w t}
      add_mem' := by
        intro f g hf hg x hx i
        obtain ⟨w, hw, hfw⟩ := hf x hx i
        obtain ⟨w', hw', hgw⟩ := hg x hx i
        exact ⟨w + w', (W i).add_mem hw hw', fun t ht => by simp [hfw t ht, hgw t ht]⟩
      zero_mem' := by
        intro x hx i
        exact ⟨0, (W i).zero_mem, fun t ht => by simp⟩
      smul_mem' := by
        intro c f hf x hx i
        obtain ⟨w, hw, hfw⟩ := hf x hx i
        exact ⟨c • w, (W i).smul_mem c hw, fun t ht => by simp [hfw t ht]⟩ }
  have key : ∀ g ∈ V, (∀ x ∈ G, g x = 0) → ∀ x ∈ Set.univ.pi D, g x = 0 := by
    intro g hg h0
    have hs : ∀ s : Finset ι, ∀ x ∈ Set.univ.pi D, (∀ i ∉ s, x i ∈ T i) → g x = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro x _ hx; exact h0 x (fun i _ => hx i (Finset.notMem_empty i))
      | insert j s hj ih =>
        intro x hx hxT
        obtain ⟨w, hw, hgw⟩ := hg x hx j
        have hwT : ∀ t ∈ T j, w t = 0 := by
          intro t ht
          rw [← hgw t (hTD j ht)]
          apply ih
          · intro i _
            by_cases h : i = j
            · subst h; simpa using hTD i ht
            · simpa [h] using hx i trivial
          · intro i hi
            by_cases h : i = j
            · subst h; simpa using ht
            · simpa [h] using hxT i (by simp [h, hi])
        have h1 := hTz j w hw hwT (x j) (hx j trivial)
        rw [← h1, ← hgw (x j) (hx j trivial), Function.update_eq_self]
    intro x hx
    exact hs Finset.univ x hx (fun i hi => absurd (Finset.mem_univ i) hi)
  let resD : ((∀ i, A i) → ℂ) →ₗ[ℂ] (Set.univ.pi D → ℂ) := LinearMap.funLeft ℂ ℂ Subtype.val
  let resG : (Set.univ.pi D → ℂ) →ₗ[ℂ] (G → ℂ) := LinearMap.funLeft ℂ ℂ (Set.inclusion hGD)
  have hsub : Submodule.span ℂ ((fun g : (∀ i, A i) → ℂ => fun x : Set.univ.pi D => g x) '' S) ≤
      V.map resD := by
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, hS g hg, rfl⟩
  haveI : Finite G := hGfin.to_subtype
  have hinj : Function.Injective (resG.domRestrict (V.map resD)) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨φ, g, hg, rfl⟩ hφ
    rw [LinearMap.mem_ker] at hφ
    rw [Submodule.mem_bot]
    ext ⟨x, hx⟩
    have hz : ∀ y ∈ G, g y = 0 := by
      intro y hy
      have := congrFun (show resG (resD g) = 0 from hφ) ⟨y, hy⟩
      exact this
    exact key g hg hz x hx
  haveI : FiniteDimensional ℂ (V.map resD) := Module.Finite.of_injective _ hinj
  exact Submodule.finiteDimensional_of_le hsub

theorem finiteDimensional_cusp_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (X.p0 = 0 ∨ X.p0 = r) → ∀ la : Wt X.Ψ r,
      FiniteDimensional ℂ (Submodule.span ℂ ((fun f : Frame X.Ψ r → ℂ => fun x : X.dom => f x) '' X.SS la)) := by
  intro E _ _ _ r X hp la
  classical
  have hdom : ∀ x : Frame X.Ψ r, x ∈ X.dom ↔ ∀ τ, (mat x τ).det ≠ 0 := by
    intro x
    constructor
    · intro hx τ; exact (hx τ).1
    · intro hx τ; exact ⟨hx τ, GlobalTheory.T.re_dmin_sign_pos_of_definite E r X hp x τ (hx τ)⟩
  set N : ℕ := ∑ τ, ∑ i, (la τ i).natAbs with hN
  have hNle : ∀ τ i, 0 ≤ la τ i + N := by
    intro τ i
    have h1 : (la τ i).natAbs ≤ N := by
      calc (la τ i).natAbs ≤ ∑ i, (la τ i).natAbs :=
            Finset.single_le_sum (f := fun i => (la τ i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        _ ≤ N := Finset.single_le_sum (f := fun τ => ∑ i, (la τ i).natAbs) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ τ)
    omega
  let d : X.Ψ → ℕ := fun τ => ∑ i, (la τ i + N).toNat
  let ev : MvPolynomial (Fin r × Fin r) ℂ →ₗ[ℂ] ((Fin r → Fin r → ℂ) → ℂ) :=
    { toFun := fun F y => MvPolynomial.eval (fun ij => y ij.1 ij.2) F * ((Matrix.of y).det)⁻¹ ^ N
      map_add' := by intro F G; funext y; simp [add_mul]
      map_smul' := by intro c F; funext y; simp [mul_assoc] }
  let W : X.Ψ → Submodule ℂ ((Fin r → Fin r → ℂ) → ℂ) :=
    fun τ => (MvPolynomial.restrictTotalDegree (Fin r × Fin r) ℂ (d τ)).map ev
  have hW : ∀ τ, FiniteDimensional ℂ (W τ) := fun τ => inferInstance
  refine finiteDimensional_span_of_slices X.Ψ (fun _ => Fin r → Fin r → ℂ) (fun _ => {y | (Matrix.of y).det ≠ 0})
    W hW X.dom ?_ (X.SS la) ?_
  · ext x
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]
    exact hdom x
  · intro g hg x hx τ
    obtain ⟨F, hF, hFy⟩ := GlobalTheory.T.frameSection_slice_eq_poly_div_det_pow E r X hdom la N hNle g hg.1.1 x hx τ
    refine ⟨ev F, ⟨F, ?_, rfl⟩, fun t ht => hFy t ht⟩
    rw [SetLike.mem_coe, MvPolynomial.mem_restrictTotalDegree]
    exact hF.totalDegree_le

end GlobalTheory.DefiniteFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierInversionSchwartzAdelic
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

noncomputable section

namespace GlobalTheory.TamFourier

theorem fourier_inversion_tamagawa : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (κ : Type) [Fintype κ], ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ → ∀ Φ ∈ schA F κ, ∀ x, ∫ y, (∫ z, Φ z * ψ (z ⬝ᵥ y) ∂μ) * ψ (y ⬝ᵥ x) ∂μ = Φ (-x) := by
  intro F _ _ hF ψ hψ κ _ inst hB μ hμ Φ hΦ x
  have hFT : ∀ H ∈ schA F κ, (fun y : κ → AF F => ∫ z, H z * ψ (z ⬝ᵥ y) ∂μ) ∈ schA F κ :=
    GlobalTheory.T.adelicFourier_mem_schwartz_totallyReal F hF ψ hψ κ μ hμ.1
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hinst : inst = MeasurableSpace.pi := by
    rw [hB.measurable_eq]
    exact (Pi.borelSpace (ι := κ) (X := fun _ => AF F)).measurable_eq.symm
  subst hinst
  set N := Fintype.card κ
  let e : κ ≃ Fin N := Fintype.equivFin κ
  obtain ⟨lam, hlam⟩ := GlobalTheory.SWQ.exists_isLam F hF ψ hψ
  obtain ⟨ν, hν⟩ := GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one F
  let a : Fin N → F := fun _ => 1 / 2
  have hC : GlobalTheory.SWQ.Ctx ψ lam ν a := ⟨hF, hψ, hlam, hν, fun _ => by norm_num [a]⟩
  have hμeq := GlobalTheory.T.tamagawa_adelicHaar_eq_map_product_measure F κ N e ν hν μ hμ
  let T : (Fin N → AF F) ≃ₜ+ (κ → AF F) := GlobalTheory.PoissonReindex.reidx e
  let Tm : (Fin N → AF F) ≃ᵐ (κ → AF F) := T.toHomeomorph.toMeasurableEquiv
  have hTm : ∀ u, Tm u = T u := fun _ => rfl
  have key : ∀ (H : (κ → AF F) → ℂ) (y' : Fin N → AF F),
      ∫ z, H z * ψ (z ⬝ᵥ T y') ∂μ = GlobalTheory.SWQ.Fo ψ ν a (fun u => H (T u)) y' := by
    intro H y'
    have hm : μ = Measure.map Tm (GlobalTheory.SWQ.muV N ν) := hμeq
    rw [hm, integral_map_equiv]
    simp only [GlobalTheory.SWQ.Fo, hTm, a, GlobalTheory.PoissonReindex.Bd_half, T, GlobalTheory.PoissonReindex.dot_reidx]
  set G : (κ → AF F) → ℂ := fun y => ∫ z, Φ z * ψ (z ⬝ᵥ y) ∂μ with hG
  set Φ' : (Fin N → AF F) → ℂ := fun u => Φ (T u) with hΦ'
  have hG' : (fun u => G (T u)) = GlobalTheory.SWQ.Fo ψ ν a Φ' := funext fun u => key Φ u
  have hGG : (fun u => (∫ z, G z * ψ (z ⬝ᵥ T u) ∂μ)) = GlobalTheory.SWQ.Fo ψ ν a (GlobalTheory.SWQ.Fo ψ ν a Φ') := by
    rw [← hG']
    exact funext fun u => key G u
  have hΦs : Φ' ∈ schA F (Fin N) := GlobalTheory.PoissonReindex.mem_schA_reidx e hΦ
  have hGs : G ∈ schA F κ := hFT Φ hΦ
  have hGGs : (fun y : κ → AF F => ∫ z, G z * ψ (z ⬝ᵥ y) ∂μ) ∈ schA F κ := hFT G hGs
  have hD1 : GlobalTheory.SWQ.Decay Φ' := GlobalTheory.SchwartzDecay.decay_of_mem_schA F N Φ' hΦs
  have hD2 : GlobalTheory.SWQ.Decay (GlobalTheory.SWQ.Fo ψ ν a Φ') := by
    rw [← hG']
    exact GlobalTheory.SchwartzDecay.decay_of_mem_schA F N _ (GlobalTheory.PoissonReindex.mem_schA_reidx e hGs)
  have hD3 : GlobalTheory.SWQ.Decay (GlobalTheory.SWQ.Fo ψ ν a (GlobalTheory.SWQ.Fo ψ ν a Φ')) := by
    rw [← hGG]
    exact GlobalTheory.SchwartzDecay.decay_of_mem_schA F N _ (GlobalTheory.PoissonReindex.mem_schA_reidx e hGGs)
  have hinv := GlobalTheory.SWQ.fourier_inversion F N ψ lam ν a hC Φ' hD1 hD2 hD3
  have hx : T (T.symm x) = x := T.apply_symm_apply x
  have h1 := congrFun hGG (T.symm x)
  rw [hinv, hx] at h1
  have hcomm : ∀ y : κ → AF F, y ⬝ᵥ x = x ⬝ᵥ y := fun y => dotProduct_comm y x
  calc ∫ y, G y * ψ (y ⬝ᵥ x) ∂μ = ∫ z, G z * ψ (z ⬝ᵥ x) ∂μ := rfl
    _ = GlobalTheory.SWQ.Da (-1) Φ' (T.symm x) := h1
    _ = Φ (-x) := by
      simp only [GlobalTheory.SWQ.Da, hΦ', neg_one_smul, map_neg, hx]

end GlobalTheory.TamFourier

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeBallCentreInterpolationDetWeightSmallSignatu
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

section
open ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.OrbitInterpSmall

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sum_bound {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (h0 : IsOrth X x0) (hPD : PropDisc X)
    (hp0 : 0 < X.p0) (hp1 : X.p0 < r) (hq : X.p0 * (r - X.p0) ≤ 3) {s : ℝ} (hs : 2 * ((r : ℝ) - 1) ≤ s) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x, IsOrth X x →
      ∑' γ : X.Γ, ENNReal.ofReal (Real.exp (-(s * GlobalTheory.Up.rhX X x0 (lact γ.1 x)))) ≤ C := by
  have hr : (2 : ℝ) ≤ r := by exact_mod_cast (show 2 ≤ r by omega)
  exact GlobalTheory.T.orbitSum_exp_potential_uniform_bound E r X x0 h0 hPD s (by linarith) (GlobalTheory.T.exists_uniform_bound_lintegral_flagDomain_ball_case E r X hp0 hp1 hq s hs)

theorem kappa_exists {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (h0 : IsOrth X x0) (hPD : PropDisc X)
    (hp0 : 0 < X.p0) (hp1 : X.p0 < r) (hq : X.p0 * (r - X.p0) ≤ 3) {bb : ℝ}
    (hbb : 4 * ((r : ℝ) - 1) ≤ bb) (hb0 : 0 < bb) :
    ∃ κ : Frame X.Ψ r → ℝ, Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧
      (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧
      (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧
      (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom,
        ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧
      ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x := by
  obtain ⟨hm, hpos, hinv, hch⟩ := GlobalTheory.FramePotential.frame_potential_basic r X x0 h0
  obtain ⟨C, hC, hS⟩ := sum_bound X x0 h0 hPD hp0 hp1 hq (s := bb / 2) (by linarith)
  refine GlobalTheory.kaFrame_of_delta X x0 bb hb0 _ (fun x => Finset.prod_nonneg fun τ _ => by positivity)
    hm hpos hinv hch (GlobalTheory.MinorRatioNear.minorRatio_near r X x0 h0) ⟨C, hC, fun x hx => ?_⟩
  refine le_trans (le_of_eq (tsum_congr fun γ => ?_)) (hS x hx)
  have hy : lact γ.1 x ∈ X.dom := MajInv.lact_mem_dom X (X.Γ_stab γ.1 γ.2) (IW.orth_mem_dom X x hx)
  congr 1
  rw [← GlobalTheory.Up.exp_neg_rhX h0 hy, ← Real.exp_mul]
  congr 1; ring

open GlobalTheory.Up.OrbitInterpolation in

theorem orbitInterp_small {r : ℕ} (X : Data E r) (G : Subgroup (GL (Fin r) E)) (x0 : Frame X.Ψ r)
    (la : Wt X.Ψ r) (ρ0 bb m : ℝ) (hPD : PropDisc X) (h0 : IsOrth X x0) (hd : 1 ≤ dimX X)
    (hp0 : 0 < X.p0) (hp1 : X.p0 < r) (hq : X.p0 * (r - X.p0) ≤ 3) (hρ0 : 0 < ρ0)
    (hG : FreeBall X G x0 ρ0) (hla : BlockConst X la)
    (hbb : 4 * ((r : ℝ) - 1) ≤ bb) (hb0 : 0 < bb) (hm : bb + dimX X / ρ0 < m)
    (hcurv : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ)
    (hSS : ∀ P, X.IsBddSec la P → P ∈ X.SS la) :
    ∃ u0 ∈ X.SS la, u0 x0 ≠ 0 ∧ ∀ γ ∈ G, γ ∉ X.Γ → u0 (lact γ x0) = 0 := by
  classical
  have hN : NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E) :=
    ⟨normFactor_rightBorel_holds, normFactor_leftAction_holds, pointwiseNorm_invariance_holds⟩
  have hbb0 : 0 ≤ bb := hb0.le
  obtain ⟨κ, hκm, hκ1, hκB, hκF, ⟨Cs, hCs, hsum⟩, hloc⟩ := kappa_exists X x0 h0 hPD hp0 hp1 hq hbb hb0
  have hsumE := sum_bound X x0 h0 hPD hp0 hp1 hq (s := bb / 2) (by linarith)
  obtain ⟨-, hW, hWl⟩ := KronMetric.kronMetric hN r X la (fun _ => 0) (fun _ _ _ _ _ _ => rfl)
    (fun _ _ => contDiffOn_const) ⟨0, fun _ _ => le_rfl⟩
  obtain ⟨⟨hz, hadd, hsmul⟩, -⟩ := siegelSpaceAlgebra_holds r X la la 0
  let S : Submodule ℂ (Frame X.Ψ r → ℂ) :=
    { carrier := X.SS la
      add_mem' := fun {P Q} hP hQ => hadd P hP Q hQ
      zero_mem' := hz
      smul_mem' := fun a P hP => hsmul a P hP }
  obtain ⟨T, hT⟩ := X.Γ_index
  have hx0 := IW.orth_mem_dom X x0 h0
  obtain ⟨u, hu, hu1, hu0⟩ := exists_of_approx S x0
    (fun s : {s : T // s.1⁻¹ ∈ G ∧ s.1⁻¹ ∉ X.Γ} => lact s.1.1⁻¹ x0) fun η hη => by
    have hη' : 0 < η / (Cs.toReal + 1) := by positivity
    obtain ⟨F, P, hF, hIn, hP, hPF, hP1, hP0⟩ := exists_approx hN extFStatement_holds measInv_holds
      GlobalTheory.PoleExistence.poleEx_holds (GlobalTheory.PoleDbar.poleSolve measInv_holds)
      GlobalTheory.Up.polePoint_holds h0 hd hρ0 hG hla hbb0 hm hcurv hκm hκ1 hκB hκF hloc hη'
    obtain ⟨hs, hbd⟩ := GlobalTheory.PoinSumBound.poin_conv_bdd E r X x0 h0 hPD la _ bb hW hWl hb0 hsumE F P hF hIn hP hPF
    have hn : ∀ (γ : X.Γ) (y : Frame X.Ψ r), ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 y)‖ = ‖P (lact γ.1 y)‖ :=
      fun γ y => by rw [norm_mul, norm_inv, OntoE.chi_norm X la γ.2, inv_one, one_mul]
    have he : η / (Cs.toReal + 1) + η / (Cs.toReal + 1) * Cs.toReal = η := by field_simp; ring
    refine ⟨poin X la P, hSS _ hbd, ?_, fun s => ?_⟩
    · have hs0 := hs x0 hx0
      unfold poin
      rw [hs0.of_norm.tsum_eq_add_tsum_ite 1]
      simp only [OneMemClass.coe_one, chi_one, FundSetPf.lact_one, inv_one, one_mul]
      have hle : ∀ γ : X.Γ, ‖if γ = 1 then 0 else (X.χ la γ.1)⁻¹ * P (lact γ.1 x0)‖ ≤
          ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x0)‖ := fun γ => by
        split_ifs
        · rw [norm_zero]; exact norm_nonneg _
        · exact le_rfl
      have hs1 := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs0
      have h2 := (norm_tsum_le_tsum_norm hs1).trans (tsum_le_of_le hs1 (fun _ => norm_nonneg _) hη'.le
        (fun γ => by
          split_ifs with h
          · rw [norm_zero]; positivity
          · rw [hn]
            exact hP0 γ.1 (hG.1 γ.2) fun h' => h (Subtype.ext h')) hCs (hsum x0 hx0))
      rw [add_sub_right_comm, ← he]
      exact (norm_add_le _ _).trans (add_le_add hP1 h2)
    · have hy := MajInv.lact_mem_dom X (hG.isUStab s.2.1) hx0
      have h2 := (norm_tsum_le_tsum_norm (hs _ hy)).trans (tsum_le_of_le (hs _ hy)
        (fun _ => norm_nonneg _) hη'.le
        (fun γ => by
          rw [hn, ← FundSetPf.lact_mul]
          refine hP0 _ (G.mul_mem (hG.1 γ.2) s.2.1) fun h => s.2.2 ?_
          rw [eq_inv_of_mul_eq_one_right h]
          exact X.Γ.inv_mem γ.2) hCs (hsum _ hy))
      exact h2.trans (by linarith)
  refine ⟨u, hu, by rw [hu1]; exact one_ne_zero, fun γ hγ hγ' => ?_⟩
  obtain ⟨s, hsT, hs⟩ := hT γ⁻¹ (hG.isUStab (G.inv_mem hγ))
  have e : s⁻¹ = (s⁻¹ * γ⁻¹) * γ := by group
  have e' : γ = (s⁻¹ * γ⁻¹)⁻¹ * s⁻¹ := by group
  have h1 : s⁻¹ ∈ G := by rw [e]; exact G.mul_mem (hG.1 hs) hγ
  have h2 : s⁻¹ ∉ X.Γ := fun h => hγ' (by rw [e']; exact X.Γ.mul_mem (X.Γ.inv_mem hs) h)
  have h3 : u (lact s⁻¹ x0) = 0 := hu0 ⟨⟨s, hsT⟩, h1, h2⟩
  have hu' : u ∈ X.SS la := hu
  rw [e', FundSetPf.lact_mul, hu'.1.1.2.2 _ (X.Γ.inv_mem hs) _
    (MajInv.lact_mem_dom X (hG.isUStab h1) hx0), h3, mul_zero]

end GlobalTheory.Up.OrbitInterpSmall
end

namespace GlobalTheory.Up.OrbitInterpSmall

theorem gapsPairing_deMul' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (h0 : 0 < X.p0) (h1 : X.p0 < r) {s : ℕ} (hs : Even s) :
    GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction.GapsPairing X (deMul X.Ψ r X.p0 s - kapW X) ((s : ℝ) - 2 * r + 2) := by
  obtain ⟨k, rfl⟩ := hs
  have hk : (k + k) / 2 = k := by omega
  intro τ
  refine ⟨fun i j hj hp => ?_, fun i0 i1 h0' h1' => ?_⟩
  · have e : ((j : ℕ) < X.p0 ↔ (i : ℕ) < X.p0) := by omega
    have hj' : ((j : ℕ) : ℤ) = (i : ℕ) + 1 := by exact_mod_cast hj
    simp only [Pi.sub_apply, deMul, kapW, hj']
    by_cases hi : (i : ℕ) < X.p0
    · rw [if_pos (e.2 hi), if_pos hi]; omega
    · rw [if_neg (mt e.1 hi), if_neg hi]; omega
  · simp only [Pi.sub_apply, deMul, kapW, h0', h1', hk]
    rw [if_pos h0, if_neg (by omega)]
    have hr : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
    rw [hr]
    push_cast
    linarith

theorem orbit_interp_small : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (∀ la, ∀ γ ∈ X.Γ, X.χ la γ = 1) → ∀ (G : Subgroup (GL (Fin r) E)) (x0 : Frame X.Ψ r), IsOrth X x0 →
    GlobalTheory.Up.FreeBall X G x0 (1 / (49 * (r : ℝ) ^ 2)) → 0 < X.p0 → X.p0 < r → X.p0 * (r - X.p0) ≤ 3 →
    ∀ s : ℕ, Even s → 2 * r + 50 * r ^ 2 * (X.Ψ.card * (X.p0 * (r - X.p0))) + 1 ≤ s →
    ∃ P ∈ X.SS (deMul X.Ψ r X.p0 s), P x0 ≠ 0 ∧ ∀ γ ∈ G, γ ∉ X.Γ → P (lact γ x0) = 0 := by
  intro E _ _ _ r X _ G x0 hx0 hFB h0 h1 hq s hs hsb
  have hd : 1 ≤ GlobalTheory.Up.dimX X := (GlobalTheory.Up.one_le_dimX_iff X).2 ⟨h0, h1⟩
  have hD : GlobalTheory.Up.dimX X = X.Ψ.card * (X.p0 * (r - X.p0)) := rfl
  have hc : 0 < X.Ψ.card := by
    rcases Nat.eq_zero_or_pos X.Ψ.card with h | h
    · rw [hD, h, zero_mul] at hd; omega
    · exact h
  obtain ⟨τ, hτ⟩ := Finset.card_pos.1 hc
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (h0.trans h1)
  have hρ : (0 : ℝ) < 1 / (49 * (r : ℝ) ^ 2) := by positivity
  have hdR : (1 : ℝ) ≤ GlobalTheory.Up.dimX X := by exact_mod_cast hd
  have hsR : 2 * (r : ℝ) + 50 * (r : ℝ) ^ 2 * (GlobalTheory.Up.dimX X : ℝ) + 1 ≤ s := by
    rw [hD]; exact_mod_cast hsb
  have hq1 : (GlobalTheory.Up.dimX X : ℝ) / (1 / (49 * (r : ℝ) ^ 2)) = 49 * (r : ℝ) ^ 2 * GlobalTheory.Up.dimX X := by
    field_simp
  have hcurv := (GlobalTheory.DivisionVolume.margin_iff h0 h1 (deMul X.Ψ r X.p0 s) ((s : ℝ) - 2 * r + 2)).2
    (gapsPairing_deMul' X h0 h1 hs) x0 hx0
  refine orbitInterp_small X G x0 _ _ (4 * ((r : ℝ) - 1) + 1 / 2) ((s : ℝ) - 2 * r + 2)
    (GlobalTheory.ClosedDiscontinuity.propDisc_closed r X) hx0 hd h0 h1 hq hρ hFB
    (fun _ _ _ h => if_congr h rfl rfl) (by linarith) (by linarith)
    (by rw [hq1]; nlinarith [mul_le_mul_of_nonneg_left hdR (sq_nonneg (r : ℝ)), sq_nonneg ((r : ℝ) - 2)])
    hcurv ?_
  refine cuspStatement_holds r X _ ⟨τ, hτ⟩ h0 h1 (fun i j hj hp => ?_) (fun i0 i1 h0' h1' => ?_)
  · have e : ((j : ℕ) < X.p0 ↔ (i : ℕ) < X.p0) := by omega
    simp only [deMul]
    by_cases hi : (i : ℕ) < X.p0
    · rw [if_pos (e.2 hi), if_pos hi]
    · rw [if_neg (mt e.1 hi), if_neg hi]
  · simp only [deMul]
    rw [if_pos (by omega), if_neg (by omega)]
    omega

end GlobalTheory.Up.OrbitInterpSmall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionModelEverywhere
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory.FlatDegreeCompare

theorem hasModel_of_goodAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (k : Type) [Field k] [NumberField k] (j : c.F →+* k) (o : Obj D l (baseKA l) (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom)), 1 ≤ D.p + D.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → ∀ 𝔭 : HeightOneSpectrum (𝓞 k), HasModel o.t 𝔭 := by
  intro E _ _ _ H D l c k _ _ j o e hg hA 𝔭
  obtain ⟨Xo⟩ := Moduli.moduli_scheme_exists E H D l e
  obtain ⟨f, ⟨hf, ⟨m⟩⟩, -⟩ := Xo.rep _ _ inferInstance o
  obtain ⟨Y⟩ := (GlobalTheory.Reg.modelAt_and_nonempty_global_model E H D l Xo c e hg hA).2
  let y : Sp k ⟶ Xo.XF c := pullback.lift f (spMap j) hf
  have hy : y ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  let oV : 𝓞 c.F →+* AdelicDegreeTameRamification.valRing k 𝔭 :=
    (j.comp (algebraMap (𝓞 c.F) c.F)).codRestrict (AdelicDegreeTameRamification.valRing k 𝔭) fun a =>
      𝔭.valuation_le_one (K := k) (RingOfIntegers.mapRingHom j a)
  obtain ⟨⟨yt, ⟨-, hyt⟩, -⟩, h⟩ := ValuativeExtension.valuation_extension E H D l Xo c _ _ Y
    (AdelicDegreeTameRamification.valRing k 𝔭) k oV j y rfl (pullback.lift_snd _ _ _)
  obtain ⟨G, ⟨n⟩⟩ := h yt
  obtain ⟨m₁, -⟩ := ObjMaps.exists_sab_cancel (g := y) Y.m0.toSABMap (hy ▸ m.toSABMap)
  obtain ⟨m₂, -⟩ := ObjMaps.exists_sab_comp Y.m m₁
  obtain ⟨m₃, -⟩ := ObjMaps.exists_sab_cancel (g := spMap (algebraMap (AdelicDegreeTameRamification.valRing k 𝔭) k)) n (hyt ▸ m₂)
  exact ⟨G.G, inferInstance, m₃.φ, G.semi, m₃.cart⟩

end GlobalTheory.FlatDegreeCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAnisotropicRallis
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)
open GlobalTheory.Core.Rk.IP in

theorem GlobalTheory.RallisBottom.heckeFormAniso_all_of_hypotheses : GlobalTheory.FunPr.Hypotheses₂ → ∀ D : D7, GlobalTheory.RallisBottom.HeckeFormAniso D := by
  intro hP D
  have hU19 := GlobalTheory.T.unramifiedDoublingIntegral_inert_place
  have hPB := paramBoundOn_all_of_split_inert D (GlobalTheory.T.sphericalParameterBound_split_place D) (GlobalTheory.T.sphericalParameterBound_nonsplit_places hU19 D)
  have hLZ := localZetaOn_all_of_split_inert D (GlobalTheory.T.unramifiedDoublingIntegral_splitPlace_adelic hP.unramifiedDoublingGL D)
    (GlobalTheory.T.unramified_doubling_integral_inert_adelic hU19 D (GlobalTheory.T.sphericalParameterBound_nonsplit_places hU19 D))
  have hE : EulerRight D :=
    GlobalTheory.T.doubling_eulerProduct_farRight hP.cuspRapidDecay D (GlobalTheory.T.doublingSphericalFactorization_of_weilDualPair hP.weilRepresentationUnitaryPair D) hLZ hPB
  have hG : GlobalTheory.BottomRallis.GlobalFormAniso D :=
    GlobalTheory.T.siegelWeil_anisotropic_global_form_of_doubling hP.weilRepresentationUnitaryPair hP.cuspRapidDecay hP.doublingMethod D
      (GlobalTheory.BottomRallis.siegelWeilFockAniso_of_siegelWeilAnisotropic hP.siegelWeilAnisotropicUnitary D)
  exact GlobalTheory.BottomRallis.heckeFormAniso_of_global_euler D hG hE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDescentEstimateStatement
section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_descent_estimate : DesPol := by
  first | exact @GlobalTheory.BigTop.Fun.desPol | exact GlobalTheory.BigTop.Fun.desPol | (intros; apply GlobalTheory.BigTop.Fun.desPol <;> assumption)
end

