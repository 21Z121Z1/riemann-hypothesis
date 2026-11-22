import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0007
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0114
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0115

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerIntegralToIntegralCoordinatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerIntegral_to_integral_coordinates : ∀ (X U Y : Type) [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace Y] (G : Type) [MeasurableSpace G] (ν : Measure X) (νU : Measure U) (μ : Measure Y) [SFinite νU] [SFinite μ] (i : X → G) (p : U → Y → G) (Inv : (G → G) → Prop), Measurable i → Measurable (Function.uncurry p) → ∀ (Dom : Set G), (∀ f : G → ENNReal, Measurable f → (∀ t, Inv t → ∀ n ∈ Dom, f (t n) = f n) → ∫⁻ x, f (i x) ∂ν = ∫⁻ u, ∫⁻ y, f (p u y) ∂μ ∂νU) → ∀ f : G → ℂ, Measurable f → (∀ t, Inv t → ∀ n ∈ Dom, f (t n) = f n) → Integrable (fun x => f (i x)) ν → Integrable (fun q : U × Y => f (p q.1 q.2)) (νU.prod μ) ∧ ∫ x, f (i x) ∂ν = ∫ u, ∫ y, f (p u y) ∂μ ∂νU := by
  first | exact @GlobalTheory.lowerIntegral_to_integral_coords | exact GlobalTheory.lowerIntegral_to_integral_coords | (intros; apply GlobalTheory.lowerIntegral_to_integral_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanValueIneqRightTranslateRealPointNearOne
section
noncomputable section

namespace GlobalTheory.CuspGeo.MeanValue

section Abstract

open GlobalTheory.SmoothForms

variable {L G ι : Type} [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] [Fintype ι]

theorem norm_sub_le (e : L → G) (he0 : e 0 = 1) (he : ∀ (Z : L) (s t : ℝ), e ((s + t) • Z) = e (s • Z) * e (t • Z))
    (b : Module.Basis ι ℝ L) {φ : G → ℂ} (hφ : Sm e φ) (g : G) (Z : L) (a : ℝ) (ha : ∀ i, |b.repr Z i| ≤ a) (c : ι → ℝ)
    (hc : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Der e (b i) φ (g * e (t • Z))‖ ≤ c i) :
    ‖φ (g * e Z) - φ g‖ ≤ a * ∑ i, c i := by
  have hc0 : ∀ i, 0 ≤ c i := fun i => (norm_nonneg _).trans (hc i 0 ⟨le_refl 0, zero_le_one⟩)

  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => φ (g * e (s • Z)))
      (fderiv ℝ (fun X : L => φ (g * e (t • Z) * e X)) ((t - t) • Z) Z) t := by
    intro t
    have hF : Differentiable ℝ (fun X : L => φ (g * e (t • Z) * e X)) :=
      (hφ (g * e (t • Z))).differentiable (by simp)
    have h1 : HasDerivAt (fun s : ℝ => (s - t) • Z) ((1 : ℝ) • Z) t :=
      ((hasDerivAt_id' t).sub_const t).smul_const Z
    rw [one_smul] at h1
    have h2 := (hF ((t - t) • Z)).hasFDerivAt.comp_hasDerivAt t h1
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show φ (g * e (s • Z)) = φ (g * e (t • Z) * e ((s - t) • Z))
    rw [mul_assoc, ← he, show t + (s - t) = s by ring]

  have key : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fun X : L => φ (g * e (t • Z) * e X)) 0 Z‖ ≤ a * ∑ i, c i := by
    intro t ht
    set F' := fderiv ℝ (fun X : L => φ (g * e (t • Z) * e X)) 0 with hF'
    have hZ : F' Z = ∑ i, b.repr Z i • F' (b i) := by
      have : F' Z = F' (∑ i, b.repr Z i • b i) := by rw [b.sum_repr]
      rw [this, map_sum]
      simp only [map_smul]
    rw [hZ, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    have hi : ‖F' (b i)‖ ≤ c i := by
      have := hc i t ht
      rwa [DerLinear.der_eq_fderiv hφ] at this
    exact mul_le_mul (ha i) hi (norm_nonneg _) ((abs_nonneg _).trans (ha i))
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s : ℝ => φ (g * e (s • Z))) (fun t _ => (hderiv t).hasDerivWithinAt)
    (fun t ht => by
      rw [sub_self, zero_smul]
      exact key t (Set.Ico_subset_Icc_self ht))
  simpa [he0] using hmv

theorem exists_coord_bound (b : Module.Basis ι ℝ L) : ∃ K : ℝ, 0 ≤ K ∧ ∀ Z i, |b.repr Z i| ≤ K * ‖Z‖ := by
  have : FiniteDimensional ℝ L := Module.Finite.of_basis b
  let f : ι → L →L[ℝ] ℝ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  refine ⟨∑ i, ‖f i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun Z i => ?_⟩
  have h1 : |b.repr Z i| = ‖f i Z‖ := by
    simp [f, Real.norm_eq_abs]
  rw [h1]
  exact ((f i).le_opNorm Z).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => norm_nonneg (f j)) (Finset.mem_univ i)) (norm_nonneg Z))

end Abstract

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem expInf_zero (R : RealPoints θ V) : expInf θ V 0 = 1 := by
  have hE := isExpFam_expInf R
  refine R.2.2.1 _ (hE (0 : LieN V)).1 _ (GinfC V).one_mem fun τ => ?_
  rw [(hE (0 : LieN V)).2 τ, R.2.2.2.2.1 1 (GfC V).one_mem τ]
  show NormedSpace.exp (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ) = 1
  exact NormedSpace.exp_zero

theorem expInf_add (R : RealPoints θ V) (Z : LieN V) (s t : ℝ) :
    expInf θ V ((s + t) • Z) = expInf θ V (s • Z) * expInf θ V (t • Z) := by
  have hE := isExpFam_expInf R
  refine R.2.2.1 _ (hE ((s + t) • Z)).1 _ (mul_mem (hE (s • Z)).1 (hE (t • Z)).1) fun τ => ?_
  rw [R.2.2.2.1, (hE ((s + t) • Z)).2 τ, (hE (s • Z)).2 τ, (hE (t • Z)).2 τ]
  show NormedSpace.exp ((s + t) • (Z τ).1) = NormedSpace.exp (s • (Z τ).1) * NormedSpace.exp (t • (Z τ).1)
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl (Z τ).1).smul_right t).smul_left s)

theorem continuous_expInf (hθ : IsInfFam θ) (R : RealPoints θ V) : Continuous (expInf θ V) := by
  have H := isLieData R
  have h1 : Continuous fun X : LieN V => NormedSpace.exp (jInf V X) :=
    (DerLinear.contDiff_exp H).continuous
  exact (GlobalTheory.Mem.DerClosed.continuousOn_secInf hθ V).comp_continuous h1 fun X => DerLinear.exp_unitary H X

open Classical in

theorem exists_basis (V : HSp D) : ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ (LieN V)) (p : ι → D.what₂.Tau)
    (X : ∀ i, LieAt V (p i)), ∀ i, b i = atPlace V (p i) (X i) := by
  refine ⟨Σ τ, Fin (Module.finrank ℝ (lieU (gramAt D V τ)).toSubmodule), inferInstance,
    Pi.basis fun τ => Module.finBasis ℝ (lieU (gramAt D V τ)).toSubmodule, fun i => i.1,
    fun i => ⟨(Module.finBasis ℝ (lieU (gramAt D V i.1)).toSubmodule i.2).1,
      (Module.finBasis ℝ (lieU (gramAt D V i.1)).toSubmodule i.2).2⟩, fun i => ?_⟩
  exact (Pi.basis_apply _ i).trans rfl

section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem norm_lieN_le (Z : LieN V) {r : ℝ} (hr : 0 ≤ r) (h : ∀ τ i j, ‖(Z τ).1 i j‖ ≤ r) : ‖Z‖ ≤ r := by
  refine (pi_norm_le_iff_of_nonneg hr).2 fun τ => ?_
  rw [Submodule.coe_norm]
  exact (Matrix.norm_le_iff hr).2 (h τ)

end

theorem exists_log (hθ : IsInfFam θ) (R : RealPoints θ V) : ∃ δ₁ C : ℝ, 0 < δ₁ ∧ 0 ≤ C ∧
    ∀ (u : GA D V) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → CloseR θ V u δ → ∃ Z : LieN V, expInf θ V Z = u ∧ ‖Z‖ ≤ C * δ := by
  have hG : ∀ τ, IsUnit (gramAt D V τ).det := fun τ => (R.1 τ).2
  choose δτ Cτ hδτ hτ using fun τ => GlobalTheory.T.exists_log_near_one_unitaryGroup_of_form_linear_bound V.rank (gramAt D V τ) (hG τ)
  obtain ⟨δ₁, hδ₁, hle⟩ : ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ τ, δ₁ ≤ δτ τ := by
    rcases isEmpty_or_nonempty D.what₂.Tau with h | h
    · exact ⟨1, one_pos, fun τ => (IsEmpty.false τ).elim⟩
    · obtain ⟨τ₀, hτ₀⟩ := Finite.exists_min δτ
      exact ⟨δτ τ₀, hδτ τ₀, hτ₀⟩
  have hC : ∀ τ, Cτ τ ≤ ∑ τ', |Cτ τ'| := fun τ =>
    (le_abs_self _).trans (Finset.single_le_sum (fun τ' _ => abs_nonneg (Cτ τ')) (Finset.mem_univ τ))
  refine ⟨δ₁, ∑ τ, |Cτ τ|, hδ₁, Finset.sum_nonneg fun τ _ => abs_nonneg _, fun u δ hδ hδle hu => ?_⟩

  have hX : ∀ τ, ∃ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 ∧
      NormedSpace.exp X = infMat D.sp.cm.sig V.gram (θ τ) u ∧ ∀ i j, ‖X i j‖ ≤ Cτ τ * δ := fun τ =>
    hτ τ _ δ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V u τ) (hδle.trans (hle τ)) (hu.2 τ)
  choose X hXl hXe hXn using hX
  let Z : LieN V := fun τ => ⟨X τ, (mem_lieAt_iff τ (X τ)).1 (hXl τ)⟩
  refine ⟨Z, ?_, ?_⟩
  · have hE := isExpFam_expInf R
    refine R.2.2.1 _ (hE Z).1 _ hu.1 fun τ => ?_
    rw [(hE Z).2 τ]
    exact hXe τ
  · refine norm_lieN_le Z (mul_nonneg (Finset.sum_nonneg fun τ _ => abs_nonneg _) hδ) fun τ i j => ?_
    exact (hXn τ i j).trans (mul_le_mul_of_nonneg_right (hC τ) hδ)

theorem mean_value : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ V : HSp D, ∃ (B : Finset (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (Ω : Set (GA D V)) (C δ₁ : ℝ), (∀ p ∈ B, p.2 ∈ lieAt V p.1) ∧ IsCompact Ω ∧ 0 < δ₁ ∧ 0 ≤ C ∧ ∀ ψ : GA D V → ℂ, SmoothW θ V ψ → ∀ (g u : GA D V) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → CloseR θ V u δ → ∀ c : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ → ℝ, (∀ p ∈ B, ∀ w ∈ Ω, ‖Rder θ V p.1 p.2 ψ (g * w)‖ ≤ c p) → ‖ψ (g * u) - ψ g‖ ≤ C * δ * ∑ p ∈ B, c p := by
  intro D θ hθ V
  classical
  have R : RealPoints θ V := (RealPts.realPoints D).2 θ hθ V
  obtain ⟨ι, hι, b, p, X, hb⟩ := exists_basis V
  obtain ⟨K, hK, hKb⟩ := exists_coord_bound b
  obtain ⟨δ₁, C₀, hδ₁, hC₀, hlog⟩ := exists_log hθ R
  have : FiniteDimensional ℝ (LieN V) := Module.Finite.of_basis b
  set B := Finset.univ.image fun i => (p i, (X i).1) with hB
  have hmemB : ∀ i, (p i, (X i).1) ∈ B := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have h0 : expInf θ V 0 ∈ expInf θ V '' Metric.closedBall 0 (C₀ * δ₁) :=
    ⟨0, Metric.mem_closedBall_self (mul_nonneg hC₀ hδ₁.le), rfl⟩
  refine ⟨B, expInf θ V '' Metric.closedBall 0 (C₀ * δ₁), K * C₀ * Fintype.card ι, δ₁, ?_, ?_, hδ₁,
    mul_nonneg (mul_nonneg hK hC₀) (Nat.cast_nonneg _), ?_⟩
  · intro q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hq
    exact (mem_lieAt_iff _ _).2 (X i).2
  · exact (isCompact_closedBall 0 _).image (continuous_expInf hθ R)
  · intro ψ hψ g u δ hδ hδle hu c hc
    obtain ⟨Z, rfl, hZ⟩ := hlog u δ hδ hδle hu
    have hsm : Sm (expInf θ V) ψ := (isSmoothInf_iff ψ).1 ((smooth_iff R ψ).1 hψ)
    have hcn : ∀ q ∈ B, 0 ≤ c q := fun q hq => (norm_nonneg _).trans (hc q hq _ h0)
    have ha : ∀ i, |b.repr Z i| ≤ K * (C₀ * δ) := fun i =>
      (hKb Z i).trans (mul_le_mul_of_nonneg_left hZ hK)
    have hder : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖Der (expInf θ V) (b i) ψ (g * expInf θ V (t • Z))‖ ≤ c (p i, (X i).1) := by
      intro i t ht
      rw [hb i, ← lieDer_eq, ← Rder_eq R]
      refine hc _ (hmemB i) _ ⟨t • Z, ?_, rfl⟩
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc t * ‖Z‖ ≤ 1 * (C₀ * δ) := mul_le_mul ht.2 hZ (norm_nonneg _) zero_le_one
        _ ≤ C₀ * δ₁ := by rw [one_mul]; exact mul_le_mul_of_nonneg_left hδle hC₀
    have key := norm_sub_le (expInf θ V) (expInf_zero R) (expInf_add R) b hsm g Z (K * (C₀ * δ)) ha
      (fun i => c (p i, (X i).1)) hder
    have hsum : ∑ i, c (p i, (X i).1) ≤ Fintype.card ι * ∑ q ∈ B, c q := by
      calc ∑ i, c (p i, (X i).1) ≤ ∑ _i : ι, ∑ q ∈ B, c q :=
            Finset.sum_le_sum fun i _ => Finset.single_le_sum hcn (hmemB i)
        _ = Fintype.card ι * ∑ q ∈ B, c q := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc ‖ψ (g * expInf θ V Z) - ψ g‖ ≤ K * (C₀ * δ) * ∑ i, c (p i, (X i).1) := key
      _ ≤ K * (C₀ * δ) * (Fintype.card ι * ∑ q ∈ B, c q) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg hK (mul_nonneg hC₀ hδ))
      _ = K * C₀ * Fintype.card ι * δ * ∑ q ∈ B, c q := by ring

end GlobalTheory.CuspGeo.MeanValue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemFlagUnipotentRadicalOfBesselNormalFrameLocal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

namespace GlobalTheory.LocFlag

theorem conj_vanish {k : Type} [CommRing k] {Z Y M : Type} [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
    [Fintype M] [DecidableEq M] (lv : Z → ℕ) (lw : Y → ℕ) (P : Matrix Z M k) (J : Matrix M Z k) (β : Matrix M Y k)
    (γ : Matrix Y M k) (hPJ : P * J = 1) (hJP : J * P = 1) (hβγ : β * γ = 1) (hγβ : γ * β = 1)
    (hA : ∀ a r, lv a ≠ lw r → (P ⬝ β) a r = 0) (q : Matrix Y Y k)
    (hq : ∀ r s, lw s ≤ lw r → q r s = (1 : Matrix Y Y k) r s) (a b : Z) (hab : lv b ≤ lv a) :
    (P ⬝ (β * q * γ - 1) ⬝ J) a b = 0 := by
  have hAB : (P * β) * (γ * J) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc β, hβγ, Matrix.one_mul, hPJ]
  have hBA : (γ * J) * (P * β) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc J, hJP, Matrix.one_mul, hγβ]
  have hB : ∀ t b, lw t ≠ lv b → (γ ⬝ J) t b = 0 := by
    intro t b h
    generalize P * β = A at hA hAB hBA
    generalize γ * J = B at hAB hBA
    have h1 : diagonal (fun a => if lv a = lv b then (1 : k) else 0) * A =
        A * diagonal (fun r => if lw r = lv b then (1 : k) else 0) := by
      ext a r
      rw [diagonal_mul, mul_diagonal]
      by_cases e : lv a = lw r
      · rw [e, mul_comm]
      · rw [hA a r e, mul_zero, zero_mul]
    have h2 : B * diagonal (fun a => if lv a = lv b then (1 : k) else 0) =
        diagonal (fun r => if lw r = lv b then (1 : k) else 0) * B := by
      rw [← Matrix.mul_one (B * _), ← hAB, ← Matrix.mul_assoc, Matrix.mul_assoc B, h1, ← Matrix.mul_assoc, hBA,
        Matrix.one_mul]
    have h3 := congrFun (congrFun h2 t) b
    rwa [diagonal_mul, mul_diagonal, if_pos rfl, if_neg h, mul_one, zero_mul] at h3
  have e : P * (β * q * γ - 1) * J = (P * β) * (q - 1) * (γ * J) := by
    rw [← hβγ]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul]
  rw [e, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  by_cases ht : lw t = lv b
  · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro r _
    by_cases hr : lv a = lw r
    · rw [Matrix.sub_apply, hq r t (by omega), sub_self, mul_zero]
    · rw [hA a r hr, zero_mul]
  · rw [hB t b ht, mul_zero]

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

def wl (σ r : ℕ) : Fin σ ⊕ (Fin r ⊕ Fin σ) → ℕ :=
  Sum.elim (fun i => i.val + 1) (Sum.elim (fun _ => σ + 1) fun i => 2 * σ - i.val + 1)

def wJ {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) : Matrix (Fin V.rank) (Fin σ ⊕ (Fin V₀.rank ⊕ Fin σ)) D.host.E :=
  fromCols d.e (fromCols d.i₀ d.e')

noncomputable def wP {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) :
    Matrix (Fin σ ⊕ (Fin V₀.rank ⊕ Fin σ)) (Fin V.rank) D.host.E :=
  fromRows d.qX (fromRows d.q0 d.qY)

theorem wJ_wP {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) : wJ d * wP d = 1 := by
  rw [wJ, wP, fromCols_mul_fromRows, fromCols_mul_fromRows, ← add_assoc, d.sum_eq_one_rat]

theorem wP_wJ {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) : wP d * wJ d = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [← d.rank_add]; ring)).1 (wJ_wP d)

theorem frame_cols {σ : ℕ} (B : BesLev D σ) (s : k) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)) (h : p.IsBesFrame B s FA FV) (r : n ⊕ Fin c) :
    ∃ x : Fin σ ⊕ (Fin B.V₀.rank ⊕ Fin σ) → k, (∀ z, wl σ _ z ≠ lev (σ + 1) r → x z = 0) ∧
      ∀ u, FV.β u r = ∑ z, (wJ B.d).map (Witness.prH p) u z * x z := by
  obtain ⟨hc, h1, h2, h3, h4⟩ := h
  rcases r with a | j
  · refine ⟨Sum.elim 0 (Sum.elim (fun w => (B.o.iA.map (Witness.prH p) * FA.β) w a) 0), ?_, fun u => ?_⟩
    · rintro (z | z | z) hz
      · rfl
      · exact absurd rfl hz
      · rfl
    · rw [h1]
      change ((B.d.i₀ * B.o.iA).map (Witness.prH p) * FA.β) u a = _
      rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply]
      simp [wJ]
  · have hj := j.isLt
    rcases lt_trichotomy j.val σ with hlt | heq | hgt
    · refine ⟨Pi.single (Sum.inl ⟨j.val, hlt⟩) (s * p.xi ^ (σ - j.val)), fun z hz => Pi.single_eq_of_ne ?_ _, fun u => ?_⟩
      · rintro rfl
        exact hz rfl
      · rw [h2 ⟨j.val, hlt⟩ j rfl, Finset.sum_eq_single (Sum.inl ⟨j.val, hlt⟩), Pi.single_eq_same, mul_comm]
        · rfl
        · intro b _ hb
          rw [Pi.single_eq_of_ne hb, mul_zero]
        · simp
    · refine ⟨Sum.elim 0 (Sum.elim (fun w => s * Witness.prH p (vecB B.o B.ζ w)) 0), ?_, fun u => ?_⟩
      · rintro (z | z | z) hz
        · rfl
        · exact absurd (by simp [wl, lev, heq]) hz
        · rfl
      · rw [h3 j heq]
        change s * Witness.prH p (∑ w, B.d.i₀ u w * vecB B.o B.ζ w) = _
        rw [map_sum, Finset.mul_sum]
        simp [wJ, mul_left_comm]
    · have hi : 2 * σ - j.val < σ := by omega
      refine ⟨Pi.single (Sum.inr (Sum.inr ⟨_, hi⟩))
        (s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (σ - 1 - (2 * σ - j.val))), fun z hz => Pi.single_eq_of_ne ?_ _, fun u => ?_⟩
      · rintro rfl
        exact hz (by simp only [wl, lev, Sum.elim_inr]; omega)
      · rw [h4 ⟨_, hi⟩ j (by simp only; omega), Finset.sum_eq_single (Sum.inr (Sum.inr ⟨_, hi⟩)), Pi.single_eq_same, mul_comm]
        · rfl
        · intro b _ hb
          rw [Pi.single_eq_of_ne hb, mul_zero]
        · simp

theorem comp_vanish {σ : ℕ} (B : BesLev D σ) (s : k) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)) (h : p.IsBesFrame B s FA FV)
    (M : Mx D B.V.rank B.V.rank) (q : GL (n ⊕ Fin c) k) (hq : q ∈ N k n c (σ + 1))
    (hM : M.map p.π = FV.β * q.val * FV.γ) (a b : Fin σ ⊕ (Fin B.V₀.rank ⊕ Fin σ)) (hab : wl σ _ b ≤ wl σ _ a) :
    p.π (((wP B.d).map (incA D) ⬝ (M - 1) ⬝ (wJ B.d).map (incA D)) a b) = 0 := by
  have h1 : (wP B.d).map (Witness.prH p) * (wJ B.d).map (Witness.prH p) = 1 := by
    rw [← Matrix.map_mul, wP_wJ, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (wJ B.d).map (Witness.prH p) * (wP B.d).map (Witness.prH p) = 1 := by
    rw [← Matrix.map_mul, wJ_wP, Matrix.map_one _ (map_zero _) (map_one _)]
  have key := conj_vanish (wl σ _) (lev (σ + 1)) _ _ FV.β FV.γ h1 h2 FV.βγ FV.γβ (fun a r har => by
    obtain ⟨x, hx, hβ⟩ := frame_cols p B s FA FV h r
    have : (((wP B.d).map (Witness.prH p)) ⬝ FV.β) a r =
        (((wP B.d).map (Witness.prH p) * (wJ B.d).map (Witness.prH p)) *ᵥ x) a := by
      rw [← Matrix.mulVec_mulVec, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun u _ => by rw [hβ]; rfl
    rw [this, h1, Matrix.one_mulVec, hx a har]) q.val ((GlobalTheory.RootEx.Radical.mem_N_iff q).1 hq) a b hab
  rw [← key, ← hM, ← Matrix.map_apply (f := p.π), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub p.π),
    Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

theorem entry_zero {V : HSp D} {g : GA D V} (hg : SuppAt p.e V g) {l m : ℕ} (P : Mx D l V.rank) (J : Mx D V.rank m) (i j)
    (h1 : p.π ((P ⬝ (mt V g - 1) ⬝ J) i j) = 0)
    (h2 : p.π (((adj J ⬝ gA V) ⬝ (mt V g⁻¹ - 1) ⬝ (giA V ⬝ adj P)) j i) = 0) : (P ⬝ (mt V g - 1) ⬝ J) i j = 0 := by
  have e1 : (p.e + cA D p.e) • (mt V g - 1) = mt V g - 1 := Matrix.ext hg
  have e2 : (p.e + cA D p.e) * (P ⬝ (mt V g - 1) ⬝ J) i j = (P ⬝ (mt V g - 1) ⬝ J) i j := by
    conv_rhs => rw [← e1, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  have e3 : (adj J ⬝ gA V) ⬝ (mt V g⁻¹ - 1) ⬝ (giA V ⬝ adj P) = adj (P ⬝ (mt V g - 1) ⬝ J) := by
    simp only [mt_inv, adj_mul, adj_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, gA_giA_cancel,
      Matrix.one_mul]
  rw [e3] at h2
  change p.π (cA D ((P ⬝ (mt V g - 1) ⬝ J) i j)) = 0 at h2
  generalize (P ⬝ (mt V g - 1) ⬝ J) i j = x at h1 h2 e2
  have a1 : p.e * x = 0 := by rw [← p.ι_π, h1, map_zero]
  have a2 : p.e * cA D x = 0 := by rw [← p.ι_π, h2, map_zero]
  have a3 : cA D p.e * x = 0 := by
    have := congrArg (cA D) a2
    rwa [map_mul, cA_cA, map_zero] at this
  rw [← e2, add_mul, a1, a3, add_zero]

theorem unip_of_blocks {R : Type} [CommRing R] {m r σ : ℕ} (jX jY : Matrix (Fin m) (Fin σ) R) (j0 : Matrix (Fin m) (Fin r) R)
    (pX pY : Matrix (Fin σ) (Fin m) R) (p0 : Matrix (Fin r) (Fin m) R) (h : jX * pX + j0 * p0 + jY * pY = 1)
    (M : Matrix (Fin m) (Fin m) R) (zXX : GlobalTheory.BesselChar.StrictUp (pX * (M - 1) * jX)) (z0X : p0 * (M - 1) * jX = 0)
    (zYX : pY * (M - 1) * jX = 0) (z00 : p0 * (M - 1) * j0 = 0) (zY0 : pY * (M - 1) * j0 = 0) :
    GlobalTheory.BesselChar.Unip jX pY M := by
  obtain ⟨L, rfl⟩ : ∃ L, M = 1 + L := ⟨M - 1, by abel⟩
  rw [add_sub_cancel_left] at zXX z0X zYX z00 zY0
  have cX : L * jX = jX * (pX * L * jX) := by
    conv_lhs => rw [← Matrix.one_mul L, ← h]
    simp only [Matrix.mul_assoc] at z0X zYX
    simp only [Matrix.add_mul, Matrix.mul_assoc, z0X, zYX, Matrix.mul_zero, add_zero]
  have c0 : L * j0 = jX * (pX * L * j0) := by
    conv_lhs => rw [← Matrix.one_mul L, ← h]
    simp only [Matrix.mul_assoc] at z00 zY0
    simp only [Matrix.add_mul, Matrix.mul_assoc, z00, zY0, Matrix.mul_zero, add_zero]
  refine ⟨⟨_, zXX, by rw [← cX, Matrix.add_mul, Matrix.one_mul]⟩, fun y hy => ?_⟩
  refine ⟨(pX * L * jX) *ᵥ (pX *ᵥ y) + (pX * L * j0) *ᵥ (p0 *ᵥ y), ?_⟩
  have hy' : y = jX *ᵥ (pX *ᵥ y) + j0 *ᵥ (p0 *ᵥ y) := by
    conv_lhs => rw [← Matrix.one_mulVec y, ← h]
    rw [Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hy, Matrix.mulVec_zero, add_zero]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec _ jX, Matrix.mulVec_mulVec _ jX, ← cX, ← c0,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_add, ← hy', Matrix.add_mulVec, Matrix.one_mulVec]

theorem mem_of_blocks {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) (g : GA D V)
    (zXX : GlobalTheory.BesselChar.StrictUp (d.pX ⬝ (mt V g - 1) ⬝ d.jX)) (z0X : d.p0 ⬝ (mt V g - 1) ⬝ d.jX = 0)
    (zYX : d.pY ⬝ (mt V g - 1) ⬝ d.jX = 0) (z00 : d.p0 ⬝ (mt V g - 1) ⬝ d.j0 = 0)
    (zY0 : d.pY ⬝ (mt V g - 1) ⬝ d.j0 = 0) : g ∈ flagN d := by
  unfold flagN
  rw [GlobalTheory.BesselChar.mem_NFlag_iff V d.e (isIsoSub_e d).1]
  exact unip_of_blocks d.jX d.jY d.j0 d.pX d.pY d.p0 d.sum_eq_one _ zXX z0X zYX z00 zY0

theorem blocks_vanish {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) (M : Mx D V.rank V.rank)
    (W : ∀ a b, wl σ _ b ≤ wl σ _ a → p.π (((wP d).map (incA D) ⬝ M ⬝ (wJ d).map (incA D)) a b) = 0) :
    (∀ i j, j ≤ i → p.π ((d.pX ⬝ M ⬝ d.jX) i j) = 0) ∧ (d.p0 ⬝ M ⬝ d.jX).map p.π = 0 ∧ (d.pY ⬝ M ⬝ d.jX).map p.π = 0 ∧
      (d.p0 ⬝ M ⬝ d.j0).map p.π = 0 ∧ (d.pY ⬝ M ⬝ d.j0).map p.π = 0 ∧
      ∀ i j, i ≤ j → p.π ((d.pY ⬝ M ⬝ d.jY) i j) = 0 := by
  refine ⟨fun i j h => W (Sum.inl i) (Sum.inl j) ?_, Matrix.ext fun i j => W (Sum.inr (Sum.inl i)) (Sum.inl j) ?_,
    Matrix.ext fun i j => W (Sum.inr (Sum.inr i)) (Sum.inl j) ?_,
    Matrix.ext fun i j => W (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j)) ?_,
    Matrix.ext fun i j => W (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)) ?_,
    fun i j h => W (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) ?_⟩ <;>
  simp only [wl, Sum.elim_inr, Sum.elim_inl] <;> omega

theorem mem_flagN : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (σ : ℕ) (B : BesLev D σ) (s : k) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA FV → ∀ (g : GA D B.V) (q : GL (n ⊕ Fin c) k), q ∈ N k n c (σ + 1) → p.IsLoc FV g q → g ∈ flagN B.d := by
  intro D k _ _ _ _ p σ B s n _ _ c FA FV hF g q hq hg
  obtain ⟨hS, hg⟩ := hg
  have hg' : (mt B.V g⁻¹).map p.π = FV.β * (q⁻¹).val * FV.γ := by
    have h1 : (mt B.V g⁻¹).map p.π * (mt B.V g).map p.π = 1 := by
      rw [← Matrix.map_mul, GlobalTheory.MixModel.mt_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : (FV.β * q.val * FV.γ) * (FV.β * (q⁻¹).val * FV.γ) = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc FV.β (q⁻¹).val, ← Matrix.mul_assoc FV.γ, FV.γβ, Matrix.one_mul,
        Matrix.mul_assoc, ← Matrix.mul_assoc q.val, Units.mul_inv, Matrix.one_mul, FV.βγ]
    rw [← Matrix.mul_one (Matrix.map _ _), ← h2, ← Matrix.mul_assoc _ (FV.β * q.val * FV.γ), ← hg, h1, Matrix.one_mul]
  obtain ⟨XX, OX, YX, OO, YO, -⟩ := blocks_vanish p B.d _ (comp_vanish p B s FA FV hF _ q hq hg)
  obtain ⟨-, OX', YX', OO', YO', YY'⟩ := blocks_vanish p B.d _ (comp_vanish p B s FA FV hF _ q⁻¹ (inv_mem hq) hg')
  generalize B.d = d at *
  have aX : giA B.V ⬝ adj d.pX = d.jY := by rw [d.pX_eq, adj_mul, adj_adj, adj_gA, giA_gA_cancel]
  have aY : giA B.V ⬝ adj d.pY = d.jX := by rw [d.pY_eq, adj_mul, adj_adj, adj_gA, giA_gA_cancel]
  have a0 : giA B.V ⬝ adj d.p0 = d.j0 ⬝ giA B.V₀ := by
    rw [d.p0_eq, adj_mul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, giA_gA_cancel]
  have b0 : adj d.j0 ⬝ gA B.V = gA B.V₀ ⬝ d.p0 := by rw [d.p0_eq, gA_giA_cancel]
  have ev : ∀ {l m : ℕ} {x : Mx D l m}, x.map p.π = 0 → ∀ i j, p.π (x i j) = 0 := fun h i j => congrFun (congrFun h i) j
  refine mem_of_blocks d g (fun i j hij => entry_zero p hS _ _ i j (XX i j hij) ?_)
    (Matrix.ext fun i j => entry_zero p hS _ _ i j (ev OX i j) ?_)
    (Matrix.ext fun i j => entry_zero p hS _ _ i j (ev YX i j) ?_)
    (Matrix.ext fun i j => entry_zero p hS _ _ i j (ev OO i j) ?_)
    (Matrix.ext fun i j => entry_zero p hS _ _ i j (ev YO i j) ?_)
  · rw [aX, ← d.pY_eq]
    exact YY' j i hij
  · refine ev ?_ j i
    rw [a0, ← d.pY_eq, ← Matrix.mul_assoc, Matrix.map_mul, YO', Matrix.zero_mul]
  · rw [aY, ← d.pY_eq]
    exact ev YX' j i
  · refine ev ?_ j i
    rw [a0, b0, ← Matrix.mul_assoc, Matrix.mul_assoc (gA _), Matrix.mul_assoc (gA _),
      Matrix.map_mul, Matrix.map_mul, OO', Matrix.mul_zero, Matrix.zero_mul]
  · refine ev ?_ j i
    rw [aY, b0, Matrix.mul_assoc (gA _), Matrix.mul_assoc (gA _), Matrix.map_mul, OX', Matrix.mul_zero]

end GlobalTheory.LocFlag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeCompletionAtPlacesOfFinPartMemHatLattiStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_latticeCompletionAtPlaces_of_finPart_mem_hatLattice : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D), (∀ i, y i ∈ idAt D P) → (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → y ∈ latV S L P := by
  first | exact @GlobalTheory.HatLatV.mem_latV_of_hatL | exact GlobalTheory.HatLatV.mem_latV_of_hatL | (intros; apply GlobalTheory.HatLatV.mem_latV_of_hatL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormLeOfCuspidalVariationUnipotentRadicalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_le_of_cuspidal_variation_unipotentRadical : ∀ (D : D7) (V : HSp D) (φ : GA D V → ℂ), IsAutFun V φ → IsCuspFun V φ → ∀ (r : ℕ) (C₀ : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C₀ → ∀ (g : GA D V) (e : ℝ), (∀ m ∈ NI V C₀, ‖φ (m * g) - φ g‖ ≤ e) → ‖φ g‖ ≤ e := by
  first | exact @GlobalTheory.CuspGeo.norm_le_of_unipRad_variation | exact GlobalTheory.CuspGeo.norm_le_of_unipRad_variation | (intros; apply GlobalTheory.CuspGeo.norm_le_of_unipRad_variation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorBijectiveFiniteTranslationCombinStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramifiedOperator_bijective_finite_translation_combination : ∀ D : D7, GlobalTheory.FinPl.RamBijective D := by
  first | exact @GlobalTheory.FinPl.ramBijective_holds | exact GlobalTheory.FinPl.ramBijective_holds | (intros; apply GlobalTheory.FinPl.ramBijective_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFlagUnipotentIsotropicBlockUnitriangularStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_flagUnipotent_isotropicBlock_unitriangular : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (γ : GA D V), γ ∈ GQ V → γ ∈ flagN d → ∃ u u' : Matrix (Fin ρ) (Fin ρ) D.host.E, (rat u : Mx D ρ ρ) = blockX d γ ∧ u * u' = 1 ∧ u' * u = 1 ∧ (∀ i, u i i = 1) ∧ (∀ i k, k < i → u i k = 0) ∧ ∀ j : Fin ρ, γ ∈ Nfix d j → ∀ i k, k ≤ j → u i k = if i = k then 1 else 0 := by
  first | exact @GlobalTheory.Unf.ratBlock_unitri | exact GlobalTheory.Unf.ratBlock_unitri | (intros; apply GlobalTheory.Unf.ratBlock_unitri <;> assumption)
end

