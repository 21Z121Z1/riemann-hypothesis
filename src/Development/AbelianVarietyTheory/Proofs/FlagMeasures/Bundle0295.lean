import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentLebesgueMeasureIsHaarOn
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0262
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0255
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0280
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureEqOfStrictFundamentalSetsPlacewise
section
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FundEq

open GlobalTheory.DegVol

theorem measurable_mulP {ι : Type} {k r : ℕ} (m : ι → Formalism.QuantumDeterminants.Mt k r) :
    Measurable (fun x : ι → Formalism.QuantumDeterminants.Mt k r => mulP m x) :=
  measurable_pi_lambda _ fun v => (GlobalTheory.DegVol.Cov.continuous_lmulM _).measurable.comp (measurable_pi_apply v)

theorem measure_eq_tsum {ι : Type} {k r : ℕ} (μ : Measure (ι → Formalism.QuantumDeterminants.Mt k r))
    (R Γ Ω S : Set (ι → Formalism.QuantumDeterminants.Mt k r)) [Countable Γ] (hR : μ Rᶜ = 0)
    (hΩ : MeasurableSet Ω) (hS : MeasurableSet S) (h : ∀ x ∈ R, ∃! m, m ∈ Γ ∧ mulP m x ∈ Ω) :
    μ S = ∑' a : Γ, μ ((fun x => mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x) ⁻¹' Ω ∩ S) := by
  rw [← measure_iUnion₀]
  · apply measure_congr
    have : ∀ᵐ x ∂μ, x ∈ R := hR
    filter_upwards [this] with x hx
    obtain ⟨s, hs, -⟩ := h x hx
    apply propext
    constructor
    · intro hxS
      exact Set.mem_iUnion.2 ⟨⟨s, hs.1⟩, hs.2, hxS⟩
    · intro hxS
      obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hxS
      exact ha.2
  · intro a b hab
    refine measure_mono_null ?_ hR
    rintro x ⟨ha, hb⟩ hx
    exact hab (Subtype.ext ((h x hx).unique ⟨a.2, ha.1⟩ ⟨b.2, hb.1⟩))
  · intro a
    exact ((measurable_mulP _ hΩ).inter hS).nullMeasurableSet

def invP {ι : Type} {k r : ℕ} (m : ι → Formalism.QuantumDeterminants.Mt k r) : ι → Formalism.QuantumDeterminants.Mt k r :=
  fun v => Matrix.of.symm (Matrix.of (m v))⁻¹

theorem mulP_invP_mulP {ι : Type} {k r : ℕ} (m : ι → Formalism.QuantumDeterminants.Mt k r) (hm : ∀ v, IsUnit (Matrix.of (m v)).det)
    (x : ι → Formalism.QuantumDeterminants.Mt k r) : mulP (invP m) (mulP m x) = x := by
  funext v
  show (Matrix.of (m v))⁻¹ * (Matrix.of (m v) * Matrix.of (x v)) = x v
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hm v), Matrix.one_mul]
  rfl

theorem pointwiseInv_pointwiseInv {ι : Type} {k r : ℕ} (m : ι → Formalism.QuantumDeterminants.Mt k r) (hm : ∀ v, IsUnit (Matrix.of (m v)).det) :
    invP (invP m) = m := by
  funext v
  show ((Matrix.of (m v))⁻¹)⁻¹ = m v
  rw [Matrix.nonsing_inv_nonsing_inv _ (hm v)]
  rfl

theorem measure_le {ι : Type} [Fintype ι] {k r : ℕ} (μ : Measure (ι → Formalism.QuantumDeterminants.Mt k r))
    (R Γ Ω₁ Ω₂ : Set (ι → Formalism.QuantumDeterminants.Mt k r)) (hΓ : Γ.Countable) (hR : μ Rᶜ = 0)
    (hinv : ∀ m ∈ Γ, invP m ∈ Γ) (hu : ∀ m ∈ Γ, ∀ v, IsUnit (Matrix.of (m v)).det)
    (hpres : ∀ m ∈ Γ, μ.map (fun x => mulP m x) = μ)
    (h₁ : IsFund Γ R Ω₁) (h₂ : IsFund Γ R Ω₂) : μ Ω₁ ≤ μ Ω₂ := by
  haveI : Countable Γ := hΓ.to_subtype
  have e1 := measure_eq_tsum μ R Γ Ω₂ Ω₁ hR h₂.1 h₁.1 h₂.2
  have e2 := measure_eq_tsum μ R Γ Ω₁ Ω₂ hR h₁.1 h₂.1 h₁.2
  have hterm : ∀ a : Γ, μ ((fun x => mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x) ⁻¹' Ω₂ ∩ Ω₁) =
      μ ((fun x => mulP (invP (a : ι → Formalism.QuantumDeterminants.Mt k r)) x) ⁻¹' Ω₁ ∩ Ω₂) := by
    intro a
    have hs : MeasurableSet ((fun x => mulP (invP (a : ι → Formalism.QuantumDeterminants.Mt k r)) x) ⁻¹' Ω₁ ∩ Ω₂) :=
      (measurable_mulP _ h₁.1).inter h₂.1
    conv_rhs => rw [← hpres a a.2, Measure.map_apply (measurable_mulP _) hs]
    congr 1
    ext x
    show (mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x ∈ Ω₂ ∧ x ∈ Ω₁) ↔
      (mulP (invP (a : ι → Formalism.QuantumDeterminants.Mt k r)) (mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x) ∈ Ω₁ ∧ mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x ∈ Ω₂)
    rw [mulP_invP_mulP _ (hu a a.2)]
    exact And.comm
  let f : Γ → Γ := fun a => ⟨invP a, hinv a a.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h' : invP (a : ι → Formalism.QuantumDeterminants.Mt k r) = invP b := congrArg Subtype.val hab
    apply Subtype.ext
    rw [← pointwiseInv_pointwiseInv _ (hu a a.2), ← pointwiseInv_pointwiseInv _ (hu b b.2), h']
  rw [e1, e2, tsum_congr hterm]
  exact ENNReal.tsum_comp_le_tsum_of_injective hf
    (fun b : Γ => μ ((fun x => mulP (b : ι → Formalism.QuantumDeterminants.Mt k r) x) ⁻¹' Ω₁ ∩ Ω₂))

theorem measure_eq : ∀ (ι : Type) [Fintype ι] (k r : ℕ) (Γ Ω₁ Ω₂ : Set (ι → Formalism.QuantumDeterminants.Mt k r)),
    Γ.Countable → (fun _ => Matrix.of.symm 1) ∈ Γ → (∀ m ∈ Γ, ∀ m' ∈ Γ, GlobalTheory.DegVol.mulP m m' ∈ Γ) →
    (∀ m ∈ Γ, (fun v => Matrix.of.symm (Matrix.of (m v))⁻¹) ∈ Γ) →
    (∀ m ∈ Γ, ∀ v, Matrix.of (m v) ∈ Formalism.QuantumDeterminants.Nset k r) →
    GlobalTheory.DegVol.IsFund Γ (GlobalTheory.DegVol.RP k r (fun _ => 1)) Ω₁ → GlobalTheory.DegVol.IsFund Γ (GlobalTheory.DegVol.RP k r (fun _ => 1)) Ω₂ →
    Measure.pi (fun _ : ι => GlobalTheory.Amp.lebN k r) Ω₁ = Measure.pi (fun _ : ι => GlobalTheory.Amp.lebN k r) Ω₂ := by
  intro ι _ k r Γ Ω₁ Ω₂ hΓ _ _ hinv hN h₁ h₂
  have hH := GlobalTheory.Amp.NHaar.isHaarOn_lebN k r
  haveI : SigmaFinite (GlobalTheory.Amp.lebN k r) := hH.1
  have hu : ∀ m ∈ Γ, ∀ v, IsUnit (Matrix.of (m v)).det := fun m hm v =>
    GlobalTheory.DegVol.RealMat.isUnit_det (hN m hm v).1
  have hnull : Measure.pi (fun _ : ι => GlobalTheory.Amp.lebN k r) (GlobalTheory.DegVol.RP k r (fun _ => 1))ᶜ = 0 := by
    refine measure_mono_null (t := ⋃ v : ι, Function.eval v ⁻¹' {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r}) ?_
      (measure_iUnion_null fun v => Measure.pi_eval_preimage_null _ hH.2.2.1)
    intro x hx
    simp only [RP, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hx
    obtain ⟨v, hv'⟩ := hx
    refine Set.mem_iUnion.2 ⟨v, ?_⟩
    intro hxN
    apply hv'
    refine ⟨hxN, ?_⟩
    simpa using hxN
  have hpres : ∀ m ∈ Γ, (Measure.pi fun _ : ι => GlobalTheory.Amp.lebN k r).map (fun x => mulP m x) =
      Measure.pi fun _ : ι => GlobalTheory.Amp.lebN k r := fun m hm => by
    have e : ∀ v, (GlobalTheory.Amp.lebN k r).map (Formalism.QuantumDeterminants.lmulM (Matrix.of (m v))) = GlobalTheory.Amp.lebN k r :=
      fun v => hH.2.2.2 _ (hN m hm v)
    haveI : ∀ v, SigmaFinite ((GlobalTheory.Amp.lebN k r).map (Formalism.QuantumDeterminants.lmulM (Matrix.of (m v)))) := fun v => by
      rw [e]; infer_instance
    have := Measure.pi_map_pi (μ := fun _ : ι => GlobalTheory.Amp.lebN k r)
      (f := fun v => Formalism.QuantumDeterminants.lmulM (Matrix.of (m v))) fun v => (GlobalTheory.DegVol.Cov.continuous_lmulM _).measurable.aemeasurable
    simp only [e] at this
    exact this
  exact le_antisymm
    (measure_le _ _ Γ Ω₁ Ω₂ hΓ hnull hinv hu hpres h₁ h₂)
    (measure_le _ _ Γ Ω₂ Ω₁ hΓ hnull hinv hu hpres h₂ h₁)

end GlobalTheory.FundEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePiPointsAtInfinitePlacesCMTypeImage
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDom

section Conj

variable {k r : ℕ}

def cjm (M : Formalism.QuantumDeterminants.Mt k r) : Formalism.QuantumDeterminants.Mt k r := fun i j => star (M i j)

theorem cjm_cjm (M : Formalism.QuantumDeterminants.Mt k r) : cjm (cjm M) = M := by
  funext i j; simp [cjm]

theorem measurable_cjm : Measurable (cjm : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r) := by
  unfold cjm; fun_prop

def cjmE : Formalism.QuantumDeterminants.Mt k r ≃ᵐ Formalism.QuantumDeterminants.Mt k r where
  toFun := cjm
  invFun := cjm
  left_inv := cjm_cjm
  right_inv := cjm_cjm
  measurable_toFun := measurable_cjm
  measurable_invFun := measurable_cjm

theorem map_star_eq (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : X.map star = Xᴴᵀ := by
  ext i j; simp

theorem exp_map_star (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    NormedSpace.exp (X.map star) = (NormedSpace.exp X).map star := by
  rw [map_star_eq, map_star_eq, Matrix.exp_transpose, Matrix.exp_conjTranspose]

theorem Hpk_map_star : (Formalism.QuantumDeterminants.Hpk k r).map star = Formalism.QuantumDeterminants.Hpk k r := by
  ext i j
  simp only [Matrix.map_apply]
  unfold Formalism.QuantumDeterminants.Hpk
  split_ifs <;> simp

theorem map_star_mem_N {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.Nset k r) : g.map star ∈ Formalism.QuantumDeterminants.Nset k r := by
  obtain ⟨h1, h2, h3⟩ := hg
  refine ⟨?_, fun a i hi => ?_, fun i j a b c => ?_⟩
  · have h1' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := h1
    show (g.map star)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g.map star = Formalism.QuantumDeterminants.Hpk k r
    have e : ∀ M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, M.map star = M.map (starRingEnd ℂ) := by
      intro M; rfl
    have hc : (g.map star)ᴴ = gᴴ.map star := by ext i j; simp
    rw [hc, ← Hpk_map_star, e, e, e, ← Matrix.map_mul, ← Matrix.map_mul, h1']
  · simp only [Matrix.map_apply, h2 a i hi]; split_ifs <;> simp
  · simp only [Matrix.map_apply, h3 i j a b c]; split_ifs <;> simp

end Conj

section Conj2
variable {k r : ℕ}

def cjR (m : ℕ) :
    EuclideanSpace ℝ (Fin m × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) where
  toFun x := (WithLp.equiv 2 _).symm (realifyFun ((unrealify x).map star))
  map_add' x y := by
    ext ⟨i, j, b⟩
    cases b <;> simp [realifyFun, unrealify] <;> ring
  map_smul' c x := by
    ext ⟨i, j, b⟩
    cases b <;> simp [realifyFun, unrealify]

theorem unrealify_realify' {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
  ext i j
  simp [unrealify, realifyFun]

theorem unrealify_cjR {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (cjR m x) = (unrealify x).map star := unrealify_realify' _

theorem norm_sq_unrealify' {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    ‖x‖ ^ 2 = ∑ i, ∑ j, ‖unrealify x i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [unrealify, Real.norm_eq_abs, sq_abs]
  ring

theorem norm_cjR {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : ‖cjR m x‖ = ‖x‖ := by
  have : ‖cjR m x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_unrealify', norm_sq_unrealify', unrealify_cjR]
    simp only [Matrix.map_apply, norm_star]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

theorem cjR_mem {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    (hS : ∀ g ∈ S, g.map star ∈ S) : ∀ x ∈ lieE S, cjR (2 * r + k + 1) x ∈ lieE S := by
  intro x hx
  have : lieE S ≤ (lieE S).comap (cjR (2 * r + k + 1)) := by
    unfold lieE
    rw [Submodule.span_le]
    rintro _ ⟨X, hX, rfl⟩
    refine Submodule.subset_span ⟨X.map star, fun t => ?_, ?_⟩
    · have e : ((t : ℂ) • X.map star) = ((t : ℂ) • X).map star := by
        ext i j; simp
      rw [e, exp_map_star]; exact hS _ (hX t)
    · show _ = (WithLp.equiv 2 _).symm (realifyFun ((unrealify _).map star))
      rw [unrealify_realify']
  exact this hx

theorem norm_cjR_restrict {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    (hS : ∀ g ∈ S, g.map star ∈ S) (x : lieE S) :
    ‖(cjR (2 * r + k + 1)).restrict (cjR_mem hS) x‖ = ‖x‖ := by
  show ‖cjR (2 * r + k + 1) (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖ =
    ‖(x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖
  exact norm_cjR _

theorem haarLie_map_cjm {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    (hS : ∀ g ∈ S, g.map star ∈ S) (κ : ENNReal) : (haarLie S κ).map (cjmE (k := k) (r := r)) = haarLie S κ := by
  unfold haarLie
  rw [Measure.map_smul]
  congr 1
  set E : lieE S → Formalism.QuantumDeterminants.Mt k r := fun x => fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j with hE
  by_cases hm : AEMeasurable E volume
  · let Φ₀ : lieE S →ₗᵢ[ℝ] lieE S := ⟨(cjR (2 * r + k + 1)).restrict (cjR_mem hS), norm_cjR_restrict hS⟩
    let Φ : lieE S ≃ₗᵢ[ℝ] lieE S := Φ₀.toLinearIsometryEquiv rfl
    have hΦ := Φ.measurePreserving
    have e : (cjmE (k := k) (r := r)) ∘ E = E ∘ Φ := by
      funext x
      show cjm (fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j) =
        fun i j => NormedSpace.exp (unrealify (cjR (2 * r + k + 1) x)) i j
      rw [unrealify_cjR, exp_map_star]
      rfl
    rw [AEMeasurable.map_map_of_aemeasurable (cjmE (k := k) (r := r)).measurable.aemeasurable hm, e,
      ← AEMeasurable.map_map_of_aemeasurable (by rwa [hΦ.map_eq]) hΦ.measurable.aemeasurable, hΦ.map_eq]
  · rw [Measure.map_of_not_aemeasurable hm, Measure.map_zero]

end Conj2

section Places

variable (D : D7)

def plE : D.what₂.Tau ≃ InfinitePlace D.host.E :=
  Equiv.ofBijective (fun τ => InfinitePlace.mk (embS D τ))
    ((Function.bijective_iff_existsUnique _).2 (GlobalTheory.RealPlaces.existsUnique_place D))

theorem plE_tauOf (w : InfinitePlace D.host.E) : plE D (tauOf D w) = w :=
  (GlobalTheory.RealPlaces.existsUnique_place D w).exists.choose_spec

theorem tauOf_eq (w : InfinitePlace D.host.E) : tauOf D w = (plE D).symm w := by
  rw [Equiv.eq_symm_apply, plE_tauOf]

def cjwE (w : InfinitePlace D.host.E) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS ≃ᵐ Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  if Direct D w then MeasurableEquiv.refl _ else cjmE

theorem cjwE_apply (w : InfinitePlace D.host.E) (M : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) : cjwE D w M = cjw D w M := by
  unfold cjwE cjw
  split_ifs <;> rfl

def GmE : (D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) ≃ᵐ (InfinitePlace D.host.E → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :=
  (MeasurableEquiv.piCongrLeft (fun _ => Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) (plE D)).trans
    (MeasurableEquiv.piCongrRight (fun w => cjwE D w))

theorem coe_GmE : ⇑(GmE D) = Gm D := by
  funext y w
  show cjwE D w ((MeasurableEquiv.piCongrLeft (fun _ => Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) (plE D)) y w) = _
  simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, cjwE_apply, Gm, tauOf_eq, eq_rec_constant]

theorem cjwE_mp (w : InfinitePlace D.host.E) :
    MeasurePreserving (cjwE D w) (haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) := by
  unfold cjwE
  split_ifs
  · exact MeasurePreserving.id _
  · exact ⟨(cjmE).measurable, haarLie_map_cjm (fun g hg => map_star_mem_N hg) 1⟩

theorem GmE_mp : MeasurePreserving (GmE D)
    (Measure.pi fun _ : D.what₂.Tau => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1)
    (Measure.pi fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) := by
  haveI : SigmaFinite (haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) :=
    (GlobalTheory.haarLie_isHaarOn_Nset D.R.k D.R.rS 1 one_pos ENNReal.one_lt_top).1
  have h1 := measurePreserving_piCongrLeft (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (plE D)
  have h2 := measurePreserving_pi (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1)
    (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (cjwE_mp D)
  exact h2.comp h1

end Places

theorem measure_Gm_image : ∀ (D : D7) (S : Set (D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)),
    Measure.pi (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (Gm D '' S) =
      Measure.pi (fun _ : D.what₂.Tau => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) S := by
  intro D S
  rw [← coe_GmE, MeasurableEquiv.image_eq_preimage_symm, ← MeasurableEquiv.map_apply, (GmE_mp D).symm.map_eq]

end GlobalTheory.CovDom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureUnipotentTuplesFreeEntryBlocks
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.BlockMeas

abbrev Yf (k r : ℕ) : Type := (NEntry.Idx k r → ℂ) × (UTr r → ℂ) × (Fin r → ℝ)

abbrev Ys (k r : ℕ) : Type :=
  ((UTr r → ℂ) × (Fin r → Fin (k + 1) → ℂ)) × ((UTr r → ℂ) × (Fin r → ℝ))

abbrev Zb (ι : Type) (k r : ℕ) : Type :=
  (UTr r → ι → ℂ) × (Fin r → ι → Fin (k + 1) → ℂ) × (UTr r → ι → ℂ) × (Fin r → ι → ℝ)

def sp (ι : Type) (k r : ℕ) (y : ι → Yf k r) : Zb ι k r :=
  (fun p w => (y w).1 (NEntry.idx k r (.inl p)), fun a w j => (y w).1 (NEntry.idx k r (.inr (a, j))),
    fun p w => (y w).2.1 p, fun a w => (y w).2.2 a)

def sq (ι : Type) (k r : ℕ) (y : ι → Ys k r) : Zb ι k r :=
  (fun p w => (y w).1.1 p, fun a w => (y w).1.2 a, fun p w => (y w).2.1 p, fun a w => (y w).2.2 a)

theorem sq_mp (ι : Type) [Fintype ι] (k r : ℕ) : MeasurePreserving (sq ι k r) volume volume := by
  have h1 := volume_measurePreserving_arrowProdEquivProdArrow ((UTr r → ℂ) × (Fin r → Fin (k + 1) → ℂ))
    ((UTr r → ℂ) × (Fin r → ℝ)) ι
  have h2 := volume_measurePreserving_arrowProdEquivProdArrow (UTr r → ℂ) (Fin r → Fin (k + 1) → ℂ) ι
  have h3 := volume_measurePreserving_arrowProdEquivProdArrow (UTr r → ℂ) (Fin r → ℝ) ι
  have s1 : MeasurePreserving (fun (f : ι → UTr r → ℂ) (p : UTr r) (i : ι) => f i p) volume volume :=
    ReciprocityTheory.GeometryOfNumbersTheory.measurePreserving_swapPi (volume : Measure ℂ)
  have s2 : MeasurePreserving (fun (f : ι → Fin r → Fin (k + 1) → ℂ) (p : Fin r) (i : ι) => f i p) volume volume :=
    ReciprocityTheory.GeometryOfNumbersTheory.measurePreserving_swapPi (volume : Measure (Fin (k + 1) → ℂ))
  have s3 : MeasurePreserving (fun (f : ι → Fin r → ℝ) (p : Fin r) (i : ι) => f i p) volume volume :=
    ReciprocityTheory.GeometryOfNumbersTheory.measurePreserving_swapPi (volume : Measure ℝ)
  haveI u0 : SigmaFinite (volume : Measure (Fin (k + 1) → ℂ)) := inferInstance
  haveI u1 : SigmaFinite (volume : Measure (Fin r → Fin (k + 1) → ℂ)) := inferInstance
  haveI u2 : SigmaFinite (volume : Measure (ι → Fin (k + 1) → ℂ)) := inferInstance
  haveI t1 : SigmaFinite (volume : Measure (ι → UTr r → ℂ)) := inferInstance
  haveI t2 : SigmaFinite (volume : Measure (ι → Fin r → Fin (k + 1) → ℂ)) := inferInstance
  haveI t3 : SigmaFinite (volume : Measure (UTr r → ι → ℂ)) := inferInstance
  haveI t4 : SigmaFinite (volume : Measure (Fin r → ι → Fin (k + 1) → ℂ)) := inferInstance
  have a := s1.prod s2
  have b := s1.prod s3
  have c := (a.prod b).comp ((h2.prod h3).comp h1)
  exact (volume_preserving_prodAssoc).comp c

theorem pi_smul (ι : Type) [Fintype ι] {X : Type} [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν] (c : NNReal) :
    Measure.pi (fun _ : ι => (c : ℝ≥0∞) • ν) = ((c : ℝ≥0∞) ^ Fintype.card ι) • Measure.pi (fun _ : ι => ν) := by
  haveI : SigmaFinite ((c : ℝ≥0∞) • ν) := by
    have e : (c : ℝ≥0∞) • ν = c • ν := by
      ext s _
      simp [Measure.smul_apply]
    rw [e]
    infer_instance
  refine Measure.pi_eq fun s hs => ?_
  simp [Measure.smul_apply, Measure.pi_pi, Finset.prod_mul_distrib, smul_eq_mul]

theorem mem_iff (ι : Type) (k r : ℕ) (DU : UTr r → Set (ι → ℂ)) (DH : Fin r → Set (ι → Fin (k + 1) → ℂ))
    (DC : UTr r → Set (ι → ℂ)) (DG : Fin r → Set (ι → ℝ)) (x : ι → Mt k r) :
    (∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet ι k r DU DH DC DG β) ↔
      sp ι k r (fun w => nCoords k r (x w)) ∈
        Set.univ.pi DU ×ˢ Set.univ.pi DH ×ˢ Set.univ.pi DC ×ˢ Set.univ.pi DG := by
  simp only [Sum.forall, Set.mem_prod, Set.mem_univ_pi]
  exact Iff.rfl

theorem measure_blocks : ∀ (ι : Type) [Fintype ι] (k r : ℕ) (DU : UTr r → Set (ι → ℂ)) (DH : Fin r → Set (ι → Fin (k + 1) → ℂ)) (DC : UTr r → Set (ι → ℂ)) (DG : Fin r → Set (ι → ℝ)), (∀ p, MeasurableSet (DU p)) → (∀ a, MeasurableSet (DH a)) → (∀ p, MeasurableSet (DC p)) → (∀ a, MeasurableSet (DG a)) → MeasurableSet {x : ι → Mt k r | (∀ w, Matrix.of (x w) ∈ Nset k r) ∧ ∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet ι k r DU DH DC DG β} ∧ (Measure.pi fun _ : ι => haarLie (Nset k r) 1) {x : ι → Mt k r | (∀ w, Matrix.of (x w) ∈ Nset k r) ∧ ∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet ι k r DU DH DC DG β} = (2 : ℝ≥0∞) ^ (Fintype.card ι * (r * (r - 1) + r * (k + 1))) * ((∏ p, volume (DU p)) * (∏ a, volume (DH a)) * (∏ p, volume (DC p)) * ∏ a, volume (DG a)) := by
  intro ι _ k r DU DH DC DG hU hH hC hG
  obtain ⟨⟨hσ, -, hnull, -⟩, -, -, hmap⟩ := GlobalTheory.T.haar_lie_nilpotent_coordinates k r
  set μ := haarLie (Nset k r) 1 with hμ
  set e := r * (r - 1) + r * (k + 1) with he
  set F : (ι → Mt k r) → (ι → Yf k r) := fun x w => nCoords k r (x w) with hFdef
  set R : Set (Zb ι k r) := Set.univ.pi DU ×ˢ Set.univ.pi DH ×ˢ Set.univ.pi DC ×ˢ Set.univ.pi DG with hRdef
  have hF : Measurable F :=
    measurable_pi_lambda _ fun w => NEntry.cont_nCoords.measurable.comp (measurable_pi_apply w)
  have hsp : Measurable (sp ι k r) := by
    unfold sp
    fun_prop
  have hR : MeasurableSet R :=
    (MeasurableSet.univ_pi hU).prod ((MeasurableSet.univ_pi hH).prod
      ((MeasurableSet.univ_pi hC).prod (MeasurableSet.univ_pi hG)))
  have hNm : MeasurableSet {x : Mt k r | Matrix.of x ∈ Nset k r} := by
    have : IsClosed {x : Mt k r | Matrix.of x ∈ Nset k r} := GlobalTheory.Amp.NLie.closed_N
    exact this.measurableSet
  have hNi : MeasurableSet {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} := by
    have : {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} =
        Set.univ.pi fun _ => {x : Mt k r | Matrix.of x ∈ Nset k r} := by
      ext x
      simp
    rw [this]
    exact MeasurableSet.univ_pi fun _ => hNm
  have hS : {x : ι → Mt k r | (∀ w, Matrix.of (x w) ∈ Nset k r) ∧
      ∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet ι k r DU DH DC DG β} =
      (sp ι k r ∘ F) ⁻¹' R ∩ {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Function.comp_apply]
    rw [mem_iff]
    exact and_comm
  rw [hS]
  refine ⟨((hsp.comp hF) hR).inter hNi, ?_⟩
  have hconull : (Measure.pi fun _ : ι => μ) {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r}ᶜ = 0 := by
    have : {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r}ᶜ ⊆
        ⋃ w, Function.eval w ⁻¹' {x : Mt k r | Matrix.of x ∉ Nset k r} := by
      intro x hx
      simpa using hx
    refine measure_mono_null this (measure_iUnion_null fun w => ?_)
    exact Measure.pi_eval_preimage_null _ hnull
  rw [measure_inter_conull hconull]
  have hc : ((2 : ℝ≥0∞) ^ e) = ((2 ^ e : NNReal) : ℝ≥0∞) := by
    push_cast
    rfl
  haveI : SigmaFinite (μ.map (nCoords k r)) := by
    rw [hmap, hc]
    have e' : ((2 ^ e : NNReal) : ℝ≥0∞) • (volume : Measure (Yf k r)) = (2 ^ e : NNReal) • volume := by
      ext s _
      simp [Measure.smul_apply]
    rw [e']
    infer_instance
  have hpi : (Measure.pi fun _ : ι => μ).map F = Measure.pi fun _ : ι => μ.map (nCoords k r) :=
    Measure.pi_map_pi (fun _ => NEntry.cont_nCoords.measurable.aemeasurable)
  have hpre : (sp ι k r ∘ F) ⁻¹' R = F ⁻¹' (sp ι k r ⁻¹' R) := rfl
  rw [hpre, ← Measure.map_apply hF (hsp hR), hpi, hmap, hc, pi_smul, Measure.smul_apply, smul_eq_mul]

  have hΦ : MeasurePreserving (fun (y : ι → Ys k r) w => ((NEntry.glue (y w).1, (y w).2) : Yf k r)) volume volume :=
    volume_preserving_pi (f := fun _ : ι => Prod.map (NEntry.glue (k := k) (r := r)) id)
      fun _ => (NEntry.glue_mp (k := k) (r := r)).1.prod (MeasurePreserving.id _)
  have hcomp : (fun (y : ι → Ys k r) w => ((NEntry.glue (y w).1, (y w).2) : Yf k r)) ⁻¹' (sp ι k r ⁻¹' R) =
      sq ι k r ⁻¹' R := by
    ext y
    have : sp ι k r (fun w => ((NEntry.glue (y w).1, (y w).2) : Yf k r)) = sq ι k r y := by
      simp [sp, sq, NEntry.glue]
    simp only [Set.mem_preimage, this]
  have hvol : (Measure.pi fun _ : ι => (volume : Measure (Yf k r))) (sp ι k r ⁻¹' R) = volume R := by
    have h1 := hΦ.measure_preimage (hsp hR).nullMeasurableSet
    rw [hcomp, (sq_mp ι k r).measure_preimage hR.nullMeasurableSet] at h1
    exact h1.symm
  haveI u0 : SigmaFinite (volume : Measure (Fin (k + 1) → ℂ)) := inferInstance
  haveI u2 : SigmaFinite (volume : Measure (ι → Fin (k + 1) → ℂ)) := inferInstance
  haveI t3 : SigmaFinite (volume : Measure (UTr r → ι → ℂ)) := inferInstance
  haveI t4 : SigmaFinite (volume : Measure (Fin r → ι → Fin (k + 1) → ℂ)) := inferInstance
  haveI t5 : SigmaFinite (volume : Measure (Fin r → ι → ℝ)) := inferInstance
  have hpow : ((2 ^ e : NNReal) : ℝ≥0∞) ^ Fintype.card ι = (2 : ℝ≥0∞) ^ (Fintype.card ι * e) := by
    rw [← hc, ← pow_mul, mul_comm]
  rw [hvol, hRdef, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    Measure.volume_eq_prod, Measure.prod_prod, volume_pi_pi, volume_pi_pi, volume_pi_pi, volume_pi_pi, hpow]
  simp only [mul_assoc]

end GlobalTheory.SnMass.VolN.BlockMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovesToGivesIntegralMatricesStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moves_to_gives_integral_matrices : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (t₀ : TauC Y u u') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ n m, n ∈ NRat (lf D (X.Fu u)) → m ∈ NRat (lf D (X.Fu u')) → ∃ B B' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, (∀ a b, b < a → B a b = 0) ∧ (∀ a, B a a = 1) ∧ (∀ a b, b < a → B' a b = 0) ∧ (∀ a, B' a a = 1) ∧ ∀ b, ρ (n (frame (lf D (X.Fu u)) b)) = ∑ a, B a b • frame F00 a ∧ ρ (n (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b)) = ∑ a, B' a b • frame F'0 a := by
  first | exact @GlobalTheory.MovedFrames.moved_frames | exact GlobalTheory.MovedFrames.moved_frames | (intros; apply GlobalTheory.MovedFrames.moved_frames <;> assumption)
end

