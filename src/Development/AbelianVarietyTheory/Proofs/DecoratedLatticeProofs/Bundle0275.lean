import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0266
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0254
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0419
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0259
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0260
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatSectionParabolicChange
section
open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem degPS_chart_isSection : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (a : GL (Fin A.rank) (AE D)) (p : siegel A), IsConj A a κ p → ∀ (χ : (AE D)ˣ →* Circle) (s₁ : ℂ), ∀ φ ∈ degPS A a χ s₁, IsSection χ s₁ (fun x => φ (κ.symm x * (p : GA D (dblSp A))⁻¹)) ∧ ∀ (s : ℂ) (g : GA D (dblSp A)), flat A a φ s₁ s g = npow (absA D (aP A p)) (s₁ - s) * stdSec (hgtStd A a κ p) (fun x => φ (κ.symm x * (p : GA D (dblSp A))⁻¹)) s₁ s (κ (g * p)) := by
  intro D A μ hμ κ hκ a p hp χ s₁ φ hφ
  obtain ⟨hlaw, hcont, hK⟩ := (mem_degPS A a).1 hφ
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro q hq a' ha' g
    have hs : κ.symm q ∈ siegel A := (mem_siegel_iff_chart_mem_P D A μ hμ κ hκ _).2 (by simpa using hq)
    have hdet := chart_aP_eq_det D A μ hμ κ hκ ⟨_, hs⟩ a' (by simpa using ha')
    have h1 := hlaw ⟨_, hs⟩ (κ.symm g * (p : GA D (dblSp A))⁻¹)
    rw [hdet] at h1
    show φ (κ.symm (q * g) * (p : GA D (dblSp A))⁻¹) = _
    rw [map_mul, mul_assoc]
    exact h1
  · exact hcont.comp (((GlobalTheory.T.continuous_standardUnitaryChart_and_symm D A μ hμ κ hκ).2).mul continuous_const)
  · obtain ⟨W, hW, hWk⟩ := isKFinite_iff.1 hK
    refine isKFinite_iff.2 ⟨W.map (LinearMap.funLeft ℂ ℂ (fun x => κ.symm x * (p : GA D (dblSp A))⁻¹)),
      inferInstance, fun k hk => ⟨_, hWk ((p : GA D (dblSp A)) * κ.symm k * (p : GA D (dblSp A))⁻¹) ?_, funext fun x => ?_⟩⟩
    · rw [hp]
      simpa [mul_assoc] using hk
    · change φ ((κ.symm x * (p : GA D (dblSp A))⁻¹) * ((p : GA D (dblSp A)) * κ.symm k * (p : GA D (dblSp A))⁻¹)) =
        φ (κ.symm (x * k) * (p : GA D (dblSp A))⁻¹)
      simp [mul_assoc]
  · intro s g
    have hr : 0 < absA D (aP A p) := hom_pos _ _
    have e1 : npow (absA D (aP A p)) (s₁ - s) * npow (absA D (aP A p)) (s - s₁) = 1 := by
      rw [← npow_add hr]; simp
    simp only [stdSec, hgtStd, map_mul, MulEquiv.symm_apply_apply, mul_inv_cancel_right, Doubling.npow_mul]
    show φ g * npow (hgt A a g) (s - s₁) = _
    linear_combination (-(φ g * npow (hgt A a g) (s - s₁))) * e1

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameValuesPolynomialDetStableHomogeneous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KJInf.ValPol

variable {ι : Type} [Fintype ι] {a : ℕ}

theorem evalAt_eq (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    evalAt y F = MvPolynomial.eval (fun x : ι × Fin a × Fin a => y x.1 x.2.1 x.2.2) F := rfl

theorem evalAt_frDet (y : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) :
    evalAt y (Formalism.L2.Ker.frDet ℂ a τ) = (y τ).det := by
  rw [evalAt_eq, Formalism.L2.Ker.frDet, RingHom.map_det]
  congr 1
  ext i j
  simp [RingHom.mapMatrix_apply]

theorem evalAt_mul_prod (y : ι → Matrix (Fin a) (Fin a) ℂ) (P : PY ι a) (n : ι → ℕ) :
    evalAt y (P * ∏ τ, (Formalism.L2.Ker.frDet ℂ a τ : PY ι a) ^ n τ) = evalAt y P * ∏ τ, (y τ).det ^ n τ := by
  rw [evalAt_eq, map_mul, map_prod, ← evalAt_eq]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, ← evalAt_eq, evalAt_frDet]

theorem fnOf_one_apply {G : ι → Matrix (Fin a) (Fin a) ℂ} (s : ι → ℤ) (P : PY ι a) (y : Frames G) :
    fnOf G s 1 P y = (∏ τ, (y.1 τ).det ^ s τ) * evalAt y.1 P := by
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, one_mul, evalAt]

theorem evalAt_lft (g y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    evalAt y (lft g F) = evalAt (fun τ => g τ * y τ) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [evalAt, lft]
  | add p q hp hq => simp only [evalAt, map_add] at *; rw [hp, hq]
  | mul_X p v hp =>
    simp only [evalAt, map_mul] at *
    rw [hp]
    simp [lft, Matrix.mul_apply]

theorem shift_eq {G : ι → Matrix (Fin a) (Fin a) ℂ} (lam : ι → DomWeight a) {n : ι → ℕ} {s : ι → ℤ}
    (hns : ∀ τ, (n τ : ℤ) = shiftOf lam τ + s τ) (P : PY ι a) (y : Frames G) :
    evalAt y.1 (P * ∏ τ, (Formalism.L2.Ker.frDet ℂ a τ : PY ι a) ^ n τ) * ∏ τ, (y.1 τ).det ^ (-s τ) =
      fnOf G (shiftOf lam) 1 P y := by
  rw [evalAt_mul_prod, fnOf_one_apply, mul_assoc, mul_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hd : (y.1 τ).det ≠ 0 := (y.2 τ).ne_zero
  rw [← zpow_natCast, ← zpow_add₀ hd, hns τ]
  congr 1
  ring

theorem mem_valC_iff (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a) (n : ι → ℕ) (s : ι → ℤ)
    (hns : ∀ τ, (n τ : ℤ) = shiftOf lam τ + s τ) (Φ : Frames G → ℂ) :
    Φ ∈ ValC G lam ↔ ∃ F ∈ Vn lam n, ∀ y, Φ y = evalAt y.1 F * ∏ τ, (y.1 τ).det ^ (-s τ) := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨_, ⟨P, hP, rfl⟩, fun y => (shift_eq lam hns P y).symm⟩
  · rintro ⟨F, ⟨P, hP, rfl⟩, hΦ⟩
    refine ⟨P, hP, funext fun y => ?_⟩
    rw [hΦ y]
    exact (shift_eq lam hns P y).symm

def nOf (lam : ι → DomWeight a) : ι → ℕ := fun τ => (shiftOf lam τ).toNat

def sOf (lam : ι → DomWeight a) : ι → ℤ := fun τ => (nOf lam τ : ℤ) - shiftOf lam τ

theorem nOf_eq (lam : ι → DomWeight a) (τ : ι) : (nOf lam τ : ℤ) = shiftOf lam τ + sOf lam τ := by
  simp [sOf]

theorem valC_eq_map (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a) :
    ValC G lam = (Vn lam (nOf lam)).map (fnOf G (fun τ => -sOf lam τ) 1) := by
  ext Φ
  rw [mem_valC_iff G lam _ _ (nOf_eq lam)]
  constructor
  · rintro ⟨F, hF, hΦ⟩
    refine ⟨F, hF, funext fun y => ?_⟩
    rw [hΦ y, fnOf_one_apply, mul_comm]
  · rintro ⟨F, hF, rfl⟩
    exact ⟨F, hF, fun y => by rw [fnOf_one_apply, mul_comm]⟩

theorem finiteDimensional_valC (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a) :
    FiniteDimensional ℂ (ValC G lam) := by
  haveI := (GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable ι a lam (nOf lam)).1
  rw [valC_eq_map]
  infer_instance

theorem valC_stable (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a) (Φ : Frames G → ℂ) (hΦ : Φ ∈ ValC G lam)
    (g : ι → Matrix (Fin a) (Fin a) ℂ) (Φ' : Frames G → ℂ) (hΦ' : ∀ y y', IsTr g y y' → Φ' y = Φ y') (hg : IsInv g) :
    Φ' ∈ ValC G lam := by
  obtain ⟨F, hF, hΦF⟩ := (mem_valC_iff G lam _ _ (nOf_eq lam) Φ).1 hΦ
  rw [mem_valC_iff G lam _ _ (nOf_eq lam)]
  refine ⟨(∏ τ, (g τ).det ^ (-sOf lam τ)) • lft g F,
    Submodule.smul_mem _ _ ((GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable ι a lam (nOf lam)).2 g F hF), fun y => ?_⟩
  let y' : Frames G := ⟨fun τ => g τ * y.1 τ, fun τ => by rw [Matrix.det_mul]; exact (hg τ).mul (y.2 τ)⟩
  rw [hΦ' y y' (fun τ => rfl), hΦF y']
  have e : evalAt y.1 ((∏ τ, (g τ).det ^ (-sOf lam τ)) • lft g F) =
      (∏ τ, (g τ).det ^ (-sOf lam τ)) * evalAt (fun τ => g τ * y.1 τ) F := by
    rw [evalAt_eq, MvPolynomial.smul_eval, ← evalAt_eq, evalAt_lft]
  rw [e]
  simp only [y', Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
  ring

theorem natW_anti' (l : DomWeight a) : Antitone l.natW := fun i j h =>
  Int.toNat_le_toNat (by have := l.anti h; omega)

theorem isHomogeneous_of_mem_delSq (l : DomWeight a) {f : MvPolynomial (Fin a × Fin a) ℂ} (hf : f ∈ delSq ℂ a l) :
    f.IsHomogeneous (∑ r, l.natW r) := by
  have h : MvPolynomial.IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW a a) f l.natW :=
    (Formalism.GradedWeylDivisibility.weylLeDual ℂ a a le_rfl l.natW (natW_anti' l) hf).1
  intro m hm
  rw [← h hm]
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Formalism.GradedWeylDivisibility.colW]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Pi.single_apply]

theorem eval_smul_of_isHomogeneous {σ : Type} {f : MvPolynomial σ ℂ} {d : ℕ} (hf : f.IsHomogeneous d)
    (c : ℂ) (v : σ → ℂ) : MvPolynomial.eval (c • v) f = c ^ d * MvPolynomial.eval v f := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have : m.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (MvPolynomial.mem_support_iff.1 hm)
  rw [← this, Finsupp.degree_apply]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

theorem sum_w_eq (l : DomWeight a) : ∑ i, l.w i = ∑ i, ((l.natW i : ℕ) : ℤ) + (a : ℤ) * l.detShift := by
  have h : ∀ i, ((l.natW i : ℕ) : ℤ) = l.w i - l.detShift := by
    intro i
    have hpos : 0 < a := Fin.pos i
    have hle : l.w ⟨a - 1, by omega⟩ ≤ l.w i := l.anti (Fin.le_iff_val_le_val.2 (by simp; omega))
    simp only [DomWeight.natW, DomWeight.detShift, dif_pos hpos]
    exact Int.toNat_of_nonneg (by omega)
  simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem evalAt_scale_cSpan (lam : ι → DomWeight a) (z : ι → ℂ) (y y' : ι → Matrix (Fin a) (Fin a) ℂ)
    (hy : ∀ τ, y' τ = z τ • y τ) (P : PY ι a) (hP : P ∈ CSpan lam) :
    evalAt y' P = (∏ τ, z τ ^ (∑ i, (lam τ).natW i)) * evalAt y P := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    simp only [evalAt_eq, ten, map_prod, MvPolynomial.eval_rename]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have e : ((fun x : ι × Fin a × Fin a => y' x.1 x.2.1 x.2.2) ∘ Prod.mk τ) =
        z τ • ((fun x : ι × Fin a × Fin a => y x.1 x.2.1 x.2.2) ∘ Prod.mk τ) := by
      funext x
      simp [hy τ]
    rw [e, eval_smul_of_isHomogeneous (isHomogeneous_of_mem_delSq (lam τ) (hf τ))]
  | zero => simp [evalAt_eq]
  | add p q _ _ hp hq => simp only [evalAt_eq, map_add] at *; rw [hp, hq]; ring
  | smul c p _ hp => simp only [evalAt_eq, MvPolynomial.smul_eval] at *; rw [hp]; ring

theorem valC_homog (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a) (Φ : Frames G → ℂ) (hΦ : Φ ∈ ValC G lam)
    (z : ι → ℂ) (y y' : Frames G) (hy : ∀ τ, y'.1 τ = z τ • y.1 τ) :
    Φ y' = (∏ τ, z τ ^ (∑ i, (lam τ).w i)) * Φ y := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have : y' = y := Subtype.ext (funext fun τ => Subsingleton.elim _ _)
    simp [this]
  obtain ⟨P, hP, rfl⟩ := hΦ
  rw [fnOf_one_apply, fnOf_one_apply, evalAt_scale_cSpan lam z y.1 y'.1 hy P hP]
  have hz : ∀ τ, z τ ≠ 0 := by
    intro τ h0
    have hne := (y'.2 τ).ne_zero
    haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
    rw [hy τ, h0, zero_smul, Matrix.det_zero] at hne
    exact hne rfl
  have per : ∀ (zz d : ℂ) (sh : ℤ) (deg : ℕ) (W : ℤ), zz ≠ 0 → W = deg + a * sh →
      (zz ^ a * d) ^ sh * zz ^ deg = zz ^ W * d ^ sh := by
    intro zz d sh deg W hz hW
    rw [mul_zpow, ← zpow_natCast zz a, ← _root_.zpow_mul, hW, zpow_add₀ hz, zpow_natCast]
    ring
  have key : (∏ τ, (y'.1 τ).det ^ shiftOf lam τ) * ∏ τ, z τ ^ (∑ i, (lam τ).natW i) =
      (∏ τ, z τ ^ (∑ i, (lam τ).w i)) * ∏ τ, (y.1 τ).det ^ shiftOf lam τ := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hy τ, Matrix.det_smul, Fintype.card_fin]
    exact per _ _ _ _ _ (hz τ) (by rw [sum_w_eq, Nat.cast_sum]; rfl)
  linear_combination (evalAt y.1 P) * key

end GlobalTheory.KJInf.ValPol

theorem GlobalTheory.KJInf.valC_poly : ∀ (ι : Type) [Fintype ι] (a : ℕ) (G : ι → Matrix (Fin a) (Fin a) ℂ) (lam : ι → DomWeight a), (∀ (n : ι → ℕ) (s : ι → ℤ), (∀ τ, (n τ : ℤ) = shiftOf lam τ + s τ) → ∀ Φ : Frames G → ℂ, Φ ∈ ValC G lam ↔ ∃ F ∈ Vn lam n, ∀ y, Φ y = evalAt y.1 F * ∏ τ, (y.1 τ).det ^ (-s τ)) ∧ FiniteDimensional ℂ (ValC G lam) ∧ (∀ Φ ∈ ValC G lam, ∀ g : ι → Matrix (Fin a) (Fin a) ℂ, ∀ Φ' : Frames G → ℂ, (∀ y y', IsTr g y y' → Φ' y = Φ y') → IsInv g → Φ' ∈ ValC G lam) ∧ ∀ Φ ∈ ValC G lam, ∀ (z : ι → ℂ) (y y' : Frames G), (∀ τ, y'.1 τ = z τ • y.1 τ) → Φ y' = (∏ τ, z τ ^ (∑ i, (lam τ).w i)) * Φ y := by
  intro ι _ a G lam
  refine ⟨fun n s hns Φ => GlobalTheory.KJInf.ValPol.mem_valC_iff G lam n s hns Φ,
    GlobalTheory.KJInf.ValPol.finiteDimensional_valC G lam,
    fun Φ hΦ g Φ' hΦ' hg => GlobalTheory.KJInf.ValPol.valC_stable G lam Φ hΦ g Φ' hΦ' hg,
    fun Φ hΦ z y y' hy => GlobalTheory.KJInf.ValPol.valC_homog G lam Φ hΦ z y y' hy⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeOperatorInverseCosetConjEigenvalue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HeckeAdjEigen

variable {D : D7} {V : HSp D}

open GlobalTheory.FinZeta (bddAut bddRep coe_bddRep)

theorem exists_dual_rep (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (R : Finset (GA D V))
    (e f : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (α : GA D V)
    (hS : OffS D Sb P) (hef : IsPrimeIdem P e f) (hϖ : ϖ ∈ P.asIdeal) (hϖ2 : ϖ ∉ P.asIdeal ^ 2)
    (hd : d.Pairwise (fun a b => b ≤ a)) (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅))
    (hχ : ∀ g ∈ J, SuppF V f g → χ g = 1) (hα : SuppF V f α) (hdiv : DivAt V e (ϖ : D.host.E) d α)
    (hrep : IsCosetRep V {k | k ∈ J ∧ SuppF V f k} α R) :
    ∃ R' : Finset (GA D V), Hecke₂ V J χ Sb P (dualLab d) R' ∧ R'.card = R.card ∧
      ∀ γ ∈ R', ∃ k₁ ∈ {k | k ∈ J ∧ SuppF V f k}, ∃ k₂ ∈ {k | k ∈ J ∧ SuppF V f k}, γ = k₁ * α⁻¹ * k₂ := by
  obtain ⟨he, v, hf⟩ := GlobalTheory.HeckeDual.idem_of_isPrimeIdem hef
  obtain ⟨a, rfl⟩ := (GlobalTheory.HeckeDual.suppF_iff V hf α).1 hα
  obtain ⟨δ, hδ, hσδ⟩ := GlobalTheory.HeckeDual.exists_skew D
  haveI := GlobalTheory.HeckeDual.isLattice_frameLat V
  have hK : ∀ g, g ∈ {k | k ∈ J ∧ SuppF V f k} ↔
      ∃ k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.frameLat V) v,
        GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k = g := fun g => by
    constructor
    · rintro ⟨h1, h2⟩
      have h3 := (hJ g h2).1 h1
      obtain ⟨k, rfl⟩ := (GlobalTheory.HeckeDual.suppF_iff V hf g).1 h2
      rw [GlobalTheory.AdelicU.KsphC_eq] at h3
      have h4 := (GlobalTheory.AdelicU.mem_levelOff.1 h3).2.2 v (Finset.notMem_empty v)
      rw [GlobalTheory.AdelicU.proj_emb_self] at h4
      exact ⟨k, h4, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      have h2 := (GlobalTheory.HeckeDual.suppF_iff V hf _).2 ⟨k, rfl⟩
      refine ⟨(hJ _ h2).2 ?_, h2⟩
      rw [GlobalTheory.AdelicU.KsphC_eq]
      exact GlobalTheory.AdelicU.emb_mem_levelOff (Finset.notMem_empty v) hk
  obtain ⟨R', h1, h2, h3⟩ := GlobalTheory.HeckeDual.exists_rep_inv
    (GlobalTheory.HeckeDual.modular_eq_one D.sp.cm.sig V.gram (fun x => star_star x) hδ hσδ
      ((GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V) v)
    (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v) (GlobalTheory.AdelicU.emb_injective _ _ v) _
    (GlobalTheory.AdelicU.isOpen_stabLoc _ _ _ v) (GlobalTheory.AdelicU.isCompact_stabLoc _ _ _ v) _ hK a R
    (fun γ hγ => (hrep.1 γ hγ).2) hrep.2
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := fun h => hϖ2 (by
    rw [show ϖ = 0 from RingOfIntegers.ext h]
    exact zero_mem _)
  refine ⟨R', ⟨e, f, ϖ, _, hS, hef, hϖ, hϖ2, ?_, hJ, hχ, (GlobalTheory.HeckeDual.suppF_iff V hf _).2 (inv_mem ⟨a, rfl⟩),
    (GlobalTheory.DivDual.divAt_inv_and_mul V e _ d _ he hϖ0 hdiv).1, fun γ hγ => (GlobalTheory.HeckeDual.suppF_iff V hf _).2 (h1 γ hγ).1,
    fun γ hγ => ⟨?_, (h1 γ hγ).2⟩, h2⟩, h3, fun γ hγ => (h1 γ hγ).2⟩
  · rw [dualLab, List.pairwise_reverse, List.pairwise_map]
    exact hd.imp fun h => neg_le_neg h
  · obtain ⟨x, rfl⟩ := (h1 γ hγ).1
    exact GlobalTheory.AdelicU.mem_finPts.2 (GlobalTheory.AdelicU.projInf_emb _ _ v x)

theorem form_sum (B : bddAut V →ₗ[ℂ] bddAut V →ₛₗ[starRingEnd ℂ] ℂ)
    (hinv : ∀ g v w, B (bddRep V g v) (bddRep V g w) = B v w) (K : Set (GA D V)) (F : bddAut V)
    (hF : ∀ k ∈ K, bddRep V k F = F) (α : GA D V) (R : Finset (GA D V))
    (hR : ∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂) :
    B (∑ γ ∈ R, bddRep V γ F) F = (R.card : ℂ) * B (bddRep V α F) F := by
  rw [map_sum, LinearMap.sum_apply]
  rw [Finset.sum_congr rfl (g := fun _ => B (bddRep V α F) F), Finset.sum_const, nsmul_eq_mul]
  intro γ hγ
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hR γ hγ
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hF k₂ hk₂]
  have h := hinv k₁ (bddRep V α F) F
  rwa [hF k₁ hk₁] at h

theorem form_inv (B : bddAut V →ₗ[ℂ] bddAut V →ₛₗ[starRingEnd ℂ] ℂ)
    (hsym : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hinv : ∀ g v w, B (bddRep V g v) (bddRep V g w) = B v w) (F : bddAut V) (α : GA D V) :
    B (bddRep V α⁻¹ F) F = starRingEnd ℂ (B (bddRep V α F) F) := by
  have h := hinv α⁻¹ F (bddRep V α F)
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h
  rw [h, hsym]

theorem coe_sum_bddRep (f : GA D V → ℂ) (hf : f ∈ bddAut V) (R : Finset (GA D V)) :
    ((∑ γ ∈ R, bddRep V γ ⟨f, hf⟩ : bddAut V) : GA D V → ℂ) = heckeLin V R f := by
  funext g
  rw [Submodule.coe_sum, Finset.sum_apply, heckeLin_apply]
  rfl

theorem heckeLin_eq_conj_of_dualLab : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SphOff J χ Sb → ∀ f ∈ GlobalTheory.FinZeta.bddAut V, (∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) → ∀ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, (∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = e P (dualLab d) • f) → ∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = conj (e P d) • f := by
  intro D V J χ Sb _ f hf hJχ ev heig P d R hR
  obtain ⟨e, f', ϖ, α, hS, hef, hϖ, hϖ2, hd, hJ, hχ, hα, hdiv, -, hrep⟩ := id hR
  obtain ⟨R', hR', hcard, hR're⟩ := exists_dual_rep J χ Sb P d R e f' ϖ α hS hef hϖ hϖ2 hd hJ hχ hα hdiv hrep
  obtain ⟨B, hsym, hpos, hinv⟩ := (GlobalTheory.FinZeta.bddRep_unitarisable_and_bounded D V).1
  set F : bddAut V := ⟨f, hf⟩ with hFdef
  have hFK : ∀ k ∈ {k | k ∈ J ∧ SuppF V f' k}, bddRep V k F = F := fun k hk => by
    refine Subtype.ext (funext fun g => ?_)
    rw [coe_bddRep]
    show f (g * k) = f g
    rw [hJχ k hk.1, hχ k hk.1 hk.2, one_mul]
  have e1 := heig P d R hR
  have e2 := heig P (dualLab d) R' hR'
  rw [show dualLab (dualLab d) = d by simp [dualLab, List.map_reverse]] at e2
  have s1 : (∑ γ ∈ R, bddRep V γ F) = ev P (dualLab d) • F := Subtype.ext (by
    rw [coe_sum_bddRep, e1]; rfl)
  have s2 : (∑ γ ∈ R', bddRep V γ F) = ev P d • F := Subtype.ext (by
    rw [coe_sum_bddRep, e2]; rfl)
  have t1 := form_sum B hinv _ F hFK α R (fun γ hγ => (hrep.1 γ hγ).2)
  have t2 := form_sum B hinv _ F hFK α⁻¹ R' hR're
  rw [form_inv B hsym hinv, s2, hcard, map_smul, LinearMap.smul_apply, smul_eq_mul] at t2
  rw [s1, map_smul, LinearMap.smul_apply, smul_eq_mul] at t1
  by_cases h0 : F = 0
  · have : f = 0 := congrArg Subtype.val h0
    subst this
    rw [map_zero, smul_zero]
  · have hb : B F F ≠ 0 := fun h => by
      have := hpos F h0
      rw [h, Complex.zero_re] at this
      exact lt_irrefl _ this
    have hbr : starRingEnd ℂ (B F F) = B F F := (hsym F F).symm
    have key : ev P (dualLab d) = starRingEnd ℂ (ev P d) := by
      apply mul_right_cancel₀ hb
      rw [t1, ← hbr, ← map_mul, t2, map_mul, map_natCast, Complex.conj_conj]
    rw [e1, key]

end GlobalTheory.HeckeAdjEigen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationExtendByZeroSourceSlice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem comb_extS_slice :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (c : WO A T →₀ ℂ) (f : WO S T → ℂ) (y : WO L T) (w : WO A T), comb ψ A T c (fun w' => f ((o.resS T).symm (w', y))) w = comb ψ S T (extS o T c) f ((o.resS T).symm (w, y)) := by
  intro D ψ S A L T o c f y w
  classical
  have hinj : Function.Injective (fun a : WO A T => (o.resS T).symm (a, 0)) := fun a b h => by
    simpa using h
  unfold comb extS
  rw [Finsupp.mapDomain_support_of_injective hinj, Finset.sum_image (fun a _ b _ h => hinj h),
    Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finsupp.mapDomain_apply hinj, Pi.smul_apply, Pi.smul_apply, heisO_resS_symm]

end GlobalTheory.FinPl.ExtZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationExtendByZeroTargetSlice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem comb_extT_resT_symm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (c : WO T A →₀ ℂ) (f : WO T S → ℂ) (y : WO T L) (w : WO T A), comb ψ T A c (fun w' => f ((o.resT T).symm (w', y))) w = comb ψ T S (extT o T c) f ((o.resT T).symm (w, y)) := by
  intro D ψ S A L T o c f y w
  have h1 : ∀ (X Y : HSp D) (d : WO X Y →₀ ℂ) (g : WO X Y → ℂ) (x : WO X Y),
      comb ψ X Y d g x = d.sum fun u a => a * heisO ψ X Y u g x := by
    intro X Y d g x
    simp only [comb, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, h1, extT, Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  exact Finsupp.sum_congr fun u _ => by rw [heisO_resT_symm]

end GlobalTheory.FinPl.ExtZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergDerivWeilTranslateContinuousCombinatioStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDeriv_weilTranslate_continuous_combination : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) → ∃ (m : ℕ) (N : Fin m → ℝ →+ WO S T) (c : Fin m → GA D S × GA D T → ℂ), (∀ i, Continuous (N i)) ∧ (∀ i s, (N i s).map (finPart D) = 0) ∧ (∀ i, Continuous (c i)) ∧ ∀ p f, IsThetaFunO ψ S T f → GlobalTheory.WeilVacMove.dLine ψ S T M (om p f) = ∑ i, c i p • om p (GlobalTheory.WeilVacMove.dLine ψ S T (N i) f) := by
  first | exact @GlobalTheory.HeisLineComb.dLine_om_comb | exact GlobalTheory.HeisLineComb.dLine_om_comb | (intros; apply GlobalTheory.HeisLineComb.dLine_om_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOneParamDerivOrthDecJoinedEqSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOneParamDeriv_orthDecJoined_eq_sum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W A S A' : HSp D) (d : OrthDec W A (GlobalTheory.ChiGrid.negSp A')) (G : WO A S → WO S A' → ℂ), IsBiTheta ψ A S A' G → ∀ M : ℝ →+ WO W S, Continuous M → (∀ s, (M s).map (finPart D) = 0) → (∀ s, (GlobalTheory.BiTransfer.fstH d S (M s)).map (finPart D) = 0) ∧ (∀ s, (GlobalTheory.BiTransfer.sndH d S (M s)).map (finPart D) = 0) ∧ GlobalTheory.WeilVacMove.dLine ψ W S M (GlobalTheory.BiTransfer.join d S G) = GlobalTheory.BiTransfer.join d S fun u v => GlobalTheory.WeilVacMove.dLine ψ A S ((GlobalTheory.BiTransfer.fstH d S).comp M) (fun u' => G u' v) u + GlobalTheory.WeilVacMove.dLine ψ S A' ((GlobalTheory.BiTransfer.sndH d S).comp M) (G u) v := by
  first | exact @GlobalTheory.BiJoinDeriv.dLine_join | exact GlobalTheory.BiJoinDeriv.dLine_join | (intros; apply GlobalTheory.BiJoinDeriv.dLine_join <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaHeisenbergDerivStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isJointlySmoothBiTheta_heisenbergDeriv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A S A' : HSp D) (G : WO A S → WO S A' → ℂ), IsBiTheta ψ A S A' G → (∀ M : ℝ →+ WO A S, Continuous M → (∀ s, (M s).map (finPart D) = 0) → IsBiTheta ψ A S A' fun u v => GlobalTheory.WeilVacMove.dLine ψ A S M (fun u' => G u' v) u) ∧ ∀ M' : ℝ →+ WO S A', Continuous M' → (∀ s, (M' s).map (finPart D) = 0) → IsBiTheta ψ A S A' fun u v => GlobalTheory.WeilVacMove.dLine ψ S A' M' (G u) v := by
  first | exact @GlobalTheory.BiDeriv.isBiTheta_dLine | exact GlobalTheory.BiDeriv.isBiTheta_dLine | (intros; apply GlobalTheory.BiDeriv.isBiTheta_dLine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaTwoVarCombinationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isJointlySmoothBiTheta_twoVarCombination : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A S A' : HSp D) (C : WO A S → WO S A' → ℂ), IsBiTheta ψ A S A' C → ∀ (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ), IsBiTheta ψ A S A' (biComb ψ A S A' c c' C) := by
  first | exact @GlobalTheory.FrCombAny.biTheta_biComb | exact GlobalTheory.FrCombAny.biTheta_biComb | (intros; apply GlobalTheory.FrCombAny.biTheta_biComb <;> assumption)
end

