import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0146
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0132
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedPointsGramVector
import Formalism.FormalDegreeBessel.Bundle0002
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothContinuousConvolutionRealPointsUnitary
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0134
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0133
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoProdSmallBallAsymptotics
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0147
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberMulTopMinorNormLeTwoPow

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealUnipotentRadicalEmbedsAdelicRadicalStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realUnipotentRadical_embeds_adelicRadical : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (v : InfinitePlace I.F), I.IsIsot W → ∃ Wv : Submodule ℂ (Fin I.n → ℂ), IsIsoC (I.ε v) Wv ∧ ∀ m ∈ NW (I.ε v) Wv, (open Classical in ((Pi.mulSingle v m, 1) : I.GA)) ∈ I.NA W := by
  first | exact @GlobalTheory.RadEmb.radical_embeds | exact GlobalTheory.RadEmb.radical_embeds | (intros; apply GlobalTheory.RadEmb.radical_embeds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.Reciprocity
section
noncomputable section

namespace GlobalTheory.GLm.Recip

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem toG_coe {g : ℕ} [Fact g.Prime] {n : ℕ} (h : Gn g n) : toG (h : Mt g n) = h := by
  unfold toG
  rw [dif_pos h.isUnit]
  exact Units.ext (IsUnit.unit_spec _)

theorem coe_toG {g : ℕ} [Fact g.Prime] {n : ℕ} {M : Mt g n} (h : IsUnit M) : ((toG M : Gn g n) : Mt g n) = M := by
  unfold toG
  rw [dif_pos h]
  exact IsUnit.unit_spec _

theorem mean_conj {G : Type} [Group G] [Fintype G] (χ F : G → ℂ) (hχ : IsClass χ) (c : ℂ) :
    mean (fun x => χ x * (c * ∑ y, F (y⁻¹ * x * y))) = c * ∑ x, F x * χ x := by
  unfold mean
  have h1 : ∀ y : G, ∑ x, χ x * F (y⁻¹ * x * y) = ∑ x, F x * χ x := by
    intro y
    symm
    refine Fintype.sum_equiv (MulAut.conj y).toEquiv _ _ ?_
    intro x
    have : y⁻¹ * (y * x * y⁻¹) * y = x := by group
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
    rw [hχ, this, mul_comm]
  have h2 : ∑ x, χ x * (c * ∑ y, F (y⁻¹ * x * y)) = c * ∑ y : G, ∑ x, χ x * F (y⁻¹ * x * y) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum]; ring
  have h3 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [h2]
  simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem mean_res (g : ℕ) [Fact g.Prime] (c d n : ℕ) (hn : n = c + d) (χ : Gn g n → ℂ)
    (Λ : Gn g c → Gn g d → ℂ) :
    mean (fun p : Gn g c × Gn g d => Λ p.1 p.2 * res c d χ p.1 p.2) =
      ((Finset.univ.filter fun x : Gn g n => InPar c (x : Mt g n)).card : ℂ)⁻¹ * ∑ x : Gn g n,
        if InPar c (x : Mt g n) then Λ (toG (tl c (x : Mt g n))) (toG (br c d (x : Mt g n))) * χ x else 0 := by
  obtain ⟨-, -, hu, -, -, hcard⟩ := GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g c d n hn
  have key : ∀ x : Gn g n, (∑ p : Gn g c × Gn g d, Λ p.1 p.2 *
      (if InPar c (x : Mt g n) ∧ tl c (x : Mt g n) = (p.1 : Mt g c) ∧ br c d (x : Mt g n) = (p.2 : Mt g d)
        then χ x else 0)) =
      if InPar c (x : Mt g n) then Λ (toG (tl c (x : Mt g n))) (toG (br c d (x : Mt g n))) * χ x else 0 := by
    intro x
    by_cases hx : InPar c (x : Mt g n)
    · obtain ⟨h1, h2⟩ := hu x hx
      rw [if_pos hx, Finset.sum_eq_single (toG (tl c (x : Mt g n)), toG (br c d (x : Mt g n)))]
      · rw [if_pos ⟨hx, (coe_toG h1).symm, (coe_toG h2).symm⟩]
      · intro p _ hp
        rw [if_neg, mul_zero]
        rintro ⟨-, e1, e2⟩
        apply hp
        rw [e1, e2, toG_coe, toG_coe]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp [hx]
  unfold mean res
  rw [hcard]
  simp only [← key]
  rw [Finset.sum_comm (γ := Gn g n), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.mul_sum, Fintype.card_prod]
  push_cast
  rw [mul_inv (_ * _)]
  ring

theorem eq_of_mean (G₁ G₂ : Type) [Group G₁] [Group G₂] [Fintype G₁] [Fintype G₂] (A B : G₁ → G₂ → ℂ)
    (hA1 : ∀ y, IsClass fun x => A x y) (hA2 : ∀ x, IsClass (A x)) (hB1 : ∀ y, IsClass fun x => B x y)
    (hB2 : ∀ x, IsClass (B x))
    (h : ∀ Λ : G₁ → G₂ → ℂ, (∀ y, IsClass fun x => Λ x y) → (∀ x, IsClass (Λ x)) →
      mean (fun p : G₁ × G₂ => Λ p.1 p.2 * A p.1 p.2) = mean (fun p : G₁ × G₂ => Λ p.1 p.2 * B p.1 p.2)) :
    A = B := by
  have h0 := h (fun x y => (starRingEnd ℂ) (A x y - B x y))
    (fun y x z => by
      have e1 := hA1 y x z
      have e2 := hB1 y x z
      simp only at e1 e2 ⊢
      rw [e1, e2])
    (fun x y z => by
      simp only
      rw [hA2 x y z, hB2 x y z])
  unfold mean at h0
  have h3 : (Fintype.card (G₁ × G₂) : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
  have h1 := sub_eq_zero.mpr (mul_left_cancel₀ h3 h0)
  rw [← Finset.sum_sub_distrib] at h1
  have h2 : ∑ p : G₁ × G₂, Complex.normSq (A p.1 p.2 - B p.1 p.2) = 0 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, Complex.ofReal_zero, ← h1]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]; ring
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)] at h2
  funext x y
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp (h2 (x, y) (Finset.mem_univ _)))

theorem reciprocity : ∀ (g : ℕ) [Fact g.Prime] , (∀ (a b n : ℕ), n = a + b → ∀ (χ : Gn g n → ℂ) (Φ : Gn g a → Gn g b → ℂ), IsClass χ → mean (fun x => χ x * hcT a b Φ n x) = mean (fun p : Gn g a × Gn g b => res a b χ p.1 p.2 * Φ p.1 p.2)) ∧ (∀ (c d n : ℕ), n = c + d → ∀ (χ : Gn g n → ℂ) (Λ : Gn g c → Gn g d → ℂ), mean (fun p : Gn g c × Gn g d => Λ p.1 p.2 * res c d χ p.1 p.2) = ((Finset.univ.filter fun x : Gn g n => InPar c (x : Mt g n)).card : ℂ)⁻¹ * ∑ x : Gn g n, if InPar c (x : Mt g n) then Λ (toG (tl c (x : Mt g n))) (toG (br c d (x : Mt g n))) * χ x else 0) ∧ ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] [Fintype G₁] [Fintype G₂] (A B : G₁ → G₂ → ℂ), (∀ y, IsClass fun x => A x y) → (∀ x, IsClass (A x)) → (∀ y, IsClass fun x => B x y) → (∀ x, IsClass (B x)) → (∀ Λ : G₁ → G₂ → ℂ, (∀ y, IsClass fun x => Λ x y) → (∀ x, IsClass (Λ x)) → mean (fun p : G₁ × G₂ => Λ p.1 p.2 * A p.1 p.2) = mean (fun p : G₁ × G₂ => Λ p.1 p.2 * B p.1 p.2)) → A = B := by
  intro g _
  refine ⟨?_, mean_res g, eq_of_mean⟩
  intro a b n hn χ Φ hχ
  have h1 := mean_res g a b n hn χ Φ
  have h2 := mean_conj χ (fun x : Gn g n => if InPar a (x : Mt g n) then
    Φ (toG (tl a (x : Mt g n))) (toG (br a b (x : Mt g n))) else 0) hχ
    ((Finset.univ.filter fun x : Gn g n => InPar a (x : Mt g n)).card : ℂ)⁻¹
  simp only [ite_mul, zero_mul] at h2
  rw [← h1] at h2
  simp only [mul_comm (res a b χ _ _)]
  exact h2

end GlobalTheory.GLm.Recip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RegularPosCompl
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem regular_pos_compl : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → γ ∈ GG k r → Gf k r z z' γ ≠ 0 → 0 < Gf k r z z' γ ∧ Dmin k r z z' γ (Fin.last (r + 1)) ≠ 0 ∧ IsUnit (gramM k r z z' γ).det ∧ ∀ y : Fin (2 * r + k + 1) → ℂ, y ≠ 0 → (∀ i, herm (Hpk k r) y (gramVec k r z z' γ i) = 0) → 0 < (herm (Hpk k r) y y).re := by
  intro k r z z' γ hz hz' hT hT' hγ hG

  have hGpos : 0 < Gf k r z z' γ :=
    lt_of_le_of_ne (Formalism.QuantumDeterminants.gNonneg k r z z' hz hz' hT hT' γ hγ) (Ne.symm hG)

  have hdet : (gramM k r z z' γ).det ≠ 0 := by
    intro h0
    apply hG
    have hg := Formalism.QuantumDeterminants.gGram k r z z' hz hz' γ hγ
    rw [h0, mul_zero] at hg
    exact_mod_cast hg

  have hk : 1 ≤ k := by
    by_contra hk0
    have hk' : k = 0 := by omega
    subst hk'
    apply hdet
    have hunit : ¬ IsUnit (gramM 0 r z z' γ) := by
      intro hu
      have h1 := Matrix.rank_of_isUnit _ hu
      rw [Formalism.QuantumDeterminants.gn_gramM_eq] at h1
      have h2 := Matrix.rank_mul_le_right
        ((Formalism.QuantumDeterminants.gnB 0 r z z' γ)ᴴ * Hpk 0 r) (Formalism.QuantumDeterminants.gnB 0 r z z' γ)
      have h3 := Matrix.rank_le_card_height (Formalism.QuantumDeterminants.gnB 0 r z z' γ)
      simp only [Fintype.card_sum, Fintype.card_fin] at h1 h3
      omega
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hunit
    exact hunit
  refine ⟨hGpos, ?_, isUnit_iff_ne_zero.mpr hdet, ?_⟩
  ·
    intro h0
    have hG' := hGpos
    unfold Gf at hG'
    rw [h0, map_zero] at hG'
    have hTT := mul_pos hT hT'
    have hn := Complex.normSq_nonneg (Dmin k r z z' γ ⟨r, by omega⟩)
    nlinarith
  ·
    intro y hy horth
    have hmem : y ∈ Formalism.FourierDecayAlt.C2.Uperp k r z z' γ := by
      rw [Formalism.FourierDecayAlt.C2.Uperp, LinearMap.mem_ker, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
      funext i
      rw [Pi.zero_apply, ← horth i]
      simp [herm, Matrix.mulVec, dotProduct]
    exact (Formalism.FourierDecayAlt.P.gram_independent_signature' k r z z' γ ⟨hk, ⟨hz, hT⟩, ⟨hz', hT'⟩⟩ ⟨hγ, hGpos⟩).2.2.1 y hmem hy

end GlobalTheory.SgInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RepresentativeValuesVectorVariationUnipotentOrbi
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.PathVar

theorem uMat_inj {n : ℕ} {ε : Fin n → Bool} {a b : Formalism.REAL.UJ ε} (h : uMat a = uMat b) : a = b :=
  Subtype.ext (Units.ext h)

theorem uMat_mul' {n : ℕ} {ε : Fin n → Bool} (a b : Formalism.REAL.UJ ε) : uMat (a * b) = uMat a * uMat b := rfl

theorem expU_add {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (s t : ℝ) :
    expU ((s + t) • X) = expU (s • X) * expU (t • X) := by
  apply uMat_inj
  rw [uMat_mul', uMat_expU, uMat_expU, uMat_expU, add_smul, Submodule.coe_add]
  apply Matrix.exp_add_of_commute
  simp only [Submodule.coe_smul]
  exact ((Commute.refl (X : Matrix (Fin n) (Fin n) ℂ)).smul_left s).smul_right t

theorem expU_zero {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) : expU ((0 : ℝ) • X) = 1 := by
  apply uMat_inj
  rw [uMat_expU, zero_smul, Submodule.coe_zero, NormedSpace.exp_zero]
  rfl

noncomputable def pt (B : RowsAut) (E : gInf B) (z : B.I.GA) (t : ℝ) : B.I.GA :=
  z * ((fun v => expU (t • E v)), 1)

theorem pt_add (B : RowsAut) (E : gInf B) (z : B.I.GA) (s t : ℝ) :
    pt B E z (s + t) = pt B E z s * ((fun v => expU (t • E v)), 1) := by
  unfold pt
  rw [mul_assoc]
  congr 1
  refine Prod.ext ?_ (by simp)
  funext v
  exact expU_add _ _ _

theorem pt_zero (B : RowsAut) (E : gInf B) (z : B.I.GA) : pt B E z 0 = z := by
  unfold pt
  have : (((fun v => expU ((0 : ℝ) • E v)), 1) : B.I.GA) = 1 := by
    refine Prod.ext ?_ rfl
    funext v
    exact expU_zero _
  rw [this, mul_one]

theorem hasDerivAt_vv (B : RowsAut) {D : ℕ} (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund))
    (Fr : Fin D → B.Hs → B.I.GA → ℂ) (h : ∀ i, IsReps B (T i) (Fr i)) {P : ℕ} {u : B.Hs} (hu : u ∈ VP B P)
    (E : gInf B) (z : B.I.GA) (s : ℝ) :
    HasDerivAt (fun t => vv B Fr u (pt B E z t)) (vv B Fr (dAct B E u) (pt B E z s)) s := by
  have h1 : ∀ i, HasDerivAt (fun t => Fr i u (pt B E z t)) (Fr i (dAct B E u) (pt B E z s)) s := by
    intro i
    have h0 := (h i P u hu).2.2 E (pt B E z s)
    rw [← sub_self s] at h0
    have h2 := h0.comp_sub_const s s
    simp only [← pt_add, add_sub_cancel] at h2
    exact h2
  have h2 : HasDerivAt (fun t => fun i => Fr i u (pt B E z t)) (fun i => Fr i (dAct B E u) (pt B E z s)) s :=
    hasDerivAt_pi.2 h1
  exact ((EuclideanSpace.equiv (Fin D) ℂ).symm.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h2

theorem hs_smul_le {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    Formalism.REAL.hs (s • X) ≤ Formalism.REAL.hs X := by
  unfold Formalism.REAL.hs
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.smul_apply, norm_smul, Real.norm_of_nonneg h0]
  exact pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_left (norm_nonneg _) h1) 2

theorem pt_mem_omega (B : RowsAut) (x : B.I.GA) (W : Submodule B.I.E (Fin B.I.n → B.I.E)) (ρ : ℝ)
    (A Z : gInf B)
    (hρ : Real.sqrt (∑ v, Formalism.REAL.hs (A v).1) + Real.sqrt (∑ v, Formalism.REAL.hs (Z v).1) ≤ ρ)
    (hN : ∀ s t : ℝ, ∃ m : B.I.Ginf, ((m, 1) : B.I.GA) ∈ B.I.NA W ∧
      ∀ v, uMat (m v) * uMat (x.1 v) =
        uMat (x.1 v) * NormedSpace.exp ((s : ℂ) • (A v).1) * NormedSpace.exp ((t : ℂ) • (Z v).1))
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    pt B Z (pt B A x s) t ∈ omega B.I x W ρ := by
  refine ⟨by simp [pt], fun v => (s • A v).1, fun v => (t • Z v).1, fun v => ⟨(s • A v).2, (t • Z v).2⟩, ?_,
    fun v => rfl, fun s' t' => ?_⟩
  · refine le_trans (add_le_add (Real.sqrt_le_sqrt ?_) (Real.sqrt_le_sqrt ?_)) hρ
    · exact Finset.sum_le_sum fun v _ => hs_smul_le _ hs.1 hs.2
    · exact Finset.sum_le_sum fun v _ => hs_smul_le _ ht.1 ht.2
  · obtain ⟨m, hm, hm'⟩ := hN (s' * s) (t' * t)
    refine ⟨m, hm, fun v => ?_⟩
    rw [hm' v]
    simp only [Submodule.coe_smul, Complex.coe_smul, smul_smul]

theorem leg (B : RowsAut) (b M : ℝ) (P : ℕ) {D : ℕ} (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund))
    (Fr : Fin D → B.Hs → B.I.GA → ℂ) (hS : StepBoundAt B b P) (h : ∀ i, IsReps B (T i) (Fr i)) (hM : 0 ≤ M)
    (E : gInf B) (z : B.I.GA)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ VP B (P + 1), ‖vv B Fr u (pt B E z t)‖ ≤ M * ‖u‖)
    {u : B.Hs} (hu : u ∈ VP B P) :
    ‖vv B Fr u (pt B E z 1) - vv B Fr u z‖ ≤
      Real.sqrt (∑ v, Formalism.REAL.hs (E v).1) * (Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖) := by
  have := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun t => vv B Fr u (pt B E z t)) (f' := fun s => vv B Fr (dAct B E u) (pt B E z s))
    (C := Real.sqrt (∑ v, Formalism.REAL.hs (E v).1) * (Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖))
    (fun s _ => (hasDerivAt_vv B T Fr h hu E z s).hasDerivWithinAt)
    (fun s hs => by
      refine (hb s (Set.Ico_subset_Icc_self hs) _ (hS.2.2.2.2.2.2 E u hu)).trans ?_
      refine (mul_le_mul_of_nonneg_left (hS.2.2.2.2.2.1 E u hu) hM).trans (le_of_eq ?_)
      ring)
  simpa only [pt_zero] using this

theorem path_variation : ∀ (B : RowsAut) (b ρ M : ℝ) (P : ℕ) (D : ℕ) (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ) (x : B.I.GA) (W : Submodule B.I.E (Fin B.I.n → B.I.E)), StepBoundAt B b P → (∀ i, IsReps B (T i) (Fr i)) → 0 ≤ M → (∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B (P + 1), ‖vv B Fr u y‖ ≤ M * ‖u‖) → ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B P, ‖vv B Fr u y - vv B Fr u x‖ ≤ ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ := by
  intro B b ρ M P D T Fr x W hS h hM hb y hy u hu
  obtain ⟨hy2, A0, Z0, hg, hρ, hy1, hN⟩ := hy
  let A : gInf B := fun v => ⟨A0 v, (hg v).1⟩
  let Z : gInf B := fun v => ⟨Z0 v, (hg v).2⟩
  have hmem := fun s t hs ht => pt_mem_omega B x W ρ A Z hρ hN (s := s) (t := t) hs ht
  have hyeq : y = pt B Z (pt B A x 1) 1 := by
    refine Prod.ext ?_ (by simp [pt, hy2])
    funext v
    apply uMat_inj
    rw [hy1 v]
    simp only [pt, one_smul]
    rfl
  have h1 := leg B b M P T Fr hS h hM A x (fun t ht w hw => by
    have := hb _ (hmem t 0 ht (by simp)) w hw
    rwa [pt_zero] at this) hu
  have h2 := leg B b M P T Fr hS h hM Z (pt B A x 1) (fun t ht w hw => hb _ (hmem 1 t (by simp) ht) w hw) hu
  have hK : 0 ≤ Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ := by
    unfold beP; positivity
  rw [← hyeq] at h2
  calc _ ≤ ‖vv B Fr u y - vv B Fr u (pt B A x 1)‖ + ‖vv B Fr u (pt B A x 1) - vv B Fr u x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (Real.sqrt (∑ v, Formalism.REAL.hs (A0 v)) + Real.sqrt (∑ v, Formalism.REAL.hs (Z0 v))) *
        (Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖) := by
        rw [add_mul, add_comm]; exact add_le_add h1 h2
    _ ≤ ρ * (Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖) := mul_le_mul_of_nonneg_right hρ hK
    _ = _ := by ring

end GlobalTheory.PathVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothContinuousConvolutionRealPointsUnitaryStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_continuous_convolution_realPointsUnitary : ∀ (I : AutInst) (a F : I.Ginf → ℂ), SmoothInf I a → HasCompactSupport a → LocallyIntegrable F (muInf I) → SmoothInf I (fun y => ∫ g, F g * a (y⁻¹ * g) ∂(muInf I)) ∧ Continuous (fun y => ∫ g, F g * a (y⁻¹ * g) ∂(muInf I)) := by
  first | exact @GlobalTheory.SmoothConv.smooth_convolution | exact GlobalTheory.SmoothConv.smooth_convolution | (intros; apply GlobalTheory.SmoothConv.smooth_convolution <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TailMassLeOfMajorantLengthMomentBound
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Cheb

theorem isClosed_GG (k r : ℕ) : IsClosed (GG k r) := by
  unfold GG UH
  exact isClosed_eq (by fun_prop) continuous_const

theorem measurableSet_len_gt (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) (T : ℝ) :
    MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r ∧ T < lA k r z (Matrix.of x) a} := by
  obtain ⟨u, hu, h⟩ := continuousOn_iff'.1 ((LenCont.lA_Sg_continuousOn k r z).1 a) (Set.Ioi T) isOpen_Ioi
  have h1 : MeasurableSet (α := Mt k r) u := IsOpen.measurableSet (α := Mt k r) hu
  have h2 : MeasurableSet (α := Mt k r) (GG k r) := IsClosed.measurableSet (α := Mt k r) (isClosed_GG k r)
  have h3 : {x : Mt k r | Matrix.of x ∈ GG k r ∧ T < lA k r z (Matrix.of x) a} = u ∩ GG k r := by
    rw [← h]
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  rw [h3]
  exact h1.inter h2

theorem cheb_one {X : Type*} [MeasurableSpace X] (ν : Measure X) (l : X → ℝ) (f : X → ℝ≥0∞) (E : Set X)
    (hE : MeasurableSet E) (T : ℝ) (hT : 0 < T) (hl : ∀ x ∈ E, T < l x) (n : ℕ) :
    ∫⁻ x in E, f x ∂ν ≤ ENNReal.ofReal ((T ^ n)⁻¹) * ∫⁻ x, ENNReal.ofReal (l x ^ n) * f x ∂ν := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans (setLIntegral_mono' hE fun x hx => ?_) (setLIntegral_le_lintegral E _)
  have hTn : 0 < T ^ n := pow_pos hT n
  rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hTn.le)]
  refine le_mul_of_one_le_left' ?_
  rw [ENNReal.one_le_ofReal, inv_mul_eq_div, one_le_div hTn]
  exact pow_le_pow_left₀ hT.le (hl x hx).le n

theorem tail_mass_le : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : (Fin (2 * r + k + 1) → ℂ)) (νS : Measure (Mt k r)) (Φ : Mat k r → Wp) (q : ℕ) (H₁ : ℝ), 1 ≤ H₁ → νS {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → MomBd z νS Φ q H₁ → ∀ i : ℕ, ∫⁻ x in {x : Mt k r | Matrix.of x ∈ GG k r ∧ (i = 0 ∨ 2 ^ i * H₁ / 2 < Sg k r z (Matrix.of x))}, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤ ENNReal.ofReal ((r + 1) * 4 ^ q * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * l2SG νS Φ := by
  intro k r Wp _ _ _ z νS Φ q H₁ hH _ _ hM i
  rcases i with _ | j
  · refine (setLIntegral_le_lintegral _ _).trans ?_
    refine le_mul_of_one_le_left' ?_
    rw [ENNReal.one_le_ofReal]
    have h1 : (1 : ℝ) ≤ 4 ^ q := one_le_pow₀ (by norm_num)
    have h2 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    simp only [pow_zero, one_pow, inv_one, mul_one]
    nlinarith
  · set T : ℝ := 2 ^ (j + 1) * H₁ / 2 with hTdef
    have hT' : T = 2 ^ j * H₁ := by rw [hTdef]; ring
    have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hT1 : 1 ≤ T := by rw [hT']; nlinarith
    have hsub : {x : Mt k r | Matrix.of x ∈ GG k r ∧ (j + 1 = 0 ∨ T < Sg k r z (Matrix.of x))} ⊆
        ⋃ a : Fin (r + 1), {x : Mt k r | Matrix.of x ∈ GG k r ∧ T < lA k r z (Matrix.of x) a} := by
      rintro x ⟨hx, h | h⟩
      · omega
      · unfold Sg at h
        rw [Finset.lt_fold_max] at h
        rcases h with h | ⟨a, -, h⟩
        · linarith
        · exact Set.mem_iUnion.2 ⟨a, hx, h⟩
    refine (lintegral_mono_set hsub).trans ((lintegral_iUnion_le _ _).trans ?_)
    rw [tsum_fintype]
    have hone : ∀ a : Fin (r + 1),
        ∫⁻ x in {x : Mt k r | Matrix.of x ∈ GG k r ∧ T < lA k r z (Matrix.of x) a},
          (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤
          ENNReal.ofReal (4 ^ q * ((2 ^ (j + 1) : ℝ) ^ (2 * q))⁻¹) * l2SG νS Φ := by
      intro a
      refine (cheb_one νS (fun x => lA k r z (Matrix.of x) a) _ _ (measurableSet_len_gt k r z a T) T
        (by linarith) (fun x hx => hx.2) (2 * q)).trans ?_
      refine (mul_le_mul_right (hM a) _).trans (le_of_eq ?_)
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      have hH0 : H₁ ≠ 0 := by linarith
      have h4 : (4 : ℝ) ^ q = 2 ^ (2 * q) := by rw [pow_mul]; norm_num
      rw [hT', h4, pow_succ, mul_pow, mul_pow]
      field_simp
    refine (Finset.sum_le_sum fun a _ => hone a).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, mul_assoc ((r : ℝ) + 1),
      ENNReal.ofReal_mul (p := (r : ℝ) + 1) (by positivity)]
    congr 2
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl

end GlobalTheory.Amp.Cheb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoBallMeanBigCellWeight
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens

theorem tendsto_mean_ball_of_continuousAt {r : ℕ} (c : Fin r → ℂ) (f : (Fin r → ℂ) → ℝ≥0∞)
    (hf : ContinuousAt f c) (h1 : f c = 1) :
    Tendsto (fun ρ : ℝ => (∫⁻ x in Metric.ball c ρ, f x) / volume (Metric.ball (0 : Fin r → ℂ) ρ))
      (𝓝[>] 0) (𝓝 1) := by
  rw [ENNReal.tendsto_nhds ENNReal.one_ne_top]
  intro ε hε
  have hfc : Tendsto f (𝓝 c) (𝓝 1) := by rw [← h1]; exact hf
  have hev := (ENNReal.tendsto_nhds ENNReal.one_ne_top).1 hfc ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  filter_upwards [Ioo_mem_nhdsGT hδ] with ρ hρ
  have hV : volume (Metric.ball c ρ) = volume (Metric.ball (0 : Fin r → ℂ) ρ) :=
    Measure.addHaar_ball_center volume c ρ
  have hpos : volume (Metric.ball c ρ) ≠ 0 := (Metric.measure_ball_pos volume c hρ.1).ne'
  have hfin : volume (Metric.ball c ρ) ≠ ⊤ := measure_ball_lt_top.ne
  have hsub : ∀ x ∈ Metric.ball c ρ, f x ∈ Set.Icc (1 - ε) (1 + ε) := fun x hx =>
    hball x (Metric.ball_subset_ball hρ.2.le hx)
  have hlo : (1 - ε) * volume (Metric.ball c ρ) ≤ ∫⁻ x in Metric.ball c ρ, f x := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_ball fun x hx => (hsub x hx).1
  have hhi : ∫⁻ x in Metric.ball c ρ, f x ≤ (1 + ε) * volume (Metric.ball c ρ) := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_ball fun x hx => (hsub x hx).2
  rw [← hV]
  constructor
  · calc 1 - ε = (1 - ε) * volume (Metric.ball c ρ) / volume (Metric.ball c ρ) :=
          (ENNReal.mul_div_cancel_right hpos hfin).symm
      _ ≤ _ := ENNReal.div_le_div_right hlo _
  · calc _ ≤ (1 + ε) * volume (Metric.ball c ρ) / volume (Metric.ball c ρ) :=
          ENNReal.div_le_div_right hhi _
      _ = 1 + ε := ENNReal.mul_div_cancel_right hpos hfin

theorem tendsto_mean_cWeight : ∀ (k r : ℕ), Tendsto (fun ρ : ℝ => (∫⁻ x in Metric.ball (fun _ => 1 : Fin r → ℂ) ρ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r x)) / volume (Metric.ball (0 : Fin r → ℂ) ρ)) (𝓝[>] 0) (𝓝 1) := by
  intro k r
  apply tendsto_mean_ball_of_continuousAt
  · refine (ENNReal.continuous_ofReal.comp ?_).continuousAt
    unfold Formalism.FourierDecayAlt.B2.cWeight
    fun_prop
  · unfold Formalism.FourierDecayAlt.B2.cWeight
    simp

end GlobalTheory.CellDens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoProdSmallBallAsymptoticsStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_prod_smallBall_asymptotics : ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (ν₁ : Measure X) (ν₂ : Measure Y) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] (ρ₁ : X → ℝ) (ρ₂ : Y → ℝ) (d₁ d₂ : ℕ) (C₁ C₂ : ℝ), Measurable ρ₁ → Measurable ρ₂ → (∀ x, 0 ≤ ρ₁ x) → (∀ y, 0 ≤ ρ₂ y) → 0 < C₁ → 0 < C₂ → Filter.Tendsto (fun r : ℝ => ν₁ {x | Real.sqrt (ρ₁ x) ≤ r} / ENNReal.ofReal (r ^ (d₁))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (C₁) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d₁))) 1))) → Filter.Tendsto (fun r : ℝ => ν₂ {x | Real.sqrt (ρ₂ x) ≤ r} / ENNReal.ofReal (r ^ (d₂))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (C₂) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d₂))) 1))) → Filter.Tendsto (fun r : ℝ => (ν₁.prod ν₂) {x | Real.sqrt (ρ₁ x.1 + ρ₂ x.2) ≤ r} / ENNReal.ofReal (r ^ (d₁ + d₂))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (C₁ * C₂) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d₁ + d₂))) 1))) := by
  first | exact @GlobalTheory.SmallBallProd.tendsto_prod_smallBall | exact GlobalTheory.SmallBallProd.tendsto_prod_smallBall | (intros; apply GlobalTheory.SmallBallProd.tendsto_prod_smallBall <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThreeBoxesVolumeProductLeExplicitPowerStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.threeBoxesVolumeProduct_le_explicitPower : ∀ (r : ℕ) (R₀ De : ℝ), 1 ≤ r → 1 ≤ R₀ → 1 ≤ De → (Real.pi * (R₀ ^ (2 * r) * De) ^ 2) ^ (r * (r - 1) / 2) * ((Real.pi * (r * R₀ ^ (4 * r - 2) * De ^ 2) ^ 2) ^ (r * (r - 1) / 2) * (2 * (r * R₀ ^ (4 * r - 2) * De ^ 2)) ^ r) * ((Real.pi * (r * R₀ ^ (2 * r - 1) * De) ^ 2) ^ (3 * r) * 4 * (r * R₀ ^ (2 * r - 1) * De) ^ (2 * r ^ 2 + 2 * r) * Real.pi ^ (r ^ 2)) ≤ (4 * r : ℝ) ^ (11 * r ^ 2) * R₀ ^ (20 * r ^ 3) * De ^ (12 * r ^ 2) := by
  first | exact @GlobalTheory.Amp.volume_product_le | exact GlobalTheory.Amp.volume_product_le | (intros; apply GlobalTheory.Amp.volume_product_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberMulTopMinorNormLeTwoPowStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoFlagsGramNumber_mul_topMinorNorm_le_two_pow : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r), TwoFl k r z z' γ → ∀ x ∈ GG k r, Yv k r z z' γ x * Yv k r z' z γ⁻¹ (γ * x) * Dr k r z z' γ ≤ 2 ^ r := by
  first | exact @GlobalTheory.Amp.LemA.Yv_mul_Yv_mul_Dr_le | exact GlobalTheory.Amp.LemA.Yv_mul_Yv_mul_Dr_le | (intros; apply GlobalTheory.Amp.LemA.Yv_mul_Yv_mul_Dr_le <;> assumption)
end

