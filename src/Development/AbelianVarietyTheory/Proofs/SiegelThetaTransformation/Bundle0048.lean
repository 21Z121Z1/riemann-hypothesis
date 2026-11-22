import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0047
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledThetaTestFunctionSesquilinearHeisenberg
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GaussianKernelIntegrableOnThinSlab
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MultiplierSqMulDetUnitaryColumnChange
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0009
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PeriodCoordinateThetaOfSignedHeisenbergVacuum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DiscreteTopologyRationalPointsHermitianSpaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteTopology_rationalPoints_hermitianSpace : ∀ (D : D7) (V : HSp D), DiscreteTopology (GQ V) := by
  first | exact @GlobalTheory.RationalDiscrete.discreteTopology_GQ | exact GlobalTheory.RationalDiscrete.discreteTopology_GQ | (intros; apply GlobalTheory.RationalDiscrete.discreteTopology_GQ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledGaussianKernelDiagonalTranslationInvarian
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker.Diag

open GlobalTheory.SW.DblLin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

variable (X) in

noncomputable def kRow (x₁ x₂ : Frame X.Ψ r) (z w : Fin g → ℂ) : ℂ :=
  ∑ τ, cz' X idx x₁ x₂ τ (z, w) ⬝ᵥ (imH (dblZ X x₁ x₂ τ))⁻¹ *ᵥ cz X idx x₁ x₂ τ (z, w)

theorem kZero_eq (x₁ x₂ : Frame X.Ψ r) (z w : Fin n → Fin g → ℂ) :
    kZero X idx x₁ x₂ z w =
      (∏ τ : X.Ψ, (((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det) ^ (n / 2))⁻¹) *
        cexp (π * ∑ k, kRow X idx x₁ x₂ (z k) (w k)) := by
  simp only [kZero, Finset.prod_mul_distrib, ← Complex.exp_sum, ← Finset.mul_sum, kRow]
  rw [Finset.sum_comm]
  rfl

theorem kRow_per (hs : IsSympl X bas) {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom)
    (y : Fin r → E) (z z' : Fin g → ℂ) :
    kRow X idx x₁ x₂ (pv X idx x₁ y + z) (fun i => conj ((pv X idx x₂ y + z') i)) =
      hx X bas idx x₁ (z + (1 / 2 : ℂ) • pv X idx x₁ y) (pv X idx x₁ y) +
      conj (hx X bas idx x₂ (z' + (1 / 2 : ℂ) • pv X idx x₂ y) (pv X idx x₂ y)) +
      kRow X idx x₁ x₂ z (fun i => conj (z' i)) := by
  have h := expo_row idx hs h₁ h₂ y y z (star z')
  have e0 : ∀ τ : X.Ψ, Data.emb τ.1 (0 : Fin r → E) = 0 := fun τ => by
    funext a; simp [Data.emb]
  have e1 : (fun i => conj ((pv X idx x₂ y + z') i)) = star z' + star (per X x₂ y ∘ idx) := by
    funext i; simp [pv, add_comm]
  rw [e1, add_comm (pv X idx x₁ y) z]
  simp only [sub_self, e0, star_zero, zero_dotProduct, dotProduct_zero, add_zero,
    Finset.sum_const_zero, mul_zero, Pi.zero_apply, star_star, hermForm_Hm] at h
  simp only [cc, map_zero, mul_zero, Finset.sum_const_zero, Rat.cast_zero, add_zero] at h
  exact h

theorem continuous_kRow (x₁ x₂ : Frame X.Ψ r) :
    Continuous fun p : (Fin g → ℂ) × (Fin g → ℂ) => kRow X idx x₁ x₂ p.1 p.2 := by
  refine continuous_finsetSum _ fun τ _ => ?_
  exact (cz' X idx x₁ x₂ τ).continuous_of_finiteDimensional.dotProduct
    (continuous_const.matrix_mulVec (cz X idx x₁ x₂ τ).continuous_of_finiteDimensional)

theorem continuous_hx (x : Frame X.Ψ r) :
    Continuous fun z : Fin g → ℂ => hx X bas idx x z z :=
  (continuous_const.matrix_mulVec continuous_id).dotProduct
    (continuous_const.matrix_mulVec (continuous_const.matrix_mulVec continuous_id).star)

theorem kernel_diag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, ∀ a b w : WR X n, cexp (π * I * (EFR X w (a - b) : ℝ)) * (gaussR X bas idx x₁ (zR X idx x₁ (w + a)) * conj (gaussR X bas idx x₂ (zR X idx x₂ (w + b))) * kZero X idx x₁ x₂ (zR X idx x₁ (w + a)) (fun k i => conj (zR X idx x₂ (w + b) k i))) = gaussR X bas idx x₁ (zR X idx x₁ a) * conj (gaussR X bas idx x₂ (zR X idx x₂ b)) * kZero X idx x₁ x₂ (zR X idx x₁ a) (fun k i => conj (zR X idx x₂ b k i)) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn x₁ h₁ x₂ h₂ a b w
  obtain ⟨⟨L₁, hL₁⟩, im₁, -, hd, -⟩ := GlobalTheory.T.realPeriodMap_homeomorph_riemannForm_density E r X g q0 hr bas idx n hs hn x₁ h₁
  obtain ⟨⟨L₂, hL₂⟩, im₂, -⟩ := GlobalTheory.T.realPeriodMap_homeomorph_riemannForm_density E r X g q0 hr bas idx n hs hn x₂ h₂
  have add₁ (u v : WR X n) : zR X idx x₁ (u + v) = zR X idx x₁ u + zR X idx x₁ v := by
    rw [← hL₁, ← hL₁, ← hL₁, map_add]
  have add₂ (u v : WR X n) : zR X idx x₂ (u + v) = zR X idx x₂ u + zR X idx x₂ v := by
    rw [← hL₂, ← hL₂, ← hL₂, map_add]
  have hE (w : WR X n) : EFR X w (a - b) = EFR X w a - EFR X w b := by
    rw [← im₁, ← im₁, ← im₁, ← sub_im, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eq_sub_iff_add_eq, ← GlobalTheory.Dict.fock_hx_add_right, ← Pi.add_apply (zR X idx x₁ (a - b)),
      ← add₁, sub_add_cancel]
  have key : ∀ w : WR X n, π * I * (EFR X w (a - b) : ℝ) +
      (-(π / 2 * ∑ k, hx X bas idx x₁ (zR X idx x₁ (w + a) k) (zR X idx x₁ (w + a) k)) +
        conj (-(π / 2 * ∑ k, hx X bas idx x₂ (zR X idx x₂ (w + b) k) (zR X idx x₂ (w + b) k))) +
        π * ∑ k, kRow X idx x₁ x₂ (zR X idx x₁ (w + a) k) (fun i => conj (zR X idx x₂ (w + b) k i))) =
      -(π / 2 * ∑ k, hx X bas idx x₁ (zR X idx x₁ a k) (zR X idx x₁ a k)) +
        conj (-(π / 2 * ∑ k, hx X bas idx x₂ (zR X idx x₂ b k) (zR X idx x₂ b k))) +
        π * ∑ k, kRow X idx x₁ x₂ (zR X idx x₁ a k) (fun i => conj (zR X idx x₂ b k i)) := by
    intro w
    refine hd.induction_on w (isClosed_eq ?_ continuous_const) fun y => ?_
    · have c₁ (k) : Continuous fun w : WR X n => zR X idx x₁ (w + a) k := by
        simp only [← hL₁]; fun_prop
      have c₂ (k) : Continuous fun w : WR X n => zR X idx x₂ (w + b) k := by
        simp only [← hL₂]; fun_prop
      have c₃ : Continuous fun w : WR X n => EFR X w (a - b) := by
        unfold EFR hermC; fun_prop
      have c₄ := continuous_finsetSum Finset.univ fun k _ =>
        (continuous_hx (bas := bas) idx x₁).comp (c₁ k)
      have c₅ := continuous_finsetSum Finset.univ fun k _ =>
        (continuous_hx (bas := bas) idx x₂).comp (c₂ k)
      have c₆ := continuous_finsetSum Finset.univ fun k _ =>
        (continuous_kRow idx x₁ x₂).comp ((c₁ k).prodMk (c₂ k).star)
      exact (continuous_const.mul (continuous_ofReal.comp c₃)).add
        (((continuous_const.mul c₄).neg.add
          (continuous_conj.comp (continuous_const.mul c₅).neg)).add (continuous_const.mul c₆))
    · have i₁ := sub_conj (∑ k, hx X bas idx x₁ (zR X idx x₁ (embR X y) k) (zR X idx x₁ a k))
      have i₂ := sub_conj (∑ k, hx X bas idx x₂ (zR X idx x₂ (embR X y) k) (zR X idx x₂ b k))
      rw [im₁] at i₁
      rw [im₂] at i₂
      rw [hE, add₁, add₂]
      simp only [Pi.add_apply (zR X idx _ (embR X y)), zR_embR] at i₁ i₂ ⊢
      simp only [kRow_per idx hs h₁ h₂]
      have s₁ (k) := GlobalTheory.Dict.fock_hx_conj X bas idx x₁ hs h₁ (pv X idx x₁ (y k)) (zR X idx x₁ a k)
      have s₂ (k) := GlobalTheory.Dict.fock_hx_conj X bas idx x₂ hs h₂ (pv X idx x₂ (y k)) (zR X idx x₂ b k)
      simp only [GlobalTheory.Dict.fock_hx_add_left, GlobalTheory.Dict.fock_hx_add_right, GlobalTheory.Dict.fock_hx_smul_left,
        s₁, s₂, Finset.sum_add_distrib, ← Finset.mul_sum, ← map_sum, map_add, map_mul, map_neg,
        conj_conj, map_div₀, conj_ofReal, map_ofNat, map_one]
      push_cast at i₁ i₂ ⊢
      linear_combination (-(π : ℂ) / 2) * i₁ + ((π : ℂ) / 2) * i₂
  simp only [gaussR, kZero_eq, ← Complex.exp_conj]
  have := congrArg cexp (key w)
  simp only [Complex.exp_add] at this
  linear_combination (∏ τ : X.Ψ, (((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det) ^ (n / 2))⁻¹) * this

end GlobalTheory.Ker.Diag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledThetaTestFunctionSesquilinearHeisenbergStatement
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → (∀ ψ, IsSB ψ → dbl X bas idx (φ₁ + ψ) φ₂ = dbl X bas idx φ₁ φ₂ + dbl X bas idx ψ φ₂ ∧ dbl X bas idx φ₁ (φ₂ + ψ) = dbl X bas idx φ₁ φ₂ + dbl X bas idx φ₁ ψ) ∧ (∀ a b : ℂ, dbl X bas idx (a • φ₁) (b • φ₂) = (a * conj b) • dbl X bas idx φ₁ φ₂) ∧ ∀ y₁ y₂ : Matrix (Fin n) (Fin r) E, dbl X bas idx (heisG X bas y₁ φ₁) (heisG X bas y₂ φ₂) = heisH (Matrix.fromCols y₁ y₂ * dblT X).toCols₁ (Matrix.fromCols y₁ y₂ * dblT X).toCols₂ (dbl X bas idx φ₁ φ₂) := by
  first | exact @GlobalTheory.SW.DblLin.dbl_lin | exact GlobalTheory.SW.DblLin.dbl_lin | (intros; apply GlobalTheory.SW.DblLin.dbl_lin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsExpansionOfRowHighest
section
section

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr

namespace GlobalTheory.Dict.CuspAny

theorem mem_minorSpan_of_rowHighest {T : Type} [Fintype T] {p q n : ℕ} {c : T → Fin p → ℕ}
    {c' : T → Fin q → ℕ} {P : Harm.Poly ℂ T p q (Fin n)} (hP : P ∈ Harm.rowHighest ℂ c c') :
    P ∈ GaussGauge.minorSpan (Fin n) c c' := by
  classical
  have h : p + q ≤ n + (p + q) := Nat.le_add_left _ _
  let A : Matrix (Fin n) (Fin (n + (p + q))) ℂ :=
    (1 : Matrix _ _ ℂ).submatrix (Fin.castAdd (p + q)) id
  have hA : A * Aᵀ = 1 := by
    ext i j
    simp [A, Matrix.mul_apply, Matrix.one_apply, eq_comm]
  have h1 : Harm.colSubst (fun _ : T => A) (fun _ => Aᵀ) P ∈ GaussGauge.minorSpan _ c c' :=
    GaussGauge.orbitSpan_le_minorSpan h c c'
      (Harm.rowHighest_eq_orbitSpan h c c' ℂ ▸ Harm.colSubst_mem_rowHighest (fun _ => hA) hP)
  have h2 : Harm.colSubst (fun _ : T => Aᵀ) (fun _ => A)
      (Harm.colSubst (fun _ : T => A) (fun _ => Aᵀ) P) = P := by
    rw [← AlgHom.comp_apply, Harm.colSubst_comp]
    simp only [hA]
    rw [Harm.colSubst_one, AlgHom.id_apply]
  rw [← h2]
  refine (Submodule.span_le (p := (GaussGauge.minorSpan (Fin n) c c').comap
    (Harm.colSubst (fun _ : T => Aᵀ) (fun _ => A)).toLinearMap)).2 ?_ h1
  rintro _ ⟨x, rfl⟩
  change Harm.colSubst (fun _ : T => Aᵀ) (fun _ => A) (Harm.minorProd c c' x.1 x.2) ∈
    GaussGauge.minorSpan (Fin n) c c'
  rw [Harm.colSubst_minorProd]
  exact GaussGauge.minorProd_mem_minorSpan _ _ _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {g : ℕ}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
  {q0 : ℕ} (hr : X.p0 + q0 = r) {n : ℕ} {c : X.Ψ → Fin q0 → ℕ} {c' : X.Ψ → Fin X.p0 → ℕ}

theorem exists_expansion_of_rowHighest (hs : IsSympl X bas) (hn : Even n)
    (hc : ∃ τ, (∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ c τ i) ∨
      ∃ i : Fin X.p0, i.val + 1 = X.p0 ∧ 1 ≤ c' τ i)
    (a b : Fin n → Fin g → ℝ) {P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)}
    (hP : P ∈ Harm.rowHighest ℂ c c') {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) :
    ∃ (A : (Fin n → Fin g → ℤ) → ℂ) (ν : (Fin n → Fin g → ℤ) → X.Ψ → ℝ),
      (Summable fun m => ‖A m‖) ∧
      (∀ s : X.Ψ → ℝ, HasSum (fun m => A m * cexp (4 * Real.pi * I * ∑ τ, (ν m τ : ℂ) * s τ))
        (thFr X hr bas idx n a b P (X.flow ξ (fun τ => (s τ : ℂ)) x))) ∧
      ∀ m, A m ≠ 0 → ν m ≠ 0 := by
  obtain ⟨bas', S, hs', hA⟩ := exists_isAdapted hs hξ.2.1
  obtain ⟨a', b', κ, -, -, hκ⟩ := exists_thFr_eq_mul idx hr hs hs' hn a b
  obtain ⟨A, hA1, hA2, hA3⟩ := hA.exists_expansion hr idx hs' hξ n a' b'
    (Harm.isHarmonic_of_mem_rowHighest hP) (mem_minorSpan_of_rowHighest hP) hc hx
  refine ⟨fun m => κ * A m, _, ?_, fun s => ?_,
    fun m hm h0 => hm (mul_eq_zero_of_right κ (hA3 m h0))⟩
  · simpa only [norm_mul] using hA1.mul_left ‖κ‖
  · have hxs := (FlowCoefficientBounds.flow_real X hξ hx s 0).1
    rw [hκ P _ hxs]
    simpa only [mul_assoc] using (hA2 _ hxs).mul_left κ

theorem mem_SS_of_eq_sum_thFr {J : Type} (s : Finset J) (t : J → ℂ) (a b : J → Fin n → Fin g → ℝ)
    {P : J → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)} {Q : Frame X.Ψ r → ℂ} (hs : IsSympl X bas)
    (hn : Even n)
    (hc : ∃ τ, (∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ c τ i) ∨
      ∃ i : Fin X.p0, i.val + 1 = X.p0 ∧ 1 ≤ c' τ i)
    (hP : ∀ j ∈ s, P j ∈ Harm.rowHighest ℂ c c')
    (hQ : ∀ x ∈ X.dom, Q x = ∑ j ∈ s, t j * thFr X hr bas idx n (a j) (b j) (P j) x)
    (hΓ : ∀ ga ∈ X.Γ, ∀ x ∈ X.dom, Q (lact ga x) = X.χ (wtOf X hr c c' n) ga * Q x) :
    Q ∈ X.SS (wtOf X hr c c' n) := by
  have hsec := isSec_of_eq_sum_thFr idx hr s t a b hs hP hQ hΓ
  refine FJZero.mem_SS_of_isModerate X _ Q hsec
    (isModerate_of_eq_sum_thFr idx hr s t a b hs hn hP hQ) fun ξ hξ x hx => ?_
  choose A ν h1 h2 h3 using fun j : s =>
    exists_expansion_of_rowHighest idx hr hs hn hc (a j) (b j) (hP j j.2) hξ hx
  have h4 (j : s) : Summable fun m => ‖t j * A j m‖ := by
    simpa only [norm_mul] using (h1 j).mul_left ‖t j‖
  refine FJZero.fj_eq_zero_of_isSec X _ Q hsec hξ hx
    (fun p : s × (Fin n → Fin g → ℤ) => t p.1 * A p.1 p.2)
    (hasSum_prod_of_fintype h4 fun j => (h4 j).of_norm.hasSum).1 (fun p => ν p.1 p.2)
    (fun u => ?_) 0 fun p hp => h3 _ _ (right_ne_zero_of_mul hp)
  rw [hQ _ (FlowCoefficientBounds.flow_real X hξ hx u 0).1, ← Finset.sum_coe_sort]
  refine (hasSum_prod_of_fintype
    (f := fun (j : s) m => t j * A j m * cexp (4 * Real.pi * I * ∑ τ, (ν j m τ : ℂ) * u τ))
    (fun j => ?_) fun j => ?_).2
  · refine (h4 j).congr fun m => ?_
    have h := FJZero.norm_expo (ν j m) u
    rw [FJZero.expo] at h
    rw [norm_mul (t j * A j m), h, mul_one]
  · simpa only [mul_assoc] using (h2 j u).mul_left (t j)

end GlobalTheory.Dict.CuspAny

end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.CuspAny

theorem mem_SS_of_eq_thP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ((∃ τ, ∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ k τ i) ∨ q0 = 0) → ∀ φ : TF n g, IsSB φ → ∀ P ∈ Harm.rowHighest ℂ k k', ∀ Q : Frame X.Ψ r → ℂ, (∀ x ∈ X.dom, Q x = thP X hr bas idx φ P x) → (∀ ga ∈ X.Γ, ∀ x ∈ X.dom, Q (lact ga x) = X.χ (wtOf X hr k k' n) ga * Q x) → Q ∈ X.SS (wtOf X hr k k' n) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn k k' hk φ hφ P hP Q hQ hΓ
  obtain ⟨m, a, b, t, h⟩ := (GlobalTheory.SW.CharLink.harmonicTheta_eq_sum_thetaCharacteristic E r X g q0 hr bas idx n hs hn).2 φ hφ
  rcases hk with ⟨τ, hτ⟩ | h0
  · exact CuspAny.mem_SS_of_eq_sum_thFr idx hr Finset.univ t (fun j k i => (a j k i : ℝ))
      (fun j k i => (b j k i : ℝ)) (P := fun _ => P) hs hn ⟨τ, Or.inl hτ⟩ (fun _ _ => hP)
      (fun x hx => (hQ x hx).trans (h P x hx)) hΓ
  · exact ThFr.mem_SS_of_eq_sum_thFr idx hr Finset.univ t (fun j k i => (a j k i : ℝ))
      (fun j k i => (b j k i : ℝ)) (P := fun _ => P) hs hn
      (Or.inr (CuspClass.not_isIso_of_definite X (by omega))) (fun _ _ => hP)
      (fun x hx => (hQ x hx).trans (h P x hx)) hΓ

end GlobalTheory.Dict.CuspAny
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionaryStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_letterRowWeightDictionary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (σ : c.F →+* ℂ) (r g n : ℕ) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ) (e : Fin g ≃ Lt1 Dw), GoodEmb c σ → r = Dw.p + Dw.q → X.p0 = Dw.q → (∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) → SelfD X X.Λ → Dom a n → ∃ Dc : Dic Dw c σ X g Dw.p n a, Dc.e = e ∧ (LastPos Dw a → 0 < Dw.p → ∃ τ, ∃ i : Fin Dw.p, i.val + 1 = Dw.p ∧ 1 ≤ Dc.k τ i) := by
  first | exact @GlobalTheory.Dict.exists_dic | exact GlobalTheory.Dict.exists_dic | (intros; apply GlobalTheory.Dict.exists_dic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplecticBasisOfSelfD
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level

theorem GlobalTheory.Ker.exists_symplectic_basis_of_selfD : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r : ℕ) (X : Data E r), SelfD X X.Λ →
    ∃ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (_ : Fin g ≃ X.Ψ × Fin r), IsSympl X bas := by
  intro E _ _ _ r X hL

  obtain ⟨bas, hbas⟩ := GlobalTheory.Dict.Letters.exists_isSympl X hL (Fintype.equivFin (X.Ψ × Fin r)).symm
  exact ⟨_, bas, (Fintype.equivFin _).symm, hbas⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GaussianKernelIntegrableOnThinSlabStatement
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianKernel_integrableOn_thin_slab : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ) (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (m : ℕ) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), Even n → (∀ j, P j ∈ Harm.rowHighest ℂ c c') → 2 * r ≤ n → ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → ∀ x₁ ∈ X.dom, IntegrableOn (fun x₂ => kern X hr idx P x₁ x₂) (slab X δ) volume ∧ ∃ C : ℝ, ∀ x₂ ∈ slab X δ, ‖kern X hr idx P x₁ x₂‖ ≤ C := by
  first | exact @GlobalTheory.SW.kern_integrableOn_slab | exact GlobalTheory.SW.kern_integrableOn_slab | (intros; apply GlobalTheory.SW.kern_integrableOn_slab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsWeakOneOfRankZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker

theorem isWeak_one_of_rank_zero (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (h : T.rank = 0) :
    IsWeak ψ S T 1 := by
  haveI : IsEmpty (Fin T.rank) := by rw [h]; infer_instance
  haveI : Subsingleton (WO S T) := ⟨fun a b => by
    first
      | (funext i; exact isEmptyElim i)
      | (funext j i; exact isEmptyElim i)⟩
  refine ⟨fun p f hf => by simpa using hf, fun g k w₀ f _ => ?_, fun γ _ γ' _ f _ => by simp,
    fun μ 𝓕 _ _ p f _ => by simp⟩
  rw [Subsingleton.elim (actO S T g k w₀) w₀]
  simp

end GlobalTheory.Ker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatOEqHatA
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.LatTens

noncomputable def gen {D : D7} (S T : HSp D) (α : Af D.host.F) :
    Matrix (Fin S.rank) (Fin T.rank) D.host.E →+ WO S T :=
  AddMonoidHom.mk' (fun y => Matrix.of fun a k => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] y k a)
    fun y y' => Matrix.ext fun a k => TensorProduct.tmul_add _ (y k a) (y' k a)

def vmv {E : Type} [Field E] {n r : ℕ} (v : Fin n → E) : (Fin r → E) →+ Matrix (Fin n) (Fin r) E :=
  AddMonoidHom.mk' (fun u => vecMulVec v u)
    fun u u' => Matrix.ext fun k a => mul_add (v k) (u a) (u' a)

theorem gen_eq {D : D7} (S T : HSp D) (hS : S.gram = 1) (α : Af D.host.F) (a : D.host.E)
    (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T)
      = gen S T α (vecMulVec (star s) (a • t)) := by
  refine Matrix.ext fun i j => ?_
  simp only [gen, AddMonoidHom.mk'_apply, Matrix.of_apply]
  congr 1
  rw [hS]
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, vecMulVec_apply, Pi.star_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem latO_eq_hatA : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (LS Λ : Lt D.host.E S.rank) (LT L : Lt D.host.E T.rank), (∀ v, v ∈ Λ ↔ star v ∈ LS) → IsAA L LT → latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True) = hatA S T (tens Λ L) := by
  intro D S T C LS Λ LT L hΛ hL
  have hS : S.gram = 1 := C.m.gS

  have hmem : ∀ α : Af D.host.F, α ∈ intAf D.host.F → ∀ a : D.host.E, a ∈ D.host.AA →
      ∀ v : Fin S.rank → D.host.E, v ∈ Λ → ∀ t : Fin T.rank → D.host.E, t ∈ LT →
      gen S T α (vecMulVec v (a • t)) ∈ latO S T (LS : Set (Fin S.rank → D.host.E))
        (LT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    intro α hα a ha v hv t ht
    unfold latO
    apply AddSubgroup.subset_closure
    refine ⟨α, hα, fun _ h => absurd trivial h, a, ha, star v, (hΛ v).1 hv, t, ht, ?_⟩
    rw [gen_eq S T hS α a (star v) t, star_star]
  apply le_antisymm
  · unfold latO
    rw [AddSubgroup.closure_le]
    rintro w ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    rw [gen_eq S T hS α a s t]
    unfold hatA
    apply AddSubgroup.subset_closure
    have hsΛ : star s ∈ Λ := (hΛ (star s)).2 (by rw [star_star]; exact hs)
    have htL : a • t ∈ L := (hL (a • t)).2 (AddSubgroup.subset_closure ⟨a, ha, t, ht, rfl⟩)
    exact ⟨α, hα, vecMulVec (star s) (a • t),
      AddSubgroup.subset_closure ⟨star s, hsΛ, a • t, htL, rfl⟩, rfl⟩
  · unfold hatA
    rw [AddSubgroup.closure_le]
    rintro w ⟨α, hα, y, hy, rfl⟩

    have hT : tens Λ L ≤ (latO S T (LS : Set (Fin S.rank → D.host.E))
        (LT : Set (Fin T.rank → D.host.E)) (fun _ => True)).comap (gen S T α) := by
      unfold tens
      rw [AddSubgroup.closure_le]
      rintro _ ⟨v, hv, u, hu, rfl⟩
      have hL' : AddSubgroup.closure {u | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ t ∈ LT, u = a • t} ≤
          (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
            (fun _ => True)).comap ((gen S T α).comp (vmv v)) := by
        rw [AddSubgroup.closure_le]
        rintro _ ⟨a, ha, t, ht, rfl⟩
        exact hmem α hα a ha v hv t ht
      exact hL' ((hL u).1 hu)
    exact hT hy

end GlobalTheory.Ker.LatTens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MultiplierSqMulDetUnitaryColumnChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplier_sq_mul_det_unitary_column_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ Λ ∈ Vset E n 1, ∀ Λ' ∈ Vset E n 1, ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∀ x ∈ X.dom, ∀ t : ℂ, ‖t‖ = 1 → (∀ z : Fin n → Fin g → ℂ, thA X bas idx (unitv (projA X bas w (tens Λ' L) v)) x (Dict.hAct X idx h z) = t * thA X bas idx (unitv (projA X bas w (tens Λ L) v)) x z) → IsMu (t ^ 2 * ∏ i : Fin g, rowType X (idx i) h.det) := by
  first | exact @GlobalTheory.Phase.Mult.isMu_multiplier_sq_mul_det | exact GlobalTheory.Phase.Mult.isMu_multiplier_sq_mul_det | (intros; apply GlobalTheory.Phase.Mult.isMu_multiplier_sq_mul_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PeriodCoordinateThetaOfSignedHeisenbergVacuumStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodCoordinateTheta_of_signedHeisenbergVacuum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∀ b : Fin g ⊕ Fin g → (Fin r → E), (∀ u, u ∈ L ↔ ∃ m : Fin g ⊕ Fin g → ℤ, u = ∑ j, m j • b j) → (∀ i j, EF X (b i) (b j) = -(omegaStd (Pi.single i 1) (Pi.single j 1) : ℤ)) → ∃ (c₁ c₂ : Fin g → ℂ) (C : ℂ), C ≠ 0 ∧ (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ ∀ x ∈ X.dom, ∀ h τ : Matrix (Fin g) (Fin g) ℂ, h = (Matrix.of fun i k => pv X idx x (b (Sum.inl k)) i)⁻¹ → τ = h * (Matrix.of fun i k => pv X idx x (b (Sum.inr k)) i) → IsUnit h.det ∧ τ ∈ SW.Siegel (Fin g) ∧ (∀ z w' : Fin g → ℂ, hx X bas idx x z w' = (h *ᵥ z) ⬝ᵥ ((τ.map Complex.im)⁻¹.map fun t : ℝ => (t : ℂ)) *ᵥ star (h *ᵥ w')) ∧ (∀ i, eps1 X w (b (Sum.inl i)) = cexp (2 * Real.pi * I * c₁ i) ∧ eps1 X w (b (Sum.inr i)) = cexp (2 * Real.pi * I * c₂ i)) ∧ ∀ z : Fin n → Fin g → ℂ, thA X bas idx v x z = C * h.det ^ (n / 2) * ∏ k, (cexp (Real.pi / 2 * ((h *ᵥ z k) ⬝ᵥ ((τ.map Complex.im)⁻¹.map fun t : ℝ => (t : ℂ)) *ᵥ (h *ᵥ z k))) * thetaChar τ c₁ c₂ (h *ᵥ z k)) := by
  first | exact @GlobalTheory.Dict.VacForm.thA_vacuum | exact GlobalTheory.Dict.VacForm.thA_vacuum | (intros; apply GlobalTheory.Dict.VacForm.thA_vacuum <;> assumption)
end

