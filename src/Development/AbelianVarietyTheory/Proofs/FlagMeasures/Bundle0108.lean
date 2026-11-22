import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0100
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0050
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0075
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularHermitianMassMulLeMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermDoubleCosetMovesFiniteTargetsSplit
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem split_by_target {W Y Z : Type} [AddCommGroup W] (A B : AddSubgroup W) (M : W → Prop) (m : W → Z)
    (f : Y → Z) (hf : Function.Injective f) (hB : Fine A (ind M) B)
    (hm : ∀ w, M w → ∀ b ∈ B, m (w + b) = m w) (hex : ∀ w, M w → ∃ y, f y = m w) (c : ℝ) (hc : 0 ≤ c) :
    {y | ∃ w, M w ∧ f y = m w}.Finite ∧ (∀ y, Nice A (ind fun w => M w ∧ f y = m w)) ∧
    {y | c * (cint A (ind fun w => M w ∧ f y = m w)).re ≠ 0}.Finite ∧
    (∀ y, 0 ≤ c * (cint A (ind fun w => M w ∧ f y = m w)).re) ∧
    ∀ (P : Y → Prop) (g : Y → ℂ) (G : W → ℂ), (∀ w y, (M w ∧ f y = m w) → G w = if P y then g y else 0) →
      (∀ w, ¬ M w → G w = 0) → Nice A G ∧
      ∑ᶠ y : {y // P y}, ((c * (cint A (ind fun w => M w ∧ f y = m w)).re : ℝ) : ℂ) * g y =
        (c : ℂ) * cint A G := by
  obtain ⟨hBA, hidx, hinv, hfin⟩ := hB
  have hsupp : Function.support (ind M) = {w | M w} := by
    ext w
    simp [ind]
  have hMinv : ∀ w, ∀ b ∈ B, (M (w + b) ↔ M w) := by
    intro w b hb
    have h := hinv w b hb
    simp only [ind] at h
    by_cases h1 : M (w + b) <;> by_cases h2 : M w <;> simp [h1, h2] at h ⊢
  have hTfin : {y | ∃ w, M w ∧ f y = m w}.Finite := by
    let g : Y → W ⧸ B := fun y =>
      if h : ∃ w, M w ∧ f y = m w then (QuotientAddGroup.mk h.choose : W ⧸ B) else 0
    refine Set.Finite.of_finite_image (f := g) (hfin.subset ?_) ?_
    · rintro _ ⟨y, hy, rfl⟩
      have hy' : ∃ w, M w ∧ f y = m w := hy
      refine ⟨hy'.choose, ?_, ?_⟩
      · rw [hsupp]
        exact hy'.choose_spec.1
      · simp only [g, dif_pos hy']
    · intro y1 hy1 y2 hy2 heq
      have hy1' : ∃ w, M w ∧ f y1 = m w := hy1
      have hy2' : ∃ w, M w ∧ f y2 = m w := hy2
      simp only [g, dif_pos hy1', dif_pos hy2'] at heq
      apply hf
      rw [hy1'.choose_spec.2, hy2'.choose_spec.2]
      have hb : -hy1'.choose + hy2'.choose ∈ B := QuotientAddGroup.eq.mp heq
      have h := hm _ hy1'.choose_spec.1 _ hb
      rw [add_neg_cancel_left] at h
      exact h.symm
  have hFine : ∀ y, Fine A (ind fun w => M w ∧ f y = m w) B := by
    intro y
    refine ⟨hBA, hidx, ?_, hfin.subset ?_⟩
    · intro w b hb
      simp only [ind]
      by_cases hw : M w
      · have h1 : M (w + b) := (hMinv w b hb).mpr hw
        simp only [h1, hw, true_and, hm w hw b hb]
      · have h1 : ¬ M (w + b) := fun h => hw ((hMinv w b hb).mp h)
        simp only [h1, hw, false_and]
    · apply Set.image_mono
      intro w hw
      rw [hsupp]
      by_contra hM
      refine (Function.mem_support.mp hw) ?_
      simp only [ind]
      rw [if_neg (fun h => hM h.1)]
  have hnice : ∀ y, Nice A (ind fun w => M w ∧ f y = m w) := fun y => ⟨B, hFine y⟩
  have hzero : ∀ y, y ∉ {y | ∃ w, M w ∧ f y = m w} → cint A (ind fun w => M w ∧ f y = m w) = 0 := by
    intro y hy
    have h : (ind fun w => M w ∧ f y = m w) = fun _ => 0 := by
      funext w
      simp only [ind]
      rw [if_neg]
      exact fun h => hy ⟨w, h⟩
    rw [h]
    simp [cint]
  obtain ⟨-, hI2, hI3, hI4⟩ := GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound A
  refine ⟨hTfin, hnice, hTfin.subset ?_, fun y => mul_nonneg hc (hI3 _).1, ?_⟩
  · intro y hy
    change c * _ ≠ 0 at hy
    by_contra hyT
    rw [hzero y hyT] at hy
    simp at hy
  · intro P g G hG hG0
    have hGeq : G = fun w => ∑ y ∈ hTfin.toFinset.filter P, g y * ind (fun w => M w ∧ f y = m w) w := by
      funext w
      by_cases hw : M w
      · obtain ⟨y0, hy0⟩ := hex w hw
        have hy0T : y0 ∈ hTfin.toFinset := by
          rw [Set.Finite.mem_toFinset]
          exact ⟨w, hw, hy0⟩
        rw [hG w y0 ⟨hw, hy0⟩]
        have hother : ∀ y, y ≠ y0 → ind (fun w => M w ∧ f y = m w) w = 0 := by
          intro y hne
          simp only [ind]
          rw [if_neg]
          rintro ⟨-, h⟩
          exact hne (hf (h.trans hy0.symm))
        by_cases hP : P y0
        · rw [if_pos hP, Finset.sum_eq_single y0]
          · simp only [ind]
            rw [if_pos ⟨hw, hy0⟩, mul_one]
          · intro y _ hne
            rw [hother y hne, mul_zero]
          · intro h
            exact absurd (Finset.mem_filter.mpr ⟨hy0T, hP⟩) h
        · rw [if_neg hP, Finset.sum_eq_zero]
          intro y hy
          have hne : y ≠ y0 := by
            rintro rfl
            exact hP (Finset.mem_filter.mp hy).2
          rw [hother y hne, mul_zero]
      · rw [hG0 w hw, Finset.sum_eq_zero]
        intro y _
        simp only [ind]
        rw [if_neg (fun h => hw h.1), mul_zero]
    have hcG : Nice A G ∧ cint A G =
        ∑ y ∈ hTfin.toFinset.filter P, g y * cint A (ind fun w => M w ∧ f y = m w) := by
      obtain ⟨hn, hs⟩ := hI4 Y (hTfin.toFinset.filter P)
        (fun y w => g y * ind (fun w => M w ∧ f y = m w) w) (fun y _ => (hI2 (g y) _ (hnice y)).1)
      rw [hGeq]
      exact ⟨hn, hs.trans (Finset.sum_congr rfl fun y _ => (hI2 (g y) _ (hnice y)).2)⟩
    refine ⟨hcG.1, ?_⟩
    rw [hcG.2]
    have hsub : Function.support (fun y : {y // P y} =>
        ((c * (cint A (ind fun w => M w ∧ f y.1 = m w)).re : ℝ) : ℂ) * g y.1) ⊆
        ↑(hTfin.toFinset.subtype P) := by
      intro y hy
      rw [Finset.mem_coe, Finset.mem_subtype, Set.Finite.mem_toFinset]
      by_contra hyT
      refine (Function.mem_support.mp hy) ?_
      rw [hzero y.1 hyT]
      simp
    rw [finsum_eq_sum_of_support_subset _ hsub]
    refine (Finset.sum_subtype_eq_sum_filter
      (fun y => ((c * (cint A (ind fun w => M w ∧ f y = m w)).re : ℝ) : ℂ) * g y)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have him := (hI3 (fun w => M w ∧ f y = m w)).2
    have hre : ((cint A (ind fun w => M w ∧ f y = m w)).re : ℂ) = cint A (ind fun w => M w ∧ f y = m w) :=
      Complex.ext (by simp) (by simp [him])
    push_cast
    rw [hre]
    ring

theorem moves_split_by_target : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → {Λ₁ : Submodule L.O S.V | ∃ w, S.MvTo (j + 1) d Λ Λ₁ w}.Finite ∧ (∀ Λ₁, Nice (S.refA (j + 1) Λ) (ind (S.MvTo (j + 1) d Λ Λ₁))) ∧ {Λ₁ | S.kern β (j + 1) βJ d Λ Λ₁ ≠ 0}.Finite ∧ (∀ Λ₁, 0 ≤ S.kern β (j + 1) βJ d Λ Λ₁) ∧ ∀ (P : Submodule L.O S.V → Prop) (g : Submodule L.O S.V → ℂ) (G : S.MW → ℂ), (∀ w Λ₁, S.MvTo (j + 1) d Λ Λ₁ w → G w = if P Λ₁ then g Λ₁ else 0) → (∀ w, ¬ S.Mv (j + 1) d Λ w → G w = 0) → Nice (S.refA (j + 1) Λ) G ∧ ∑ᶠ y : {y // P y}, (S.kern β (j + 1) βJ d Λ y : ℂ) * g y = (S.cK β βJ : ℂ) * cint (S.refA (j + 1) Λ) G := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hFF
  obtain ⟨B, hB, hinv⟩ := GlobalTheory.T.exists_fineSubgroup_moves_at_lattice L r k S j β βJ d Λ hT hFF
  have hex : ∀ w, S.Mv (j + 1) d Λ w →
      ∃ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ w.1.1 w.2.1 (S.sOf w) := by
    intro w hw
    obtain ⟨Λ₁, h1, -⟩ := GlobalTheory.T.hermitianDoubleCoset_move_term_weight_character L r k S j β βJ d Λ hT hFF w.1.1 w.1.2 w.2.1 (S.sOf w) hw
    exact ⟨Λ₁, h1⟩
  have hc : 0 ≤ S.cK β βJ := by
    unfold Frames.cK
    positivity
  exact split_by_target (S.refA (j + 1) Λ) B (S.Mv (j + 1) d Λ)
    (fun w => S.moved Λ w.1.1 w.2.1 (S.sOf w)) (fun Λ₁ : Submodule L.O S.V => (Λ₁ : Set S.V))
    SetLike.coe_injective hB (fun w hw b hb => (hinv w hw b hb).1) hex (S.cK β βJ) hc

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvariantPosDefFormEqSmulInnerOfIrreducible
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem exists_endomorphism_representing_sesquilinear_form
    (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : ∃ A : W →ₗ[ℂ] W, ∀ x y, B x y = ⟪x, A y⟫_ℂ := by
  classical
  let e := stdOrthonormalBasis ℂ W
  refine ⟨∑ j, (B (e j)).smulRight (e j), fun x y => ?_⟩
  conv_lhs => rw [← e.sum_repr' x]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, inner_sum, inner_smul_right, smul_eq_mul, inner_conj_symm]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem invariant_posDef_form_eq_smul_inner_of_irreducible :
    ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (I : Type) (π : I → (W →L[ℂ] W)) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), (∀ i v, ‖π i v‖ = ‖v‖) → (∀ S : Submodule ℂ W, (∀ i, ∀ v ∈ S, π i v ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ i x y, B (π i x) (π i y) = B x y) → (∀ x y, B y x = star (B x y)) → (∀ x, x ≠ 0 → 0 < (B x x).re) → ∃ c : ℝ, 0 < c ∧ (Nontrivial W → ∀ x y, B x y = c * ⟪x, y⟫_ℂ) := by
  intro W _ _ _ I π B hiso hirr hinv hherm hpos
  rcases subsingleton_or_nontrivial W with hW | hW
  · exact ⟨1, one_pos, fun h => absurd h (not_nontrivial W)⟩
  obtain ⟨A, hA⟩ := exists_endomorphism_representing_sesquilinear_form W B
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue A
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hAv : A v = μ • v := hv.apply_eq_smul
  have hinner : ∀ i x y, ⟪π i x, π i y⟫_ℂ = ⟪x, y⟫_ℂ := fun i x y =>
    (⟨(π i : W →ₗ[ℂ] W), hiso i⟩ : W →ₗᵢ[ℂ] W).inner_map_map x y
  have hsurj : ∀ i, Function.Surjective (π i) := fun i =>
    (LinearMap.injective_iff_surjective (f := (π i : W →ₗ[ℂ] W))).1
      (⟨(π i : W →ₗ[ℂ] W), hiso i⟩ : W →ₗᵢ[ℂ] W).injective
  let S : Submodule ℂ W :=
    { carrier := {y | ∀ x, B x y = μ * ⟪x, y⟫_ℂ}
      add_mem' := fun {a b} ha hb x => by
        rw [map_add, inner_add_right, ha x, hb x, mul_add]
      zero_mem' := fun x => by simp
      smul_mem' := fun c a ha x => by
        rw [map_smul, inner_smul_right, ha x, smul_eq_mul]; ring }
  have hS : ∀ y, y ∈ S ↔ ∀ x, B x y = μ * ⟪x, y⟫_ℂ := fun y => Iff.rfl
  have hvS : v ∈ S := by
    rw [hS]; intro x
    rw [hA, hAv, inner_smul_right]
  have hstab : ∀ i, ∀ y ∈ S, π i y ∈ S := by
    intro i y hy
    rw [hS] at hy ⊢
    intro x
    obtain ⟨x', rfl⟩ := hsurj i x
    rw [hinv, hinner, hy]
  have htop : S = ⊤ := by
    rcases hirr S hstab with h | h
    · rw [h] at hvS
      exact absurd ((Submodule.mem_bot ℂ).1 hvS) hv0
    · exact h
  have hall : ∀ x y, B x y = μ * ⟪x, y⟫_ℂ := fun x y =>
    (hS y).1 (htop ▸ Submodule.mem_top) x
  have hvv : B v v = μ * ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [hall, inner_self_eq_norm_sq_to_K]; simp
  have hn : (0 : ℝ) < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv0) 2
  have him : μ.im = 0 := by
    have h1 := congrArg Complex.im (hherm v v)
    rw [hvv] at h1
    simp only [Complex.star_def, Complex.conj_im, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re, mul_zero, zero_add] at h1
    have h2 : μ.im * ‖v‖ ^ 2 = 0 := by linarith
    exact (mul_eq_zero.1 h2).resolve_right hn.ne'
  have hre : 0 < μ.re := by
    have h1 := hpos v hv0
    rw [hvv] at h1
    simp only [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, mul_zero, sub_zero] at h1
    exact (mul_pos_iff_of_pos_right hn).1 h1
  refine ⟨μ.re, hre, fun _ x y => ?_⟩
  have : (μ.re : ℂ) = μ := Complex.ext rfl (by simp [him])
  rw [this, hall]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadMinorExpHermitianEqConvexExpSum
section
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.LeadMinorExp

theorem sum_dite_card {n l : ℕ} {M : Type*} [AddCommMonoid M] (f : Set.powersetCard (Fin n) l → M) :
    ∑ J : Finset (Fin n), (if h : J.card = l then f ⟨J, h⟩ else 0) = ∑ S, f S := by
  symm
  refine Finset.sum_of_injOn (fun S : Set.powersetCard (Fin n) l => S.1)
    (fun _ _ _ _ h => Subtype.ext h) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro J _ hJ
    rw [dif_neg]
    intro h
    exact hJ ⟨⟨J, h⟩, by simp, rfl⟩
  · intro S _
    have h : S.1.card = l := S.2
    rw [dif_pos h]

theorem exp_smul_eq {n : ℕ} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y.IsHermitian) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Y) =
      (hY.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        diagonal (fun j => ((Real.exp (t * hY.eigenvalues j) : ℝ) : ℂ)) *
        (hY.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hY.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have h1 : U * Uᴴ = 1 := (hY.eigenvectorUnitary).2.2
  have h2 : Uᴴ * U = 1 := (hY.eigenvectorUnitary).2.1
  have hs : Y = U * diagonal (fun j => ((hY.eigenvalues j : ℝ) : ℂ)) * Uᴴ := by
    have := hY.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have h3 : (t : ℂ) • Y = U * diagonal (fun j => ((t * hY.eigenvalues j : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hs]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
    congr 3
    funext j
    simp
  rw [h3]
  refine (Matrix.exp_units_conj (⟨U, Uᴴ, h1, h2⟩ : (Matrix (Fin n) (Fin n) ℂ)ˣ) _).trans ?_
  rw [Matrix.exp_diagonal]
  change U * _ * Uᴴ = _
  congr 3
  funext j
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]

theorem leadMinor_exp_eq_sum (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian) (l : ℕ)
    (hl : l ≤ n) :
    ∃ w : Finset (Fin n) → ℝ, (∀ J, 0 ≤ w J) ∧ (∀ J, w J ≠ 0 → J.card = l) ∧ ∑ J, w J = 1 ∧
      ∀ t : ℝ, leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl =
        ((∑ J, w J * Real.exp (t * ∑ j ∈ J, hY.eigenvalues j) : ℝ) : ℂ) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hY.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have h1 : U * Uᴴ = 1 := (hY.eigenvectorUnitary).2.2
  set A : Matrix (Fin l) (Fin n) ℂ := U.submatrix (Fin.castLE hl) id with hA
  have hAA : A * Aᴴ = 1 := by
    rw [hA, conjTranspose_submatrix, ← submatrix_mul U Uᴴ _ id _ Function.bijective_id, h1]
    exact submatrix_one _ (Fin.castLE_injective hl)
  refine ⟨fun J => if h : J.card = l then
    ‖(A.submatrix id (GlobalTheory.subsetEnum (⟨J, h⟩ : Set.powersetCard (Fin n) l))).det‖ ^ 2 else 0,
    ?_, ?_, ?_, ?_⟩
  · intro J
    dsimp only
    split_ifs <;> positivity
  · intro J hJ
    by_contra h
    exact hJ (dif_neg h)
  · rw [sum_dite_card (fun S => ‖(A.submatrix id (GlobalTheory.subsetEnum S)).det‖ ^ 2)]
    exact GlobalTheory.sum_norm_sq_minors_eq_one A hAA
  · intro t
    have hsum : (∑ J : Finset (Fin n), (if h : J.card = l then
        ‖(A.submatrix id (GlobalTheory.subsetEnum (⟨J, h⟩ : Set.powersetCard (Fin n) l))).det‖ ^ 2 else 0) *
          Real.exp (t * ∑ j ∈ J, hY.eigenvalues j)) =
        ∑ S : Set.powersetCard (Fin n) l, ‖(A.submatrix id (GlobalTheory.subsetEnum S)).det‖ ^ 2 *
          Real.exp (t * ∑ j ∈ S.1, hY.eigenvalues j) := by
      rw [← sum_dite_card]
      refine Finset.sum_congr rfl fun J _ => ?_
      split_ifs <;> simp
    rw [hsum, exp_smul_eq hY t, leadMinor]
    rw [submatrix_mul _ _ _ id _ Function.bijective_id,
      submatrix_mul _ _ _ id _ Function.bijective_id, submatrix_id_id,
      ← conjTranspose_submatrix]
    refine (GlobalTheory.det_mul_diagonal_mul_eq_sum_minors A _ Aᴴ).trans ?_
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [← conjTranspose_submatrix, det_conjTranspose, Complex.star_def, Complex.mul_conj',
      Finset.mul_sum, Real.exp_sum]
    push_cast
    ring

end GlobalTheory.LeadMinorExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemUJsetOfKset
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory
namespace LowKProj

section General
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem fix_of_mem {E : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S) :
    ∀ x ∈ S, E x = x := by
  intro x hx
  obtain ⟨hidem, -, hrange⟩ := hE
  rw [← hrange] at hx
  obtain ⟨y, rfl⟩ := hx
  change E (E y) = E y
  rw [← ContinuousLinearMap.comp_apply, hidem]

theorem apply_mem {E : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S) (x : H) :
    E x ∈ S := by
  rw [← hE.2.2]
  exact ⟨x, rfl⟩

theorem norm_le_one {E : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S) :
    ‖E‖ ≤ 1 := by
  obtain ⟨hidem, hsym, -⟩ := hE
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  have hEE : E (E x) = E x := by rw [← ContinuousLinearMap.comp_apply, hidem]
  have hsq : ‖E x‖ ^ 2 ≤ ‖x‖ * ‖E x‖ := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hsym, hEE]
    exact re_inner_le_norm x (E x)
  have h0 : 0 ≤ ‖x‖ := norm_nonneg x
  have h1 : 0 ≤ ‖E x‖ := norm_nonneg (E x)
  nlinarith

theorem exists_proj (S : Submodule ℂ H) [FiniteDimensional ℂ S] :
    ∃ E : H →L[ℂ] H, IsOrthProjOnto E S := by
  have : CompleteSpace S := FiniteDimensional.complete ℂ S
  refine ⟨S.starProjection, ?_, ?_, ?_⟩
  · exact S.isIdempotentElem_starProjection
  · exact S.inner_starProjection_left_eq_right
  · exact S.range_starProjection

theorem comm_of_stable {E A B : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S)
    (hAB : ∀ x y, ⟪A x, y⟫_ℂ = ⟪x, B y⟫_ℂ) (hA : ∀ v ∈ S, A v ∈ S) (hB : ∀ v ∈ S, B v ∈ S) :
    E ∘L A = A ∘L E := by
  have hfix := fix_of_mem hE
  have hmem := apply_mem hE
  have hsym := hE.2.1
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  refine ext_inner_right ℂ fun y => ?_

  calc ⟪E (A x), y⟫_ℂ = ⟪A x, E y⟫_ℂ := hsym _ _
    _ = ⟪x, B (E y)⟫_ℂ := hAB _ _
    _ = ⟪x, E (B (E y))⟫_ℂ := by rw [hfix _ (hB _ (hmem y))]
    _ = ⟪E x, B (E y)⟫_ℂ := (hsym _ _).symm
    _ = ⟪A (E x), E y⟫_ℂ := (hAB _ _).symm
    _ = ⟪E (A (E x)), y⟫_ℂ := (hsym _ _).symm
    _ = ⟪A (E x), y⟫_ℂ := by rw [hfix _ (hA _ (hmem x))]

end General

theorem mem_UJset_of_Kset {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) : k ∈ UJset ε := by
  obtain ⟨hu, hc⟩ := hk
  have h2 : star k * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hu
  show kᴴ * Jm ε * k = Jm ε
  rw [← Matrix.star_eq_conjTranspose, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, h2, Matrix.one_mul]

private lemma star_mem_Kset {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) : star k ∈ Kset ε := by
  obtain ⟨hu, hc⟩ := hk
  have h1 : k * star k = 1 := (Matrix.mem_unitaryGroup_iff).1 hu
  have h2 : star k * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hu
  refine ⟨(Matrix.mem_unitaryGroup_iff).2 (by rw [star_star]; exact h2), ?_⟩
  calc star k * Jm ε = star k * Jm ε * (k * star k) := by rw [h1, Matrix.mul_one]
    _ = star k * (Jm ε * k) * star k := by simp only [Matrix.mul_assoc]
    _ = star k * (k * Jm ε) * star k := by rw [hc]
    _ = (star k * k) * Jm ε * star k := by simp only [Matrix.mul_assoc]
    _ = Jm ε * star k := by rw [h2, Matrix.one_mul]

theorem inner_adj {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (x y : H) :
    ⟪σ k x, y⟫_ℂ = ⟪x, σ (star k) y⟫_ℂ := by
  obtain ⟨⟨h1, hmul⟩, hiso, -⟩ := hσ
  have hkU := mem_UJset_of_Kset hk
  have hsU := mem_UJset_of_Kset (star_mem_Kset hk)
  have hks : k * star k = 1 := (Matrix.mem_unitaryGroup_iff).1 hk.1

  let L : H →ₗᵢ[ℂ] H := ⟨(σ k : H →ₗ[ℂ] H), fun v => hiso k hkU v⟩
  have hy : σ k (σ (star k) y) = y := by
    rw [← ContinuousLinearMap.comp_apply, ← hmul k hkU (star k) hsU, hks, h1]
    rfl
  calc ⟪σ k x, y⟫_ℂ = ⟪L x, L (σ (star k) y)⟫_ℂ := by
        change ⟪σ k x, y⟫_ℂ = ⟪σ k x, σ k (σ (star k) y)⟫_ℂ
        rw [hy]
    _ = ⟪x, σ (star k) y⟫_ℂ := L.inner_map_map _ _

theorem lowKSub_stable {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsKStableOn ε σ (lowKSub ε lam σ) := by
  intro g hg v hv

  have hle : lowKSub ε lam σ ≤ (lowKSub ε lam σ).comap (σ g : H →ₗ[ℂ] H) :=
    sSup_le fun S hS w hw => le_sSup hS (hS.2.1 g hg w hw)
  exact hle hv

theorem lowK_projection : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → (∃ w, IsHighestUnit ε lam σ w) ∧ IsKStableOn ε σ (lowKSub ε lam σ) ∧ (FiniteDimensional ℂ (lowKSub ε lam σ) → ∃ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub ε lam σ)) ∧ ∀ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub ε lam σ) → ‖E‖ ≤ 1 ∧ (∀ x ∈ lowKSub ε lam σ, E x = x) ∧ ∀ k ∈ Kset ε, E ∘L σ k = σ k ∘L E ∧ ‖σ k‖ ≤ 1 := by
  intro n ε lam H _ _ _ σ hDS
  obtain ⟨-, -, hrep, -, -, ⟨S, hS⟩, -⟩ := hDS
  refine ⟨?_, lowKSub_stable ε lam σ, fun _ => exists_proj _, ?_⟩
  ·
    obtain ⟨v, hvS, hv0, hwt⟩ := hS.2.2.2.1
    have hn : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hv0
    refine ⟨((‖v‖ : ℂ)⁻¹) • v, ?_, ?_, ?_⟩
    · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)
    · have hle : S ≤ lowKSub ε lam σ :=
        le_sSup (show S ∈ {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S} from hS)
      exact Submodule.smul_mem _ _ (hle hvS)
    · intro θ hθ
      rw [map_smul, hwt θ hθ, smul_comm]
  · intro E hE
    refine ⟨norm_le_one hE, fix_of_mem hE, fun k hk => ⟨?_, ?_⟩⟩
    · exact comm_of_stable hE (inner_adj hrep hk) (fun v hv => lowKSub_stable ε lam σ k hk v hv)
        (fun v hv => lowKSub_stable ε lam σ (star k) (star_mem_Kset hk) v hv)
    · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
        rw [hrep.2.1 k (mem_UJset_of_Kset hk) x, one_mul]

end LowKProj
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularHermitianMassMulLeMassStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unimodularHermitianMass_mul_le_mass : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∀ (k s : ℕ) (Mb : ℝ) (ms : ℕ → ℝ), 3 ≤ k → 1 ≤ s → s < k → (∀ (n : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (h : W →ₗ⋆[K] W →ₗ[K] K) (I : Submodule (𝓞 K) W), h.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h I n → Formalism.HermitianLatticesTheory.mass h I = ms n) → ms 1 ≤ Mb → ms 2 ≤ Mb → 1 ≤ Mb → ms s * ms (k - s) ≤ ms k * (Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (Formalism.HermitianLatticesTheory.fDeg K) * 16 ^ (s * k * (Formalism.HermitianLatticesTheory.fDeg K))) := by
  first | exact @GlobalTheory.MassRatioBound.mass_mul_mass_le | exact GlobalTheory.MassRatioBound.mass_mul_mass_le | (intros; apply GlobalTheory.MassRatioBound.mass_mul_mass_le <;> assumption)
end

