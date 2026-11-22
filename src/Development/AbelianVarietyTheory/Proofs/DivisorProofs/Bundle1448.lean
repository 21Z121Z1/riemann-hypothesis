import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1423
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0267
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1433
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1431
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1428
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactConeDiagonalConjUpperTriangular
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

noncomputable def upperConeRescale {E : Type} [Field E] (a : ℕ) (N : Matrix (Fin a) (Fin a) ℝ)
    (M : Matrix (Fin a) (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E) :=
  Matrix.of fun p q => (fun _ => ((N p q : ℝ) : ℂ)) * M p q

lemma continuous_upperConeRescale {E : Type} [Field E] (a : ℕ) :
    Continuous (fun x : Matrix (Fin a) (Fin a) ℝ × Matrix (Fin a) (Fin a) (Cinf E) => upperConeRescale a x.1 x.2) := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [upperConeRescale, Matrix.of_apply]
  refine Continuous.mul ?_ ?_
  · refine continuous_pi fun _ => ?_
    exact Complex.continuous_ofReal.comp ((continuous_apply q).comp ((continuous_apply p).comp continuous_fst))
  · exact (continuous_apply q).comp ((continuous_apply p).comp continuous_snd)

lemma upperCone_conj_diag_eq {E : Type} [Field E] (a : ℕ) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i)
    (d : GL (Fin a) (Cinf E)) (hd : d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)))
    (M : Matrix (Fin a) (Fin a) (Cinf E)) (hM : M.BlockTriangular id) :
    (d⁻¹).val * M * d.val = upperConeRescale a (fun p q => if p ≤ q then r q / r p else 0) M := by
  have hD : (d⁻¹).val = Matrix.diagonal (fun i => fun _ => ((r i)⁻¹ : ℂ)) := by
    have h1 : d.val * Matrix.diagonal (fun i => fun _ => ((r i)⁻¹ : ℂ)) = 1 := by
      rw [hd, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i x
      have : (r i : ℂ) ≠ 0 := by exact_mod_cast (hr i).ne'
      simp [this]
    calc (d⁻¹).val = (d⁻¹).val * (d.val * Matrix.diagonal (fun i => fun _ => ((r i)⁻¹ : ℂ))) := by
          rw [h1, mul_one]
      _ = _ := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  rw [hD, hd]
  ext p q x
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [upperConeRescale, Matrix.of_apply, Pi.mul_apply]
  by_cases hpq : p ≤ q
  · rw [if_pos hpq]
    have : (r p : ℂ) ≠ 0 := by exact_mod_cast (hr p).ne'
    push_cast
    field_simp
  · rw [if_neg hpq]
    have h0 : M p q = 0 := hM (lt_of_not_ge hpq)
    simp [h0]

end GlobalTheory

theorem GlobalTheory.upperCone_conj_compact : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ω : Set (GL (Fin a) (Cinf E))), IsCompact ω → (∀ b ∈ ω, b.val.BlockTriangular id) → ∀ t : ℝ, 0 < t → ∃ Ω : Set (GL (Fin a) (Cinf E)), IsCompact Ω ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ b ∈ ω, d⁻¹ * b * d ∈ Ω := by
  intro E _ _ _ a ω hω htri t ht
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.cone_coordinate_ratio_bounded a t ht
  set K : Set (Matrix (Fin a) (Fin a) ℝ) := Set.univ.pi (fun _ => Set.univ.pi (fun _ => Set.Icc (0:ℝ) C)) with hK
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  set A : Set (Matrix (Fin a) (Fin a) (Cinf E)) :=
    (fun x : Matrix (Fin a) (Fin a) ℝ × GL (Fin a) (Cinf E) => GlobalTheory.upperConeRescale a x.1 x.2.val) '' (K ×ˢ ω)
  set B : Set (Matrix (Fin a) (Fin a) (Cinf E)) :=
    (fun x : Matrix (Fin a) (Fin a) ℝ × GL (Fin a) (Cinf E) => GlobalTheory.upperConeRescale a x.1 (x.2⁻¹).val) '' (K ×ˢ ω)
  have hAc : IsCompact A := (hKc.prod hω).image
    ((GlobalTheory.continuous_upperConeRescale (E := E) a).comp (continuous_fst.prodMk (Units.continuous_val.comp continuous_snd)))
  have hBc : IsCompact B := (hKc.prod hω).image
    ((GlobalTheory.continuous_upperConeRescale (E := E) a).comp (continuous_fst.prodMk (Units.continuous_coe_inv.comp continuous_snd)))
  refine ⟨Units.embedProduct _ ⁻¹' (A ×ˢ (MulOpposite.op '' B)), ?_, ?_⟩
  · exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hAc.prod (hBc.image MulOpposite.continuous_op))
  intro r d hr hcone hd b hb
  have hN : (fun p q : Fin a => if p ≤ q then r q / r p else 0) ∈ K := by
    simp only [hK, Set.mem_pi]
    intro p _ q _
    rw [Set.mem_Icc]
    by_cases hpq : p ≤ q
    · simp only [if_pos hpq]
      exact ⟨div_nonneg (hr q).le (hr p).le, hC r hr hcone p q hpq⟩
    · simp only [if_neg hpq]
      exact ⟨le_rfl, hC0⟩
  have hbinv : (b⁻¹).val.BlockTriangular id := by
    have := Units.invertible b
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular (htri b hb)
  refine ⟨?_, ?_⟩
  · refine ⟨(_, b), ⟨hN, hb⟩, ?_⟩
    simp only [Units.val_mul]
    exact (GlobalTheory.upperCone_conj_diag_eq a r hr d hd b.val (htri b hb)).symm
  · refine ⟨(d⁻¹ * b * d)⁻¹.val, ⟨(_, b), ⟨hN, hb⟩, ?_⟩, rfl⟩
    have : (d⁻¹ * b * d)⁻¹ = d⁻¹ * b⁻¹ * d := by group
    simp only [this, Units.val_mul]
    exact (GlobalTheory.upperCone_conj_diag_eq a r hr d hd (b⁻¹).val hbinv).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactGeCompactPartTwistedCentralizer
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section
namespace GlobalTheory.CptTorus

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem twCent_commute (hE : Unr E) (n : ℕ) (w : Pl E) (y : GLw n w) {g : GLw n w}
    (hg : g ∈ twCent (thL n w) y) : Commute g (nrmL n w y) := by
  have hinv : ∀ x, thL n w (thL n w x) = x := (GlobalTheory.T.localTwist_continuous_involution_integral_properties E hE n w).2.1
  have hg' : g * y = y * thL n w g := hg
  unfold nrmL
  split_ifs with hs
  · have ht : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
    rw [ht] at hg'
    exact hg'
  · have ht : thL n w = thetaGL n (cj w) := by unfold thL; rw [if_neg hs]
    rw [ht] at hg' hinv
    show g * (y * thetaGL n (cj w) y) = (y * thetaGL n (cj w) y) * g
    calc g * (y * thetaGL n (cj w) y) = (g * y) * thetaGL n (cj w) y := by rw [mul_assoc]
      _ = y * (thetaGL n (cj w) g * thetaGL n (cj w) y) := by rw [hg', mul_assoc]
      _ = y * thetaGL n (cj w) (g * y) := by rw [map_mul]
      _ = y * thetaGL n (cj w) (y * thetaGL n (cj w) g) := by rw [hg']
      _ = (y * thetaGL n (cj w) y) * g := by rw [map_mul, hinv, mul_assoc]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w),
    (nrmL n w y).val.charpoly.Separable →
    ∃ H : Subgroup (GLw n w), IsCompact (H : Set (GLw n w)) ∧ cptPart (twCent (thL n w) y) ≤ H := by
  intro E _ _ _ hE n w y hs
  set M := nrmL n w y with hM
  set N : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hN
  have hval : ∀ g : GLw n w, Commute g M → (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * N = N * g := by
    intro g hg
    have := congrArg (fun x : GLw n w => (x : Matrix (Fin n) (Fin n) (w.adicCompletion E))) hg.eq
    simpa [Units.val_mul] using this
  have hadj : ∀ g : GLw n w, Commute g M →
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ∈ Algebra.adjoin (w.adicCompletion E) {N} :=
    fun g hg => GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute N _ hs (hval g hg)
  have hcomm : ∀ g h : GLw n w, Commute g M → Commute h M → Commute g h := by
    intro g h hg hh
    have h1 : Commute (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (h : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
      refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute (hadj h hh) ?_
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      rw [hb]
      exact hval g hg
    exact Units.ext (by simpa [Units.val_mul] using h1.eq)
  let S : Set (GLw n w) := {g | Commute g M ∧ IsCompact (closure (Subgroup.zpowers g : Set (GLw n w)))}
  let H0 : Subgroup (GLw n w) :=
    { carrier := S
      one_mem' := by
        refine ⟨Commute.one_left M, ?_⟩
        rw [Subgroup.zpowers_one_eq_bot, Subgroup.coe_bot, closure_singleton]
        exact isCompact_singleton
      mul_mem' := by
        intro g h hg hh
        refine ⟨hg.1.mul_left hh.1, ?_⟩
        have hK := hg.2.mul hh.2
        refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
        rintro x ⟨k, rfl⟩
        simp only
        rw [(hcomm g h hg.1 hh.1).mul_zpow]
        exact Set.mul_mem_mul (subset_closure ⟨k, rfl⟩) (subset_closure ⟨k, rfl⟩)
      inv_mem' := by
        intro g hg
        refine ⟨hg.1.inv_left, ?_⟩
        show IsCompact (closure (Subgroup.zpowers g⁻¹ : Set (GLw n w)))
        rw [Subgroup.zpowers_inv]
        exact hg.2 }
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_valuation_bound_of_isIntegral_mem_adjoin E w n N hs
  have hB := GlobalTheory.T.isCompact_GL_bounded_entries_completion_finitePlace E w n c
  have hSB : (H0 : Set (GLw n w)) ⊆ {g : GL (Fin n) (w.adicCompletion E) | ∀ i j,
      Valued.v ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c ∧
      Valued.v (((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c} := by
    intro g hg
    have hg' : g⁻¹ ∈ H0 := H0.inv_mem hg
    intro i j
    exact ⟨hc _ (hadj g hg.1) (GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers E w n g hg.2) i j,
      hc _ (hadj g⁻¹ hg'.1) (GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers E w n g⁻¹ hg'.2) i j⟩
  refine ⟨H0.topologicalClosure, ?_, ?_⟩
  · rw [Subgroup.topologicalClosure_coe]
    exact hB.of_isClosed_subset isClosed_closure (closure_minimal hSB hB.isClosed)
  · refine le_trans ?_ (Subgroup.le_topologicalClosure H0)
    rw [cptPart, Subgroup.closure_le]
    rintro t ⟨ht, htc⟩
    exact ⟨twCent_commute hE n w y ht, htc⟩

end GlobalTheory.CptTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockMapOfCanonicalCommutationRelations
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.CCRFock
open MvPolynomial

theorem polEval_X {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (m : ι → Module.End ℂ V)
    (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V) (i : ι) (p : MvPolynomial ι ℂ) :
    polEval m hm f₀ (X i * p) = m i (polEval m hm f₀ p) := by
  simp [polEval, Module.End.mul_apply]

theorem polEval_one {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (m : ι → Module.End ℂ V)
    (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V) : polEval m hm f₀ 1 = f₀ := by
  simp [polEval]

theorem atPl_add {W Λ : Type} [Fintype W] [DecidableEq W] (w : W) (A B : Module.End ℂ (MvPolynomial Λ ℂ)) :
    GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w (A + B) =
      GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w A + GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w B := by
  simp only [GlobalTheory.RealLift.atPl]
  exact PiTensorProduct.map_update_add (s := fun _ : W => MvPolynomial Λ ℂ) (t := fun _ : W => MvPolynomial Λ ℂ) (fun _ => LinearMap.id) w A B

theorem atPl_smul {W Λ : Type} [Fintype W] [DecidableEq W] (w : W) (c : ℂ) (A : Module.End ℂ (MvPolynomial Λ ℂ)) :
    GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w (c • A) = c • GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w A := by
  simp only [GlobalTheory.RealLift.atPl]
  exact PiTensorProduct.map_update_smul (s := fun _ : W => MvPolynomial Λ ℂ) (t := fun _ : W => MvPolynomial Λ ℂ) (fun _ => LinearMap.id) w c A

theorem atPl_linear {W Λ : Type} [Fintype W] [DecidableEq W] (w : W) :
    ∃ L : Module.End ℂ (MvPolynomial Λ ℂ) →ₗ[ℂ] Module.End ℂ (⨂[ℂ] _ : W, MvPolynomial Λ ℂ),
      ∀ A, L A = GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w A := ⟨(PiTensorProduct.mapMultilinear ℂ (fun _ : W => MvPolynomial Λ ℂ) (fun _ : W => MvPolynomial Λ ℂ)).toLinearMap
      (fun _ => LinearMap.id) w, fun A => by
    simp [GlobalTheory.RealLift.atPl]⟩

theorem fock_map_of_ccr : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ f₀ : V, f₀ ≠ 0 →
    (∀ w a b, H (Pi.single w (Matrix.single a b 1)) f₀ +
      (lineSign a b * Complex.I) • H (Pi.single w (Matrix.single a b Complex.I)) f₀ = 0) →
    ∃ Φ : (⨂[ℂ] _ : W, Pol P Q R S) →ₗ[ℂ] V, Function.Injective Φ ∧
      ∀ c T, Φ (sumPl (fun w => heisOp (c w)) T) = H c (Φ T) := by
  intro V _ _ W _ _ P Q R S H hadd hsmul hccr f₀ hf₀ hvac

  have hm : ∀ i j, fockM H i * fockM H j = fockM H j * fockM H i := GlobalTheory.T.heisenberg_creation_operators_commute_of_ccr H hadd hsmul hccr
  have hcr := GlobalTheory.T.heisenberg_annihilation_creation_commutator_eq_delta H hadd hsmul hccr

  have hd0 : ∀ j, fockD H j f₀ = 0 := by
    rintro ⟨w, a, b⟩
    have h := hvac w a b
    simp only [fockD, unitAt, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.add_apply]
    rw [h, smul_zero, neg_zero]
  have hpd := GlobalTheory.T.commutingOperatorsPolynomialEval_pderiv (fockM H) (fockD H) hm f₀ hcr hd0
  have hinj0 : Function.Injective (polEval (fockM H) hm f₀) :=
    GlobalTheory.T.injective_of_map_pderiv_eq_and_map_one_ne_zero _ (fockD H) hpd (by rw [polEval_one]; exact hf₀)
  refine ⟨polEval (fockM H) hm f₀ ∘ₗ polMap W (Ix P Q × Ix R S), hinj0.comp (GlobalTheory.T.tensorPolynomialsToProductVariables_injective W _), ?_⟩

  have hX : ∀ (w : W) (l : Ix P Q × Ix R S) T, polEval (fockM H) hm f₀ (polMap W (Ix P Q × Ix R S)
      (GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w
        (LinearMap.mulLeft ℂ (MvPolynomial.X l)) T)) =
      fockM H (w, l) (polEval (fockM H) hm f₀ (polMap W (Ix P Q × Ix R S) T)) := by
    intro w l T
    have h := LinearMap.congr_fun (GlobalTheory.T.tensorPolynomialsToProductVariables_comp_mulLeft_X W (Ix P Q × Ix R S) w l) T
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply] at h
    rw [h, polEval_X]
  have hD : ∀ (w : W) (l : Ix P Q × Ix R S) T, polEval (fockM H) hm f₀ (polMap W (Ix P Q × Ix R S)
      (GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w
        (MvPolynomial.pderiv l).toLinearMap T)) =
      fockD H (w, l) (polEval (fockM H) hm f₀ (polMap W (Ix P Q × Ix R S) T)) := by
    intro w l T
    have h := LinearMap.congr_fun (GlobalTheory.T.tensorPolynomialsToProductVariables_comp_pderiv W (Ix P Q × Ix R S) w l) T
    simp only [LinearMap.comp_apply, Derivation.coeFn_coe] at h
    rw [h, hpd]

  choose L hL using fun w : W => atPl_linear (Λ := Ix P Q × Ix R S) w
  intro c T
  have hsum : ∀ w, GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w (heisOp (c w)) =
      ∑ l : Ix P Q × Ix R S, ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * coefM (c w l.1 l.2) (lineSign l.1 l.2)) •
          GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w
            (LinearMap.mulLeft ℂ (MvPolynomial.X l)) +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * coefD (c w l.1 l.2) (lineSign l.1 l.2)) •
          GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w
            (MvPolynomial.pderiv l).toLinearMap) := by
    intro w
    clear hX hD hpd hinj0 hcr hm hd0 hvac hccr hsmul hadd hf₀
    rw [← hL w (heisOp (c w)), GlobalTheory.T.fockHeisenbergOperatorOfCoords_eq_sum_mulLeft_pderiv (c w), map_sum]
    simp only [map_add, map_smul]
    simp only [hL]
  rw [GlobalTheory.T.heisenberg_family_expand_creation_annihilation H hadd hsmul c]
  simp only [GlobalTheory.RealLift.sumPl, hsum, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.add_apply, LinearMap.smul_apply, map_sum, map_add, map_smul, hX, hD]
  conv_rhs => rw [Fintype.sum_prod_type]

end GlobalTheory.CCRFock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.QDom

open scoped Pointwise

theorem isFundamentalDomain_inf {G : Type} [Group G] [MeasurableSpace G] {μ : Measure G}
    (hm : ∀ g : G, Measurable (g * ·)) (hinv : ∀ g : G, μ.map (g * ·) = μ)
    {Γ : Subgroup G} [Countable Γ] {D : Set G} (hD : IsFundamentalDomain Γ D μ) (S : Subgroup G) :
    ∃ 𝓓 : Set G, IsFundamentalDomain ↥(Γ ⊓ S) 𝓓 μ := by
  classical
  let Q' : Subgroup Γ := (Γ ⊓ S).subgroupOf Γ
  haveI : Countable (Γ ⧸ Q') := Function.Surjective.countable QuotientGroup.mk_surjective
  let rep : Γ ⧸ Q' → Γ := fun c => (Quotient.out c)⁻¹
  have hmp : ∀ g : G, MeasurePreserving (g * ·) μ μ := fun g => ⟨hm g, hinv g⟩
  have himg : ∀ (g : G) (s : Set G), g • s = (g⁻¹ * ·) ⁻¹' s := by
    intro g s; ext x; simp [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
  have hnm : ∀ g : G, NullMeasurableSet (g • D) μ := fun g => by
    rw [himg]; exact hD.nullMeasurableSet.preimage (hmp g⁻¹).quasiMeasurePreserving
  refine ⟨⋃ c, ((rep c : Γ) : G) • D, ?_⟩
  refine IsFundamentalDomain.mk'' ?_ ?_ ?_ ?_
  · exact NullMeasurableSet.iUnion fun c => hnm _
  · filter_upwards [hD.ae_covers] with x hx
    obtain ⟨γ, hγ⟩ := hx
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Q' γ
    have hQ : ((h : Γ) : G) ∈ Γ ⊓ S := (Subgroup.mem_subgroupOf).1 h.2
    refine ⟨⟨((h : Γ) : G)⁻¹, inv_mem hQ⟩, Set.mem_iUnion.2 ⟨(γ : Γ ⧸ Q'), ?_⟩⟩
    rw [himg, Set.mem_preimage]
    have e1 : ((rep (γ : Γ ⧸ Q') : Γ) : G)⁻¹ = (γ : G) * ((h : Γ) : G) := by
      simp only [rep, inv_inv]
      have := congrArg (fun y : Γ => (y : G)) hh
      simpa using this
    rw [e1]
    have : (γ : G) * ((h : Γ) : G) * ((⟨((h : Γ) : G)⁻¹, inv_mem hQ⟩ : ↥(Γ ⊓ S)) • x) = γ • x := by
      rw [Subgroup.smul_def, Subgroup.smul_def]
      simp [smul_eq_mul, mul_assoc]
    rw [this]; exact hγ
  · intro g hg
    have hsm : g • ⋃ c, ((rep c : Γ) : G) • D = ⋃ c, ((g : G) * ((rep c : Γ) : G)) • D := by
      rw [Set.smul_set_iUnion]
      refine Set.iUnion_congr fun c => ?_
      rw [← smul_smul]; rfl
    rw [hsm, AEDisjoint.iUnion_left_iff]
    intro c
    rw [AEDisjoint.iUnion_right_iff]
    intro c'
    have hgΓ : (g : G) ∈ Γ := (Subgroup.mem_inf.1 g.2).1
    let γ₁ : Γ := ⟨g, hgΓ⟩ * rep c
    have hne : γ₁ ≠ rep c' := by
      intro heq
      have hmem : (Quotient.out c)⁻¹ * Quotient.out c' ∈ Q' := by
        rw [Subgroup.mem_subgroupOf]
        have : (Quotient.out c')⁻¹ = ⟨g, hgΓ⟩ * (Quotient.out c)⁻¹ := by
          simpa [γ₁, rep] using heq.symm
        have h2 : (Quotient.out c)⁻¹ * Quotient.out c' = (⟨g, hgΓ⟩ : Γ)⁻¹ := by
          rw [← inv_inj, mul_inv_rev, inv_inv, this, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
        rw [h2]
        simpa using inv_mem g.2
      have hcc : c = c' := by
        rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
        exact (QuotientGroup.eq).2 hmem
      subst hcc
      apply hg
      have : (⟨g, hgΓ⟩ : Γ) = 1 := by simpa [γ₁] using heq
      ext; simpa using congrArg Subtype.val this
    exact hD.aedisjoint hne
  · intro g
    exact (hmp (g : G)).quasiMeasurePreserving

end GlobalTheory.QDom

namespace GlobalTheory.QDom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem countable_numberField : Countable E :=
  Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm

theorem countable_ratU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  classical
  haveI := countable_numberField (E := E)
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  have hmat : Countable (GL (Fin n) E) := Function.Injective.countable (f := fun A : GL (Fin n) E => (A : Matrix (Fin n) (Fin n) E)) Units.val_injective
  have hpre : ∀ x : ratU σ J, ∃ A : GL (Fin n) E, Matrix.GeneralLinearGroup.map (inclR (AF F)) A = ((x : UA σ J) : GL (Fin n) (AE F E)) := by
    intro x
    have := x.2
    unfold ratU at this
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range] at this
    exact this
  choose f hf using hpre
  refine Function.Injective.countable (f := f) ?_
  intro x y hxy
  apply Subtype.ext; apply Subtype.ext
  rw [← hf x, ← hf y, hxy]

set_option synthInstance.maxHeartbeats 400000 in
theorem measurable_mul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) :
    Measurable (g * ·) := by
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  apply Continuous.measurable
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · simp only [Function.comp_def, Subgroup.coe_mul, Units.val_mul]
    exact continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)
  · simp only [Subgroup.coe_mul, mul_inv_rev, Units.val_mul]
    exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_mul continuous_const

end GlobalTheory.QDom

namespace GlobalTheory.QDom

theorem exists_fundamentalDomain_ratStab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∃ 𝓓 : Set (UA σ G.V.J), IsFundamentalDomain ↥(ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}) 𝓓 G.M.μ := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' _ X om om' hT
  haveI := countable_ratU σ G.V.J
  have hgood := hT.geo.hM
  haveI := hgood.haar
  exact isFundamentalDomain_inf (measurable_mul_left σ G.V.J) (fun g => map_mul_left_eq_self G.M.μ g) hgood.dom _

end GlobalTheory.QDom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainRationalBlockUnipotentGLStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundamentalDomain_rationalBlockUnipotentGL : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (s : ℕ) [MeasurableSpace (BlockIx a s → Ad E)] [BorelSpace (BlockIx a s → Ad E)] (μ : Measure (BlockIx a s → Ad E)) [μ.IsAddHaarMeasure], ∃ 𝓕 : Set (BlockIx a s → Ad E), IsAddFundamentalDomain (ratN E a s) 𝓕 μ ∧ μ 𝓕 ≠ 0 ∧ μ 𝓕 < ⊤ := by
  first | exact @GlobalTheory.CuspRep.exists_isAddFundamentalDomain_ratN | exact GlobalTheory.CuspRep.exists_isAddFundamentalDomain_ratN | (intros; apply GlobalTheory.CuspRep.exists_isAddFundamentalDomain_ratN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAbsGtOne
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DivAbsBig

theorem exists_idele_absE_gt_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ t : (AE F E)ˣ, 1 < (absE F E t : ℝ) := by
  intro F E _ _ _ _ _
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨b, h2⟩ : ∃ b : w.Completion, ‖b‖ = 2 := by
    refine ⟨_, (InfinitePlace.Completion.norm_coe w ((WithAbs.equiv w.1).symm (2 : F))).trans ?_⟩
    show w (2 : F) = 2
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.apply, map_ofNat]
    norm_num
  have hne : b ≠ 0 := by
    intro h; rw [h, norm_zero] at h2; norm_num at h2
  let a : (w.Completion)ˣ := Units.mk0 b hne
  let y : (w.Completion ⊗[F] E)ˣ := Units.map (algebraMap w.Completion (w.Completion ⊗[F] E)).toMonoidHom a
  refine ⟨GlobalTheory.Doubling.ideleAtInf F E w y, ?_⟩
  rw [GlobalTheory.Doubling.absE_ideleAtInf, GlobalTheory.Doubling.absEw_apply]
  change 1 < ((‖Algebra.norm w.Completion (algebraMap w.Completion (w.Completion ⊗[F] E) b)‖₊ ^ w.mult : ℝ≥0) : ℝ)
  rw [Algebra.norm_algebraMap, Module.finrank_baseChange, NNReal.coe_pow, coe_nnnorm, norm_pow, h2, ← pow_mul]
  have hn : 0 < Module.finrank F E := Module.finrank_pos
  have hm : 0 < w.mult := by unfold InfinitePlace.mult; split_ifs <;> norm_num
  exact one_lt_pow₀ (by norm_num) (Nat.mul_ne_zero hn.ne' hm.ne')

end GlobalTheory.DivAbsBig

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantHermitianFormCuspidalRepStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_hermitianForm_cuspidalRep : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∃ H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) ∧ (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) ∧ (∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) ∧ (∀ k φ ψ, H (π.op (.cpt k) φ) (π.op (.cpt k) ψ) = H φ ψ) ∧ ∀ X φ ψ, H (π.op (.lie X) φ) ψ + H φ (π.op (.lie X) ψ) = 0 := by
  first | exact @GlobalTheory.GelfandKazhdanHerm.exists_invariant_hermitian | exact GlobalTheory.GelfandKazhdanHerm.exists_invariant_hermitian | (intros; apply GlobalTheory.GelfandKazhdanHerm.exists_invariant_hermitian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroWeightTensorIntertwiningAutRepStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_weightTensor_intertwining_autRep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → (∀ v : InfinitePlace E, HasWeightAt π v.embedding (lam v)) → ∃ T : Wsp lam →ₗ[ℂ] (UA E n → ℂ), T ≠ 0 ∧ (∀ w, T w ∈ π) ∧ ∀ x ∈ infU E n, ∀ w, T (wInf lam x w) = RU E n x (T w) := by
  first | exact @GlobalTheory.BCT.TrKer.exists_ne_zero_wsp_intertwining | exact GlobalTheory.BCT.TrKer.exists_ne_zero_wsp_intertwining | (intros; apply GlobalTheory.BCT.TrKer.exists_ne_zero_wsp_intertwining <;> assumption)
end

