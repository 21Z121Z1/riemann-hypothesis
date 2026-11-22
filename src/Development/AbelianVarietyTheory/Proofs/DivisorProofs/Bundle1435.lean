import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1411
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPointCountOneClassCommensurable
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1415
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0100
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0094
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramSkewHermitianSignatureStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_det_gram_skewHermitian_signature : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d : ℕ) (W : Spc F E d) (r s : ℕ), W.IsSkew σ B r s → IsUnit W.J.det := by
  first | exact @GlobalTheory.SkewUnit.isUnit_det_of_isSkew | exact GlobalTheory.SkewUnit.isUnit_det_of_isSkew | (intros; apply GlobalTheory.SkewUnit.isUnit_det_of_isSkew <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPointCountOneClassCommensurableStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitz_pointCount_one_class_commensurable : ∀ {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂) (f₁ : G₁ → ℂ) (φ : G₂ → ℂ), (∀ g : G₁, Subgroup.Commensurable (K₁.map (MulAut.conj g).toMonoidHom) K₁) → (∀ g : G₂, Subgroup.Commensurable (K₂.map (MulAut.conj g).toMonoidHom) K₂) → K₂.map θ ≤ K₂ → (∀ k ∈ K₁, ∀ x, f₁ (k⁻¹ * x * k) = f₁ x) → (∀ k ∈ K₂, ∀ x, φ (k⁻¹ * x * θ k) = φ x) → (∀ g : Γ, ι₁ g * γ = γ * ι₁ g) → (∀ g : Γ, ι₂ g * δ = δ * θ (ι₂ g)) → Function.Injective (ι₁.prod ι₂) → (∀ x : G₁ × G₂, Finite (stab ι₁ ι₂ K₁ K₂ x)) → {q : DoubleCoset.Quotient ((ι₁.prod ι₂).range : Set (G₁ × G₂)) ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)) | f₁ ((Quotient.out q).1⁻¹ * γ * (Quotient.out q).1) * φ ((Quotient.out q).2⁻¹ * δ * θ (Quotient.out q).2) ≠ 0}.Finite → pointSum ι₁ ι₂ θ K₁ K₂ γ δ f₁ φ = pointSide ι₁ ι₂ θ K₁ K₂ γ δ f₁ φ := by
  first | (exact @GlobalTheory.LKCountComm.pointSum_eq_pointSide_of_commensurable) | (exact GlobalTheory.LKCountComm.pointSum_eq_pointSide_of_commensurable) | (intros; apply GlobalTheory.LKCountComm.pointSum_eq_pointSide_of_commensurable  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LandherrStandardDefiniteHermitianCmFieldStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.landherr_standard_definite_hermitian_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) E), IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H.map τ = cT (starRingEnd ℂ) Q * Q) → (∀ w : Pl E, ¬ IsSplitAt w → ∃ g : Matrix (Fin n) (Fin n) (w.adicCompletion E), H.map (algebraMap E (w.adicCompletion E)) = cT (cj w) g * g) → ∃ h : GL (Fin n) E, H = cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val * h.val := by
  first | exact @GlobalTheory.LandherrStd.main | exact GlobalTheory.LandherrStd.main | (intros; apply GlobalTheory.LandherrStd.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaplacianPolynomialKernelOfPolynomialLaplacian
section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
noncomputable section

namespace GlobalTheory.HCA

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E a) in

def glRho : glL E a →ₗ[ℝ] Module.End ℂ ((glH E a).smoothFuns (F := ℂ)) where
  toFun X := (glH E a).rightDerivEnd X
  map_add' X Y := by ext1 f; ext1; exact (glH E a).rightDeriv_add_left _ _ _
  map_smul' r X := by ext1 f; ext1; exact (glH E a).rightDeriv_smul_left r _ _

variable (E a) in

def glLap : Module.End ℂ ((glH E a).smoothFuns (F := ℂ)) :=
  ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a,
    ((glH E a).rightDerivEnd ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 +
      (glH E a).rightDerivEnd ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2)

theorem aeval_intertwine {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (Φ : M →ₗ[ℂ] N) (A : Module.End ℂ M) (B : Module.End ℂ N) (h : ∀ x, Φ (A x) = B (Φ x))
    (p : Polynomial ℂ) (x : M) : Φ (Polynomial.aeval A p x) = Polynomial.aeval B p (Φ x) := by
  have hp : ∀ n : ℕ, ∀ x, Φ ((A ^ n) x) = (B ^ n) (Φ x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h, ih]
  induction p using Polynomial.induction_on' with
  | add p q hp' hq' => simp only [map_add, LinearMap.add_apply, hp', hq']
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul, hp]

theorem contDiffOn_finsum {ι : Type*} (s : Finset ι) (g : ι → Lie E a → ℂ)
    (hg : ∀ i ∈ s, ContDiffOn ℝ ∞ (g i) (invSet E a)) : ContDiffOn ℝ ∞ (∑ i ∈ s, g i) (invSet E a) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact contDiffOn_const (c := (0 : ℂ))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hg i (Finset.mem_insert_self _ _)).add (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))

theorem rightDeriv_glF {f : Lie E a → ℂ} (hf : ContDiffOn ℝ ∞ f (invSet E a)) (X : glL E a)
    (g : (glH E a).smoothFuns (F := ℂ)) (hg : g.1 = fun y : glG E a => f (toL y.1.val)) :
    ((glH E a).rightDerivEnd X g).1 = fun y : glG E a => vecF E a (toL X.1) f (toL y.1.val) := by
  rw [IsExpLieAlgebra.coe_rightDerivEnd, hg]
  exact ((GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField E a f hf).2 X).2

theorem glLap_glF {f : Lie E a → ℂ} (hf : ContDiffOn ℝ ∞ f (invSet E a))
    (g : (glH E a).smoothFuns (F := ℂ)) (hg : g.1 = fun y : glG E a => f (toL y.1.val)) :
    (glLap E a g).1 = (fun y : glG E a => lapF E a f (toL y.1.val)) ∧ ContDiffOn ℝ ∞ (lapF E a f) (invSet E a) := by
  have key : ∀ X : glL E a, ((glH E a).rightDerivEnd X ((glH E a).rightDerivEnd X g)).1 =
      fun y : glG E a => vecF E a (toL X.1) (vecF E a (toL X.1) f) (toL y.1.val) := fun X =>
    rightDeriv_glF ((GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField E a f hf).2 X).1 X _ (rightDeriv_glF hf X g hg)
  have hv : ∀ X : Lie E a, ContDiffOn ℝ ∞ (vecF E a X f) (invSet E a) := fun X =>
    ((GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField E a f hf).2 ⟨Matrix.of X, Submodule.mem_top⟩).1
  have hvv : ∀ X : Lie E a, ContDiffOn ℝ ∞ (vecF E a X (vecF E a X f)) (invSet E a) := fun X =>
    ((GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField E a _ (hv X)).2 ⟨Matrix.of X, Submodule.mem_top⟩).1
  refine ⟨?_, ?_⟩
  · simp only [glLap, LinearMap.sum_apply, LinearMap.add_apply, sq, Module.End.mul_apply,
      Submodule.coe_sum, Submodule.coe_add, key]
    funext y
    simp only [lapF, Finset.sum_apply, Pi.add_apply]
  · unfold lapF
    exact contDiffOn_finsum _ _ fun τ _ => contDiffOn_finsum _ _ fun i _ => contDiffOn_finsum _ _ fun j _ =>
      (hvv _).add (hvv _)

theorem glLap_pow_glF (k : ℕ) : ∀ {f : Lie E a → ℂ}, ContDiffOn ℝ ∞ f (invSet E a) →
    ∀ (g : (glH E a).smoothFuns (F := ℂ)), g.1 = (fun y : glG E a => f (toL y.1.val)) →
    ((glLap E a ^ k) g).1 = (fun y : glG E a => (lapF E a)^[k] f (toL y.1.val)) ∧
      ContDiffOn ℝ ∞ ((lapF E a)^[k] f) (invSet E a) := by
  induction k with
  | zero => intro f hf g hg; exact ⟨hg, hf⟩
  | succ k ih =>
    intro f hf g hg
    obtain ⟨h1, h2⟩ := glLap_glF hf g hg
    rw [pow_succ, Module.End.mul_apply, Function.iterate_succ_apply]
    exact ih h2 _ h1

theorem glLap_glRes (φ : Sm E a) (x : GA E a) :
    glLap E a ⟨glRes φ.1 x, (GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq E a φ x).1⟩ = ⟨glRes (lapOp E a φ).1 x, (GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq E a _ x).1⟩ := by
  have key : ∀ (i j : Fin a) (z : Cinf E) (ψ : Sm E a),
      (glH E a).rightDerivEnd ⟨Matrix.single i j z, Submodule.mem_top⟩ ⟨glRes ψ.1 x, (GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq E a ψ x).1⟩ =
        ⟨glRes (lieS E a i j z ψ).1 x, (GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq E a _ x).1⟩ := by
    intro i j z ψ
    apply Subtype.ext
    rw [IsExpLieAlgebra.coe_rightDerivEnd, (GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq E a ψ x).2, lieS_apply]
  apply Subtype.ext
  simp only [glLap, lapOp, LinearMap.sum_apply, LinearMap.add_apply, sq, Module.End.mul_apply,
    key, Submodule.coe_sum, Submodule.coe_add]
  funext y
  simp only [glRes, Finset.sum_apply, Pi.add_apply, Submodule.coe_sum, Submodule.coe_add]

theorem solG_of_polyLap : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∀ p : Polynomial ℂ, p ≠ 0 → ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (glL E a)) (P : Polynomial ℂ), P.Monic ∧ (∀ f : Lie E a → ℂ, ContDiffOn ℝ ∞ f (invSet E a) → (∀ y ∈ invSet E a, polyF E a p f y = 0) → (fun y : glG E a => f (toL y.1.val)) ∈ solG (glH E a) b P) ∧ ∀ φ : Sm E a, Polynomial.aeval (lapOp E a) p φ = 0 → ∀ x, glRes φ.1 x ∈ solG (glH E a) b P := by
  intro E _ _ _ a p hp
  obtain ⟨d, b, hb⟩ := GlobalTheory.T.exists_realBasis_glLieAlgebra_sum_sq_elementary E a
  have hΔ : (∑ i, (glH E a).rightDerivEnd (F := ℂ) (b i) * (glH E a).rightDerivEnd (F := ℂ) (b i)) = glLap E a := by
    rw [glLap]
    simp only [sq]
    exact hb _ (glRho E a)
  refine ⟨d, b, p * Polynomial.C p.leadingCoeff⁻¹, Polynomial.monic_mul_leadingCoeff_inv hp, ?_, ?_⟩
  · have hP : ∀ g, Polynomial.aeval (glLap E a) (p * Polynomial.C p.leadingCoeff⁻¹) g =
        p.leadingCoeff⁻¹ • Polynomial.aeval (glLap E a) p g := by
      intro g
      rw [Polynomial.aeval_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
    intro f hf h0
    rw [mem_solG]
    refine ⟨(GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField E a f hf).1, ?_⟩
    rw [hΔ, hP]
    have hk : ∀ k : ℕ, ((glLap E a ^ k) ⟨_, (GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField E a f hf).1⟩).1 =
        (fun y : glG E a => (lapF E a)^[k] f (toL y.1.val)) := fun k => (glLap_pow_glF k hf _ rfl).1
    suffices h : Polynomial.aeval (glLap E a) p ⟨_, (GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField E a f hf).1⟩ = 0 by rw [h, smul_zero]
    apply Subtype.ext
    rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum]
    funext y
    simp only [Finset.sum_apply, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, hk, Submodule.coe_zero,
      Pi.zero_apply]
    have := h0 _ (val_mem_invSet y.1)
    simpa only [polyF, Finset.sum_apply, Pi.smul_apply] using this
  · intro φ hφ x
    rw [mem_solG]
    refine ⟨(GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq E a φ x).1, ?_⟩
    rw [hΔ, Polynomial.aeval_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
    let Φ : Sm E a →ₗ[ℂ] (glH E a).smoothFuns (F := ℂ) :=
      { toFun := fun ψ => ⟨glRes ψ.1 x, (GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq E a ψ x).1⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have e := aeval_intertwine Φ (lapOp E a) (glLap E a) (fun ψ => (glLap_glRes ψ x).symm) p φ
    change p.leadingCoeff⁻¹ • Polynomial.aeval (glLap E a) p (Φ φ) = 0
    rw [← e, hφ, map_zero, smul_zero]

end GlobalTheory.HCA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEqIntegralCoords
section
namespace GlobalTheory.LatticeIntegralCoordinates

theorem exists_basis_of_lattice (O E V : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [Field E] [Algebra O E] [IsFractionRing O E] [AddCommGroup V] [Module E V] [Module O V]
    [IsScalarTower O E V] (L : Submodule O V) (hfg : L.FG)
    (hspan : Submodule.span E (L : Set V) = ⊤) :
    ∃ b : Module.Basis (Fin (Module.finrank E V)) E V,
      ∀ y : V, y ∈ L ↔ ∀ i, b.repr y i ∈ (algebraMap O E).range := by
  classical
  haveI : Module.IsTorsionFree O V := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro c v h
    rw [← algebraMap_smul E c v] at h
    rcases smul_eq_zero.mp h with h | h
    · left; exact (IsFractionRing.injective O E) (by simpa using h)
    · right; exact h
  haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free O L := inferInstance
  let bL := Module.Free.chooseBasis O L
  let v : Module.Free.ChooseBasisIndex O L → V := fun i => (bL i : V)
  have hli : LinearIndependent O v :=
    bL.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hliE : LinearIndependent E v := hli.localization E (nonZeroDivisors O)
  have hL : Submodule.span O (Set.range v) = L := by
    have : Set.range v = L.subtype '' Set.range bL := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, bL.span_eq, Submodule.map_top, Submodule.range_subtype]
  have htop : ⊤ ≤ Submodule.span E (Set.range v) := by
    rw [← hspan, Submodule.span_le]
    intro x hx
    exact Submodule.span_subset_span O E _ (hL.ge hx)
  let b0 := Module.Basis.mk hliE htop
  have hb0 : ∀ j, b0 j = v j := fun j => Module.Basis.mk_apply hliE htop j
  have hcard := Module.finrank_eq_card_basis b0
  let e := Fintype.equivFinOfCardEq hcard.symm
  refine ⟨b0.reindex e, fun y => ⟨fun hy i => ?_, fun hy => ?_⟩⟩
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 (hL.ge hy)
    have h1 : ∑ j, c j • v j = ∑ j, algebraMap O E (c j) • b0 j :=
      Finset.sum_congr rfl fun j _ => by rw [hb0, algebraMap_smul]
    rw [Module.Basis.repr_reindex_apply, h1, b0.repr_sum_self]
    exact ⟨_, rfl⟩
  · rw [← b0.sum_repr y]
    refine L.sum_mem fun j _ => ?_
    obtain ⟨c, hc⟩ := hy (e j)
    rw [Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply] at hc
    rw [← hc, algebraMap_smul, hb0]
    exact L.smul_mem c (bL j).2

theorem lattice_eq_integral_coords :
    ∀ (K : GlobalTheory.UnitLemma.UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V]
      [IsScalarTower K.O K.E V] [FiniteDimensional K.E V] (L : Submodule K.O V),
      L.FG → Submodule.span K.E (L : Set V) = ⊤ →
      ∃ b : Module.Basis (Fin (Module.finrank K.E V)) K.E V,
        ∀ y : V, y ∈ L ↔ ∀ i, b.repr y i ∈ (algebraMap K.O K.E).range :=
  fun K V _ _ _ _ _ L hfg hspan => exists_basis_of_lattice K.O K.E V L hfg hspan

end GlobalTheory.LatticeIntegralCoordinates
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStableAlmostAllPlacesRightStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_stable_almost_all_places_right : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (X : Spc F E n)
    (Y : Spc F E d), Y.L.IsLattice E → ∀ N : Matrix (Fin d) (Fin d) (AE F E),
    Set.Finite {w : Pl F | ¬ ∀ γ ∈ latAtV X Y w, γ * Matrix.transpose N ∈ latAtV X Y w} := by
  first | exact @GlobalTheory.AdelMatLatRight.almost_all_stable_right | exact GlobalTheory.AdelMatLatRight.almost_all_stable_right | (intros; apply GlobalTheory.AdelMatLatRight.almost_all_stable_right <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeLeOfBoundOnFiniteDirections
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CuspRapid

theorem exists_finset_clm_bound (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ (B : Finset V) (C : ℝ), 0 ≤ C ∧ ∀ (L : V →L[ℝ] ℂ) (X : V) (M : ℝ),
      (∀ Y ∈ B, ‖L Y‖ ≤ M) → 0 ≤ M → ‖L X‖ ≤ C * ‖X‖ * M := by
  classical
  obtain ⟨C, hC, h⟩ := (Module.finBasis ℝ V).exists_opNorm_le (F := ℂ)
  refine ⟨Finset.univ.image (Module.finBasis ℝ V), C, hC.le, fun L X M hB hM => ?_⟩
  have h1 : ‖L‖ ≤ C * M := h hM fun i => hB _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  calc ‖L X‖ ≤ ‖L‖ * ‖X‖ := L.le_opNorm X
    _ ≤ C * M * ‖X‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = C * ‖X‖ * M := by ring

theorem lieD_le_of_basis : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ (B : Finset (Lie E a)) (C : ℝ), 0 ≤ C ∧ ∀ (ψ : GA E a → ℂ) (g : GA E a) (X : Lie E a) (M : ℝ), (∀ Y ∈ B, ‖lieD Y ψ g‖ ≤ M) → 0 ≤ M → ‖lieD X ψ g‖ ≤ C * ‖X‖ * M := by
  intro E _ _ _ a
  obtain ⟨B, C, hC, h⟩ := exists_finset_clm_bound (Lie E a)
  exact ⟨B, C, hC, fun ψ g X M hB hM => h (fderiv ℝ (chart ψ g) (oneL E a)) X M hB hM⟩

end GlobalTheory.CuspRapid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensity
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem integral_mul_fderiv_lmul_eq_dens (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] {α : Lie E a → ℂ}
    (hα : IsTest (invSet E a) α) (X : Lie E a) {G : Lie E a → ℂ} (hG : ContDiffOn ℝ ∞ G (invSet E a)) :
    ∫ x, α x * fderiv ℝ G x (lmul X x) ∂ν = ∫ x, dens X α x * G x ∂ν := by
  set L := lmul X with hL
  let b := Module.finBasis ℝ (Lie E a)
  let c : Fin (Module.finrank ℝ (Lie E a)) → Lie E a → ℂ := fun i x => α x * (b.repr (L x) i : ℝ)
  have hc : ∀ i, IsTest (invSet E a) (c i) := fun i => hα.mul (Complex.ofRealCLM.contDiff.comp
    ((LinearMap.toContinuousLinearMap (b.coord i)).contDiff.comp L.contDiff))
  have hG' : ∀ v, ContinuousOn (fun x => fderiv ℝ G x v) (invSet E a) := fun v =>
    (hG.continuousOn_fderiv_of_isOpen isOpen_invSet (by simp)).clm_apply continuousOn_const
  have e : ∀ x, α x * fderiv ℝ G x (L x) = ∑ i, c i x * fderiv ℝ G x (b i) := fun x => by
    conv_lhs => rw [← b.sum_repr (L x)]
    simp only [map_sum, map_smul, Finset.mul_sum, c, Complex.real_smul, mul_assoc]
  have hdc : ∀ i x, fderiv ℝ (c i) x (b i) =
      α x * (b.repr (L (b i)) i : ℝ) + (b.repr (L x) i : ℝ) * fderiv ℝ α x (b i) := by
    intro i x
    have h1 : HasFDerivAt (fun x => ((b.repr (L x) i : ℝ) : ℂ))
        (Complex.ofRealCLM.comp ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)) x :=
      (Complex.ofRealCLM.comp ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)).hasFDerivAt
    have h2 := ((hα.1.differentiable (by simp) x).hasFDerivAt).mul h1
    rw [show c i = (α * fun x => ((b.repr (L x) i : ℝ) : ℂ)) from rfl, h2.fderiv]
    simp [Module.Basis.coord_apply, smul_eq_mul]
  have key : ∀ x, ∑ i, fderiv ℝ (c i) x (b i) = -dens X α x := by
    intro x
    have h3 : fderiv ℝ α x (L x) = ∑ i, (b.repr (L x) i : ℝ) * fderiv ℝ α x (b i) := by
      calc fderiv ℝ α x (L x) = fderiv ℝ α x (∑ i, b.repr (L x) i • b i) := by rw [b.sum_repr]
        _ = _ := by rw [map_sum]; simp only [map_smul, Complex.real_smul]
    have h4 : (LinearMap.trace ℝ (Lie E a) L.toLinearMap : ℂ) = ∑ i, ((b.repr (L (b i)) i : ℝ) : ℂ) := by
      rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
      simp [LinearMap.toMatrix_apply]
    simp only [hdc, Finset.sum_add_distrib, dens, neg_neg, ← hL, h3, h4, Finset.sum_mul]
    rw [add_comm]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
  have hi1 : ∀ i, Integrable (fun x => c i x * fderiv ℝ G x (b i)) ν := fun i =>
    (hc i).integrable_mul ν isOpen_invSet (hG' _)
  have hi2 : ∀ i, Integrable (fun x => fderiv ℝ (c i) x (b i) * G x) ν := fun i => by
    simpa using (((hc i).fderiv (b i)).mul contDiff_const (β := fun _ => (1 : ℂ))).integrable_mul ν isOpen_invSet
      hG.continuousOn
  calc ∫ x, α x * fderiv ℝ G x (L x) ∂ν = ∫ x, ∑ i, c i x * fderiv ℝ G x (b i) ∂ν := integral_congr_ae (.of_forall e)
    _ = ∑ i, ∫ x, c i x * fderiv ℝ G x (b i) ∂ν := integral_finset_sum _ fun i _ => hi1 i
    _ = ∑ i, ∫ x, -(fderiv ℝ (c i) x (b i) * G x) ∂ν := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hi2 i) (hi1 i)
        ((hc i).integrable_mul ν isOpen_invSet hG.continuousOn)
        (fun x _ => (hc i).1.differentiable (by simp) x)
        (fun x hx => (hG.contDiffAt (isOpen_invSet.mem_nhds ((hc i).2.2 hx))).differentiableAt (by simp)),
        integral_neg]
    _ = ∫ x, ∑ i, -(fderiv ℝ (c i) x (b i) * G x) ∂ν := (integral_finset_sum _ fun i _ => (hi2 i).neg).symm
    _ = ∫ x, dens X α x * G x ∂ν := by
      refine integral_congr_ae (.of_forall fun x => ?_)
      dsimp only
      rw [Finset.sum_neg_distrib, ← Finset.sum_mul, key, neg_mul, neg_neg]

namespace SmoothingDeriv

omit [IsTotallyComplex E] in

theorem continuous_rmul_fun : Continuous (fun y : Lie E a => rmul y) := by
  let R : Lie E a →ₗ[ℝ] (Lie E a →L[ℝ] Lie E a) :=
    { toFun := rmul
      map_add' := fun x y => ContinuousLinearMap.ext fun z =>
        show Matrix.of z * Matrix.of (x + y) = Matrix.of z * Matrix.of x + Matrix.of z * Matrix.of y by
          rw [← Matrix.of_add_of, Matrix.mul_add]
      map_smul' := fun c x => ContinuousLinearMap.ext fun z =>
        show Matrix.of z * Matrix.of (c • x) = c • (Matrix.of z * Matrix.of x) by
          rw [← Matrix.smul_of, Matrix.mul_smul] }
  exact R.continuous_of_finiteDimensional

omit [IsTotallyComplex E] in
theorem lmul_oneL (y : Lie E a) : lmul (oneL E a) y = y := one_mul (Matrix.of y)

omit [IsTotallyComplex E] in
theorem continuous_lmul_pair : Continuous fun p : Lie E a × Lie E a => lmul p.1 p.2 :=
  Continuous.matrix_mul (A := fun p : Lie E a × Lie E a => Matrix.of p.1) (B := fun p : Lie E a × Lie E a => Matrix.of p.2)
    continuous_fst continuous_snd

theorem chart_smoothing (ν : Measure (Lie E a)) (α : Lie E a → ℂ) (ψ : GA E a → ℂ) (g : GA E a) :
    chart (smoothing ν α ψ) g = fun z => ∫ y, α y * chart ψ g (lmul z y) ∂ν := by
  funext z
  by_cases h : IsUnit (Matrix.of z)
  · obtain ⟨u, hu⟩ := h
    obtain rfl : z = toL u.val := hu.symm
    rw [chart_val, smoothing, chart_mul]
    rfl
  · have h' : ∀ y, chart ψ g (lmul z y) = 0 := fun y => by
      have hn : ¬ IsUnit (Matrix.of (lmul z y)) := fun hy => h (by
        have h2 := (Matrix.isUnit_iff_isUnit_det _).1 hy
        change IsUnit (Matrix.of z * Matrix.of y).det at h2
        rw [Matrix.det_mul] at h2
        exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left h2))
      simp [chart, hn]
    simp only [h', mul_zero, integral_zero]
    simp [chart, h]

end SmoothingDeriv

open SmoothingDeriv in

theorem lieD_smoothing (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] {α : Lie E a → ℂ}
    (hα : IsTest (invSet E a) α) {ψ : GA E a → ℂ} (hψ : ψ ∈ Sm E a) (X : Lie E a) (g : GA E a) :
    lieD X (smoothing ν α ψ) g = smoothing ν (dens X α) ψ g := by
  set f := chart ψ g with hf
  have hfs : ContDiffOn ℝ ∞ f (invSet E a) := hψ g
  have hfd : ContinuousOn (fderiv ℝ f) (invSet E a) :=
    hfs.continuousOn_fderiv_of_isOpen isOpen_invSet (by simp)
  have hmul : ∀ z y, z ∈ invSet E a → y ∈ invSet E a → lmul z y ∈ invSet E a :=
    fun z y hz hy => IsUnit.mul hz hy
  obtain ⟨ε, ε0, hε⟩ := Metric.isOpen_iff.1 isOpen_invSet (oneL E a) isUnit_one
  have hr : 0 < ε / 2 := half_pos ε0
  have hball : Metric.closedBall (oneL E a) (ε / 2) ⊆ invSet E a :=
    (Metric.closedBall_subset_ball (half_lt_self ε0)).trans hε
  set K := (fun p : Lie E a × Lie E a => lmul p.1 p.2) '' (Metric.closedBall (oneL E a) (ε / 2) ×ˢ tsupport α)
  have hKc : IsCompact K := ((isCompact_closedBall _ _).prod hα.2.1.isCompact).image continuous_lmul_pair
  have hKs : K ⊆ invSet E a := by
    rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
    exact hmul _ _ (hball hp1) (hα.2.2 hp2)
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hfd.mono hKs)
  let F : Lie E a → Lie E a → ℂ := fun z y => α y * f (lmul z y)
  let F' : Lie E a → Lie E a → (Lie E a →L[ℝ] ℂ) := fun z y => α y • (fderiv ℝ f (lmul z y)).comp (rmul y)
  have hcontOn : ∀ z ∈ invSet E a, ContinuousOn (fun y => f (lmul z y)) (invSet E a) := fun z hz =>
    hfs.continuousOn.comp (lmul z).continuous.continuousOn fun y hy => hmul z y hz hy
  have hF'c : Continuous (F' (oneL E a)) := by
    refine continuous_of_tsupport fun y hy => ?_
    have hy' : y ∈ invSet E a := hα.2.2 (tsupport_smul_subset_left _ _ hy)
    simp only [F', lmul_oneL]
    exact hα.1.continuous.continuousAt.smul
      ((hfd.continuousAt (isOpen_invSet.mem_nhds hy')).clm_comp continuous_rmul_fun.continuousAt)
  have hbound : ∀ y, ∀ z ∈ Metric.ball (oneL E a) (ε / 2), ‖F' z y‖ ≤ ‖α y‖ * (C * ‖rmul y‖) := by
    intro y z hz
    by_cases h0 : α y = 0
    · simp [F', h0]
    have hy : y ∈ tsupport α := subset_tsupport _ h0
    have hK : lmul z y ∈ K := ⟨(z, y), ⟨Metric.ball_subset_closedBall hz, hy⟩, rfl⟩
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hC _ hK) (norm_nonneg _))) (norm_nonneg _)
  have hbi : Integrable (fun y => ‖α y‖ * (C * ‖rmul y‖)) ν :=
    (hα.1.continuous.norm.mul (continuous_const.mul continuous_rmul_fun.norm)).integrable_of_hasCompactSupport
      hα.2.1.norm.mul_right
  have hdiff : ∀ y, ∀ z ∈ Metric.ball (oneL E a) (ε / 2), HasFDerivAt (fun z => F z y) (F' z y) z := by
    intro y z hz
    by_cases h0 : α y = 0
    · simp only [F, F', h0, zero_mul, zero_smul]; exact hasFDerivAt_const 0 z
    have hy : y ∈ invSet E a := hα.2.2 (subset_tsupport _ h0)
    have hw : lmul z y ∈ invSet E a := hmul _ _ (hball (Metric.ball_subset_closedBall hz)) hy
    have h1 : HasFDerivAt f (fderiv ℝ f (lmul z y)) (rmul y z) :=
      ((hfs.contDiffAt (isOpen_invSet.mem_nhds hw)).differentiableAt (by simp)).hasFDerivAt
    exact (h1.comp z (rmul y).hasFDerivAt).const_mul (α y)
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := F) (F' := F') (Metric.ball_mem_nhds _ hr)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds _ hr) fun z hz =>
      (hα.continuous_mul isOpen_invSet (hcontOn z (hball (Metric.ball_subset_closedBall hz)))).aestronglyMeasurable)
    (hα.integrable_mul ν isOpen_invSet (hcontOn _ isUnit_one)) hF'c.aestronglyMeasurable
    (.of_forall hbound) hbi (.of_forall hdiff)
  have hint : Integrable (F' (oneL E a)) ν :=
    hbi.mono' hF'c.aestronglyMeasurable (.of_forall fun y => hbound y _ (Metric.mem_ball_self hr))
  rw [lieD, chart_smoothing, ← hf, hmain.fderiv, ContinuousLinearMap.integral_apply hint, smoothing,
    ← integral_mul_fderiv_lmul_eq_dens ν hα X hfs]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [F', lmul_oneL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  rfl

theorem lieD_smoothing_eq_dens : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ ψ ∈ Sm E a,
    ∀ (X : Lie E a) (g : GA E a), lieD X (smoothing ν α ψ) g = smoothing ν (dens X α) ψ g :=
  fun _ _ _ _ _ ν _ _ hα _ hψ X g => lieD_smoothing ν hα hψ X g

end GlobalTheory.AutGrowth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralPropertiesStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localTwist_continuous_involution_integral_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), Continuous (thL n w) ∧ (∀ g, thL n w (thL n w g) = g) ∧ (∀ k ∈ GlobalTheory.LFun.KGL w n, thL n w k ∈ GlobalTheory.LFun.KGL w n) ∧ (∀ g y, nrmL n w (g⁻¹ * y * thL n w g) = g⁻¹ * nrmL n w y * g) ∧ IsOpen (GlobalTheory.LFun.KGL w n : Set (GLw n w)) ∧ IsCompact (GlobalTheory.LFun.KGL w n : Set (GLw n w)) ∧ IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) ∧ (∀ δ : GL (Fin n) E, (nrmL n w (locEl n w δ)).val.charpoly = atPl w (δ * thE E n δ).val.charpoly) ∧ ∀ x ∈ locU n w, cLoc w x ∈ UL n w := by
  first | exact @GlobalTheory.BCT.ThBasic.twist_basic | exact GlobalTheory.BCT.ThBasic.twist_basic | (intros; apply GlobalTheory.BCT.ThBasic.twist_basic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRankNormalFormStatement
section
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_rank_normal_form : ∀ (K : Type) [Field K] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (X : Matrix A D K), ∃ (H : Matrix (Fin X.rank) A K) (Q : Matrix D (Fin X.rank) K), H * X * Q = 1 := by
  first | exact @GlobalTheory.rank_frame_exists | exact GlobalTheory.rank_frame_exists | (intros; apply GlobalTheory.rank_frame_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiformHeightLowerBoundStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiformHeight_lowerBound : HtLow := by
  first | exact @GlobalTheory.HtLowProof.htLow | exact GlobalTheory.HtLowProof.htLow | (intros; apply GlobalTheory.HtLowProof.htLow <;> assumption)
end

