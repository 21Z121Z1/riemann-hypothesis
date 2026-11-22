import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0944
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0060
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuaternionMatrixEqOfUnitaryDetOne
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.PlaneSU

section Form

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]

theorem tensor_decomp (b : Module.Basis (Fin 2) F E) (hb0 : b 0 = 1) (z : R ⊗[F] E) :
    ∃ r₀ r₁ : R, z = algebraMap R (R ⊗[F] E) r₀ + algebraMap R (R ⊗[F] E) r₁ * ((1 : R) ⊗ₜ[F] b 1) := by
  let B := Algebra.TensorProduct.basis R b
  have hB : ∀ i, B i = 1 ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply b i
  have hz := B.sum_repr z
  rw [Fin.sum_univ_two, hB, hB, hb0, Algebra.smul_def, Algebra.smul_def, ← Algebra.TensorProduct.one_def,
    mul_one] at hz
  exact ⟨B.repr z 0, B.repr z 1, hz.symm⟩

theorem sigR_algebraMap (σ : E →ₐ[F] E) (r : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  show sigR R σ (r ⊗ₜ[F] 1) = r ⊗ₜ[F] 1
  simp [sigR]

theorem sigR_theta (σ : E →ₐ[F] E) (e : E) (he : σ e = -e) :
    sigR R σ ((1 : R) ⊗ₜ[F] e) = -((1 : R) ⊗ₜ[F] e) := by
  simp [sigR, he, TensorProduct.tmul_neg]

theorem cT_mul_eq_mul_adjugate {A : Type} [CommRing A] (c : A →+* A) (H X : Matrix (Fin 2) (Fin 2) A)
    (hX : Formalism.UG.cT c X * H * X = H) (hd : X.det = 1) : Formalism.UG.cT c X * H = H * X.adjugate := by
  calc Formalism.UG.cT c X * H = Formalism.UG.cT c X * H * (X * X.adjugate) := by
        rw [Matrix.mul_adjugate, hd, one_smul, Matrix.mul_one]
    _ = H * X.adjugate := by rw [← Matrix.mul_assoc, hX]

end Form
end GlobalTheory.PlaneSU

theorem GlobalTheory.PlaneSU.exists_qm_eq_of_unitary : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (δ : F) (b : Module.Basis (Fin 2) F E), b 0 = 1 → σ (b 1) = -b 1 → b 1 * b 1 = algebraMap F E δ → ∀ f₁ f₂ : F, f₁ ≠ 0 → f₂ ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] (X : Matrix (Fin 2) (Fin 2) (R ⊗[F] E)), Formalism.UG.cT (sigR R σ) X * Matrix.diagonal ![algebraMap F (R ⊗[F] E) f₁, algebraMap F (R ⊗[F] E) f₂] * X = Matrix.diagonal ![algebraMap F (R ⊗[F] E) f₁, algebraMap F (R ⊗[F] E) f₂] → X.det = 1 → ∃ x : ℍ[R, algebraMap F R δ, algebraMap F R (-(f₂ / f₁))], qm (algebraMap R (R ⊗[F] E)) ((1 : R) ⊗ₜ[F] b 1) x = X := by
  intro F E _ _ _ σ δ b hb0 hσ _ f₁ f₂ hf₁ _ R _ _ X hX hd
  set ι := algebraMap R (R ⊗[F] E) with hιdef
  set θ : R ⊗[F] E := (1 : R) ⊗ₜ[F] b 1 with hθdef
  set c := sigR R σ with hcdef
  set h₁ := algebraMap F (R ⊗[F] E) f₁ with hh₁
  set h₂ := algebraMap F (R ⊗[F] E) f₂ with hh₂
  set u := algebraMap F (R ⊗[F] E) f₁⁻¹ with hudef
  have key := GlobalTheory.PlaneSU.cT_mul_eq_mul_adjugate c _ X hX hd
  have k00 : c (X 0 0) * h₁ = h₁ * X 1 1 := by
    have := congrFun (congrFun key 0) 0
    simpa [Formalism.UG.cT, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] using this
  have k01 : c (X 1 0) * h₂ = -(h₁ * X 0 1) := by
    have := congrFun (congrFun key 0) 1
    simpa [Formalism.UG.cT, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] using this
  have hcθ : c θ = -θ := GlobalTheory.PlaneSU.sigR_theta σ (b 1) hσ
  have hcι : ∀ r, c (ι r) = ι r := GlobalTheory.PlaneSU.sigR_algebraMap σ
  have hu : h₁ * u = 1 := by
    rw [hh₁, hudef, ← map_mul, mul_inv_cancel₀ hf₁, map_one]
  have hb : ι (algebraMap F R (-(f₂ / f₁))) = -(h₂ * u) := by
    rw [hιdef, ← IsScalarTower.algebraMap_apply, div_eq_mul_inv, map_neg, map_mul]
  obtain ⟨r₀, r₁, hα⟩ := GlobalTheory.PlaneSU.tensor_decomp (R := R) b hb0 (X 0 0)
  obtain ⟨s₀, s₁, hβ⟩ := GlobalTheory.PlaneSU.tensor_decomp (R := R) b hb0 (X 1 0)
  have hcα : c (X 0 0) = ι r₀ - ι r₁ * θ := by rw [hα, map_add, map_mul, hcι, hcι, hcθ]; ring
  have hcβ : c (X 1 0) = ι s₀ - ι s₁ * θ := by rw [hβ, map_add, map_mul, hcι, hcι, hcθ]; ring
  have e00 : ι r₀ + ι r₁ * θ = X 0 0 := hα.symm
  have e10 : ι s₀ - ι (-s₁) * θ = X 1 0 := by rw [hβ, map_neg]; ring
  have e11 : ι r₀ - ι r₁ * θ = X 1 1 := by
    linear_combination (-1 : R ⊗[F] E) * hcα + u * k00 + (X 1 1 - c (X 0 0)) * hu
  have e01 : ι (algebraMap F R (-(f₂ / f₁))) * (ι s₀ + ι (-s₁) * θ) = X 0 1 := by
    rw [hb, map_neg]
    linear_combination (-u) * k01 + X 0 1 * hu + h₂ * u * hcβ
  refine ⟨⟨r₀, r₁, s₀, -s₁⟩, ?_⟩
  show !![ι r₀ + ι r₁ * θ, ι (algebraMap F R (-(f₂ / f₁))) * (ι s₀ + ι (-s₁) * θ);
    ι s₀ - ι (-s₁) * θ, ι r₀ - ι r₁ * θ] = X
  rw [e00, e01, e10, e11]
  exact (Matrix.eta_fin_two X).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealCharacter
section
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv.RealChar

variable {D : D7} {S T : HSp D} (C : GlobalTheory.Ker.Ctx S T)

theorem xB_mem_dom {B : C.Bas} (hB : C.IsB B) : C.xB B ∈ C.X.dom :=
  GlobalTheory.Ker.ONBasis.mem_dom C.X (GlobalTheory.Ker.ONBasis.isONFr_xB C hB)

theorem Th_ne_zero {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {φ : TF S.rank C.g} (hφ : GlobalTheory.SW.IsSB φ)
    (h0 : φ ≠ 0) : C.Th x φ ≠ 0 := by
  intro h
  obtain ⟨l1, l2, -⟩ := GlobalTheory.Ker.Ctx.th_laws D S T C x hx φ hφ
  have h3 : GlobalTheory.SW.IsSB ((0 : ℂ) • φ) := by
    rw [zero_smul]
    exact GlobalTheory.SW.isSB_zero
  refine h0 (((l1 _ h3).2 ?_).trans (zero_smul ℂ φ))
  rw [l2, h, smul_zero]

theorem Th_zero {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) : C.Th x (0 : TF S.rank C.g) = 0 := by
  have h := (GlobalTheory.Ker.Ctx.th_laws D S T C x hx 0 GlobalTheory.SW.isSB_zero).2.1 0
  rwa [zero_smul, zero_smul] at h

theorem scalar_eq {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : GlobalTheory.Ker.IsWeak C.ψ S T om)
    {u : GA D T} {B B' : C.Bas} (hB : C.IsB B) (hB' : C.IsB B') {φ : TF S.rank C.g} (hφ : GlobalTheory.SW.IsSB φ)
    (h0 : φ ≠ 0) {c c' : ℂ} (hc' : ‖c'‖ = 1)
    (e : om (1, u) (C.Th (C.xB B) φ) = c • C.Th (C.xB (C.mvB u B)) φ)
    (e' : om (1, u) (C.Th (C.xB B') φ) = c' • C.Th (C.xB (C.mvB u B')) φ) : c = c' := by
  obtain ⟨⟨μ, 𝓕, hμ⟩, hip⟩ := GlobalTheory.Ker.ScalarProduct.ip_basic D S T C
  have hmv : ∀ A, C.IsB A → C.IsB (C.mvB u A) := fun A hA =>
    (((GlobalTheory.Ker.onBasis_frame_period D S T C).2 A hA).2.2.2.2.2 u).1
  have hth : ∀ A, C.IsB A → C.IsTh (C.Th (C.xB A) φ) := fun A hA =>
    (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ (xB_mem_dom C hA) φ hφ).1.1
  have hd : dbl C.X C.bas C.idx φ φ 0 ≠ 0 := by
    intro hc
    have h1 := GlobalTheory.AdTh.Overlap.ipO_Th C hμ (xB_mem_dom C hB) (xB_mem_dom C hB) hφ hφ
    rw [hc, zero_mul] at h1
    exact Th_ne_zero C (xB_mem_dom C hB) hφ h0 ((hip μ 𝓕 hμ _ (hth B hB)).2.1 h1)
  have hk : kZero C.X C.idx (C.xB B) (C.xB B') (0 : Fin S.rank → Fin C.g → ℂ) 0 ≠ 0 := by
    rw [GlobalTheory.AdTh.Overlap.kZero_zero]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => inv_ne_zero (pow_ne_zero _ (mul_ne_zero
      (DblPoint.det_aLin_ne_zero (xB_mem_dom C hB) (xB_mem_dom C hB') τ)
      (DblPoint.det_aAnti_ne_zero (xB_mem_dom C hB) (xB_mem_dom C hB') τ)))
  have h1 := ((hip μ 𝓕 hμ _ (hth B hB)).2.2.2 _ (hth B' hB')).2.2.2.2.2 om hom (1, u)
  have h2 : GlobalTheory.Ker.ipO μ 𝓕 (c • C.Th (C.xB (C.mvB u B)) φ) (c' • C.Th (C.xB (C.mvB u B')) φ) =
      c * conj c' * GlobalTheory.Ker.ipO μ 𝓕 (C.Th (C.xB (C.mvB u B)) φ) (C.Th (C.xB (C.mvB u B')) φ) := by
    rw [GlobalTheory.Ker.ipO, GlobalTheory.Ker.ipO, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  rw [e, e', h2, GlobalTheory.AdTh.Overlap.ipO_Th C hμ (xB_mem_dom C (hmv B hB)) (xB_mem_dom C (hmv B' hB')) hφ hφ,
    GlobalTheory.AdTh.Overlap.ipO_Th C hμ (xB_mem_dom C hB) (xB_mem_dom C hB') hφ hφ,
    GlobalTheory.AdTh.Overlap.kZero_mvB C hB u] at h1
  have h3 : c * conj c' = 1 := mul_right_cancel₀ (mul_ne_zero hd hk) (h1.trans (one_mul _).symm)
  have h4 : c' * conj c' = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc']
    simp
  linear_combination c' * h3 - c * h4

end GlobalTheory.FrameEquiv.RealChar

open GlobalTheory.FrameEquiv.RealChar in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.FrameEquiv.exists_real_character : ∀ (D : D7) (S T : HSp D) (C : GlobalTheory.Ker.Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak C.ψ S T om → ∃ χ : GA D T → ℂ, (∀ u ∈ GinfC T, ‖χ u‖ = 1) ∧ (∀ u ∈ GinfC T, ∀ u' ∈ GinfC T, χ (u * u') = χ u * χ u') ∧ ∀ u ∈ GinfC T, ∀ B, C.IsB B → ∀ φ : TF S.rank C.g, GlobalTheory.SW.IsSB φ → om (1, u) (C.Th (C.xB B) φ) = χ u • C.Th (C.xB (C.mvB u B)) φ := by
  intro D S T C om hom
  by_cases hex : ∃ φ₀ : TF S.rank C.g, GlobalTheory.SW.IsSB φ₀ ∧ φ₀ ≠ 0
  swap
  · refine ⟨fun _ => 1, fun _ _ => norm_one, fun _ _ _ _ => (mul_one _).symm, fun u _ B hB φ hφ => ?_⟩
    have h0 : φ = 0 := by
      by_contra h
      exact hex ⟨φ, hφ, h⟩
    have hmv : C.IsB (C.mvB u B) := (((GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.2.2.2.2 u).1
    rw [h0, Th_zero C (xB_mem_dom C hB), Th_zero C (xB_mem_dom C hmv), map_zero, smul_zero]
  obtain ⟨φ₀, s₀, n₀⟩ := hex
  obtain ⟨⟨B₀, hB₀⟩, hJ⟩ := GlobalTheory.Ker.onBasis_frame_period D S T C
  have hr := GlobalTheory.Ker.RealScalar.om_real_Th D S T C om hom 1 (one_mem _)
  choose! χ hχ1 hχ using fun u hu => hr u hu B₀ hB₀
  have main : ∀ u ∈ GinfC T, ∀ B, C.IsB B → ∀ φ : TF S.rank C.g, GlobalTheory.SW.IsSB φ →
      om (1, u) (C.Th (C.xB B) φ) = χ u • C.Th (C.xB (C.mvB u B)) φ := fun u hu B hB φ hφ => by
    obtain ⟨c, -, hc⟩ := hr u hu B hB
    rw [← scalar_eq C hom hB hB₀ s₀ n₀ (hχ1 u hu) (hc φ₀ s₀) (hχ u hu φ₀ s₀)]
    exact hc φ hφ
  refine ⟨χ, hχ1, fun u hu u' hu' => ?_, main⟩
  have h1 := main (u * u') (mul_mem hu hu') B₀ hB₀ φ₀ s₀
  obtain ⟨hm, hmul, -⟩ := (hJ B₀ hB₀).2.2.2.2.2 u'
  have e : ((1, u * u') : GA D S × GA D T) = (1, u) * (1, u') := by simp
  rw [e, map_mul, Module.End.mul_apply, main u' hu' B₀ hB₀ φ₀ s₀, map_smul, main u hu _ hm φ₀ s₀, hmul u,
    smul_smul] at h1
  have hne := Th_ne_zero C (xB_mem_dom C ((hJ _ hm).2.2.2.2.2 u).1) s₀ n₀
  rw [mul_comm]
  exact (smul_left_injective ℂ hne h1).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueCoordinatesOfLocalModelBelowPlaceStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residue_coordinates_of_localModel_below_place : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q),
    letI := hQ.isLocalRing; ∀ (N r : ℕ) (V : Place c) (hC : V.Contains Q) (u : Fin r → V.ring),
    (∃ x : Fin N → L, TrBasis c x) →
    (∀ q ∈ IsLocalRing.maximalIdeal Q,
      (⟨q, hC _ q.2⟩ : V.ring) ∈ IsLocalRing.maximalIdeal V.ring) →
    (∀ P : MvPolynomial (Fin r) Q, (∃ α, P.coeff α ∉ IsLocalRing.maximalIdeal Q) →
      IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P)) →
    (∀ f : V.ring, ∃ P R : MvPolynomial (Fin r) Q,
      IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R) ∧
      f * MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R =
        MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P) →
    ∃ (j : ℕ) (s : Fin j → Q), r + j + 1 = N ∧
      ∀ P : MvPolynomial (Fin (r + j)) ℂ, P ≠ 0 →
        IsUnit (MvPolynomial.eval₂ V.const
          (Fin.append u fun i => (⟨s i, hC _ (s i).2⟩ : V.ring)) P) := by
  first | exact @GlobalTheory.FieldPair.exists_residue_coords_of_locModel | exact GlobalTheory.FieldPair.exists_residue_coords_of_locModel | (intros; apply GlobalTheory.FieldPair.exists_residue_coords_of_locModel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResiduePlaceOfTwoDimLocalModelStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residuePlace_of_twoDimLocalModel : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  ∀ (S : Place cL) (ψ : S.ring →+* K), S.IsPrimeOf Q → S.ord (t : L) = 1 →
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) →
  ∃ F : Place cK, (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) ∧
    ∀ us : S.ring, (us : L) = u → F.ord (ψ us) = 1 := by
  first | exact @GlobalTheory.FieldPair.residuePlace_of_locModel | exact GlobalTheory.FieldPair.residuePlace_of_locModel | (intros; apply GlobalTheory.FieldPair.residuePlace_of_locModel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueToComplexOfRationalResidueStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residue_to_complex_of_rationalResidue : ∀ {K : Type} [Field K] [Algebra ℂ K] (R : Subring K) (h : IsLocModel (algebraMap ℂ K) R),
  RatRes (algebraMap ℂ K) R →
  ∃ ε : R →+* ℂ, (∀ a : ℂ, ε ⟨algebraMap ℂ K a, h.const_mem a⟩ = a) ∧ ∀ r : R, ε r = 0 ↔ NonUnit R (r : K) := by
  first | exact @GlobalTheory.FieldPair.exists_residue_complex | exact GlobalTheory.FieldPair.exists_residue_complex | (intros; apply GlobalTheory.FieldPair.exists_residue_complex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionAmpleTwistNonvanishingFiniteSetStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_ampleTwist_nonvanishing_finiteSet : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M A : HermLB p), IsAmpleLB A.B → ∀ S : Set X, S.Finite → ∃ b : ℕ, 0 < b ∧ ∃ u : (M.tens (A.pow b)).B.Sec, S ⊆ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  first | exact @GlobalTheory.VolBr.exists_sec_finite_subset_nonzeroLocus | exact GlobalTheory.VolBr.exists_sec_finite_subset_nonzeroLocus | (intros; apply GlobalTheory.VolBr.exists_sec_finite_subset_nonzeroLocus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionExtendingRationalGenericFibreMulIntStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_extending_rationalGenericFibre_mul_int : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (B : LB X), B.IsLB → ∀ t : (B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))).Sec, ∃ s : B.Sec, ∀ y : ↥(Limits.pullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))), (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))) y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ↔ y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
  first | exact @GlobalTheory.GenSecInt.main | exact GlobalTheory.GenSecInt.main | (intros; apply GlobalTheory.GenSecInt.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualLatticeSemicharacterVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDualLattice_semicharacter_vacuum : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ b : 𝓞 D.host.E, (b : D.host.E) + star (b : D.host.E) = 1 → ∃ χ : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) χ ∧ ∀ l ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True), χ l = ψ (symplOH S T (l.map fun z => incA D (b : D.host.E) * z) l) := by
  first | exact @GlobalTheory.SemiCharValue.exists_semichar_value | exact GlobalTheory.SemiCharValue.exists_semichar_value | (intros; apply GlobalTheory.SemiCharValue.exists_semichar_value <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallOpenCompactNormal
section
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

noncomputable section
namespace GlobalTheory.GamMul.Cong

section Ring
variable {R : Type} [CommRing R] {m m₁ m₂ : ℕ}

theorem put_mul_put (y z : Matrix (Fin m₁) (Fin m₂) R) : put m 0 m₁ y * put m 0 m₁ z = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  simp only [put, Matrix.of_apply]
  split_ifs with h1 h2
  · omega
  all_goals simp

theorem uni_val (y : Matrix (Fin m₁) (Fin m₂) R) :
    (uni m 0 m₁ y).val = 1 + put m 0 m₁ y ∧ ((uni m 0 m₁ y)⁻¹).val = 1 - put m 0 m₁ y := by
  let u : GL (Fin m) R := ⟨1 + put m 0 m₁ y, 1 - put m 0 m₁ y,
    by simp [add_mul, mul_sub, put_mul_put], by simp [sub_mul, mul_add, put_mul_put]⟩
  have : uni m 0 m₁ y = u := toGL_val u
  rw [this]
  exact ⟨rfl, rfl⟩

theorem put_inl_inr (h : m₁ + m₂ = m) (y : Matrix (Fin m₁) (Fin m₂) R) (i : Fin m₁) (j : Fin m₂) :
    put m 0 m₁ y (stdSum h (.inl i)) (stdSum h (.inr j)) = y i j := by
  simp only [put, Matrix.of_apply]
  rw [dif_pos (by simp)]
  congr 1 <;> ext <;> simp

theorem put_inr (h : m₁ + m₂ = m) (y : Matrix (Fin m₁) (Fin m₂) R) (i : Fin m₂) (j : Fin m) :
    put m 0 m₁ y (stdSum h (.inr i)) j = 0 := by
  simp only [put, Matrix.of_apply]
  rw [dif_neg (by simp)]

end Ring

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mul_bd {a b d : Type} [Fintype b] {X : Matrix a b k} {Y : Matrix b d k} {s t : ValueGroupWithZero k}
    (hX : ∀ i j, valuation k (X i j) ≤ s) (hY : ∀ i j, valuation k (Y i j) ≤ t) (i : a) (j : d) :
    valuation k ((X * Y) i j) ≤ s * t := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact mul_le_mul' (hX i l) (hY l j)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem solve_bd {a : Type} [Fintype a] [DecidableEq a] {A : Matrix a a k} (hA : ∀ i j, valuation k ((A - 1) i j) < 1)
    {x : a → k} {s : ValueGroupWithZero k} (hb : ∀ i, valuation k ((A *ᵥ x) i) ≤ s) (i : a) :
    valuation k (x i) ≤ s := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => valuation k (x i)) ⟨i, Finset.mem_univ _⟩
  refine (hi₀ i (Finset.mem_univ _)).trans ?_
  by_contra hlt
  rw [not_le] at hlt
  have h0 : 0 < valuation k (x i₀) := lt_of_le_of_lt zero_le hlt
  have e : x i₀ = (A *ᵥ x) i₀ - ((A - 1) *ᵥ x) i₀ := by simp [Matrix.sub_mulVec]
  have h1 : valuation k (((A - 1) *ᵥ x) i₀) < valuation k (x i₀) := by
    simp only [Matrix.mulVec, dotProduct]
    refine Valuation.map_sum_lt _ h0.ne' fun l _ => ?_
    rw [map_mul]
    calc _ ≤ valuation k ((A - 1) i₀ l) * valuation k (x i₀) := mul_le_mul' le_rfl (hi₀ l (Finset.mem_univ _))
      _ < 1 * valuation k (x i₀) := mul_lt_mul_of_pos_right (hA _ _) h0
      _ = _ := one_mul _
  have h2 := Valuation.map_sub_lt (valuation k) ((hb i₀).trans_lt hlt) h1
  rw [← e] at h2
  exact lt_irrefl _ h2

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem isUnit_of_near {a : Type} [Fintype a] [DecidableEq a] {A : Matrix a a k}
    (hA : ∀ i j, valuation k ((A - 1) i j) < 1) : IsUnit A := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  rw [← sub_eq_zero]
  funext i
  have := solve_bd hA (x := x - y) (s := 0) (fun i => by simp [Matrix.mulVec_sub, hxy]) i
  simpa using this

theorem bd_KO {n : Type} [Fintype n] [DecidableEq n] {g : GL n k} (hg : g ∈ KO k n) (i j : n) :
    valuation k (g.val i j) ≤ 1 := ((GlobalTheory.SplitFlip.mem_KO_iff g).1 hg).1 i j

def congK (m : ℕ) (c : kˣ) : Subgroup (GL (Fin m) k) where
  carrier := {g | g ∈ KO k (Fin m) ∧ g.val - 1 ∈ box m m c}
  one_mem' := ⟨one_mem _, fun i j => by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨mul_mem hx hy, fun i j => ?_⟩
    have e : (x * y).val - 1 = (x.val - 1) * y.val + (y.val - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [e, Matrix.add_apply]
    exact Valuation.map_add_le _ (by simpa using mul_bd hx' (bd_KO hy) i j) (hy' i j)
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨inv_mem hx, fun i j => ?_⟩
    have e : (x⁻¹).val - 1 = -((x.val - 1) * (x⁻¹).val) := by
      rw [sub_mul, Units.mul_inv]; noncomm_ring
    rw [e, Matrix.neg_apply, Valuation.map_neg]
    simpa using mul_bd hx' (bd_KO (inv_mem hx)) i j

theorem isOpen_congK (m : ℕ) (c : kˣ) : IsOpen (congK m c : Set (GL (Fin m) k)) := by
  have hb : IsOpen (box m m c) := by rw [box_eq_standard_box]; exact GlobalTheory.LocMod.Inhab.isOpen_box c
  exact GlobalTheory.SplitFlip.isOpen_KO.inter
    (hb.preimage (f := fun g : GL (Fin m) k => g.val - 1) (Units.continuous_val.sub continuous_const))

theorem conj_mem_congK (m : ℕ) (c : kˣ) {x y : GL (Fin m) k} (hx : x ∈ KO k (Fin m)) (hy : y ∈ congK m c) :
    x * y * x⁻¹ ∈ congK m c := by
  refine ⟨mul_mem (mul_mem hx hy.1) (inv_mem hx), fun i j => ?_⟩
  have e : (x * y * x⁻¹).val - 1 = x.val * (y.val - 1) * (x⁻¹).val := by
    rw [mul_sub, sub_mul, mul_one, Units.mul_inv, Units.val_mul, Units.val_mul]
  rw [e]
  simpa using mul_bd (mul_bd (bd_KO hx) hy.2) (bd_KO (inv_mem hx)) i j

theorem uni_mem_congK {m m₁ m₂ : ℕ} {c : kˣ} (hc : valuation k (c : k) ≤ 1) {y : Matrix (Fin m₁) (Fin m₂) k}
    (hy : y ∈ box m₁ m₂ c) : uni m 0 m₁ y ∈ congK m c := by
  have hp : ∀ i j, valuation k (put m 0 m₁ y i j) ≤ valuation k (c : k) := fun i j => by
    simp only [put, Matrix.of_apply]
    split_ifs
    · exact hy _ _
    · simp
  have h1 : ∀ i j, valuation k ((1 : Matrix (Fin m) (Fin m) k) i j) ≤ 1 := bd_KO (one_mem _)
  refine ⟨(GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rw [(uni_val y).1]
    exact Valuation.map_add_le (valuation k) (h1 i j) ((hp i j).trans hc)
  · rw [(uni_val y).2]
    exact Valuation.map_sub_le (valuation k) (h1 i j) ((hp i j).trans hc)
  · rw [(uni_val y).1, add_sub_cancel_left]
    exact hp i j

theorem factor_congK {m m₁ m₂ : ℕ} (h : m₁ + m₂ = m) {c : kˣ} (hc : valuation k (c : k) < 1) {g : GL (Fin m) k}
    (hg : g ∈ congK m c) : ∃ p ∈ parabLower k (two (stdSum h)), ∃ y ∈ box m₁ m₂ c, g = p * uni m 0 m₁ y := by
  set e := stdSum h with he
  let A : Matrix (Fin m₁) (Fin m₁) k := Matrix.of fun i j => g.val (e (.inl i)) (e (.inl j))
  let B : Matrix (Fin m₁) (Fin m₂) k := Matrix.of fun i j => g.val (e (.inl i)) (e (.inr j))
  have hA : ∀ i j, valuation k ((A - 1) i j) < 1 := fun i j => by
    have := (hg.2 (e (.inl i)) (e (.inl j))).trans_lt hc
    simpa [A, Matrix.one_apply] using this
  have hB : ∀ i j, valuation k (B i j) ≤ valuation k (c : k) := fun i j => by
    have := hg.2 (e (.inl i)) (e (.inr j))
    simpa [B, Matrix.one_apply] using this
  obtain ⟨a, ha⟩ := isUnit_of_near hA
  have hy : A * ((a⁻¹).val * B) = B := by rw [← ha, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  generalize (a⁻¹).val * B = y at hy
  refine ⟨g * (uni m 0 m₁ y)⁻¹, (mem_parabLower_two k).2 fun i j => ?_, y, fun i j => ?_, by simp⟩
  · rw [Units.val_mul, (uni_val y).2, mul_sub, mul_one, Matrix.sub_apply, Matrix.mul_apply, ← e.sum_comp,
      Fintype.sum_sum_type]
    simp only [he, put_inl_inr, put_inr, mul_zero, Finset.sum_const_zero, add_zero]
    have := congrFun (congrFun hy i) j
    rw [Matrix.mul_apply] at this
    exact sub_eq_zero.2 this.symm
  · refine solve_bd hA (x := fun l => y l j) (fun l => ?_) i
    have := hB l j
    rw [← hy] at this
    exact this

theorem exists_congK_subset (m : ℕ) {U : Set (GL (Fin m) k)} (hU : U ∈ nhds (1 : GL (Fin m) k)) :
    ∃ c : kˣ, valuation k (c : k) < 1 ∧ (congK m c : Set (GL (Fin m) k)) ⊆ U := by
  rw [GlobalTheory.SplitFlip.isEmbedding_val_GL.isInducing.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  have hc : Continuous fun X : Matrix (Fin m) (Fin m) k => X + 1 := continuous_id.add continuous_const
  have hV' : (fun X : Matrix (Fin m) (Fin m) k => X + 1) ⁻¹' V ∈ nhds (0 : Matrix (Fin m) (Fin m) k) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨c, hc⟩ := GlobalTheory.LocMod.Inhab.exists_box_subset hV'
  obtain ⟨d, hd0, hd1⟩ : ∃ d : k, d ≠ 0 ∧ valuation k d < 1 := by
    obtain ⟨d, h1, h2⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
    exact ⟨d, by simpa using h1, h2⟩
  have key : ∀ c' : kˣ, valuation k (c' : k) ≤ valuation k (c : k) → (congK m c' : Set (GL (Fin m) k)) ⊆ U := by
    intro c' h g hg
    refine hVU ?_
    have := hc _ (box_mono m m h hg.2)
    simpa using this
  rcases le_total (valuation k (c : k)) (valuation k d) with h | h
  · exact ⟨c, h.trans_lt hd1, key c le_rfl⟩
  · exact ⟨Units.mk0 d hd0, hd1, key _ h⟩

theorem exists_cong_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m m₁ m₂ : ℕ) (h : m₁ + m₂ = m), ∀ U ∈ nhds (1 : GL (Fin m) k), ∃ (c : kˣ) (K : Subgroup (GL (Fin m) k)), IsOpen (K : Set (GL (Fin m) k)) ∧ IsCompact (K : Set (GL (Fin m) k)) ∧ (K : Set (GL (Fin m) k)) ⊆ U ∧ K ≤ KO k (Fin m) ∧ (∀ x ∈ KO k (Fin m), ∀ y ∈ K, x * y * x⁻¹ ∈ K) ∧ (∀ y ∈ box m₁ m₂ c, uni m 0 m₁ y ∈ K) ∧ (∀ g ∈ K, ∃ p ∈ parabLower k (two (stdSum h)), ∃ y ∈ box m₁ m₂ c, g = p * uni m 0 m₁ y) ∧ IsOpen (KO k (Fin m) : Set (GL (Fin m) k)) ∧ IsCompact (KO k (Fin m) : Set (GL (Fin m) k)) := by
  intro k _ _ _ _ m m₁ m₂ h U hU
  obtain ⟨c, hc, hK⟩ := exists_congK_subset m hU
  exact ⟨c, congK m c, isOpen_congK m c,
    GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ (isOpen_congK m c)) fun _ hg => hg.1,
    hK, fun _ hg => hg.1, fun x hx y hy => conj_mem_congK m c hx hy, fun y hy => uni_mem_congK hc.le hy,
    fun g hg => factor_congK h hc hg, GlobalTheory.SplitFlip.isOpen_KO, GlobalTheory.SplitFlip.isCompact_KO⟩

end GlobalTheory.GamMul.Cong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopologicalKrullDimClosurePointLeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_topologicalKrullDim_closure_point_le : ∀ (X : Scheme.{0}) (n : ℕ) (z : X), topologicalKrullDim X = n → ∃ e : ℕ, e ≤ n ∧ topologicalKrullDim (closure ({z} : Set X)) = e ∧ ∀ x, z ⤳ x → x ≠ z → 1 ≤ e := by
  first | exact @GlobalTheory.closure_point_topologicalKrullDim | exact GlobalTheory.closure_point_topologicalKrullDim | (intros; apply GlobalTheory.closure_point_topologicalKrullDim <;> assumption)
end

