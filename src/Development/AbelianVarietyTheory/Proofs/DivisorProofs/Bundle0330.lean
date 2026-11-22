import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0286
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0222
import ReciprocityTheory.Chebotarev.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleXSqAddOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0297
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0307
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0262

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGenericFibreClosurePartition
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem smooth_genericFibre_closure_partition : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Smooth f → ∀ C C' : Set X, C ∪ C' = f ⁻¹' {(⊥ : PrimeSpectrum R)} → Disjoint C (closure C') → Disjoint (closure C) C' → Disjoint (closure C) (closure C') ∧ closure C ∪ closure C' = Set.univ := by
  intro R _ _ _ X f hf C C' hU h1 h2
  have key : ∀ (A : CommRingCat.{0}) (j : Spec A ⟶ X) [IsOpenImmersion j],
      Disjoint (j ⁻¹' closure C) (j ⁻¹' closure C') ∧
        (j ⁻¹' closure C) ∪ (j ⁻¹' closure C') = Set.univ := by
    intro A j _
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ f)
    have hs : Smooth (Spec.map φ) := by rw [hφ]; infer_instance
    have hφs : φ.hom.Smooth := (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs
    letI : Algebra R A := φ.hom.toAlgebra
    have hA : Algebra.Smooth R A := hφs
    have hcl : ∀ S : Set X, j ⁻¹' closure S = closure (j ⁻¹' S) := fun S =>
      j.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage j.continuous S
    rw [hcl, hcl]
    refine GlobalTheory.T.closure_generic_fibre_clopen_split_alt R A hA (j ⁻¹' C) (j ⁻¹' C') ?_ ?_ ?_
    · have : j ⁻¹' C ∪ j ⁻¹' C' = (Spec.map φ) ⁻¹' {(⊥ : PrimeSpectrum R)} := by
        rw [← Set.preimage_union, hU, hφ, ← Set.preimage_comp, Scheme.Hom.comp_base]
        rfl
      refine this.trans ?_
      ext r
      exact ⟨fun h => congrArg PrimeSpectrum.asIdeal h, fun h => PrimeSpectrum.ext h⟩
    · have := h1.preimage j
      rw [hcl] at this
      exact this
    · have := h2.preimage j
      rw [hcl] at this
      exact this
  constructor
  · rw [Set.disjoint_left]
    intro x hx hx'
    obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
    exact Set.disjoint_left.mp (@key _ (X.affineCover.f i) (X.affineCover.map_prop i)).1 hx hx'
  · rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
    exact (Set.eq_univ_iff_forall.mp (@key _ (X.affineCover.f i) (X.affineCover.map_prop i)).2) y

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitarySiegelParabolicBlockRelations
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

open MeasureTheory Matrix in

theorem _root_.GlobalTheory.KSp.sieg_blocks : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E)
    (hE : _root_.GlobalTheory.WeilM.IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (p : _root_.GlobalTheory.WeilM.UG c (_root_.GlobalTheory.SplitUnitary.stdJ ν E)), p ∈ _root_.GlobalTheory.KSp.sieg c ν →
    (_root_.GlobalTheory.KSp.mat c p).toBlocks₁₁ * (((_root_.GlobalTheory.KSp.mat c p).toBlocks₂₂).map c)ᵀ = 1 ∧
    (_root_.GlobalTheory.KSp.mat c p).toBlocks₁₁ * (((_root_.GlobalTheory.KSp.mat c p).toBlocks₁₂).map c)ᵀ = (_root_.GlobalTheory.KSp.mat c p).toBlocks₁₂ * (((_root_.GlobalTheory.KSp.mat c p).toBlocks₁₁).map c)ᵀ ∧
    ∃ (a : GL ν E) (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b), p = _root_.GlobalTheory.SplitUnitary.levi c hE.invol a * _root_.GlobalTheory.KSp.unip c b hb := by
  intro F _ _ E _ _ c δ hE ν _ _ p hp
  rw [_root_.GlobalTheory.KSp.mem_sieg] at hp
  have hc := hE.invol
  have hu := (_root_.GlobalTheory.SplitUnitary.mem_UG_iff c (p : GL (ν ⊕ ν) E)).mp p.2
  have hM : ((p : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = _root_.GlobalTheory.KSp.mat c p := rfl
  set M := _root_.GlobalTheory.KSp.mat c p
  rw [hM, ← fromBlocks_toBlocks M, hp] at hu
  unfold _root_.GlobalTheory.SplitUnitary.stdJ at hu
  simp only [fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_inj] at hu
  simp at hu
  obtain ⟨h1, h2, h3⟩ := hu
  have h2' := mul_eq_one_comm.mp h2
  have h3' := mul_eq_one_comm.mp h3
  have hcc : ∀ X : Matrix ν ν E, (X.map c).map c = X := fun X => by ext i j; simp [hc]
  have hAB : M.toBlocks₁₁ * (M.toBlocks₁₂.map c)ᵀ = M.toBlocks₁₂ * (M.toBlocks₁₁.map c)ᵀ :=
    sub_eq_zero.mp (by rw [← neg_add_eq_sub]; exact h1)
  refine ⟨h2, hAB, ?_⟩
  set A := M.toBlocks₁₁
  set B := M.toBlocks₁₂
  set D := M.toBlocks₂₂
  let a : GL ν E := ⟨A, (D.map c)ᵀ, h2, h2'⟩
  have hb : (((D.map c)ᵀ * B).map c)ᵀ = (D.map c)ᵀ * B := by
    rw [Matrix.map_mul, transpose_mul, transpose_map, hcc, transpose_transpose]
    have hB : B * (A.map c)ᵀ = A * (B.map c)ᵀ := hAB.symm
    calc (B.map c)ᵀ * D = (D.map c)ᵀ * A * (B.map c)ᵀ * D := by rw [h2', Matrix.one_mul]
      _ = (D.map c)ᵀ * (B * (A.map c)ᵀ) * D := by rw [hB]; simp only [Matrix.mul_assoc]
      _ = (D.map c)ᵀ * B * ((A.map c)ᵀ * D) := by simp only [Matrix.mul_assoc]
      _ = (D.map c)ᵀ * B := by rw [h3', Matrix.mul_one]
  refine ⟨a, (D.map c)ᵀ * B, hb, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, _root_.GlobalTheory.SplitUnitary.levi_val, hM]
  unfold _root_.GlobalTheory.KSp.unip
  simp only [fromBlocks_multiply]
  have ha : ((a⁻¹ : GL ν E) : Matrix ν ν E) = (D.map c)ᵀ := rfl
  rw [ha, transpose_map, hcc, transpose_transpose, ← Matrix.mul_assoc, h2]
  conv_lhs => rw [← fromBlocks_toBlocks M, hp]
  simp [A, B, D]
  rfl

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubInvMulOutMemIff
section
open MeasureTheory Matrix ValuativeRel

namespace GlobalTheory.HeisUnit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open Classical in

theorem intInd_apply {n d : ℕ} (M : Matrix (Fin n) (Fin d) k) :
    intInd k n d M = if ∀ i j, M i j ∈ 𝒪[k] then 1 else 0 := by
  classical
  simp only [intInd, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]

theorem sub_inv_mul_out_mem_iff {ϖ : kˣ} (hϖ : SplitFlip.IsUnif ϖ) (y : k) (t : SplitFlip.Res k 1) :
    y - (ϖ : k)⁻¹ * ((Quotient.out t : 𝒪[k]) : k) ∈ 𝒪[k] ↔
      ∃ h : (ϖ : k) * y ∈ 𝒪[k], t = Ideal.Quotient.mk _ ⟨(ϖ : k) * y, h⟩ := by
  have ht : t = Ideal.Quotient.mk _ (Quotient.out t) := (Quotient.out_eq t).symm
  set a := Quotient.out t
  have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
  constructor
  · intro hc
    have hy : (ϖ : k) * y = ϖ * (y - (ϖ : k)⁻¹ * a) + a := by field_simp; ring
    have hmem : (ϖ : k) * y ∈ 𝒪[k] := hy ▸ add_mem (mul_mem hϖ.mem hc) a.2
    refine ⟨hmem, ?_⟩
    rw [ht, Ideal.Quotient.eq, pow_one, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton']
    refine ⟨-⟨_, hc⟩, Subtype.ext ?_⟩
    push_cast
    field_simp
    ring
  · rintro ⟨h, e⟩
    have e' := ht.symm.trans e
    rw [Ideal.Quotient.eq, pow_one, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at e'
    obtain ⟨c, hc⟩ := e'
    have hc' : (c : k) * ϖ = a - ϖ * y := by simpa using congrArg Subtype.val hc
    have hinv : (ϖ : k)⁻¹ * ϖ = 1 := inv_mul_cancel₀ hϖ0
    have : y - (ϖ : k)⁻¹ * a = -(c : k) := by
      linear_combination (ϖ : k)⁻¹ * hc' - (y + c) * hinv
    rw [this]
    exact neg_mem c.2

theorem intInd_diagAt_eq_sum : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i0 : Fin n) (Y : Matrix (Fin n) (Fin d) k),
    GlobalTheory.HeisUnit.intInd k n d ((GlobalTheory.HeisUnit.diagAt ϖ i0).valᵀ * Y) =
      ∑ T : Fin d → GlobalTheory.SplitFlip.Res k 1, GlobalTheory.HeisUnit.intInd k n d (Y + GlobalTheory.HeisUnit.cosetRep ϖ i0 T) := by
  intro k _ _ _ _ n d ϖ hϖ i0 Y
  classical
  have hL : ∀ i j, ((diagAt ϖ i0).valᵀ * Y) i j = (if i = i0 then (ϖ : k) else 1) * Y i j := by
    intro i j
    rw [diagAt_val, diagonal_transpose, diagonal_mul]
  have hR : ∀ (T : Fin d → SplitFlip.Res k 1) i j, (Y + cosetRep ϖ i0 T) i j =
      if i = i0 then Y i j - (ϖ : k)⁻¹ * ((Quotient.out (T j) : 𝒪[k]) : k) else Y i j := by
    intro T i j
    simp only [cosetRep, Matrix.add_apply, Matrix.of_apply]
    split_ifs <;> ring
  by_cases hQR : (∀ i j, i ≠ i0 → Y i j ∈ 𝒪[k]) ∧ ∀ j, (ϖ : k) * Y i0 j ∈ 𝒪[k]
  · obtain ⟨hQ, hRR⟩ := hQR
    let T0 : Fin d → SplitFlip.Res k 1 := fun j => Ideal.Quotient.mk _ ⟨_, hRR j⟩
    have hl : intInd k n d ((diagAt ϖ i0).valᵀ * Y) = 1 := by
      rw [intInd_apply, if_pos]
      intro i j
      rw [hL]
      split_ifs with h
      · subst h; exact hRR j
      · rw [one_mul]; exact hQ i j h
    have hs : ∀ T, intInd k n d (Y + cosetRep ϖ i0 T) = if T = T0 then 1 else 0 := by
      intro T
      rw [intInd_apply]
      by_cases hT : T = T0
      · rw [if_pos hT, if_pos]
        intro i j
        rw [hR]
        split_ifs with h
        · subst h; exact (sub_inv_mul_out_mem_iff hϖ _ _).2 ⟨hRR j, by rw [hT]⟩
        · exact hQ i j h
      · rw [if_neg hT, if_neg]
        intro hm
        apply hT
        funext j
        have := hm i0 j
        rw [hR, if_pos rfl] at this
        obtain ⟨_, e⟩ := (sub_inv_mul_out_mem_iff hϖ _ _).1 this
        exact e
    rw [hl, Finset.sum_congr rfl (fun T _ => hs T), Finset.sum_ite_eq']
    simp
  · have hl : intInd k n d ((diagAt ϖ i0).valᵀ * Y) = 0 := by
      rw [intInd_apply, if_neg]
      intro hm
      refine hQR ⟨fun i j h => ?_, fun j => ?_⟩
      · have := hm i j; rwa [hL, if_neg h, one_mul] at this
      · have := hm i0 j; rwa [hL, if_pos rfl] at this
    rw [hl]
    symm
    apply Finset.sum_eq_zero
    intro T _
    rw [intInd_apply, if_neg]
    intro hm
    refine hQR ⟨fun i j h => ?_, fun j => ?_⟩
    · have := hm i j; rwa [hR, if_neg h] at this
    · have := hm i0 j
      rw [hR, if_pos rfl] at this
      exact ((sub_inv_mul_out_mem_iff hϖ _ _).1 this).1

end GlobalTheory.HeisUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHilbertEisensteinLatticeClassWeightTwo
section
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem GlobalTheory.HeckeTwo.summable_eisClass_two : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
    Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 2 σ z) := by
  intro F _ _ _ 𝔞 𝔟 σ hσ z hz
  obtain ⟨C, hC⟩ := GlobalTheory.T.hilbertEisensteinLatticeSummand_weightTwo_bound F σ hσ z hz
  have hS := (GlobalTheory.T.summable_gaussianExtension_norm_rpow F 𝔞 𝔟 (1 + σ.re) (by linarith) (GlobalTheory.T.finite_gaussianExtension_units_quot_units F)).mul_left C
  refine Summable.of_norm_bounded hS fun c => ?_
  have hp : c.out.1 ≠ 0 := c.out.2.2.2
  have e : |((Algebra.norm ℚ (GlobalTheory.GaussExt.gEmb F c.out.1) : ℚ) : ℝ)| =
      ∏ τ : F →+* ℝ, ((τ c.out.1.1) ^ 2 + (τ c.out.1.2) ^ 2) := by
    rw [GlobalTheory.T.algebraNorm_rat_gaussianExtensionOfPair F c.out.1.1 c.out.1.2]
    exact abs_of_nonneg (Finset.prod_nonneg fun τ _ => by positivity)
  rw [e]
  exact hC _ hp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaProjectionEigenImage
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem smul_one_mulVec_divisor {R : Type} [CommRing R] {n : ℕ} (c : R) (v : Fin n → R) :
    (c • (1 : Matrix (Fin n) (Fin n) R)) *ᵥ v = c • v := by
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

theorem proj_kills_other_eig : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (σ : Λ →+* O) (f : RL p O Λ →+* O) (ρ : Λ → Matrix (Fin h) (Fin h) (Ainf p O)) (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) (π : (Fin h → C) →ₗ[C] (Fin N → C)), Function.Injective (algebraMap O C) → IsTheta σ f → IsFrame ρ e → IsProj C e f π → ∀ z ∈ ⨆ s : {s : Λ →+* O // s ≠ σ}, eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) s.1, π z = 0 := by
  intro p _ O _ _ _ C _ _ Λ _ _ N h σ f ρ e π hinj hθ hfr hπ z hz
  suffices hle : (⨆ s : {s : Λ →+* O // s ≠ σ}, eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) s.1) ≤ LinearMap.ker π from
    LinearMap.mem_ker.mp (hle hz)
  refine iSup_le fun s => ?_
  intro z hz
  rw [LinearMap.mem_ker]
  obtain ⟨l, hl⟩ : ∃ l, s.1 l ≠ σ l := by
    by_contra hc
    push_neg at hc
    exact s.2 (RingHom.ext hc)

  have hmat : IsMat e e (ρ l) (((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l : RL p O Λ) • (1 : Matrix (Fin N) (Fin N) (RL p O Λ))) := by
    intro w
    rw [smul_one_mulVec_divisor, hfr l w]
  have h1 := GlobalTheory.T.theta_projection_intertwining p O C Λ N h f e e π π (ρ l) _ hπ hπ hmat z
  have hf : f ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) = σ l := by
    rw [hθ]; simp
  have hY : ((((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l : RL p O Λ) • (1 : Matrix (Fin N) (Fin N) (RL p O Λ))).map ((algebraMap O C).comp f)) = (algebraMap O C (σ l)) • (1 : Matrix (Fin N) (Fin N) C) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, hf]
  rw [hY, smul_one_mulVec_divisor] at h1

  have hz' : redC C (ρ l) z = algebraMap O C (s.1 l) • z := by
    have := (Submodule.mem_iInf _).mp hz l
    rw [Module.End.mem_eigenspace_iff] at this
    rw [← this]
    simp [redC, Matrix.map_map]
  rw [hz', map_smul] at h1
  have hne : algebraMap O C (s.1 l) - algebraMap O C (σ l) ≠ 0 := by
    rw [sub_ne_zero]; exact fun h => hl (hinj h)
  have h2 : (algebraMap O C (s.1 l) - algebraMap O C (σ l)) • π z = 0 := by
    rw [sub_smul, h1, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left hne

end GlobalTheory.DetInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToSpanSingletonConstGenSurjective
section
noncomputable section

open CategoryTheory

namespace GlobalTheory

namespace PDivGroup

theorem exists_algHom_pi_eq_eval {O ι : Type*} [CommRing O] [Nontrivial O] [Finite ι]
    (hO : ∀ e : O, IsIdempotentElem e → e = 0 ∨ e = 1) (f : (ι → O) →ₐ[O] O) :
    ∃ k, ∀ g, f g = g k := by
  classical
  have := Fintype.ofFinite ι
  have h1 : ∃ k, f (Pi.single k 1) ≠ 0 := by
    by_contra h
    have h' : ∀ k, f (Pi.single k 1) = 0 := fun k => by_contra fun hk => h ⟨k, hk⟩
    have h2 : f (∑ k, Pi.single k 1) = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero fun k _ => h' k
    have h3 : (∑ k, Pi.single k 1 : ι → O) = 1 := Finset.univ_sum_single (1 : ι → O)
    rw [h3, map_one] at h2
    exact one_ne_zero h2
  obtain ⟨k, hk⟩ := h1
  have hi : IsIdempotentElem (Pi.single k 1 : ι → O) := by
    rw [IsIdempotentElem, ← Pi.single_mul, mul_one]
  have h4 : f (Pi.single k 1) = 1 := (hO _ (hi.map f)).resolve_left hk
  refine ⟨k, fun g => ?_⟩
  have h5 : g * Pi.single k 1 = g k • (Pi.single k 1 : ι → O) := by
    funext j
    by_cases hj : j = k
    · subst hj; simp
    · simp [hj]
  have h6 := congrArg f h5
  rwa [map_mul, map_smul, h4, mul_one, smul_eq_mul, mul_one] at h6

variable (p : ℕ) (O : Type) [CommRing O] [Fact p.Prime]

@[simp] theorem constHom_constGen : constHom _ (constGen p O) = 𝟙 _ := by
  rw [← LinearEquiv.eq_symm_apply, constHom_symm_apply, tateMap_id]

variable [Nontrivial O]

theorem toSpanSingleton_constGen_surjective
    (hO : ∀ e : O, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Function.Surjective (LinearMap.toSpanSingleton ℤ_[p] _ (constGen p O)) := fun t => by
  have h1 : ∀ n, ∃ k : ℕ, ∀ φ, t.pt n φ = constFun p O n φ k := fun n => by
    obtain ⟨k, hk⟩ := exists_algHom_pi_eq_eval hO
      ((t.pt n).comp ((constFun p O n).symm : (ZMod (p ^ n) → O) →ₐ[O] (const p O).A n))
    refine ⟨k.val, fun φ => ?_⟩
    rw [ZMod.natCast_zmod_val, ← hk (constFun p O n φ)]
    exact congrArg (t.pt n) ((constFun p O n).symm_apply_apply φ).symm
  choose k hk using h1
  have h2 : ∀ n, ((k (n + 1) : ℕ) : ZMod (p ^ n)) = k n := fun n => by
    have h := t.pt_mulP n ((constFun p O n).symm (Pi.single (k n : ZMod (p ^ n)) 1))
    rw [hk, hk, constFun_mulP, AlgEquiv.apply_symm_apply, Pi.single_eq_same] at h
    by_contra hne
    rw [Pi.single_eq_of_ne hne] at h
    exact zero_ne_one h
  have h3 : ∀ n, (p : ℤ) ^ n ∣ (k (n + 1) : ℤ) - k n := fun n => by
    rw [← Nat.cast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast,
      Int.cast_natCast, h2, sub_self]
  refine ⟨PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun n => (k n : ℤ)) p h3),
    TateOver.ext (funext fun n => AlgHom.ext fun φ => ?_)⟩
  rw [LinearMap.toSpanSingleton_apply, smul_constGen_pt,
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => (k n : ℤ)) p h3 n, Int.cast_natCast, hk]

theorem toSpanSingleton_constGen_bijective
    (hO : ∀ e : O, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Function.Bijective (LinearMap.toSpanSingleton ℤ_[p] _ (constGen p O)) :=
  ⟨toSpanSingleton_constGen_injective p O, toSpanSingleton_constGen_surjective p O hO⟩

end PDivGroup

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopMulDescendedSubmoduleOfUnitCocycleEqTopStatement
section
open TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_mul_descendedSubmoduleOfUnitCocycle_eq_top : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] (u : (B ⊗[A] B)ˣ), UCoc A B u → (⊤ : Submodule A B) * descMod A B u = ⊤ := by
  first | exact @GlobalTheory.DescTop.top_mul_descMod_eq_top | exact GlobalTheory.DescTop.top_mul_descMod_eq_top | (intros; apply GlobalTheory.DescTop.top_mul_descMod_eq_top; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointRowsSumEqDivisorSeries
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.RowsSummed

theorem norm_ch (N : ℕ) (j : ZMod N) : ‖ch N j‖ = 1 := by
  unfold ch
  rw [Complex.norm_exp]
  simp [Complex.div_re]

theorem norm_q_lt (N : ℕ) [NeZero N] (τ : ℍ) :
    ‖Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N)‖ < 1 := by
  rw [Complex.norm_exp, show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm, Real.exp_lt_exp]
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hτ := τ.im_pos
  have : ((2 * (Real.pi : ℂ) * Complex.I) * τ / N).re = -(2 * Real.pi * τ.im) / N := by
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
    field_simp
  rw [this]
  apply div_neg_of_neg_of_pos _ hN
  have := Real.pi_pos
  nlinarith

theorem main : ∀ (N : ℕ) [NeZero N] (e : ℕ) (τ : ℍ) (x : Fin 2 → ZMod N) (S : ℂ), 1 ≤ e → HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (tors N τ x + n * (τ : ℂ) + m) ^ (e + 1)) S → ∃ T : ℂ, HasSum (fun k : ℕ => cSum N e ((-1) ^ (e + 1)) x k * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ k) T ∧ S = (if x 0 = 0 then ∑' m : ℤ, 1 / ((((x 1).val : ℂ)) / N + m) ^ (e + 1) else 0) + (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ) * T := by
  intro N _ e τ x S he hS
  set q : ℂ := Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) with hq
  set K : ℂ := (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ)
  set R : ℤ → ℂ := fun k => ∑' m : ℤ, 1 / (((k : ℂ) * τ + ((x 1).val : ℂ)) / N + m) ^ (e + 1) with hR
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hfR : (fun n : ℤ => ∑' m : ℤ, 1 / (tors N τ x + n * (τ : ℂ) + m) ^ (e + 1)) =
      fun n : ℤ => R (((x 0).val : ℤ) + n * N) := by
    funext n
    simp only [hR]
    congr 1
    funext m
    congr 3
    unfold tors
    push_cast
    field_simp
    ring
  rw [hfR] at hS
  have hsplit := GlobalTheory.T.tsum_residueClass_split_by_sign N (x 0) R hS.summable
  let c₁ : ℕ → ℕ → ℂ := fun d m => if ((d : ℕ) : ZMod N) = x 0 then ch N ((m : ZMod N) * x 1) else 0
  let c₂ : ℕ → ℕ → ℂ := fun d m => if ((d : ℕ) : ZMod N) = -x 0 then ch N (-((m : ZMod N) * x 1)) else 0
  have hq1 : ‖q‖ < 1 := norm_q_lt N τ
  have hc₁ : ∀ d m, ‖c₁ d m‖ ≤ 1 := by
    intro d m
    simp only [c₁]
    split_ifs
    · rw [norm_ch]
    · simp
  have hc₂ : ∀ d m, ‖c₂ d m‖ ≤ 1 := by
    intro d m
    simp only [c₂]
    split_ifs
    · rw [norm_ch]
    · simp
  have h₁ := GlobalTheory.T.hasSum_lambert_double_series_divisors e q c₁ hq1 hc₁
  have h₂ := GlobalTheory.T.hasSum_lambert_double_series_divisors e q c₂ hq1 hc₂
  set T₁ := ∑' d : ℕ+, ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c₁ d m * q ^ ((d : ℕ) * (m : ℕ))
  set T₂ := ∑' d : ℕ+, ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c₂ d m * q ^ ((d : ℕ) * (m : ℕ))
  refine ⟨T₁ + (-1) ^ (e + 1) * T₂, ?_, ?_⟩
  · have h := h₁.add (h₂.mul_left ((-1) ^ (e + 1)))
    convert h using 1
    funext k
    simp only [cSum, c₁, c₂]
    rw [show ∀ A B C D : ℂ, A * D + C * (B * D) = (A + C * B) * D from fun A B C D => by ring]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  · rw [← hS.tsum_eq, hsplit]
    have hpos : ∀ d : ℕ+, (if ((d : ℕ) : ZMod N) = x 0 then R ((d : ℕ) : ℤ) else 0) =
        K * ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c₁ d m * q ^ ((d : ℕ) * (m : ℕ)) := by
      intro d
      simp only [c₁]
      split_ifs with hd
      · have := (GlobalTheory.T.torsionPoint_rowSum_eq_qExpansion_series N e τ (x 1) d he).1
        simp only [hR]
        push_cast
        rw [this]
      · simp
    have hneg : ∀ d : ℕ+, (if ((d : ℕ) : ZMod N) = -x 0 then R (-((d : ℕ) : ℤ)) else 0) =
        K * ((-1) ^ (e + 1) * ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c₂ d m * q ^ ((d : ℕ) * (m : ℕ))) := by
      intro d
      simp only [c₂]
      split_ifs with hd
      · have := (GlobalTheory.T.torsionPoint_rowSum_eq_qExpansion_series N e τ (x 1) d he).2
        simp only [hR]
        push_cast
        rw [this]
      · simp
    rw [tsum_congr hpos, tsum_congr hneg, tsum_mul_left, tsum_mul_left, tsum_mul_left]
    have h0 : R 0 = ∑' m : ℤ, 1 / ((((x 1).val : ℂ)) / N + m) ^ (e + 1) := by
      simp [hR]
    rw [h0]
    ring

end GlobalTheory.WpFam.RowsSummed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorBaseChangeZmodStatement
section
open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsor_base_change_zmod : ∀ (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ) (D : Type) [CommRing D]
    [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D)), 0 < q →
    GlobalTheory.LocAcyc.IsZModTorsor U D q act →
    ∃ actB : Multiplicative (ZMod q) →* (TensorProduct U B D ≃ₐ[B] TensorProduct U B D),
      GlobalTheory.LocAcyc.IsZModTorsor B (TensorProduct U B D) q actB := by
  first | exact @GlobalTheory.LocAcyc.exists_isZModTorsor_tensorBase | exact GlobalTheory.LocAcyc.exists_isZModTorsor_tensorBase | (intros; apply GlobalTheory.LocAcyc.exists_isZModTorsor_tensorBase <;> assumption)
end

