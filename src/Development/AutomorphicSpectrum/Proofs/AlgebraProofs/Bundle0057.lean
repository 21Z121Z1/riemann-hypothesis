import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0055
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.OrbitTrans
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

namespace GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd

private theorem exists_hom_of_comp_snd_eq_comp_smul {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {M X Y : C} [MonObj M] [ModObj M X] (a b : Y ⟶ M ⊗ X)
    (h : b ≫ SemiCartesianMonoidalCategory.snd M X = a ≫ ModObj.smul (M := M) (X := X)) :
    ∃ r : Y ⟶ M ⊗ X, r ≫ SemiCartesianMonoidalCategory.snd M X = a ≫ SemiCartesianMonoidalCategory.snd M X ∧
      r ≫ ModObj.smul (M := M) (X := X) = b ≫ ModObj.smul (M := M) (X := X) := by
  have key : ∀ c : Y ⟶ M ⊗ X, c ≫ ModObj.smul (M := M) (X := X) =
      (c ≫ SemiCartesianMonoidalCategory.fst M X) • (c ≫ SemiCartesianMonoidalCategory.snd M X) := by
    intro c
    rw [CategoryTheory.Hom.smul_def, CartesianMonoidalCategory.lift_comp_fst_snd]
  refine ⟨CartesianMonoidalCategory.lift
    ((b ≫ SemiCartesianMonoidalCategory.fst M X) * (a ≫ SemiCartesianMonoidalCategory.fst M X))
    (a ≫ SemiCartesianMonoidalCategory.snd M X), CartesianMonoidalCategory.lift_snd _ _, ?_⟩
  rw [← CategoryTheory.Hom.smul_def, mul_smul, ← key a, ← h, ← key b]

theorem orbit_trans {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X] (x y w : X.left) :
    y ∈ orbit G X x → w ∈ orbit G X y → w ∈ orbit G X x := by
  simp only [GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.orbit, Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff]
  rintro ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := (ModObj.smul (M := G) (X := X)).left) (g := (SemiCartesianMonoidalCategory.snd G X).left)
    p q hq.symm
  have e₁ : (SemiCartesianMonoidalCategory.snd G X).left ≫ X.hom = (G ⊗ X).hom := Over.w _
  have e₂ : (ModObj.smul (M := G) (X := X)).left ≫ X.hom = (G ⊗ X).hom := Over.w _
  have hw : pullback.snd (ModObj.smul (M := G) (X := X)).left (SemiCartesianMonoidalCategory.snd G X).left ≫
      (G ⊗ X).hom =
      pullback.fst (ModObj.smul (M := G) (X := X)).left (SemiCartesianMonoidalCategory.snd G X).left ≫
      (G ⊗ X).hom := by
    rw [← e₂, pullback.condition_assoc, e₁, e₂]
  obtain ⟨r, hr₁, hr₂⟩ := exists_hom_of_comp_snd_eq_comp_smul
    (Y := Over.mk (pullback.fst (ModObj.smul (M := G) (X := X)).left
      (SemiCartesianMonoidalCategory.snd G X).left ≫ (G ⊗ X).hom))
    (Over.homMk (pullback.fst (ModObj.smul (M := G) (X := X)).left
      (SemiCartesianMonoidalCategory.snd G X).left) rfl)
    (Over.homMk (pullback.snd (ModObj.smul (M := G) (X := X)).left
      (SemiCartesianMonoidalCategory.snd G X).left) hw)
    (Over.OverMorphism.ext (by
      simp only [Over.comp_left, Over.homMk_left]
      exact pullback.condition.symm))
  refine ⟨r.left z, ?_, ?_⟩
  · have h₁ := congrArg Over.Hom.left hr₁
    simp only [Over.comp_left, Over.homMk_left] at h₁
    rw [← Scheme.Hom.comp_apply, h₁, Scheme.Hom.comp_apply, hz₁, hp]
  · have h₂ := congrArg Over.Hom.left hr₂
    simp only [Over.comp_left, Over.homMk_left] at h₂
    rw [← Scheme.Hom.comp_apply, h₂, Scheme.Hom.comp_apply, hz₂]

end GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqUnimodularDualStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sesq_unimodular_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∀ y, (∀ x, sesq D x y = 0) → y = 0) ∧ ∀ f : D.La →ₗ[𝓞 E] E, (∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ x, ∃ b : 𝓞 E, (δ : E) * f x = b) → ∃ y, ∀ x, f x = sesq D x y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.unimodularity_sesq | exact GlobalTheory.CompanionTheory.Ar.Fl.unimodularity_sesq | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.unimodularity_sesq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShearIsoActionProjection
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

noncomputable section

namespace GlobalTheory.CompanionTheory.FreeQuotProof

theorem action_eq_fst_smul_snd {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X] :
    (γ[G, X] : G ⊗ X ⟶ X) = (fst G X) • (snd G X) := by
  rw [CategoryTheory.Hom.smul_def, lift_fst_snd, Category.id_comp]

theorem exists_iso_swap_action_snd : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X], ∃ σ : G ⊗ X ⟶ G ⊗ X, IsIso σ ∧ σ ≫ snd G X = γ[G, X] ∧ σ ≫ γ[G, X] = snd G X := by
  intro S G X _ _
  have hγ : (γ[G, X] : G ⊗ X ⟶ X) = fst G X • snd G X := GlobalTheory.CompanionTheory.FreeQuotProof.action_eq_fst_smul_snd G X
  obtain ⟨σ, h₁, h₂⟩ : ∃ σ : G ⊗ X ⟶ G ⊗ X,
      σ ≫ snd G X = fst G X • snd G X ∧ σ ≫ fst G X = (fst G X)⁻¹ :=
    ⟨lift (fst G X)⁻¹ (fst G X • snd G X), lift_snd _ _, lift_fst _ _⟩
  have h₃ : σ ≫ (fst G X • snd G X) = snd G X := by
    rw [CategoryTheory.ModObj.comp_smul, h₂, h₁, inv_smul_smul]
  have h₄ : σ ≫ σ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, h₂, CategoryTheory.Hom.inv_def, ← Category.assoc, h₂,
        ← CategoryTheory.Hom.inv_def, inv_inv, Category.id_comp]
    · rw [Category.assoc, h₁, h₃, Category.id_comp]
  exact ⟨σ, ⟨σ, h₄, h₄⟩, by rw [hγ]; exact h₁, by rw [hγ]; exact h₃⟩

end GlobalTheory.CompanionTheory.FreeQuotProof
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupQuotientStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_quotient : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → ∀ c' c : R, idealX AA.carrier K t τ = Ideal.span {c'} → idealX AA.carrier K t (τ ^ p) = Ideal.span {c} → v (algebraMap R C c') ^ p < v (algebraMap R C c) → c ∈ idealD p AA.carrier K t (τ ^ p) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_quotient | exact GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_quotient | (intros; apply GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_quotient <;> assumption)
end

