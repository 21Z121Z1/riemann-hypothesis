import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3400
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3399
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3398
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3386
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativesCoboundaryCoeffsMemMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3401
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3353
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0803
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0700
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsBasisVerticalDerivations
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3370
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3378

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageQuotientFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineOpen_preimage_quotientFibre : ∀ (X Z : Scheme.{0}) (p : Z ⟶ X) (U : X.affineOpens) (m : Ideal Γ(X, U.1)) (A : Scheme.{0}) (q : A ⟶ Sp (Γ(X, U.1) ⧸ m)) (ι : A ⟶ Z), IsPullback ι q p (spMap (Ideal.Quotient.mk m) ≫ chart U) → ∀ W : Z.Opens, IsAffineOpen W → W ≤ p ⁻¹ᵁ U.1 → IsAffineOpen (ι ⁻¹ᵁ W) := by
  first | exact @GlobalTheory.AffinePreimageFibre.isAffineOpen_preimage_fibre | exact GlobalTheory.AffinePreimageFibre.isAffineOpen_preimage_fibre | (intros; apply GlobalTheory.AffinePreimageFibre.isAffineOpen_preimage_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedSingletonGenericFibreOfMaximalAffineOpenStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_singleton_genericFibre_of_maximal_affineOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (mm : Ideal Γ(Y.X, U.1)), mm.IsMaximal → ∀ x : gen Y, genι Y x ∈ U.1 → (∀ f ∈ mm, genι Y x ∉ Y.X.basicOpen f) → IsClosed ({x} : Set (gen Y)) := by
  first | exact @GlobalTheory.LocReg.isClosed_singleton_gen | exact GlobalTheory.LocReg.isClosed_singleton_gen | (intros; apply GlobalTheory.LocReg.isClosed_singleton_gen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactOfLeAffineOpenToroidalModelStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_of_le_affineOpen_toroidalModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (W : Y.X.Opens), W ≤ U.1 → IsCompact (W : Set Y.X) := by
  first | exact @GlobalTheory.ModelQC.isCompact_of_le_affineOpen | exact GlobalTheory.ModelQC.isCompact_of_le_affineOpen | (intros; apply GlobalTheory.ModelQC.isCompact_of_le_affineOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHorizOfComm
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.TranslHoriz

theorem isHoriz_of_comm : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ A.left), IsGrpPullback B' A (spMap ρ) π₁ → IsGrpPullback B' A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) (_ : GrpObj A₀) (m₀ : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ (dl : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)), GlobalTheory.KS.LocDerK A₀.hom A.hom m₀ (fun r => (ρ r).snd) ⊤ dl → ∀ (s : 𝟙_ (Over (Sp R)) ⟶ A) (T₀ : A₀.left ⟶ A₀.left), T₀ ≫ m₀ = m₀ ≫ (lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left → T₀ ≫ A₀.hom = A₀.hom → (∀ (W : A.left.Opens) (f : Γ(A.left, W)), dl ((lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left ⁻¹ᵁ W) (((lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left.app W).hom f) = pbT T₀ (dl W f) (m₀ ⁻¹ᵁ ((lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left ⁻¹ᵁ W))) → ∀ x : Sp (DualNumber k) ⟶ B'.left, x ≫ B'.hom = 𝟙 _ → x ≫ π₁ = spMap ρ ≫ s.left → x ≫ π₂ = spMap (constHom ρ) ≫ s.left := by
  intro k _ R _ A _ hA ρ B' _ π₁ π₂ h₁ h₂ hcl A₀ _ m₀ hm₀ dl hdl s T₀ hT₀ hT₀h hcomm x hx hx1
  set fst := (TrivSqZeroExt.fstHom k k k).toRingHom with hfst
  set alg := algebraMap k (DualNumber k) with halg
  have e_fa : spMap fst ≫ spMap alg = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]; congr 1
  have e_c : spMap (constHom ρ) = spMap alg ≫ spMap (fst.comp ρ) := by
    simp only [spMap, constHom, ← Spec.map_comp]; rfl
  have e_r : spMap (fst.comp ρ) = spMap fst ≫ spMap ρ := by
    simp only [spMap, ← Spec.map_comp]; rfl
  have P₁ := h₁.1
  have P₂ := h₂.1
  have P₀ := hm₀.1
  have wr : π₂ ≫ A.hom = (B'.hom ≫ spMap alg) ≫ spMap (fst.comp ρ) := by
    rw [P₂.w, e_c, Category.assoc]
  let r : B'.left ⟶ A₀.left := P₀.lift π₂ (B'.hom ≫ spMap alg) wr
  have hr1 : r ≫ m₀ = π₂ := P₀.lift_fst _ _ _
  have hr2 : r ≫ A₀.hom = B'.hom ≫ spMap alg := P₀.lift_snd _ _ _
  have Pr : IsPullback r B'.hom A₀.hom (spMap alg) := by
    refine IsPullback.of_right ?_ hr2 P₀
    rw [hr1, ← e_c]; exact P₂
  have wj : m₀ ≫ A.hom = (A₀.hom ≫ spMap fst) ≫ spMap (constHom ρ) := by
    rw [P₀.w, Category.assoc, e_c, ← Category.assoc (spMap fst), e_fa, Category.id_comp]
  let j : A₀.left ⟶ B'.left := P₂.lift m₀ (A₀.hom ≫ spMap fst) wj
  have hj1 : j ≫ π₂ = m₀ := P₂.lift_fst _ _ _
  have hj2 : j ≫ B'.hom = A₀.hom ≫ spMap fst := P₂.lift_snd _ _ _
  have hjr : j ≫ r = 𝟙 _ := P₀.hom_ext (by rw [Category.assoc, hr1, hj1, Category.id_comp])
    (by rw [Category.assoc, hr2, ← Category.assoc, hj2, Category.assoc, e_fa, Category.comp_id, Category.id_comp])
  have hjπ₁ : j ≫ π₁ = m₀ := by rw [hcl A₀.left j A₀.hom hj2, hj1]
  obtain ⟨-, Pj, -⟩ := GlobalTheory.ConstThickening.structure_dualNumber k A₀.left B'.left A₀.hom B'.hom r j Pr hjr hj2
  have hjs : Surjective j :=
    MorphismProperty.of_isPullback (P := @Surjective) Pj.flip GlobalTheory.ConstThickening.surjective_spMap_fst
  have hm : m₀ ≫ A.hom = A₀.hom ≫ spMap fst ≫ spMap ρ := by rw [P₀.w, e_r]
  obtain ⟨Φ, hΦj, hΦp, hΦ⟩ := GlobalTheory.KS.DerMorK.exists_hom_of_derivation k A₀.left B'.left A₀.hom B'.hom r j Pr hjr hj2
    R ρ A.left A.hom m₀ dl hm hdl
  have hb : ∀ y, Φ y = m₀ (r y) := by
    intro y
    obtain ⟨y₀, rfl⟩ := hjs.surj y
    show (j ≫ Φ) y₀ = (j ≫ r ≫ m₀) y₀
    rw [hΦj, ← Category.assoc, hjr, Category.id_comp]
  have wT : (r ≫ T₀) ≫ A₀.hom = B'.hom ≫ spMap alg := by rw [Category.assoc, hT₀h, hr2]
  let TB : B'.left ⟶ B'.left := Pr.lift (r ≫ T₀) B'.hom wT
  have hTB1 : TB ≫ r = r ≫ T₀ := Pr.lift_fst _ _ _
  have hTB2 : TB ≫ B'.hom = B'.hom := Pr.lift_snd _ _ _
  have hcΦ : TB ≫ Φ = Φ ≫ (lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left :=
    GlobalTheory.T.firstOrderLift_derivation_comm_translations k A₀.left B'.left A.left m₀ B'.hom r dl Φ hb hΦ _ T₀ TB hT₀ hTB1 hTB2 hcomm
  let α : B'.left ⟶ B'.left := P₁.lift Φ B'.hom hΦp
  have hα1 : α ≫ π₁ = Φ := P₁.lift_fst _ _ _
  have hα2 : α ≫ B'.hom = B'.hom := P₁.lift_snd _ _ _
  have hjα : j ≫ α = j := P₁.hom_ext (by rw [Category.assoc, hα1, hΦj, hjπ₁]) (by rw [Category.assoc, hα2])
  let αo : B' ⟶ B' := Over.homMk α hα2
  have hB' : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h₁
  set w : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B' := η[B'] ≫ αo with hw
  have hαo : αo = lift (toUnit B' ≫ w) (𝟙 B') ≫ μ[B'] := GlobalTheory.T.abelianScheme_dualNumber_endo_eq_translation k B' hB' αo (fun Z z y hz => by
    change z ≫ α = z
    rw [← Pj.lift_fst z y hz, Category.assoc, hjα])
  let xo : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B' := Over.homMk x hx
  have wσ : (spMap (constHom ρ) ≫ s.left) ≫ A.hom = 𝟙 _ ≫ spMap (constHom ρ) := by
    rw [Category.assoc, Over.w s, Category.id_comp]; rfl
  let σ : Sp (DualNumber k) ⟶ B'.left := P₂.lift (spMap (constHom ρ) ≫ s.left) (𝟙 _) wσ
  have hσ1 : σ ≫ π₂ = spMap (constHom ρ) ≫ s.left := P₂.lift_fst _ _ _
  have hσ2 : σ ≫ B'.hom = 𝟙 _ := P₂.lift_snd _ _ _
  let σo : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B' := Over.homMk σ hσ2
  have tx := GlobalTheory.T.groupPullback_translation_comp_eq B' A (spMap ρ) π₁ h₁ xo s hx1
  have tσ := GlobalTheory.T.groupPullback_translation_comp_eq B' A (spMap (constHom ρ)) π₂ h₂ σo s hσ1
  have hTBσ : TB = (lift (toUnit B' ≫ σo) (𝟙 B') ≫ μ[B']).left := by
    refine P₂.hom_ext ?_ ?_
    · rw [tσ, ← hr1, ← Category.assoc, hTB1, Category.assoc, hT₀, ← Category.assoc]
    · rw [hTB2, Over.w]
  have hcα : αo ≫ (lift (toUnit B' ≫ xo) (𝟙 B') ≫ μ[B']) = (lift (toUnit B' ≫ σo) (𝟙 B') ≫ μ[B']) ≫ αo := by
    apply Over.OverMorphism.ext
    refine P₁.hom_ext ?_ ?_
    · show α ≫ (lift (toUnit B' ≫ xo) (𝟙 B') ≫ μ[B']).left ≫ π₁ =
        (lift (toUnit B' ≫ σo) (𝟙 B') ≫ μ[B']).left ≫ α ≫ π₁
      rw [tx, ← Category.assoc, hα1, ← hcΦ, hTBσ]
    · simp only [Over.comp_left, Category.assoc, Over.w]
  haveI : IsCommMonObj B' := hB'.comm
  have hτ : ∀ (u y : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B'), y ≫ (lift (toUnit B' ≫ u) (𝟙 B') ≫ μ[B']) = u * y := by
    intro u y
    rw [← Category.assoc, comp_lift, ← Category.assoc, toUnit_unique (y ≫ toUnit B') (𝟙 _), Category.id_comp,
      Category.comp_id, ← Hom.mul_def]
  have h1 : (η[B'] : 𝟙_ _ ⟶ B') = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have e1 : η[B'] ≫ αo ≫ (lift (toUnit B' ≫ xo) (𝟙 B') ≫ μ[B']) = xo * w := by
    rw [← Category.assoc, ← hw, hτ]
  have e2 : η[B'] ≫ (lift (toUnit B' ≫ σo) (𝟙 B') ≫ μ[B']) ≫ αo = w * σo := by
    rw [← Category.assoc, hτ, h1, _root_.mul_one]
    nth_rewrite 1 [hαo]
    rw [hτ]
  have key : xo * w = w * σo := by
    rw [← e1, ← e2]
    exact congrArg (η[B'] ≫ ·) hcα
  have hxσ : xo = σo := by
    rw [_root_.mul_comm w σo] at key
    exact _root_.mul_right_cancel key
  have : x = σ := congrArg Over.Hom.left hxσ
  rw [this, hσ1]

end GlobalTheory.TranslHoriz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInvariantFieldDualNumberOfIsInvariantTangentVeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isInvariantField_dualNumber_of_isInvariant_tangentVector : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (v : TanM (𝟙 (Sp K)) A) (u : epsR K ⟶ A) (dd : Fld A.left), u.left = (tv v).left → IsTangent u → IsInv A v dd → GlobalTheory.KS.IsInvDer u dd := by
  first | exact @GlobalTheory.InvDerBridge.isInvDer_of_isInv | exact GlobalTheory.InvDerBridge.isInvDer_of_isInv | (intros; apply GlobalTheory.InvDerBridge.isInvDer_of_isInv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoIsogenyOmegaAndDualSurjective
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu

section Corner

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

theorem comp_proj_eq_of_comp_eq_zero {X Y Y₀ Y₁ : PDivGroup p k} (f : X ⟶ Y) (r₀ : Y ⟶ Y₀)
    (j₀ : Y₀ ⟶ Y) (r₁ : Y ⟶ Y₁) (j₁ : Y₁ ⟶ Y) (hY : r₀ ≫ j₀ + r₁ ≫ j₁ = 𝟙 Y)
    (h : f ≫ r₁ = 0) : f ≫ r₀ ≫ j₀ = f := by
  have h' : f ≫ r₁ ≫ j₁ = 0 := by rw [← Category.assoc, h, Limits.zero_comp]
  calc f ≫ r₀ ≫ j₀ = f ≫ r₀ ≫ j₀ + f ≫ r₁ ≫ j₁ := by rw [h', add_zero]
    _ = f ≫ 𝟙 Y := by rw [← hY, Preadditive.comp_add]
    _ = f := Category.comp_id f

theorem proj_comp_eq_of_comp_eq_zero {X X₀ X₁ Y : PDivGroup p k} (f : X ⟶ Y) (π₀ : X ⟶ X₀)
    (i₀ : X₀ ⟶ X) (π₁ : X ⟶ X₁) (i₁ : X₁ ⟶ X) (hX : π₀ ≫ i₀ + π₁ ≫ i₁ = 𝟙 X)
    (h : i₀ ≫ f = 0) : π₁ ≫ i₁ ≫ f = f := by
  have h' : π₀ ≫ i₀ ≫ f = 0 := by rw [h, Limits.comp_zero]
  calc π₁ ≫ i₁ ≫ f = π₀ ≫ i₀ ≫ f + π₁ ≫ i₁ ≫ f := by rw [h', zero_add]
    _ = 𝟙 X ≫ f := by rw [← hX, Preadditive.add_comp, Category.assoc, Category.assoc]
    _ = f := Category.id_comp f

theorem isIsog_corner {G H G' H' : PDivGroup p k} (q : G ⟶ H) (hq : IsIsog q) (i : G' ⟶ G)
    (π : G ⟶ G') (j : H' ⟶ H) (r : H ⟶ H') (hiπ : i ≫ π = 𝟙 G') (hjr : j ≫ r = 𝟙 H')
    (hq' : i ≫ q ≫ r ≫ j = i ≫ q) (hg : ∀ g : H ⟶ G, j ≫ g ≫ π ≫ i = j ≫ g) :
    IsIsog (i ≫ q ≫ r) := by
  obtain ⟨n, g, h1, h2⟩ := hq
  refine ⟨n, j ≫ g ≫ π, ?_, ?_⟩
  · calc (i ≫ q ≫ r) ≫ j ≫ g ≫ π = (i ≫ q ≫ r ≫ j) ≫ g ≫ π := by
          simp only [Category.assoc]
      _ = i ≫ (q ≫ g) ≫ π := by rw [hq']; simp only [Category.assoc]
      _ = _ := by rw [h1, Linear.smul_comp, Linear.comp_smul, Category.id_comp, hiπ]
  · calc (j ≫ g ≫ π) ≫ i ≫ q ≫ r = (j ≫ g ≫ π ≫ i) ≫ q ≫ r := by
          simp only [Category.assoc]
      _ = j ≫ (g ≫ q) ≫ r := by rw [hg g]; simp only [Category.assoc]
      _ = _ := by rw [h2, Linear.smul_comp, Linear.comp_smul, Category.id_comp, hjr]

theorem omegaMap_corner_surjective {G H G' H' : PDivGroup p k} (q : G ⟶ H)
    (hs : Function.Surjective (omegaMap G H q)) (i : G' ⟶ G) (π : G ⟶ G') (j : H' ⟶ H)
    (r : H ⟶ H') (hiπ : i ≫ π = 𝟙 G') (hq' : i ≫ q ≫ r ≫ j = i ≫ q) :
    Function.Surjective (omegaMap G' H' (i ≫ q ≫ r)) := by
  intro w
  obtain ⟨v, hv⟩ := hs (omegaMap G G' π w)
  refine ⟨omegaMap H' H j v, ?_⟩
  have e1 : omegaMap G' H' (i ≫ q ≫ r) (omegaMap H' H j v) = omegaMap G' H (i ≫ q) v := by
    rw [← LinearMap.comp_apply, ← omegaMap_comp]
    simp only [Category.assoc]
    rw [hq']
  rw [e1, omegaMap_comp, LinearMap.comp_apply, hv, ← LinearMap.comp_apply, ← omegaMap_comp, hiπ,
    omegaMap_id, LinearMap.id_apply]

theorem isIsog_dualHom_of_isIsog {G H : PDivGroup p k} (f : G ⟶ H) (hf : IsIsog f) :
    IsIsog (dualHom G H f) := by
  obtain ⟨n, g, h1, h2⟩ := hf
  refine ⟨n, dualHom H G g, ?_, ?_⟩
  · rw [← dualHom_comp, h2, map_smul, dualHom_id]
  · rw [← dualHom_comp, h1, map_smul, dualHom_id]

theorem isIso_of_isIso_dualHom {G H : PDivGroup p k} (f : G ⟶ H) (h : IsIso (dualHom G H f)) :
    IsIso f := by
  obtain ⟨d, hd⟩ := (dualHom_bijective (G := H) (H := G)).2 (inv (dualHom G H f))
  refine ⟨⟨d, ?_, ?_⟩⟩
  · apply (dualHom_bijective (G := G) (H := G)).1
    rw [dualHom_comp, hd, IsIso.inv_hom_id, dualHom_id]
  · apply (dualHom_bijective (G := H) (H := H)).1
    rw [dualHom_comp, hd, IsIso.hom_inv_id, dualHom_id]

theorem isIso_of_isConn_of_omegaMap_surjective [CharP k p] {G H : PDivGroup p k} (f : G ⟶ H)
    (hG : G.IsConn) (hf : IsIsog f) (hs : Function.Surjective (omegaMap G H f)) : IsIso f := by
  have hsurj := GlobalTheory.T.app_surjective_of_omegaMap_surjective_connected p k G H f hG hs
  have hdeg : HasLogDeg f 0 := ⟨0, fun n _ => by
    rw [pow_zero]
    exact (GlobalTheory.T.bialgHom_surjective_iff_finrank_kernelQuotient_eq_one k _ _ _).1 (hsurj n)⟩
  exact ((GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).2.2.2 H f hf).1 hdeg

end Corner

theorem isIso_of_isIsog_of_omegaMap_surjective : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q →
    Function.Surjective (omegaMap G H q) →
    Function.Surjective (omegaMap H.dual G.dual (dualHom G H q)) → IsIso q := by
  intro p _ k _ _ _ G H q hq hs hsd
  obtain ⟨G₀, G₁, i₀, π₀, i₁, π₁, hG₀, hG₁, hi₀, hi₁, hG⟩ := GlobalTheory.T.exists_connected_etale_splitting_pDivGroup p k G
  obtain ⟨H₀, H₁, j₀, r₀, j₁, r₁, hH₀, hH₁, hj₀, hj₁, hH⟩ := GlobalTheory.T.exists_connected_etale_splitting_pDivGroup p k H
  have z : ∀ {X Y : PDivGroup p k}, X.IsConn → Y.IsEt → (∀ f : X ⟶ Y, f = 0) ∧ ∀ f : Y ⟶ X, f = 0 :=
    fun {X Y} hX hY => GlobalTheory.T.hom_eq_zero_of_isConn_of_isEt' p k X Y hX hY

  have c₀ : i₀ ≫ q ≫ r₀ ≫ j₀ = i₀ ≫ q := by
    simpa only [Category.assoc] using
      comp_proj_eq_of_comp_eq_zero (i₀ ≫ q) r₀ j₀ r₁ j₁ hH ((z hG₀ hH₁).1 _)
  have c₁ : i₁ ≫ q ≫ r₁ ≫ j₁ = i₁ ≫ q := by
    have hH' : r₁ ≫ j₁ + r₀ ≫ j₀ = 𝟙 H := by rw [add_comm, hH]
    simpa only [Category.assoc] using
      comp_proj_eq_of_comp_eq_zero (i₁ ≫ q) r₁ j₁ r₀ j₀ hH' ((z hH₀ hG₁).2 _)
  have g₀ : ∀ g : H ⟶ G, j₀ ≫ g ≫ π₀ ≫ i₀ = j₀ ≫ g := fun g => by
    simpa only [Category.assoc] using
      comp_proj_eq_of_comp_eq_zero (j₀ ≫ g) π₀ i₀ π₁ i₁ hG ((z hH₀ hG₁).1 _)
  have g₁ : ∀ g : H ⟶ G, j₁ ≫ g ≫ π₁ ≫ i₁ = j₁ ≫ g := fun g => by
    have hG' : π₁ ≫ i₁ + π₀ ≫ i₀ = 𝟙 G := by rw [add_comm, hG]
    simpa only [Category.assoc] using
      comp_proj_eq_of_comp_eq_zero (j₁ ≫ g) π₁ i₁ π₀ i₀ hG' ((z hG₀ hH₁).2 _)

  have ha : IsIso (i₀ ≫ q ≫ r₀) :=
    isIso_of_isConn_of_omegaMap_surjective _ hG₀ (isIsog_corner q hq i₀ π₀ j₀ r₀ hi₀ hj₀ c₀ g₀)
      (omegaMap_corner_surjective q hs i₀ π₀ j₀ r₀ hi₀ c₀)

  have hb : IsIso (i₁ ≫ q ≫ r₁) := by
    apply isIso_of_isIso_dualHom
    have hdb : dualHom G₁ H₁ (i₁ ≫ q ≫ r₁) =
        dualHom H H₁ r₁ ≫ dualHom G H q ≫ dualHom G₁ G i₁ := by
      rw [dualHom_comp, dualHom_comp, Category.assoc]
    have hrj : dualHom H H₁ r₁ ≫ dualHom H₁ H j₁ = 𝟙 H₁.dual := by
      rw [← dualHom_comp, hj₁, dualHom_id]
    have hq'd : dualHom H H₁ r₁ ≫ dualHom G H q ≫ dualHom G₁ G i₁ ≫ dualHom G G₁ π₁ =
        dualHom H H₁ r₁ ≫ dualHom G H q := by
      have e : π₁ ≫ i₁ ≫ q ≫ r₁ = q ≫ r₁ :=
        proj_comp_eq_of_comp_eq_zero (q ≫ r₁) π₀ i₀ π₁ i₁ hG
          (by rw [← Category.assoc]; exact (z hG₀ hH₁).1 _)
      have e' := congrArg (dualHom G H₁) e
      simp only [dualHom_comp, Category.assoc] at e'
      exact e'
    have hs' : Function.Surjective (omegaMap H₁.dual G₁.dual (dualHom G₁ H₁ (i₁ ≫ q ≫ r₁))) := by
      rw [hdb]
      exact omegaMap_corner_surjective (dualHom G H q) hsd (dualHom H H₁ r₁) (dualHom H₁ H j₁)
        (dualHom G G₁ π₁) (dualHom G₁ G i₁) hrj hq'd
    exact isIso_of_isConn_of_omegaMap_surjective _ (GlobalTheory.T.dual_isConn_of_isEt_pDivGroup p k H₁ hH₁)
      (isIsog_dualHom_of_isIsog _ (isIsog_corner q hq i₁ π₁ j₁ r₁ hi₁ hj₁ c₁ g₁)) hs'

  have hqd : q = π₀ ≫ (i₀ ≫ q ≫ r₀) ≫ j₀ + π₁ ≫ (i₁ ≫ q ≫ r₁) ≫ j₁ := by
    simp only [Category.assoc, c₀, c₁]
    rw [← Category.assoc π₀, ← Category.assoc π₁, ← Preadditive.add_comp, hG, Category.id_comp]
  have hj01 : j₀ ≫ r₁ = 0 := (z hH₀ hH₁).1 _
  have hj10 : j₁ ≫ r₀ = 0 := (z hH₀ hH₁).2 _
  have hi01 : i₀ ≫ π₁ = 0 := (z hG₀ hG₁).1 _
  have hi10 : i₁ ≫ π₀ = 0 := (z hG₀ hG₁).2 _
  generalize i₀ ≫ q ≫ r₀ = a at ha hqd
  generalize i₁ ≫ q ≫ r₁ = b at hb hqd
  subst hqd
  refine ⟨⟨r₀ ≫ inv a ≫ i₀ + r₁ ≫ inv b ≫ i₁, ?_, ?_⟩⟩
  · simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, reassoc_of% hj₀,
      reassoc_of% hj₁, reassoc_of% hj01, reassoc_of% hj10, Limits.zero_comp, Limits.comp_zero,
      add_zero, zero_add, IsIso.hom_inv_id_assoc]
    exact hG
  · simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, reassoc_of% hi₀,
      reassoc_of% hi₁, reassoc_of% hi01, reassoc_of% hi10, Limits.zero_comp, Limits.comp_zero,
      add_zero, zero_add, IsIso.inv_hom_id_assoc]
    exact hH

end GlobalTheory.Dieu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerOfCohomologousCocycleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKodairaSpencer_of_cohomologous_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → ∀ (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)) (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (a : ∀ i, Γ(t.G.left, W i)ˣ) (u : ∀ i i', Γ(t.G.left, W i ⊓ W i')ˣ), ⨆ i, W i = t.G.hom ⁻¹ᵁ (U.1 ⊓ V) → (∀ i, IsField (W i) (d i)) → (∀ i (h : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), d i (W i) ((t.G.hom.appLE U.1 (W i) h).hom r) = (t.G.hom.appLE U.1 (W i) h).hom (D r)) → (∀ i i', (u i i').val * resG t.G.left (inf_le_right : W i ⊓ W i' ≤ W i') (a i').val = resG t.G.left (inf_le_left : W i ⊓ W i' ≤ W i) (a i).val * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) → (∀ (i i' : J) (O : t.G.left.Opens), O ≤ W i ⊓ W i' → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ b, IsTranslate t φ g₀ (v b) (w b)) → valR g₀ O (d i O f - d i' O f) = ∑ b, ∑ b', φ (Θ b b') * ((valR (w b') (W i ⊓ W i') (u i i').val).snd * valR g₀ (W i ⊓ W i') (u i i')⁻¹.val) * (valR (w b) O f).snd) → IsKS t V U v D Θ := by
  first | exact @GlobalTheory.LogKSCoh.isKS_of_cohomologous | exact GlobalTheory.LogKSCoh.isKS_of_cohomologous | (intros; apply GlobalTheory.LogKSCoh.isKS_of_cohomologous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieBasisDualPointsOfTangentModuleBasisStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLieBasis_dualPoints_of_tangentModule_basis : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ} (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)), IsLieBasis (fun a => GlobalTheory.VertCoeffRing.tvE (v a)) := by
  first | exact @GlobalTheory.VertCoeffRing.isLieBasis_tvE | exact GlobalTheory.VertCoeffRing.isLieBasis_tvE | (intros; apply GlobalTheory.VertCoeffRing.isLieBasis_tvE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenEigenRankLevelSetIntegersActionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_eigenRank_levelSet_integersAction : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (F : IntermediateField ℚ ℂ) (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) (R : Type) [CommRing R] (iF : F →+* R) (n : ℕ) (A : 𝓞 E → Matrix (Fin n) (Fin n) R), A 1 = 1 → (∀ a b, A (a + b) = A a + A b) → (∀ a b, A (a * b) = A a * A b) → ∀ (τ : E →+* ℂ) (N : ℕ), IsOpen {𝔭 : PrimeSpectrum R | GlobalTheory.BalProj.eigRank (algebraMap R 𝔭.asIdeal.ResidueField) A (GlobalTheory.BalProj.embR F hF iF τ) = N} := by
  first | exact @GlobalTheory.BalProjOpen.isOpen_eigRank_eq | exact GlobalTheory.BalProjOpen.isOpen_eigRank_eq | (intros; apply GlobalTheory.BalProjOpen.isOpen_eigRank_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerfectPairOfGeometricFibresStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPerfectPair_of_geometric_fibres : ∀ (R : Type) [CommRing R] (M N : Type 1) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N] (φ : Module.Dual R M →ₗ[R] Module.Dual R N →ₗ[R] R), (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω], ∃ (M' N' : Type 1) (_ : AddCommGroup M') (_ : Module Ω M') (_ : AddCommGroup N') (_ : Module Ω N') (f : M →ₛₗ[algebraMap R Ω] M') (f' : N →ₛₗ[algebraMap R Ω] N') (φ' : Module.Dual Ω M' →ₗ[Ω] Module.Dual Ω N' →ₗ[Ω] Ω), Function.Bijective (liftSemi f) ∧ Function.Bijective (liftSemi f') ∧ φ'.IsPerfPair ∧ ∀ (x : Module.Dual R M) (x' : Module.Dual Ω M') (y : Module.Dual R N) (y' : Module.Dual Ω N'), (∀ c, x' (f c) = algebraMap R Ω (x c)) → (∀ c, y' (f' c) = algebraMap R Ω (y c)) → φ' x' y' = algebraMap R Ω (φ x y)) → φ.IsPerfPair := by
  first | exact @GlobalTheory.PairFibres.isPerfPair_of_fibres₂ | exact GlobalTheory.PairFibres.isPerfPair_of_fibres₂ | (intros; apply GlobalTheory.PairFibres.isPerfPair_of_fibres₂ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudFourierTermSubSmulStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRaynaudFourierTerm_sub_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (k : ℕ) (α : Q.X) (σ σ' : Q.SecB k α) (τ τ' : SecM Y.q.left Q.P.L k) (e : R), IsTerm Y k α σ τ → IsTerm Y k α σ' τ' → IsTerm Y k α (σ' - constFn Q.P.A.hom ⊤ e • σ) (τ' - constFn Y.H.hom ⊤ e • τ) := by
  first | exact @GlobalTheory.HeatTermLin.isTerm_sub_smul | exact GlobalTheory.HeatTermLin.isTerm_sub_smul | (intros; apply GlobalTheory.HeatTermLin.isTerm_sub_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionMulStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRaynaudTorusWeightFunction_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Y.H.left.Opens) (χ χ' : Q.X) (f g : Γ(Y.H.left, V)), IsWt Y χ V f → IsWt Y χ' V g → IsWt Y (χ + χ') V (f * g) := by
  first | exact @GlobalTheory.Heat.WtMul.isWt_mul | exact GlobalTheory.Heat.WtMul.isWt_mul | (intros; apply GlobalTheory.Heat.WtMul.isWt_mul <;> assumption)
end

