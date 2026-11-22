import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerShapeDependsOnlyOnMatrices
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0123
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleSpecialFibreExtendedPrincipalPolarisatio
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdjointEndomorphismsCubeLBOfDenseFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open CechPic

theorem CechPic.lam_pull_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' T' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (c : Pic G.left) (x y : T' ⟶ G') :
    lam (pull φ c) x y = lam c (pushHom h T' x) (pushHom h T' y) := by
  rw [lam, lam, ← map_mul, ← map_one (pushHom h T')]
  simp only [← pull_comp]
  rfl

theorem adjoint_cubeLB_of_dense_fibres : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) [IsReduced S] (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (u v : A ⟶ A), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → IsMonHom u → IsMonHom v → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (G : Over (Sp K)) (_ : GrpObj G) (_ : IsCommMonObj G) (φ : G.left ⟶ A.left) (L' : LB G.left) (u' v' : G ⟶ G), p ∈ Set.range x ∧ IsGrpPullback G A x φ ∧ L'.IsLB ∧ LBIso L' (L.pull φ) ∧ u'.left ≫ φ = φ ≫ u.left ∧ v'.left ≫ φ = φ ≫ v.left ∧ LBIso (cubeLB G ![fst G G ≫ u', snd G G] L') (cubeLB G ![fst G G, snd G G ≫ v'] L')} → LBIso (cubeLB A ![fst A A ≫ u, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ v] L) := by
  intro hG S _ A _ _ L u v hA hL hamp hu hv hd
  have := hA.smooth
  have : IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  have hp : IsPullback (snd A A).left (fst A A).left A.hom A.hom :=
    (IsPullback.of_hasPullback A.hom A.hom).flip
  have h₁ : (cubeLB A ![fst A A ≫ u, snd A A] L).IsLB := LB.isLB_linComb hL _ _
  have h₂ : (cubeLB A ![fst A A, snd A A ≫ v] L).IsLB := LB.isLB_linComb hL _ _
  have hN := LB.isLB_div h₂ h₁
  refine GlobalTheory.T.seesaw_reduced_base_abelianScheme_of_dense_fibres hG S A L hA hL hamp A.left (A ⊗ A).left A.hom (snd A A).left (fst A A).left _ hp hN
    ((hd.preimage A.hom.isOpenMap).mono ?_) (lift (𝟙 A) (1 : A ⟶ A)).left ?_ ?_
  · rintro a ⟨K, _, x, G, _, _, φ, L', u', v', ⟨q, hq⟩, h, hL', hiso, hu', hv', H⟩
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback h.1 a q hq.symm
    let U : Over.mk ((G ⊗ G).hom ≫ x) ⟶ A ⊗ A := lift (pushHom h _ (fst G G)) (pushHom h _ (snd G G))
    have e₁ : U.left ≫ (fst A A).left = (fst G G).left ≫ φ :=
      congrArg (fun q => q.left) (lift_fst (pushHom h _ (fst G G)) (pushHom h _ (snd G G)))
    have e₂ : U.left ≫ (snd A A).left = (snd G G).left ≫ φ :=
      congrArg (fun q => q.left) (lift_snd (pushHom h _ (fst G G)) (pushHom h _ (snd G G)))
    have P : IsPullback U.left (fst G G).left (fst A A).left φ := by
      have B := (IsPullback.of_hasPullback G.hom G.hom).flip.paste_horiz h.1
      refine IsPullback.of_right ?_ e₁ hp
      rw [e₂, h.1.w]
      exact B
    have push : ∀ {w' : G ⟶ G} {w : A ⟶ A}, w'.left ≫ φ = φ ≫ w.left → ∀ y : G ⊗ G ⟶ G,
        pushHom h _ (y ≫ w') = pushHom h _ y ≫ w := fun hw y => Over.OverMorphism.ext (by
      show (y.left ≫ _) ≫ _ = (y.left ≫ _) ≫ _
      rw [Category.assoc, hw, Category.assoc])
    refine ⟨G.left.residueField z, inferInstance, G.left.fromSpecResidueField z ≫ φ,
      pullback (fst G G).left (G.left.fromSpecResidueField z), pullback.fst _ _ ≫ U.left,
      pullback.snd _ _, ⟨IsLocalRing.closedPoint (G.left.residueField z), ?_⟩,
      (IsPullback.of_hasPullback _ _).paste_horiz P, ?_⟩
    · rw [← hz]
      exact congrArg φ (Scheme.fromSpecResidueField_apply z _)
    · have h₁' : (cubeLB G ![fst G G ≫ u', snd G G] L').IsLB := LB.isLB_linComb hL' _ _
      have h₂' : (cubeLB G ![fst G G, snd G G ≫ v'] L').IsLB := LB.isLB_linComb hL' _ _
      have H' := (cls_eq_iff h₁' h₂').2 H
      rw [cls_cube_two hL', cls_cube_two hL', (cls_eq_iff hL' (pull_isLB hL φ)).2 hiso, cls_pull hL,
        lam_pull_of_isGrpPullback h, lam_pull_of_isGrpPullback h, push hu', push hv'] at H'
      have j : pull U.left (cls _ h₂ - cls _ h₁) = 0 := by
        rw [cls_cube_two hL, cls_cube_two hL, map_sub, pull_lam, pull_lam, lift_fst,
          lift_snd, lift_fst_assoc, lift_snd_assoc]
        exact sub_eq_zero.2 H'.symm
      refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
      rw [cls_pull hN, cls_div h₂ h₁]
      exact (pull_comp _ _ _).trans ((congrArg _ j).trans (map_zero _))
  · rw [← Over.comp_left, lift_fst, Over.id_left]
  · refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
    rw [cls_pull hN, cls_div h₂ h₁, cls_cube_two hL, cls_cube_two hL, map_sub, pull_lam, pull_lam, lift_fst,
      lift_snd, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp, lam_one_right, lam_one_right, sub_self]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionAbelianVariety
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem card_torsion_abelianVariety : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g N : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (N : k) ≠ 0 → Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ B // x ^ N = 1} = N ^ (2 * g) :=
  fun k _ _ B _ g N hB hg hN => GlobalTheory.abMulN_holds k B g N hB hg hN

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerShapeDependsOnlyOnMatricesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPower_shape_depends_only_on_matrices : Out.Laws → Out.Laws2 → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (c : SiegPre h k (b.ζ : o) s) (c' : SiegPre h k (b.ζ : o) s') (t : TObj g k J b s) (t' : TObj g k J b s'), 1 ≤ h → Nonempty S → c.Principal → c'.Principal → IsSharp W a bas t c → IsSharp W a bas t' c' → t.Shape Mat κ → t'.Shape Mat κ := by
  first | exact @GlobalTheory.SharpShape.shape_of_isSharp | exact GlobalTheory.SharpShape.shape_of_isSharp | (intros; apply GlobalTheory.SharpShape.shape_of_isSharp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasicOpenKTrivOfFibre
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.KTrivSpread

theorem exists_smul_eq_zero {R K J : Type} [CommRing R] [Field K] [Algebra R K] [AddCommGroup J] [Module R J]
    [Module.Finite R J] (h : Subsingleton (K ⊗[R] J)) : ∃ f : R, algebraMap R K f ≠ 0 ∧ ∀ m : J, f • m = 0 := by
  obtain ⟨p, hp₀⟩ : ∃ p : PrimeSpectrum R, ∀ r, r ∈ p.asIdeal ↔ algebraMap R K r = 0 :=
    ⟨⟨RingHom.ker (algebraMap R K), RingHom.ker_isPrime _⟩, fun _ => Iff.rfl⟩
  let l : p.asIdeal.ResidueField →+* K := Ideal.ResidueField.lift p.asIdeal (algebraMap R K) (fun r hr => (hp₀ r).1 hr)
    (fun r hr => (IsUnit.mk0 _ (fun e => hr ((hp₀ r).2 e))))
  letI : Algebra p.asIdeal.ResidueField K := l.toAlgebra
  have : IsScalarTower R p.asIdeal.ResidueField K := IsScalarTower.of_algebraMap_eq fun r =>
    (Ideal.ResidueField.lift_algebraMap _ _ _ _ r).symm
  have h₁ : Subsingleton (K ⊗[p.asIdeal.ResidueField] (p.asIdeal.ResidueField ⊗[R] J)) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField K K J).toEquiv.subsingleton
  have h₂ : Subsingleton (p.asIdeal.ResidueField ⊗[R] J) :=
    Module.FaithfullyFlat.lTensor_reflects_triviality p.asIdeal.ResidueField K _
  have h₃ : p ∉ Module.support R J := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct, not_nontrivial_iff_subsingleton]
    exact h₂
  rw [Module.mem_support_iff_of_finite, SetLike.not_le_iff_exists] at h₃
  obtain ⟨f, hf, hp⟩ := h₃
  exact ⟨f, fun e => hp ((hp₀ f).2 e), Module.mem_annihilator.1 hf⟩

theorem exists_mul_sub_eq_zero {R B K : Type} [CommRing R] [CommRing B] [Field K] (α : R →+* B) (hα : α.Finite)
    (σ : B →+* R) (hσ : ∀ r, σ (α r) = r) (x : R →+* K)
    (h : ∀ (C : Type) [CommRing C] (ψ : B →+* C) (κ : K →+* C), ψ.comp α = κ.comp x → ∀ b, ψ b = ψ (α (σ b))) :
    ∃ f : R, x f ≠ 0 ∧ ∀ b, α f * (b - α (σ b)) = 0 := by
  letI := α.toAlgebra
  letI := x.toAlgebra
  have : Module.Finite R B := hα
  let s : B →ₐ[R] R := { σ with commutes' := hσ }
  let P : B →ₗ[R] B := LinearMap.id - (Algebra.linearMap R B).comp s.toLinearMap
  have hP : ∀ b, P b = b - α (σ b) := fun b => rfl
  have hPP : ∀ b, P (P b) = P b := fun b => by
    rw [hP (P b), hP, map_sub, hσ, sub_self, map_zero, sub_zero]
  have h₀ : ∀ b, (1 : K) ⊗ₜ[R] P b = 0 := fun b => by
    have := h (K ⊗[R] B) (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).toRingHom
      Algebra.TensorProduct.includeLeftRingHom (RingHom.ext fun r =>
        ((Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B)).commutes r).trans rfl) b
    rw [hP, TensorProduct.tmul_sub, sub_eq_zero]
    exact this
  have h₁ : ∀ m : LinearMap.range P, (1 : K) ⊗ₜ[R] m = 0 := by
    rintro ⟨_, b, rfl⟩
    have := congrArg (P.rangeRestrict.lTensor K) (h₀ b)
    rw [map_zero, LinearMap.lTensor_tmul] at this
    rw [← this]
    congr 1
    exact Subtype.ext (hPP b).symm
  have h₂ : Subsingleton (K ⊗[R] LinearMap.range P) := by
    refine subsingleton_of_forall_eq 0 fun z => ?_
    induction z with
    | zero => rfl
    | tmul k m => rw [← _root_.mul_one k, ← smul_eq_mul, ← TensorProduct.smul_tmul', h₁, smul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  obtain ⟨f, hf, H⟩ := exists_smul_eq_zero h₂
  refine ⟨f, hf, fun b => ?_⟩
  have := congrArg Subtype.val (H ⟨P b, b, rfl⟩)
  rw [← hP]
  exact (Algebra.smul_def f (P b)).symm.trans this

theorem memKL_push {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
    {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left} (h : IsGrpPullback A' A f φ) (hL : L.IsLB)
    (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) {Z : Scheme.{0}} (t : Z ⟶ S') (x : Over.mk t ⟶ A')
    (hx : MemKL A' L' x) : MemKL A L (pushPt h.1.w x) := by
  obtain ⟨w, hw⟩ := hw
  replace hw := (isGen_iff w).1 hw
  intro p
  obtain ⟨V, hV, c, hc⟩ := hx p
  refine ⟨V, hV, ?_⟩
  let T : Over S := Over.mk (t ≫ f)
  let T₂ : Over S' := Over.mk ((fst T A).left ≫ t)
  have sq : (snd T A).left ≫ A.hom = ((fst T A).left ≫ t) ≫ f := pullback.condition.symm.trans (Category.assoc _ _ _).symm
  let a : T₂ ⟶ Over.mk t := Over.homMk (fst T A).left rfl
  let b : T₂ ⟶ A' := Over.homMk (h.1.lift _ _ sq) (h.1.lift_snd _ _ _)
  have hb : b.left ≫ φ = (snd T A).left := h.1.lift_fst _ _ _
  have k₁ : (lift a b).left ≫ (fst (Over.mk t) A').left = (fst T A).left := congrArg (fun q => q.left) (lift_fst a b)
  have k₂ : (lift a b).left ≫ (snd (Over.mk t) A').left ≫ φ = (snd T A).left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ φ) (lift_snd a b)).trans hb)
  have k₃ : (lift a b).left ≫ ((fst (Over.mk t) A' ≫ x) * snd (Over.mk t) A').left ≫ φ =
      ((fst T A ≫ pushPt h.1.w x) * snd T A).left := by
    have e : lift a b ≫ ((fst (Over.mk t) A' ≫ x) * snd (Over.mk t) A') = (a ≫ x) * b := by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
    let j : Over.mk (T₂.hom ≫ f) ⟶ T ⊗ A := Over.homMk (𝟙 _) ((Category.id_comp _).trans
      ((Over.w (snd T A)).symm.trans sq))
    have e₁ := h.2 T₂ (a ≫ x) b (j ≫ fst T A ≫ pushPt h.1.w x) (j ≫ snd T A)
      ((Category.id_comp _).trans (Category.assoc _ _ _).symm) ((Category.id_comp _).trans hb.symm)
    rw [← MonObj.comp_mul, ← e] at e₁
    exact (Category.assoc _ _ _).symm.trans (e₁.symm.trans (Category.id_comp _))
  obtain ⟨n, hn⟩ : ∃ n : ((fst T A).left ⁻¹ᵁ V).toScheme ⟶ ((fst (Over.mk t) A').left ⁻¹ᵁ V).toScheme,
      n ≫ ((fst (Over.mk t) A').left ⁻¹ᵁ V).ι = ((fst T A).left ⁻¹ᵁ V).ι ≫ (lift a b).left :=
    ⟨IsOpenImmersion.lift _ (((fst T A).left ⁻¹ᵁ V).ι ≫ (lift a b).left) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q y.1 ∈ V) k₁).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L' _ _ _) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up hw hL hL' c₁ h₁
  refine gen_chartPull (chartPullOut L _ _ _ _ fun k => ?_) _ (DVR.pullGen_isGen _ _ _ c₂ h₂ n)
  show n ≫ (_ ≫ _) ≫ φ = _
  rw [Category.assoc, ← Category.assoc n, hn, Category.assoc]
  fin_cases k
  exacts [congrArg (_ ≫ ·) k₃, congrArg (_ ≫ ·) k₂]

theorem exists_finite_rep (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (L : LB A.left)
    (hA : IsAbelianScheme A) (hL : L.IsLB) (ha : Out.RelAmple A L) :
    ∃ (Z : Over (Sp R)) (i : Z ⟶ A), IsClosedImmersion i.left ∧ IsFinite Z.hom ∧
      ∀ (T : Over (Sp R)) (x : T ⟶ A), MemKL A L x ↔ ∃ z : T ⟶ Z, z ≫ i = x := by
  have := hA.comm
  obtain ⟨d, -, n, s, hs⟩ := (Unif.relAmple_iff_veryAmpleBy R A L hL).1 ha
  have hp : AbLaw.IsProjBy A.hom := ⟨_, AbLaw.isLB_pw hL _, n, s, hs⟩
  obtain ⟨hO, -, hK⟩ := UU.TrivTwist.inK_iff_trivial_twist _ A L hL
  obtain ⟨Z, i, hi, hZ⟩ := _root_.GlobalTheory.UU.TwistKer.exists_closed_twist_kernel globalFns_holds R A hA hp L _ hL hO
  exact ⟨Z, i, hi, AmpleStabFinite.isFinite_of_relAmple globalFns_holds R A hA L _ hL hO ha Z i hi hZ,
    fun T x => (hK _ rfl T x).trans (hZ T x)⟩

theorem exists_kTriv_of_isUnit : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (K : Type) [Field K] (x : R →+* K) (A₀ : Over (Sp K)) [GrpObj A₀] (φ₀ : A₀.left ⟶ A.left), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → IsGrpPullback A₀ A (spMap x) φ₀ → Out.KTriv A₀ (L.pull φ₀) → ∃ f : R, x f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (A' : Over (Sp R')) [GrpObj A'] (π : A'.left ⟶ A.left), IsUnit (φ f) → IsGrpPullback A' A (spMap φ) π → Out.KTriv A' (L.pull π) := by
  intro R _ _ A _ L K _ x A₀ _ φ₀ hA hL ha h₀ hk
  obtain ⟨Z, i, hi, hfin, hZ⟩ := exists_finite_rep R A L hA hL ha
  have : IsAffine Z.left := isAffine_of_isAffineHom Z.hom
  let ε := Z.left.isoSpec
  obtain ⟨e, he⟩ := (hZ (𝟙_ _) 1).1 (memKL_one hL _)
  obtain ⟨α, hα⟩ := Spec.map_surjective (ε.inv ≫ Z.hom)
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (R := Γ(Z.left, ⊤)) (S := CommRingCat.of R) (e.left ≫ ε.hom)
  have hασ : α ≫ σ = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, hα, hσ, Category.assoc, Iso.hom_inv_id_assoc, Spec.map_id]
    exact Over.w e)
  have hαf : α.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hα]
    infer_instance
  have key : ∀ (C : Type) [CommRing C] (t : Sp C ⟶ Sp R) (z : Over.mk t ⟶ Z) (ψ : Γ(Z.left, ⊤) ⟶ CommRingCat.of C),
      Spec.map ψ = z.left ≫ ε.hom → (z ≫ i = 1 ↔ ψ = σ ≫ α ≫ ψ) := by
    intro C _ t z ψ hψ
    have e₁ : toUnit (Over.mk t) ≫ e ≫ i = 1 := by rw [he, MonObj.comp_one]
    have e₂ : Spec.map (σ ≫ α ≫ ψ) = (toUnit (Over.mk t) ≫ e).left ≫ ε.hom := by
      have e₃ : Spec.map (α ≫ ψ) = t := by
        rw [Spec.map_comp, hψ, hα, Category.assoc, Iso.hom_inv_id_assoc]
        exact Over.w z
      have e₄ : (toUnit (Over.mk t)).left = t := (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk t)))
      rw [Spec.map_comp, e₃, hσ, Over.comp_left, e₄]
      exact (Category.assoc _ _ _).symm
    have : Mono i := Over.mono_of_mono_left i
    rw [← e₁, ← Category.assoc, cancel_mono, ← Spec.map_injective.eq_iff, e₂, hψ, cancel_mono]
    exact ⟨fun h => by rw [h], Over.OverMorphism.ext⟩
  obtain ⟨f, hf, H⟩ := exists_mul_sub_eq_zero α.hom hαf σ.hom
    (fun r => congrArg (fun q => q.hom r) hασ) x (by
      intro C _ ψ κ hψ b
      let d : Sp C ⟶ Z.left := Spec.map (CommRingCat.ofHom ψ) ≫ ε.inv
      let t : Sp C ⟶ Sp K := spMap κ
      have hd : d ≫ Z.hom = t ≫ spMap x := by
        simp only [d, t, spMap, Category.assoc, ← hα, ← Spec.map_comp]
        congr 1
        exact CommRingCat.hom_ext hψ
      have hdi : (d ≫ i.left) ≫ A.hom = t ≫ spMap x := by
        rw [Category.assoc, Over.w i, hd]
      let y : Over.mk t ⟶ A₀ := Over.homMk (h₀.1.lift _ _ hdi) (h₀.1.lift_snd _ _ _)
      let z : Over.mk (t ≫ spMap x) ⟶ Z := Over.homMk d hd
      have hz : z ≫ i = pushPt h₀.1.w y := Over.OverMorphism.ext (h₀.1.lift_fst _ _ hdi).symm
      have hL₀ : (L.pull φ₀).IsLB := DVR.linComb_isLB _ hL _ _
      have hy : y = 1 := hk _ t y (memKL_of_push h₀ hL hL₀ (lbIso_self hL₀) y ((hZ _ _).2 ⟨z, hz⟩))
      have hy' : pushPt h₀.1.w y = 1 := (congrArg (pushHom h₀ (Over.mk t)) hy).trans (map_one _)
      have := (key C _ z (CommRingCat.ofHom ψ) (by
        show _ = (_ ≫ ε.inv) ≫ ε.hom
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id])).1 (hz.trans hy')
      exact congrArg (fun q => q.hom b) this)
  refine ⟨f, hf, fun R' _ φ A' _ π hu h C _ t y hy => ?_⟩
  have hL' : (L.pull π).IsLB := DVR.linComb_isLB _ hL _ _
  obtain ⟨z, hz⟩ := (hZ _ _).1 (memKL_push h hL hL' (lbIso_self hL') t y hy)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (R := Γ(Z.left, ⊤)) (S := CommRingCat.of C) (z.left ≫ ε.hom)
  obtain ⟨τ, rfl⟩ := Spec.map_surjective t
  have hc : α ≫ ψ = CommRingCat.ofHom φ ≫ τ := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_comp, hα, hψ, Category.assoc, Iso.hom_inv_id_assoc]
    exact Over.w z)
  have hu' : IsUnit (ψ.hom (α.hom f)) := by
    have : ψ.hom (α.hom f) = τ.hom (φ f) := congrArg (fun q => q.hom f) hc
    rw [this]
    exact hu.map _
  have h₁ : z ≫ i = 1 := (key C _ z ψ hψ).2 (CommRingCat.hom_ext (RingHom.ext fun b => by
    have := congrArg ψ.hom (H b)
    rw [map_mul, map_zero, hu'.mul_right_eq_zero, map_sub, sub_eq_zero] at this
    exact this))
  have inj : ∀ {T : Over (Sp R')} {u v : T ⟶ A'}, pushPt h.1.w u = pushPt h.1.w v → u = v := fun {T u v} e =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))
  exact inj ((hz.symm.trans h₁).trans (map_one (pushHom h (Over.mk (Spec.map τ)))).symm)

end GlobalTheory.KTrivSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGenSecNear
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.EmbLocal

open ReciprocityTheory.ChartRestriction.G.Out

variable {S : Scheme.{0}}

theorem exists_isGenSec_near (hS : SecBaseChangeAnySt) (P : PolAV S) (x : S) :
    ∃ V : S.Opens, x ∈ V ∧ ∀ (R : Type) [CommRing R] (q : Sp R ⟶ S), Set.range q ⊆ V →
      ∃ th, IsGenSec P.A P.L 1 (T := Over.mk q) th := by
  obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl x
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  let T : Over S := overRes (T := baseOver S) V
  have hT : T.hom = V.ι := Category.comp_id _
  haveI : IsOpenImmersion T.hom := by rw [hT]; exact inferInstanceAs (IsOpenImmersion V.ι)
  refine ⟨V, hV, fun R _ q hqV => ?_⟩
  obtain ⟨t, rfl⟩ : ∃ t : Spec (CommRingCat.of R) ⟶ T.left, t ≫ T.hom = q :=
    ⟨IsOpenImmersion.lift T.hom q (by rw [hT]; exact hqV.trans (Scheme.Opens.range_ι V).ge),
      IsOpenImmersion.lift_fac _ _ _⟩
  choose b' hb' using fun i =>
    PushInv.exists_pull P.A P.L (1 : ℕ) (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i)
  obtain ⟨-, hsp⟩ := hb R t b' hb'
  refine ⟨b' hq.default, fun s => ?_⟩
  rw [Set.range_unique] at hsp
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (hsp.ge (Submodule.mem_top (x := SecM.ofSec P.A s)))
  exact ⟨r, fun j => (congrArg (fun q => q.1 j) hr).symm⟩

theorem exists_mulPull (hG : GlobalFnsSt) (P : PolAV S) (k : ℕ) (T : Over S) :
    ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ k).left] ![(k : ℤ) ^ 2, -1]),
      α.IsGen := by
  obtain ⟨α₀, hα₀⟩ := (MulPull.mulPull_of_cube_of_symm AbLaw.CubeAssembly.cube_gen (exists_gen_negLB hG)).1 S P k
  have e₁ : (snd T P.A).left ≫ (mulA P.A k).left = (snd T P.A ^ k).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α, hα, -⟩ := exists_gen P.isLB (φ' := ![(snd T P.A).left, (snd T P.A ^ k).left])
    (ε' := ![(k : ℤ) ^ 2, -1])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ ((k : ℤ) ^ 2)) (Category.comp_id _)
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A k).left] ![(k : ℤ) ^ 2, -1] α₀ (snd T P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  exact ⟨α, hα⟩

theorem exists_symLift_near (hG : GlobalFnsSt) (P : PolAV S) {k : ℕ} (hk : Odd k) {T : Over S} (y : T ⟶ P.A)
    (hy : y ^ k = 1) (p : T.left) :
    ∃ V : T.left.Opens, p ∈ V ∧ ∀ (T' : Over S) (h : T' ⟶ T), Set.range h.left ⊆ V →
      ∃ θ : ThetaGrp P.A P.L k T', SymLift P.A P.L k k (h ≫ y) θ := by
  obtain ⟨V, hV, θ, hθ⟩ := ((symLift_odd hG
    (kerPow_of_square (AbSquare.square_of_cube AbLaw.CubeAssembly.cube_gen).1).2.2 (exists_gen_negLB hG)).1
      S P k hk T y hy).1 p
  refine ⟨V, hV, fun T' h hh => ?_⟩
  have hr : Set.range h.left ⊆ Set.range V.ι := hh.trans (Scheme.Opens.range_ι V).ge
  let l : T' ⟶ overRes V := Over.homMk (IsOpenImmersion.lift V.ι h.left hr) (by
    show IsOpenImmersion.lift V.ι h.left hr ≫ V.ι ≫ T.hom = T'.hom
    rw [IsOpenImmersion.lift_fac_assoc, Over.w h])
  have e : l ≫ overResι V = h := Over.OverMorphism.ext (IsOpenImmersion.lift_fac V.ι h.left hr)
  obtain ⟨θ', hθ'⟩ := GlobalLift.exists_symLift_pull P.isLB l hθ
  exact ⟨θ', by rw [← e, Category.assoc]; exact hθ'⟩

theorem exists_affine_nhds {R : Type} [CommRing R] (W : (Sp R).Opens) (p : Sp R) (hp : p ∈ W) :
    ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R'), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧
      Set.range (spMap φ) ⊆ W := by
  obtain ⟨_, ⟨r, rfl⟩, hr, hW⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (u := W.1) hp W.isOpen
  have e : Set.range (spMap (algebraMap R (Localization.Away r))) = (PrimeSpectrum.basicOpen r).1 :=
    PrimeSpectrum.localization_away_comap_range (R := R) (Localization.Away r) r
  refine ⟨Localization.Away r, inferInstance, algebraMap _ _, ?_, e.ge hr, e.le.trans hW⟩
  exact inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))))

theorem lab_pow {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o} (t : TObj g k J b s)
    (a : Ix g k) : t.lab a ^ k = 1 := by
  have := t.ab.comm
  rw [TObj.lab, linComb, List.prod_ofFn, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, t.torsion, one_pow]

end GlobalTheory.EmbLocal

namespace GlobalTheory

open EmbLocal

theorem exists_emb_locally : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S), Odd N' → m ∣ N' → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (σ : _), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ t.Emb m (Over.mk (spMap φ ≫ x)) σ := by
  intro hL hL2 o _ g N' J b S s t m R _ x hN hm p
  have hmo : Odd m := hN.of_dvd_nat hm
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero 2 hN.pos.ne'⟩
  let u : Over.mk x ⟶ Out.baseOver S := Over.homMk x (by simp)
  have hy : ∀ a, ((u ≫ t.lab a) ^ ((N' / m) ^ 2)) ^ (m ^ 2) = 1 := fun a => by
    rw [← pow_mul, ← mul_pow, Nat.div_mul_cancel hm, ← MonObj.comp_pow, lab_pow, MonObj.comp_one]
  obtain ⟨V, hV, hth⟩ := exists_isGenSec_near hL2.secBaseChangeAny t.pol (x p)
  choose W hW hU using fun a => exists_symLift_near hL.globalFns t.pol (k := m ^ 2) hmo.pow
    (T := Over.mk x) _ (hy a) p
  obtain ⟨R', _, φ, hφ, hp, hsub⟩ := exists_affine_nhds
    (x ⁻¹ᵁ V ⊓ ⟨⋂ a, (W a).1, isOpen_iInter_of_finite fun a => (W a).isOpen⟩) p
    ⟨hV, Set.mem_iInter.2 hW⟩
  let T : Over S := Over.mk (spMap φ ≫ x)
  let h : T ⟶ Over.mk x := Over.homMk (spMap φ) rfl
  obtain ⟨th, hth⟩ := hth R' (spMap φ ≫ x) (by
    rintro _ ⟨z, rfl⟩
    exact (hsub ⟨z, rfl⟩).1)
  obtain ⟨α, hα⟩ := exists_mulPull hL.globalFns t.pol m T
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull t.isLB (Out.mulT t.A T m) (snd T t.A ^ m) (lift_snd _ _)
    ((m : ℤ) ^ 2) 1 α hα th
  have hU' : ∀ a, ∃ θ : Out.ThetaGrp t.A t.L ((m : ℤ) ^ 2) T, Out.SymLift t.A t.L ((m : ℤ) ^ 2) (m ^ 2)
      (((Over.homMk T.hom (by simp) : T ⟶ Out.baseOver S) ≫ t.lab a) ^ ((N' / m) ^ 2)) θ := fun a => by
    obtain ⟨θ, hθ⟩ := hU a T h fun z hz => Set.mem_iInter.1 (hsub hz).2 a
    rw [← Nat.cast_pow]
    refine ⟨θ, ?_⟩
    have e : h ≫ (u ≫ t.lab a) ^ ((N' / m) ^ 2) =
        ((Over.homMk T.hom (by simp) : T ⟶ Out.baseOver S) ≫ t.lab a) ^ ((N' / m) ^ 2) := by
      rw [MonObj.comp_pow, ← Category.assoc]; rfl
    rw [← e]
    exact hθ
  choose U hU' using hU'
  choose σ hσ using fun a => ThetaPtExist.exists_isTwistPull t.isLB (Out.translT t.A (U a).pt)
    (Out.translPt t.A (U a).pt) (lift_snd _ _) ((m : ℤ) ^ 2) ((m : ℤ) ^ 2) (U a).φ (U a).isGen s₁
  exact ⟨R', inferInstance, φ, σ, hφ, hp, th, s₁, α, U, hth, hα, hs₁, hU', hσ⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaObject_eighthPower_principalSiegel : Out.Laws → Out.Laws2 → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (c : SiegPre h k (b.ζ : o) s), Odd k → 3 ≤ k → b.ζ ^ k = 1 → c.Principal → ∃ t : TObj g k J b s, IsSharp W a bas t c := by
  first | exact @GlobalTheory.SiegelPower.exists_tObj_isSharp | exact GlobalTheory.SiegelPower.exists_tObj_isSharp | (intros; apply GlobalTheory.SiegelPower.exists_tObj_isSharp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleSpecialFibreExtendedPrincipalPolarisatioStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_specialFibre_extended_principalPolarisation : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → IsAdicComplete (IsLocalRing.maximalIdeal V) V → RelAmple ((Over.pullback (spMap (IsLocalRing.residue V))).obj B) (M.L.L.pull (pullback.fst B.hom (spMap (IsLocalRing.residue V)))) := by
  first | exact @GlobalTheory.SpecialAmple.relAmple_special_fibre | exact GlobalTheory.SpecialAmple.relAmple_special_fibre | (intros; apply GlobalTheory.SpecialAmple.relAmple_special_fibre <;> assumption)
end

