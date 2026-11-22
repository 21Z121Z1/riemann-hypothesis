import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0123
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBase
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaLocal

open Out ThetaPtExist

theorem exists_isThetaPtOver {S : Scheme.{0}} (P : PolAV S) (k : ℕ)
    (α₀ : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A k).left] ![(k : ℤ) ^ 2, -1]))
    (hα₀ : α₀.IsGen) {T : Over S} {I : Type} (x : I → (T ⟶ P.A)) (th : LB.Sec (LPow P.A P.L 1 T))
    (hth : IsGenSec P.A P.L 1 th)
    (hU : ∀ i, ∃ θ : ThetaGrp P.A P.L ((k : ℤ) ^ 2) T, SymLift P.A P.L ((k : ℤ) ^ 2) (k ^ 2) (x i) θ) :
    ∃ v, IsThetaPtOver P k x v := by
  have hL := P.isLB
  have e₁ : (snd T P.A).left ≫ (mulA P.A k).left = (snd T P.A ^ k).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α, hα, -⟩ := exists_gen hL (φ' := ![(snd T P.A).left, (snd T P.A ^ k).left]) (ε' := ![(k : ℤ) ^ 2, -1])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ ((k : ℤ) ^ 2)) (Category.comp_id _)
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A k).left] ![(k : ℤ) ^ 2, -1] α₀ (snd T P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨ρ, hρ⟩ := P.rigid
  obtain ⟨τ, hτ, -⟩ := exists_gen hL (φ' := fun _ : Fin 1 => (1 : T ⟶ P.A).left) (ε' := fun _ => (k : ℤ) ^ 2)
    (fun U _ f => by
      rw [Fintype.prod_unique, Fin.prod_univ_one]
      exact congrArg₂ (fun q n => f q ^ n) rfl (by simp))
    (GeneratorPullback.powGen P.L _ _ (LB.pullGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) ρ (toUnit T).left) (k ^ 2))
    (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hρ _) _)
  obtain ⟨s₁, hs₁⟩ := exists_isTwistPull hL (mulT P.A T k) (snd T P.A ^ k) (lift_snd _ _) ((k : ℤ) ^ 2) 1 α hα th
  choose U hU using hU
  choose s₂ hs₂ using fun i => exists_isTwistPull hL (translT P.A (U i).pt) (translPt P.A (U i).pt) (lift_snd _ _)
    ((k : ℤ) ^ 2) ((k : ℤ) ^ 2) (U i).φ (U i).isGen s₁
  choose w hw using fun i => exists_isValueAt hL (s₂ i) 1 τ hτ
  exact ⟨w, th, s₁, α, τ, U, s₂, w, 1, hth, hα, hτ, hs₁, hU, hs₂, hw, fun i => (_root_.one_mul _).symm⟩

theorem exists_isThetaPt {S : Scheme.{0}} (P : PolAV S) (k : ℕ) (hk : Odd k)
    (α₀ : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A k).left] ![(k : ℤ) ^ 2, -1]))
    (hα₀ : α₀.IsGen) {T : Over S} (hu : IsUnit (k : Γ(T.left, ⊤))) {I : Type} (x : I → (T ⟶ P.A))
    (t : SecM P.A P.L 1 T) (ht : ∀ s, ∃ r : Γ(T.left, ⊤), r • t = s)
    (hU : ∀ i, ∃ θ : ThetaGrp P.A P.L ((k : ℤ) ^ 2) T, SymLift P.A P.L ((k : ℤ) ^ 2) (k ^ 2) (x i) θ) :
    ∃ v, IsThetaPt P k x v := by
  let h : T ⟶ overRes (T := T) ⊤ := Over.homMk T.left.topIso.inv (by
    show T.left.topIso.inv ≫ (⊤ : T.left.Opens).ι ≫ T.hom = T.hom
    rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp])
  have hh : h ≫ overResι (T := T) ⊤ = 𝟙 T := Over.OverMorphism.ext T.left.toIso_inv_ι
  have hi : overResι (T := T) ⊤ ≫ h = 𝟙 _ := by
    haveI : Mono (overResι (T := T) ⊤) := Over.mono_of_mono_left _ (hk := inferInstanceAs (Mono (⊤ : T.left.Opens).ι))
    rw [← cancel_mono (overResι (T := T) ⊤), Category.assoc, hh, Category.comp_id, Category.id_comp]
  obtain ⟨th, hth⟩ := exists_isGenSec_of_retract P.isLB (overResι (T := T) ⊤) h hi t ht
  obtain ⟨w, hw⟩ := exists_isThetaPtOver P k α₀ hα₀ (fun i => overResι (T := T) ⊤ ≫ x i) th hth fun i => by
    obtain ⟨θ, hθ⟩ := hU i
    exact GlobalLift.exists_symLift_pull P.isLB _ hθ
  refine ⟨fun i => h.left.appTop.hom (w i), hk, hu, fun _ => ⟨⊤, trivial, ?_⟩⟩
  convert hw using 2 with i
  have q := congrArg (fun q => q.left.appTop.hom (w i)) hi
  simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, Over.id_left,
    Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply] at q
  exact q

theorem exists_generator {R M K : Type} [CommRing R] [AddCommGroup M] [Module R M] [Subsingleton K] (b : K → M)
    (hb : Submodule.span R (Set.range b) = ⊤) : ∃ t : M, ∀ s, ∃ r : R, r • t = s := by
  rcases isEmpty_or_nonempty K with h | ⟨⟨i⟩⟩
  · refine ⟨0, fun s => ⟨0, ?_⟩⟩
    have : s ∈ Submodule.span R (Set.range b) := hb ▸ Submodule.mem_top
    rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at this
    rw [this, zero_smul]
  · have e : Set.range b = {b i} := by
      ext m
      exact ⟨fun ⟨j, hj⟩ => by rw [← hj, Subsingleton.elim j i]; rfl, fun hm => ⟨i, hm.symm⟩⟩
    exact ⟨b i, fun s => Submodule.mem_span_singleton.1 (by rw [← e, hb]; exact Submodule.mem_top)⟩

theorem exists_affine_isThetaPt (hG : GlobalFnsSt) (hB : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) (k : ℕ)
    (hk : Odd k) (hu : IsUnit (k : Γ(S, ⊤))) {I : Type} [Finite I] (y : I → (baseOver S ⟶ P.A))
    (hy : ∀ i, y i ^ (k ^ 2) = 1) (p : S) :
    ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ S), IsOpenImmersion x ∧ p ∈ Set.range x ∧
      ∃ v, IsThetaPt P k (T := Over.mk x)
        (fun a => (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ y a) v := by
  have cg := GlobalTheory.AbLaw.CubeAssembly.cube_gen
  have neg := GlobalTheory.exists_gen_negLB hG
  obtain ⟨α₀, hα₀⟩ := (GlobalTheory.MulPull.mulPull_of_cube_of_symm cg neg).1 S P k
  have sym := (GlobalTheory.symLift_odd hG (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube cg).1).2.2 neg).1
  obtain ⟨V₀, hV₀, b, hb⟩ := hB S P 1 le_rfl p
  choose V hV θ hθ using fun i => (sym S P (k ^ 2) hk.pow (baseOver S) (y i) (hy i)).1 p
  let O : S.Opens := V₀ ⊓ ⟨⋂ i, (V i).carrier, isOpen_iInter_of_finite fun i => (V i).2⟩
  have hO : p ∈ O := ⟨hV₀, Set.mem_iInter.2 hV⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hpW, hWO⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open hO O.2
  have hW' : IsAffineOpen W := hW
  let x₀ : Sp Γ(S, W) ⟶ S := hW'.fromSpec
  have hx₀ : Set.range x₀ = W := hW'.range_fromSpec
  have hl : ∀ U : S.Opens, O ≤ U → ∃ t : Sp Γ(S, W) ⟶ U.toScheme, t ≫ U.ι = x₀ := fun U hU =>
    ⟨IsOpenImmersion.lift U.ι x₀ (by
      rw [hx₀, Scheme.Opens.range_ι]; exact hWO.trans hU), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨t, ht⟩ := hl V₀ inf_le_left
  have ex : t ≫ (overRes (T := baseOver S) V₀).hom = x₀ := (congrArg (t ≫ ·) (Category.comp_id _)).trans ht
  refine ⟨Γ(S, W), inferInstance, t ≫ (overRes (T := baseOver S) V₀).hom, ?_, ?_, ?_⟩
  · rw [ex]; exact inferInstanceAs (IsOpenImmersion hW'.fromSpec)
  · rw [ex, hx₀]; exact hpW
  obtain ⟨-, hsp⟩ := hb _ t (fun i => VVRank.pullS P.A _ (homAt t) (b i)) fun i => VVRank.isPullSec_pullS _ _ _ _
  haveI : Subsingleton (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  obtain ⟨th, hth⟩ := exists_generator _ hsp
  refine exists_isThetaPt P k hk α₀ hα₀ (T := baseAt t) ?_ _ th hth fun i => ?_
  · simpa using hu.map (baseAt t).hom.appTop.hom
  · obtain ⟨u, hu'⟩ := hl (V i) (inf_le_right.trans fun q hq => Set.mem_iInter.1 hq i)
    let r : baseAt t ⟶ overRes (T := baseOver S) (V i) := Over.homMk u
      (((congrArg (u ≫ ·) (Category.comp_id _)).trans hu').trans ex.symm)
    obtain ⟨θ', hθ'⟩ := GlobalLift.exists_symLift_pull P.isLB r (hθ i)
    have e : r ≫ overResι (V i) = (Over.homMk (baseAt t).hom (by simp) : baseAt t ⟶ baseOver S) :=
      Over.OverMorphism.ext (hu'.trans ex.symm)
    rw [← Category.assoc, e] at hθ'
    rw [← Nat.cast_pow]
    exact ⟨θ', hθ'⟩

theorem linComb_pow_eq_one {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {r n : ℕ}
    {y : Fin r → (T ⟶ A)} (hy : ∀ i, y i ^ n = 1) (a : Fin r → ℕ) : linComb y a ^ n = 1 := by
  rw [linComb, List.prod_ofFn, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]

theorem exists_hasTh : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s), Odd N' → ∀ p : S, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), IsOpenImmersion x ∧ p ∈ Set.range x ∧ t.HasTh x v := by
  intro h₁ h₂ o _ g N' J b S s t hN p
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero _ hN.pos.ne'⟩
  have hu : IsUnit (N' : Γ(S, ⊤)) := by
    have := (b.unit.map (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom).map s.appTop.hom
    rw [map_natCast, map_natCast, Nat.cast_pow] at this
    exact (isUnit_pow_iff two_ne_zero).1 this
  haveI := t.ab.comm
  obtain ⟨R, _, x, hx, hp, v, hv⟩ := exists_affine_isThetaPt h₁.globalFns h₂.secBaseChangeAny t.pol N' hN hu t.lab
    (fun a => linComb_pow_eq_one t.torsion _) p
  refine ⟨R, inferInstance, x, fun a => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (v a), hx, hp, ?_⟩
  unfold TObj.HasTh
  convert hv using 2 with a
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply (v a)

end GlobalTheory.ThetaLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionCubeLBIsoPolarisationTranslate
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.TorsionTranslation

open Out CommutatorPairing PrimCocycle CechPic

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem transl_mulA (k : ℕ) (y : 𝟙_ (Over S) ⟶ A) (hy : y ^ k = 1) :
    ((toUnit A ≫ y) * 𝟙 A).left ≫ (mulA A k).left = (mulA A k).left := by
  rw [← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, hy,
    MonObj.comp_one, _root_.one_mul]

theorem exists_character (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {X : Scheme.{0}} {M : LB X} (hM : M.IsLB)
    {I : Type} [Fintype I] (φ : I → (A.left ⟶ X)) (ε : I → ℤ) (k : ℕ)
    (u : LB.Gen (LB.LinComb M (fun i => (mulA A k).left ≫ φ i) ε)) (hu : u.IsGen) :
    ∃ χ : {y : 𝟙_ (Over S) ⟶ A // y ^ k = 1} → Γ((𝟙_ (Over S)).left, ⊤)ˣ,
      (∀ x y, χ ⟨x.1 * y.1, by rw [mul_pow, x.2, y.2, _root_.one_mul]⟩ = χ x * χ y) ∧
      ∀ y (z : A.left) J, Good M z J →
        val u ((toUnit A ≫ y.1) * 𝟙 A).left z J = val u (𝟙 _) z J * gm (toUnit A).left z ⊤ (χ y) := by
  have he : (1 : 𝟙_ (Over S) ⟶ A).left ≫ (toUnit A).left = 𝟙 _ := by
    rw [← Over.comp_left, comp_toUnit, toUnit_unit]; rfl
  have hp : Function.Surjective (toUnit A).left.appTop.hom := by
    have e : (toUnit A).left = A.hom := (Category.comp_id _).symm.trans (Over.w (toUnit A))
    rw [e]
    exact (hG _ _ hA).2
  have H : ∀ y : {y : 𝟙_ (Over S) ⟶ A // y ^ k = 1}, ∃ c : Γ((𝟙_ (Over S)).left, ⊤)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J), Good M z J →
        val u (r ≫ ((toUnit A ≫ y.1) * 𝟙 A).left) z J = val u r z J * gm (r ≫ (toUnit A).left) z ⊤ c := by
    intro y
    obtain ⟨c, hc⟩ := exists_ratio hM (fun U _ h => Finset.prod_congr rfl fun i _ => by
        rw [← Category.assoc, transl_mulA k y.1 y.2]) (toUnit A).left _ he hp
      (DVR.pullGen_isGen _ _ _ u hu ((toUnit A ≫ y.1) * 𝟙 A).left) hu
    exact ⟨c, fun Z r z J hJ => (val_pull hJ _ _ _).symm.trans (hc Z r z J hJ)⟩
  choose χ hχ using H
  refine ⟨χ, fun x y => unit_ext fun z _ => ?_, fun y z J hJ => ?_⟩
  · choose J hJ using fun ψ : (𝟙_ (Over S)).left ⟶ X => exists_chart hM (ψ z)
    have a := hχ ⟨x.1 * y.1, by rw [mul_pow, x.2, y.2, _root_.one_mul]⟩ _ (1 : 𝟙_ (Over S) ⟶ A).left z J hJ
    have b := hχ x _ (1 : 𝟙_ (Over S) ⟶ A).left z J hJ
    have c := hχ y _ ((1 : 𝟙_ (Over S) ⟶ A).left ≫ ((toUnit A ≫ x.1) * 𝟙 A).left) z J hJ
    have e₁ : ((toUnit A ≫ x.1) * 𝟙 A).left ≫ ((toUnit A ≫ y.1) * 𝟙 A).left =
        ((toUnit A ≫ (x.1 * y.1)) * 𝟙 A).left := by
      rw [← Over.comp_left, MonObj.comp_mul, MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id,
        ← _root_.mul_assoc, mul_comm (toUnit A ≫ y.1)]
    have e₂ : ((toUnit A ≫ x.1) * 𝟙 A).left ≫ (toUnit A).left = (toUnit A).left := by
      rw [← Over.comp_left, comp_toUnit]
    rw [b, Category.assoc, Category.assoc, e₁, e₂, a, he, _root_.mul_assoc, ← map_mul] at c
    exact mul_left_cancel c
  · have := hχ y _ (𝟙 _) z J hJ
    rwa [Category.id_comp, Category.id_comp] at this

theorem exists_gen_mulA {M : LB A.left} (hM : M.IsLB) (hΘ : ∃ t : LB.Gen (Theta A M), t.IsGen) (k : ℕ)
    (x : 𝟙_ (Over S) ⟶ A) (hx : x ^ k = 1) :
    ∃ u : LB.Gen (LB.LinComb M (fun I : ULift.{0} (Finset (Fin 2)) =>
      (mulA A k).left ≫ (psum A ![toUnit A ≫ x, 𝟙 A] I.down).left) lamε), u.IsGen := by
  refine (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).1 ?_
  have h₁ : (cubeLB A ![toUnit A ≫ x, 𝟙 A] M).IsLB := LB.isLB_linComb hM _ _
  have e := congrArg (CechPic.pull (mulA A k).left) ((cls_linComb hM _ _ h₁).symm.trans (cls_cube_two hM _ _ h₁))
  rw [pull_lam, comp_toUnit_assoc, Category.comp_id, map_sum] at e
  have e' : lam (cls M hM) (toUnit A ≫ x) (mulA A k) = 0 := by
    rw [mulA, lam_pow_right hM hΘ, ← lam_pow_left hM hΘ, ← MonObj.comp_pow, hx, MonObj.comp_one, lam_one_left]
  rw [cls_linComb hM]
  refine Eq.trans (Finset.sum_congr rfl fun I _ => ?_) (e.trans e')
  rw [map_zsmul, pull_comp]

end GlobalTheory.TorsionTranslation

namespace GlobalTheory

open TorsionTranslation PairingDetermines IsoDescent PrimCocycle

theorem exists_torsion_lbIso_cubeLB : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (k : ℕ) (x : 𝟙_ (Over (Sp K)) ⟶ P.A), M.IsLB → (k : K) ≠ 0 → x ^ k = 1 → ∃ y : 𝟙_ (Over (Sp K)) ⟶ P.A, y ^ k = 1 ∧ LBIso (cubeLB P.A ![toUnit P.A ≫ x, 𝟙 P.A] M) (cubeLB P.A ![toUnit P.A ≫ y, 𝟙 P.A] P.L) := by
  intro hL hL' K _ _ P M k x hM hk hx
  haveI : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨u, hu⟩ := exists_gen_mulA hM (AbLaw.CubeAssembly.cube_gen _ P M hM) k x hx
  obtain ⟨χ, hχ, vχ⟩ := exists_character hL.globalFns P.isAb hM _ _ k u hu
  obtain ⟨y, ⟨hy, hw⟩, -⟩ := hL'.charPair K P k hk (fun δ => (χ δ)⁻¹) (fun a b =>
    (congrArg (·⁻¹) (hχ a b)).trans (mul_inv _ _))
  refine ⟨y, hy, ?_⟩
  obtain ⟨u₀, hu₀, v₀⟩ := exists_gen_lam hL.globalFns hL.cube P (𝟙 P.A) 1 k y hy
  obtain ⟨u', hu', v'⟩ := exists_gen P.isLB (φ' := fun I : ULift.{0} (Finset (Fin 2)) =>
      (Out.mulA P.A k).left ≫ (psum P.A ![toUnit P.A ≫ y, 𝟙 P.A] I.down).left) (ε' := lamε)
    (fun U _ h => Finset.prod_congr rfl fun I _ => by
      have e : (lift (toUnit P.A ≫ y) (𝟙 P.A)).left ≫ lamφ P.A I =
          (psum P.A ![toUnit P.A ≫ y, 𝟙 P.A] I.down).left :=
        congrArg (fun q => q.left) ((psum_hom (preHom (lift (toUnit P.A ≫ y) (𝟙 P.A))) (x2 P.A) I.down).trans
          (congrArg (fun q => psum P.A q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])))
      rw [Over.id_left, Category.comp_id, e, Nat.cast_one, _root_.mul_one]) u₀ hu₀
  refine lbIso_of_invariant hM P.isLB _ _ _ _ (Out.mulA P.A k).left
    (I := {y : 𝟙_ (Over (Sp K)) ⟶ P.A // y ^ k = 1}) (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left)
    (fun δ => transl_mulA k δ.1 δ.2)
    (fun U f hf => torsion_invariant_descends (fun S _ P n hn => by
      obtain ⟨a, b, c, e, -⟩ := hL.mulN S P n hn
      exact ⟨a, b, c, e⟩) K P k hk U f fun y hy => hf ⟨y, hy⟩) u hu u' hu'
    (fun δ z J J' hJ hJ' => ?_)
  have w := CommPairing.weilIs_symm P.isLB (hw δ)
  rw [inv_inv] at w
  have h₁ := vχ δ z J hJ
  have h₂ := v₀ δ.1 (χ δ) δ.2 (by rw [Category.comp_id, Category.comp_id]; exact w) z J' hJ'
  rw [pow_one, ← v' _ _ z J' hJ', ← v' _ _ z J' hJ'] at h₂
  refine (congrArg₂ (fun a b => a * b⁻¹) h₂ h₁).trans ?_
  exact mul_div_mul_right_eq_div _ _ _ |> fun h => by simpa only [div_eq_mul_inv] using h

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfUnifOfSubsingleton
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.NoTorus

theorem pmaps_id {X Y : Scheme.{0}} {L : LB X} {F : X ⟶ X} (hF : F = 𝟙 X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) :
    PMaps (isoPullId (Geo.Tor.idIso L) hF) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  subst hF
  have hp' : ∀ k, φ k (r z) ∈ L.U (p k) := hp
  rw [Category.comp_id]
  refine (gen_trans ht r z (Set.mem_iInter.2 hp') (Set.mem_iInter.2 hq)).trans
    (congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_))
  rw [gw_isoPullId (Geo.Tor.idIso L) rfl (r ≫ φ k) z (p k) (q k) (hp' k) (hq k)]
  rfl

theorem nonempty_isPullDeg_self {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hR : AdmBase R I)
    (D : DegData R I) : Nonempty (IsPullDeg (RingHom.id R) D.toPre D.toPre) := by
  have : IsMonHom (Iso.refl D.toPre.P.A).hom := inferInstanceAs (IsMonHom (𝟙 D.toPre.P.A))
  have gp : IsGrpPullback D.toPre.P.A D.toPre.P.A (specOf (RingHom.id R)) (Iso.refl D.toPre.P.A).hom.left :=
    (isGrpPullback_of_iso (Iso.refl D.toPre.P.A)).congr (specOf_id R).symm rfl
  obtain ⟨e, me, hF⟩ := grpPullback_iso gp (isGrpPullback_pullback D.toPre.P.A (specOf (RingHom.id R)))
  have hF' : e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ := hF
  obtain ⟨W, hW, ⟨ψW⟩⟩ := psiOnExists R I hR D
  obtain ⟨hD, -⟩ := UnifUniq.exists_isPullDeg_id D.toPre D.toPre W hW ψW e me
    (isoPullId (Geo.Tor.idIso D.toPre.P.L) hF') ((isGen_iff _).2 (isoPullId_pgen (idIso_isGen D.toPre.P.isLB) hF'))
    ((congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (pmaps_id hF' (K := PUnit) (fun _ => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig_gen) (AddEquiv.refl _)
    (fun x => (congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (fun x => pmaps_id hF' (K := PUnit) (fun _ => D.toPre.xK x) (fun _ => -1) (D.toPre.psi_gen x))
  exact ⟨hD⟩

end GlobalTheory.NoTorus

namespace GlobalTheory

theorem isAbelianScheme_of_unif_of_subsingleton : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (IsLocalRing.maximalIdeal V) D A G → Subsingleton D.toPre.X → IsAbelianScheme G := by
  intro hL hL₂ V _ _ _ _ hc D A G _ hG hsa U hX
  have hR : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨A', eA, hA, hw⟩ := GoodReductionUnif.exists_baseChange hL.polBaseChange (jK V) D.toPre.P
  obtain ⟨hD⟩ := NoTorus.nonempty_isPullDeg_self hR D
  obtain ⟨ψ, -⟩ := GlobalTheory.T.exists_iso_uniformisations_of_iso_degeneration_data hL hL₂ V _ hR rfl D D A A' G D.toPre.P.A hsa
    (isSemiAbelian_of_isAbelianScheme _ D.toPre.P.isAb) U
    ⟨SelfUnif.selfPre D A' eA hA hw, fun k _ =>
      SelfUnif.expBij D A' eA hA hw hL.globalFns (IsAdicComplete.le_jacobson_bot _) k⟩ hD
  have e : G.hom = ψ.inv.left ≫ D.toPre.P.A.hom := (Over.w ψ.inv).symm
  have := D.toPre.P.isAb.proper
  have : IsIso ψ.inv.left := inferInstanceAs (IsIso ((Over.forget _).map ψ.inv))
  exact ⟨hG, hsa.smooth, by rw [e]; infer_instance, hsa.geomConnected⟩

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KTrivOfGeometricPointsAndTangents
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.KCriterion

theorem mono_of_unramified_of_geometric_points {X Y : Scheme.{0}} (f : X ⟶ Y) [FormallyUnramified f]
    [LocallyOfFiniteType f]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ X), y ≫ f = y' ≫ f → y = y') : Mono f := by
  have hs : Surjective (pullback.diagonal f) := ⟨fun z => by
    let κ : Type := (pullback f f).residueField z
    let y : Sp (AlgebraicClosure κ) ⟶ pullback f f :=
      spMap (algebraMap κ (AlgebraicClosure κ)) ≫ (pullback f f).fromSpecResidueField z
    have e := h _ (y ≫ pullback.fst f f) (y ≫ pullback.snd f f)
      ((Category.assoc _ _ _).trans ((congrArg _ pullback.condition).trans (Category.assoc _ _ _).symm))
    have e' : (y ≫ pullback.fst f f) ≫ pullback.diagonal f = y := by
      refine pullback.hom_ext ?_ ?_
      · simp
      · simp [e]
    exact ⟨(y ≫ pullback.fst f f) (IsLocalRing.closedPoint _),
      (congrArg (fun q => q (IsLocalRing.closedPoint _)) e').trans (Scheme.fromSpecResidueField_apply z _)⟩⟩
  have : IsIso (pullback.diagonal f) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hs⟩
  exact (pullback.isIso_diagonal_iff f).1 this

theorem triv_of_inK_local {S : Scheme.{0}} {A : Over S} [GrpObj A] {M : LB A.left} {K : Type} [CommRing K]
    [IsLocalRing K] {t : Sp K ⟶ S} {x : Over.mk t ⟶ A} (hx : InK A M x) : Triv (Out.translDiff A M x) := by
  obtain ⟨V, hp, c, hc⟩ := hx (IsLocalRing.closedPoint K)
  have hV : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).1 hp
  have := exists_isGen_translDiff_comp A M x (𝟙 _) V (fun q => hV.ge trivial) c hc
  rwa [Category.id_comp] at this

theorem kTriv_of_points_of_tangents : Out.Laws → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → IsProjBy A.hom → ∀ M : LB A.left, M.IsLB → (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K], (∀ x : specO R K ⟶ A, Triv (Out.translDiff A M x) → x = 1) ∧ ∀ x : specO R (DualNumber K) ⟶ A, ptMap (TrivSqZeroExt.fstHom R K K) ≫ x = 1 → Triv (Out.translDiff A M x) → x = 1) → Out.KTriv A M := by
  intro hL R _ A _ _ hA hP M hM hK
  obtain ⟨hO, -, hT⟩ := TrivTwist.inK_iff_trivial_twist _ A M hM
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hL.globalFns R A hA hP M (pw M 0) hM hO
  have hrep : ∀ (T : Over (Sp R)) (x : T ⟶ A), InK A M x ↔ ∃ y : T ⟶ H, y ≫ j = x :=
    fun T x => (hT _ rfl T x).trans (hH T x)
  have := hA.proper
  have hft : LocallyOfFiniteType H.hom := by rw [← Over.w j]; infer_instance
  have hpt : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (y : Over.mk t ⟶ H), y ≫ j = 1 := by
    intro k _ _ t
    obtain ⟨φ, rfl⟩ := Spec.map_surjective t
    let _ : Algebra R k := φ.hom.toAlgebra
    exact fun y => (hK k).1 (y ≫ j) (triv_of_inK_local ((hrep _ _).2 ⟨y, rfl⟩))
  have htan : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R)
      (y : Over.mk (TangentCrit.dualBase k ≫ t) ⟶ H), y ≫ j = 1 := by
    intro k _ _ t
    obtain ⟨φ, rfl⟩ := Spec.map_surjective t
    let _ : Algebra R k := φ.hom.toAlgebra
    have e : TangentCrit.dualBase k ≫ Spec.map φ = spMap (algebraMap R (DualNumber k)) :=
      (Spec.map_comp _ _).symm
    rw [e]
    intro y
    refine (hK k).2 (y ≫ j) ?_ (triv_of_inK_local ((hrep _ _).2 ⟨y, rfl⟩))
    rw [← Category.assoc]
    exact hpt k _ _
  have hext : ∀ {T : Scheme.{0}} {t : T ⟶ Sp R}, (∀ y : Over.mk t ⟶ H, y ≫ j = 1) →
      ∀ w w' : T ⟶ H.left, w ≫ H.hom = t → w' ≫ H.hom = t → w = w' := fun h w w' e e' =>
    (cancel_mono j.left).1 (congrArg (fun q => q.left)
      ((h (Over.homMk w e)).trans (h (Over.homMk w' e')).symm))
  have hu : FormallyUnramified H.hom :=
    TangentCrit.formallyUnramified_of_tangent H.hom fun k _ _ w hw =>
      hext (htan k (TangentCrit.dualPt k ≫ w ≫ H.hom)) _ _ hw (by simp only [Category.assoc])
  have hm : Mono H.hom := mono_of_unramified_of_geometric_points H.hom fun k _ _ y y' e =>
    hext (hpt k (y' ≫ H.hom)) _ _ e rfl
  refine kTriv_iff_forall.2 fun T x hx => ?_
  obtain ⟨y, rfl⟩ := (hrep T x).1 hx
  obtain ⟨y', hy'⟩ := (hrep T 1).1 (inK_one hM T)
  have : y = y' := Over.OverMorphism.ext ((cancel_mono H.hom).1 ((Over.w y).trans (Over.w y').symm))
  rw [this, hy']

end GlobalTheory.KCriterion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MulAPullbackIsoPowSqSymmetricAbelianVariety
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.MulSym

open GlobalTheory.MulPull GlobalTheory.PrimNorm

theorem lbIso_mulPull_of_cube {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (M : LB A.left)
    (k : ℕ) (hM : M.IsLB) (hc : ∃ t : LB.Gen (Theta A M), t.IsGen) (hs : SymB M) :
    LBIso (M.pull (Out.mulA A k).left) (lbPow M (k ^ 2)) := by
  have hcube : HasGen M (thφ A (x3 A)) thε := hc
  have hrig : HasGen M (Y := Spec (CommRingCat.of K)) (K := PUnit) (fun _ => eSec A) (fun _ => 1) :=
    DVR.exists_gen_of_local M hM _ _
  have hs' : LBIso (M.pull (𝟙 A.left)) (M.pull (GrpObj.inv : A ⟶ A).left) :=
    LBIso.chartPull (chartPullPull M _ _ rfl) (chartPullId _) hs
  have hneg := (lbIso_iff hM _ _ _ _).1 hs'
  simp only [Fintype.prod_unique, zpow_one] at hneg
  have main := hasGen_pow hM hcube (𝟙 A) ?_ ?_ k
  · have h := (hasGen_iff hM _ _).1 main
    refine (lbIso_iff hM _ _ _ _).2 ?_
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg_one,
      mul_inv_eq_one] at h
    simp only [Fintype.prod_unique, zpow_one, Nat.cast_pow]
    exact h.symm
  · refine (hrig.pull (toUnit A).left).of_formEq hM (fun U _ h => ?_)
    simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Matrix.cons_val_zero, _root_.mul_one]
    rfl
  · refine (hasGen_iff hM _ _).2 ?_
    have e : ((𝟙 A : A ⟶ A)⁻¹) = (GrpObj.inv : A ⟶ A) := Category.id_comp _
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg_one, zpow_one,
      mul_inv_eq_one, e]
    exact hneg

theorem lbIso_mulPull_of_symB : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (k : ℕ), M.IsLB → SymB M → LBIso (M.pull (Out.mulA P.A k).left) (lbPow M (k ^ 2)) :=
  fun _ _ _ P M k hM hs => lbIso_mulPull_of_cube P.A M k hM (GlobalTheory.AbLaw.CubeAssembly.cube_gen _ P M hM) hs

end GlobalTheory.MulSym
end

