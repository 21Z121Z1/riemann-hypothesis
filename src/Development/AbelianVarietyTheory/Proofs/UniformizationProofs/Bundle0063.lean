import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0053
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0054

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.JKAppTopInjective
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.PsiInt

theorem gs_scal {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z)
    (c : R) : gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) :=
  calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
    _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
    _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl

theorem scal_jK {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of (FractionRing R))) (c : R) :
    scal (p ≫ jK R) c = scal p (algebraMap R (FractionRing R) c) := by
  have e := congrArg (fun q => q.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  unfold scal
  rw [e]
  rfl

theorem jK_appTop_injective (R : Type) [CommRing R] [IsDomain R] : Function.Injective (jK R).appTop.hom := by
  have hs := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2
  have hi := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv).1
  intro x y h
  obtain ⟨a, rfl⟩ := hs x
  obtain ⟨b, rfl⟩ := hs y
  have e := fun c => congrArg (fun q => q.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  have := hi ((e a).trans (h.trans (e b).symm))
  rw [IsFractionRing.injective R (FractionRing R) this]

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem cT_zero (T : Over (Spec (CommRingCat.of R))) : cT D T 0 = 1 := by
  have h : D.c 0 = D.c 0 * D.c 0 := by
    have := D.c_add 0 0
    rwa [add_zero] at this
  have h1 : D.c 0 = 1 := left_eq_mul.1 h
  rw [cT, h1, MonObj.comp_one]

theorem exists_defect
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (f : ∀ α, SecBT D (𝟙_ _) 1 α) (χ : D.X) (hg : (ga χ).IsGen) (p q : R) :
    ∃ d : SecBT D (𝟙_ _) 1 χ, ∀ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J),
      Good D.P.L z J → sval d (lift (toUnit T) y).left z J =
        gs (𝟙 _) z ⊤ (scal T.hom q) * sval (f χ) (lift (toUnit T) y).left z J -
        gs (𝟙 _) z ⊤ (scal T.hom p) * ((val (ga χ) (toUnit T).left z J * rigV D z J).val *
          sval (f 0) (lift (toUnit T) (y * cT D T χ)).left z J) := by
  let Y : Over (Spec (CommRingCat.of R)) := 𝟙_ _ ⊗ D.P.A
  let τ : Y ⟶ Y := lift (toUnit Y) (snd _ _ * cT D Y χ)
  have hF : FormEq (famφT D (𝟙_ _) χ) (DegPre.famε 1)
      (Sum.elim (fun k => τ.left ≫ famφT D (𝟙_ _) 0 k)
        (fun k => (toUnit Y).left ≫ Sum.elim (fun _ : PUnit => (D.c χ).left) (fun _ : PUnit => eSec D.P.A) k))
      (Sum.elim (DegPre.famε 1) (Sum.elim (fun _ => -1) (fun _ => 1))) := by
    intro U _ h
    have e₁ : τ.left ≫ famφT D (𝟙_ _) 0 1 = famφT D (𝟙_ _) χ 1 := by
      change (τ ≫ (snd _ _ * cT D Y 0)).left = (snd _ _ * cT D Y χ).left
      rw [cT_zero, _root_.mul_one, lift_snd]
    have e₂ : τ.left ≫ famφT D (𝟙_ _) 0 2 = famφT D (𝟙_ _) χ 3 := by
      change (τ ≫ cT D Y 0).left = (1 : Y ⟶ D.P.A).left
      rw [cT_zero, MonObj.comp_one]
    have e₃ : τ.left ≫ famφT D (𝟙_ _) 0 3 = famφT D (𝟙_ _) χ 3 := by
      change (τ ≫ (1 : Y ⟶ D.P.A)).left = (1 : Y ⟶ D.P.A).left
      rw [MonObj.comp_one]
    have e₄ : (toUnit Y).left ≫ (D.c χ).left = famφT D (𝟙_ _) χ 2 := rfl
    have e₅ : (toUnit Y).left ≫ eSec D.P.A = famφT D (𝟙_ _) χ 3 := rfl
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_four,
      e₁, e₂, e₃, e₄, e₅]
    simp [DegPre.famε, _root_.mul_assoc]
  obtain ⟨d, hd⟩ := exists_sec_relation_defect Y.left D.P.A.left Y.left D.P.L D.P.isLB _ _ _ _ _ _ _ _ _ τ.left
    (f 0) (f χ) (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (ga χ) D.rig) (toUnit Y).left)
    (scal Y.hom p) (scal Y.hom q)
    (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hg D.rig_gen) _) hF
  refine ⟨d, fun T y z J hJ => ?_⟩
  have e₁ : (lift (toUnit T) y).left ≫ Y.hom = T.hom := Over.w _
  have e₂ : (lift (toUnit T) y).left ≫ τ.left = (lift (toUnit T) (y * cT D T χ)).left := by
    rw [← Over.comp_left]
    congr 1
    simp only [τ, comp_lift, MonObj.comp_mul, lift_snd, cT, ← Category.assoc]
    congr 2
    · exact toUnit_unique _ _
    · congr 1
      exact toUnit_unique _ _
  have e₃ : (lift (toUnit T) y).left ≫ (toUnit Y).left = (toUnit T).left := by
    rw [← Over.comp_left]
    exact congrArg _ (toUnit_unique _ _)
  rw [hd _ _ z J hJ, gs_scal, gs_scal Y.hom _ z p, e₁, e₂, val_pull hJ, e₃, val_mul hJ, mul_comm (sval (f 0) _ z J)]
  congr 5

theorem psiRel_integral : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ) (f : ∀ α, SecBT D (𝟙_ _) 1 α), PsiScal D ga a → PsiRel D (𝟙_ _) f → ∀ (χ : D.X) (p q : R), algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) p → ∀ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → gs (𝟙 _) z ⊤ (scal T.hom q) * sval (f χ) (lift (toUnit T) y).left z J = gs (𝟙 _) z ⊤ (scal T.hom p) * ((val (ga χ) (toUnit T).left z J * rigV D z J).val * sval (f 0) (lift (toUnit T) (y * cT D T χ)).left z J) := by
  intro R _ _ D ga a f hS hR χ p q hpq T y z J hJ
  obtain ⟨d, hd⟩ := exists_defect D ga f χ (hS χ).1 p q
  haveI : Flat D.P.A.hom := by
    haveI := D.P.smoothDim
    haveI : Smooth D.P.A.hom := SmoothOfRelativeDimension.smooth D.P.g _
    infer_instance
  haveI : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left := inferInstanceAs (IsAffine (Spec _))
  haveI : IsAffine (TK R).left := inferInstanceAs (IsAffine (Spec _))
  have hinj : Function.Injective (toUnit (TK R)).left.appTop.hom := by
    have e : (toUnit (TK R)).left = jK R := by simp
    rw [e]
    exact jK_appTop_injective R
  have h0 := sec_eq_zero_of_sval_whiskerRight_eq_zero _ D.P.A (𝟙_ _) (TK R) (toUnit _) hinj _ D.P.L D.P.isLB _ _ _ d
    (fun w I hI => by
      have e : toUnit (TK R) ▷ D.P.A = lift (toUnit (TK R ⊗ D.P.A)) (snd _ _) := by
        ext1
        · exact toUnit_unique _ _
        · simp
      have e' : (TK R ⊗ D.P.A).hom = (fst (TK R) D.P.A).left ≫ jK R := (Over.w (fst (TK R) D.P.A)).symm
      have e₁ := hR χ _ (toUnit _) (fst (TK R) D.P.A) (snd _ _) w I hI
      have e₂ := (hS χ).2 _ (fst (TK R) D.P.A) w I hI
      have e₃ : gs (𝟙 _) w ⊤ (scal (TK R ⊗ D.P.A).hom q) * gs (𝟙 _) w ⊤ (scal (fst (TK R) D.P.A).left (a χ).val) =
          gs (𝟙 _) w ⊤ (scal (TK R ⊗ D.P.A).hom p) := by
        rw [← gs_mul _ w ⊤ trivial, e']
        congr 1
        refine (congrArg (· * _) (scal_jK _ q)).trans (Eq.trans ?_ (scal_jK _ p).symm)
        rw [← hpq]
        unfold scal
        rw [map_mul, map_mul]
      rw [e, hd _ _ w I hI, e₁, Units.val_mul, Units.val_mul, e₂, ← e₃]
      ring)
  refine sub_eq_zero.1 ((hd T y z J hJ).symm.trans ?_)
  refine (congrArg (gs _ z _) (h0 _)).trans ((gs_eq _ z _ (hJ.mem _ _) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)

end GlobalTheory.PsiInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MatchingSectionsExist
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UnitSec

section Gen
variable {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem exists_pull {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)} (h : Y' ⟶ Y)
    (hφ : ∀ k, φ' k = h ≫ φ k) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext hφ
  exact ⟨_, fun Z r z J hJ => DVR.SectionScalarValuation.sval_pullSec φ ε s h r z hJ⟩

theorem exists_push {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)} (h : Y' ⟶ Y) (g : Y ⟶ Y')
    (h₁ : g ≫ h = 𝟙 Y) (h₂ : h ≫ g = 𝟙 Y')
    (hφ : ∀ k, φ' k = h ≫ φ k) (s' : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain ⟨s, hs⟩ := exists_pull (φ' := φ) g
    (fun k => by rw [hφ k, ← Category.assoc, h₁, Category.id_comp]) s'
  refine ⟨s, fun Z r z J hJ => ?_⟩
  rw [hs Z _ z J hJ, Category.assoc, h₂, Category.comp_id]

end Gen

theorem unit_inv_snd {S : Scheme.{0}} (G : Over S) :
    (λ_ G).inv.left ≫ (snd (𝟙_ (Over S)) G).left = 𝟙 G.left := by
  rw [← Over.comp_left, leftUnitor_inv_snd, Over.id_left]

theorem snd_unit_inv {S : Scheme.{0}} (G : Over S) :
    (snd (𝟙_ (Over S)) G).left ≫ (λ_ G).inv.left = 𝟙 (𝟙_ (Over S) ⊗ G).left := by
  rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]

theorem famφT_eq {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (α : D.X) (k : Fin 4) : famφT D T α k = (snd T D.P.A).left ≫ D.famφB α k := by
  fin_cases k
  · change (snd T D.P.A).left = (snd T D.P.A).left ≫ 𝟙 _
    rw [Category.comp_id]
  · change (padd D.P.A (snd T D.P.A) (toUnit _ ≫ D.c α)).left =
      (snd T D.P.A).left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left
    rw [← Over.comp_left]; congr 1
    simp only [padd]
    rw [← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
  · change (toUnit (T ⊗ D.P.A) ≫ D.c α).left = (snd T D.P.A).left ≫ (toUnit D.P.A ≫ D.c α).left
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
  · change (toUnit (T ⊗ D.P.A) ≫ η[D.P.A]).left = (snd T D.P.A).left ≫ (toUnit D.P.A ≫ η[D.P.A]).left
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]

theorem same_exists : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (G : Over (Spec (CommRingCat.of R))) (L : LB G.left), L.IsLB → ∀ k : ℕ, (∀ σ : H0 L k, ∃ σ', SameG σ σ') ∧ (∀ σ', ∃ σ : H0 L k, SameG σ σ') ∧ (∀ f : ∀ α, D.SecB k α, ∃ f', SameB f f') ∧ ∀ f', ∃ f : ∀ α, D.SecB k α, SameB f f' := by
  intro R _ _ D G L _ k
  refine ⟨fun σ => ?_, fun σ' => ?_, fun f => ?_, fun f' => ?_⟩
  · exact exists_pull (snd _ G).left (fun _ => (Category.comp_id _).symm) σ
  · exact exists_push (φ := fun _ : Fin 1 => 𝟙 G.left) (snd _ G).left (λ_ G).inv.left (unit_inv_snd G)
      (snd_unit_inv G) (fun _ => (Category.comp_id _).symm) σ'
  · choose f' hf' using fun α => exists_pull (snd _ D.P.A).left (famφT_eq D (𝟙_ _) α) (f α)
    exact ⟨f', hf'⟩
  · choose f hf using fun α => exists_push (snd _ D.P.A).left (λ_ D.P.A).inv.left (unit_inv_snd _)
      (snd_unit_inv _) (famφT_eq D (𝟙_ _) α) (f' α)
    exact ⟨f, hf⟩

end GlobalTheory.UnitSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductSupportInSubgroupTheta
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.MulSupp

section
variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem sval_eq_zero (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J}
    (hJ : Good L z J) : sval s r z J = 0 :=
  (congrArg (gs r z _) (h _)).trans ((gs_eq r z _ (hJ.mem φ r) _).trans ((congrArg _ (map_zero _)).trans (map_zero _)))

theorem exists_sub_sum {N : Type} (a : LB.Sec (LB.LinComb L φ ε)) (p : N → LB.Sec (LB.LinComb L φ ε)) (s : Finset N) :
    ∃ d : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval d r z J = sval a r z J - ∑ i ∈ s, sval (p i) r z J := by
  refine ⟨⟨fun j => a.f j - ∑ i ∈ s, (p i).f j, fun i j => ?_⟩, fun Z r z J hJ => ?_⟩
  · rw [map_sub, map_sub, map_sum, map_sum, mul_sub, Finset.mul_sum, a.compat]
    exact congrArg _ (Finset.sum_congr rfl fun b _ => (p b).compat i j)
  · have hm := hJ.mem φ r
    refine (gs_eq r z _ hm _).trans ?_
    refine (congrArg _ (map_sub _ _ _)).trans ((map_sub _ _ _).trans (congrArg₂ (· - ·) (gs_eq r z _ hm _).symm ?_))
    refine (congrArg _ (map_sum _ _ _)).trans ((map_sum _ _ _).trans (Finset.sum_congr rfl fun b _ => ?_))
    exact (gs_eq r z _ hm _).symm
end

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

noncomputable def cubAt (α β : D.X) {Z : Scheme.{0}} (ψ : Z ⟶ D.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
    (ψ ≫ (lift (toUnit _ ≫ D.c α) (lift (toUnit _ ≫ D.c β) (𝟙 D.P.A))).left) z J

theorem val_pull_cub (α β : D.X) {Y : Over (Spec (CommRingCat.of R))} (p : Y ⟶ D.P.A) {Z : Scheme.{0}}
    (r : Z ⟶ Y.left) (z : Z) {J} (hJ : Good D.P.L z J) :
    val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift (toUnit _ ≫ D.c α) (lift (toUnit _ ≫ D.c β) p)).left) r z J = cubAt D α β (r ≫ p.left) z J := by
  refine (val_pull hJ _ _ _).trans ?_
  have e : lift (toUnit _ ≫ D.c α) (lift (toUnit _ ≫ D.c β) p) =
      p ≫ lift (toUnit _ ≫ D.c α) (lift (toUnit _ ≫ D.c β) (𝟙 D.P.A)) := by
    simp only [comp_lift, comp_toUnit_assoc, Category.comp_id]
  rw [e, Over.comp_left, ← Category.assoc]
  rfl

theorem exists_prod (T : Over (Spec (CommRingCat.of R))) (k l : ℕ) (α β : D.X) (a : SecBT D T k α) (b : SecBT D T l β) :
    ∃ p : SecBT D T (k + l) (α + β), ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J →
      sval p r z J = sval a r z J * sval b r z J * (cubAt D α β (r ≫ (snd T D.P.A).left) z J).val := by
  obtain ⟨p, hp⟩ := exists_sec D.P.isLB (φ' := famφT D T (α + β)) (ε' := DegPre.famε (k + l)) (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (Fintype.prod_sum_type _)
        (prod_cub (toUnit _ ≫ D.c α) (toUnit _ ≫ D.c β) (snd T D.P.A) h))).trans ?_
      have e₀ : ∀ u, padd D.P.A (snd T D.P.A) u = u * snd T D.P.A :=
        fun u => mul_comm (snd T D.P.A) u
      have e₁ : toUnit (T ⊗ D.P.A) ≫ D.c (α + β) = (toUnit _ ≫ D.c α) * (toUnit _ ≫ D.c β) := by
        rw [D.c_add]; exact MonObj.comp_mul _ _ _
      have e₂ : toUnit (T ⊗ D.P.A) ≫ η[D.P.A] = 1 := rfl
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, famφT, DegPre.famε, e₀, e₁, e₂, Matrix.cons_val]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      push_cast
      module)
    (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.mulSec a b) (genSec (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift (toUnit _ ≫ D.c α) (lift (toUnit _ ≫ D.c β) (snd T D.P.A))).left) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _)))
  refine ⟨p, fun Z r z J hJ => (hp Z r z J hJ).trans ?_⟩
  exact (H1.SectionArithmetic.sval_mulSec _ _ r z hJ).trans (congrArg₂ (· * ·) (H1.SectionArithmetic.sval_mulSec _ _ r z hJ)
    ((sval_genSec _ _ r z hJ).trans (congrArg Units.val (val_pull_cub D α β _ r z hJ))))

variable {D} {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem val_coord_mul {e : ℕ} (g : GtCoord I D e G) (α β : D.X) {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e G).left)
    (z : Z) {J} (hJ : Good D.P.L z J) :
    val (g.t (α + β)) x z J * cubAt D α β (x ≫ g.pG.left) z J = val (g.t α) x z J * val (g.t β) x z J := by
  have E := val_corr hJ (g.t_mul α β) x
  exact ((val_mul hJ _ _ _).trans (congrArg _ (val_pull_cub D α β g.pG x z hJ))).symm.trans (E.trans (val_mul hJ _ _ _))

theorem level {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} (U : PreU I D A G) (Λ : AddSubgroup D.X) (k l : ℕ)
    (σ : U.SecGT (𝟙_ _) k) (σ' : U.SecGT (𝟙_ _) l) (σ'' : U.SecGT (𝟙_ _) (k + l)) (f) (f') (f'')
    (h : U.ExpT (𝟙_ _) k σ f) (h' : U.ExpT (𝟙_ _) l σ' f') (h'' : U.ExpT (𝟙_ _) (k + l) σ'' f'')
    (hm : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J →
      sval σ'' r z J = sval σ r z J * sval σ' r z J)
    (hf : ∀ α ∉ Λ, ∀ j, (f α).f j = 0) (hf' : ∀ α ∉ Λ, ∀ j, (f' α).f j = 0) (χ₀ : D.X) (hχ : χ₀ ∉ Λ) (e : ℕ)
    (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left)
    (hr : r ≫ (snd _ D.P.A).left = x ≫ (U.gt e).pG.left) (z : Z) (J) (hJ : Good D.P.L z J) :
    sval (f'' χ₀) r z J = 0 := by
  classical
  obtain ⟨s, hs⟩ := h e
  obtain ⟨s', hs'⟩ := h' e
  obtain ⟨s'', hs''⟩ := h'' e
  have c₁ : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left),
      (x ≫ (lift (toUnit _) (fstG I e G)).left) ≫ (snd (𝟙_ _) G).left = x ≫ (fstG I e G).left := fun Z x =>
    (Category.assoc _ _ _).trans (congrArg (fun q => x ≫ q.left) (lift_snd (toUnit _) (fstG I e G)))
  have c₂ : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left),
      r ≫ (snd _ D.P.A).left = x ≫ (U.gt e).pG.left →
      r ≫ (fst (𝟙_ _) D.P.A).left = (x ≫ (lift (toUnit _) (fstG I e G)).left) ≫ (fst (𝟙_ _) G).left := by
    intro Z x r hr
    have a₁ : fst (𝟙_ _) D.P.A = snd _ D.P.A ≫ toUnit _ := toUnit_unique _ _
    have a₂ : (U.gt e).pG ≫ toUnit _ = lift (toUnit _) (fstG I e G) ≫ fst (𝟙_ _) G := toUnit_unique _ _
    rw [a₁, Over.comp_left, ← Category.assoc, hr]
    exact (Category.assoc _ _ _).trans ((congrArg (fun q => x ≫ q.left) a₂).trans (Category.assoc _ _ _).symm)
  have ex : ∀ (g : D.X) (p : D.X × D.X), ∃ q : SecBT D (𝟙_ _) (k + l) g,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J →
      sval q r z J = if p.1 + p.2 = g then
        sval (f p.1) r z J * sval (f' p.2) r z J * (cubAt D p.1 p.2 (r ≫ (snd _ D.P.A).left) z J).val else 0 := by
    intro g p
    by_cases hp : p.1 + p.2 = g
    · subst hp
      simpa only [if_true] using exists_prod D (𝟙_ _) k l p.1 p.2 (f p.1) (f' p.2)
    · exact ⟨H1.SectionArithmetic.secZero _, fun Z r z J hJ => by rw [if_neg hp]; exact sval_eq_zero _ (fun _ => rfl) r z hJ⟩
  choose q hq using ex
  choose d hd using fun g => exists_sub_sum (f'' g) (q g) (s ×ˢ s')
  let S : Finset D.X := s'' ∪ (s ×ˢ s').image (fun p => p.1 + p.2)
  choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
  by_cases hS : χ₀ ∈ S
  swap
  · exact (hs'' Z x _ r (c₁ Z x) hr (c₂ Z x r hr) z JG J hJG hJ).1 χ₀ fun h => hS (Finset.mem_union_left _ h)
  have H := sval_eq_zero_of_sum_mul_coord R I D e G (U.gt e) (𝟙_ _ ⊗ D.P.A) (snd _ _) (Fin 4) (famφT D (𝟙_ _))
    (DegPre.famε (k + l)) d S (fun Z x r hr z J hJ => by
      choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
      obtain ⟨-, E⟩ := hs Z x _ r (c₁ Z x) hr (c₂ Z x r hr) z JG J hJG hJ
      obtain ⟨-, E'⟩ := hs' Z x _ r (c₁ Z x) hr (c₂ Z x r hr) z JG J hJG hJ
      obtain ⟨E₀, E''⟩ := hs'' Z x _ r (c₁ Z x) hr (c₂ Z x r hr) z JG J hJG hJ
      rw [hm _ _ z JG hJG, pow_add, _root_.mul_mul_mul_comm, E, E', Finset.sum_mul_sum, ← Finset.sum_product'] at E''
      simp only [hd _ Z r z J hJ, hq _ _ Z r z J hJ, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
      rw [sub_eq_zero, ← Finset.sum_subset Finset.subset_union_left (fun g _ hg => by rw [E₀ g hg, zero_mul]), ← E'',
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun p hp => ?_
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq]
      rw [if_pos (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun p : D.X × D.X => p.1 + p.2) hp)), hr,
        _root_.mul_mul_mul_comm, ← Units.val_mul, ← val_coord_mul (U.gt e) p.1 p.2 x z hJ, Units.val_mul]
      ring) χ₀ hS Z x r hr z J hJ
  rw [hd χ₀ Z r z J hJ, Finset.sum_eq_zero, sub_zero] at H
  · exact H
  intro p _
  rw [hq χ₀ p Z r z J hJ]
  split_ifs with hp
  · by_cases h₁ : p.1 ∈ Λ
    · have h₂ : p.2 ∉ Λ := fun h₂ => hχ (hp ▸ Λ.add_mem h₁ h₂)
      rw [sval_eq_zero _ (hf' _ h₂) r z hJ, mul_zero, zero_mul]
    · rw [sval_eq_zero _ (hf _ h₁) r z hJ, zero_mul, zero_mul]
  · rfl

theorem main : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (Λ : AddSubgroup D.X) (k l : ℕ) (σ : U.SecGT (𝟙_ _) k) (σ' : U.SecGT (𝟙_ _) l) (σ'' : U.SecGT (𝟙_ _) (k + l)) f f' f'', U.ExpT (𝟙_ _) k σ f → U.ExpT (𝟙_ _) l σ' f' → U.ExpT (𝟙_ _) (k + l) σ'' f'' → (∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ'' r z J = sval σ r z J * sval σ' r z J) → (∀ α ∉ Λ, ∀ j, (f α).f j = 0) → (∀ α ∉ Λ, ∀ j, (f' α).f j = 0) → ∀ α ∉ Λ, ∀ j, (f'' α).f j = 0) := by
  intro V _ _ _ hV D A G _ _ U Λ k l σ σ' σ'' f f' f'' h h' h'' hm hf hf' χ₀ hχ
  have := hV.1
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of V)))).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of V)))
  have eV : V ≃+* Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of V)).symm.commRingCatIsoToRingEquiv
  have : IsNoetherianRing Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) := isNoetherianRing_of_ringEquiv V eV
  have : Nontrivial Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) := eV.symm.nontrivial
  have : IsLocalRing Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) :=
    IsLocalRing.of_surjective' eV.toRingHom eV.surjective
  refine sec_eq_zero_of_sval_finite_level V (IsLocalRing.maximalIdeal V) (𝟙_ _) D.P.A (fun a ha => ?_) _ D.P.L D.P.isLB
    (Fin 4) _ _ (f'' χ₀) (fun e => LiftTest.main V _ D e G (U.gt e) (𝟙_ _ ⊗ D.P.A) (snd _ _) _ D.P.L D.P.isLB _ _ _ (f'' χ₀)
      (level U Λ k l σ σ' σ'' f f' f'' h h' h'' hm hf hf' χ₀ hχ e))
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  intro hu
  have hu' : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) := hu
  have := hu'.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom
  rw [Iso.inv_hom_id_apply] at this
  exact ha this

end GlobalTheory.MulSupp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiZeroMulRigV
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem psi_zero_mul_rigV : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1), PsiRel D (TF (R := R) F) s₀ → (∃ j, (s₀ 0).f j ≠ 0) → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → val (Z := (TF (R := R) F).left) (D.psi (0)) (jFK (R := R) F) z J * rigV D z J = 1 := by
  intro R _ _ D F _ _ s₀ H hs z J hJ
  have hc : cT D (DegPre.BF D F) 0 = 1 := by
    have h := DVR.cPoint_add D (DegPre.BF D F) 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have : IsIntegral (DegPre.BF D F).left :=
    isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (TF (R := R) F)
  let ζ : (TF (R := R) F).left ⟶ (DegPre.BF D F).left := (DegPre.zF D F).left
  let p : DegPre.BF D F ⟶ TF (R := R) F := fst _ _
  have hζ : ζ ≫ p.left = 𝟙 _ := by
    show (DegPre.zF D F ≫ p).left = _
    rw [show DegPre.zF D F ≫ p = 𝟙 _ from lift_fst _ _]
    rfl
  let κ₀ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
  let J' : ((DegPre.BF D F).left ⟶ D.P.A.left) → D.P.L.ι := fun ψ => J (ζ ≫ ψ)
  have hJ' : Good D.P.L (ζ z) J' := fun ψ => hJ (ζ ≫ ψ)
  have e := H 0 (DegPre.BF D F) p (p ≫ κ₀) (snd _ _) (ζ z) J' hJ'
  rw [hc, _root_.mul_one, show lift p (snd _ _) = 𝟙 (DegPre.BF D F) from lift_fst_snd] at e
  have hne : sval (s₀ 0) (𝟙 (DegPre.BF D F).left) (ζ z) J' ≠ 0 :=
    sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s₀ 0) hs _ (𝟙 _) (ζ z) J' hJ'
  have e1 : (val (D.psi 0) (p ≫ κ₀).left (ζ z) J' * rigV D (ζ z) J').val = 1 :=
    (mul_eq_right₀ hne).1 e.symm
  have n1 := (values_natural _ _ _ _ D.P.L _ _ _ (p ≫ κ₀).left ζ z J hJ).2.2.1 (D.psi 0)
  have n2 := (values_natural _ _ _ _ D.P.L PUnit (fun _ => eSec D.P.A) (fun _ => 1)
    (DegPre.BF D F).hom ζ z J hJ).2.2.1 D.rig
  have a1 : ζ ≫ (p ≫ κ₀).left = jFK (R := R) F := by
    show ζ ≫ p.left ≫ jFK (R := R) F = _
    rw [← Category.assoc, hζ, Category.id_comp]
  have a2 : ζ ≫ (DegPre.BF D F).hom = (TF (R := R) F).hom := Over.w (DegPre.zF D F)
  rw [a1] at n1
  rw [a2] at n2
  apply Units.ext
  have e2 := congrArg (ζ.stalkMap z).hom e1
  rw [map_one, Units.val_mul, map_mul] at e2
  rw [Units.val_mul, Units.val_one]
  exact (congrArg₂ (· * ·) n1 n2).trans e2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaOperatorsProjectiveRepresentationStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.thetaOperators_projective_representation : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → ∃ Φ : ∀ (p : QkPt D.toPre F k), Frm D.toPre F k p.g.b → (Fam D.toPre F k →ₗ[F] Fam D.toPre F k), (∀ p w, w.IsGen → Function.Bijective (Φ p w) ∧ ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ p w s) ∧ (∀ p w, w.IsGen → ∀ c : F, c ≠ 0 → ∃ w', w'.IsGen ∧ Φ p w' = c • Φ p w) ∧ (∀ p w w', w.IsGen → w'.IsGen → ∃ c : F, c ≠ 0 ∧ Φ p w' = c • Φ p w) ∧ (∀ p p' w, w.IsGen → QkPt.Equiv D.toPre F p p' → ∃ w', w'.IsGen ∧ Φ p' w' = Φ p w) ∧ (∀ p p' p'' w w', w.IsGen → w'.IsGen → QkAdd p p' p'' → ∃ w'', w''.IsGen ∧ Φ p'' w'' = Φ p w ∘ₗ Φ p' w') ∧ ∀ p w, p.y = 0 → p.g.IsZero → FrmOne w → Φ p w = LinearMap.id := by
  first | exact @GlobalTheory.UT.PhiProj.phi_projective | exact GlobalTheory.UT.PhiProj.phi_projective | (intros; apply GlobalTheory.UT.PhiProj.phi_projective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismCharacterMapConstantStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_endomorphism_character_map_constant : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (aG : G ⟶ G), IsMonHom aG → ∃ h : D.toPre.X →+ D.toPre.X, ∀ e, ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X ⟶ splitTorus _ D.toPre.X, TorusEndOf D.toPre.X h t ∧ (U.gt e).i ≫ (Over.pullback (thick R I e)).map aG = t ≫ (U.gt e).i := by
  first | exact @GlobalTheory.unifPre_end_character_const | exact GlobalTheory.unifPre_end_character_const | (intros; apply GlobalTheory.unifPre_end_character_const <;> assumption)
end

