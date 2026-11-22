import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0119
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionLinearCombinationOfCompatibleThicke
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SecAlgLinComb
open GlobalTheory.CompleteBaseExpansion GlobalTheory.BaseExpansionExists

theorem exists_sec_linComb : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ (W : Scheme.{0}) (L : LB W) (K : Type) [Fintype K] (φ : K → (Y.left ⟶ W)) (ε : K → ℤ) (φ' : ∀ e, K → ((thickObj R I e Y).left ⟶ W)), L.IsLB → (∀ e k, pullback.fst Y.hom (thick R I e) ≫ φ k = φ' e k) → ∀ f : ∀ e, LB.Sec (LB.LinComb L (φ' e) ε), (∀ e z J, Good L z J → sval (f (e + 1)) (thickMap R I e Y) z J = sval (f e) (𝟙 _) z J) → ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e Y).left) (z : Z) (J), Good L z J → sval s (r ≫ pullback.fst Y.hom (thick R I e)) z J = sval (f e) r z J := by
  intro R _ _ I hI Y hsm hp W L K _ φ ε φ' hL hφ f hf
  obtain rfl : φ' = fun e k => (fstG I e Y).left ≫ φ k := funext fun e => funext fun k => (hφ e k).symm
  choose f' hf' using fun e => exists_in (φ := φ) (fstG I e Y).left (f e)
  obtain ⟨s', hs', -⟩ := GlobalTheory.SecAlg.existsUnique_sec R I hI Y hsm hp _ (DVR.linComb_isLB _ hL _ _) f'
    fun e z J hJ => by
      refine (hf' _ _ _ z _ (hJ.mem (fun _ : PUnit => (fstG I (e + 1) Y).left) _)).trans
        (Eq.trans ?_ (hf' _ _ _ z _ (hJ.mem (fun _ : PUnit => (fstG I e Y).left) _)).symm)
      have E : thickMap R I e Y ≫ (fstG I (e + 1) Y).left = 𝟙 _ ≫ (fstG I e Y).left :=
        ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).trans (Category.id_comp _).symm
      beta_reduce
      rw [E]
      exact gs_eq_of_sval hL _ _ _ _ (fun i => (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ φ i) E).trans (Category.assoc _ _ _))) z (hf e z) _
        (pull_le _ _ (hJ.mem (fun _ : PUnit => (fstG I e Y).left) _))
  obtain ⟨s₁, hs₁⟩ := exists_out (𝟙 _) s'
  obtain ⟨s, hs⟩ := exists_sec hL (φ' := φ) (ε' := ε)
    (fun U _ h => by simp only [Category.id_comp]) s₁
  have key : ∀ e z J, Good L z J → sval s (fstG I e Y).left z J = sval (f e) (𝟙 _) z J := by
    refine fun e z J hJ => (hs _ _ z J hJ).trans ((hs₁ _ _ z _ (hJ.mem _ _)).trans ?_)
    have hN : Good (LB.LinComb L φ ε) z (fun ψ i => J (ψ ≫ φ i)) :=
      fun ψ => hJ.mem _ ψ
    refine Eq.trans ?_ ((hs' e z _ hN).trans
      ((hf' _ _ _ z _ (hN.mem (fun _ : PUnit => (fstG I e Y).left) _)).trans ?_))
    · exact (sval_of s' _ z _ _ (fun _ => funext fun i => congrArg J (Category.assoc _ _ _))).symm
    · exact (sval_of (f e) _ z J _ (fun i => congrArg J (Category.assoc _ _ _).symm)).symm
  refine ⟨s, fun e Z r z J hJ => (sval_eq_of_id (key e) r z hJ).trans ?_⟩
  exact congrArg (fun p => sval (f e) p z J) (Category.comp_id _)

end GlobalTheory.SecAlgLinComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomogeneousFormSectionsEqZeroOfThickenings
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FormVan

variable {X X' Z : Scheme.{0}}

def zeroSec (M : LB X) : LB.Sec M := ⟨fun _ => 0, fun _ _ => by rw [map_zero, map_zero, mul_zero]⟩

theorem gs_zero (r : Z ⟶ X) (z : Z) (U : X.Opens) : gs r z U 0 = 0 := by
  by_cases h : r z ∈ U
  · rw [gs_eq r z U h, map_zero, map_zero]
  · exact dif_neg h

theorem sval_zeroSec (M : LB X) (π : X' ⟶ X) (r : Z ⟶ X') (z : Z) (J : (Z ⟶ X) → M.ι) :
    sval (zeroSec (M.pull π)) r z J = 0 := gs_zero r z _

theorem exists_pull_id {M : LB X} (τ : LB.Sec M) : ∃ s : LB.Sec (M.pull (𝟙 X)),
    ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (j : PUnit → M.ι), r z ∈ M.U (j PUnit.unit) →
      gs r z ((M.pull (𝟙 X)).U j) (s.f j) = gs r z (M.U (j PUnit.unit)) (τ.f (j PUnit.unit)) := by
  have le : ∀ j : PUnit → M.ι, (M.pull (𝟙 X)).U j ≤ M.U (j PUnit.unit) := fun j y hy => mem_pull.1 hy
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (j : PUnit → M.ι), r z ∈ M.U (j PUnit.unit) →
      gs r z ((M.pull (𝟙 X)).U j) (rs X (le j) (τ.f (j PUnit.unit))) =
        gs r z (M.U (j PUnit.unit)) (τ.f (j PUnit.unit)) :=
    fun Z r z j hj => gs_res r z (le j) (mem_pull.2 hj) _
  refine ⟨⟨fun j => rs X (le j) (τ.f (j PUnit.unit)), fun j j' => fn_ext fun y hy => ?_⟩, v⟩
  have hm : (𝟙 X : X ⟶ X) y ∈ M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit) := ⟨le j hy.1, le j' hy.2⟩
  refine ((gs_res (𝟙 X) y _ hy _).trans (v _ _ y j hm.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 X) y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 X) y _ hy _).trans
      (congrArg Units.val (gm_pull_g M (𝟙 X) (𝟙 X) y j j' hy.1 hy.2)))
      ((gs_res (𝟙 X) y _ hy _).trans (v _ _ y j' hm.2)))).symm)
  rw [Category.id_comp]
  exact (gs_res (𝟙 X) y _ hm _).symm.trans ((congrArg (gs (𝟙 X) y _) (τ.compat _ _)).trans
    ((gs_mul (𝟙 X) y _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 X) y _ hm _) (gs_res (𝟙 X) y _ hm _))))

theorem eval₂Hom_scale {κ R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (c : A) (x : κ → A)
    {P : MvPolynomial κ R} {e : ℕ} (hP : P.IsHomogeneous e) :
    MvPolynomial.eval₂Hom φ (fun j => c * x j) P = c ^ e * MvPolynomial.eval₂Hom φ x P := by
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hd : ∑ j ∈ a.support, a j = e := by
    have := hP (MvPolynomial.mem_support_iff.1 ha)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

def formSec {R : Type} [CommRing R] (p : X ⟶ Spec (CommRingCat.of R)) {N : LB X} {κ : Type} (σ : κ → LB.Sec N)
    {d : ℕ} {F : MvPolynomial κ R} (hF : F.IsHomogeneous d) : LB.Sec (pw N d) where
  f := fun k => MvPolynomial.eval₂Hom (cst p (N.U k)) (fun j => (σ j).f k) F
  compat := fun i j => by
    have c : ∀ {U V : X.Opens} (h : V ≤ U), (rs X h).comp (cst p U) = cst p V :=
      fun h => RingHom.ext (rs_cst p h)
    change rs X (inf_le_left : N.U i ⊓ N.U j ≤ N.U i) (MvPolynomial.eval₂Hom _ _ F) =
      (N.g i j ^ (d : ℤ)).val * rs X (inf_le_right : N.U i ⊓ N.U j ≤ N.U j) (MvPolynomial.eval₂Hom _ _ F)
    rw [MvPolynomial.map_eval₂Hom, MvPolynomial.map_eval₂Hom, c, c, zpow_natCast, Units.val_pow_eq_pow_val,
      ← eval₂Hom_scale _ _ _ hF]
    congr 2
    exact funext fun a => (σ a).compat i j

theorem sec_eq_zero (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (hI : IsAdicComplete I R)
    (Y : Over (Spec (CommRingCat.of R))) (hs : Smooth Y.hom) (hp : IsProjBy Y.hom) (M : LB Y.left) (hM : M.IsLB)
    (τ : LB.Sec M) (h : ∀ (e : ℕ) (z : (thickObj R I e Y).left) (k : M.ι),
      pullback.fst Y.hom (thick R I e) z ∈ M.U k → gs (pullback.fst Y.hom (thick R I e)) z (M.U k) (τ.f k) = 0)
    (k : M.ι) : τ.f k = 0 := by
  obtain ⟨s, hv⟩ := exists_pull_id τ
  have e : s = zeroSec _ := (GlobalTheory.SecAlg.existsUnique_sec R I hI Y hs hp M hM (fun _ => zeroSec _)
    (fun e z J _ => (sval_zeroSec _ _ _ z J).trans (sval_zeroSec _ _ _ z J).symm)).unique
    (fun e z J hJ => by
      have hm : (fstG I e Y).left z ∈ M.U (J ((fstG I e Y).left ≫ 𝟙 _)) := hJ ((fstG I e Y).left ≫ 𝟙 _)
      exact (hv _ _ z _ hm).trans ((h e z _ hm).trans (sval_zeroSec _ _ _ z J).symm))
    (fun e z J _ => (sval_zeroSec _ _ _ z J).trans (sval_zeroSec _ _ _ z J).symm)
  refine fn_ext fun y hy => ?_
  rw [← hv _ (𝟙 _) y (fun _ => k) hy, e, gs_zero]
  exact gs_zero _ _ _

theorem form_eq_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ (N : LB Y.left) (κ : Type) (σ : κ → LB.Sec N) (d : ℕ) (F : MvPolynomial κ R), N.IsLB → F.IsHomogeneous d → (∀ (e : ℕ) (z : (thickObj R I e Y).left) (k : N.ι), pullback.fst Y.hom (thick R I e) z ∈ N.U k → gs (pullback.fst Y.hom (thick R I e)) z (N.U k) (MvPolynomial.eval₂Hom (cst Y.hom (N.U k)) (fun j => (σ j).f k) F) = 0) → ∀ k, MvPolynomial.eval₂Hom (cst Y.hom (N.U k)) (fun j => (σ j).f k) F = 0 :=
  fun R _ _ I hI Y hs hp N _ σ d _ hN hF h k =>
    sec_eq_zero R I hI Y hs hp (pw N d) (isLB_pw hN d) (formSec Y.hom σ hF) h k

end GlobalTheory.FormVan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecZeroOfPull
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.SchurConst

theorem gs_zero {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs
  split_ifs with h
  · simp only [map_zero]
  · rfl

theorem sec_zero_of_val {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = 0)
    (j : K → L.ι) : s.f j = 0 := by
  refine fn_ext fun y hy => ?_
  obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
  rw [h y J hJ, mul_zero] at e
  exact e.trans (gs_zero _ _ _).symm

theorem sec_zero_of_pull {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K₃ : Type} [Fintype K] [Fintype K₃]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (τ : Y' ⟶ Y) (σ : Y ⟶ Y') (hστ : σ ≫ τ = 𝟙 Y)
    {φ₃ : K₃ → (Y' ⟶ X)} {ε₃ : K₃ → ℤ} (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen)
    (h : ∀ y J, Good L y J → sval s τ y J = 0) (j : K → L.ι) : s.f j = 0 := by
  have h1 := sec_zero_of_val hL (pullMulSec s τ u hu) (fun y J hJ => by
    rw [sval_pullMulSec s τ u hu _ y hJ, Category.id_comp, h y J hJ, zero_mul])
  refine sec_zero_of_val hL s (fun y J hJ => ?_) j
  have h2 : sval (pullMulSec s τ u hu) σ y J = 0 := by
    unfold sval
    rw [h1]
    exact gs_zero _ _ _
  rw [sval_pullMulSec s τ u hu _ y hJ, hστ] at h2
  exact (Units.mul_left_eq_zero _).1 h2

theorem main : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => ∀ N : ℕ, 1 ≤ N → (∀ α, ∃ t s, U.ExpF (Kbar V) N t s ∧ DegPre.FamFE D (Kbar V) N s ∧ ∃ j, (s α).f j ≠ 0) → U.FE (Kbar V) N := by
  intro hL1 hL2 V _ _ _ hV D A G _ _ U N hN hw t s hts mu α u hu hcorr
  obtain ⟨t₀, s₀, he₀, hfe₀, j, hj⟩ := hw α
  obtain ⟨a, ha⟩ := GlobalTheory.T.expansionComponents_proportional_shift_multiple hL1 hL2 V hV D A G U N hN α mu u hu ⟨t₀, s₀, he₀, j, hj⟩
  have hc : ∀ (z : (DegPre.BF D (Kbar V)).left) (b c : Kbar V),
      gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (b * c) ⊤) =
        gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) b ⊤) * gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) c ⊤) := by
    intro z b c
    rw [← gs_mul _ _ ⊤ trivial]
    simp only [DegPre.constBF, map_mul]
  have hc1 : ∀ (z : (DegPre.BF D (Kbar V)).left),
      gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) 1 ⊤) = 1 := by
    intro z
    rw [gs_eq _ _ ⊤ trivial]
    simp only [DegPre.constBF, map_one]
  have hca : ∀ (z : (DegPre.BF D (Kbar V)).left) (b : Kbar V),
      gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (b - 1) ⊤) =
        gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) b ⊤) - 1 := by
    intro z b
    rw [gs_eq _ _ ⊤ trivial, gs_eq _ _ ⊤ trivial]
    simp only [DegPre.constBF, map_sub, map_one]
  have ha1 : a = 1 := by
    by_contra hne
    apply hj
    have hinv : (DegPre.trF D (Kbar V) (-mu)).left ≫ (DegPre.trF D (Kbar V) mu).left = 𝟙 _ := by
      rw [← Over.comp_left, DVR.UUA.trF_add, neg_add_cancel, DVR.UUA.trF_zero, Over.id_left]
    refine sec_zero_of_pull D.P.isLB (s₀ α) _ _ hinv u hu (fun z J hJ => ?_) j
    have e1 := ha t₀ s₀ he₀ z J hJ
    have e2 := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ _).1 (hfe₀ mu α u hu hcorr) _ (𝟙 _) z J hJ
    rw [Category.id_comp] at e2
    have e3 : gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (a - 1) ⊤) *
        (sval (s₀ α) (DegPre.trF D (Kbar V) mu).left z J * (val u (𝟙 _) z J).val) = 0 := by
      rw [hca, _root_.sub_mul, _root_.one_mul, ← e1, ← e2, sub_self]
    have e4 := congrArg (gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) (a - 1)⁻¹ ⊤) * ·) e3
    simp only [mul_zero] at e4
    rw [← _root_.mul_assoc, ← hc, inv_mul_cancel₀ (sub_ne_zero.2 hne), hc1, _root_.one_mul] at e4
    exact (Units.mul_left_eq_zero _).1 e4
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ _).2 fun z J hJ => ?_
  rw [Category.id_comp, ha t s hts z J hJ, ha1, hc1, _root_.one_mul]

end GlobalTheory.UU.SchurConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SubsingletonOfForallIsMaximalSmulEqZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

set_option backward.isDefEq.respectTransparency false in

theorem acyclic_extendScalars_of_flat {R S : Type} [CommRing R] [CommRing S] (g : R →+* S)
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) (hn : ∀ p, n < p → IsZero (C.X p))
    (hflat : ∀ p, Module.Flat R (C.X p)) (hC : C.Acyclic) :
    (((ModuleCat.extendScalars.{0, 0, 0} g).mapHomologicalComplex _).obj C).Acyclic := by
  have : QuasiIso (0 : C ⟶ C) := ⟨fun p => (quasiIsoAt_iff_exactAt _ p (hC p)).2 (hC p)⟩
  have h := GlobalTheory.quasiIso_extendScalars_of_flat (0 : C ⟶ C) hflat hflat n hn hn g
  rw [Functor.map_zero] at h
  intro p
  have h' := (quasiIsoAt_iff_isIso_homologyMap _ p).1 (h.1 p)
  rw [HomologicalComplex.homologyMap_zero] at h'
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (isIsoZero_iff_source_target_isZero _ _).1 h' |>.1

theorem subsingleton_of_forall_isMaximal_smul_eq_zero {R M : Type} [CommRing R] [AddCommGroup M]
    [Module R M] (h : ∀ P : Ideal R, P.IsMaximal → ∃ r, r ∉ P ∧ ∀ z : M, r • z = 0) :
    Subsingleton M := by
  rw [← Module.annihilator_eq_top_iff (R := R)]
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨r, hr, hz⟩ := h P hP
  exact hr (hle (Module.mem_annihilator.2 hz))

theorem cechLB_acyclic_iff_fibres : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), Flat f → IsProjBy f → ∀ F : LB Y, F.IsLB → ((∀ P : Ideal R, P.IsMaximal → ∃ (K : Type) (_ : Field K) (χ : R →+* K), RingHom.ker χ = P ∧ ∀ (Y₀ : Scheme.{0}) (π : Y₀ ⟶ Y) (f₀ : Y₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom χ)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y₀).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f₀) (F.pull π) D).Acyclic)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F) D).Acyclic)) ∧ ((∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F) D).Acyclic) → ∀ (K : Type) [Field K] (χ : R →+* K), ∀ (Y₀ : Scheme.{0}) (π : Y₀ ⟶ Y) (f₀ : Y₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom χ)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y₀).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f₀) (F.pull π) D).Acyclic)) := by
  intro R _ _ Y f hf hproj F hF
  have := isProper_of_isProjBy R Y f hproj
  have : Y.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from f]
    infer_instance
  have hI : ∀ {κ : Type} {D : κ → Y.Opens}, (∀ i, IsAffineOpen (D i)) → ∀ s : Finset κ,
      s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i) := fun hD s hs =>
    IsAffineOpen.biInf _ (Finset.finite_toSet _) (by exact_mod_cast hs) fun i _ => hD i
  refine ⟨fun H κ _ _ D hD hc p => ?_, fun H K _ χ Y₀ π f₀ h κ _ _ D hD hc p => ?_⟩
  · rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
    refine subsingleton_of_forall_isMaximal_smul_eq_zero (R := R) fun P hP => ?_
    obtain ⟨K, _, χ, rfl, HK⟩ := H P hP
    have h' := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom χ))
    have hac := HK _ _ _ h' κ
      (fun i => pullback.fst f (Spec.map (CommRingCat.ofHom χ)) ⁻¹ᵁ D i)
      (fun i => isAffineOpen_preimage_of_isPullback h' (hD i))
      (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl)
    exact GlobalTheory.exists_smul_homology_eq_zero_of_acyclic_fibre R K χ _ (Fintype.card κ)
      (fun p hp => isZero_cechLB_X _ _ _ hp.le) (flat_cechLB_X f hF (hI hD))
      (cechLB_homology_finite_of_affine_cover R Y f F κ D hF inferInstance hproj hD hc)
      (fun q => (hac q).of_iso (cechLBBaseChangeIso hF h' (hI hD)).symm) p
  · obtain ⟨L, -, m, s, hc', hs⟩ := hproj
    have hD' : ∀ i, IsAffineOpen (nonzeroLocus (s i)) := fun i => (hs i).1
    have hac := acyclic_extendScalars_of_flat χ _ (Fintype.card (Fin (m + 1)))
      (fun p hp => isZero_cechLB_X _ _ _ hp.le) (flat_cechLB_X f hF (hI hD')) (H _ _ hD' hc')
    have h₁ := (hac p).of_iso (cechLBBaseChangeIso hF h (hI hD'))
    have : IsSeparated f₀ := MorphismProperty.of_isPullback (P := @IsSeparated) h inferInstance
    obtain ⟨e⟩ := cechLB_homology_equiv_of_affine_covers K Y₀ f₀ (F.pull π) κ D _
      (fun i => π ⁻¹ᵁ nonzeroLocus (s i)) (LB.isLB_pull hF π) inferInstance hD hc
      (fun i => isAffineOpen_preimage_of_isPullback h (hD' i))
      (by rw [← Scheme.Hom.preimage_iSup, hc']; rfl) p
    rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton] at h₁ ⊢
    exact e.subsingleton

end GlobalTheory.AbLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaSectionSupportEqUniv
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
namespace GlobalTheory.UU

theorem theta_support_eq_univ : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → (∀ α, ∃ j, (f α).f j ≠ 0) ∧ ∀ α, U.Supp (Kbar V) 2 α) := by
  intro h1 h2 V _ _ _ hV D A G _ _ U θ f hθ
  have hrel := GlobalTheory.T.thetaSupport_pair_iff_degreeTwo_sum_diff h1 h2 V hV D A G U θ f hθ
  have hodd := GlobalTheory.T.thetaExpansion_support_not_in_primeIndex_subgroup h1 h2 V hV D A G U θ f hθ
  have hw := GlobalTheory.T.lineBundleSections_torusTorsion_weightSpaces h1 h2 V hV D A G U
  have hpull := GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1
  obtain ⟨th, hth, -⟩ := hpull.1 θ
  obtain ⟨s₀, hs₀, -⟩ := hpull.2 f
  have hone := (GlobalTheory.T.expF_of_theta_degree_one h1 h2 V hV D A G U θ f hθ th s₀ hth hs₀).2.2
  have hne : ({α | ∃ j, (f α).f j ≠ 0} : Set D.X).Nonempty := by
    obtain ⟨mu, t, s, hts, j, hj⟩ := (hw 1 le_rfl).2.1 0
    obtain ⟨c, hc⟩ := hone t s hts
    refine ⟨0 + 1 • mu, (_root_.GlobalTheory.pullB_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ _).1 ⟨j, fun h0 => hj ?_⟩⟩
    rw [hc, h0, mul_zero]
  obtain ⟨hS, Λ, hΛ, hc⟩ := GlobalTheory.support_subgroup_odd_index D.X {α | ∃ j, (f α).f j ≠ 0}
    {α | U.Supp (Kbar V) 2 α} hne hrel (fun x => by
      obtain ⟨mu, hmu⟩ := (hw 2 (by norm_num)).2.1 x
      exact ⟨mu, by rw [← two_nsmul]; exact hmu⟩)
  have htop : Λ = ⊤ := by
    rcases hc with h | ⟨l, hl, -, g, hg, hgΛ⟩
    · exact h
    · refine absurd (hodd l hl g fun α hα => hgΛ α ?_) hg
      have : α ∈ (Λ : Set D.X) := by rw [hΛ]; exact hα
      exact this
  have hall : ∀ α, α ∈ ({α | ∃ j, (f α).f j ≠ 0} : Set D.X) := fun α => by
    rw [← hΛ, htop]; trivial
  refine ⟨hall, fun α => ?_⟩
  have : α ∈ ({α | U.Supp (Kbar V) 2 α} : Set D.X) := by rw [hS]; exact hall α
  exact this

end GlobalTheory.UU
end

