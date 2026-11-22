import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0129
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0130
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0015
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0012
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0125

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAutomorphismInducingFrobeniusAllDegreesStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_automorphism_inducing_frobenius_all_degrees : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p : QkPt D.toPre F k, ∃ ψ : (TFK (R := R) F ⊗ A.A) ≅ (TFK (R := R) F ⊗ A.A), ∀ (n N : ℕ), 1 ≤ n → N = k * n → ∀ q : QkPt D.toPre F N, q.y = n • p.y → q.g = p.g → IndAt U.toUnifPre F N q ψ.hom := by
  first | exact @GlobalTheory.InducingAut.exists_aut | exact GlobalTheory.InducingAut.exists_aut | (intros; apply GlobalTheory.InducingAut.exists_aut <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEndomorphismAlgebraisingThickenings
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EndAlg

variable {X X' : Scheme.{0}} {κ : Type}

theorem eval₂_scale {σ R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (c : A) (x : σ → A)
    {P : MvPolynomial σ R} {e : ℕ} (hP : P.IsHomogeneous e) :
    MvPolynomial.eval₂ φ (fun j => x j * c) P = MvPolynomial.eval₂ φ x P * c ^ e := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' := hP (MvPolynomial.mem_support_iff.mp hd)
  simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, _root_.mul_one, Finsupp.sum] at hd'
  rw [← hd']
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, _root_.mul_assoc]

theorem gs_eval {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (φ : X' ⟶ X) (z : X') (U : X.Opens)
    (h : φ z ∈ U) (x : κ → Γ(X, U)) (P : MvPolynomial κ R) :
    gs φ z U (MvPolynomial.eval₂Hom (cst f U) x P) =
      MvPolynomial.eval₂ ((X'.presheaf.germ ⊤ z trivial).hom.comp (cst (φ ≫ f) ⊤)) (fun j => gs φ z U (x j)) P := by
  rw [gs_eq φ z U h, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left]
  congr 1
  · ext r
    simp only [RingHom.comp_apply]
    rw [← gs_eq φ z U h]
    simp only [GlobalTheory.AbLaw.cst, rs, RingHom.comp_apply]
    rw [gs_res φ z le_top h, gs_eq φ z ⊤ trivial]
    have hid : X'.presheaf.map (homOfLE (le_top : (⊤ : X'.Opens) ≤ ⊤)).op = 𝟙 _ := by
      rw [show (homOfLE (le_top : (⊤ : X'.Opens) ≤ ⊤)) = 𝟙 _ from Subsingleton.elim _ _]
      exact X'.presheaf.map_id _
    rw [hid]
    simp only [CommRingCat.hom_id, RingHom.id_apply]
    rfl
  · funext j
    simp only [Function.comp_apply]
    exact (gs_eq φ z U h _).symm

theorem isUnit_gs_iff (r : X' ⟶ X) (z : X') (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h a]
  refine (X'.mem_basicOpen (U := r ⁻¹ᵁ U) ((r.app U).hom a) z h).symm.trans ?_
  rw [← Scheme.Hom.preimage_basicOpen]
  rfl

theorem exists_pull {M : LB X} (s : LB.Sec M) (π : X' ⟶ X) :
    ∃ t : LB.Sec (M.pull π), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (J), Good M z J →
      sval t r z J = gs (r ≫ π) z _ (s.f (J (r ≫ π))) := by
  have hle : ∀ j : PUnit → M.ι, LB.wchart M (fun _ : PUnit => π) j ≤ π ⁻¹ᵁ M.U (j ⟨⟩) :=
    fun _ _ hy => Set.mem_iInter.1 hy ⟨⟩
  refine ⟨⟨fun j => (X'.presheaf.map (homOfLE (hle j)).op).hom ((π.app (M.U (j ⟨⟩))).hom (s.f (j ⟨⟩))),
    fun i j => ?_⟩, ?_⟩
  · refine ReciprocityTheory.ChartRestriction.G.DVR.app_compat_generic π (hle i) (hle j) (s.f _) (s.f _) _ (s.compat _ _) _ ?_
    show (∏ k : PUnit, _) = _
    rw [Fintype.prod_unique, zpow_one]
  · intro Z r z J hJ
    have hm := hJ.mem (fun _ : PUnit => π) r
    have hz : (r ≫ π) z ∈ M.U (J (r ≫ π)) := hJ (r ≫ π)
    show gs r z _ ((X'.presheaf.map (homOfLE (hle _)).op).hom ((π.app _).hom (s.f _))) = _
    rw [gs_res r z (hle _) hm, gs_pull r π z _ hz]

theorem exists_prod {H : LB X} (hH : H.IsLB) (p g : X' ⟶ X) (t : ℤ) (s : LB.Sec H)
    (u : LB.Sec (LB.LinComb H (K := Fin 2) ![p, g] ![t, -1])) :
    ∃ w : LB.Sec (LB.LinComb H (K := PUnit) (fun _ => p) (fun _ => t)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (J), Good H z J →
        sval w r z J = gs (r ≫ g) z _ (s.f (J (r ≫ g))) * sval u r z J := by
  obtain ⟨t0, ht0⟩ := exists_pull s g
  have hF : FormEq (Sum.elim (fun _ : PUnit => g) ![p, g]) (Sum.elim (fun _ : PUnit => (1 : ℤ)) ![t, -1])
      (fun _ : PUnit => p) (fun _ => t) := by
    intro U _ h
    simp [Fintype.prod_sum_type, Fin.prod_univ_two]
  obtain ⟨w, hw⟩ := exists_sec hH hF (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.mulSec t0 u)
  refine ⟨w, fun Z r z J hJ => ?_⟩
  rw [hw Z r z J hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_mulSec t0 u r z hJ, ht0 Z r z J hJ]

private theorem gs_sec_chart_transition {X Z : Scheme.{0}} {H : LB X} (s : LB.Sec H) (ψ : Z ⟶ X) (z : Z) (k k' : H.ι)
    (hk : ψ z ∈ H.U k) (hk' : ψ z ∈ H.U k') :
    gs ψ z (H.U k) (s.f k) = gs ψ z (H.U k ⊓ H.U k') (H.g k k' : Γ(X, H.U k ⊓ H.U k')) * gs ψ z (H.U k') (s.f k') := by
  have hkk : ψ z ∈ H.U k ⊓ H.U k' := TopologicalSpace.Opens.mem_inf.2 ⟨hk, hk'⟩
  rw [← gs_res ψ z (inf_le_left : H.U k ⊓ H.U k' ≤ H.U k) hkk, s.compat k k', gs_mul ψ z _ hkk,
    gs_res ψ z inf_le_right hkk]

theorem exists_end_of_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ f : ∀ e, (thickObj R I e Y).left ⟶ Y.left, (∀ e, f e ≫ Y.hom = pullback.fst Y.hom (thick R I e) ≫ Y.hom) → (∀ e, thickMap R I e Y ≫ f (e + 1) = f e) → ∃ g : Y ⟶ Y, ∀ e, pullback.fst Y.hom (thick R I e) ≫ g.left = f e := by
  intro R _ _ _ I hI Y hsm hpr f hf hfc
  obtain ⟨H, hH, n, s, hva⟩ := id hpr
  obtain ⟨t, m, u, hcov, hu⟩ := GlobalTheory.T.exists_compatible_generatingSections_all_thickenings R I Y H n s hsm hH hva f hfc
  have hw0 : ∀ e (i : Fin (n + 1)) (j : Fin (m + 1)), ∃ w : LB.Sec (LB.LinComb H (K := PUnit)
      (fun _ => pullback.fst Y.hom (thick R I e)) (fun _ => t)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e Y).left) (z : Z) (J), Good H z J →
        sval w r z J = gs (r ≫ f e) z _ ((s i).f (J (r ≫ f e))) * sval (u e j) r z J :=
    fun e i j => exists_prod hH (pullback.fst Y.hom (thick R I e)) (f e) t (s i) (u e j)
  choose w hw using hw0
  have hS0 : ∀ (i : Fin (n + 1)) (j : Fin (m + 1)), ∃ S : LB.Sec (LB.LinComb H (K := PUnit)
      (fun _ => 𝟙 Y.left) (fun _ => t)),
      ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e Y).left) (z : Z) (J), Good H z J →
        sval S (r ≫ pullback.fst Y.hom (thick R I e)) z J = sval (w e i j) r z J := by
    intro i j
    refine GlobalTheory.T.exists_section_linearCombination_of_compatible_thickenings R I hI Y hsm hpr Y.left H PUnit (fun _ => 𝟙 Y.left) (fun _ => t)
      (fun e _ => pullback.fst Y.hom (thick R I e)) hH (fun e k => Category.comp_id _) (fun e => w e i j) ?_
    intro e z J hJ
    rw [hw (e + 1) i j _ _ z J hJ, hw e i j _ _ z J hJ, hfc e, Category.id_comp, hu e j z J hJ]
  choose S hS using hS0
  have hN : (LB.LinComb H (K := PUnit) (fun _ => 𝟙 Y.left) (fun _ => t)).IsLB := LB.isLB_linComb hH _ _
  have key : ∀ e (z : (thickObj R I e Y).left) (k' : PUnit → H.ι),
      pullback.fst Y.hom (thick R I e) z ∈ H.U (k' ⟨⟩) →
      ∃ J, Good H z J ∧ f e z ∈ H.U (J (f e)) ∧ ∀ i j,
        gs (pullback.fst Y.hom (thick R I e)) z
            ((LB.LinComb H (K := PUnit) (fun _ => 𝟙 Y.left) (fun _ => t)).U k') ((S i j).f k') =
          gs (f e) z (H.U (J (f e))) ((s i).f (J (f e))) * sval (u e j) (𝟙 _) z J := by
    intro e z k' hz
    obtain ⟨J, hJ, hJk⟩ := exists_good H hH z (fun _ : PUnit => 𝟙 _ ≫ pullback.fst Y.hom (thick R I e))
      (fun _ => k' ⟨⟩) (fun _ _ _ => rfl) (fun _ => by simpa using hz)
    refine ⟨J, hJ, hJ (f e), fun i j => ?_⟩
    have h1 := (hS i j e _ (𝟙 _) z J hJ).trans (hw e i j _ (𝟙 _) z J hJ)
    rw [sval_of (S i j) _ z J k' (fun k => by cases k; simpa using hJk ⟨⟩)] at h1
    rw [Category.id_comp, Category.id_comp] at h1
    exact h1
  have hcov' : (⨆ i, ⨆ j, nonzeroLocus (S i j)) = ⊤ := by
    have hjac : I ≤ (⊥ : Ideal R).jacobson := by have := hI; exact IsAdicComplete.le_jacobson_bot (I := I)
    have : IsProper Y.hom := GlobalTheory.AbLaw.isProper_of_isProjBy R Y.left Y.hom hpr
    refine GlobalTheory.T.open_eq_top_of_contains_special_part_universallyClosed R I hjac Y _ fun z => ?_
    have hz1 : z ∈ ⨆ j, nonzeroLocus (u 0 j) := by rw [hcov]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hz1
    unfold nonzeroLocus at hj
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hj
    have hz2 : f 0 z ∈ ⨆ i, nonzeroLocus (s i) := by rw [hva.1]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz2
    unfold nonzeroLocus at hi
    obtain ⟨kk0, hkk0⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    have hkU : z ∈ LB.wchart H ![pullback.fst Y.hom (thick R I 0), f 0] k := Scheme.basicOpen_le _ _ hk
    have hq : pullback.fst Y.hom (thick R I 0) z ∈ H.U (k 0) := Set.mem_iInter.1 hkU 0
    obtain ⟨J, hJ, hJe, hv⟩ := key 0 z (fun _ => k 0) hq
    have hqN : pullback.fst Y.hom (thick R I 0) z ∈
        (LB.LinComb H (K := PUnit) (fun _ => 𝟙 Y.left) (fun _ => t)).U (fun _ => k 0) :=
      Set.mem_iInter.2 fun _ => hq
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩⟩
    unfold nonzeroLocus
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => k 0, ?_⟩
    rw [← isUnit_gs_iff _ _ _ hqN, hv i j]
    refine IsUnit.mul ?_ ?_
    · have hm0 : f 0 z ∈ H.U kk0 := Scheme.basicOpen_le _ _ hkk0
      have hu0 := (isUnit_gs_iff (f 0) z (H.U kk0) hm0 ((s i).f kk0)).2 hkk0
      rw [gs_sec_chart_transition (s i) (f 0) z kk0 (J (f 0)) hm0 hJe] at hu0
      exact isUnit_of_mul_isUnit_right hu0
    · have hm := hJ.mem ![pullback.fst Y.hom (thick R I 0), f 0] (𝟙 _)
      rw [sval_of (u 0 j) (𝟙 _) z J _ (fun _ => rfl), sec_trans (u 0 j) (𝟙 _) z hm hkU]
      exact (Units.isUnit _).mul ((isUnit_gs_iff _ _ _ hkU _).2 hk)
  have hrel : ∀ i i' j j' k, (S i j).f k * (S i' j').f k = (S i j').f k * (S i' j).f k := by
    intro i i' j j' k
    have hF : (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.X 2 * MvPolynomial.X 3 :
        MvPolynomial (Fin 4) R).IsHomogeneous 2 :=
      ((MvPolynomial.isHomogeneous_X R 0).mul (MvPolynomial.isHomogeneous_X R 1)).sub
        ((MvPolynomial.isHomogeneous_X R 2).mul (MvPolynomial.isHomogeneous_X R 3))
    have h := GlobalTheory.T.homogeneousForm_sections_eq_zero_of_thickenings R I hI Y hsm hpr _ (Fin 4) ![S i j, S i' j', S i j', S i' j] 2 _ hN hF ?_ k
    · simpa [sub_eq_zero] using h
    · intro e z k hz
      obtain ⟨J, hJ, hJe, hv⟩ := key e z k (Set.mem_iInter.1 hz ⟨⟩)
      rw [gs_eval Y.hom _ z _ hz]
      simp [hv]
      ring
  have hhom : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous d →
      (∀ k, MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst Y.hom (H.U k)) (fun i => (s i).f k) F = 0) →
      ∀ j k, MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst Y.hom ((LB.LinComb H (K := PUnit) (fun _ => 𝟙 Y.left) (fun _ => t)).U k))
        (fun i => (S i j).f k) F = 0 := by
    intro d F hF h0 j
    refine GlobalTheory.T.homogeneousForm_sections_eq_zero_of_thickenings R I hI Y hsm hpr _ (Fin (n + 1)) (fun i => S i j) d F hN hF ?_
    intro e z k hz
    obtain ⟨J, hJ, hJe, hv⟩ := key e z k (Set.mem_iInter.1 hz ⟨⟩)
    rw [gs_eval Y.hom _ z _ hz]
    simp only [hv]
    have h2 := gs_eval Y.hom (f e) z (H.U (J (f e))) hJe (fun i => (s i).f (J (f e))) F
    rw [h0, hf e] at h2
    have hz0 : gs (f e) z (H.U (J (f e))) 0 = 0 := by rw [gs_eq _ _ _ hJe, map_zero, map_zero]
    rw [eval₂_scale _ (sval (u e j) (𝟙 _) z J) (fun i => gs (f e) z (H.U (J (f e))) ((s i).f (J (f e)))) hF,
      ← h2, hz0, zero_mul]
  obtain ⟨φ, hφ, huniq⟩ := GlobalTheory.T.exists_morphism_to_projective_of_rank_one_sections R Y.left Y.hom H n s hH hva Y.left Y.hom _ m S hN hcov' hrel hhom
  refine ⟨Over.homMk φ hφ, fun e => ?_⟩
  refine huniq _ (pullback.fst Y.hom (thick R I e)) (f e) (hf e) ?_
  intro z k k' i i' j hzk hzk'
  obtain ⟨J, hJ, hJe, hv⟩ := key e z k' (Set.mem_iInter.1 hzk' ⟨⟩)
  rw [hv, hv, gs_sec_chart_transition (s i) (f e) z k (J (f e)) hzk hJe, gs_sec_chart_transition (s i') (f e) z k (J (f e)) hzk hJe]
  ring

end GlobalTheory.EndAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsWeightBundleTorusQuotientTowerAlgebraisatiStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weightBundle_torusQuotientTower_algebraisation : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (χ : s.X), ∃ O : LB a.B.left, O.IsLB ∧ (∃ u : LB.Gen (abelian₂ a.B O), u.IsGen) ∧ ∀ e, ∃ u : LB.Gen (O.pull ((t.l e).Q.q.left ≫ a.b e)), u.IsGen ∧ ∀ j, IsWt (t.l e).Q.i _ (u.s j).val χ := by
  first | exact @GlobalTheory.WtTower.exists_weight_bundle_alg | exact GlobalTheory.WtTower.exists_weight_bundle_alg | (intros; apply GlobalTheory.WtTower.exists_weight_bundle_alg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAbelianSchemeOfCompatibleThickenings
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isAbelianScheme_of_thickenings : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans V _ e) (β e)) → ∀ (B : Over (Spec (CommRingCat.of V))) (b : ∀ e, (Y e).left ⟶ B.left), (∀ e, IsAbelianScheme (Y e)) → (∀ e, IsCommMonObj (Y e)) → IsProjBy B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∃ _ : GrpObj B, IsCommMonObj B ∧ IsAbelianScheme B ∧ ∀ e, IsGrpPullback (Y e) B (thick V _ e) (b e) := by
  intro V _ _ _ _ Y _ β hβ B b hA hc hP hb hβb
  have hprop : IsProper B.hom := GlobalTheory.AbLaw.isProper_of_isProjBy V B.left B.hom hP
  have hsm : Smooth B.hom := by
    refine GlobalTheory.SmoothLimit.main V B fun e ↦ ?_
    have h : Smooth (Y e).hom := (hA e).smooth
    have he : (thickObj V (IsLocalRing.maximalIdeal V) e B).hom =
        (hb e).isoPullback.inv ≫ (Y e).hom := ((hb e).isoPullback_inv_snd).symm
    have h' : Smooth ((hb e).isoPullback.inv ≫ (Y e).hom) := inferInstance
    exact he ▸ h'
  have hconn : GeometricallyConnected B.hom :=
    GlobalTheory.ConnFibre.geometricallyConnected_of_closedFibre V B hsm hP (Y 0) (b 0) (hb 0)
      (hA 0).geomConnected
  obtain ⟨mu, io, un, H⟩ := GlobalTheory.T.exists_algebraization_group_operations_cdvr V Y β hβ B b hP inferInstance hb hβb
  obtain ⟨G, hG, hcomm⟩ := GlobalTheory.grpObj_of_thickenings V Y β hβ B b hb hβb mu io un H
  exact ⟨G, hcomm hc, ⟨hcomm hc, hsm, hprop, hconn⟩, hG⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivTorusQuotientTowerAlgebraisationStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kTriv_torusQuotientTower_algebraisation : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L := by
  first | exact @GlobalTheory.UU.Principal.kTriv_alg | exact GlobalTheory.UU.Principal.kTriv_alg | (intros; apply GlobalTheory.UU.Principal.kTriv_alg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiFunctionEqThetaOfPrimitiveLineBundle
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.PsiPrim

theorem exists_norm_three {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) (f : G ⟶ G) [IsMonHom f]
    (N : ℕ) (h : HasGen Lr.L (fsum (K := Fin 2) ![𝟙 G.left, f.left] ![((1 * N : ℕ) : ℤ), -((1 : ℕ) : ℤ)])) :
    ∃ β : LB.Gen (LB.LinComb Lr.L (K := Fin 3) ![𝟙 _, f.left, (1 : G ⟶ G).left]
      ![(N : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - N]), β.IsGen ∧
      LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ β (eSec G)) (LB.oneGen Lr.L) := by
  have h1 := h.add ((GlobalTheory.PullGenG.hasGen_one Lr).zsmul (((1 : ℕ) : ℤ) - N))
  obtain ⟨X0, hX0⟩ := h1.gen Lr.isLB (K' := Fin 3) ![𝟙 _, f.left, (1 : G ⟶ G).left]
      ![(N : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - N] (by
    simp only [fsum, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.cons_val, lf_single, Finsupp.smul_single_one,
      _root_.one_mul, Matrix.cons_val_zero, Matrix.cons_val_one])
  have hzp : eSec G ≫ (toUnit G).left = 𝟙 _ := by
    simp only [eSec, ← Over.comp_left]
    rw [show η[G] ≫ toUnit G = 𝟙 _ from toUnit_unique _ _]
    rfl
  obtain ⟨β, hβ, n⟩ := exists_normalized Lr.isLB _ _ X0 hX0 (toUnit G).left (eSec G) hzp (by
    have ha : eSec G ≫ f.left = eSec G := by
      simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
    have hb : eSec G ≫ (1 : G ⟶ G).left = eSec G := by
      show eSec G ≫ (toUnit G).left ≫ eSec G = _
      rw [← Category.assoc, hzp, Category.id_comp]
    simp only [fsum, Fin.sum_univ_three, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id,
      ha, hb, ← Finsupp.single_add]
    rw [show (N : ℤ) + -((1 : ℕ) : ℤ) + (((1 : ℕ) : ℤ) - N) = 0 by ring, Finsupp.single_zero])
  exact ⟨β, hβ, corr_one_of (fun j hj => n j hj)⟩

theorem star_smul_injective {O : Type} [CommRing O] [StarRing O] {X : Type} [AddCommGroup X] [Module O X]
    [Module.Free ℤ X] (a : O) (N : ℕ) (hN : a * star a = (N : O)) (hN1 : 1 ≤ N) {x y : X}
    (h : star a • x = star a • y) : x = y := by
  have h2 := congrArg (a • ·) h
  simp only [smul_smul, hN, Nat.cast_smul_eq_nsmul] at h2
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have h3 : (N : ℤ) • (x - y) = 0 := by
    rw [smul_sub, natCast_zsmul, natCast_zsmul, h2, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_left hN0)

theorem exists_norm_form : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.toUnifPre.OLinear O ιD ιA ιG → (∀ a, LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L)) → ∀ (w₀ : O), LBIso U.LG.L (cubeLB G ![𝟙 G, ιG.act w₀] U.LG.L) → ∀ (a : O) (N : ℕ), a * star a = (N : O) → 1 ≤ N →
    ∃ κ : LB.Gen (kapLB D.toPre (ιD.onB.act a) N 1), Normd κ ∧ ∀ y (z : (TK R).left) J, Good D.toPre.P.L z J →
      val (D.toPre.psi (a • y)) (𝟙 _) z J * rigV D.toPre (TK R).hom z J =
        val (D.toPre.psi y) (𝟙 _) z J ^ N * val κ (D.toPre.xK y) z J * rigV D.toPre (TK R).hom z J ^ N := by
  intro hL h1 h2 h3 h4 R _ _ _ I hI D A G _ _ hG U O _ _ _ ιD ιA ιG hlin hadj w₀ hprim a N hN hN1
  obtain ⟨E, eG, -, eB, eh, -⟩ := GlobalTheory.T.exists_uniformizationEndomorphism_of_linear hL R I hI D A G hG U O ιD ιA ιG hlin a
  obtain ⟨E', eG', -, -, eh', -⟩ := GlobalTheory.T.exists_uniformizationEndomorphism_of_linear hL R I hI D A G hG U O ιD ιA ιG hlin (star a)
  have hg := GlobalTheory.PullGenG.hasGen_pull U.LG U.cubG ιG w₀ a N hN (hadj a) hprim 1
  rw [← eG] at hg
  haveI := E.homG
  obtain ⟨β, hβ, nβ⟩ := exists_norm_three U.LG E.aG N hg
  obtain ⟨κ, hκ, -⟩ := GlobalTheory.T.descent_powerIso_endomorphism_abelianPart_uniformization hL R I hI D A G hG U E N 1 β hβ nβ
  have key := GlobalTheory.T.psi_comp_endomorphism_eq_pow_of_pullback_iso hL h1 h2 h3 h4 R I hI D A G hG U (AlgebraicClosure (FractionRing R)) E E'
    (by rw [eG, eG']; exact hadj a)
    (fun x y e => star_smul_injective a N hN hN1 (by rw [← eh, ← eh]; exact e)) N hN1
    (fun y => by rw [eh, eh', star_star, smul_smul, mul_comm, hN, Nat.cast_smul_eq_nsmul])
    (hg.gen U.LG.isLB _ _ (by rw [_root_.one_mul])) κ hκ
  rw [← eB]
  refine ⟨κ, hκ, fun y z J hJ => ?_⟩
  have := key y z J hJ
  rwa [eh', star_star] at this

theorem prod_kap {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (f : D.P.A ⟶ D.P.A) (N : ℕ) {U : Type} [CommGroup U]
    (h : (D.P.A.left ⟶ D.P.A.left) → U) :
    ∏ i : Fin 3, h ((![𝟙 _, f.left, (1 : D.P.A ⟶ D.P.A).left] : Fin 3 → _) i) ^
      (![(N : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - N] : Fin 3 → ℤ) i =
      h (𝟙 _) ^ (N : ℤ) * h f.left ^ (-((1 : ℕ) : ℤ)) * h (1 : D.P.A ⟶ D.P.A).left ^ (((1 : ℕ) : ℤ) - N) :=
  Fin.prod_univ_three _

theorem traceFormTwistIso_of_primitive_lineBundle : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.toUnifPre.OLinear O ιD ιA ιG → (∀ a, LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L)) → ∀ (w₀ : O) (ν : ℕ), w₀ + star w₀ = 1 → w₀ * star w₀ = (ν : O) → 1 ≤ ν → Even ν → LBIso U.LG.L (cubeLB G ![𝟙 G, ιG.act w₀] U.LG.L) → TraceFormTwistIso D.toPre ιD w₀ := by
  intro hL h1 h2 h3 h4 R _ _ _ I hI D A G _ _ hG U O _ _ _ ιD ιA ιG hlin hadj w₀ ν htr hν hν1 _ hprim
  have H := exists_norm_form hL h1 h2 h3 h4 R I hI D A G hG U O ιD ιA ιG hlin hadj w₀ hprim
  obtain ⟨κ₀, ⟨g₀, n₀⟩, v₀⟩ := H w₀ ν hν hν1
  obtain ⟨κ₁, ⟨g₁, n₁⟩, v₁⟩ := H (1 + w₀) (ν + 2) (by
    rw [star_add, star_one]; push_cast; linear_combination htr + hν) (by omega)
  have e₁ : ιD.onB.act (1 + w₀) = padd D.toPre.P.A (𝟙 _) (ιD.onB.act w₀) := by
    rw [ιD.onB.map_add, ιD.onB.map_one]
  obtain ⟨u, hu, vu⟩ := exists_gen D.toPre.P.isLB (K' := Fin 4)
    (φ' := ![(padd D.toPre.P.A (𝟙 _) (ιD.onB.act w₀)).left, 𝟙 D.toPre.P.A.left, (ιD.onB.act w₀).left,
      (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left]) (ε' := ![1, -2, -1, 2]) (fun V _ h => by
      refine (prod_sum₂ (K := Fin 3) (K' := Fin 3) (U := V) _ (prod_kap D.toPre _ ν h)
        (prod_neg _ _ (prod_kap D.toPre _ (ν + 2) h))).trans ?_
      rw [Fin.prod_univ_four, e₁]
      have o : (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]) = 1 := rfl
      rw [o]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      module)
    (LB.mulGen D.toPre.P.L _ _ _ _ κ₀ (LB.invGen D.toPre.P.L _ _ κ₁))
    (mulGen_isGen _ _ _ _ _ _ _ g₀ (invGen_isGen _ _ _ _ g₁))
  refine ⟨u, hu, corr_of_val D.toPre.P.isLB fun z J hJ => ?_, fun y => corr_of_val D.toPre.P.isLB fun z J hJ => ?_⟩
  · have a₀ := val_corr hJ n₀ (𝟙 _)
    have a₁ := val_corr hJ n₁ (𝟙 _)
    rw [val_pull hJ] at a₀ a₁
    rw [val_pull hJ, vu _ _ z J hJ, val_mul hJ, val_inv, a₀, a₁, mul_inv_cancel, val_one]
  · have t : val (D.toPre.tau y (w₀ • y)) (𝟙 _) z J = val (D.toPre.psi (y + w₀ • y)) (𝟙 _) z J *
        (val (D.toPre.psi y) (𝟙 _) z J)⁻¹ * (val (D.toPre.psi (w₀ • y)) (𝟙 _) z J)⁻¹ * (val D.toPre.rigK (𝟙 _) z J)⁻¹ :=
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
    have r : val D.toPre.rigK (𝟙 _) z J = rigV D.toPre (TK R).hom z J :=
      (val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)
    have b₀ := v₀ y z J hJ
    have b₁ := v₁ y z J hJ
    rw [add_smul, one_smul] at b₁
    rw [val_mul hJ, val_mul hJ, val_pull hJ, Category.id_comp, vu _ _ z J hJ, val_mul hJ, val_inv, t, r]
    apply Additive.ofMul.injective
    have c₀ := congrArg Additive.ofMul b₀
    have c₁ := congrArg Additive.ofMul b₁
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at c₀ c₁ ⊢
    linear_combination (norm := module) c₁ - c₀

end GlobalTheory.PsiPrim

end
end

