import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0120
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0013
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThickIsoOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0121
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0103
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicSumSectionsOfFiniteSumsOnThickenings
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.SecAdicSum

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw

theorem sumI_of_ker {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) {a b : ℕ}
    (A : Matrix (Fin b) (Fin a) R) {E Ix : Type} [AddCommGroup E] [Module R E] (ev : (Fin a → R) →ₗ[R] E)
    (v : Ix → Fin a → R) (v₀ : Fin a → R) (hv : ∀ i, A.mulVec (v i) = 0) (hv₀ : A.mulVec v₀ = 0)
    (h : ∀ e : ℕ, ∃ S : Finset Ix, ∀ T : Finset Ix, S ⊆ T → ∀ k, (v₀ - ∑ i ∈ T, v i) k ∈ I ^ (e + 1)) :
    SumI I (fun i => ev (v i)) (ev v₀) := by
  let N : Submodule R (Fin a → R) := LinearMap.ker A.mulVecLin
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I N
  refine ⟨N.map ev, (IsNoetherian.noetherian N).map ev, ⟨v₀, hv₀, rfl⟩, fun i => ⟨v i, hv i, rfl⟩, fun n => ?_⟩
  obtain ⟨S, hS⟩ := h (n + c)
  refine ⟨S, fun T hT => ?_⟩
  have m₁ : v₀ - ∑ i ∈ T, v i ∈ N := N.sub_mem hv₀ (N.sum_mem fun i _ => hv i)
  have m₂ : v₀ - ∑ i ∈ T, v i ∈ I ^ (n + c) • (⊤ : Submodule R (Fin a → R)) := by
    rw [pi_eq_sum_univ (v₀ - ∑ i ∈ T, v i)]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem_smul
      (Ideal.pow_le_pow_right (Nat.le_succ _) (hS T hT k)) Submodule.mem_top
  have m₃ := (hc (n + c) (Nat.le_add_left _ _)).le ⟨m₂, m₁⟩
  rw [Nat.add_sub_cancel] at m₃
  rw [← map_sum, ← map_sub, ← Submodule.map_smul'']
  exact ⟨_, Submodule.smul_mono le_rfl inf_le_right m₃, rfl⟩

section
variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X}
  (P : Perf f M)

theorem exists_vec (s : LB.Sec M) :
    ∃ v : Fin P.a → R, P.D₀.mulVec v = 0 ∧ ∀ i, AbLaw.rs X (P.le i) (s.f (P.ch i)) = loc₀ P v i := by
  have h : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E, hE⟩ := P.sec R (RingHom.id R) X (𝟙 X) f h
  have le : ∀ j : PUnit → M.ι, (M.pull (𝟙 X)).U j ≤ M.U (j PUnit.unit) := fun j y hy =>
    Set.mem_iInter.1 hy PUnit.unit
  let t : LB.Sec (M.pull (𝟙 X)) := ⟨fun j => AbLaw.rs X (le j) (s.f (j PUnit.unit)), fun j j' => fn_ext fun y hy => by
    have hm : y ∈ M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit) := ⟨le j hy.1, le j' hy.2⟩
    refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y _ hy.1 _)).trans (Eq.trans ?_
      ((gs_mul (𝟙 X) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 X) y _ hy _).trans
        (congrArg Units.val (gm_linComb M _ _ (𝟙 X) y j j' hy.1 hy.2)))
        ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y _ hy.2 _)))).symm)
    rw [Fintype.prod_unique, zpow_one]
    exact (gs_res (𝟙 X) y _ hm _).symm.trans ((congrArg (gs (𝟙 X) y _) (s.compat _ _)).trans
      ((gs_mul (𝟙 X) y _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 X) y _ hm _) (gs_res (𝟙 X) y _ hm _))))⟩
  obtain ⟨v, hv⟩ := E.surjective t
  refine ⟨v.1, v.2, fun i => ?_⟩
  have e := hE v i
  rw [hv] at e
  exact (AbLaw.rs_rs _ _ _).symm.trans e

theorem comp_eq_zero {g : R →+* R'} {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')}
    (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) (v : Fin P.a → R) (hv : P.D₀.mulVec v = 0)
    (h0 : ∀ i y, π y ∈ P.W i → gs π y _ (loc₀ P v i) = 0) : g ∘ v = 0 := by
  obtain ⟨E, hE⟩ := P.sec R' g X' π f' h
  have k₁ : (P.D₀.map g).mulVec (g ∘ v) = 0 := funext fun j =>
    (RingHom.map_mulVec g _ _ j).symm.trans ((congrArg g (congrFun hv j)).trans (map_zero g))
  refine congrArg Subtype.val (E.injective (a₁ := ⟨_, k₁⟩) (a₂ := ⟨0, Matrix.mulVec_zero _⟩) ?_)
  refine Seesaw.sec_ext _ _ (fun i => π ⁻¹ᵁ P.W i) (fun i _ => P.ch i) (fun i => le_pull M π (P.le i))
    (fun y => exists_mem P (π y)) fun i => ?_
  refine (hE _ i).trans (Eq.trans ?_ (hE _ i).symm)
  refine (loc_comp P h v i).trans (Eq.trans (fn_ext (b := 0) fun y hy => ?_) (by simp))
  refine (gs_pull (𝟙 X') π y _ hy _).trans ?_
  rw [Category.id_comp, h0 i y hy, gs_eq (𝟙 X') y (π ⁻¹ᵁ P.W i) hy, map_zero, map_zero]

theorem loc₀_sub_sum {Ix : Type} (v₀ : Fin P.a → R) (v : Ix → Fin P.a → R) (T : Finset Ix) (i : P.I) :
    loc₀ P (v₀ - ∑ j ∈ T, v j) i = loc₀ P v₀ i - ∑ j ∈ T, loc₀ P (v j) i := by
  simp only [loc₀, Pi.sub_apply, Finset.sum_apply, map_sub, map_sum, sub_mul, Finset.sum_mul,
    Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

end

section
variable {X Y Z : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] {φ : K → (X ⟶ Y)} {ε : K → ℤ} {R : Type} [CommRing R]
  {f : X ⟶ Spec (CommRingCat.of R)} (P : Perf f (LB.LinComb L φ ε))

theorem gs_loc₀ {s : LB.Sec (LB.LinComb L φ ε)} {v : Fin P.a → R}
    (h : ∀ i, AbLaw.rs X (P.le i) (s.f (P.ch i)) = loc₀ P v i) (r : Z ⟶ X) (z : Z) {i : P.I} (hi : r z ∈ P.W i)
    {J : (Z ⟶ Y) → L.ι} (hJ : Good L z J) :
    gs r z _ (loc₀ P v i) = (trF φ ε r z (P.ch i) fun k => J (r ≫ φ k)).val * sval s r z J := by
  rw [← h i]
  exact (gs_res r z (P.le i) hi _).trans (sec_trans s r z (P.le i hi) (hJ.mem φ r))

end

theorem gs_cst_point {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    {B : Over (Spec (CommRingCat.of R))} (b : TF (R := R) F ⟶ B) (z : (TF (R := R) F).left) (W : B.left.Opens)
    (hz : b.left z ∈ W) (c : R) : gs b.left z W (AbLaw.cst B.hom W c) =
      CoefBasic.cstH z (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) c)) := by
  have w : b.left ≫ B.hom = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom
      ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))) := by
    rw [Over.w b, Category.id_comp, CommRingCat.ofHom_comp, Spec.map_comp]
    rfl
  rw [gs_eq b.left z W hz, app_cst w W c]
  exact TopCat.Presheaf.germ_res_apply (TF (R := R) F).left.presheaf _ z hz _

theorem sumF_of_sum_on_thickenings : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (K : Type) [Fintype K] (φ : K → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (ε : K → ℤ) (Ix : Type) (n : Ix → LB.Sec (LB.LinComb D.toPre.P.L φ ε)) (n₀ : LB.Sec (LB.LinComb D.toPre.P.L φ ε)), (∀ e : ℕ, ∃ S : Finset Ix, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D.toPre.P.A).left) (z : Z) (J), Good D.toPre.P.L z J → (∀ i ∉ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J = 0) ∧ sval n₀ (r ≫ (D.toPre.prBe I e).left) z J = ∑ i ∈ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J) → ∀ (b : TF (R := R) F ⟶ D.toPre.P.A) (τ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => b.left ≫ φ i) ε)), τ.IsGen → ∀ (x : Ix → F) (x₀ : F), (∀ z J, Good D.toPre.P.L z J → (∀ i, sval (n i) b.left z J = cst F z (x i) * (val τ (𝟙 _) z J).val) ∧ sval n₀ b.left z J = cst F z x₀ * (val τ (𝟙 _) z J).val) → SumF I F x x₀ := by
  intro _ R _ _ _ I hR D F _ _ _ K _ φ ε Ix n n₀ hS b τ _ x x₀ hx
  have := hR.1
  have := D.toPre.P.isAb.smooth
  have hL := D.toPre.P.isLB
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_noetherian R _ D.toPre.P.A.hom inferInstance
    (GlobalTheory.AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ (LB.isLB_linComb hL φ ε)
  choose v hv hv' using fun i => exists_vec P (n i)
  obtain ⟨v₀, hv₀, hv₀'⟩ := exists_vec P n₀
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' hL z
  obtain ⟨i₀, hi₀⟩ := exists_mem P (b.left z)
  let t := trF φ ε b.left z (P.ch i₀) (fun k => J (b.left ≫ φ k)) * val τ (𝟙 _) z J
  choose y hy using fun k => CoefBasic.cstH_surj z (gs b.left z _ (P.u k i₀) * (t⁻¹).val)
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  let ev : (Fin P.a → R) →ₗ[R] F := Fintype.linearCombination R y
  have key : ∀ (s : LB.Sec (LB.LinComb D.toPre.P.L φ ε)) (w : Fin P.a → R) (c : F),
      (∀ i, AbLaw.rs _ (P.le i) (s.f (P.ch i)) = loc₀ P w i) →
      sval s b.left z J = UT.cst F z c * (val τ (𝟙 _) z J).val → c = ev w := fun s w c h₁ h₂ => by
    have e := gs_loc₀ P h₁ b.left z hi₀ hJ
    rw [h₂, mul_left_comm, ← Units.val_mul, CoefBasic.cst_eq] at e
    refine CoefBasic.cstH_inj (R := R) z ?_
    have e' : CoefBasic.cstH z c = gs b.left z _ (loc₀ P w i₀) * (t⁻¹).val :=
      (Units.eq_mul_inv_iff_mul_eq t).2 e.symm
    have hs : ∀ a : Fin P.a → Γ(D.toPre.P.A.left, P.W i₀), gs b.left z _ (∑ k, a k) = ∑ k, gs b.left z _ (a k) :=
      fun a => by simp only [gs_eq b.left z _ hi₀, map_sum]
    rw [e', loc₀, hs, Finset.sum_mul]
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (map_sum _ (fun k => w k • y k) _).symm
    rw [gs_mul b.left z _ hi₀, gs_cst_point b z _ hi₀, _root_.mul_assoc, ← hy, ← map_mul, ← Algebra.smul_def]
    rfl
  obtain rfl : x = fun i => ev (v i) := funext fun i => key _ _ _ (hv' i) ((hx z J hJ).1 i)
  obtain rfl : x₀ = ev v₀ := key _ _ _ hv₀' (hx z J hJ).2
  refine sumI_of_ker I P.D₀ ev v v₀ hv hv₀ fun e => ?_
  obtain ⟨S, hS⟩ := hS e
  refine ⟨S, fun T hT k => Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (comp_eq_zero P
    (IsPullback.of_hasPullback D.toPre.P.A.hom (thick R I e)) (v₀ - ∑ i ∈ T, v i) ?_ fun i p hp => ?_) k)⟩
  · simp only [Matrix.mulVec_sub, Matrix.mulVec_sum, hv, hv₀, Finset.sum_const_zero, sub_zero]
  · obtain ⟨J', hJ'⟩ := CoefBasic.exists_good' hL p
    obtain ⟨h₁, h₂⟩ := hS _ (𝟙 _) p J' hJ'
    rw [Category.id_comp] at h₁ h₂
    have h₃ := h₂.trans (Finset.sum_subset hT fun j _ hj => h₁ j hj)
    have e₀ := gs_loc₀ P hv₀' _ p hp hJ'
    have e₁ := fun j => gs_loc₀ P (hv' j) _ p hp hJ'
    rw [gs_eq _ p _ hp] at e₀
    simp only [gs_eq _ p _ hp] at e₁
    rw [loc₀_sub_sum, gs_eq _ p _ hp, map_sub, map_sub, map_sum, map_sum, e₀, Finset.sum_congr rfl fun j _ => e₁ j,
      ← Finset.mul_sum]
    exact sub_eq_zero.2 (congrArg _ h₃)

end GlobalTheory.SecAdicSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsAbelianVarietyStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_torsion_points_abelianVariety : GlobalFnsSt → RigiditySt → (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) := by
  first | exact @GlobalTheory.UU.TorsionCount.card_torsion_points | exact GlobalTheory.UU.TorsionCount.card_torsion_points | (intros; apply GlobalTheory.UU.TorsionCount.card_torsion_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CechComplexAcyclicPrimitiveNontrivialAlgClosedStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechComplex_acyclic_primitive_nontrivial_algClosed : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ M : LB B.left, M.IsLB → (∃ u : LB.Gen (abelian₂ B M), u.IsGen) → ¬ Triv M → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (B.left).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (B.hom) (M) D).Acyclic) := by
  first | exact @GlobalTheory.PrimVan.acyclic_cechLB_of_primitive | exact GlobalTheory.PrimVan.acyclic_cechLB_of_primitive | (intros; apply GlobalTheory.PrimVan.acyclic_cechLB_of_primitive <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeLocallyTrivialProductLineBuStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedSubscheme_locallyTrivial_product_lineBundle : GlobalFnsSt → ∀ (R : Type) [CommRing R] (T B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ F : LB (T ⊗ B).left, F.IsLB → ∃ (H : Over (Spec (CommRingCat.of R))) (j : H ⟶ T), IsClosedImmersion j.left ∧ ∀ (T' : Over (Spec (CommRingCat.of R))) (x : T' ⟶ T), (∀ p : T'.left, ∃ U : T'.left.Opens, p ∈ U ∧ Triv ((F.pull (x ▷ B).left).pull ((fst T' B).left ⁻¹ᵁ U).ι)) ↔ ∃ y : T' ⟶ H, y ≫ j = x := by
  first | exact @GlobalTheory.TrivSubscheme.exists_closed_locTriv | exact GlobalTheory.TrivSubscheme.exists_closed_locTriv | (intros; apply GlobalTheory.TrivSubscheme.exists_closed_locTriv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoUniformisationsOfIsoDegenerationData
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pmaps_rig_of_thick_compat {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {I : Ideal R} (hI : I ≠ ⊤) {D D' : DegData R I} {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    (U : UnifPre I D A G) (U' : UnifPre I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre)
    (j : ∀ e : ℕ, thickObj R I e G' ⟶ thickObj R I e G) (hj : ∀ e, IsMonHom (j e))
    {F : G'.left ⟶ G.left} (he : eSec G' ≫ F = eSec G)
    (wL : LB.Iso U'.LG.L (U.LG.L.pull F)) (hw : wL.IsGen)
    (H : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι)
      (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈
        D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' →
      (fstG I e G).left ((j e).left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' →
      Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') =
        Geo.Tor.gw (U.w e) (r ≫ (j e).left) z jM (fun _ => jL) *
          Geo.Tor.gw wL (r ≫ (fstG I e G').left) z jL jL') :
    PMaps wL (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) U'.LG.rig U.LG.rig (𝟙 _) := by
  refine AbelianPartIso.pmaps_of_thickenings hI U.LG.isLB U'.LG.isLB wL hw _ _ he _ U'.LG.rigGen _ U.LG.rigGen
    fun e z p q hp hq => ?_
  have hs := Geo.Tor.specOf_id R
  have hB : eSec D'.toPre.P.A ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
      eSec D.toPre.P.A := hD.he.trans ((congrArg (· ≫ _) hs).trans (Category.id_comp _))
  have hje : eSec (thickObj R I e G') ≫ (j e).left = eSec (thickObj R I e G) :=
    congrArg Over.Hom.left (hj e).one_hom
  obtain ⟨m, hm⟩ := Geo.Tor.exists_chart D.toPre.P.isLB ((UnitValue.thU R I e ≫ eSec D.toPre.P.A) z)
  obtain ⟨m', hm'⟩ := Geo.Tor.exists_chart D'.toPre.P.isLB ((UnitValue.thU R I e ≫ eSec D'.toPre.P.A) z)
  have hm₂ : (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)))
      ((UnitValue.thU R I e ≫ eSec D'.toPre.P.A) z) ∈ D.toPre.P.L.U m :=
    (congrArg (fun g => (UnitValue.thU R I e ≫ g) z ∈ D.toPre.P.L.U m) hB).mpr hm
  have e₁ := UnitValue.wv_rig U e z m p hm hp
  have e₂ := UnitValue.wv_rig U' e z m' q hm' hq
  have e₃ := (Geo.Tor.maps_iff hD.w _ (fun _ => eSec D.toPre.P.A) _ D'.toPre.rig D.toPre.rig
    (specOf (RingHom.id R)) _ (rigPull_le _ _ hD.he D.toPre.P.L) (fun _ => rfl)).1 hD.w_rig _
    (UnitValue.thU R I e) z (fun _ => m) (fun _ => m') (fun _ => hm₂) (fun _ => hm')
  have e₄ := H e _ (eSec (thickObj R I e G')) z m m' p q
    ((congrArg (fun g => (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) (g z) ∈
      D.toPre.P.L.U m) (UnitValue.eSec_pGl U' e)).mpr hm₂)
    ((congrArg (fun g => g z ∈ D'.toPre.P.L.U m') (UnitValue.eSec_pGl U' e)).mpr hm')
    ((congrArg (fun g => g z ∈ U.LG.L.U p)
      (((congrArg (· ≫ (fstG I e G).left) hje)).trans (UnitValue.eSec_fGl (G := G) e))).mpr hp)
    ((congrArg (fun g => g z ∈ U'.LG.L.U q) (UnitValue.eSec_fGl (G := G') e)).mpr hq)
  have ht : UnitValue.thU R I e ≫ specOf (RingHom.id R) = UnitValue.thU R I e :=
    (congrArg (_ ≫ ·) hs).trans (Category.comp_id _)
  rw [UnitValue.eSec_pGl U' e, UnitValue.eSec_fGl (G := G') e, hje] at e₄
  rw [ht, Fintype.prod_unique, zpow_one] at e₃
  exact mul_left_cancel (e₁.trans (e₃.trans ((congrArg _ e₂.symm).trans ((mul_assoc _ _ _).symm.trans
    ((congrArg (· * _) e₄).trans (mul_assoc _ _ _))))))

theorem exists_iso_isPullUnif_of_isPullDeg : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre), ∃ (ψ : G' ≅ G) (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G), IsMonHom ψ.hom ∧ IsMonHom bc.hom ∧ bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.hom.left ∧ IsPullUnif (RingHom.id R) hD bc U U' := by
  intro hL hL2 R _ _ _ I hR hI D D' A A' G G' _ _ _ _ hG hG' U U' hD
  obtain ⟨j, hj⟩ := exists_thick_iso_of_isPullDeg hL.globalFns R I hR hI D D' A A' G G' hG hG' U U' hD
  obtain ⟨ΦK, wK, hK⟩ := GlobalTheory.T.exists_genericFibreIso_of_compatible_thickenings hL hL2 R I hR hI D D' A A' G G' hG hG' U U' hD j hj
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.generic_iso_extends_semiAbelian_dvr_inducing_formal hL hL2 R I hR hI D D' A A' G G' hG hG' U U' hD j hj ΦK wK hK
  obtain ⟨wL, hwL, H⟩ := GlobalTheory.T.exists_bundleIso_extending_generic_alt hL hL2 R I hR hI D D' A A' G G' hG hG' U U' hD j hj ΦK wK hK ψ hψ
  obtain ⟨hm, -, hf⟩ := hψ
  have hs := Geo.Tor.specOf_id R
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso ((isGrpPullback_of_iso ψ).congr hs.symm rfl)
    (isGrpPullback_pullback G (specOf (RingHom.id R)))
  have hbc' : bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.hom.left := hbc
  have he₀ : eSec G' ≫ ψ.hom.left = eSec G := congrArg Over.Hom.left hm.one_hom
  have he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) =
      specOf (RingHom.id R) ≫ eSec G :=
    (congrArg (_ ≫ ·) hbc').trans (he₀.trans ((congrArg (· ≫ _) hs).trans (Category.id_comp _)).symm)
  have hI' : I ≠ ⊤ := hI ▸ (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hr := pmaps_rig_of_thick_compat hI' U.toUnifPre U'.toUnifPre hD (fun e => (j e).hom) (fun e => (hj e).1)
    he₀ wL hwL H
  refine ⟨ψ, bc, hm, mbc, hbc', (isPullUnif_iff_stalks R R I I _ D D' hD A A' G G' bc U U').2
    ⟨pullCongr hbc'.symm wL, (isGen_iff _).2 (pgen_pullCongr _ ((isGen_iff _).1 hwL)), he, ?_, fun e =>
      ⟨(j e).hom.left, (hf e).symm.trans (congrArg (_ ≫ ·) hbc'.symm), (hj e).2.2,
        fun Z r z jM jM' jL jL' h₁ h₂ h₃ h₄ => ?_⟩⟩⟩
  · refine (Geo.Tor.maps_iff _ _ (fun _ => eSec G) _ U'.LG.rig U.LG.rig (specOf (RingHom.id R)) _
      (rigPull_le _ _ he U.LG.L) (fun _ => rfl)).2 (pmaps_pullCongr _ ?_)
    exact (congrArg (PMaps wL (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) U'.LG.rig U.LG.rig)
      hs).mpr hr
  · rw [gw_pullCongr]
    refine H e Z r z jM jM' jL jL' h₁ h₂ ?_ h₄
    rw [hbc'] at h₃
    exact (congrArg (fun g => g (r z) ∈ U.LG.L.U jL) (hf e)).mp h₃

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionLiftBaseChangeH1VanishingTestRingStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_lift_baseChange_h1Vanishing_testRing : ∀ (A A' S : Type) [CommRing A] [CommRing A'] [CommRing S] (g' : A →+* A') (g : A →+* S), (∀ (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) A) (D₁ : Matrix (Fin c) (Fin b) A), D₁ * D₀ = 0 → (∀ w : Fin b → S, (D₁.map g).mulVec w = 0 → ∃ v, (D₀.map g).mulVec v = w) → ∀ v' : Fin a → A', (D₀.map g').mulVec v' = 0 → ∃ v, D₀.mulVec v = 0 ∧ ∀ k, g' (v k) = v' k) → ∀ (X X' XS : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of A')) (fS : XS ⟶ Spec (CommRingCat.of S)) (β : X' ⟶ X) (σ : XS ⟶ X), Smooth f → IsProjBy f → IsPullback β f' f (Spec.map (CommRingCat.ofHom g')) → IsPullback σ fS f (Spec.map (CommRingCat.ofHom g)) → ∀ (W : Scheme.{0}) (L : LB W) (K : Type) [Fintype K] (φ : K → (X ⟶ W)) (φ' : K → (X' ⟶ W)) (ε : K → ℤ), L.IsLB → (∀ k, β ≫ φ k = φ' k) → FirstCohomologyVanishes ((LB.LinComb L φ ε).pull σ) → ∀ s' : LB.Sec (LB.LinComb L φ' ε), ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ z J, Good L z J → sval s β z J = sval s' (𝟙 _) z J := by
  first | exact @GlobalTheory.SecLift.exists_lift | exact GlobalTheory.SecLift.exists_lift | (intros; apply GlobalTheory.SecLift.exists_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionLinearCombinationOfCompatibleThickeStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_linearCombination_of_compatible_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ (W : Scheme.{0}) (L : LB W) (K : Type) [Fintype K] (φ : K → (Y.left ⟶ W)) (ε : K → ℤ) (φ' : ∀ e, K → ((thickObj R I e Y).left ⟶ W)), L.IsLB → (∀ e k, pullback.fst Y.hom (thick R I e) ≫ φ k = φ' e k) → ∀ f : ∀ e, LB.Sec (LB.LinComb L (φ' e) ε), (∀ e z J, Good L z J → sval (f (e + 1)) (thickMap R I e Y) z J = sval (f e) (𝟙 _) z J) → ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e Y).left) (z : Z) (J), Good L z J → sval s (r ≫ pullback.fst Y.hom (thick R I e)) z J = sval (f e) r z J := by
  first | exact @GlobalTheory.SecAlgLinComb.exists_sec_linComb | exact GlobalTheory.SecAlgLinComb.exists_sec_linComb | (intros; apply GlobalTheory.SecAlgLinComb.exists_sec_linComb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FunctionalEquationAllDegreesAlgebraicClosure
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem fe_all_degrees : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U =>
    D.TauBimult → U.FE (Kbar V) 1 → ∀ N : ℕ, 1 ≤ N → U.FE (Kbar V) N := by
  intro h1 h2 V _ _ _ hV D A G _ _ U hτ hFE
  have hsupp : ∀ N : ℕ, 1 ≤ N → ∃ β, U.Supp (Kbar V) N β := fun N hN => by
    obtain ⟨mu, hmu⟩ := (GlobalTheory.T.lineBundleSections_torusTorsion_weightSpaces h1 h2 V hV D A G U N hN).2.1 0
    exact ⟨_, hmu⟩
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact hFE
  | succ k hk ih =>
    exact GlobalTheory.UU.SchurConst.main h1 h2 V hV D A G U (k + 1) (by omega)
      (GlobalTheory.T.exists_functionalEquation_section_nonzero_class h1 h2 V hV D A G U hτ k hk hFE ih (hsupp 1 le_rfl) (hsupp k hk))

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomogeneousFormSectionsEqZeroOfThickeningsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousForm_sections_eq_zero_of_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ (N : LB Y.left) (κ : Type) (σ : κ → LB.Sec N) (d : ℕ) (F : MvPolynomial κ R), N.IsLB → F.IsHomogeneous d → (∀ (e : ℕ) (z : (thickObj R I e Y).left) (k : N.ι), pullback.fst Y.hom (thick R I e) z ∈ N.U k → gs (pullback.fst Y.hom (thick R I e)) z (N.U k) (MvPolynomial.eval₂Hom (cst Y.hom (N.U k)) (fun j => (σ j).f k) F) = 0) → ∀ k, MvPolynomial.eval₂Hom (cst Y.hom (N.U k)) (fun j => (σ j).f k) F = 0 := by
  first | exact @GlobalTheory.FormVan.form_eq_zero | exact GlobalTheory.FormVan.form_eq_zero | (intros; apply GlobalTheory.FormVan.form_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaSectionSupportEqUnivStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSection_support_eq_univ : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → (∀ α, ∃ j, (f α).f j ≠ 0) ∧ ∀ α, U.Supp (Kbar V) 2 α) := by
  first | exact @GlobalTheory.UU.theta_support_eq_univ | exact GlobalTheory.UU.theta_support_eq_univ | (intros; apply GlobalTheory.UU.theta_support_eq_univ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUniqueStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_degenerationData_unique : GlobalFnsSt → SecBaseChangeSt → AmpleSt → UnifUniqSt := by
  first | exact @GlobalTheory.unifUniq | exact GlobalTheory.unifUniq | (intros; apply GlobalTheory.unifUniq <;> assumption)
end

