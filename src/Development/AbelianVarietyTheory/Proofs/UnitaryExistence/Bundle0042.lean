import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0013
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0012
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueHomExtensionSemiAbelianDvr
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_prime_isUnit_of_isLocalRing (T : Type) [CommRing T] [IsLocalRing T] :
    ∃ n : ℕ, n.Prime ∧ IsUnit (n : T) := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (3 : T) with h | h
  · exact ⟨3, Nat.prime_three, by simpa using h⟩
  · refine ⟨2, Nat.prime_two, ?_⟩
    have : (1 - 3 : T) = -((2 : ℕ) : T) := by push_cast; ring
    rw [this] at h
    exact (IsUnit.neg_iff _).1 h

theorem existsUnique_hom_extension_semiAbelian_dvr :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (n : ℕ), IsAbelianScheme B → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C) → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) := by
  intro hfin T K _ _ _ _ _ _ G G' _ _ hG hG' f hf
  have := hG.comm
  have := hG'.comm
  have := hG.smooth
  have := hG'.smooth
  have := hG.separated
  have := hG'.separated
  have := hG.quasiCompact
  have := hG'.quasiCompact
  have hGflat : Flat G.hom := inferInstance
  obtain ⟨n, hn, hnT⟩ := exists_prime_isUnit_of_isLocalRing T
  let Φ := Over.pullback (spMap (algebraMap T K))
  let i : Φ.obj G ⟶ Φ.obj (G ⊗ G') := lift (𝟙 _) f ≫ Functor.LaxMonoidal.μ Φ G G'
  have hi : IsMonHom i := inferInstance
  have hi1 : i ≫ Φ.map (fst G G') = 𝟙 _ := by
    rw [Category.assoc, Functor.Monoidal.μ_fst, lift_fst]
  have hi2 : i ≫ Φ.map (snd G G') = f := by simp [i]
  have hs1 : IsSeparated (fst G G').left := inferInstanceAs (IsSeparated (pullback.fst G.hom G'.hom))
  have hs2 : LocallyOfFiniteType (fst G G').left :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom G'.hom))
  have hs3 : QuasiCompact (fst G G').left :=
    inferInstanceAs (QuasiCompact (pullback.fst G.hom G'.hom))
  have hsP : IsSeparated (G ⊗ G').hom :=
    inferInstanceAs (IsSeparated (pullback.fst G.hom G'.hom ≫ G.hom))
  have hlP : LocallyOfFiniteType (G ⊗ G').hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom G'.hom ≫ G.hom))
  have hs4 : IsSeparated (Φ.map (fst G G')).left := by
    have h1 : IsSeparated (Φ.obj (G ⊗ G')).hom :=
      inferInstanceAs (IsSeparated (pullback.snd (G ⊗ G').hom _))
    rw [← Over.w (Φ.map (fst G G'))] at h1
    exact IsSeparated.of_comp _ (Φ.obj G).hom
  have hic : IsClosedImmersion i.left := by
    have h1 : IsClosedImmersion (i.left ≫ (Φ.map (fst G G')).left) := by
      rw [← Over.comp_left, hi1, Over.id_left]; infer_instance
    exact IsClosedImmersion.of_comp i.left (Φ.map (fst G G')).left
  obtain ⟨Ga, io, e, hio, hGa, he⟩ := exists_flat_closure T K (G ⊗ G') (Φ.obj G) i hic
  obtain ⟨_, hio', -, hc⟩ := flat_closure_subgroup T K (G ⊗ G') Ga io (Φ.obj G) i e hio hGa hi he
  have := hc inferInstance
  have hp : IsMonHom (io ≫ fst G G') := inferInstance
  have hpK : Φ.map (io ≫ fst G G') = e.hom := by
    rw [Functor.map_comp, ← he, Category.assoc, hi1, Category.comp_id]
  have hpKi : IsIso (Φ.map (io ≫ fst G G')) := by rw [hpK]; infer_instance
  have hGaS : IsSeparated Ga.hom := by rw [← Over.w io]; infer_instance
  have hGaL : LocallyOfFiniteType Ga.hom := by rw [← Over.w io]; infer_instance
  have hp1 : IsSeparated (io ≫ fst G G').left := by rw [Over.comp_left]; infer_instance
  have hp2 : LocallyOfFiniteType (io ≫ fst G G').left := by rw [Over.comp_left]; infer_instance
  have hp3 : QuasiCompact (io ≫ fst G G').left := by rw [Over.comp_left]; infer_instance
  have hnt := KernelNoTorsion.eq_one_of_pow_eq_one_of_comp_eq_one T K Ga G (io ≫ fst G G') n hp hGaS
    (etale_mulN_torsion_dvr T Ga n hnT hGa hGaL).2
    (etale_mulN_torsion_dvr T G n hnT hGflat inferInstance).2 hpKi
  have hnS : IsUnit (n : Γ(Sp T, ⊤)) := by
    simpa using hnT.map (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom
  have hker := finite_geometric_kernel_of_pow_eq_one hfin (Sp T) G G' Ga io n hG' hio' hio hn hnS hnt
  have hqf := locallyQuasiFinite_of_finite_geometric_ker (Sp T) Ga G (io ≫ fst G G') hp hp2 hp3 hker
  have hiso := isIso_of_quasiFinite_of_isIso_genericFibre_dvr T K Ga G (io ≫ fst G G') hp hGa hp1 hp2
    hp3 hqf hG.smooth hG.geomConnected hpKi
  have hF : Φ.map (inv (io ≫ fst G G') ≫ io ≫ snd G G') = f := by
    rw [Functor.map_comp, Functor.map_inv, IsIso.inv_comp_eq, hpK, Functor.map_comp, ← he,
      Category.assoc, hi2]
  refine ⟨inv (io ≫ fst G G') ≫ io ≫ snd G G', ⟨?_, hF⟩, fun F hF' => ?_⟩
  · refine flat_dvr_generic_fibre.2.2 T K G G' _ hGflat hG'.separated ?_
    exact hF ▸ hf
  · exact flat_dvr_generic_fibre.1 T K G G' hGflat hG'.separated _ _ (hF'.2.trans hF.symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueLinearLiftUniformisedFibres
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology

namespace GlobalTheory

namespace UniformLift

def toAddHom {V A : Type*} [AddGroup V] [Group A] (e : V → A) (he : ∀ z w, e (z + w) = e z * e w) :
    V →+ Additive A :=
  AddMonoidHom.mk' (fun z => Additive.ofMul (e z)) fun z w => by rw [he, ofMul_mul]

theorem map_zero_eq_one {V A : Type*} [AddGroup V] [Group A] (e : V → A) (he : ∀ z w, e (z + w) = e z * e w) :
    e 0 = 1 :=
  (toAddHom e he).map_zero

theorem addMonoidHom_eq_of_eventuallyEq_addGroup {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [AddGroup A]
    {e e' : V →+ A} (h : e =ᶠ[𝓝 0] e') : e = e' := by
  ext v
  have ht : Tendsto (fun j : ℕ => (2⁻¹ : ℝ) ^ j • v) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num)
      (by norm_num)).smul_const v
  obtain ⟨j, hj⟩ := (ht.eventually h).exists
  have hv : v = (2 ^ j : ℕ) • (2⁻¹ : ℝ) ^ j • v := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp
  rw [hv, map_nsmul, map_nsmul, hj]

theorem existsUnique_linearMap_lift_of_germ {V W A : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [AddGroup A] {ex : V →+ A} {ex' : W →+ A}
    (hker : IsDiscrete (ex'.ker : Set W)) {k : V → W} (hd : DifferentiableAt ℂ k 0) (h0 : k 0 = 0)
    (hk : ∀ᶠ z in 𝓝 0, ex' (k z) = ex z) : ∃! L : V →ₗ[ℂ] W, ∀ z, ex' (L z) = ex z := by
  have hadd : Tendsto (fun p : V × V ↦ p.1 + p.2) (𝓝 0) (𝓝 0) := by
    simpa using continuous_add.tendsto (0 : V × V)
  have hL := eventuallyEq_fderiv_of_eventually_add_mod_discrete hker hd h0 <| by
    filter_upwards [hadd.eventually hk, (continuous_fst.tendsto (0 : V × V)).eventually hk,
      (continuous_snd.tendsto (0 : V × V)).eventually hk] with p h1 h2 h3
    rw [AddMonoidHom.mem_ker, sub_sub, map_sub, map_add, h1, h2, h3, map_add, sub_self]
  have hL' : ex'.comp (fderiv ℂ k 0 : V →+ W) = ex := addMonoidHom_eq_of_eventuallyEq_addGroup <| by
    filter_upwards [hL, hk] with z h1 h2
    change ex' (fderiv ℂ k 0 z) = ex z
    rw [← h1, h2]
  have hL'' : ∀ z, ex' (fderiv ℂ k 0 z) = ex z := fun z => DFunLike.congr_fun hL' z
  refine ⟨(fderiv ℂ k 0 : V →ₗ[ℂ] W), hL'', fun L h => ?_⟩
  have := realLinear_eq_of_sub_mem_discrete hker (L := L.restrictScalars ℝ)
    (L' := (fderiv ℂ k 0 : V →ₗ[ℂ] W).restrictScalars ℝ) fun x => by
      rw [AddMonoidHom.mem_ker, map_sub]
      exact sub_eq_zero.2 ((h x).trans (hL'' x).symm)
  exact LinearMap.ext fun z => DFunLike.congr_fun this z

theorem fibPt_fst {X : Scheme.{0}} (G : Over X) {y : Sp ℂ ⟶ X} (x : Over.mk y ⟶ G) :
    fibPt G x ≫ pullback.fst _ _ = x.left := pullback.lift_fst _ _ _

theorem fibPt_snd {X : Scheme.{0}} (G : Over X) {y : Sp ℂ ⟶ X} (x : Over.mk y ⟶ G) :
    fibPt G x ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _

theorem fibPt_injective {X : Scheme.{0}} (G : Over X) {y : Sp ℂ ⟶ X} {x x' : Over.mk y ⟶ G}
    (h : fibPt G x = fibPt G x') : x = x' :=
  Over.OverMorphism.ext (by rw [← fibPt_fst, h, fibPt_fst])

end UniformLift

open UniformLift in

theorem existsUnique_linear_lift_fibre :
    ∀ (X X' : Scheme.{0}) (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (y : Sp ℂ ⟶ X) (y' : Sp ℂ ⟶ X') (g g' : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (e' : (Fin g' → ℂ) → (Over.mk y' ⟶ G')) (ψ : pullback G.hom y ⟶ pullback G'.hom y') (ψp : (Over.mk y ⟶ G) →* (Over.mk y' ⟶ G')), Smooth G'.hom → (∀ z w, e (z + w) = e z * e w) → (∀ z w, e' (z + w) = e' z * e' w) → IsHolTo Set.univ (fun z => (e z).left) → IsHolTo Set.univ (fun z => (e' z).left) → ((∀ w, ∃! v : epsPt y' ⟶ G', IsDerivAt0 (fun z => (e' z).left) w v.left) ∧ ∀ v : epsPt y' ⟶ G', spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left → ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) → DiscreteTopology {z // e' z = 1} → ψ ≫ pullback.snd _ _ = pullback.snd _ _ → (∀ x, fibPt G x ≫ ψ = fibPt G' (ψp x)) → ∃! h : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), ∀ z, e' (h z) = ψp (e z) := by
  intro X X' G G' _ _ y y' g g' e e' ψ ψp hsm he he' hol hol' hder hdisc hψ hψp
  have hsm' : Smooth (pullback.snd G'.hom y') := inferInstance
  have hd := isDerivAt0_fibre X' G' y' g' e' _ _ _ (fun z => fibPt G' (e' z)) (IsPullback.of_hasPullback G'.hom y')
    (fun z => ⟨fibPt_fst _ _, fibPt_snd _ _⟩) hol' hder
  obtain ⟨k, k0, hka, hk⟩ := LocalLift.exists_local_lift _ (pullback.snd G'.hom y') g g'
    (fun z => fibPt G (e z) ≫ ψ) (fun z => fibPt G' (e' z)) hsm'
    (fun z => by rw [Category.assoc, hψ, fibPt_snd]) (fun z => fibPt_snd _ _)
    ((T.isHolTo_fibPt_and_comp_fibre X G y g e hol).2 _ ψ) (T.isHolTo_fibPt_and_comp_fibre X' G' y' g' e' hol').1 hd
    (by simp only [hψp, map_zero_eq_one e he, map_zero_eq_one e' he', map_one])
  exact existsUnique_linearMap_lift_of_germ
    (ex := toAddHom (fun z => ψp (e z)) fun z w => by rw [he, map_mul]) (ex' := toAddHom e' he')
    ⟨hdisc⟩ hka.differentiableAt k0 (hk.mono fun z hz => fibPt_injective G' (hz.trans (hψp _)))

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameEqOfBaseChangeInjective
section
namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem frPt_eq_of_frMap_injective : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (z z' : FrPt Xo c S) (w : FrPt Xo c T), Function.Injective φ → z'.x = z.x → FrMap φ z w → FrMap φ z' w → z = z' := by
  intro _ E _ _ _ H Dw l Xo c S _ _ T _ _ φ z z' w hφ hx hz hz'
  obtain ⟨g, a, -, hga⟩ := (GlobalTheory.T.frameChange_exists_unique_of_same_point E H Dw l Xo c S z z').1 hx
  have h1 := (GlobalTheory.T.frameChange_comm_baseChange E H Dw l Xo c S T φ z z' w w g (a : S) hga hz).1 hz'
  have h2 := (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c T w w w).1
  obtain ⟨hg, ha⟩ := (GlobalTheory.T.frameChange_exists_unique_of_same_point E H Dw l Xo c T w w).2 _ _ _ _ h1 h2
  have ha1 : (a : S) = ((1 : Sˣ) : S) := hφ (by rw [ha]; simp)
  have hg1 : g = fun _ => 1 := by
    funext τ
    have h := congrFun hg τ
    ext i j
    apply hφ
    have hij := congrFun (congrFun h i) j
    simp only [Matrix.map_apply] at hij
    rw [hij]
    by_cases e : i = j
    · subst e; simp
    · simp [Matrix.one_apply_ne e]
  rw [ha1, hg1] at hga
  have h3 : FrChg (fun _ => 1) ((1 : Sˣ) : S) z z := (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c S z z z).1
  exact (GlobalTheory.T.existsUnique_frameChangeByMatrices E H Dw l Xo c S z (fun _ => 1) 1 (fun _ => by simp)).unique h3 hga

end GlobalTheory.Frames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

section Tri

variable {S : Type} [CommRing S] {n : ℕ}

theorem lowerTri_mul (A B : Matrix (Fin n) (Fin n) S) (hA : ∀ i j, i < j → A i j = 0)
    (hB : ∀ i j, i < j → B i j = 0) : ∀ i j, i < j → (A * B) i j = 0 := by
  first
  | exact @_root_.GlobalTheory.LowerTriangularMul.main
  | exact _root_.GlobalTheory.LowerTriangularMul.main
  | (apply _root_.GlobalTheory.LowerTriangularMul.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LowerTriangularMul.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LowerTriangularMul.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LowerTriangularMul.main ..)

theorem lowerTri_mul_diag (A B : Matrix (Fin n) (Fin n) S) (hA : ∀ i j, i < j → A i j = 0)
    (hB : ∀ i j, i < j → B i j = 0) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hB k i h, mul_zero]
  · rw [hA i k h, zero_mul]

theorem lowerTri_isUnit_det (A : Matrix (Fin n) (Fin n) S) (hA : ∀ i j, i < j → A i j = 0)
    (hd : ∀ i, IsUnit (A i i)) : IsUnit A.det := by
  have h : A.BlockTriangular OrderDual.toDual := fun i j hij => hA i j hij
  rw [Matrix.det_of_lowerTriangular A h]
  exact IsUnit.prod_univ_iff.mpr hd

theorem lowerTri_inv (A : Matrix (Fin n) (Fin n) S) (hA : ∀ i j, i < j → A i j = 0)
    (hd : IsUnit A.det) : ∀ i j, i < j → A⁻¹ i j = 0 := by
  have h : A.BlockTriangular OrderDual.toDual := fun i j hij => hA i j hij
  letI := Matrix.invertibleOfIsUnitDet A hd
  have h' := Matrix.blockTriangular_inv_of_blockTriangular h
  exact fun i j hij => h' hij

end Tri

theorem frBor_iff_frChg {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y y' : FrPt Xo c S) (t : Ix Dw → Sˣ) :
    FrBor t y y' ↔ ∃ g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S),
      (∀ τ i j, i < j → g τ i j = 0) ∧ (∀ τ i, g τ i i = (t (some ⟨τ, i⟩) : S)) ∧
        FrChg g (t none : S) y y' := by
  have hid : spMap (RingHom.id S) = 𝟙 _ := by
    show Spec.map (𝟙 (CommRingCat.of S)) = _
    exact Spec.map_id _
  constructor
  · rintro ⟨hx, hu, pm, h1, h2, h3⟩
    choose cf hd hz hc using hu
    refine ⟨fun τ => Matrix.of (cf τ), fun τ i j h => hz τ i j h, hd, hx, hc, pm, h1, ?_, h3⟩
    rw [hid]
    exact h2.trans (Category.comp_id _).symm
  · rintro ⟨g, hz, hd, hx, hc, pm, h1, h2, h3⟩
    refine ⟨hx, fun τ i => ⟨g τ i, hd τ i, hz τ i, hc τ i⟩, pm, h1, ?_, h3⟩
    rw [hid] at h2
    exact h2.trans (Category.comp_id _)

theorem frBor_calculus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y y' y'' : FrPt Xo c S), (∀ t : Ix Dw → Sˣ, FrBor t y y' ↔ ∃ g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S), (∀ τ i j, i < j → g τ i j = 0) ∧ (∀ τ i, g τ i i = (t (some ⟨τ, i⟩) : S)) ∧ FrChg g (t none : S) y y') ∧ (y'.x = y.x → (∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → S, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧ IsCombAt y.x (y.u τ) cf (y'.u τ i)) → ∃ t : Ix Dw → Sˣ, FrBor t y y') ∧ (∀ t t' : Ix Dw → Sˣ, FrBor t y y' → FrBor t' y' y'' → FrBor (t' * t) y y'') ∧ (∀ t : Ix Dw → Sˣ, FrBor t y y' → FrBor t⁻¹ y' y) := by
  intro E _ _ _ H Dw l Xo c S _ _ y y' y''
  refine ⟨frBor_iff_frChg y y', fun hx hu => ?_, fun t t' h h' => ?_, fun t h => ?_⟩
  · obtain ⟨g₀, a, -, -, -, hs⟩ := (GlobalTheory.T.frameChange_exists_unique_of_same_point E H Dw l Xo c S y y').1 hx
    choose cf hd hz hc using hu
    refine ⟨fun k => match k with
      | none => a
      | some ⟨τ, i⟩ => (hd τ i).unit, (frBor_iff_frChg y y' _).2
        ⟨fun τ => Matrix.of (cf τ), fun τ i j h => hz τ i j h, fun τ i => ?_, hx, hc, hs⟩⟩
    exact (hd τ i).unit_spec.symm
  · obtain ⟨g, hz, hd, hc⟩ := (frBor_iff_frChg y y' t).1 h
    obtain ⟨g', hz', hd', hc'⟩ := (frBor_iff_frChg y' y'' t').1 h'
    refine (frBor_iff_frChg y y'' _).2 ⟨fun τ => g' τ * g τ,
      fun τ => lowerTri_mul _ _ (hz' τ) (hz τ), fun τ i => ?_, ?_⟩
    · show (g' τ * g τ) i i = _
      rw [lowerTri_mul_diag _ _ (hz' τ) (hz τ), hd, hd', Pi.mul_apply, Units.val_mul]
    · rw [Pi.mul_apply, Units.val_mul]
      exact (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c S y y' y'').2 g g' _ _ hc hc'
  · obtain ⟨g, hz, hd, hc⟩ := (frBor_iff_frChg y y' t).1 h
    have hdet : ∀ τ, IsUnit (g τ).det := fun τ =>
      lowerTri_isUnit_det _ (hz τ) fun i => by rw [hd]; exact Units.isUnit _
    have hinv : ∀ τ, (g τ)⁻¹ * g τ = 1 := fun τ => Matrix.nonsing_inv_mul _ (hdet τ)
    have hzi : ∀ τ i j, i < j → (g τ)⁻¹ i j = 0 := fun τ => lowerTri_inv _ (hz τ) (hdet τ)
    obtain ⟨z, hzc, -⟩ := GlobalTheory.T.existsUnique_frameChangeByMatrices E H Dw l Xo c S y' (fun τ => (g τ)⁻¹) (t none)⁻¹
      fun τ => Matrix.isUnit_nonsing_inv_det _ (hdet τ)
    have h1 := (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c S y y' z).2 g _ _ _ hc hzc
    simp only [hinv, Units.inv_mul] at h1
    have h0 := (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c S y y y).1
    have hzy : z = y := (GlobalTheory.T.existsUnique_frameChangeByMatrices E H Dw l Xo c S y (fun _ => 1) 1 (fun τ => by simp)).unique h1 h0
    subst hzy
    refine (frBor_iff_frChg y' z _).2 ⟨fun τ => (g τ)⁻¹, hzi, fun τ i => ?_, hzc⟩
    have h2 := lowerTri_mul_diag _ _ (hzi τ) (hz τ) i
    rw [hinv, Matrix.one_apply_eq, hd] at h2
    rw [Pi.inv_apply]
    exact Units.eq_inv_of_mul_eq_one_right h2.symm

end GlobalTheory.Frames
end

