import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfLocallyRel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEquivPow
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace PowSections

variable {Y : Scheme.{0}}

theorem sec_ext {M : LB Y} {s t : LB.Sec M} (h : ∀ i, s.f i = t.f i) : s = t := by
  cases s; cases t
  congr 1
  exact funext h

def refine {M M' : LB Y} (σ : M'.ι → M.ι) (hU : ∀ i, M'.U i ≤ M.U (σ i))
    (hg : ∀ i j y, y ∈ M'.U i → y ∈ M'.U j →
      gm (𝟙 Y) y _ (M'.g i j) = gm (𝟙 Y) y _ (M.g (σ i) (σ j))) (s : LB.Sec M) : LB.Sec M' where
  f i := (Y.presheaf.map (homOfLE (hU i)).op).hom (s.f (σ i))
  compat i j := fn_ext fun y hy => by
    have hm : (𝟙 Y : Y ⟶ Y) y ∈ M.U (σ i) ⊓ M.U (σ j) := ⟨hU i hy.1, hU j hy.2⟩
    have e := congrArg (gs (𝟙 Y) y _) (s.compat (σ i) (σ j))
    rw [gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, gs_unit _ y _ hm] at e
    rw [gs_mul _ y _ hy, gs_res _ y inf_le_left hy, gs_res _ y inf_le_right hy, gs_unit _ y _ hy, gs_res _ y (hU i) hy.1,
      gs_res _ y (hU j) hy.2, hg i j y hy.1 hy.2]
    exact e

theorem gs_refine {M M' : LB Y} (σ : M'.ι → M.ι) (hU : ∀ i, M'.U i ≤ M.U (σ i))
    (hg : ∀ i j y, y ∈ M'.U i → y ∈ M'.U j →
      gm (𝟙 Y) y _ (M'.g i j) = gm (𝟙 Y) y _ (M.g (σ i) (σ j))) (s : LB.Sec M) (i : M'.ι) (y : Y)
    (hy : y ∈ M'.U i) :
    gs (𝟙 Y) y _ ((refine σ hU hg s).f i) = gs (𝟙 Y) y _ (s.f (σ i)) :=
  gs_res (𝟙 Y) y (hU i) hy _

def secEquiv {M M' : LB Y} (σ : M'.ι ≃ M.ι) (hU : ∀ i, M'.U i = M.U (σ i))
    (hg : ∀ i j y, y ∈ M'.U i → y ∈ M'.U j →
      gm (𝟙 Y) y _ (M'.g i j) = gm (𝟙 Y) y _ (M.g (σ i) (σ j))) : LB.Sec M ≃ LB.Sec M' :=
  have hU' : ∀ i, M.U i ≤ M'.U (σ.symm i) := fun i => by rw [hU, σ.apply_symm_apply]
  have hg' : ∀ i j y, y ∈ M.U i → y ∈ M.U j →
      gm (𝟙 Y) y _ (M.g i j) = gm (𝟙 Y) y _ (M'.g (σ.symm i) (σ.symm j)) := fun i j y hi hj => by
    rw [hg _ _ y (hU' i hi) (hU' j hj)]
    obtain ⟨i, rfl⟩ := σ.surjective i
    obtain ⟨j, rfl⟩ := σ.surjective j
    rw [σ.apply_symm_apply, σ.apply_symm_apply]
  { toFun := refine σ (fun i => (hU i).le) hg
    invFun := refine σ.symm hU' hg'
    left_inv := fun s => sec_ext fun i => fn_ext fun y hy => by
      rw [gs_refine _ _ _ _ _ y hy, gs_refine _ _ _ _ _ y (hU' i hy), σ.apply_symm_apply]
    right_inv := fun s => sec_ext fun i => fn_ext fun y hy => by
      rw [gs_refine _ _ _ _ _ y hy, gs_refine _ _ _ _ _ y ((hU i).le hy), σ.symm_apply_apply] }

theorem gs_secEquiv {M M' : LB Y} (σ : M'.ι ≃ M.ι) (hU : ∀ i, M'.U i = M.U (σ i))
    (hg : ∀ i j y, y ∈ M'.U i → y ∈ M'.U j →
      gm (𝟙 Y) y _ (M'.g i j) = gm (𝟙 Y) y _ (M.g (σ i) (σ j))) (s : LB.Sec M) (i : M'.ι) (y : Y)
    (hy : y ∈ M'.U i) :
    gs (𝟙 Y) y _ ((secEquiv σ hU hg s).f i) = gs (𝟙 Y) y _ (s.f (σ i)) :=
  gs_res (𝟙 Y) y (hU i).le hy _

theorem exists_equiv_pow (M : LB Y) (n : ℕ) (g : ∀ i j, Γ(Y, M.U i ⊓ M.U j)ˣ)
    (hg : ∀ i j y, y ∈ M.U i → y ∈ M.U j →
      gm (𝟙 Y) y _ (g i j) = gm (𝟙 Y) y _ (M.g i j) ^ (n : ℤ)) :
    ∃ E : H0 M n ≃ LB.Sec (⟨M.ι, M.U, g⟩ : LB Y),
      ∀ a (j : M.ι) (y : Y), y ∈ M.U j →
        gs (𝟙 _) y _ ((E a).f j) = gs (𝟙 _) y _ (a.f (fun _ => j)) := by
  have m₁ : ∀ (j : M.ι) (y : Y), y ∈ M.U j →
      y ∈ LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => j) := fun j y hy => Set.mem_iInter.2 fun _ => hy
  let σ : M.ι ≃ (Fin 1 → M.ι) :=
    ⟨fun j _ => j, fun J => J 0, fun _ => rfl, fun J => funext fun k => by rw [Subsingleton.elim k 0]⟩
  have hU : ∀ j : M.ι, M.U j = LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => j) :=
    fun j => le_antisymm (fun y hy => m₁ j y hy) (fun y hy => Set.mem_iInter.1 hy 0)
  have hg' : ∀ i j y, y ∈ M.U i → y ∈ M.U j → gm (𝟙 Y) y _ (g i j) = gm (𝟙 Y) y _
      ((LB.LinComb M (K := Fin 1) (fun _ => 𝟙 Y) (fun _ => (n : ℤ))).g (fun _ => i) (fun _ => j)) := by
    intro i j y hi hj
    have e := gm_linComb M (fun _ : Fin 1 => 𝟙 Y) (fun _ => (n : ℤ)) (𝟙 Y) y (fun _ => i) (fun _ => j)
      (m₁ i y hi) (m₁ j y hj)
    rw [Fin.prod_univ_one, Category.id_comp] at e
    rw [hg i j y hi hj]
    exact e.symm
  exact ⟨secEquiv (M := LB.LinComb M (K := Fin 1) (fun _ => 𝟙 Y) (fun _ => (n : ℤ)))
    (M' := ⟨M.ι, M.U, g⟩) σ hU hg',
    fun a j y hy => gs_secEquiv (M := LB.LinComb M (K := Fin 1) (fun _ => 𝟙 Y) (fun _ => (n : ℤ)))
      (M' := ⟨M.ι, M.U, g⟩) σ hU hg' a j y hy⟩

theorem exists_equiv {X : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N n : ℕ) :
    ∃ E : H0 (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => (N : ℤ))) n ≃
        LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => ((N * n : ℕ) : ℤ))),
      ∀ a (j : Fin 1 → L.ι) (y : Y), p y ∈ L.U (j 0) →
        gs (𝟙 _) y _ ((E a).f j) = gs (𝟙 _) y _ (a.f (fun _ => j)) := by
  obtain ⟨E, hE⟩ := exists_equiv_pow (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => (N : ℤ))) n
    (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => ((N * n : ℕ) : ℤ))).g (fun i j y hi hj => by
      have e := gm_linComb L (fun _ : Fin 1 => p) (fun _ => (N : ℤ)) (𝟙 Y) y i j hi hj
      have e' := gm_linComb L (fun _ : Fin 1 => p) (fun _ => ((N * n : ℕ) : ℤ)) (𝟙 Y) y i j hi hj
      rw [Fin.prod_univ_one] at e e'
      refine e'.trans (Eq.trans ?_ (congrArg (· ^ (n : ℤ)) e.symm))
      rw [Nat.cast_mul, zpow_mul])
  refine ⟨E, fun a j y hy => hE a j y (Set.mem_iInter.2 fun k => ?_)⟩
  obtain rfl : k = 0 := Subsingleton.elim _ _
  exact hy

end PowSections

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteExtensionPrimitiveResidue
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isPrimitiveRoot_residue_of_isUnit {W : Type*} [CommRing W] [IsDomain W] [IsLocalRing W]
    {ζ : W} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hN : IsUnit (N : W)) :
    IsPrimitiveRoot (IsLocalRing.residue W ζ) N := by
  refine ⟨by rw [← map_pow, hζ.pow_eq_one, map_one], fun l hl => hζ.dvd_of_pow_eq_one l ?_⟩
  by_contra hne
  have h1 : (ζ ^ l) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have h2 : ∑ i ∈ Finset.range N, (ζ ^ l) ^ i = 0 := by
    have := geom_sum_mul (ζ ^ l) N
    rw [h1, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
  have h3 := congrArg (IsLocalRing.residue W) h2
  simp only [map_sum, map_pow, hl, one_pow, map_zero, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] at h3
  have h4 := hN.map (IsLocalRing.residue W)
  rw [map_natCast] at h4
  exact h4.ne_zero (by simpa using h3)

theorem exists_finite_extension_primitive_residue :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V], (∃ n : ℕ, n.Prime ∧ IsUnit (n : V)) ∧ ∀ (n j : ℕ), n.Prime → IsUnit (n : V) → ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra V W) (φ : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) (ζ : W), (Module.Finite V W ∧ Module.Free V W ∧ IsDomain W ∧ IsLocalHom (algebraMap V W) ∧ IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W) ∧ Function.Injective φ.left.appTop.hom ∧ IsUnit (n : W) ∧ ζ ^ (n ^ j) = 1 ∧ IsPrimitiveRoot (IsLocalRing.residue W ζ) (n ^ j) := by
  intro V _ _ _ _ _
  refine ⟨?_, fun n j hn hu => ?_⟩
  · have h : IsUnit ((3 : V) + -2) := by norm_num
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
    · exact ⟨3, Nat.prime_three, by exact_mod_cast h⟩
    · exact ⟨2, Nat.prime_two, by exact_mod_cast (IsUnit.neg_iff _).1 h⟩
  · let F := AlgebraicClosure (FractionRing V)
    have hpos : 0 < n ^ j := pow_pos hn.pos j
    have : NeZero (n ^ j) := ⟨hpos.ne'⟩
    have : NeZero ((n ^ j : ℕ) : F) := inferInstance
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F (n ^ j)
    let W : Subalgebra V F := Algebra.adjoin V {z}
    have hzW : z ∈ W := Algebra.subset_adjoin rfl
    have hfin : Module.Finite V W :=
      Algebra.finite_adjoin_simple_of_isIntegral
        ⟨Polynomial.X ^ (n ^ j) - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hpos.ne', by
          simp [hz.pow_eq_one]⟩
    have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 fun x y h =>
      IsFractionRing.injective V (FractionRing V) ((algebraMap (FractionRing V) F).injective
        (congrArg Subtype.val h))
    have hfree : Module.Free V W := Module.free_of_finite_type_torsion_free'
    have hW : IsLocalRing W := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := V) W
    have hloc : IsLocalHom (algebraMap V W) := inferInstance
    have hc := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra (R := V) W
    have hζ : IsPrimitiveRoot (⟨z, hzW⟩ : W) (n ^ j) :=
      IsPrimitiveRoot.of_map_of_injective (f := W.val) hz Subtype.val_injective
    have hnW : IsUnit (n : W) := by simpa using hu.map (algebraMap V W)
    refine ⟨W, inferInstance, inferInstance, inferInstance,
      Over.homMk (Spec.map (CommRingCat.ofHom W.val.toRingHom)) ?_, ⟨z, hzW⟩,
      ⟨hfin, hfree, inferInstance, hloc, hc⟩, ?_, hnW, hζ.pow_eq_one,
      isPrimitiveRoot_residue_of_isUnit hζ (by exact_mod_cast hnW.pow j)⟩
    · change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp]
      rfl
    · change Function.Injective (Spec.map (CommRingCat.ofHom W.val.toRingHom)).appTop.hom
      have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom W.val.toRingHom)
      have hi : Function.Injective ((Spec.map (CommRingCat.ofHom W.val.toRingHom)).appTop ≫
          (Scheme.ΓSpecIso _).hom).hom := by
        rw [h, CommRingCat.hom_comp, RingHom.coe_comp]
        exact Subtype.val_injective.comp (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.injective
      rw [CommRingCat.hom_comp, RingHom.coe_comp] at hi
      exact hi.of_comp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntermediateFieldOfPowEqOne
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionSeparable

theorem exists_intermediateField {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) [FormallyUnramified p] [LocallyOfFiniteType p]
    (a : Spec (CommRingCat.of Ω) ⟶ X)
    (ha : a ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    ∃ K : IntermediateField k Ω, FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ b : Spec (CommRingCat.of K) ⟶ X,
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ b = a := by
  first
  | (rename_i h_2 h_3 h_4 h_7 h_8; revert k Ω h_2 h_3 h_4 X p h_7 h_8 a ha; exact @_root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point)
  | exact @_root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point
  | exact _root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point
  | (apply _root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point ..)

theorem exists_intermediateField_of_pow_eq_one {V : Type} [CommRing V]
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] [LocallyOfFiniteType G.hom]
    {N : ℕ} (hN : IsUnit (N : V)) {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (r : V →+* k)
    (f : V →+* Ω) (hf : (algebraMap k Ω).comp r = f)
    (x : Over.mk (Spec.map (CommRingCat.ofHom f)) ⟶ G) (hx : x ^ N = 1) :
    ∃ K : IntermediateField k Ω, FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ b : Spec (CommRingCat.of K) ⟶ G.left,
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ b = x.left := by
  have hN' : IsUnit (N : Γ(Spec (CommRingCat.of V), ⊤)) := by
    simpa using hN.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
  have h₁ := formallyUnramified_mulN _ G N hN'
  have h₂ : LocallyOfFiniteType (mulN G N).left := by
    have : LocallyOfFiniteType ((mulN G N).left ≫ G.hom) := by rw [Over.w]; infer_instance
    exact locallyOfFiniteType_of_comp _ G.hom
  let T : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom r))
  let e : Spec (CommRingCat.of k) ⟶ G.left := (1 : T ⟶ G).left
  let j : Over.mk (Spec.map (CommRingCat.ofHom f)) ⟶ T :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (by
      subst hf
      exact (Spec.map_comp _ _).symm)
  have hw : x.left ≫ (mulN G N).left = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ≫ e := by
    change (x ≫ mulN G N).left = (j ≫ (1 : T ⟶ G)).left
    rw [MulUnramified.comp_mulN, hx, comp_one]
  have : FormallyUnramified (pullback.snd (mulN G N).left e) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @FormallyUnramified)
      (IsPullback.of_hasPullback _ _) h₁
  obtain ⟨K, hK, hK', b, hb⟩ := exists_intermediateField (pullback.snd (mulN G N).left e)
    (pullback.lift x.left _ hw) (pullback.lift_snd _ _ _)
  exact ⟨K, hK, hK', b ≫ pullback.fst _ _, by rw [reassoc_of% hb, pullback.lift_fst]⟩

theorem epi_specMap {K L : Type} [Field K] [Field L] (σ : K →+* L) :
    Epi (Spec.map (CommRingCat.ofHom σ)) := by
  have : Flat (Spec.map (CommRingCat.ofHom σ)) := inferInstance
  have : Surjective (Spec.map (CommRingCat.ofHom σ)) :=
    ⟨fun u => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

end GlobalTheory.TorsionSeparable

namespace GlobalTheory

open TorsionSeparable IsLocalRing

theorem exists_finite_extension_torsion_lift : UnramExtSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (N : ℕ), IsUnit (N : V) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (f : V →+* Ω), IsLocalHom f → ∀ s : Finset (Over.mk (Spec.map (CommRingCat.ofHom f)) ⟶ G), (∀ x ∈ s, x ^ N = 1) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (_ : Algebra V W) (f' : W →+* Ω), Module.Finite V W ∧ Function.Injective (algebraMap V W) ∧ IsLocalHom (algebraMap V W) ∧ IsLocalHom f' ∧ f'.comp (algebraMap V W) = f ∧ ∀ x ∈ s, ∃ y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G, y ^ N = 1 ∧ Spec.map (CommRingCat.ofHom f') ≫ y.left = x.left := by
  intro hU V _ _ _ _ G _ _ _ N hN Ω _ _ f hf s hs
  let : Algebra (ResidueField V) Ω := (ResidueField.lift f).toAlgebra
  have hr : (algebraMap (ResidueField V) Ω).comp (residue V) = f := ResidueField.lift_comp_residue f
  choose K hK hK' b hb using fun x : s =>
    exists_intermediateField_of_pow_eq_one G hN (residue V) f hr x.1 (hs x.1 x.2)
  let L : IntermediateField (ResidueField V) Ω := ⨆ x, K x
  have : FiniteDimensional (ResidueField V) L := inferInstance
  have : Algebra.IsSeparable (ResidueField V) L := inferInstance
  obtain ⟨W, _, _, _, _, _, hfin, hinj, hloc, -, e, he⟩ := hU V L
  let σ : ResidueField W →+* Ω := (algebraMap L Ω).comp e.toRingHom
  have hcomp : (σ.comp (residue W)).comp (algebraMap V W) = f := by
    ext v
    change algebraMap L Ω (e (residue W (algebraMap V W v))) = f v
    rw [he, ← IsScalarTower.algebraMap_apply, ← hr]
    rfl
  have hσ : IsLocalHom (σ.comp (residue W)) := ⟨fun a ha => by
    by_contra hn
    exact ha.ne_zero (by rw [RingHom.comp_apply, (residue_eq_zero_iff a).2 hn, map_zero])⟩
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    σ.comp (residue W), hfin, hinj, hloc, hσ, hcomp, fun x hx => ?_⟩
  have := epi_specMap σ
  let c : Spec (CommRingCat.of (ResidueField W)) ⟶ G.left :=
    Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp
      (IntermediateField.inclusion (le_iSup K ⟨x, hx⟩)).toRingHom)) ≫ b ⟨x, hx⟩
  have hc : Spec.map (CommRingCat.ofHom σ) ≫ c = x.left := by
    rw [← hb ⟨x, hx⟩, ← Spec.map_comp_assoc]
    congr 2
    ext t
    simp [σ]
  have hp : Spec.map (CommRingCat.ofHom σ) ≫ Spec.map (CommRingCat.ofHom (residue W)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap V W)) = Spec.map (CommRingCat.ofHom f) := by
    rw [← hcomp, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  let T : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom (residue W)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap V W)))
  let x₀ : T ⟶ G := Over.homMk c (by
    rw [← cancel_epi (Spec.map (CommRingCat.ofHom σ))]
    exact ((reassoc_of% hc) _).trans ((Over.w x).trans hp.symm))
  let j : Over.mk (Spec.map (CommRingCat.ofHom f)) ⟶ T :=
    Over.homMk (Spec.map (CommRingCat.ofHom σ)) hp
  have hj : j ≫ x₀ = x := Over.OverMorphism.ext hc
  have : Epi j.left := epi_specMap σ
  have : Epi j := Over.epi_of_epi_left j
  have hx₀ : x₀ ^ N = 1 := by
    rw [← cancel_epi j, comp_pow, hj, hs x hx, comp_one]
  obtain ⟨y, ⟨hy, hy'⟩, -⟩ := existsUnique_torsion_lift W _ G
    (Spec.map (CommRingCat.ofHom (algebraMap V W))) N
    (by simpa using hN.map (algebraMap V W)) x₀ hx₀
  refine ⟨y, hy, ?_⟩
  rw [← hc, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hy']
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNeZeroIffSvalGenericPointNeZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem gs_id_eq_zero_iff {Y : Scheme.{0}} [IsIntegral Y] (y : Y) (U : Y.Opens) (hy : y ∈ U) (a : Γ(Y, U)) :
    gs (𝟙 Y) y U a = 0 ↔ a = 0 := by
  have e : gs (𝟙 Y) y U a = (Y.presheaf.germ U y hy).hom a := gs_eq (𝟙 Y) y U hy a
  rw [e]
  exact map_eq_zero_iff _ (germ_injective_of_isIntegral Y y hy)

theorem exists_ne_zero_iff_sval_ne_zero {Y X : Scheme.{0}} [IsIntegral Y] {L : LB X} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) {y : Y} {J : (Y ⟶ X) → L.ι} (hJ : Good L y J) :
    (∃ j, s.f j ≠ 0) ↔ sval s (𝟙 Y) y J ≠ 0 := by
  have hm : y ∈ LB.wchart L φ (fun k => J (𝟙 Y ≫ φ k)) := hJ.mem φ (𝟙 Y)
  constructor
  · rintro ⟨j, hj⟩ h0
    apply hj
    have h1 : s.f (fun k => J (𝟙 Y ≫ φ k)) = 0 := (gs_id_eq_zero_iff y _ hm _).1 h0
    refine fn_ext (V := LB.wchart L φ j) fun x hx => ?_
    have hne : (LB.wchart L φ j : Set Y).Nonempty := ⟨x, hx⟩
    obtain ⟨w, hw, hw'⟩ := nonempty_preirreducible_inter (LB.wchart L φ j).isOpen
      (LB.wchart L φ (fun k => J (𝟙 Y ≫ φ k))).isOpen hne ⟨y, hm⟩
    have h2 := sec_trans s (𝟙 Y) w hw hw'
    have h3 : gs (𝟙 Y) w (LB.wchart L φ (fun k => J (𝟙 Y ≫ φ k))) (s.f (fun k => J (𝟙 Y ≫ φ k))) = 0 :=
      (gs_id_eq_zero_iff w _ hw' _).2 h1
    rw [h3, mul_zero] at h2
    exact congrArg (gs (𝟙 Y) x (LB.wchart L φ j)) ((gs_id_eq_zero_iff w _ hw _).1 h2)
  · intro h
    exact ⟨fun k => J (𝟙 Y ≫ φ k), fun h0 => h ((gs_id_eq_zero_iff y _ hm _).2 h0)⟩

theorem exists_ne_zero_of_sval_eq_mul_unit : ∀ (Y X : Scheme.{0}) [IsIntegral Y] (L : LB X), L.IsLB → ∀ (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (φ'' : K'' → (Y ⟶ X)) (ε'' : K'' → ℤ) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (d : LB.Sec (LB.LinComb L φ'' ε'')), (∀ (y : Y) (J), Good L y J → ∃ v : (Y.presheaf.stalk y)ˣ, sval d (𝟙 Y) y J = sval s (𝟙 Y) y J * sval s' (𝟙 Y) y J * v.val) → (∃ j, s.f j ≠ 0) → (∃ j, s'.f j ≠ 0) → ∃ j, d.f j ≠ 0 := by
  intro Y X _ L hL K K' K'' _ _ _ φ ε φ' ε' φ'' ε'' s s' d h hs hs'
  choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ (genericPoint Y))
  have hG : Good L (genericPoint Y) J := hJ
  obtain ⟨v, hv⟩ := h _ J hG
  rw [exists_ne_zero_iff_sval_ne_zero _ hG] at hs hs' ⊢
  rw [hv]
  exact mul_ne_zero (mul_ne_zero hs hs') v.ne_zero

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointEquivSmoothLocus
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace WeierstrassCurve

theorem exists_point_equiv_smoothLocus {R : Type} [CommRing R] (W : WeierstrassCurve R)
    (U : (scheme W).Opens)
    (hU : ∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k) (h : IsUnimodularSol (W.map ρ) P),
      ⊤ ≤ ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P)
    (k : Type) [Field k] [Algebra R k] :
    ∃ c : (W.baseChange k).toProjective.Point ≃ (specOver R k ⟶ Over.mk (U.ι ≫ toSpec W)),
      ∀ p, (c p).left ≫ U.ι = (ofProjectivePoint W k p).left := by
  have hr : ∀ p, Set.range (ofProjectivePoint W k p).left ⊆ Set.range U.ι := by
    rintro @⟨⟨P⟩, hP⟩ _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (hU k (algebraMap R k) P (.of_nonsingular hP)).mpr hP (Set.mem_univ z)
  let c : (W.baseChange k).toProjective.Point → (specOver R k ⟶ Over.mk (U.ι ≫ toSpec W)) :=
    fun p => Over.homMk (IsOpenImmersion.lift U.ι _ (hr p))
      ((IsOpenImmersion.lift_fac_assoc U.ι _ (hr p) _).trans (Over.w (ofProjectivePoint W k p)))
  have hc : ∀ p, (c p).left ≫ U.ι = (ofProjectivePoint W k p).left := fun p =>
    IsOpenImmersion.lift_fac U.ι _ (hr p)
  refine ⟨Equiv.ofBijective c ⟨fun p q e => ?_, fun x => ?_⟩, hc⟩
  · refine ofProjectivePoint_injective W k (Over.OverMorphism.ext ?_)
    rw [← hc, ← hc, e]
  · obtain ⟨P, hP, e⟩ := exists_eq_ptHom W (algebraMap R k) (x.left ≫ U.ι)
      ((Category.assoc _ _ _).trans (Over.w x))
    have hns : (W.baseChange k).toProjective.Nonsingular P := (hU k _ P hP).mp (by
      rw [← e]
      intro y _
      exact (x.left y).2)
    refine ⟨⟨(WeierstrassCurve.Projective.nonsingularLift_iff P).mpr hns⟩,
      Over.OverMorphism.ext ?_⟩
    exact (cancel_mono U.ι).mp ((hc _).trans e.symm)

end WeierstrassCurve

open WeierstrassCurve in

theorem exists_grpObj_smoothLocus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (W : WeierstrassCurve R) (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → Smooth (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → GeometricallyIntegral (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → ∃ _ : GrpObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)), IsCommMonObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)) ∧ (η[(Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))]).left ≫ U.ι = GlobalTheory.WeierstrassCurve.zero W ∧ (∀ (k : Type) [Field k] (ρ : R →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) Q), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → y.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), (lift x y ≫ μ[(Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))]).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h) := by
  intro R _ _ _ W U hU hs hg
  classical
  obtain ⟨m, hm⟩ := exists_add_smoothLocus R W U hU hs hg
  obtain ⟨i, e, he, hi⟩ := exists_neg_origin_smoothLocus R W U hU
  let G : Over (Spec (.of R)) := Over.mk (U.ι ≫ toSpec W)
  have hG : IsIntegral (U : Scheme) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (U.ι ≫ toSpec W)
  have hN : IsLocallyNoetherian (U : Scheme) :=
    LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ toSpec W)
  have hG₁ : IsIntegral G.left := hG
  have hG₂ : IsIntegral (pullback (U.ι ≫ toSpec W) (U.ι ≫ toSpec W)) := inferInstance
  have hG₂' : IsIntegral (G ⊗ G).left := hG₂
  have hN₂ : IsLocallyNoetherian (G ⊗ G).left :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (U.ι ≫ toSpec W) (U.ι ≫ toSpec W))
  have hG₃ : IsIntegral ((G ⊗ G) ⊗ G).left := inferInstanceAs (IsIntegral
    (pullback (G ⊗ G).hom (U.ι ≫ toSpec W)))
  have hsep : IsSeparated G.hom := inferInstanceAs (IsSeparated (U.ι ≫ toSpec W))
  have H : ∀ (k : Type) [Field k] [Algebra R k], ∃ (M : Type) (_ : AddCommGroup M)
      (c : M ≃ (specOver R k ⟶ G)), toUnit _ ≫ e = c 0 ∧
        (∀ a b, lift (c a) (c b) ≫ m = c (a + b)) ∧ ∀ a, c a ≫ i = c (-a) := by
    intro k _ _
    obtain ⟨c, hc⟩ := exists_point_equiv_smoothLocus W U hU k
    refine ⟨_, inferInstance, c, ?_, ?_, ?_⟩
    · refine Over.OverMorphism.ext ((cancel_mono U.ι).mp ?_)
      rw [hc, ofProjectivePoint_zero, zeroOver_left]
      exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) he)
    · rintro @⟨⟨P⟩, hP⟩ @⟨⟨Q⟩, hQ⟩
      obtain ⟨h, e'⟩ := hm k (algebraMap R k) (c ⟨hP⟩) (c ⟨hQ⟩) P Q (.of_nonsingular hP)
        (.of_nonsingular hQ) (hc _) (hc _)
      refine Over.OverMorphism.ext ((cancel_mono U.ι).mp (e'.trans ?_))
      rw [hc]
      rfl
    · rintro @⟨⟨P⟩, hP⟩
      obtain ⟨h, e'⟩ := hi k (algebraMap R k) (c ⟨hP⟩) P (.of_nonsingular hP) (hc _)
      refine Over.OverMorphism.ext ((cancel_mono U.ι).mp (e'.trans ?_))
      rw [hc]
      rfl
  letI : GrpObj G := grpObjOfFieldPoints e m i H
  refine ⟨this, ⟨?_⟩, he, hm⟩
  refine over_hom_eq_iff_forall_field_algebra.mpr fun k _ _ x => ?_
  obtain ⟨M, _, c, h₀, h₁, h₂⟩ := H k
  obtain ⟨a, ha⟩ := c.surjective (x ≫ fst _ _)
  obtain ⟨b, hb⟩ := c.surjective (x ≫ snd _ _)
  obtain rfl : x = lift (c a) (c b) :=
    CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, ha]) (by rw [lift_snd, hb])
  change lift (c a) (c b) ≫ (β_ G G).hom ≫ m = lift (c a) (c b) ≫ m
  rw [lift_braiding_hom_assoc, h₁, h₁, add_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OpenEqTopOfContainsSpecialPartUniversallyClosedStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_eq_top_of_contains_special_part_universallyClosed : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (Y : Over (Spec (CommRingCat.of R))) [UniversallyClosed Y.hom] (U : Y.left.Opens), (∀ z : (thickObj R I 0 Y).left, pullback.fst Y.hom (thick R I 0) z ∈ U) → U = ⊤ := by
  first | exact @GlobalTheory.Unif.eq_top_of_special_part | exact GlobalTheory.Unif.eq_top_of_special_part | (intros; apply GlobalTheory.Unif.eq_top_of_special_part <;> assumption)
end

