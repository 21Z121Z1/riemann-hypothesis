import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2396
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaledIsoPreservingRigidification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.RigRescale

variable {X Y : Scheme.{0}}

theorem germ_id_pull (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm (𝟙 Y) y (f ⁻¹ᵁ U) (pullU f U a) = gm f y U a := by
  rw [gm_pull (𝟙 Y) f y U h a, Category.id_comp]

theorem germ_pull_g (L : LB X) (f : Y ⟶ X) (y : Y) (P P' : PUnit → L.ι)
    (hp : f y ∈ L.U (P PUnit.unit)) (hp' : f y ∈ L.U (P' PUnit.unit)) :
    gm (𝟙 Y) y ((L.pull f).U P ⊓ (L.pull f).U P') ((L.pull f).g P P') =
      gm f y (L.U (P PUnit.unit) ⊓ L.U (P' PUnit.unit)) (L.g (P PUnit.unit) (P' PUnit.unit)) := by
  have hm : y ∈ (L.pull f).U P ⊓ (L.pull f).U P' := ⟨mem_pull.2 hp, mem_pull.2 hp'⟩
  show gm (𝟙 Y) y _ (∏ _k : PUnit, (res _ (pullU f _ (L.g _ _))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res (𝟙 Y) y _ hm _).trans (germ_id_pull f y (L.U (P PUnit.unit) ⊓ L.U (P' PUnit.unit)) ⟨hp, hp'⟩ _)

theorem germ_linCombIso {L M : LB X} (w : LB.Iso L M) (f : Y ⟶ X) (y : Y) (P : PUnit → M.ι)
    (Q : PUnit → L.ι) (hp : f y ∈ M.U (P PUnit.unit)) (hq : f y ∈ L.U (Q PUnit.unit)) :
    gm (𝟙 Y) y ((M.pull f).U P ⊓ (L.pull f).U Q)
        ((LB.linCombIso w (K := PUnit) (fun _ => f) (fun _ => 1)).s (P, Q)) =
      gm f y ((LB.div M L).U (P PUnit.unit, Q PUnit.unit)) (w.s (P PUnit.unit, Q PUnit.unit)) := by
  have hm : y ∈ (M.pull f).U P ⊓ (L.pull f).U Q := ⟨mem_pull.2 hp, mem_pull.2 hq⟩
  show gm (𝟙 Y) y _ (∏ _k : PUnit, (res _ (pullU f ((LB.div M L).U (P PUnit.unit, Q PUnit.unit))
    (w.s (P PUnit.unit, Q PUnit.unit)))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res (𝟙 Y) y _ hm _).trans (germ_id_pull f y ((LB.div M L).U (P PUnit.unit, Q PUnit.unit))
    (show f y ∈ M.U (P PUnit.unit) ⊓ L.U (Q PUnit.unit) from ⟨hp, hq⟩) _)

theorem germ_iso_isGen {L M : LB X} (w : LB.Iso L M) (hw : w.IsGen) (f : Y ⟶ X) (y : Y)
    (p p' : M.ι) (q q' : L.ι) (hp : f y ∈ M.U p) (hp' : f y ∈ M.U p') (hq : f y ∈ L.U q)
    (hq' : f y ∈ L.U q') :
    gm f y ((LB.div M L).U (p, q)) (w.s (p, q)) =
      gm f y (M.U p ⊓ M.U p') (M.g p p') * (gm f y (L.U q ⊓ L.U q') (L.g q q'))⁻¹ *
        gm f y ((LB.div M L).U (p', q')) (w.s (p', q')) := by
  have hm : f y ∈ M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q') := ⟨⟨hp, hq⟩, hp', hq'⟩
  have h := (congrArg (gm f y (M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q'))) (hw (p, q) (p', q'))).trans
    (map_mul (gm f y (M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q'))) ((LB.div M L).g (p, q) (p', q'))
      (res inf_le_right (w.s (p', q'))))
  have hg : gm f y (M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q')) ((LB.div M L).g (p, q) (p', q')) =
      gm f y (M.U p ⊓ M.U p') (M.g p p') * (gm f y (L.U q ⊓ L.U q') (L.g q q'))⁻¹ := by
    show gm f y _ (res _ (M.g p p') * (res _ (L.g q q'))⁻¹) = _
    rw [map_mul, map_inv]
    exact congrArg₂ (· * ·) (gm_res f y _ hm _) (congrArg _ (gm_res f y _ hm _))
  calc gm f y ((LB.div M L).U (p, q)) (w.s (p, q))
      = gm f y (M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q')) (res inf_le_left (w.s (p, q))) :=
        (gm_res f y _ hm _).symm
    _ = _ := h
    _ = _ := congrArg₂ (· * ·) hg (gm_res f y _ hm _)

theorem germ_gen_isGen (L : LB X) (f : Y ⟶ X) (t : LB.Gen (L.pull f)) (ht : t.IsGen) (y : Y)
    (P P' : PUnit → L.ι) (hp : f y ∈ L.U (P PUnit.unit)) (hp' : f y ∈ L.U (P' PUnit.unit)) :
    gm (𝟙 Y) y ((L.pull f).U P) (t.s P) =
      gm f y (L.U (P PUnit.unit) ⊓ L.U (P' PUnit.unit)) (L.g (P PUnit.unit) (P' PUnit.unit)) *
        gm (𝟙 Y) y ((L.pull f).U P') (t.s P') := by
  have hm : y ∈ (L.pull f).U P ⊓ (L.pull f).U P' := ⟨mem_pull.2 hp, mem_pull.2 hp'⟩
  have h := congrArg (gm (𝟙 Y) y ((L.pull f).U P ⊓ (L.pull f).U P')) (ht P P')
  rw [map_mul] at h
  calc gm (𝟙 Y) y ((L.pull f).U P) (t.s P)
      = gm (𝟙 Y) y ((L.pull f).U P ⊓ (L.pull f).U P') (res inf_le_left (t.s P)) :=
        (gm_res (𝟙 Y) y _ hm _).symm
    _ = _ := h
    _ = _ := by rw [germ_pull_g L f y P P' hp hp']; exact congrArg _ (gm_res (𝟙 Y) y _ hm _)

theorem alg₁ {M : Type*} [CommGroup M] (a b E A B : M) :
    a * A * (a * b⁻¹ * E * (b * B))⁻¹ = A * (E * B)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem alg₂ {M : Type*} [CommGroup M] (A E B : M) : A = E * (A * (E * B)⁻¹) * B := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem proj_comp : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G],
    eSec G ≫ (toUnit G).left = 𝟙 (𝟙_ (Over S)).left := by
  intro S G _
  show (η[G] ≫ toUnit G).left = 𝟙 _
  rw [toUnit_unique (η[G] ≫ toUnit G) (𝟙 _)]
  rfl

theorem exists_isGen_maps_rig {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]
    (L₁ L₂ : RigLB G) (e : LB.Iso L₁.L L₂.L) (he : e.IsGen) : ∃ e' : LB.Iso L₁.L L₂.L, e'.IsGen ∧
      LB.Gen.Maps (LB.linCombIso e' (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₁.rig L₂.rig := by
  let W : (PUnit → L₂.L.ι) × (PUnit → L₁.L.ι) → (𝟙_ (Over S)).left.Opens :=
    fun i => (L₂.L.pull (eSec G)).U i.1 ⊓ (L₁.L.pull (eSec G)).U i.2
  let u : ∀ i, Γ((𝟙_ (Over S)).left, W i)ˣ := fun i =>
    res inf_le_left (L₂.rig.s i.1) *
      ((LB.linCombIso e (K := PUnit) (fun _ => eSec G) (fun _ => 1)).s i *
        res inf_le_right (L₁.rig.s i.2))⁻¹
  have key : ∀ i, ∀ x ∈ W i, gm (𝟙 _) x (W i) (u i) =
      gm (𝟙 _) x ((L₂.L.pull (eSec G)).U i.1) (L₂.rig.s i.1) *
        (gm (eSec G) x ((LB.div L₂.L L₁.L).U (i.1 PUnit.unit, i.2 PUnit.unit))
            (e.s (i.1 PUnit.unit, i.2 PUnit.unit)) *
          gm (𝟙 _) x ((L₁.L.pull (eSec G)).U i.2) (L₁.rig.s i.2))⁻¹ := by
    intro i x hx
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res (𝟙 _) x _ hx _)
      ((map_inv _ _).trans (congrArg _ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        (germ_linCombIso e (eSec G) x i.1 i.2 (mem_pull.1 hx.1) (mem_pull.1 hx.2))
        (gm_res (𝟙 _) x _ hx _))))))
  obtain ⟨c, hc⟩ := glue_unit (X := (𝟙_ (Over S)).left) ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨p, hp⟩ := exists_chart L₂.isLB ((eSec G) x)
      obtain ⟨q, hq⟩ := exists_chart L₁.isLB ((eSec G) x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(fun _ => p, fun _ => q), mem_pull.2 hp, mem_pull.2 hq⟩) u
    (fun i j x hx => by
      rw [key i x hx.1, key j x hx.2,
        germ_gen_isGen L₂.L (eSec G) L₂.rig L₂.rigGen x i.1 j.1 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1),
        germ_gen_isGen L₁.L (eSec G) L₁.rig L₁.rigGen x i.2 j.2 (mem_pull.1 hx.1.2) (mem_pull.1 hx.2.2),
        germ_iso_isGen e he (eSec G) x _ (j.1 PUnit.unit) _ (j.2 PUnit.unit) (mem_pull.1 hx.1.1)
          (mem_pull.1 hx.2.1) (mem_pull.1 hx.1.2) (mem_pull.1 hx.2.2)]
      exact alg₁ _ _ _ _ _)
  let C := pullU (toUnit G).left ⊤ c
  let e' : LB.Iso L₁.L L₂.L := ⟨fun i => e.s i * res (U := (toUnit G).left ⁻¹ᵁ ⊤) (fun _ _ => trivial) C⟩
  have hC : ∀ i, ∀ x ∈ (LB.div L₂.L L₁.L).U i,
      gm (𝟙 _) x ((LB.div L₂.L L₁.L).U i) (e'.s i) =
        gm (𝟙 _) x ((LB.div L₂.L L₁.L).U i) (e.s i) * gm (𝟙 _) x ((toUnit G).left ⁻¹ᵁ ⊤) C :=
    fun i x hx => (map_mul _ _ _).trans (congrArg _ (gm_res (𝟙 _) x _ hx _))
  refine ⟨e', ?_, ?_⟩
  · rintro ⟨p, q⟩ ⟨p', q'⟩
    apply unit_ext
    intro x hx
    have hE : gm (𝟙 _) x ((LB.div L₂.L L₁.L).U (p, q)) (e.s (p, q)) =
        gm (𝟙 _) x ((LB.div L₂.L L₁.L).U (p, q) ⊓ (LB.div L₂.L L₁.L).U (p', q'))
            ((LB.div L₂.L L₁.L).g (p, q) (p', q')) *
          gm (𝟙 _) x ((LB.div L₂.L L₁.L).U (p', q')) (e.s (p', q')) :=
      (gm_res (𝟙 _) x _ hx _).symm.trans (((congrArg (gm (𝟙 _) x _) (he (p, q) (p', q'))).trans
        (map_mul _ _ _)).trans (congrArg _ (gm_res (𝟙 _) x _ hx _)))
    exact (gm_res (𝟙 _) x _ hx _).trans ((hC _ x hx.1).trans ((congrArg (· * _) hE).trans
      ((mul_assoc _ _ _).trans ((congrArg _ ((hC _ x hx.2).symm.trans
        (gm_res (𝟙 _) x _ hx _).symm)).trans (map_mul _ _ _).symm))))
  · rintro ⟨P, Q⟩
    apply unit_ext
    intro x hx
    have hx₁ := mem_pull.1 hx.1
    have hx₂ := mem_pull.1 hx.2
    have hcx : gm (𝟙 _) x ⊤ c = gm (𝟙 _) x (W (P, Q)) (u (P, Q)) := by
      rw [← hc (P, Q)]; exact (gm_res (𝟙 _) x _ hx _).symm
    have hσ : gm (eSec G) x ((LB.div L₂.L L₁.L).U (P PUnit.unit, Q PUnit.unit))
        (e'.s (P PUnit.unit, Q PUnit.unit)) =
        gm (eSec G) x ((LB.div L₂.L L₁.L).U (P PUnit.unit, Q PUnit.unit))
          (e.s (P PUnit.unit, Q PUnit.unit)) * gm (𝟙 _) x ⊤ c := by
      refine (map_mul _ _ _).trans (congrArg _ ?_)
      refine (gm_res (eSec G) x _ (show (eSec G) x ∈ L₂.L.U _ ⊓ L₁.L.U _ from ⟨hx₁, hx₂⟩) _).trans ?_
      refine (gm_pull (eSec G) (toUnit G).left x ⊤ trivial c).trans ?_
      rw [proj_comp]
    have hEq : gm (𝟙 _) x (W (P, Q))
        ((LB.linCombIso e' (K := PUnit) (fun _ => eSec G) (fun _ => 1)).s (P, Q)) =
        gm (eSec G) x ((LB.div L₂.L L₁.L).U (P PUnit.unit, Q PUnit.unit))
            (e.s (P PUnit.unit, Q PUnit.unit)) *
          (gm (𝟙 _) x ((L₂.L.pull (eSec G)).U P) (L₂.rig.s P) *
            (gm (eSec G) x ((LB.div L₂.L L₁.L).U (P PUnit.unit, Q PUnit.unit))
                (e.s (P PUnit.unit, Q PUnit.unit)) *
              gm (𝟙 _) x ((L₁.L.pull (eSec G)).U Q) (L₁.rig.s Q))⁻¹) := by
      rw [germ_linCombIso e' (eSec G) x P Q hx₁ hx₂, hσ, hcx, key (P, Q) x hx]
    exact (gm_res (𝟙 _) x _ hx _).trans ((alg₂ _ _ _).trans
      ((congrArg₂ (· * ·) hEq.symm (gm_res (𝟙 _) x _ hx _).symm).trans (map_mul _ _ _).symm))

end GlobalTheory.RigRescale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueMapClosurePoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ResMap

def stalkEquiv {X : Scheme.{0}} [IsIntegral X] (x : X) : X.presheaf.stalk x ≃+* locRing x :=
  RingEquiv.ofBijective (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict
    ⟨fun _ _ e => IsFractionRing.injective _ X.functionField (congrArg Subtype.val e),
      RingHom.rangeRestrict_surjective _⟩

theorem residueMap : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (z : X) (k : ℕ),
  topologicalKrullDim (closure ({z} : Set X)) = k →
  ∃ (κ : Type) (_ : Field κ) (_ : Algebra ℂ κ) (π₀ : locRing z →+* κ),
    Function.Surjective π₀ ∧ (∀ r : locRing z, π₀ r = 0 ↔ ZeroAt z (r : X.functionField)) ∧
    (∀ a (h : Cartier.constFn p a ∈ locRing z), π₀ ⟨Cartier.constFn p a, h⟩ = algebraMap ℂ κ a) ∧
    (∃ w : Fin k → κ, TrBasis (algebraMap ℂ κ) w) ∧
    ∀ (x : X) (h : locRing x ≤ locRing z), IsLocModel (algebraMap ℂ κ) (π₀.comp (Subring.inclusion h)).range ∧
      (∀ f : κ, ∃ a b : locRing x, π₀ (Subring.inclusion h b) ≠ 0 ∧ f * π₀ (Subring.inclusion h b) = π₀ (Subring.inclusion h a)) ∧
      (IsClosed ({x} : Set X) → RatRes (algebraMap ℂ κ) (π₀.comp (Subring.inclusion h)).range) := by
  intro X _ _ p hp z k hk
  have hprop : IsProper p := by
    obtain ⟨N, j, hj, rfl⟩ := hp
    have := isProper_str ℂ N
    infer_instance
  have hsep : X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from p]; infer_instance⟩
  obtain ⟨Z, i, hi, hZ, rfl⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint z
  let q := i ≫ p
  have hrange : Set.range i = closure ({i (genericPoint Z)} : Set X) := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact (isGenericPoint_def.mp h₁).symm
  have hdim : topologicalKrullDim Z = k := by
    rw [← GlobalTheory.topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange]
    exact hk
  obtain ⟨-, w, hw⟩ := isLocModel_locRing_and_exists_trBasis Z q k (genericPoint Z) hdim
  letI alg : Algebra ℂ Z.functionField := (Cartier.constFn q).toAlgebra
  let π₀ : locRing (i (genericPoint Z)) →+* Z.functionField :=
    (i.stalkMap (genericPoint Z)).hom.comp (stalkEquiv (i (genericPoint Z))).symm.toRingHom
  refine ⟨Z.functionField, inferInstance, alg, π₀, ?_, ?_, ?_, ⟨w, hw⟩, ?_⟩
  · exact (i.stalkMap_surjective _).comp (stalkEquiv _).symm.surjective
  · intro r
    obtain ⟨a, rfl⟩ := (stalkEquiv _).surjective r
    have e1 : π₀ (stalkEquiv _ a) = (i.stalkMap (genericPoint Z)).hom a := by
      show (i.stalkMap (genericPoint Z)).hom ((stalkEquiv _).symm (stalkEquiv _ a)) = _
      rw [RingEquiv.symm_apply_apply]
    have e2 : ((stalkEquiv _ a : locRing _) : X.functionField) = algebraMap _ _ a := rfl
    rw [e1, e2]
    constructor
    · intro h0
      refine ⟨a, ?_, rfl⟩
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have := hu.map (i.stalkMap (genericPoint Z)).hom
      rw [h0] at this
      exact not_isUnit_zero this
    · rintro ⟨b, hb, e⟩
      obtain rfl := IsFractionRing.injective _ X.functionField e
      by_contra hne
      have hu : IsUnit ((i.stalkMap (genericPoint Z)).hom b) := isUnit_iff_ne_zero.2 hne
      exact (IsLocalRing.mem_maximalIdeal _).1 hb ((isUnit_map_iff _ _).1 hu)
  · intro a ha
    have hg := (algebraMap_germ (X := X) (x := i (genericPoint Z)) (U := ⊤) trivial (algX p ⊤ a)).trans
      (RingHom.congr_fun (fnOf_comp_algX p ⊤ (gen_mem (x := i (genericPoint Z)) trivial)) a)
    have hr : (⟨Cartier.constFn p a, ha⟩ : locRing _) =
        stalkEquiv _ (X.presheaf.germ ⊤ _ trivial (algX p ⊤ a)) := Subtype.ext hg.symm
    rw [hr]
    show (i.stalkMap (genericPoint Z)).hom ((stalkEquiv _).symm (stalkEquiv _ _)) = _
    rw [RingEquiv.symm_apply_apply]
    erw [Scheme.Hom.germ_stalkMap_apply i ⊤ (genericPoint Z) trivial (algX p ⊤ a)]
    have hc : (i.app ⊤).hom (algX p ⊤ a) = algX q (i ⁻¹ᵁ ⊤) a := by
      have e : (i ≫ p).appLE ⊤ (i ⁻¹ᵁ ⊤) (le_top.trans (Scheme.Hom.preimage_top _).ge) =
          p.appLE ⊤ ⊤ (le_top.trans (Scheme.Hom.preimage_top _).ge) ≫ i.appLE ⊤ (i ⁻¹ᵁ ⊤) le_rfl := by
        first
          | rw [Scheme.Hom.appLE_comp_appLE]
          | (simp only [Scheme.Hom.comp_appLE, Scheme.Hom.appLE, Category.assoc,
              Scheme.Hom.naturality_assoc]; rfl)
      simp only [algX, q, RingHom.comp_apply]
      rw [Scheme.Hom.app_eq_appLE, e, CommRingCat.comp_apply]
    rw [hc]
    exact RingHom.congr_fun (fnOf_comp_algX q (i ⁻¹ᵁ ⊤) (gen_mem (x := genericPoint Z) trivial)) a
  · intro x h
    have hs : i (genericPoint Z) ⤳ x := GlobalTheory.T.specializes_of_pointLocalRing_le_separated X x _ h
    obtain ⟨y, rfl⟩ : x ∈ Set.range i := by
      rw [hrange]; exact specializes_iff_mem_closure.mp hs
    have key : ∀ a : X.presheaf.stalk (i y),
        π₀ (Subring.inclusion h ⟨algebraMap _ X.functionField a, a, rfl⟩) =
          algebraMap (Z.presheaf.stalk y) Z.functionField ((i.stalkMap y).hom a) := by
      intro a
      have e : (Subring.inclusion h ⟨algebraMap _ X.functionField a, a, rfl⟩ : locRing _) =
          stalkEquiv _ ((X.presheaf.stalkSpecializes hs).hom a) := by
        apply Subtype.ext
        show algebraMap _ X.functionField a =
          algebraMap _ X.functionField ((X.presheaf.stalkSpecializes hs).hom a)
        simp only [RingHom.algebraMap_toAlgebra]
        rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
      rw [e]
      show (i.stalkMap (genericPoint Z)).hom ((stalkEquiv _).symm (stalkEquiv _ _)) = _
      rw [RingEquiv.symm_apply_apply]
      exact Scheme.Hom.stalkSpecializes_stalkMap_apply i (genericPoint Z) y
        ((genericPoint_spec Z).specializes trivial) a
    have hR : (π₀.comp (Subring.inclusion h)).range = locRing y := by
      ext f
      constructor
      · rintro ⟨⟨r, a, rfl⟩, rfl⟩
        exact ⟨(i.stalkMap y).hom a, (key a).symm⟩
      · rintro ⟨b, rfl⟩
        obtain ⟨a, rfl⟩ := i.stalkMap_surjective y b
        exact ⟨⟨_, a, rfl⟩, key a⟩
    have hloc : IsLocModel (Cartier.constFn q) (locRing y) := isLocModel_locRing y
    rw [hR]
    refine ⟨hloc, fun f => ?_, fun hx => ?_⟩
    · obtain ⟨a', ha', b', hb', hb0, e⟩ := hloc.frac f
      rw [← hR] at ha' hb'
      obtain ⟨a, rfl⟩ := ha'
      obtain ⟨b, rfl⟩ := hb'
      exact ⟨a, b, hb0, e⟩
    · have hy : IsClosed ({y} : Set Z) := by
        have hpre : (i : Z → X) ⁻¹' {i y} = {y} := by
          ext t
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
          exact i.isClosedEmbedding.injective.eq_iff
        rw [← hpre]
        exact hx.preimage i.continuous
      exact GlobalTheory.T.hasRationalResidueField_pointLocalRing_closedPoint Z q y hy

end GlobalTheory.ResMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfNaturalOnAlgebraPointsOfCover
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

theorem Pt.aff_in (s : X ⟶ Sp R) (V : X.affineOpens) : (Pt.aff s V).In V.1 :=
  V.2.fromSpec_preimage_self.ge

def Pt.homAff (V : X.affineOpens) (Q : Pt s) (h : Q.In V.1) : (Pt.aff s V).Hom Q :=
  ⟨{ (GlobalTheory.Points.valMap Q.x V.1 h).hom with
      commutes' := fun r ↦ by
        have e := GlobalTheory.Points.valR_constFn_of_over s (algebraMap R Q.B) Q.x Q.w V.1 h r
        rw [GlobalTheory.Points.valR_eq Q.x V.1 h] at e
        exact e },
    GlobalTheory.Points.specMap_valMap_fromSpec V.2 Q.x h⟩

theorem Pt.homAff_apply (V : X.affineOpens) (Q : Pt s) (h : Q.In V.1) (a : CechDR.Sec s V.1) :
    (Pt.homAff V Q h).ρ a = valR Q.x V.1 a :=
  (GlobalTheory.Points.valR_eq Q.x V.1 h a).symm

theorem exists_sec_of_isNat (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (W : J → X.Opens)
    (U : X.Opens) (hWU : ∀ j, W j ≤ U) (hU : U ≤ ⨆ j, W j) (F : PtFn s) (hF : ∀ j, IsNat (W j) F) :
    ∃ f : Γ(X, U), ∀ (j : J) (P : Pt s), P.In (W j) → F P = valR P.x U f := by
  let Ix := {V : X.affineOpens // ∃ j, V.1 ≤ W j}
  let Vs : Ix → X.Opens := fun i ↦ i.1.1
  have hVU : ∀ i : Ix, Vs i ≤ U := fun i ↦ i.2.choose_spec.trans (hWU _)
  let iUV : ∀ i : Ix, Vs i ⟶ U := fun i ↦ homOfLE (hVU i)
  have hcov : U ≤ iSup Vs := by
    intro x hx
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hU hx)
    obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := W j) (x := x) hj
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, j, hVW⟩, hxV⟩
  have hres : ∀ (i : Ix) (V : X.affineOpens) (h : V.1 ≤ i.1.1),
      F (Pt.aff s V) = CechDR.Sec.res s h (F (Pt.aff s i.1)) := fun i V h ↦
    hF i.2.choose (Pt.aff s i.1) (Pt.aff s V) (Pt.affHom s h) ((Pt.aff_in s i.1).mono i.2.choose_spec)
  let sf : ∀ i : Ix, Γ(X, Vs i) := fun i ↦ F (Pt.aff s i.1)
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 Vs sf := by
    intro i i'
    refine X.sheaf.eq_of_locally_eq' (fun V : {V : X.affineOpens // V.1 ≤ Vs i ⊓ Vs i'} ↦ V.1.1) _
      (fun V ↦ homOfLE V.2) ?_ _ _ ?_
    · intro x hx
      obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := Vs i ⊓ Vs i') (x := x) hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
    · intro V
      have k : ∀ (T : Ix) (h2 : Vs i ⊓ Vs i' ≤ Vs T) (g : Vs i ⊓ Vs i' ⟶ Vs T),
          X.sheaf.1.map (homOfLE V.2).op (X.sheaf.1.map g.op (sf T)) = F (Pt.aff s V.1) := fun T h2 g ↦ by
        rw [Subsingleton.elim g (homOfLE h2)]
        change CechDR.Sec.res s V.2 (CechDR.Sec.res s h2 (sf T)) = _
        rw [← CechDR.Sec.res_res]
        exact (hres T V.1 _).symm
      exact (k i inf_le_left _).trans (k i' inf_le_right _).symm
  obtain ⟨f, hf, -⟩ := X.sheaf.existsUnique_gluing' Vs U iUV hcov sf hcomp
  refine ⟨f, fun j P hP ↦ ?_⟩
  have hPU : P.In U := hP.mono (hWU j)
  have key : ∀ (V' : (Sp P.B).affineOpens) (i : Ix), V'.1 ≤ P.x ⁻¹ᵁ i.1.1 →
      CechDR.toSec R P.B V' (F P) = CechDR.toSec R P.B V' (valR P.x U f) := by
    intro V' i hV'
    let P' : Pt s := ⟨CechDR.Sec (CechDR.algStr R P.B) V'.1, CechDR.affPt (CechDR.algStr R P.B) V' ≫ P.x, by
      rw [Category.assoc, P.w]; exact CechDR.affPt_w _ V'⟩
    have hpt : spMap ((CechDR.toSec R P.B V' : P.B →ₐ[R] P'.B) : P.B →+* P'.B) ≫ P.x = P'.x := by
      change _ = CechDR.affPt _ V' ≫ P.x
      rw [CechDR.affPt_eq]; rfl
    let φ : P.Hom P' := ⟨CechDR.toSec R P.B V', hpt⟩
    have hP'V : P'.In i.1.1 := fun q _ ↦ hV' (V'.2.fromSpec_preimage_self.ge (Set.mem_univ q))
    have e1 : F P' = φ.ρ (F P) := hF j P P' φ hP
    have e2 : F P' = (Pt.homAff i.1 P' hP'V).ρ (F (Pt.aff s i.1)) :=
      hF i.2.choose _ _ _ ((Pt.aff_in s i.1).mono i.2.choose_spec)
    rw [Pt.homAff_apply] at e2
    have e3 : valR P'.x i.1.1 (F (Pt.aff s i.1)) = valR P'.x U f := by
      have h0 := hf i
      have h1 := GlobalTheory.Points.valR_res P'.x (hVU i) hP'V f
      change valR P'.x i.1.1 (sf i) = _
      rw [← h0]
      exact h1
    have e4 : valR P'.x U f = φ.ρ (valR P.x U f) := by
      have h2 := GlobalTheory.Points.valR_spMap_comp (φ.ρ : P.B →+* P'.B) P.x U hPU f
      rw [hpt] at h2
      exact h2
    exact e1.symm.trans (e2.trans (e3.trans e4))
  have hex : ∀ y : Sp P.B, ∃ V' : (Sp P.B).affineOpens, y ∈ V'.1 ∧ ∃ i : Ix, V'.1 ≤ P.x ⁻¹ᵁ i.1.1 := by
    intro y
    obtain ⟨V, hV, hyV, hVW⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (U := W j) (x := P.x y) (hP (Set.mem_univ y))
    obtain ⟨V', hV', hyV', hV'V⟩ :=
      exists_isAffineOpen_mem_and_subset (X := Sp P.B) (U := P.x ⁻¹ᵁ V) (x := y) hyV
    exact ⟨⟨V', hV'⟩, hyV', ⟨⟨V, hV⟩, j, hVW⟩, hV'V⟩
  choose V' hyV' i hi using hex
  have key2 : (Scheme.ΓSpecIso (CommRingCat.of P.B)).inv (F P) =
      (Scheme.ΓSpecIso (CommRingCat.of P.B)).inv (valR P.x U f) := by
    refine (Sp P.B).sheaf.eq_of_locally_eq' (fun y ↦ (V' y).1) ⊤ (fun _ ↦ homOfLE le_top)
      (fun y _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyV' y⟩) _ _ (fun y ↦ ?_)
    have := key (V' y) (i y) (hi y)
    change (CechDR.secMap (𝟙 (Sp P.B)) (V' y).1).hom (F P) =
      (CechDR.secMap (𝟙 (Sp P.B)) (V' y).1).hom (valR P.x U f) at this
    simp only [CechDR.secMap, Scheme.Hom.appLE, Scheme.Hom.id_app, CommRingCat.hom_comp, RingHom.comp_apply] at this
    exact this
  exact (Scheme.ΓSpecIso (CommRingCat.of P.B)).symm.commRingCatIsoToRingEquiv.injective key2

end GlobalTheory.CechKS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowAmpleForallLocalConditionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_pow_ample_forall_local_condition : ∀ (W : Scheme.{0}) [IsIntegral W] (H : LB W), IsAmpleLB H → ∀ (P : W → W.functionField → Prop), (∀ y c c', P y c → RegAt y c' → P y (c' * c)) → (∀ y, ∃ (V : W.Opens) (hy : y ∈ V) (d : Γ(W, V)), fnOf V (gen_mem hy) d ≠ 0 ∧ ∀ y' ∈ V, P y' (fnOf V (gen_mem hy) d)) → ∃ n, 1 ≤ n ∧ ∃ t : (lbPow H n).Sec, t ≠ 0 ∧ ∀ (y : W) (i : (lbPow H n).ι) (hi : y ∈ (lbPow H n).U i), P y (fnOf _ (gen_mem hi) (t.f i)) := by
  first | exact @GlobalTheory.exists_sec_forall_local_condition | exact GlobalTheory.exists_sec_forall_local_condition | (intros; apply GlobalTheory.exists_sec_forall_local_condition <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSqNonzeroLocusOfTranslateGeneratorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_sq_nonzeroLocus_of_translate_generator : ∀ (Y X : Scheme.{0}) (f : Y ⟶ X) (M₀ : LB X), M₀.IsLB → ∀ (s₀ : M₀.Sec) (T₁ T₂ : Y ⟶ Y), (∃ t : LB.Gen (LB.LinComb (M₀.pull f) (K := Fin 3) ![T₁, T₂, 𝟙 Y] ![1, 1, -2]), t.IsGen) → ∃ s : (lbPow (M₀.pull f) 2).Sec, nonzeroLocus s = (T₁ ≫ f) ⁻¹ᵁ nonzeroLocus s₀ ⊓ (T₂ ≫ f) ⁻¹ᵁ nonzeroLocus s₀ := by
  first | exact @GlobalTheory.PullSecSq.exists_sec_lbPow_two_nonzeroLocus | exact GlobalTheory.PullSecSq.exists_sec_lbPow_two_nonzeroLocus | (intros; apply GlobalTheory.PullSecSq.exists_sec_lbPow_two_nonzeroLocus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateBaseChangeOfPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_translate_baseChange_of_point : ∀ (R R' : Type) [CommRing R] [CommRing R'] (ρ : R →+* R') (G : Over (Sp R)) [GrpObj G] (c : Sp R' ⟶ G.left), c ≫ G.hom = spMap ρ → ∃ (a : 𝟙_ (Over (Sp R')) ⟶ (Over.pullback (spMap ρ)).obj G) (Φ : pullback G.hom (spMap ρ) ⟶ (G ⊗ G).left), IsPullback Φ (pullback.snd G.hom (spMap ρ)) (snd G G).left c ∧ Φ ≫ (fst G G).left = pullback.fst G.hom (spMap ρ) ∧ (𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a)).left ≫ pullback.fst G.hom (spMap ρ) = Φ ≫ (fst G G * snd G G).left ∧ (𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a⁻¹)).left ≫ pullback.fst G.hom (spMap ρ) = Φ ≫ (fst G G * (snd G G)⁻¹).left := by
  first | exact @GlobalTheory.TransBaseChange.exists_section_translate | exact GlobalTheory.TransBaseChange.exists_section_translate | (intros; apply GlobalTheory.TransBaseChange.exists_section_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianPullbackFramedTangentStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelian_pullback_framed_tangent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1), IsBaseFrame TF U e v P hU → ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → GlobalTheory.DeRham.epsRed K ≫ y' = frX P → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G P.x π → IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' → i ≫ π' = π → (∀ σ k, (ub σ k).left ≫ π = P.u σ k) → ∃ (ι : A.left ⟶ TF.Y.t.G.left) (ι' : A'.left ⟶ TF.Y.t.G.left), IsGrpPullback A TF.Y.t.G (frX P ≫ TF.Y.j) ι ∧ IsGrpPullback A' TF.Y.t.G (y' ≫ TF.Y.j) ι' ∧ i ≫ ι' = ι ∧ (∀ σ k, (ub σ k).left ≫ ι = spMap (dualMap (ev (frX P ≫ TF.Y.j) U.1 hU)) ≫ v (e ⟨σ, k⟩)) ∧ LBIso (TF.Y.t.PP.L.pull ι) (Xo.univ.t.PP.L.pull π) ∧ ⨆ k, (Xo.univ.t.PP.L.pull π).U k = ⊤ := by
  first | exact @GlobalTheory.FramedTransport.exists_model_pullback | exact GlobalTheory.FramedTransport.exists_model_pullback | (intros; apply GlobalTheory.FramedTransport.exists_model_pullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothNhdsOfSmoothOverLocalSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_nhds_of_smooth_over_local_scheme : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Scheme.{0}) (p : P ⟶ Sp R) (x : Sp R) (V W : P.Opens), W ≤ V → Smooth (Limits.pullback.snd (V.ι ≫ p) ((Sp R).fromSpecStalk x)) → LocallyOfFiniteType (W.ι ≫ p) → ∀ z : P, z ∈ W → (p z).asIdeal ≤ x.asIdeal → ∃ W' : P.Opens, z ∈ W' ∧ W' ≤ W ∧ Smooth (W'.ι ≫ p) := by
  first | exact @GlobalTheory.Desc.exists_smooth_nhds_of_smooth_fromSpecStalk | exact GlobalTheory.Desc.exists_smooth_nhds_of_smooth_fromSpecStalk | (intros; apply GlobalTheory.Desc.exists_smooth_nhds_of_smooth_fromSpecStalk <;> assumption)
end

