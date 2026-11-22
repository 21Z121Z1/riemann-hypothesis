import Mathlib
import GroundTheory.ProfiniteCohomology.ContinuousCochains
import GroundTheory.ProfiniteCohomology.BridgeDefs
import GroundTheory.ProfiniteCohomology.Bundle0001
import GroundTheory.ProfiniteCohomology.OpenNormal
import GroundTheory.ProfiniteCohomology.Supernatural
import GroundTheory.ProfiniteCohomology.OfNatRelIndexSupAntitone
import GroundTheory.ProfiniteCohomology.IsProPGroupSubgroupIffIsPGroupMap

-- bundled from GroundTheory.ProfiniteCohomology.Bridge
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory TopRep ContRepresentation

universe u

section General

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_partialProd (n : ℕ) :
    Continuous fun g : Fin n → G => Fin.partialProd g := by
  refine continuous_pi fun i => ?_
  induction i using Fin.induction with
  | zero => simpa using continuous_const
  | succ i ih =>
    simp only [Fin.partialProd_succ]
    exact ih.mul (continuous_apply i)

variable {k : Type u} [CommRing k]

theorem isLocallyConstant_ρ_apply {Y : Type*} [TopologicalSpace Y] (A : Rep.{u} k G)
    [IsDiscreteRep A] {p : Y → G} (hp : Continuous p) {ψ : Y → A} (hψ : IsLocallyConstant ψ) :
    IsLocallyConstant fun y => A.ρ (p y) (ψ y) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have h1 : ∀ᶠ z in nhds y, ψ z = ψ y := hψ.eventually_eq y
  have h2 : ∀ᶠ z in nhds y, A.ρ (p z) (ψ y) = A.ρ (p y) (ψ y) :=
    hp.continuousAt.eventually ((isLocallyConstant_apply A (ψ y)).eventually_eq (p y))
  filter_upwards [h1, h2] with z hz1 hz2
  rw [hz1, hz2]

end General

variable {k G : Type u} [CommRing k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]

section Invariant

variable (X : TopRep.{u} k G)

theorem nestedHomeomorph_mul_apply_of_mem_invariants {m : ℕ} {a : resolutionX X m}
    (ha : a ∈ (resolutionX X m).ρ.invariants) (g : G) (x : Fin m → G) :
    nestedHomeomorph X m a (fun i => g * x i) = X.ρ g (nestedHomeomorph X m a x) := by
  have h := nestedHomeomorph_ρ_apply X m g a (fun i => g * x i)
  rw [(mem_invariants a).1 ha g] at h
  simpa using h

end Invariant

variable (X : TopRep.{u} k G) [DiscreteTopology X] [IsDiscreteRep (underlyingRep X)]

def toInhomogeneous (n : ℕ) (σ : (resolutionX X (n + 1)).ρ.invariants) :
    locallyConstantCochains (underlyingRep X) n :=
  ⟨fun g => nestedHomeomorph X (n + 1) σ.1 (Fin.partialProd g),
    (IsLocallyConstant.iff_continuous _).2
      ((nestedHomeomorph X (n + 1) σ.1).continuous.comp (continuous_partialProd n))⟩

omit [IsDiscreteRep (underlyingRep X)] in
theorem toInhomogeneous_apply (n : ℕ) (σ : (resolutionX X (n + 1)).ρ.invariants) (g : Fin n → G) :
    (toInhomogeneous X n σ : (Fin n → G) → underlyingRep X) g =
      nestedHomeomorph X (n + 1) σ.1 (Fin.partialProd g) :=
  rfl

def homogeneousFun (n : ℕ) (φ : (Fin n → G) → underlyingRep X) (x : Fin (n + 1) → G) : X :=
  X.ρ (x 0) (φ fun i => (x (Fin.castSucc i))⁻¹ * x i.succ)

omit [LocallyCompactSpace G] [DiscreteTopology X] in
theorem isLocallyConstant_homogeneousFun (n : ℕ) {φ : (Fin n → G) → underlyingRep X}
    (hφ : IsLocallyConstant φ) : IsLocallyConstant (homogeneousFun X n φ) :=
  isLocallyConstant_ρ_apply (underlyingRep X) (continuous_apply 0)
    (hφ.comp_continuous (continuous_pi fun _ =>
      ((continuous_apply _).inv).mul (continuous_apply _)))

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [DiscreteTopology X]
  [IsDiscreteRep (underlyingRep X)] in
theorem homogeneousFun_mul (n : ℕ) (φ : (Fin n → G) → underlyingRep X) (g : G)
    (x : Fin (n + 1) → G) :
    homogeneousFun X n φ (fun i => g * x i) = X.ρ g (homogeneousFun X n φ x) := by
  simp only [homogeneousFun, mul_inv_rev, mul_assoc, inv_mul_cancel_left, map_mul]
  rfl

def ofInhomogeneous (n : ℕ) (φ : locallyConstantCochains (underlyingRep X) n) :
    (resolutionX X (n + 1)).ρ.invariants :=
  ⟨(nestedHomeomorph X (n + 1)).symm
      ⟨homogeneousFun X n φ.1, (isLocallyConstant_homogeneousFun X n φ.2).continuous⟩, by
    rw [mem_invariants]
    intro g
    apply (nestedHomeomorph X (n + 1)).injective
    ext x
    rw [nestedHomeomorph_ρ_apply, Homeomorph.apply_symm_apply]
    change X.ρ g (homogeneousFun X n φ.1 fun i => g⁻¹ * x i) = homogeneousFun X n φ.1 x
    rw [homogeneousFun_mul]
    change (X.ρ g * X.ρ g⁻¹) _ = _
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl⟩

omit [DiscreteTopology X] in
theorem nestedHomeomorph_ofInhomogeneous (n : ℕ) (φ : locallyConstantCochains (underlyingRep X) n)
    (x : Fin (n + 1) → G) :
    nestedHomeomorph X (n + 1) (ofInhomogeneous X n φ).1 x = homogeneousFun X n φ.1 x := by
  simp [ofInhomogeneous]

def homogeneousEquiv (n : ℕ) :
    locallyConstantCochains (underlyingRep X) n ≃ₗ[k] (resolutionX X (n + 1)).ρ.invariants :=
  LinearEquiv.symm
  { toFun := toInhomogeneous X n
    invFun := ofInhomogeneous X n
    map_add' σ τ := by
      ext g
      simp only [toInhomogeneous_apply, Submodule.coe_add, Pi.add_apply]
      rw [nestedHomeomorph_add]
      rfl
    map_smul' r σ := by
      ext g
      simp only [toInhomogeneous_apply, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
      rw [nestedHomeomorph_smul]
      rfl
    left_inv σ := by
      apply Subtype.ext
      apply (nestedHomeomorph X (n + 1)).injective
      ext x
      rw [nestedHomeomorph_ofInhomogeneous]
      change X.ρ (x 0) (nestedHomeomorph X (n + 1) σ.1
        (Fin.partialProd fun i => (x (Fin.castSucc i))⁻¹ * x i.succ)) = _
      rw [← nestedHomeomorph_mul_apply_of_mem_invariants X σ.2]
      congr 1
      exact Fin.partialProd_left_inv x
    right_inv φ := by
      ext g
      rw [toInhomogeneous_apply, nestedHomeomorph_ofInhomogeneous]
      simp only [homogeneousFun, Fin.partialProd_zero, Fin.partialProd_right_inv, map_one]
      rfl }

omit [IsDiscreteRep (underlyingRep X)] in

theorem nestedHomeomorph_d_partialProd (n : ℕ) (σ : (resolutionX X (n + 1)).ρ.invariants)
    (g : Fin (n + 1) → G) :
    nestedHomeomorph X (n + 2) ((d X (n + 1)).hom σ.1) (Fin.partialProd g) =
      (inhomogeneousCochains.d (underlyingRep X) n).hom
        (toInhomogeneous X n σ : (Fin n → G) → underlyingRep X) g := by
  rw [nestedHomeomorph_d_apply, Fin.sum_univ_succ, inhomogeneousCochains.d_hom_apply]
  congr 1
  · simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, Fin.partialProd_succ']
    exact nestedHomeomorph_mul_apply_of_mem_invariants X σ.2 _ _
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [toInhomogeneous_apply, Fin.partialProd_contractNth, Fin.val_succ]
    rfl

theorem homogeneousEquiv_symm_d (i : ℕ) (σ : (homogeneousCochains X).X i) :
    (homogeneousEquiv X (i + 1)).symm (((homogeneousCochains X).d i (i + 1)).hom σ) =
      (dLocallyConstant (underlyingRep X) i).hom ((homogeneousEquiv X i).symm σ) := by
  apply Subtype.ext
  funext g
  rw [dLocallyConstant_hom_apply]
  change nestedHomeomorph X (i + 2) (((homogeneousCochains X).d i (i + 1)).hom σ).1
    (Fin.partialProd g) = _
  rw [homogeneousCochains.d_apply]
  exact nestedHomeomorph_d_partialProd X i σ g

noncomputable def cochainsIsoHomogeneousCochains :
    cochainsComplex (underlyingRep X) ≅
      ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).mapHomologicalComplex _).obj
        (homogeneousCochains X) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (homogeneousEquiv X n).toModuleIso) (by
    rintro i j (rfl : i + 1 = j)
    rw [cochainsComplex_d]
    ext φ : 2
    obtain ⟨σ, rfl⟩ := (homogeneousEquiv X i).symm.surjective φ
    change ((homogeneousCochains X).d i (i + 1)).hom (homogeneousEquiv X i
      ((homogeneousEquiv X i).symm σ)) = homogeneousEquiv X (i + 1)
        ((dLocallyConstant (underlyingRep X) i).hom ((homogeneousEquiv X i).symm σ))
    rw [LinearEquiv.apply_symm_apply]
    exact (homogeneousEquiv X (i + 1)).symm_apply_eq.1 (homogeneousEquiv_symm_d X i σ))

noncomputable def cohomologyIsoContinuousCohomology (n : ℕ) :
    cohomology (underlyingRep X) n ≅
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).obj (continuousCohomology n X) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (cochainsIsoHomogeneousCochains X) ≪≫
    ((homogeneousCochains X).sc n).mapHomologyIso (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))

noncomputable def cohomologyLinearEquivContinuousCohomology (n : ℕ) :
    cohomology (underlyingRep X) n ≃ₗ[k]
      ((continuousCohomology n X : TopModuleCat.{u} k) : Type u) :=
  (cohomologyIsoContinuousCohomology X n).toLinearEquiv

section Discrete

variable [DiscreteTopology k]

noncomputable def cohomologyIsoContinuousCohomologyDiscrete (A : Rep.{u} k G) [IsDiscreteRep A]
    (n : ℕ) :
    cohomology A n ≅
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).obj
        (continuousCohomology n (discreteTopRep A)) :=
  cohomologyIsoContinuousCohomology (discreteTopRep A) n

noncomputable def cohomologyLinearEquivContinuousCohomologyDiscrete (A : Rep.{u} k G)
    [IsDiscreteRep A] (n : ℕ) :
    cohomology A n ≃ₗ[k]
      ((continuousCohomology n (discreteTopRep A) : TopModuleCat.{u} k) : Type u) :=
  cohomologyLinearEquivContinuousCohomology (discreteTopRep A) n

end Discrete

end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.NotDvdSuperIndexIffMap
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Pointwise CategoryTheory

variable {G : Type*} [Group G]

theorem sup_eq_comap_map (H U : Subgroup G) [U.Normal] :
    H ⊔ U = (H.map (QuotientGroup.mk' U)).comap (QuotientGroup.mk' U) := by
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']

theorem index_sup_eq_index_map (H U : Subgroup G) [U.Normal] :
    (H ⊔ U).index = (H.map (QuotientGroup.mk' U)).index := by
  rw [sup_eq_comap_map, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective U)]

variable [TopologicalSpace G]

noncomputable def quotMap {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    G ⧸ (U : Subgroup G) →* G ⧸ (V : Subgroup G) :=
  QuotientGroup.map _ _ (MonoidHom.id G) (fun _ hx => h hx)

theorem quotMap_comp_mk' {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    (quotMap h).comp (QuotientGroup.mk' (U : Subgroup G)) = QuotientGroup.mk' (V : Subgroup G) :=
  rfl

theorem quotMap_surjective {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    Function.Surjective (quotMap h) := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (V : Subgroup G) y
  exact ⟨QuotientGroup.mk' (U : Subgroup G) x, rfl⟩

theorem quotMap_self {U : OpenNormalSubgroup G} (h : U ≤ U) : quotMap h = MonoidHom.id _ :=
  MonoidHom.ext fun x => QuotientGroup.induction_on x fun _ => rfl

theorem quotMap_comp {U V W : OpenNormalSubgroup G} (h₁ : U ≤ V) (h₂ : V ≤ W) :
    (quotMap h₂).comp (quotMap h₁) = quotMap (h₁.trans h₂) :=
  MonoidHom.ext fun x => QuotientGroup.induction_on x fun _ => rfl

theorem map_map_quotMap (H : Subgroup G) {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    (H.map (QuotientGroup.mk' (U : Subgroup G))).map (quotMap h) =
      H.map (QuotientGroup.mk' (V : Subgroup G)) := by
  rw [Subgroup.map_map, quotMap_comp_mk']

def IsProSylow (p : ℕ) (P : Subgroup G) : Prop :=
  IsClosed (P : Set G) ∧ IsProPGroup p P ∧ ¬ Supernatural.ofNat p ∣ superIndex P

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
variable {p : ℕ} [hp : Fact p.Prime]

omit [TotallyDisconnectedSpace G] in

theorem not_dvd_superIndex_iff_map (H : Subgroup G) :
    ¬ Supernatural.ofNat p ∣ superIndex H ↔
      ∀ U : OpenNormalSubgroup G, ¬ p ∣ (H.map (QuotientGroup.mk' (U : Subgroup G))).index := by
  have h := not_dvd_superIndex_iff (⟨p, hp.out⟩ : Nat.Primes) H
  simp only [index_sup_eq_index_map] at h
  exact h

theorem isProSylow_iff {P : Subgroup G} (hP : IsClosed (P : Set G)) :
    IsProSylow p P ↔ ∀ U : OpenNormalSubgroup G,
      IsPGroup p (P.map (QuotientGroup.mk' (U : Subgroup G))) ∧
        ¬ p ∣ (P.map (QuotientGroup.mk' (U : Subgroup G))).index := by
  rw [IsProSylow, isProPGroup_subgroup_iff_isPGroup_map, not_dvd_superIndex_iff_map, ← forall_and]
  exact ⟨fun h => h.2, fun h => ⟨hP, h⟩⟩

noncomputable def IsProSylow.toSylow {P : Subgroup G} (hP : IsProSylow p P)
    (U : OpenNormalSubgroup G) : Sylow p (G ⧸ (U : Subgroup G)) :=
  IsPGroup.toSylow (isProPGroup_subgroup_iff_isPGroup_map.mp hP.2.1 U)
    ((not_dvd_superIndex_iff_map P).mp hP.2.2 U)

@[simp] theorem IsProSylow.coe_toSylow {P : Subgroup G} (hP : IsProSylow p P)
    (U : OpenNormalSubgroup G) :
    (hP.toSylow U : Subgroup (G ⧸ (U : Subgroup G))) = P.map (QuotientGroup.mk' (U : Subgroup G)) :=
  rfl

omit [CompactSpace G] [TotallyDisconnectedSpace G] in

noncomputable def sylowSystem (p : ℕ) [Fact p.Prime] (H : Subgroup G) :
    OpenNormalSubgroup G ⥤ Type _ where
  obj U := {S : Sylow p (G ⧸ (U : Subgroup G)) //
    H.map (QuotientGroup.mk' (U : Subgroup G)) ≤ (S : Subgroup (G ⧸ (U : Subgroup G)))}
  map {U V} f := ↾fun S => ⟨S.1.mapSurjective (quotMap_surjective (leOfHom f)), by
    rw [Sylow.coe_mapSurjective, ← map_map_quotMap H (leOfHom f)]
    exact Subgroup.map_mono S.2⟩
  map_id U := by
    ext ⟨S, hS⟩ x
    show x ∈ (S : Subgroup (G ⧸ (U : Subgroup G))).map (quotMap _) ↔
      x ∈ (S : Subgroup (G ⧸ (U : Subgroup G)))
    rw [quotMap_self, Subgroup.map_id]
  map_comp {U V W} f g := by
    ext ⟨S, hS⟩ x
    show x ∈ (S : Subgroup (G ⧸ (U : Subgroup G))).map (quotMap _) ↔
      x ∈ ((S : Subgroup (G ⧸ (U : Subgroup G))).map (quotMap (leOfHom f))).map
        (quotMap (leOfHom g))
    rw [Subgroup.map_map, quotMap_comp]

theorem exists_isProSylow_le {H : Subgroup G} (hH : IsProPGroup p H) :
    ∃ P : Subgroup G, IsProSylow p P ∧ H ≤ P := by
  rw [isProPGroup_subgroup_iff_isPGroup_map] at hH
  have hfin : ∀ U, Finite ((sylowSystem p H).obj U) := fun U => by
    have := Sylow.finite_of_finiteIndex (default : Sylow p (G ⧸ (U : Subgroup G)))
    exact Subtype.finite
  have hne : ∀ U, Nonempty ((sylowSystem p H).obj U) := fun U => by
    obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow (hH U)
    exact ⟨⟨S, hS⟩⟩
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system (sylowSystem p H)

  let T : OpenNormalSubgroup G → Subgroup G := fun U =>
    ((s U).1 : Subgroup (G ⧸ (U : Subgroup G))).comap (QuotientGroup.mk' (U : Subgroup G))
  have hc : ∀ {U V : OpenNormalSubgroup G} (h : U ≤ V),
      ((s V).1 : Subgroup (G ⧸ (V : Subgroup G))) =
        ((s U).1 : Subgroup (G ⧸ (U : Subgroup G))).map (quotMap h) := by
    intro U V h
    rw [← hs (homOfLE h)]
    rfl
  have hHT : ∀ U, H ≤ T U := fun U => Subgroup.map_le_iff_le_comap.mp (s U).2
  have hUT : ∀ U : OpenNormalSubgroup G, (U : Subgroup G) ≤ T U := fun U x hx => by
    show QuotientGroup.mk' (U : Subgroup G) x ∈ ((s U).1 : Subgroup _)
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hTcl : ∀ U, IsClosed (T U : Set G) := fun U =>
    Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono (hUT U) U.toOpenSubgroup.isOpen)
  have hTmono : ∀ {U V : OpenNormalSubgroup G}, U ≤ V → T U ≤ T V := fun {U V} h x hx => by
    show QuotientGroup.mk' (V : Subgroup G) x ∈ ((s V).1 : Subgroup _)
    rw [hc h]
    exact Subgroup.mem_map_of_mem (quotMap h) hx
  have hTlift : ∀ {U V : OpenNormalSubgroup G}, U ≤ V → ∀ x ∈ T V,
      ∃ y ∈ T U, y⁻¹ * x ∈ (V : Subgroup G) := fun {U V} h x hx => by
    have hx' : QuotientGroup.mk' (V : Subgroup G) x ∈ ((s V).1 : Subgroup _) := hx
    rw [hc h] at hx'
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx'
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (U : Subgroup G) z
    exact ⟨y, hz, QuotientGroup.eq.mp hzx⟩
  let P : Subgroup G := ⨅ U, T U
  have hPcl : IsClosed (P : Set G) := by
    rw [Subgroup.coe_iInf]
    exact isClosed_iInter hTcl
  have hPmap : ∀ U : OpenNormalSubgroup G,
      P.map (QuotientGroup.mk' (U : Subgroup G)) = ((s U).1 : Subgroup _) := by
    intro U
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr (iInf_le T U)) fun z hz => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (U : Subgroup G) z
    have hx : x ∈ T U := hz

    let t : OpenNormalSubgroup G → Set G := fun W =>
      (T (W ⊓ U) : Set G) ∩ {y | x⁻¹ * y ∈ (U : Subgroup G)}
    have htcl : ∀ W, IsClosed (t W) := fun W =>
      (hTcl _).inter ((Subgroup.isClosed_of_isOpen _ U.toOpenSubgroup.isOpen).preimage
        (continuous_const_mul x⁻¹))
    have htdir : Directed (· ⊇ ·) t := fun W₁ W₂ =>
      ⟨W₁ ⊓ W₂, fun y hy => ⟨hTmono (inf_le_inf_right U inf_le_left) hy.1, hy.2⟩,
        fun y hy => ⟨hTmono (inf_le_inf_right U inf_le_right) hy.1, hy.2⟩⟩
    have htne : ∀ W, (t W).Nonempty := fun W => by
      obtain ⟨y, hy, hyx⟩ := hTlift (inf_le_right : W ⊓ U ≤ U) x hx
      refine ⟨y, hy, ?_⟩
      have := (U : Subgroup G).inv_mem hyx
      rwa [mul_inv_rev, inv_inv] at this
    obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htdir
      htne (fun W => (htcl W).isCompact) htcl
    rw [Set.mem_iInter] at hy
    have hyP : y ∈ P := Subgroup.mem_iInf.mpr fun W => hTmono inf_le_left (hy W).1
    refine Subgroup.mem_map.mpr ⟨y, hyP, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq.mpr (hy U).2).symm
  refine ⟨P, (isProSylow_iff hPcl).mpr fun U => ?_, le_iInf fun U => hHT U⟩
  rw [hPmap U]
  exact ⟨(s U).1.isPGroup', (s U).1.not_dvd_index⟩

theorem exists_isProSylow : ∃ P : Subgroup G, IsProSylow p P :=
  let ⟨P, hP, _⟩ := exists_isProSylow_le (isProPGroup_bot (G := G) p)
  ⟨P, hP⟩

end GroundTheory.ProfCoh
end

