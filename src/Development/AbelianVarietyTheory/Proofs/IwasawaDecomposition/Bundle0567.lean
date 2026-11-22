import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPelUnifPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0563
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0564
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem admissibleBase_of_completeNormalLocalCharZero {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (h : IsCN R) :
    AdmBase R (maximalIdeal R) :=
  ⟨h.1, inferInstance, h.2.1, h.2.2.1⟩

theorem pullSt : PullSt := by
  intro E _ _ _ H R R' _ _ _ _ _ _ φ t P hR hR' hφ hloc _
  obtain ⟨h1, -, h3, h4, h5, -⟩ := GlobalTheory.allSixLaws
  have aR := admissibleBase_of_completeNormalLocalCharZero hR
  have aR' := admissibleBase_of_completeNormalLocalCharZero hR'
  have : CharZero R' := hR'.2.2.2
  have hI : (maximalIdeal R).map φ ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (map_mem_nonunits_iff φ a).2 ha
  obtain ⟨t', m₀, P', hD, -, -, -, -, xl, -⟩ :=
    GlobalTheory.ArcDataDescent.exists_pelUnif_pull h3.cubePull h1.polBaseChange h4.unifBaseChange h5 aR aR' t P φ hφ hI
  let e : P'.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X := { hD.xe with map_smul' := xl }
  exact ⟨t', m₀, P', e, GlobalTheory.FlatTors.torsionIso_holds E H R' _ aR' t' P',
    fun y r hr => GlobalTheory.PelCoordPull.psiCoord_pull hD y r hr⟩

end GlobalTheory.TorRef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AltSumMultilinear
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.PolarMultilinear

theorem powerset_map {α β : Type} (f : α → β) (s : Multiset α) :
    (s.map f).powerset = s.powerset.map (Multiset.map f) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.powerset_cons, ih, Multiset.map_map]

theorem powerset_val {α : Type} (s : Finset α) :
    s.val.powerset = s.powerset.val.map Finset.val := by
  simp [Finset.powerset, Multiset.map_pmap, Multiset.pmap_eq_map]

theorem alt_sum {d : ℕ} (r : Fin d → Fin d) :
    (∑ T : Finset (Fin d), if ∀ i, r i ∈ T then (-1 : ℝ) ^ (d - T.card) else 0) =
      if Function.Surjective r then 1 else 0 := by
  classical
  have h := Finset.prod_add (fun _ : Fin d => (1 : ℝ))
    (fun j : Fin d => if j ∈ Set.range r then (0 : ℝ) else -1) Finset.univ
  rw [Finset.powerset_univ] at h
  have h2 : ∀ T : Finset (Fin d), (if ∀ i, r i ∈ T then (-1 : ℝ) ^ (d - T.card) else 0) =
      (∏ _i ∈ T, (1 : ℝ)) * ∏ j ∈ Finset.univ \ T, (if j ∈ Set.range r then (0 : ℝ) else -1) := by
    intro T
    rw [Finset.prod_const_one, one_mul]
    split_ifs with hT
    · rw [Finset.prod_congr rfl (g := fun _ => (-1 : ℝ)), Finset.prod_const, Finset.card_univ_diff,
        Fintype.card_fin]
      intro j hj
      rw [if_neg]
      rintro ⟨i, rfl⟩
      exact (Finset.mem_sdiff.1 hj).2 (hT i)
    · obtain ⟨i, hi⟩ := not_forall.1 hT
      exact (Finset.prod_eq_zero (i := r i) (by simp [hi]) (by simp)).symm
  rw [Finset.sum_congr rfl fun T _ => h2 T, ← h]
  split_ifs with hs
  · refine Finset.prod_eq_one fun j _ => ?_
    rw [if_pos (show j ∈ Set.range r from hs j), add_zero]
  · obtain ⟨j, hj⟩ := not_forall.1 hs
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    rw [if_neg (show ¬ j ∈ Set.range r from hj)]; ring

theorem alt_sum_multilinear {A : Type} [AddCommGroup A] {d : ℕ}
    (M : MultilinearMap ℤ (fun _ : Fin d => A) ℝ)
    (hM : ∀ (σ : Equiv.Perm (Fin d)) (a : Fin d → A), M (a ∘ σ) = M a) (a : Fin d → A) :
    (∑ T : Finset (Fin d), (-1 : ℝ) ^ (d - T.card) * M fun _ => ∑ i ∈ T, a i) =
      (d.factorial : ℝ) * M a := by
  classical
  have h1 : ∀ T : Finset (Fin d), (-1 : ℝ) ^ (d - T.card) * (M fun _ => ∑ i ∈ T, a i) =
      ∑ r : Fin d → Fin d, (if ∀ i, r i ∈ T then (-1 : ℝ) ^ (d - T.card) else 0) * M (a ∘ r) := by
    intro T
    rw [M.map_sum_finset (fun _ i => a i) (fun _ => T), Finset.mul_sum]
    simp_rw [ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun r _ => rfl
    ext r
    simp [Fintype.mem_piFinset]
  rw [Finset.sum_congr rfl fun T _ => h1 T, Finset.sum_comm]
  simp_rw [← Finset.sum_mul, alt_sum, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  have h3 : (∑ r ∈ Finset.univ.filter (fun r : Fin d → Fin d => Function.Surjective r), M (a ∘ r)) =
      ∑ σ : Equiv.Perm (Fin d), M (a ∘ σ) := by
    symm
    refine Finset.sum_bij (fun σ _ => (σ : Fin d → Fin d)) ?_ ?_ ?_ ?_
    · intro σ _
      simpa using σ.surjective
    · intro σ _ τ _ h
      exact Equiv.ext (congrFun h)
    · intro r hr
      have hs : Function.Surjective r := by simpa using hr
      exact ⟨Equiv.ofBijective r (Finite.surjective_iff_bijective.1 hs), Finset.mem_univ _, rfl⟩
    · intro σ _
      rfl
  rw [h3]
  simp [hM, Fintype.card_perm]

theorem polar_diag : ∀ (A : Type) [AddCommGroup A] (d : ℕ) (M : MultilinearMap ℤ (fun _ : Fin d => A) ℝ),
    (∀ (σ : Equiv.Perm (Fin d)) (a : Fin d → A), M (a ∘ σ) = M a) →
    ∀ a : Fin d → A, polar (fun b => M fun _ => b) (Multiset.map a Finset.univ.val) = M a := by
  intro A _ d M hM a
  have hc : Multiset.card (Multiset.map a Finset.univ.val) = d := by simp
  unfold Pad.polar
  rw [hc, powerset_map, powerset_val, Multiset.map_map, Multiset.map_map, Finset.powerset_univ]
  have h := alt_sum_multilinear M hM a
  have h' : (Multiset.map (((fun T : Multiset A => (-1 : ℝ) ^ (d - Multiset.card T) * M fun _ => T.sum) ∘
      Multiset.map a) ∘ Finset.val) (Finset.univ : Finset (Finset (Fin d))).val).sum =
      (d.factorial : ℝ) * M a := by
    rw [← h, Finset.sum_eq_multiset_sum]
    congr 1
    refine Multiset.map_congr rfl fun T _ => ?_
    simp only [Function.comp, Multiset.card_map, Finset.card_val]
    rfl
  rw [h', ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast d.factorial_ne_zero), one_mul]

end GlobalTheory.ShFam.PolarMultilinear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmplePointsLocalizedModel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.TorRef

namespace GlobalTheory.TorRef.DomFine

theorem generalizing_of_stalk {Y : Scheme.{0}} {A : Type} [CommRing A] [IsLocalRing A] (ξ : Sp A ⟶ Y)
    (hf : (Scheme.stalkClosedPointTo ξ).hom.Flat) : GeneralizingMap ξ := by
  have h₁ : Flat (Spec.map (Scheme.stalkClosedPointTo ξ)) := by
    rw [Flat.SpecMap_iff]; exact hf
  have h₂ : GeneralizingMap (Y.fromSpecStalk (ξ (closedPoint _))) := by
    refine (Y.fromSpecStalk (ξ (closedPoint _))).isEmbedding.isInducing.generalizingMap ?_
    rw [Scheme.range_fromSpecStalk]
    exact fun a b hab hb => hab.trans hb
  have e : (ξ : Sp A → Y) = Y.fromSpecStalk (ξ (closedPoint _)) ∘ Spec.map (Scheme.stalkClosedPointTo ξ) := by
    funext p
    conv_lhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
    exact Scheme.Hom.comp_apply _ _ _
  rw [e]
  exact (Flat.generalizingMap _).comp h₂

theorem flat_stalk_of_comp {X Y : Scheme.{0}} {A : Type} [CommRing A] [IsLocalRing A] (ξ : Sp A ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion f] (hf : (Scheme.stalkClosedPointTo (ξ ≫ f)).hom.Flat) :
    (Scheme.stalkClosedPointTo ξ).hom.Flat := by
  rw [Scheme.stalkClosedPointTo_comp] at hf
  have e : Scheme.stalkClosedPointTo ξ =
      inv (f.stalkMap (ξ (closedPoint _))) ≫ (f.stalkMap (ξ (closedPoint _)) ≫ Scheme.stalkClosedPointTo ξ) := by
    simp
  rw [e, CommRingCat.hom_comp]
  refine RingHom.Flat.comp ?_ hf
  exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)

theorem eq_of_specializes {Y : Scheme.{0}} {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] (ξ : Sp A ⟶ Y)
    (hf : (Scheme.stalkClosedPointTo ξ).hom.Flat) (w : Sp (FractionRing A)) (q : Y) (h : q ⤳ (jK A ≫ ξ) w) :
    q = (jK A ≫ ξ) w := by
  rw [Scheme.Hom.comp_apply] at h ⊢
  obtain ⟨r, hr, rfl⟩ := generalizing_of_stalk ξ hf h
  have hw : (jK A w).asIdeal = ⊥ := by
    haveI : (PrimeSpectrum.asIdeal w).IsPrime := PrimeSpectrum.isPrime w
    have hw₀ : PrimeSpectrum.asIdeal w = ⊥ := Ideal.eq_bot_of_prime _
    ext x
    change algebraMap A (FractionRing A) x ∈ PrimeSpectrum.asIdeal w ↔ _
    rw [hw₀, Ideal.mem_bot, Ideal.mem_bot]
    exact map_eq_zero_iff _ (IsFractionRing.injective A (FractionRing A))
  have hle := (PrimeSpectrum.le_iff_specializes (R := A) r (jK A w)).mpr hr
  have : r = jK A w := by
    apply le_antisymm hle
    change (jK A w).asIdeal ≤ PrimeSpectrum.asIdeal r
    rw [hw]; exact bot_le
  rw [this]

theorem mem_range_of_generic {U V : Scheme.{0}} (j : U ⟶ V) [IsOpenImmersion j] (hd : Dense (Set.range j))
    [TopologicalSpace.NoetherianSpace V] (g : V) (hg : ∀ q : V, q ⤳ g → q = g) : g ∈ Set.range j := by
  have hc : closure {g} ∈ irreducibleComponents V := by
    refine ⟨isIrreducible_singleton.closure, fun S hS hle => ?_⟩
    have hq := hS.isGenericPoint_genericPoint_closure
    have hgS : g ∈ S := hle (subset_closure rfl)
    have e := hg _ (hq.specializes (subset_closure hgS))
    rw [e] at hq
    exact subset_closure.trans hq.def.symm.subset
  obtain ⟨o, ho, hne, hle⟩ := TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hc
  obtain ⟨u, hu, hu'⟩ := hd.inter_open_nonempty o ho hne
  have hs : g ⤳ u := specializes_iff_mem_closure.2 (hle hu)
  exact j.isOpenEmbedding.isOpen_range.stableUnderGeneralization hs hu'

theorem eq_of_jK {A B : Type} [CommRing A] [IsDomain A] [CommRing B] (u v : Sp A ⟶ Sp B) (h : jK A ≫ u = jK A ≫ v) :
    u = v := by
  obtain ⟨f, rfl⟩ := Spec.map_surjective u
  obtain ⟨g, rfl⟩ := Spec.map_surjective v
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  congr 1
  ext x
  apply IsFractionRing.injective A (FractionRing A)
  exact ConcreteCategory.congr_hom h' x

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem isUnit_of_point {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] [IsLocalRing R'] (a : O) (b : O →+* R)
    (hloc : @IsLocalization.Away O _ a R _ b.toAlgebra) {X : Scheme.{0}} (s : X ⟶ Sp O) (ξ₀ : Sp R' ⟶ X) (κ : O →+* R')
    (hκ : spMap κ = ξ₀ ≫ s) (x : ↥(pullback s (spMap b))) (hz : ξ₀ (closedPoint R') = pullback.fst s (spMap b) x) :
    IsUnit (κ a) := by
  by_contra hn
  have h1 : a ∈ PrimeSpectrum.asIdeal (spMap κ (closedPoint R')) := (mem_maximalIdeal _).2 hn
  have e : spMap κ (closedPoint R') = spMap b (pullback.snd s (spMap b) x) := by
    rw [hκ]
    refine (Scheme.Hom.comp_apply ξ₀ s _).trans ?_
    rw [hz]
    refine (Scheme.Hom.comp_apply (pullback.fst s (spMap b)) s x).symm.trans ?_
    rw [pullback.condition]
    exact Scheme.Hom.comp_apply _ _ x
  rw [e] at h1
  have h2 : b a ∈ PrimeSpectrum.asIdeal (pullback.snd s (spMap b) x) := h1
  have hu : IsUnit (b a) := by
    letI := b.toAlgebra
    haveI : IsLocalization.Away a R := hloc
    exact IsLocalization.Away.algebraMap_isUnit a
  exact (PrimeSpectrum.isPrime _).ne_top (Ideal.eq_top_of_isUnit_mem _ h2 hu)

theorem injective_of_flat {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [IsDomain A] [IsLocalRing A]
    {X : Scheme.{0}} (s : X ⟶ Sp O) (hs : Flat s) (ξ₀ : Sp A ⟶ X) (hfl : (Scheme.stalkClosedPointTo ξ₀).hom.Flat)
    (κ : O →+* A) (hκ : spMap κ = ξ₀ ≫ s) : Function.Injective ((algebraMap A (FractionRing A)).comp κ) := by
  have hsρ : spMap ((algebraMap A (FractionRing A)).comp κ) = (jK A ≫ ξ₀) ≫ s := by
    rw [← spMap_comp', hκ, Category.assoc]
  refine GlobalTheory.GenericFlat.injective_of_apply_eq_genericPoint _ (⊥ : PrimeSpectrum (FractionRing A)) ?_
  obtain ⟨y, hy, e⟩ := Flat.generalizingMap s
    (genericPoint_specializes (s ((jK A ≫ ξ₀) (⊥ : PrimeSpectrum (FractionRing A)))))
  have h := eq_of_specializes ξ₀ hfl (⊥ : PrimeSpectrum (FractionRing A)) y hy
  rw [hsρ]
  refine (Scheme.Hom.comp_apply (jK A ≫ ξ₀) s _).trans ?_
  rw [← h, e]

theorem exists_lift_frac {O F B : Type} [CommRing O] [IsDomain O] [Field F] [Algebra O F] [IsFractionRing O F] [CommRing B]
    (g : O →+* B) (hu : ∀ y : O, y ≠ 0 → IsUnit (g y)) : ∃ ρ : F →+* B, ρ.comp (algebraMap O F) = g := by
  have hu' : ∀ y : nonZeroDivisors O, IsUnit (g y) := fun y => hu _ (nonZeroDivisors.ne_zero y.2)
  exact ⟨IsLocalization.lift hu', IsLocalization.lift_comp hu'⟩

theorem exists_generic_fibre {O F A : Type} [CommRing O] [IsDomain O] [Field F] [Algebra O F] [IsFractionRing O F]
    [CommRing A] [IsDomain A] [IsLocalRing A] {X : Scheme.{0}} (s : X ⟶ Sp O) (hs : Flat s) (ξ₀ : Sp A ⟶ X)
    (hfl : (Scheme.stalkClosedPointTo ξ₀).hom.Flat) :
    ∃ v : Sp (FractionRing A) ⟶ pullback s (spMap (algebraMap O F)), v ≫ pullback.fst _ _ = jK A ≫ ξ₀ := by
  obtain ⟨κ', hκ'⟩ := Spec.map_surjective (ξ₀ ≫ s)
  obtain ⟨κ, rfl⟩ : ∃ κ : O →+* A, CommRingCat.ofHom κ = κ' := ⟨κ'.hom, rfl⟩
  have hκ : spMap κ = ξ₀ ≫ s := hκ'
  have hρ := injective_of_flat s hs ξ₀ hfl κ hκ
  obtain ⟨ρ', hρ'⟩ := exists_lift_frac (F := F) ((algebraMap A (FractionRing A)).comp κ) (fun y hy => by
    have h0 : κ y ≠ 0 := fun h => hy (hρ (by simp [h]))
    exact IsLocalization.map_units (FractionRing A) (⟨κ y, mem_nonZeroDivisors_of_ne_zero h0⟩ : nonZeroDivisors A))
  have hv : (jK A ≫ ξ₀) ≫ s = spMap ρ' ≫ spMap (algebraMap O F) := by
    rw [spMap_comp', hρ', ← spMap_comp', hκ, Category.assoc]
  exact ⟨pullback.lift (jK A ≫ ξ₀) _ hv, pullback.lift_fst _ _ _⟩

theorem exists_generic_point (O F : Type) [CommRing O] [IsDedekindDomain O] [Field F] [Algebra O F] [IsFractionRing O F]
    (X U : Scheme.{0}) (s : X ⟶ Sp O) (jQ : U ⟶ pullback s (spMap (algebraMap O F))) (hs : Flat s) (hp : IsProjOver s)
    (hj : IsOpenImmersion jQ) (hd : Dense (Set.range jQ)) {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    (ξ₀ : Sp A ⟶ X) (hfl : (Scheme.stalkClosedPointTo ξ₀).hom.Flat) :
    ∃ y : Sp (FractionRing A) ⟶ U, y ≫ jQ ≫ pullback.fst _ _ = jK A ≫ ξ₀ := by
  obtain ⟨v, v1⟩ := exists_generic_fibre (F := F) s hs ξ₀ hfl
  obtain ⟨hN, hC, -⟩ := GlobalTheory.genericPart_dense_proOpen O F X U s jQ hs hp hj hd
  haveI : IsNoetherian X := {}
  have hb0 : IsPreimmersion (spMap (algebraMap O F)) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of O) (S := F) (nonZeroDivisors O)
  haveI h1 : IsPreimmersion (pullback.fst s (spMap (algebraMap O F))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb0
  haveI hNs : TopologicalSpace.NoetherianSpace ↥(pullback s (spMap (algebraMap O F))) :=
    (pullback.fst s (spMap (algebraMap O F))).isEmbedding.isInducing.noetherianSpace
  have hr : Set.range v ⊆ Set.range jQ := by
    rintro _ ⟨w, rfl⟩
    refine mem_range_of_generic jQ hd _ fun q hq => ?_
    have h' := hq.map (pullback.fst s (spMap (algebraMap O F))).continuous
    have e : (pullback.fst s (spMap (algebraMap O F))) (v w) = (jK A ≫ ξ₀) w := by
      rw [← Scheme.Hom.comp_apply, v1]
    rw [e] at h'
    exact (pullback.fst s (spMap (algebraMap O F))).isEmbedding.injective ((eq_of_specializes ξ₀ hfl w _ h').trans e.symm)
  refine ⟨IsOpenImmersion.lift jQ v hr, ?_⟩
  rw [← Category.assoc, IsOpenImmersion.lift_fac, v1]

theorem exists_ext_at_points : FreeSt → ExtendSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (R : Type) [CommRing R] (a : 𝓞 c.F) (b : 𝓞 c.F →+* R) (ω : R →+* c.F) (C : Model Xo c ω), IsDedFrac ω → ω.comp b = algebraMap (𝓞 c.F) c.F → @IsLocalization.Away (𝓞 c.F) _ a R _ b.toAlgebra → ∀ (m : ℕ), 1 ≤ m → AmpAt C m → (∀ z : Z.X, ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ξ : Sp R' ⟶ Z.X) (t : SAB H (Sp R')) (_ : SABMap t Z.t ξ) (P : PELUnif (maximalIdeal R') t), IsCN R' ∧ ξ (closedPoint R') = z ∧ (Scheme.stalkClosedPointTo ξ).hom.Flat ∧ FineData P.D.toPre 1 ∧ FineData P.D.toPre (m ^ 2)) → ∀ jX : Xo.XF c ⟶ pullback Z.s (spMap b), jX ≫ pullback.fst _ _ = Z.j → ∀ x : ↥(pullback Z.s (spMap b)), ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ξ : Sp R' ⟶ pullback Z.s (spMap b)) (y : Sp (FractionRing R') ⟶ Xo.XF c) (χ : Sp R' ⟶ C.X), ξ (closedPoint R') = x ∧ (Scheme.stalkClosedPointTo ξ).hom.Flat ∧ y ≫ jX = jK R' ≫ ξ ∧ jK R' ≫ χ = y ≫ C.j ∧ χ ≫ C.s = ξ ≫ pullback.snd _ _ ∧ ∀ (w : Sp (FractionRing R')) (q : ↥(pullback Z.s (spMap b))), q ⤳ (jK R' ≫ ξ) w → q = (jK R' ≫ ξ) w := by
  intro hFree hExt E _ _ _ H D l Xo c Z R _ a b ω C hω hωb hloc m hm hAmp hpts jX hjX x
  haveI := c.fin
  haveI : NumberField c.F := {}
  have hβ : IsDedFrac (algebraMap (𝓞 c.F) c.F) := ⟨⟨inferInstance, inferInstance⟩, inferInstance,
    (inferInstance : IsFractionRing (𝓞 c.F) c.F)⟩
  haveI hopen : IsOpenImmersion (spMap b) := by
    letI := b.toAlgebra
    haveI : IsLocalization.Away a R := hloc
    exact IsOpenImmersion.of_isLocalization a
  obtain ⟨R', iR, iD, iL, ξ₀, t, μ, P, hCN, hz, hfl, hF1, hF2⟩ := hpts (pullback.fst Z.s (spMap b) x)
  obtain ⟨κ', hκ'⟩ := Spec.map_surjective (ξ₀ ≫ Z.s)
  obtain ⟨κ, rfl⟩ : ∃ κ : 𝓞 c.F →+* R', CommRingCat.ofHom κ = κ' := ⟨κ'.hom, rfl⟩
  have hκ : spMap κ = ξ₀ ≫ Z.s := hκ'
  have hua : IsUnit (κ a) := isUnit_of_point a b hloc Z.s ξ₀ κ hκ x hz
  obtain ⟨b', hb'⟩ : ∃ b' : R →+* R', b'.comp b = κ := by
    letI := b.toAlgebra
    haveI : IsLocalization.Away a R := hloc
    exact ⟨IsLocalization.Away.lift a hua, IsLocalization.Away.lift_comp a hua⟩
  have hsb : spMap b' ≫ spMap b = ξ₀ ≫ Z.s := by rw [spMap_comp', hb', hκ]
  obtain ⟨ξ, e1, e2⟩ : ∃ ξ : Sp R' ⟶ pullback Z.s (spMap b), ξ ≫ pullback.fst _ _ = ξ₀ ∧ ξ ≫ pullback.snd _ _ = spMap b' :=
    ⟨pullback.lift ξ₀ (spMap b') hsb.symm, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hinjf : Function.Injective (pullback.fst Z.s (spMap b)) := (pullback.fst Z.s (spMap b)).isOpenEmbedding.injective
  have hclosed : ξ (closedPoint R') = x := hinjf
    ((Scheme.Hom.comp_apply ξ (pullback.fst Z.s (spMap b)) _).symm.trans (by rw [e1]; exact hz))
  have hflat : (Scheme.stalkClosedPointTo ξ).hom.Flat :=
    flat_stalk_of_comp ξ (pullback.fst Z.s (spMap b)) (by rw [e1]; exact hfl)
  have hlast : ∀ (w : Sp (FractionRing R')) (q : ↥(pullback Z.s (spMap b))), q ⤳ (jK R' ≫ ξ) w → q = (jK R' ≫ ξ) w := by
    intro w q h
    apply hinjf
    have h' := h.map (pullback.fst Z.s (spMap b)).continuous
    have e : (pullback.fst Z.s (spMap b)) ((jK R' ≫ ξ) w) = (jK R' ≫ ξ₀) w := by
      rw [← Scheme.Hom.comp_apply, Category.assoc, e1]
    rw [e] at h' ⊢
    exact eq_of_specializes ξ₀ hfl w _ h'
  obtain ⟨y, hyj'⟩ := exists_generic_point (𝓞 c.F) c.F Z.X (Xo.XF c) Z.s Z.jQ Z.flat Z.proj Z.jQ_open Z.jQ_dense ξ₀ hfl
  have hyj : y ≫ Z.j = jK R' ≫ ξ₀ := hyj'
  have hyX : y ≫ jX = jK R' ≫ ξ := by
    rw [← cancel_mono (pullback.fst Z.s (spMap b)), Category.assoc, hjX, hyj, Category.assoc, e1]
  have hjs : Z.j ≫ Z.s = pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, Category.assoc, pullback.condition, ← Category.assoc, Z.jQ_over]
  have hjC : C.j ≫ C.s = pullback.snd _ _ ≫ spMap ω := by
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]
  have hs : jK R' ≫ spMap b' = (y ≫ pullback.snd _ _) ≫ spMap ω :=
    GlobalTheory.Models.Domination.eq_of_overring hβ hω hωb (jK R' ≫ spMap b') (y ≫ pullback.snd _ _) (by
      rw [Category.assoc, hsb, ← Category.assoc, ← hyj, Category.assoc, hjs, Category.assoc])
  have hC1 : y ≫ C.j ≫ C.s = jK R' ≫ spMap b' := by
    rw [hjC, hs, Category.assoc]
  obtain ⟨χ, hχ⟩ := hExt E H D l Xo c R (𝓞 c.F) ω (algebraMap _ _) C Z R' ξ₀ t μ y b' m hCN hyj hC1 hAmp
    (hFree E H R' t P 1 hCN le_rfl hF1) (hFree E H R' t P (m ^ 2) hCN (Nat.one_le_pow _ _ hm) hF2)
  refine ⟨R', iR, iD, iL, ξ, y, χ, hclosed, hflat, hyX, hχ, ?_, hlast⟩
  rw [e2]
  apply eq_of_jK
  rw [← Category.assoc, hχ, Category.assoc, hC1]

end GlobalTheory.TorRef.DomFine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopDensityModelMetricOriginStatement
section
open Formalism.DegreeFormula

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernTop_density_model_metric_origin : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n), GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p) (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 = GlobalTheory.TrueCx.grassConst p q ^ Fintype.card ι := by
  first | exact @GlobalTheory.DomainDens.chernTop_model_origin | exact GlobalTheory.DomainDens.chernTop_model_origin | (intros; apply GlobalTheory.DomainDens.chernTop_model_origin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmpStOfSabExtNormalSt
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal

namespace GlobalTheory.TorRef

theorem exists_sabMap_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.proved_CubePullSt f t
  exact ⟨_, ⟨m⟩⟩

theorem cmpSt_of_sabExtNormalSt : SabExtNormalSt → CmpSt := by
  intro hS E _ _ _ H D l Xo c O O' _ _ β β' Y Z ρ hρ hN
  have := isProper_genStr Z
  have : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  obtain ⟨t₀, ⟨n₁⟩⟩ := exists_sabMap_pull (genι Z) Z.t
  obtain ⟨t', ⟨n'⟩⟩ := exists_sabMap_pull (ρ ≫ genι Y) Y.t
  obtain ⟨a, ha⟩ := GlobalTheory.LevelCover.sab_cancel n₁ Z.m Z.jQ rfl
  obtain ⟨k, hk⟩ := GlobalTheory.LevelCover.sab_cancel Y.m0.toSABMap Z.m0.toSABMap (𝟙 _) (Category.id_comp _)
  obtain ⟨ky, hky⟩ := GlobalTheory.LevelCover.sab_comp k Y.m (e := Z.jQ ≫ ρ ≫ genι Y)
    (by rw [Category.id_comp, ← hρ, Category.assoc])
  obtain ⟨a', ha'⟩ := GlobalTheory.LevelCover.sab_cancel n' ky Z.jQ rfl
  have hdom : IsDominant Z.jQ := ⟨Z.jQ_dense⟩
  obtain ⟨b, hb⟩ := hS E H (gen Z) (Xo.XF c) Z.jQ hN Z.jQ_open hdom Z.oF.t t₀ t' a a' Z.oF.proper
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.LevelCover.sab_comp b n' (Category.id_comp _)
  refine ⟨t₀, n₁, n₂, fun T g g₁ g₂ h₁ h₂ h₃ h₄ => ?_⟩
  have hg : g = g₁ ≫ a.φ := by
    apply n₁.cart.1.hom_ext
    · rw [h₂, Category.assoc, ha]
    · rw [h₁, Category.assoc, a.cart.1.w]
  have hg₂ : g₁ ≫ k.φ = g₂ := by
    apply Y.m0.toSABMap.cart.1.hom_ext
    · rw [Category.assoc, hk, h₃]
    · rw [Category.assoc, k.cart.1.w, Category.comp_id, h₄]
  rw [hn₂, hg]
  simp only [Category.assoc]
  rw [reassoc_of% hb, ha', hky, reassoc_of% hg₂]

end GlobalTheory.TorRef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientMapExtensionOverEnlargedBaseStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coefficientMap_extension_over_enlarged_base : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std →
  ∀ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks)
    (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
    Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
    BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R'.toRealDat → RSideW z Wt' R' →
    ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ c0L, GlobalTheory.Mem.R3.Rw.OmExt.CoefFam z.R.toRealDat c0L →
      (∀ x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0, x = 0) ∨
      ∃ c0L', GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R'.toRealDat c0L' ∧
        ∀ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL),
          HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) → HEq (c0L' i' v') (c0L i v) := by
  first | exact @GlobalTheory.Mem.R3.Rw.OmCoef.exists_coefFam_ext | exact GlobalTheory.Mem.R3.Rw.OmCoef.exists_coefFam_ext | (intros; apply GlobalTheory.Mem.R3.Rw.OmCoef.exists_coefFam_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataNonzeroIndexPlacesCorrespondStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendedData_nonzero_index_places_correspond_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ v v', Below (w.D Z) (w'.D Z') v v' → (v ∈ z.W1 (fun _ _ => 0) ↔ v' ∈ z'.W1 fun _ _ => 0)) := by
  first | exact @GlobalTheory.Mem.R3.TwistedPlaceExtensions.extendedData_nonzero_index_places_correspond | exact GlobalTheory.Mem.R3.TwistedPlaceExtensions.extendedData_nonzero_index_places_correspond | (intros; apply GlobalTheory.Mem.R3.TwistedPlaceExtensions.extendedData_nonzero_index_places_correspond <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromTestAndValLaws
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.ShFam

theorem FlagCpt.fromTest_and_val_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e), (letI := (constF e C.Y).toAlgebra; FromTest (K := c.F) (fun R _ _ => FrPt Xo c R) (fun φ y z => FrMap φ y z) C.y0) ∧ C.val 1 = 1 ∧ (∀ f g, C.val (f * g) = C.val f * C.val g) ∧ (∀ f g, C.val (f + g) = C.val f + C.val g) ∧ ∀ (a : c.F) f, C.val (a • f) = constF e C.Y a * C.val f := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C
  letI := (constF e C.Y).toAlgebra
  have hA : AllTest Xo c :=
    GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c
  have hT := hA C.Y.Fn C.y0
  exact ⟨hT, evalAt_one _ _ C.y0 hT, fun f g => evalAt_mul _ _ f g C.y0,
    fun f g => evalAt_add _ _ f g C.y0, fun a f => evalAt_smul _ _ a f C.y0⟩

end GlobalTheory.ShFam
end

