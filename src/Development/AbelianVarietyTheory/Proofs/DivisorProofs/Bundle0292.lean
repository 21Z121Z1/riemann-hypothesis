import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0257
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0258
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfFieldPointRelationProper
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FieldPointGraph

theorem epi_spMap {K K' : Type} [Field K] [Field K'] (ι : K →+* K') : Epi (spMap ι) := by
  have : Flat (spMap ι) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := ι.toAlgebra
    exact (inferInstance : Module.Flat K K')
  have : Surjective (spMap ι) := ⟨fun y => ⟨IsLocalRing.closedPoint K', Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

noncomputable def pt (K : Type) [Field K] : Sp K := IsLocalRing.closedPoint K

theorem eq_pt {K : Type} [Field K] (t : Sp K) : t = pt K := Subsingleton.elim _ _

theorem exists_eq_spMap_comp {X : Scheme.{0}} {K : Type} [Field K] (c : Sp K ⟶ X) {x : X}
    (hx : c (pt K) = x) :
    ∃ ι : X.residueField x →+* K, c = spMap ι ≫ X.fromSpecResidueField x := by
  subst hx
  exact ⟨_, (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X c).symm⟩

theorem exists_valuationRing_factor {R K : Type} [CommRing R] [IsLocalRing R] [Field K]
    (f : R →+* K) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A) (φ : R →+* A)
      (ι : FractionRing A →+* K), IsLocalHom φ ∧
        ι.comp ((algebraMap A (FractionRing A)).comp φ) = f := by
  obtain ⟨A, hA, hl⟩ := IsLocalRing.exists_factor_valuationRing f
  refine ⟨A, inferInstance, inferInstance, inferInstance, f.codRestrict A.toSubring hA,
    IsFractionRing.lift (A := A) (g := A.subtype) Subtype.val_injective, hl, ?_⟩
  ext a
  exact IsFractionRing.lift_algebraMap (A := A) (g := A.subtype) Subtype.val_injective _

theorem exists_valuationRing_of_specializes {X : Scheme.{0}} {x y : X} (h : x ⤳ y) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A) (u : Sp A ⟶ X)
      (ι : FractionRing A →+* X.residueField x),
      spMap ι ≫ spMap (algebraMap A (FractionRing A)) ≫ u = X.fromSpecResidueField x ∧
        (spMap (IsLocalRing.residue A) ≫ u) (pt _) = y := by
  obtain ⟨A, _, _, _, φ, ι, hl, hf⟩ := exists_valuationRing_factor
    (X.presheaf.stalkSpecializes h ≫ X.residue x).hom
  refine ⟨A, inferInstance, inferInstance, inferInstance, spMap φ ≫ X.fromSpecStalk y, ι, ?_, ?_⟩
  · have e : spMap ι ≫ spMap (algebraMap A (FractionRing A)) ≫ spMap φ =
        Spec.map (X.presheaf.stalkSpecializes h ≫ X.residue x) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hf]
      rfl
    refine Eq.trans ?_ ((congrArg (· ≫ X.fromSpecStalk y) e).trans ?_)
    · simp only [Category.assoc]
    · rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
      rfl
  · have e1 : (spMap (IsLocalRing.residue A)) (pt _) = IsLocalRing.closedPoint A :=
      IsLocalRing.comap_closedPoint (IsLocalRing.residue A)
    have e2 : (spMap φ) (IsLocalRing.closedPoint A) = IsLocalRing.closedPoint _ :=
      IsLocalRing.comap_closedPoint φ
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, e1]
    exact (congrArg (X.fromSpecStalk y) e2).trans Scheme.fromSpecStalk_closedPoint

theorem exists_section {W Q : Scheme.{0}} (r : W ⟶ Q) [IsProper r] [IsNoetherian Q]
    [GlobalTheory.IsNormalScheme Q] (G : ∀ (K : Type) [Field K], (Sp K ⟶ W) → Prop)
    (hU : ∀ (K : Type) [Field K] (z : Sp K ⟶ Q), ∃! c, G K c ∧ c ≫ r = z)
    (hB : ∀ (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (c : Sp K ⟶ W),
      G K c → G K' (spMap ι ≫ c))
    (hV : ∀ (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] (u : Sp A ⟶ W),
      G (FractionRing A) (spMap (algebraMap A (FractionRing A)) ≫ u) →
      G (IsLocalRing.ResidueField A) (spMap (IsLocalRing.residue A) ≫ u)) :
    ∃ s : Q ⟶ W, s ≫ r = 𝟙 Q ∧ ∀ (K : Type) [Field K] (z : Sp K ⟶ Q), G K (z ≫ s) := by

  have hD : ∀ (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (c : Sp K ⟶ W),
      G K' (spMap ι ≫ c) → G K c := by
    intro K K' _ _ ι c hc
    obtain ⟨d, ⟨hd, hdr⟩, -⟩ := hU K (c ≫ r)
    have e : spMap ι ≫ c = spMap ι ≫ d :=
      (hU K' (spMap ι ≫ c ≫ r)).unique ⟨hc, Category.assoc _ _ _⟩
        ⟨hB _ _ ι d hd, by rw [Category.assoc, hdr]⟩
    have := epi_spMap ι
    rwa [(cancel_epi _).mp e]
  let T : Set W := {x | G (W.residueField x) (W.fromSpecResidueField x)}
  have hT : ∀ (K : Type) [Field K] (c : Sp K ⟶ W),
      G K c ↔ c (pt K) ∈ T := by
    intro K _ c
    obtain ⟨ι, hι⟩ := exists_eq_spMap_comp c rfl
    exact ⟨fun h => hD _ _ ι _ (hι ▸ h), fun h => by rw [hι]; exact hB _ _ ι _ h⟩
  have hspec : ∀ x y : W, x ⤳ y → x ∈ T → y ∈ T := by
    intro x y h hx
    obtain ⟨A, _, _, _, u, ι, hu, hy⟩ := exists_valuationRing_of_specializes h
    have h1 := hV A u (hD _ _ ι _ (hu ▸ hx))
    rwa [hT, hy] at h1
  choose g hg hg' using fun y : Q => hU (Q.residueField y) (Q.fromSpecResidueField y)
  let γ : Q → W := fun y => g y (pt _)
  have hγT : ∀ y, γ y ∈ T := fun y => (hT _ _).mp (hg y).1
  have hγr : ∀ y, r (γ y) = y := fun y => by
    refine (Scheme.Hom.comp_apply (g y) r _).symm.trans ?_
    rw [(hg y).2]
    exact Scheme.fromSpecResidueField_apply _ _
  have hTγ : ∀ x ∈ T, x = γ (r x) := by
    intro x hx
    have hpt : (W.fromSpecResidueField x ≫ r) (pt (W.residueField x)) =
        r x := by
      rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    obtain ⟨ι, hι⟩ := exists_eq_spMap_comp (K := W.residueField x) _ hpt
    have e : W.fromSpecResidueField x = spMap ι ≫ g (r x) :=
      (hU (W.residueField x) (W.fromSpecResidueField x ≫ r)).unique ⟨hx, rfl⟩
        ⟨hB _ _ ι _ (hg _).1, by rw [Category.assoc, (hg _).2, hι]⟩
    have e1 := Scheme.fromSpecResidueField_apply x (pt (W.residueField x))
    refine e1.symm.trans ?_
    rw [e, Scheme.Hom.comp_apply]
    exact congrArg (g (r x)) (eq_pt _)
  have hfin : (γ '' genericPoints Q).Finite :=
    (genericPoints.finite NoetherianSpace.finite_irreducibleComponents).image γ
  have hsub : closure (γ '' genericPoints Q) ⊆ T := by
    intro x hx
    rw [← Set.biUnion_of_singleton (γ '' genericPoints Q), hfin.closure_biUnion] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨_, ⟨y, -, rfl⟩, hx⟩ := hx
    exact hspec _ _ (specializes_iff_mem_closure.mpr hx) (hγT y)
  have hcl : IsClosed T := by
    have hsurj : r '' closure (γ '' genericPoints Q) = Set.univ := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← genericPoints.closure (α := Q)]
      refine closure_minimal (fun y hy => ⟨γ y, subset_closure ⟨y, hy, rfl⟩, hγr y⟩)
        (r.isClosedMap _ isClosed_closure)
    have : T = closure (γ '' genericPoints Q) := by
      refine Set.Subset.antisymm (fun x hx => ?_) hsub
      obtain ⟨x', hx', e⟩ : r x ∈ r '' closure (γ '' genericPoints Q) := hsurj ▸ Set.mem_univ _
      rwa [hTγ x hx, ← e, ← hTγ x' (hsub hx')]
    rw [this]
    exact isClosed_closure
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨T, hcl⟩ : Closeds W)
  have hI : Set.range I.subschemeι = T := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  have hGI : ∀ (K : Type) [Field K] (c : Sp K ⟶ I.subscheme), G K (c ≫ I.subschemeι) := by
    intro K _ c
    rw [hT, ← hI, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have : IsIso (I.subschemeι ≫ r) := by
    refine GlobalTheory.isIso_of_isProper_of_existsUnique_field_point _ _ _ inferInstance
      (ReducedSubgroup.isReduced_subscheme_vanishingIdeal _) (GlobalTheory.IsNormalScheme.pred _)
      inferInstance fun K _ z => ?_
    obtain ⟨c, ⟨hc, hcr⟩, hu⟩ := hU K z
    have hker : I.subschemeι.ker ≤ c.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      refine ReducedSubgroup.vanishingIdeal_le_ker c _ ?_
      rintro _ ⟨t, rfl⟩
      rw [eq_pt t]
      exact (hT K c).mp hc
    have hl := IsClosedImmersion.lift_fac I.subschemeι c hker
    refine ⟨IsClosedImmersion.lift I.subschemeι c hker, ?_, fun d hd => ?_⟩
    · show _ ≫ _ ≫ _ = _
      rw [← Category.assoc, hl, hcr]
    · rw [← cancel_mono I.subschemeι, hl]
      exact hu _ ⟨hGI K d, (Category.assoc _ _ _).trans hd⟩
  refine ⟨inv (I.subschemeι ≫ r) ≫ I.subschemeι, ?_, fun K _ z => ?_⟩
  · rw [Category.assoc, IsIso.inv_hom_id]
  · rw [← Category.assoc]
    exact hGI K _

theorem exists_hom_of_rel : ∀ (Q P S : Scheme.{0}) (q : Q ⟶ S) (p : P ⟶ S) [IsProper p] [IsNoetherian Q] [GlobalTheory.IsNormalScheme Q] (R : ∀ (K : Type) [Field K], (Sp K ⟶ Q) → (Sp K ⟶ P) → Prop), (∀ (K : Type) [Field K] (z : Sp K ⟶ Q) (w : Sp K ⟶ P), R K z w → z ≫ q = w ≫ p) → (∀ (K : Type) [Field K] (z : Sp K ⟶ Q), ∃! w, R K z w) → (∀ (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (z : Sp K ⟶ Q) (w : Sp K ⟶ P), R K z w → R K' (spMap ι ≫ z) (spMap ι ≫ w)) → (∀ (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] (u : Sp A ⟶ Q) (v : Sp A ⟶ P), u ≫ q = v ≫ p → R (FractionRing A) (spMap (algebraMap A (FractionRing A)) ≫ u) (spMap (algebraMap A (FractionRing A)) ≫ v) → R (IsLocalRing.ResidueField A) (spMap (IsLocalRing.residue A) ≫ u) (spMap (IsLocalRing.residue A) ≫ v)) → ∃ h : Q ⟶ P, h ≫ p = q ∧ ∀ (K : Type) [Field K] (z : Sp K ⟶ Q), R K z (z ≫ h) := by
  intro Q P S q p _ _ _ R hC hU hB hV
  obtain ⟨s, hs, hG⟩ := exists_section (pullback.fst q p)
    (fun K _ c => R K (c ≫ pullback.fst q p) (c ≫ pullback.snd q p))
    (fun K _ z => by
      obtain ⟨w, hw, hu⟩ := hU K z
      refine ⟨pullback.lift z w (hC K z w hw), ⟨?_, pullback.lift_fst _ _ _⟩, fun c hc => ?_⟩
      · rwa [pullback.lift_fst, pullback.lift_snd]
      · refine pullback.hom_ext (by rw [pullback.lift_fst, hc.2]) ?_
        rw [pullback.lift_snd]
        exact hu _ (hc.2 ▸ hc.1))
    (fun K K' _ _ ι c hc => by
      rw [Category.assoc, Category.assoc]
      exact hB K K' ι _ _ hc)
    (fun A _ _ _ u hu => by
      rw [Category.assoc, Category.assoc] at hu ⊢
      exact hV A _ _ (by simp [pullback.condition]) hu)
  refine ⟨s ≫ pullback.snd q p, ?_, fun K _ z => ?_⟩
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc, hs, Category.id_comp]
  · have := hG K z
    rwa [Category.assoc, Category.assoc, hs, Category.comp_id] at this

end GlobalTheory.FieldPointGraph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIotaScalarExactPairStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iota_scalar_exact_pair : ∀ (C : Type) [Field C] (N : ℕ) (α β : Matrix (Fin N) (Fin N) C), α * β = 0 → β * α = 0 → (∀ x, α *ᵥ x = 0 → ∃ y, x = β *ᵥ y) → ∃ lam : C, lam ≠ 0 ∧ IotaScalar α β β.rank lam := by
  first | exact @GlobalTheory.DetInv.ScalarEx.exists_iotaScalar | exact GlobalTheory.DetInv.ScalarEx.exists_iotaScalar | (intros; apply GlobalTheory.DetInv.ScalarEx.exists_iotaScalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHOfIsFrob
section
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem exists_isH_of_isFrob : ∀ {K Kt : Type} [CommRing K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) (F F' : Kt →+* Kt), IsFlatLift p π → IsFrob p π F → IsFrob p π F' →
    ∃ h, IsH p π F F' h := by
  intro K Kt _ _ p _ _ π F F' hL hF hF'
  have hex : ∀ z, ∃ w, F' z = F z + p * w := by
    intro z
    obtain ⟨w, hw⟩ := (hL.ker (F' z - F z)).1 (by rw [map_sub, hF, hF', sub_self])
    exact ⟨w, by rw [← hw]; ring⟩
  have huniq : ∀ z w w', F' z = F z + p * w → F' z = F z + p * w' → π w = π w' := by
    intro z w w' h1 h2
    have h3 : (p : Kt) * (w - w') = 0 := by rw [mul_sub]; linear_combination h2 - h1
    have h4 := (hL.ann (w - w')).1 h3
    rw [map_sub] at h4
    exact sub_eq_zero.1 h4
  let g : Kt → K := fun z => π (Classical.choose (hex z))
  have hg : ∀ z w, F' z = F z + p * w → g z = π w := fun z w hw =>
    huniq z _ w (Classical.choose_spec (hex z)) hw
  have hgadd : ∀ z z', g (z + z') = g z + g z' := by
    intro z z'
    obtain ⟨w, h1⟩ := hex z
    obtain ⟨w', h2⟩ := hex z'
    rw [hg z w h1, hg z' w' h2, hg (z + z') (w + w') (by rw [map_add, map_add, h1, h2]; ring), map_add]
  have hgp : ∀ y, g (p * y) = 0 := by
    intro y
    obtain ⟨w, h1⟩ := hex y
    rw [hg (p * y) (p * w) (by rw [map_mul, map_mul, map_natCast, map_natCast, h1]; ring), map_mul,
      map_natCast, CharP.cast_eq_zero, zero_mul]
  have hgmul : ∀ z z', g (z * z') = π z' ^ p * g z + π z ^ p * g z' := by
    intro z z'
    obtain ⟨w, h1⟩ := hex z
    obtain ⟨w', h2⟩ := hex z'
    rw [hg z w h1, hg z' w' h2, hg (z * z') (w * F z' + F z * w' + p * w * w')
      (by rw [map_mul, map_mul, h1, h2]; ring)]
    simp only [map_add, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]
    rw [hF z, hF z']
    ring
  have hwd : ∀ z z', π z = π z' → g z = g z' := by
    intro z z' hzz
    obtain ⟨y, hy⟩ := (hL.ker (z - z')).1 (by rw [map_sub, hzz, sub_self])
    have : z = z' + p * y := by rw [← hy]; ring
    rw [this, hgadd, hgp, add_zero]
  let φ : K →+ K := AddMonoidHom.mk' (fun x => g (Function.surjInv hL.surj x)) (by
    intro a b
    show g _ = g _ + g _
    rw [← hgadd]
    apply hwd
    rw [map_add, Function.surjInv_eq hL.surj, Function.surjInv_eq hL.surj, Function.surjInv_eq hL.surj])
  have hφ : ∀ z, φ (π z) = g z := by
    intro z
    show g _ = g _
    exact hwd _ _ (Function.surjInv_eq hL.surj _)
  obtain ⟨f, hfs, hfD⟩ := GlobalTheory.T.frobeniusDerivation_factors_through_kaehler (M := K) p φ (by
    intro a b
    obtain ⟨z, rfl⟩ := hL.surj a
    obtain ⟨z', rfl⟩ := hL.surj b
    rw [← map_mul, hφ, hφ, hφ, hgmul, smul_eq_mul, smul_eq_mul]; ring)
  refine ⟨f, fun c v => by rw [hfs, smul_eq_mul], fun z w hzw => ?_⟩
  rw [hfD, hφ, hg z w hzw]

end GlobalTheory.DI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitDetKrylovMatrixOfSeparableStatement
section
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isUnit_det_krylovMatrix_of_separable : ∀ {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F), y.charpoly.Separable → ∃ e : Fin r → F, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det := by
  first | exact @GlobalTheory.LeviDesc.Krylov.exists_isUnit_det_krylov_of_separable | exact GlobalTheory.LeviDesc.Krylov.exists_isUnit_det_krylov_of_separable | (intros; apply GlobalTheory.LeviDesc.Krylov.exists_isUnit_det_krylov_of_separable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicGraphDetLowerRowNeZeroField
section
open scoped Matrix

namespace GlobalTheory

theorem exists_isotropic_graph_det_lowerRow_ne_zero_field :
    ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → (∃ ε : k, ε ≠ 0 ∧ σ ε = -ε) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) k), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k, g.det ≠ 0 →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map σ = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) k, Zᵀ * J + J * Z.map σ = 0 ∧
        (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det ≠ 0 := by
  intro k _ σ hσ hε n J hJ hJd g hg hQ
  obtain ⟨ε, hε0, hε⟩ := hε
  have hmm : ∀ A : Matrix (Fin n) (Fin n) k, (A.map σ).map σ = A := by
    intro A; ext i j; simp [hσ]
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJd
  set K : Matrix (Fin n) (Fin n) k := J⁻¹ with hK
  have hJK : J * K = 1 := Matrix.mul_nonsing_inv J hJu
  have hKJ : K * J = 1 := Matrix.nonsing_inv_mul J hJu
  have hJh : (J.map σ)ᵀ = J := by ext i j; simp [hJ]
  have hKh : (K.map σ)ᵀ = K := by
    have h1 : (K.map σ)ᵀ * J = 1 := by
      conv_lhs => rw [← hJh]
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hJK]
      simp
    calc (K.map σ)ᵀ = (K.map σ)ᵀ * (J * K) := by rw [hJK, Matrix.mul_one]
      _ = K := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hKt : Kᵀ = K.map σ := by
    conv_lhs => rw [← hKh]
    simp
  have hQR : Matrix.fromBlocks 0 K K 0 * Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) k) J J 0
      = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) := by
    rw [Matrix.fromBlocks_multiply]
    simp [hKJ]
  have hRQ : Matrix.fromBlocks 0 J J 0 * Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) k) K K 0
      = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) := mul_eq_one_comm.mp hQR
  have h2 : (Matrix.fromBlocks 0 K K 0 * gᵀ * Matrix.fromBlocks 0 J J 0) * g.map σ = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᵀ, hQ, hQR]
  have h3 := mul_eq_one_comm.mp h2
  have h4 : g.map σ * Matrix.fromBlocks 0 K K 0 * gᵀ = Matrix.fromBlocks 0 K K 0 := by
    calc g.map σ * Matrix.fromBlocks 0 K K 0 * gᵀ
        = g.map σ * Matrix.fromBlocks 0 K K 0 * gᵀ *
          (Matrix.fromBlocks 0 J J 0 * Matrix.fromBlocks 0 K K 0) := by rw [hRQ, Matrix.mul_one]
      _ = (g.map σ * (Matrix.fromBlocks 0 K K 0 * gᵀ * Matrix.fromBlocks 0 J J 0)) *
          Matrix.fromBlocks 0 K K 0 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h3, Matrix.one_mul]
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, g = Matrix.fromBlocks A B C D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks g).symm⟩
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at h4
  have h5 := h4.2.2.2
  simp only [Matrix.mul_zero, zero_add, add_zero] at h5
  have h6 : D * K.map σ * (C.map σ)ᵀ + C * K.map σ * (D.map σ)ᵀ = 0 := by
    have := congrArg (fun M : Matrix (Fin n) (Fin n) k => M.map σ) h5
    simp only [Matrix.map_add σ (map_add σ), Matrix.map_mul, hmm, Matrix.map_zero σ (map_zero σ)] at this
    simpa [Matrix.transpose_map] using this
  have hJσ : K.map σ * J.map σ = 1 := by
    rw [← Matrix.map_mul, hKJ]; simp
  obtain ⟨V, hV, hdet⟩ := GlobalTheory.T.exists_skewHermitian_mul_add_det_ne_zero k σ hσ ε hε0 hε n (C * K.map σ) D
    (by
      rw [Matrix.map_mul, hmm, Matrix.transpose_mul, hKt, ← Matrix.mul_assoc, add_comm]
      exact h6)
    (by
      intro a ha hD
      have hC : a ᵥ* C = 0 := by
        have : a ᵥ* (C * K.map σ * J.map σ) = 0 := by
          rw [← Matrix.vecMul_vecMul, ha, Matrix.zero_vecMul]
        rwa [Matrix.mul_assoc, hJσ, Matrix.mul_one] at this
      have h7 : (Sum.elim 0 a) ᵥ* Matrix.fromBlocks A B C D = 0 := by
        rw [Matrix.vecMul_fromBlocks]
        simp [hC, hD]
      have h8 := Matrix.eq_zero_of_vecMul_eq_zero hg h7
      funext i
      exact congrFun h8 (Sum.inr i))
  refine ⟨K.map σ * V, ?_, ?_⟩
  · rw [Matrix.transpose_mul, hKh, Matrix.mul_assoc, hKJ, Matrix.mul_one, Matrix.map_mul, hmm,
      ← Matrix.mul_assoc, hJK, Matrix.one_mul]
    have : V.map σ = -Vᵀ := by
      rw [← Matrix.transpose_neg, ← hV, Matrix.transpose_transpose]
    rw [this, add_neg_cancel]
  · simpa [Matrix.mul_assoc] using hdet

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJetExtensionSquareZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

theorem exists_jet_factor {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) {k : K.K} {T : K.Obj} (f₁ f₂ : K.triv k ⟶ T) (n : Fin g → T.C) (hd : f₁.deg = f₂.deg)
    (hJ : ∀ a, n a ∈ T.J) (hn : ∀ a b, n a * n b = 0)
    (hf : ∀ x : Hol (K.W k), f₂.φ x = f₁.φ x + ∑ a, f₁.φ (dw a x : Hol (K.W k)) * n a) :
    ∃ χ : K.jet k ⟶ T, χ.deg = f₁.deg ∧ jet0 k ≫ χ = f₁ ∧ jet1 k ≫ χ = f₂ ∧
      ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)),
        χ.φ x = f₁.φ (x.fst : Hol (K.W k)) + ∑ a, f₁.φ (x.snd a : Hol (K.W k)) * n a := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet
  | exact @_root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet
  | exact _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet
  | (apply _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet <;> assumption)
  | (intros; apply _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet ..)

end GlobalTheory.AnPer.Charts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearIndependentIterates
section
open Polynomial Matrix

namespace GlobalTheory.ConjLocal

variable {R : Type} [CommRing R] {n : ℕ}

def iterMat (Y : Matrix (Fin n) (Fin n) R) (v : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => (Y ^ (j : ℕ) *ᵥ v) i

def compMat (Q : R[X]) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if (j : ℕ) + 1 < n then (if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) else -Q.coeff i

theorem exists_linearIndependent_iterates {K : Type} [Field K] (M : Matrix (Fin n) (Fin n) K)
    (hs : M.charpoly.Separable) :
    ∃ v : Fin n → K, LinearIndependent K (fun j : Fin n => (M ^ (j : ℕ)) *ᵥ v) := by
  obtain ⟨e, -, he⟩ := Formalism.IrreducibleCountingLemmas.Z.exists_annihilator_eq (toLin' M) (by rw [charpoly_toLin']; exact hs)
    (toLin' M).charpoly dvd_rfl
  refine ⟨e, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let q : K[X] := ∑ j : Fin n, monomial (j : ℕ) (c j)
  have ha : ∀ p : K[X], aeval (toLin' M) p = toLin' (aeval M p) := fun p =>
    aeval_algHom_apply (toLinAlgEquiv' (R := K) (n := Fin n)) M p
  have hq0 : aeval (toLin' M) q e = 0 := by
    rw [ha, toLin'_apply]
    have haq : aeval M q = ∑ j : Fin n, c j • M ^ (j : ℕ) := by
      simp [q, map_sum, aeval_monomial, Algebra.smul_def]
    rw [haq, Matrix.sum_mulVec]
    simpa [Matrix.smul_mulVec] using hc
  have hdvd := he q hq0
  rw [charpoly_toLin'] at hdvd
  have hdeg : q.degree < M.charpoly.degree := by
    rw [degree_eq_natDegree M.charpoly_monic.ne_zero, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j _ => ?_
    exact lt_of_le_of_lt (degree_monomial_le _ _) (by exact_mod_cast j.2)
  have hq : q = 0 := eq_zero_of_dvd_of_degree_lt hdvd hdeg
  intro j
  have := congrArg (fun p : K[X] => p.coeff j) hq
  simpa [q, finset_sum_coeff, coeff_monomial, Fin.val_inj] using this

end GlobalTheory.ConjLocal

namespace GlobalTheory.ConjLocal

variable {R : Type} [CommRing R] {n : ℕ}

theorem pow_dim_mulVec [Nontrivial R] (Y : Matrix (Fin n) (Fin n) R) (v : Fin n → R) (i : Fin n) :
    (Y ^ n *ᵥ v) i = -∑ k : Fin n, Y.charpoly.coeff k * (Y ^ (k : ℕ) *ᵥ v) i := by
  have h0 := Matrix.aeval_self_charpoly Y
  have hm := Y.charpoly_monic.as_sum
  rw [charpoly_natDegree_eq_dim, Fintype.card_fin] at hm
  rw [hm] at h0
  simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C] at h0
  have := congrArg (fun M => (M *ᵥ v) i) h0
  simp only [add_mulVec, sum_mulVec, Pi.add_apply, Finset.sum_apply, zero_mulVec, Pi.zero_apply] at this
  rw [eq_neg_iff_add_eq_zero, ← this, ← Fin.sum_univ_eq_sum_range]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mulVec_mulVec, algebraMap_eq_diagonal, mulVec_diagonal]
  rfl

theorem mul_iterMat [Nontrivial R] (Y : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    Y * iterMat Y v = iterMat Y v * compMat Y.charpoly := by
  ext i j
  have hl : (Y * iterMat Y v) i j = (Y ^ ((j : ℕ) + 1) *ᵥ v) i := by
    rw [pow_succ', ← mulVec_mulVec]; rfl
  rw [hl, Matrix.mul_apply]
  simp only [iterMat, compMat, Matrix.of_apply]
  split_ifs with hj
  · rw [Finset.sum_eq_single ⟨(j : ℕ) + 1, hj⟩]
    · simp
    · intro b _ hb
      rw [if_neg (fun h => hb (Fin.ext h)), mul_zero]
    · simp
  · have : (j : ℕ) + 1 = n := by omega
    rw [this, pow_dim_mulVec, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

theorem exists_isUnit_det_iterMat [IsLocalRing R] (Y : Matrix (Fin n) (Fin n) R) (hs : Y.charpoly.Separable) :
    ∃ v : Fin n → R, IsUnit (iterMat Y v).det := by
  let f := IsLocalRing.residue R
  have hs' : (Y.map f).charpoly.Separable := by rw [Matrix.charpoly_map]; exact hs.map
  obtain ⟨w, hw⟩ := exists_linearIndependent_iterates (Y.map f) hs'
  choose v hv using fun i => IsLocalRing.residue_surjective (w i)
  refine ⟨v, ?_⟩
  have hmap : (iterMat Y v).map f = iterMat (Y.map f) w := by
    ext i j
    simp only [iterMat, Matrix.map_apply, Matrix.of_apply, ← Matrix.map_pow, RingHom.map_mulVec]
    congr 1
    funext k
    exact hv k
  have hunit : IsUnit (iterMat (Y.map f) w) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    convert hw using 1
    funext j
    ext i
    rfl
  apply isUnit_of_map_unit f
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap]
  exact (Matrix.isUnit_iff_isUnit_det _).1 hunit

end GlobalTheory.ConjLocal
end

