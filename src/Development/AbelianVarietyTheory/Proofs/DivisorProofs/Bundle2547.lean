import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2439
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2440
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreConnected
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

noncomputable section

namespace GlobalTheory.SpecialConn

theorem range_spec_map_eq {O S : Type} [CommRing O] [IsLocalRing O] [CommRing S] [Nontrivial S] (φ : O →+* S)
    (hφ : ∀ Q : Ideal S, Q.IsPrime → IsLocalRing.maximalIdeal O ≤ Q.comap φ) :
    Set.range (Spec.map (CommRingCat.ofHom φ)) = {IsLocalRing.closedPoint O} := by
  have key : ∀ Q : PrimeSpectrum S, Spec.map (CommRingCat.ofHom φ) Q = IsLocalRing.closedPoint O := by
    intro Q
    refine PrimeSpectrum.ext ?_
    change Q.asIdeal.comap φ = IsLocalRing.maximalIdeal O
    exact le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.comap φ).ne_top) (hφ _ Q.2)
  ext x
  constructor
  · rintro ⟨Q, rfl⟩
    exact key Q
  · rintro rfl
    obtain ⟨M, hM⟩ := Ideal.exists_maximal S
    exact ⟨⟨M, hM.isPrime⟩, key _⟩

theorem range_thickQ (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    Set.range (Spec.map (CommRingCat.ofHom (thickQ O n))) = {IsLocalRing.closedPoint O} := by
  haveI : Nontrivial (O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal O).ne_top
      (Ideal.pow_le_self (Nat.succ_ne_zero n)))
  refine range_spec_map_eq _ fun Q hQ => ?_
  have h : IsLocalRing.maximalIdeal O ^ (n + 1) ≤ Q.comap (thickQ O n) := fun a ha => by
    change Ideal.Quotient.mk _ a ∈ Q
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]
    exact Q.zero_mem
  exact (Ideal.IsPrime.comap (thickQ O n)).le_of_pow_le h

theorem range_residue (O : Type) [CommRing O] [IsLocalRing O] :
    Set.range (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) = {IsLocalRing.closedPoint O} := by
  refine range_spec_map_eq _ fun Q hQ a ha => ?_
  change IsLocalRing.residue O a ∈ Q
  rw [(IsLocalRing.residue_eq_zero_iff a).2 ha]
  exact Q.zero_mem

theorem connectedSpace_specialFibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)), IsIntegral Y → (∀ z : Y, IsIntegrallyClosed (Y.presheaf.stalk z)) → IsProper f → Flat f → ConnectedSpace (specialFibre f) := by
  intro O _ _ _ _ Y f hY _ hP hF
  have hT : Set.range (specialι f) = f ⁻¹' {IsLocalRing.closedPoint O} := by
    have h := Scheme.Pullback.range_fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))
    rw [range_residue] at h
    exact h
  have hTn : ∀ n, Set.range (thickι f n) = f ⁻¹' {IsLocalRing.closedPoint O} := fun n => by
    have h := Scheme.Pullback.range_fst f (Spec.map (CommRingCat.ofHom (thickQ O n)))
    rw [range_thickQ] at h
    exact h
  have hne : ∃ y : Y, f y = IsLocalRing.closedPoint O := by
    obtain ⟨y⟩ := (inferInstance : Nonempty Y)
    let η : Spec (.of O) := ⟨⊥, Ideal.bot_prime⟩
    have hgen : η ⤳ f y := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    obtain ⟨y', -, hy'⟩ := (Flat.generalizingMap f) hgen
    have hc : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
    have hsp : η ⤳ IsLocalRing.closedPoint O :=
      (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    exact hsp.mem_closed hc ⟨y', hy'⟩
  obtain ⟨y₀, hy₀⟩ := hne
  have hy₀' : y₀ ∈ Set.range (specialι f) := by rw [hT]; exact hy₀
  obtain ⟨z₀, -⟩ := hy₀'
  haveI : Nonempty (specialFibre f) := ⟨z₀⟩
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  haveI : IsClosedImmersion (specialι f) :=
    inferInstanceAs (IsClosedImmersion (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))))
  have hcl : Topology.IsClosedEmbedding (specialι f) := (specialι f).isClosedEmbedding
  refine { toPreconnectedSpace := preconnectedSpace_iff_clopen.2 fun U hU => ?_, toNonempty := ‹_› }
  by_contra hcon
  push_neg at hcon
  obtain ⟨hU0, hU1⟩ := hcon
  obtain ⟨u, hu⟩ := hU0
  obtain ⟨u', hu'⟩ : ∃ u', u' ∉ U := by
    by_contra h
    push_neg at h
    exact hU1 (Set.eq_univ_of_forall h)
  let A := specialι f '' U
  let B := specialι f '' Uᶜ
  have hA : IsClosed A := hcl.isClosedMap _ hU.1
  have hB : IsClosed B := hcl.isClosedMap _ hU.2.isClosed_compl
  have hpt : ∀ n (z : specialFibre f), ∃ x, thickι f n x = specialι f z := fun n z => by
    have : specialι f z ∈ Set.range (thickι f n) := by rw [hTn, ← hT]; exact ⟨z, rfl⟩
    exact this
  have hAB : ∀ n, (thickι f n ⁻¹' A)ᶜ = thickι f n ⁻¹' B := by
    intro n
    ext x
    obtain ⟨z, hz⟩ : thickι f n x ∈ Set.range (specialι f) := by rw [hT, ← hTn n]; exact ⟨x, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_preimage, A, B, Set.mem_image]
    constructor
    · intro h
      exact ⟨z, fun hzU => h ⟨z, hzU, hz⟩, hz⟩
    · rintro ⟨w, hw, hw'⟩ ⟨w', hw'U, hw''⟩
      exact hw (hcl.injective (hw''.trans hw'.symm) ▸ hw'U)
  have hclo : ∀ n, IsClopen (thickι f n ⁻¹' A) := fun n =>
    ⟨hA.preimage (thickι f n).continuous,
      by rw [← isClosed_compl_iff, hAB n]; exact hB.preimage (thickι f n).continuous⟩
  choose e he hbe using fun n => GlobalTheory.T.exists_idempotent_of_clopen _ _ (hclo n)
  have hcomp : ∀ n, (thickTr f n).appTop.hom (e (n + 1)) = e n := by
    intro n
    refine GlobalTheory.T.idempotent_eq_of_basicOpen_eq' _ _ _ (by rw [← map_mul, he]) (he n) ?_
    refine TopologicalSpace.Opens.ext ?_
    rw [← Scheme.Hom.preimage_basicOpen_top, hbe n]
    change thickTr f n ⁻¹' ((Scheme.basicOpen _ (e (n + 1)) : Set _)) = _
    rw [hbe (n + 1), ← Set.preimage_comp, ← thickTr_ι f n]
    rfl
  obtain ⟨s, hs⟩ := GlobalTheory.T.proper_flat_adic_sections_lift O Y f e hcomp
  have hss : s * s = s := by
    have := GlobalTheory.T.proper_flat_section_eq_zero_of_thickenings O Y f (s * s - s) fun n => by rw [map_sub, map_mul, hs, he, sub_self]
    exact sub_eq_zero.1 this
  have h01 : s = 0 ∨ s = 1 := IsIdempotentElem.iff_eq_zero_or_one.1 hss
  obtain ⟨x, hx⟩ := hpt 0 u
  obtain ⟨x', hx'⟩ := hpt 0 u'
  rcases h01 with h0 | h1
  · have e0 : e 0 = 0 := by rw [← hs 0, h0, map_zero]
    have hxA : x ∈ thickι f 0 ⁻¹' A := ⟨u, hu, hx.symm⟩
    rw [← hbe 0, e0, Scheme.basicOpen_zero] at hxA
    exact hxA
  · have e1 : e 0 = 1 := by rw [← hs 0, h1, map_one]
    have hxA : x' ∈ ((thickFib f 0).basicOpen (e 0) : Set _) := by
      rw [e1, Scheme.basicOpen_one]
      trivial
    rw [hbe 0] at hxA
    obtain ⟨w, hw, hw'⟩ := hxA
    exact hu' (hcl.injective (hw'.trans hx') ▸ hw)

end GlobalTheory.SpecialConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionOfBaseChangeAlongIdentity
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SqDecIdBC

theorem sqDec_of_baseChange_id : ∀ (F : Type) [CommRing F] (A : Over (Sp F)) [GrpObj A] (L M : LB A.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap (RingHom.id F))).obj A) (L.pull (pullback.fst A.hom (spMap (RingHom.id F)))) (M.pull (pullback.fst A.hom (spMap (RingHom.id F)))) → SqDec A L M := by
  intro F _ A _ L M hL hM hD
  have hid : spMap (RingHom.id F) = 𝟙 (Sp F) := by
    simp [spMap]
  have hw : 𝟙 A.left ≫ A.hom = A.hom ≫ spMap (RingHom.id F) := by rw [hid]; simp
  let π' : A.left ⟶ pullback A.hom (spMap (RingHom.id F)) := pullback.lift (𝟙 _) A.hom hw
  have e₁ : π' ≫ pullback.fst A.hom (spMap (RingHom.id F)) = 𝟙 _ := pullback.lift_fst _ _ _
  have e₂ : π' ≫ ((Over.pullback (spMap (RingHom.id F))).obj A).hom = A.hom ≫ 𝟙 _ := by
    rw [Category.comp_id]; exact pullback.lift_snd _ _ _
  have hP : IsGrpPullback A ((Over.pullback (spMap (RingHom.id F))).obj A) (𝟙 _) π' := by
    have n : IsGrpPullback A A (𝟙 _ ≫ spMap (RingHom.id F)) (π' ≫ pullback.fst A.hom (spMap (RingHom.id F))) := by
      rw [e₁, Category.id_comp, hid]; exact GlobalTheory.SiegLower.isGrpPullback_id A
    exact IsGrpPullback.cancel (isGrpPullback_pullback A _) n e₂
  obtain ⟨N, a₀, r, e, β, hN, ha₀, hβ, hI⟩ := hD
  have hβ' : ∀ i, ∃ g : A ⟶ A, IsMonHom g ∧ g.left ≫ π' = π' ≫ (β i).left := fun i => by
    haveI := hβ i
    exact GlobalTheory.HomDescent.exists_isMonHom_pull hP hP (β i)
  choose β' hβ'm hβ'c using hβ'
  have iL : LBIso L ((L.pull (pullback.fst A.hom (spMap (RingHom.id F)))).pull π') :=
    LBIso.trans hL (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (GlobalTheory.SiegLower.lbIso_pull_id hL)
      (GlobalTheory.ShapePull.iso_linComb_pull (GlobalTheory.SiegLower.lbIso_pull_id hL) _ _ _ π' (fun _ => by rw [e₁]; simp))
  have iM : LBIso M ((M.pull (pullback.fst A.hom (spMap (RingHom.id F)))).pull π') :=
    LBIso.trans hM (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (GlobalTheory.SiegLower.lbIso_pull_id hM)
      (GlobalTheory.ShapePull.iso_linComb_pull (GlobalTheory.SiegLower.lbIso_pull_id hM) _ _ _ π' (fun _ => by rw [e₁]; simp))
  refine ⟨N, a₀, r, e, β', hN, ha₀, hβ'm, ?_⟩
  have j₁ : LBIso (lbPow L N) ((lbPow (L.pull (pullback.fst A.hom (spMap (RingHom.id F)))) N).pull π') :=
    GlobalTheory.ShapePull.iso_linComb_pull iL _ _ _ π' (fun _ => by simp)
  have j₂ := GlobalTheory.RigidBundleGlue.LBIso.pull hI π'
  have j₃ : LBIso (LB.LinComb M (K := Option (Fin r))
        (fun o => o.elim (𝟙 _) fun i => (β' i).left) fun o => o.elim (a₀ : ℤ) fun i => (e i : ℤ))
      ((LB.LinComb (M.pull (pullback.fst A.hom (spMap (RingHom.id F)))) (K := Option (Fin r))
        (fun o => o.elim (𝟙 _) fun i => (β i).left) fun o => o.elim (a₀ : ℤ) fun i => (e i : ℤ)).pull π') :=
    GlobalTheory.ShapePull.iso_linComb_pull iM _ _ _ π' (fun o => by
      cases o with
      | none => simp
      | some i => exact hβ'c i)
  exact LBIso.trans (isLB_lbPow hL N) (pull_isLB (isLB_lbPow (pull_isLB hL _) N) _)
    (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hM _ _) j₁
    (LBIso.trans (pull_isLB (isLB_lbPow (pull_isLB hL _) N) _)
      (pull_isLB (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hM _) _ _) _)
      (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hM _ _) j₂ (LBIso.symm j₃))

end GlobalTheory.SqDecIdBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkNormalFlatOfSmoothOverRegularLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalk_normal_flat_of_smooth_over_regular_local : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (X : Scheme.{0}) (p : X ⟶ Sp R), Smooth p → ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsNoetherianRing (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) ∧ (Spec.preimage (X.fromSpecStalk x ≫ p)).hom.Flat ∧ Function.Injective (Spec.preimage (X.fromSpecStalk x ≫ p)).hom := by
  first | exact @GlobalTheory.SmoothStalkNormal.stalk_of_smooth_over_regular | exact GlobalTheory.SmoothStalkNormal.stalk_of_smooth_over_regular | (intros; apply GlobalTheory.SmoothStalkNormal.stalk_of_smooth_over_regular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardSmoothLiftOverSqZeroThickeningStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardSmooth_lift_over_sqZero_thickening : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀], Algebra.IsStandardSmooth R₀ B₀ → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  first | exact @GlobalTheory.Obs.standardSmooth_lift_of_sqZero | exact GlobalTheory.Obs.standardSmooth_lift_of_sqZero | (intros; apply GlobalTheory.Obs.standardSmooth_lift_of_sqZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafPullbackRelationsBasicStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.structureSheaf_pullback_relations_basic : ∀ (R : Type) [CommRing R] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R) (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap (RingHom.id R)), Function.Bijective (pairRes φ s').pull2 ∧ (∀ a b a' b', IsPullO h a a' → IsPullO h b b' → IsPullbackH2Structure h (GlobalTheory.CatCoh.cup _ a b) (GlobalTheory.CatCoh.cup _ a' b')) ∧ ∀ (X'' : Scheme.{0}) (s'' : X'' ⟶ Sp R) (ψ : X'' ⟶ X') (h' : ψ ≫ s' = s'' ≫ spMap (RingHom.id R)) (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (RingHom.id R)) a a' a'', IsPullO h a a' → IsPullO h' a' a'' → IsPullO h'' a a'' := by
  first | exact @GlobalTheory.Obs.pullO_basic | exact GlobalTheory.Obs.pullO_basic | (intros; apply GlobalTheory.Obs.pullO_basic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTmulEqZeroOfFlatLinearlyDisjointSubringStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_tmul_eq_zero_of_flat_linearlyDisjoint_subring : ∀ (R R₁ A F K : Type) [CommRing R] [CommRing R₁] [CommRing A] [Field F] [Field K] [Algebra R A] [Algebra R R₁], Module.Flat R R₁ → ∀ (c₀ : R →+* F) (e : A →+* F) (c : R₁ →+* K) (θ : F →+* K), Function.Injective c₀ → Function.Injective e → e.comp (algebraMap R A) = c₀ → θ.comp c₀ = c.comp (algebraMap R R₁) → LinDisj c₀ c θ → ∀ (n : ℕ) (a : Fin n → A) (r : Fin n → R₁), ∑ i, θ (e (a i)) * c (r i) = 0 → ∑ i, a i ⊗ₜ[R] r i = 0 := by
  first | exact @GlobalTheory.Desc.tmul_sum_eq_zero_of_flat_linDisj | exact GlobalTheory.Desc.tmul_sum_eq_zero_of_flat_linDisj | (intros; apply GlobalTheory.Desc.tmul_sum_eq_zero_of_flat_linDisj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTwoPointFunctionMultiplesNaturalCharP
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem chi_natural : ∀ (p : ℕ) (R : Type) [CommRing R], (p : R) = 0 → ∀ (A : Over (Sp R)) [GrpObj A] (f : Fn1 A) (g : Fn2 A), IsAdd f g → ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D), chi p g D' (spOver φ ≫ x) - φ (chi p g D x) = f D D' φ (x ^ p) - f D D' φ 1 := by
  intro p R _ hp A _ f g hg D _ _ D' _ _ φ x
  have hp' : (p : D') = 0 := by
    rw [← map_natCast (algebraMap R D') p, hp, map_zero]
  unfold chi
  rw [map_sum, ← Finset.sum_sub_distrib]
  have h : ∀ i ∈ Finset.range p, g D' ((spOver φ ≫ x) ^ i) (spOver φ ≫ x) - φ (g D (x ^ i) x) =
      (f D D' φ (x ^ (i + 1)) - f D D' φ (x ^ i)) - f D D' φ x := by
    intro i _
    rw [← MonObj.comp_pow, hg D D' φ (x ^ i) x, pow_succ]
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_range_sub (fun i ↦ f D D' φ (x ^ i)) p,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, hp', zero_mul, sub_zero, pow_zero]

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummandDualAnnihilatorReductionProjectiveStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summand_dualAnnihilator_reduction_projective : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → ∀ (C C₀ : Type 1) [AddCommGroup C] [Module R C] [AddCommGroup C₀] [Module R₀ C₀], Module.Finite R C → Module.Projective R C → ∀ ρ : C →ₛₗ[π] C₀, Function.Surjective ρ → (∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R C)) → ∀ F₀ : Submodule R₀ C₀, (∃ N₀, IsCompl F₀ N₀) → (∀ K : Submodule R C, (∃ N, IsCompl K N) → (∃ N, IsCompl K.dualAnnihilator N) ∧ K.dualAnnihilator.dualCoannihilator = K ∧ ((∀ c, c ∈ K ⊔ RingHom.ker π • ⊤ ↔ ρ c ∈ F₀) ↔ ∀ y : Module.Dual R₀ C₀, y ∈ F₀.dualAnnihilator ↔ ∃ x ∈ K.dualAnnihilator, ∀ c, y (ρ c) = π (x c))) ∧ ∀ G : Submodule R (Module.Dual R C), (∃ N, IsCompl G N) → ∃ K : Submodule R C, (∃ N, IsCompl K N) ∧ G = K.dualAnnihilator := by
  first | exact @GlobalTheory.LiftSys.summand_dual_reduction | exact GlobalTheory.LiftSys.summand_dual_reduction | (intros; apply GlobalTheory.LiftSys.summand_dual_reduction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupLatticeReferenceExponentThetaWeightLevelLeOneStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supLatticeReferenceExponent_thetaWeight_level_le_one : ∀ (D : D7) (T : Core D), LawsM T → ∀ (_ : ErrX D) (j : ℕ), InR D j → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (cst : ℝ), Dom a n → LastPos (T.Q.Dw j) a → ∑ f : Lt1 (T.Q.Dw j), 2 * rk f ≤ n → 2 * D.R.r ≤ n → JetNum D (DF (T.Q.Dw j) a) cst → ∀ k : Fin 2, refExp_vp (T.U j) cst (wtZ a n) (D.host.g k) ≤ ((1 : ℝ) : EReal) := by
  first | exact @GlobalTheory.RefLevel.refExp_level_le_one | exact GlobalTheory.RefLevel.refExp_level_le_one | (intros; apply GlobalTheory.RefLevel.refExp_level_le_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfSurjectiveOnPoints
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ComplexAbVarSurj

theorem surjective_of_surjective_points : ∀ (A X : Over (Sp ℂ)) [GrpObj A] [GrpObj X] (ψ : A ⟶ X), IsAbelianScheme A → IsAbelianScheme X →
    (∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ X, ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ ψ = y) → Surjective ψ.left := by
  intro A X _ _ ψ hA hX h
  have hAp : IsProper A.hom := hA.proper
  have hXp : IsProper X.hom := hX.proper
  have : UniversallyClosed (ψ.left ≫ X.hom) := by rw [Over.w]; infer_instance
  have : UniversallyClosed ψ.left := UniversallyClosed.of_comp_of_isSeparated ψ.left X.hom
  have hcl : IsClosed (Set.range ψ.left) := ψ.left.isClosedMap.isClosed_range
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  let pt : Spec (CommRingCat.of ℂ) := IsLocalRing.closedPoint ℂ
  have hsub : closedPoints X.left ⊆ Set.range ψ.left := by
    intro z hz
    obtain ⟨x, hx⟩ := h (Over.homMk (pointOfClosedPoint (K := ℂ) X.hom z hz)
      (pointOfClosedPoint_comp (K := ℂ) X.hom z hz))
    refine ⟨x.left pt, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hx]
    exact pointOfClosedPoint_apply (K := ℂ) X.hom z hz pt
  have hall : Set.range ψ.left = Set.univ := by
    have := closure_mono hsub
    rw [closure_closedPoints, hcl.closure_eq] at this
    exact Set.eq_univ_of_univ_subset this
  exact ⟨Set.range_eq_univ.mp hall⟩

end GlobalTheory.ComplexAbVarSurj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveSpMapOfSq
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem surjective_spMap_of_sq {A B : Type} [CommRing A] [CommRing B] (π : A →+* B) (hπ : Function.Surjective π)
    (hsq : ∀ a ∈ RingHom.ker π, a * a = 0) : Function.Surjective (spMap π) := fun x ↦ by
  have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker π : Set A) := fun a ha ↦
    (x.isPrime.mem_or_mem ((hsq a ha).symm ▸ x.asIdeal.zero_mem)).elim id id
  rw [← range_comap_of_surjective B π hπ] at hx
  exact hx

theorem pt_dual_le_of_fst : ∀ (R : Type) [CommRing R] (H : Over (Sp R)) (D : Type) [CommRing D] [Algebra R D]
      (Z : Pt H (DualNumber D)) (U : H.left.Opens),
      ⊤ ≤ (spOver (TrivSqZeroExt.fstHom R D D) ≫ Z).left ⁻¹ᵁ U → ⊤ ≤ Z.left ⁻¹ᵁ U := by
  intro R _ H D _ _ Z U h x _
  have hs : Function.Surjective (spMap ((TrivSqZeroExt.fstHom R D D : DualNumber D →ₐ[R] D) : DualNumber D →+* D)) :=
    surjective_spMap_of_sq _ (fun d ↦ ⟨TrivSqZeroExt.inl d, rfl⟩) fun a ha ↦ by
      have h0 : a.fst = 0 := ha
      ext <;> simp [h0]
  obtain ⟨y, rfl⟩ := hs x
  have hy := h (show y ∈ (⊤ : (Sp D).Opens) from trivial)
  simpa [Over.comp_left, PDiv.spOver_left] using hy

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLineBundlePullbackBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_lineBundle_pullback_baseChange : ∀ (S T : Scheme.{0}) (G : Over S) [GrpObj G] (j : T ⟶ S) (L : LB G.left), L.IsLB → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L → LBIso ((L.pull (pullback.fst G.hom j)).pull (GrpObj.inv : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G).left) (L.pull (pullback.fst G.hom j)) := by
  first | exact @GlobalTheory.SymBaseChange.symm_pull | exact GlobalTheory.SymBaseChange.symm_pull | (intros; apply GlobalTheory.SymBaseChange.symm_pull <;> assumption)
end

