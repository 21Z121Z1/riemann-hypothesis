import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2933
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2958
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0198
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0098
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3022
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2865
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0058
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2984
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumOnGoodPlaces
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2948
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2960
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2901
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2559
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsPrimitiveAtUniformisedTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.PrimTrait

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := by
  simp [spMap]

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left}

theorem heq_pullS {R : Type} [CommRing R] {x₁ x₂ : Sp R ⟶ S} (h : x₁ = x₂) {T : Over S}
    (f₁ : Over.mk x₁ ⟶ T) (f₂ : Over.mk x₂ ⟶ T) (hf : f₁.left = f₂.left)
    (s : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) :
    HEq (VVRank.pullS G _ f₁ s) (VVRank.pullS G _ f₂ s) := by
  subst h
  obtain rfl : f₁ = f₂ := Over.OverMorphism.ext hf
  rfl

theorem thList_of_eq (ρ : LB.Gen (L.pull (eSec G))) (m : ℕ) {K : Type} [Field K] {x₁ x₂ : Sp K ⟶ S}
    (h : x₁ = x₂) {θ₁ : SecAt G L x₁} {θ₂ : SecAt G L x₂} (hθ : HEq θ₁ θ₂) {N : ℕ}
    {pt : Fin N → (Over.mk x₁ ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m x₁ θ₁ pt c) :
    ∃ pt₂ : Fin N → (Over.mk x₂ ⟶ G), (∀ a, (pt₂ a).left = (pt a).left) ∧ ThList G L ρ m x₂ θ₂ pt₂ c := by
  subst h
  cases hθ
  exact ⟨pt, fun _ => rfl, H⟩

theorem pt_of_eq {R : Type} [CommRing R] {x₁ x₂ : Sp R ⟶ S} (h : x₁ = x₂) (p : Over.mk x₁ ⟶ G) :
    ∃ p₂ : Over.mk x₂ ⟶ G, p₂.left = p.left ∧ ∀ n : ℕ, p ^ n = 1 → p₂ ^ n = 1 := by
  subst h
  exact ⟨p, rfl, fun _ h => h⟩

theorem thG_unique [IsCommMonObj G] (ρ : LB.Gen (L.pull (eSec G))) (hL : L.IsLB) (hρ : ρ.IsGen) {g m : ℕ}
    {K : Type} [Field K] {x : Sp K ⟶ S} (θ : SecAt G L x) (p : Over.mk x ⟶ G) {c c' : K} (hm : Odd m)
    (hm0 : (m : K) ≠ 0) (hP : PolFib G L g x) (h₁ : ThG G L ρ m θ p (GlobalTheory.ZH.fn c))
    (h₂ : ThG G L ρ m θ p (GlobalTheory.ZH.fn c')) : c' = c := by
  have := (GlobalTheory.T.thetaConstant_unique_and_linear_in_section S G L ρ hL hρ g m K x θ θ p 1 c c' hm hm0 hP (by simp) h₁).1 h₂
  simpa using this
end

theorem isIntegralElem_of_sq {V F K Kb : Type} [CommRing V] [Field F] [Field K] [Field Kb] (φ : V →+* F) (i : V →+* K)
    (i' : K →+* Kb) (j : F →+* Kb) (hsq : i'.comp i = j.comp φ) {z : F} {w : K} (h : j z = i' w)
    (hz : φ.IsIntegralElem z) : i.IsIntegralElem w := by
  obtain ⟨p, hp, hp0⟩ := hz
  refine ⟨p, hp, i'.injective ?_⟩
  rw [Polynomial.hom_eval₂, ← h, hsq, ← Polynomial.hom_eval₂, hp0, map_zero, map_zero]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (t' : SAB H (Sp V)), Nonempty (SABMap t' t χ) → Nonempty (PELUnif (IsLocalRing.maximalIdeal V) t') → ∀ (σ : SecAt t.G t.PP.L χ), NZ t.G t.PP.L χ σ → ∀ (m N : ℕ), Odd m → 3 ≤ m → IsUnit (m : V) → ∀ (K : Type) [Field K] (i : V →+* K) (pt : Fin N → (Over.mk (spMap i ≫ χ) ⟶ t.G)) (c : Fin N → K), Function.Injective i → ThList t.G t.PP.L t.PP.rig m (spMap i ≫ χ) (SecAt.pull t.G t.PP.L σ i) pt c → Prim i c := by
  intro E _ _ _ H S t V _ _ _ hV χ t' ⟨hm⟩ ⟨P⟩ σ hσ m N hodd h3 hmu K _ i pt c hi hL
  haveI : IsDiscreteValuationRing V := hV.1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let F := AlgebraicClosure (FractionRing V)
  obtain ⟨v, hv⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_valOver hϖ F
  obtain ⟨g, hg⟩ := GlobalTheory.T.principallyPolarised_genericFibre_uniformised_trait E H S t V hV χ t' ⟨hm⟩ ⟨P⟩
  set x' : Sp F ⟶ S := (jFK (R := V) F ≫ jK V) ≫ χ with hx'
  set θF : SecAt t.G t.PP.L x' :=
    VVRank.pullS t.G _ (Over.homMk (jFK (R := V) F ≫ jK V) rfl : Over.mk x' ⟶ Over.mk χ) σ with hθF
  obtain ⟨hA, x0, c0, hx0, hv0⟩ := (GlobalTheory.Ex.OneGen.theta_at_trait GlobalTheory.lawsAndExpansions E H S t V hV χ t' hm P σ
    hσ).2 ϖ hϖ F v hv m hodd hmu h3 x' (Over.homMk (jFK (R := V) F ≫ jK V) rfl) rfl
  let φF : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
  have hPF : PolFib t.G t.PP.L g x' := by
    have := hg F (algebraMap (FractionRing V) F)
    simpa only [hx', Category.assoc] using this
  have hmF : (m : F) ≠ 0 := by
    have := hmu.map φF
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨ptF, cF, hLF⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen g m (m ^ (4 * g)) F x' θF hodd
    hmF rfl hPF
  let Kb := AlgebraicClosure K
  let i' : K →+* Kb := algebraMap K Kb
  have hii : Function.Injective (i'.comp i) := i'.injective.comp hi
  let e : FractionRing V →+* Kb := IsFractionRing.lift hii
  letI : Algebra (FractionRing V) Kb := e.toAlgebra
  let j : F →+* Kb := (IsAlgClosed.lift : F →ₐ[FractionRing V] Kb).toRingHom
  have hsq : i'.comp i = j.comp φF := by
    ext r
    change _ = (IsAlgClosed.lift : F →ₐ[FractionRing V] Kb) (algebraMap (FractionRing V) F _)
    rw [AlgHom.commutes]
    exact (IsFractionRing.lift_algebraMap hii r).symm
  have hy : spMap i' ≫ spMap i ≫ χ = spMap j ≫ x' := by
    change _ = spMap j ≫ (spMap (algebraMap (FractionRing V) F) ≫ spMap (algebraMap V (FractionRing V))) ≫ χ
    rw [← Category.assoc, spMap_comp', spMap_comp', ← Category.assoc, spMap_comp', hsq]

  have hPy : PolFib t.G t.PP.L g (spMap j ≫ x') := by
    have := hg Kb (j.comp (algebraMap (FractionRing V) F))
    rw [← spMap_comp'] at this
    simpa only [hx', Category.assoc] using this
  have hmKb : (m : Kb) ≠ 0 := by
    have := hmu.map (i'.comp i)
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨pt1, hpt1, hL1⟩ := GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen m N K Kb i' (spMap i ≫ χ)
    (SecAt.pull t.G t.PP.L σ i) pt c hL
  have hθ : HEq (SecAt.pull t.G t.PP.L (SecAt.pull t.G t.PP.L σ i) i') (SecAt.pull t.G t.PP.L θF j) := by
    simp only [SecAt.pull, hθF, GlobalTheory.ThetaRuleCompare.pullS_comp]
    refine heq_pullS hy _ _ ?_ σ
    simp only [Over.comp_left, Over.homMk_left]
    change spMap i' ≫ spMap i = spMap j ≫ (spMap (algebraMap (FractionRing V) F) ≫ spMap (algebraMap V (FractionRing V)))
    rw [spMap_comp', spMap_comp', spMap_comp', hsq]
  obtain ⟨ptK, hptK, hLK⟩ := thList_of_eq t.PP.rig m hy hθ hL1
  obtain ⟨ptF', hptF', hLF'⟩ := GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen m (m ^ (4 * g)) F Kb j x' θF
    ptF cF hLF
  have hint : ∀ b, φF.IsIntegralElem (cF b) := fun b =>
    GlobalTheory.T.isIntegralElem_of_val_nonneg_over_completeDVR V hV ϖ hϖ F v hv (cF b) (hA (ptF b) (cF b) (hLF.2.1 b))
  refine ⟨fun a => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hLF.2.2 Kb j (ptK a) (hLK.2.1 a).1
    have heq : ptK a = ptF' b := Over.OverMorphism.ext (hb.trans (hptF' b).symm)
    have h1 := hLK.2.1 a
    rw [heq] at h1
    have hab : j (cF b) = i' (c a) :=
      thG_unique t.PP.rig t.PP.isLB t.PP.rigGen _ (ptF' b) hodd hmKb hPy h1 (hLF'.2.1 b)
    exact isIntegralElem_of_sq φF i i' j hsq hab (hint b)
  · obtain ⟨x0', hx0'l, hx0't⟩ := pt_of_eq (show x' = spMap (RingHom.id F) ≫ x' by rw [spMap_id', Category.id_comp]) x0
    obtain ⟨b0, hb0⟩ := hLF.2.2 F (RingHom.id F) x0' (hx0't _ hx0.1)
    have hx0b : x0 = ptF b0 := Over.OverMorphism.ext (by rw [← hx0'l, hb0, spMap_id', Category.id_comp])
    subst hx0b
    have hc0b : cF b0 = c0 :=
      thG_unique t.PP.rig t.PP.isLB t.PP.rigGen θF (ptF b0) hodd hmF hPF hx0 (hLF.2.1 b0)
    obtain ⟨q, hql, hqt⟩ := pt_of_eq hy.symm (ptF' b0)
    obtain ⟨a0, ha0⟩ := hL.2.2 Kb i' q (hqt _ (hLF'.2.1 b0).1)
    have heq : ptK a0 = ptF' b0 := Over.OverMorphism.ext (by rw [hptK, hpt1, ← ha0, hql])
    have h1 := hLK.2.1 a0
    rw [heq] at h1
    have hab : j c0 = i' (c a0) := by
      rw [← hc0b]
      exact thG_unique t.PP.rig t.PP.isLB t.PP.rigGen _ (ptF' b0) hodd hmKb hPy h1 (hLF'.2.1 b0)
    have hc0 : c0 ≠ 0 := by
      rintro rfl
      simp at hv0
    have hca : c a0 ≠ 0 := by
      intro h
      rw [h, map_zero] at hab
      exact hc0 (j.injective (hab.trans (map_zero j).symm))
    refine ⟨a0, hca, isIntegralElem_of_sq φF i i' j hsq (z := c0⁻¹) (by rw [map_inv₀, map_inv₀, hab]) ?_⟩
    refine GlobalTheory.T.isIntegralElem_of_val_nonneg_over_completeDVR V hV ϖ hϖ F v hv _ ?_
    have h01 : v c0 + v c0⁻¹ = 0 := by
      rw [← AddValuation.map_mul, mul_inv_cancel₀ hc0, AddValuation.map_one]
    rw [hv0, zero_add] at h01
    rw [h01]

end GlobalTheory.UMin.PrimTrait
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralLinearCombination
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.CMTorsion.AlgMap

theorem exists_totPos (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) : ∃ c : 𝔠.elt, IsTotPos (c : F) := by
  have h0 : (𝔠 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := 𝔠.ne_zero
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := ((𝔠 : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F)) (by
    intro h; exact h0 (FractionalIdeal.coeToSubmodule_injective (by simpa using h)))
  obtain ⟨a, ha, hint⟩ := (𝔠 : FractionalIdeal (𝓞 F)⁰ F).isFractional
  obtain ⟨y, hy⟩ := hint x hx
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero, Algebra.smul_def] at hy
    exact mul_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 ha0) hx0 hy.symm
  have hm := Ideal.absNorm_mem (Ideal.span {y})
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hm
  set m := Ideal.absNorm (Ideal.span {y})
  have hm0 : m ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hy0
  have hmem : (m : F) ∈ 𝔠.elt := by
    have e : (m : F) = t • (a • x) := by
      rw [← hy, Algebra.smul_def, ← map_mul, ht, map_natCast]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hx)
  refine ⟨⟨_, hmem⟩, fun τ => ?_⟩
  simp only [map_natCast]
  exact_mod_cast Nat.pos_of_ne_zero hm0

end GlobalTheory.CMTorsion.AlgMap

namespace GlobalTheory.CMTorsion.AlgMap

theorem valAt'_comp {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (x ≫ φ) U f = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  unfold valAt'
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U)
  · rw [dif_pos h, dif_pos (show ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U from h)]
    unfold valAt
    congr 1
  · rw [dif_neg h, dif_neg (show ¬ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U from h)]

theorem factor : ∀ (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ (Y : Scheme.{0}) (N : ℕ) (i : Y ⟶ PSpace ℂ N),
    IsClosedImmersion i → ∀ (ψ : scheme (curve Λ Ω) ⟶ PSpace ℂ N) (φ : ℂ → (Sp ℂ ⟶ Y)),
    (∀ z, pt Λ Ω z ≫ ψ = φ z ≫ i) → ∃ f : scheme (curve Λ Ω) ⟶ Y, f ≫ i = ψ := by
  intro Λ Ω hΩ Y N i hi ψ φ h
  refine GlobalTheory.AbelianSubgroupFinite.exists_lift_of_range_subset ψ i ?_
  have hc : IsClosed (ψ ⁻¹' Set.range i) := i.isClosedEmbedding.isClosed_range.preimage ψ.continuous
  have hJ : JacobsonSpace (scheme (curve Λ Ω)) := LocallyOfFiniteType.jacobsonSpace (toSpec (curve Λ Ω))
  have hcp : closedPoints (scheme (curve Λ Ω)) ⊆ ψ ⁻¹' Set.range i := by
    intro y hy
    have hy₁ : IsClosed {y} := hy
    obtain ⟨z, hz⟩ := GlobalTheory.T.elliptic_section_from_uniformization Λ Ω hΩ (pointOfClosedPoint (toSpec (curve Λ Ω)) y hy₁)
      (pointOfClosedPoint_comp _ _ _)
    obtain ⟨a⟩ : Nonempty (Sp ℂ) := inferInstance
    have hy' : pt Λ Ω z a = y := by rw [hz, pointOfClosedPoint_apply]
    refine ⟨φ z a, ?_⟩
    rw [← hy']
    simpa [Scheme.Hom.comp_apply] using (congrArg (fun g : Sp ℂ ⟶ PSpace ℂ N => g a) (h z)).symm
  have hu : closure (closedPoints (scheme (curve Λ Ω))) = Set.univ := by
    have := JacobsonSpace.closure_inter_closedPoints_eq_closure (X := scheme (curve Λ Ω)) (S := Set.univ) isOpen_univ.isLocallyClosed
    rwa [Set.univ_inter, closure_univ] at this
  rintro _ ⟨y, rfl⟩
  have : y ∈ closure (closedPoints (scheme (curve Λ Ω))) := hu ▸ Set.mem_univ y
  exact (closure_minimal hcp hc) this

theorem main : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt) (n : ℕ) (u : HolUnif X.A (X.diag c) n) (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ β : Fin n → ℂ, (∀ l ∈ Λ.lattice, l • β ∈ u.Λ) → ∃ f : scheme (curve Λ Ω) ⟶ X.A.left, f ≫ X.A.hom = toSpec (curve Λ Ω) ∧ ∀ z, pt Λ Ω z ≫ f = (u.ex (z • β)).left := by
  intro F _ _ 𝔠 X c n u Λ Ω hΩ β hβ
  obtain ⟨c', hc'⟩ := exists_totPos F 𝔠
  obtain ⟨N, i, hi, hstr⟩ := GlobalTheory.RealMult.ProjOverC.isProjOver_A F 𝔠 X c' hc'
  let φ : ℂ → (Sp ℂ ⟶ X.A.left) := fun z => (u.ex (z • β)).left
  have hcomp : ∀ z, (φ z ≫ i) ≫ PSpace.str ℂ N = 𝟙 _ := fun z => by
    rw [Category.assoc, hstr]
    exact Over.w (u.ex (z • β))
  have hper : ∀ z, ∀ l ∈ Λ.lattice, φ (z + l) ≫ i = φ z ≫ i := fun z l hl => by
    have e : u.ex ((z + l) • β) = u.ex (z • β) := by
      rw [add_smul, u.ex_add, (u.ker _).2 (hβ l hl), _root_.mul_one]
    simp only [φ, e]
  have hhol : ∀ (U : (PSpace ℂ N).Opens) (s : Γ(PSpace ℂ N, U)), IsOpen {z | ⊤ ≤ (φ z ≫ i) ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (φ z ≫ i) U s) {z | ⊤ ≤ (φ z ≫ i) ⁻¹ᵁ U} := fun U s => by
    obtain ⟨h1, h2⟩ := u.hol (i ⁻¹ᵁ U) ((i.app U).hom s)
    have hL : Differentiable ℂ (fun z : ℂ => z • β) := differentiable_id.smul_const β
    have hset : {z : ℂ | ⊤ ≤ (φ z ≫ i) ⁻¹ᵁ U} = (fun z : ℂ => z • β) ⁻¹' {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ (i ⁻¹ᵁ U)} := rfl
    rw [hset]
    refine ⟨h1.preimage hL.continuous, ?_⟩
    have e : (fun z => valAt' (φ z ≫ i) U s) = (fun w => valAt' (u.ex w).left (i ⁻¹ᵁ U) ((i.app U).hom s)) ∘ (fun z : ℂ => z • β) :=
      funext fun z => valAt'_comp _ _ _ _
    rw [e]
    exact h2.comp hL.differentiableOn (fun z hz => hz)
  obtain ⟨ψ, hψ1, hψ2⟩ := GlobalTheory.T.holomorphic_map_to_projective_space Λ Ω hΩ N (fun z => φ z ≫ i) hcomp hper hhol
  obtain ⟨f, hf⟩ := factor Λ Ω hΩ X.A.left N i hi ψ φ hψ2
  refine ⟨f, ?_, fun z => ?_⟩
  · rw [← hstr, ← Category.assoc, hf, hψ1]
  · rw [← cancel_mono i, Category.assoc, hf, hψ2]

end GlobalTheory.CMTorsion.AlgMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferentStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_key_section_valuation_bounds_different : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (K : (Rul Xo c)ˣ), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) → (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) → ∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (K : Rul Xo c) ∧ v (K : Rul Xo c) ≤ ((4 * ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ) : ℝ) : EReal) := by
  first | exact @GlobalTheory.KeyIntegralVal.key_valuation_bounds | exact GlobalTheory.KeyIntegralVal.key_valuation_bounds | (intros; apply GlobalTheory.KeyIntegralVal.key_valuation_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMapFiniteGeometricFibresOfLargeLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.QF

theorem polFib_transport {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB) {K : Type}
    [Field K] {x : Sp K ⟶ S} {P P' : PolAV (Sp K)} (φ : P'.A ≅ P.A) (hφ : IsPolIso P' P φ)
    {α : P.A.left ⟶ G.left} (hα : IsGrpPullback P.A G x α) (hLα : LBIso P.L (L.pull α)) :
    IsGrpPullback P'.A G x (φ.hom.left ≫ α) ∧ LBIso P'.L (L.pull (φ.hom.left ≫ α)) := by
  have := hφ.1
  refine ⟨((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso φ).comp hα).congr (Category.id_comp _) rfl, ?_⟩
  obtain ⟨t, ht⟩ := hφ.2
  have h1 : LBIso P'.L (P.L.pull φ.hom.left) := LBIso.symm ⟨t, ht⟩
  have h2 : LBIso (P.L.pull φ.hom.left) (L.pull (φ.hom.left ≫ α)) :=
    LBIso.chartPull (chartPullPull P.L φ.hom.left)
      (chartPullSame L (fun _ : PUnit => φ.hom.left ≫ α) (fun _ => α) (fun _ => 1) φ.hom.left
        (fun _ => rfl)) hLα
  exact LBIso.trans P'.isLB (pull_isLB P.isLB _) (pull_isLB hL _) h1 h2

theorem charZero_of_pt {F K : Type} [Field F] [CharZero F] [Field K] (t : Sp K ⟶ Sp F) : CharZero K := by
  have f := (Spec.preimage t).hom
  exact (f.charZero_iff f.injective).1 inferInstance

end GlobalTheory.UMin.QF

namespace GlobalTheory.UMin.QF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

def ThetaData (Xo : Moduli Dw l) {K : Type} [Field K] (y : Sp K ⟶ Xo.X) (g m : ℕ) (ze : Γ(Sp K, ⊤)ˣ)
    (v : (Fin (2 * g) → ZMod (m ^ 2)) → Γ((baseOver (Sp K)).left, ⊤)) : Prop :=
  ∃ (P : PolAV (Sp K)) (hg : P.g = g) (α : P.A.left ⟶ Xo.univ.t.G.left) (lev : Out.Level P (m ^ 2) ze),
    IsGrpPullback P.A Xo.univ.t.G y α ∧ LBIso P.L (Xo.univ.t.PP.L.pull α) ∧ IsThetaPt P m (levelPoint lev hg) v

theorem finite_thetaData (Xo : Moduli Dw l) (c : Coeff l) (g j : ℕ) (hbig : 81 ^ g * g.factorial < 3 ^ j * 81)
    (K : Type) [Field K] [IsAlgClosed K] (h3 : ((3 : ℕ) : K) ≠ 0) (ze : Γ(Sp K, ⊤)ˣ) (x : Sp K ⟶ Xo.XF c)
    (v : (Fin (2 * g) → ZMod ((3 ^ j * 81) ^ 2)) → Γ((baseOver (Sp K)).left, ⊤)) :
    Set.Finite {y : Sp K ⟶ Xo.XF c | y ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ ∧
      ThetaData Xo (y ≫ pullback.fst _ _) g (3 ^ j * 81) ze v} := by
  by_cases hne : ∃ y₀ : Sp K ⟶ Xo.XF c, y₀ ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ ∧
      ThetaData Xo (y₀ ≫ pullback.fst _ _) g (3 ^ j * 81) ze v
  · obtain ⟨y₀, -, P₀, hg₀, -, lev₀, -, -, hθ₀⟩ := hne
    have hQ := GlobalTheory.T.unitaryModuli_finite_points_with_given_polarisedFibre E H Dw l Xo K P₀ (x ≫ pullback.fst _ _ ≫ Xo.s)
    refine Set.Finite.of_finite_image (f := fun y => y ≫ pullback.fst _ _) (hQ.subset ?_) ?_
    · rintro _ ⟨y, ⟨hys, P, hg, α, lev, hpb, hPL, hθ⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · show (y ≫ pullback.fst _ _) ≫ Xo.s = x ≫ pullback.fst _ _ ≫ Xo.s
        rw [Category.assoc, pullback.condition, ← Category.assoc, hys, Category.assoc, ← pullback.condition]
      · obtain ⟨φ, hφ, -⟩ := (GlobalTheory.T.thetaPoint_determines_and_end_determined_torsion).1 g 3 2 j 81 (3 ^ j * 81) Nat.prime_three (by decide) le_rfl
          (by norm_num) rfl hbig K h3 P₀ P hg₀ hg ze lev₀ lev v hθ₀ hθ
        exact ⟨φ.hom.left ≫ α, polFib_transport Xo.univ.t.PP.isLB φ hφ hpb hPL⟩
    · intro y₁ h₁ y₂ h₂ h
      exact pullback.hom_ext h (h₁.1.trans h₂.1.symm)
  · convert Set.finite_empty
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => hne ⟨y, h⟩

end GlobalTheory.UMin.QF

namespace GlobalTheory.UMin.QF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

theorem exists_thetaData (Xo : Moduli Dw l) (c : Coeff l) {o : Type} [CommRing o] {n j g : ℕ}
    (hg : g = Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) (f : Xo.XF c ⟶ PSpace o n)
    (hn : n + 1 = (3 ^ j * 81) ^ (4 * g))
    (hth : ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (3 ^ j * 81) (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f)
    (K : Type) [Field K] [IsAlgClosed K] (hm0 : ((3 ^ j * 81 : ℕ) : K) ≠ 0) (ze : Γ(Sp K, ⊤)ˣ)
    (hze : IsPrimitiveRoot ze ((3 ^ j * 81) ^ 2)) (x : Sp K ⟶ Xo.XF c) (e : Fin (n + 1) → K)
    (he : PCrd (x ≫ f) e) (T : Finset (Fin (n + 1) → K))
    (hT : ∀ (c : Fin (n + 1) → K) (a : K), a ≠ 0 → (∀ j, symTup c j = a * e j) →
      ∃ mu : K, mu ≠ 0 ∧ (fun b => mu * c b) ∈ T)
    (y : Sp K ⟶ Xo.XF c) (hy : y ≫ f = x ≫ f) :
    ∃ (t : T) (β : (Fin (2 * g) → ZMod ((3 ^ j * 81) ^ 2)) → Fin (n + 1)),
      ThetaData Xo (y ≫ pullback.fst _ _) g (3 ^ j * 81) ze (fun a => GlobalTheory.ZH.fn ((t : Fin (n + 1) → K) (β a))) := by
  have hodd : Odd (3 ^ j * 81) := (Odd.pow (by decide : Odd 3)).mul (by decide : Odd 81)
  have hLB := Xo.univ.t.PP.isLB
  have hρ := Xo.univ.t.PP.rigGen
  obtain ⟨P, α, hPg, hpb, hPL⟩ := GlobalTheory.T.universalTriple_fibre_principallyPolarised_dimension E H Dw l Xo c K (y ≫ pullback.fst _ _)
  rw [← hg] at hPg
  have hfib : PolFib Xo.univ.t.G Xo.univ.t.PP.L g (y ≫ pullback.fst _ _) := ⟨P, α, hPg, hpb, hPL⟩
  obtain ⟨⟨θ, hθ⟩, -⟩ := GlobalTheory.T.principallyPolarisedFibre_exists_generator_stable _ Xo.univ.t.G Xo.univ.t.PP.L hLB g K _ hfib
  obtain ⟨pt, cy, hcy⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed _ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig hLB hρ g (3 ^ j * 81) (n + 1) K
    _ θ hodd hm0 hn hfib
  have hH : HasTh Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (3 ^ j * 81) (y ≫ pullback.fst _ _) cy :=
    ⟨θ, pt, hθ, hcy⟩
  have hP1 : PCrd (y ≫ f) (symTup cy) := hth K y cy hH
  rw [hy] at hP1
  obtain ⟨a, ha0, ha⟩ := (GlobalTheory.T.projectiveHomogeneousCoords_field_determine_descend).2.1 o K n (x ≫ f) e (symTup cy) he hP1
  obtain ⟨mu, hmu0, hmuT⟩ := hT cy a ha0 ha
  haveI := P.isAb.comm
  obtain ⟨rig, hrig⟩ := P.rigid
  have hP : HasTh P.A P.L rig (3 ^ j * 81) (𝟙 (Sp K)) cy := by
    rw [hasTh_iff] at hH ⊢
    refine (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian _ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig hLB hρ (Sp K) P.A P.L rig
      (y ≫ pullback.fst _ _) α P.isLB hrig hpb hPL (3 ^ j * 81) (3 ^ j * 81) (n + 1) (n + 1) K (𝟙 _) cy cy).2 ?_
    rwa [Category.id_comp]
  obtain ⟨lev, β, hβ⟩ := GlobalTheory.T.exists_level_thetaPoint_of_thetaConstants_level_square K P rig g (3 ^ j * 81) (n + 1) hPg cy ze hrig hodd hm0 hze hP
  exact ⟨⟨_, hmuT⟩, β, P, hPg, α, lev, hpb, hPL, hβ mu hmu0⟩

end GlobalTheory.UMin.QF

namespace GlobalTheory.UMin.QF

theorem finite_fibre_thMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (j n : ℕ) (f : Xo.XF c ⟶ PSpace o n), 81 ^ (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)).factorial < 3 ^ j * 81 → n + 1 = (3 ^ j * 81) ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (3 ^ j * 81) (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Xo.XF c), Set.Finite {y : Sp K ⟶ Xo.XF c | y ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ ∧ y ≫ f = x ≫ f} := by
  intro E _ _ _ H Dw l Xo c o _ j n f hbig hn hth K _ _ x
  haveI : CharZero K := charZero_of_pt (x ≫ pullback.snd _ _)
  set g := Module.finrank ℚ E / 2 * (Dw.p + Dw.q) with hg
  have hm0 : ((3 ^ j * 81 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  have h3 : ((3 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by norm_num)
  have hpos : 0 < (3 ^ j * 81) ^ 2 := by positivity
  haveI : NeZero (((3 ^ j * 81) ^ 2 : ℕ) : K) := ⟨Nat.cast_ne_zero.2 hpos.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K ((3 ^ j * 81) ^ 2)
  let eK := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  have hz' := hz.map_of_injective eK.injective
  set ze : Γ(Sp K, ⊤)ˣ := (hz'.isUnit hpos.ne').unit with hzedef
  have hze : IsPrimitiveRoot ze ((3 ^ j * 81) ^ 2) := hz'.isUnit_unit hpos.ne'
  obtain ⟨⟨e, he⟩, -⟩ := (GlobalTheory.T.projectiveHomogeneousCoords_basic_properties).2.2 o K n (x ≫ f)
  obtain ⟨T, hT⟩ := GlobalTheory.T.thetaSymmetricFunctionsDegreeFactorial_scaled_finite K (n + 1) e
  haveI : NeZero ((3 ^ j * 81) ^ 2) := ⟨hpos.ne'⟩
  refine (Set.finite_iUnion fun d : T × ((Fin (2 * g) → ZMod ((3 ^ j * 81) ^ 2)) → Fin (n + 1)) =>
    finite_thetaData Xo c g j hbig K h3 ze x
      (fun a => GlobalTheory.ZH.fn ((d.1 : Fin (n + 1) → K) (d.2 a)))).subset ?_
  rintro y ⟨h1, h2⟩
  obtain ⟨t, β, hd⟩ := exists_thetaData Xo c hg f hn hth K hm0 ze hze x e he T hT y h2
  exact Set.mem_iUnion.2 ⟨(t, β), h1, hd⟩

end GlobalTheory.UMin.QF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTranslateValuesShiftByRootOfUnityStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_translate_values_shift_by_root_of_unity : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] {S : ThetaSys o Ω} (ρ : S.Real) (H : AddSubgroup S.Gam) (m : ℕ), S.N = m ^ 2 → ∀ h h' : S.Gam, m • h = m • h' → h' - h ∈ H → ∃ ξ : Ω, (∃ k : ℕ, 0 < k ∧ ξ ^ k = 1) ∧ ∀ t ∈ S.perp H, ∑ j, algebraMap o Ω (S.ρ t j ρ.i₀) * S.ev h' j = ξ * ∑ j, algebraMap o Ω (S.ρ t j ρ.i₀) * S.ev h j := by
  first | exact @GlobalTheory.UPoinc.USum.sum_ev_shift | exact GlobalTheory.UPoinc.USum.sum_ev_shift | (intros; apply GlobalTheory.UPoinc.USum.sum_ev_shift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityBaseFormMulFibreVolumeStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeDensity_baseForm_mul_fibreVolume : ∀ (n d : ℕ) (J : Type) [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) (α : Alt d), dens (pull (bsL ε) α * ((∏ j : J, (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j)) : Ev n) : Alt n)) = dens α := by
  first | exact @GlobalTheory.FlagCell2.BaseVol.dens_pull_mul_vol | exact GlobalTheory.FlagCell2.BaseVol.dens_pull_mul_vol | (intros; apply GlobalTheory.FlagCell2.BaseVol.dens_pull_mul_vol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityBlockTriangularDiagonalBlocksStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeDensity_blockTriangular_diagonalBlocks : ∀ (n d : ℕ) (J T : Type) [Fintype J] [Fintype T] (ε : Fin n ≃ Fin d ⊕ J) (lev : J → T) (ρ : T → ℕ) (K : T → Fin n → Fin n → ℂ) (r : T → ℕ), (∀ t, r t = Fintype.card {j // lev j = t}) → (∀ t j, lev j ≠ t → ρ t ≤ ρ (lev j) → ∀ b, K t (ε.symm (.inr j)) b = 0 ∧ K t b (ε.symm (.inr j)) = 0) → ∀ α : Alt d, dens (pull (bsL ε) α * ((∏ t, (∑ a, ∑ b, K t a b • sym (a, b)) ^ r t : Ev n) : Alt n)) = dens (pull (bsL ε) α * ((∏ t, (∑ a : {j // lev j = t}, ∑ b : {j // lev j = t}, K t (ε.symm (.inr a.1)) (ε.symm (.inr b.1)) • sym (ε.symm (.inr a.1), ε.symm (.inr b.1))) ^ r t : Ev n) : Alt n)) := by
  first | exact @GlobalTheory.FlagTri.dens_blockTri | exact GlobalTheory.FlagTri.dens_blockTri | (intros; apply GlobalTheory.FlagTri.dens_blockTri <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjFixAtStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_conj_fix_at : GlobalTheory.Published.RayClassFieldSt → TwAdm → GlobalTheory.BigOn.Exp.TwConj.FixAt := by
  first | exact @GlobalTheory.BigOn.Exp.TwConj.fixAt_holds | exact GlobalTheory.BigOn.Exp.TwConj.fixAt_holds | (intros; apply GlobalTheory.BigOn.Exp.TwConj.fixAt_holds <;> assumption)
end

