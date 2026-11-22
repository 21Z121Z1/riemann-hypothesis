import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0091
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.TopologicalKrullDimLeOfIrreducibleCloseds

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatesIntoHolds
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIntegral

theorem exists_point_in_all {K : Type} [Field K] [IsAlgClosed K] {X Y : Scheme.{0}} (π : X ⟶ Y)
    [LocallyOfFiniteType π] [GeometricallyIntegral π] (x : Sp K ⟶ Y) {J : Type} [Finite J]
    (U : J → X.Opens) (hU : ∀ i, ∃ q : X, q ∈ U i ∧ π q = x (IsLocalRing.closedPoint K)) :
    ∃ g : Sp K ⟶ X, g ≫ π = x ∧ ∀ i, g (IsLocalRing.closedPoint K) ∈ U i := by
  have : IsIntegral (pullback π x) :=
    GeometricallyIntegral.geometrically_isIntegral x _ _ (IsPullback.of_hasPullback π x)
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x)
  have hgen : ∀ i, pullback.fst π x (genericPoint (pullback π x :)) ∈ U i := fun i => by
    obtain ⟨q, hq, hx⟩ := hU i
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x) q
      (IsLocalRing.closedPoint K) hx
    exact ((genericPoint_specializes z).map (pullback.fst π x).continuous).mem_open (U i).isOpen (hz ▸ hq)
  obtain ⟨c, hcO, hc'⟩ := nonempty_inter_closedPoints
    (Z := ⋂ i, ((pullback.fst π x ⁻¹ᵁ U i : (pullback π x).Opens) : Set (pullback π x :))) ⟨_, Set.mem_iInter.2 hgen⟩
    (isOpen_iInter_of_finite fun i => (pullback.fst π x ⁻¹ᵁ U i).isOpen).isLocallyClosed
  have hc : IsClosed {c} := hc'
  refine ⟨pointOfClosedPoint (pullback.snd π x) c hc ≫ pullback.fst π x, ?_, fun i => ?_⟩
  · rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  · show pullback.fst π x (pointOfClosedPoint (pullback.snd π x) c hc _) ∈ U i
    exact (congrArg (fun t => pullback.fst π x t ∈ U i)
      (pointOfClosedPoint_apply (pullback.snd π x) c hc _)).mpr (Set.mem_iInter.1 hcO i)

section Translation

variable {O : Type} [CommRing O]

theorem specO_self_hom : (specO O O).hom = 𝟙 (Sp O) := Spec.map_id _

def toBase (G : Over (Sp O)) : G ⟶ specO O O :=
  Over.homMk G.hom ((congrArg (G.hom ≫ ·) specO_self_hom).trans (Category.comp_id _))

theorem eq_toBase {G : Over (Sp O)} (f : G ⟶ specO O O) : f = toBase G :=
  Over.OverMorphism.ext (((Category.comp_id _).symm.trans
    (congrArg (f.left ≫ ·) specO_self_hom.symm)).trans (Over.w f))

def transl {G : Over (Sp O)} [GrpObj G] (a : specO O O ⟶ G) : G ⟶ G := 𝟙 G * (toBase G ≫ a)

theorem comp_transl {G T : Over (Sp O)} [GrpObj G] (a : specO O O ⟶ G) (w : T ⟶ G) :
    w ≫ transl a = w * (toBase T ≫ a) := by
  rw [transl, MonObj.comp_mul, Category.comp_id, ← Category.assoc, eq_toBase (w ≫ toBase G)]

theorem point_comp_transl {G : Over (Sp O)} [GrpObj G] (a z : specO O O ⟶ G) :
    z ≫ transl a = z * a := by
  rw [comp_transl, ← eq_toBase (𝟙 _), Category.id_comp]

theorem transl_inv_comp {G : Over (Sp O)} [GrpObj G] (a : specO O O ⟶ G) :
    transl a⁻¹ ≫ transl a = 𝟙 G := by
  rw [comp_transl, transl, _root_.mul_assoc, ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one,
    _root_.mul_one]

end Translation

theorem exists_translate_inOpen (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field K]
    [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (G : Over (Sp O)) [GrpObj G] [Smooth G.hom]
    [GeometricallyConnected G.hom] (U : G.left.Opens) (x : G.left) (hx : x ∈ U)
    (hx' : G.hom x = IsLocalRing.closedPoint O) (J : Type) [Finite J] (a : J → (specO O O ⟶ G)) :
    ∃ z : specO O O ⟶ G, ∀ i, InOpen U (z * a i) := by
  obtain ⟨-, hk, hlift⟩ := valuationRing_henselian_and_lift_of_isAlgClosed O K
  have := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres G.hom
  have hr : spMap (IsLocalRing.residue O) (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) =
      IsLocalRing.closedPoint O := IsLocalRing.comap_closedPoint (IsLocalRing.residue O)
  obtain ⟨g, hg, hgU⟩ := exists_point_in_all G.hom (spMap (IsLocalRing.residue O))
    (fun i => (transl (a i)).left ⁻¹ᵁ U) fun i => ⟨(transl (a i)⁻¹).left x, by
      show (transl (a i)).left ((transl (a i)⁻¹).left x) ∈ U
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, transl_inv_comp]
      exact hx, by
      rw [← Scheme.Hom.comp_apply, Over.w, hx', hr]⟩
  obtain ⟨y, hy, hy'⟩ := hlift _ G.hom inferInstance g hg
  refine ⟨Over.homMk y (hy.trans specO_self_hom.symm), fun i => ?_⟩
  rw [← point_comp_transl]
  have h1 : (y ≫ (transl (a i)).left) (IsLocalRing.closedPoint O) ∈ U := by
    have e : g (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) = y (IsLocalRing.closedPoint O) := by
      rw [← hy', ← hr]
      rfl
    have := hgU i
    rw [e] at this
    exact this
  exact eq_top_iff.2 fun q _ =>
    ((IsLocalRing.specializes_closedPoint (R := O) q).map
      (y ≫ (transl (a i)).left).continuous).mem_open U.isOpen h1

theorem translatesInto : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
    (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), TranslatesInto P := by
  intro p hp C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P U ⟨x, hx, hxp⟩ J _ a
  have hv := P.integers
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : IsFractionRing O C := hv.isFractionRing
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI := P.semi.smooth
  haveI := P.semi.geomConnected
  refine exists_translate_inOpen O C P.G U x hx ?_ J a
  refine PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal (PrimeSpectrum.isPrime _).ne_top)
    fun b hb => ?_)
  have h1 : v (algebraMap O C b) < 1 := lt_of_le_of_ne (hv.map_le_one b) fun e => hb (hv.isUnit_of_one' e)
  have h2 : 0 < v (algebraMap O C p) := by
    rw [map_natCast]
    exact pos_iff_ne_zero.2 ((Valuation.ne_zero_iff v).2 (Nat.cast_ne_zero.2 hp.out.ne_zero))
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one h2 h1
  have h3 : (p : O) ∣ b ^ n := hv.le_iff_dvd.1 (by rw [map_pow, map_pow]; exact hn.le)
  exact (PrimeSpectrum.isPrime _).mem_of_pow_mem n (Ideal.mem_of_dvd _ h3 hxp)

end GlobalTheory.WeilIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialisingOpenExists
section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat

namespace GlobalTheory.WeilIntegral

theorem exists_open_generic_le (p : ℕ) (O : Type) [CommRing O] (h : SpecialFibreNotInClosure p O)
    {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp O) [Smooth f] (x : X)
    (hx : (p : O) ∈ PrimeSpectrum.asIdeal (R := O) (f x)) (W : X.Opens) (hW : (W : Set X).Nonempty) :
    ∃ U : X.Opens, (∃ y : X, y ∈ U ∧ (p : O) ∈ PrimeSpectrum.asIdeal (R := O) (f y)) ∧
      ∀ y ∈ U, PrimeSpectrum.asIdeal (R := O) (f y) = ⊥ → y ∈ W := by
  obtain ⟨R, j, hj, ⟨x', rfl⟩, -⟩ := X.exists_affine_mem_range_and_range_subset (x := x) (U := ⊤) trivial
  have : Nonempty (Spec R) := ⟨x'⟩
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion j
  have : IsDomain R := (affine_isIntegral_iff R).1 ‹_›
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ f)
  have hs : Smooth (Spec.map φ) := by rw [hφ]; infer_instance
  have hs' : φ.hom.Smooth := (HasRingHomProperty.Spec_iff (P := @Smooth)).1 hs
  letI : Algebra O R := φ.hom.toAlgebra
  have : Algebra.Smooth O R := hs'
  have key : ∀ (z : Spec R) (c : O), c ∈ PrimeSpectrum.asIdeal (R := O) (f (j z)) ↔
      algebraMap O R c ∈ PrimeSpectrum.asIdeal (R := R) z := by
    intro z c
    rw [← Scheme.Hom.comp_apply, ← hφ]
    rfl
  obtain ⟨_, hz, z, rfl⟩ := nonempty_preirreducible_inter W.isOpen j.isOpenEmbedding.isOpen_range hW ⟨_, x', rfl⟩
  obtain ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, hza, ha⟩ := PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
    (a := (z : PrimeSpectrum R)) (u := (j ⁻¹ᵁ W : Set (Spec R))) hz (j ⁻¹ᵁ W).isOpen
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hza (Ideal.zero_mem _)
  obtain ⟨q, g, c, hq, hg, hc, d, hd⟩ := h R a ha0 ⟨x', by simpa using (key x' p).1 hx⟩
  refine ⟨j ''ᵁ (PrimeSpectrum.basicOpen g), ⟨j q, ⟨q, hg, rfl⟩, (key q p).2 (by simpa using hq)⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩ h0
  refine ha (a := y) fun hay => ?_
  have h1 : algebraMap O R c * g ∈ PrimeSpectrum.asIdeal (R := R) y := hd ▸ Ideal.mul_mem_right _ _ hay
  rcases (PrimeSpectrum.isPrime (R := R) y).mem_or_mem h1 with h2 | h2
  · exact hc (h0.le ((key y c).2 h2))
  · exact hy h2

theorem hasTrivialisingOpen_of_specialFibreNotInClosure (p : ℕ) [Fact p.Prime] (C : Type) [Field C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [hp : Fact ¬IsUnit (p : O)]
    (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ) (h : SpecialFibreNotInClosure p O) :
    HasTrivialisingOpen P := by
  have hinj := P.integers.hom_inj
  have : IsDomain O := hinj.isDomain (algebraMap O C)
  have : IsFractionRing O C := P.integers.isFractionRing
  have := P.semi.smooth
  have := P.semi.geomConnected
  have : IsIntegral P.G.left := isIntegral_of_smooth_of_geometricallyConnected P.G.hom
  have := geometricallyIntegral_of_smooth P.G.hom
  have : IsPreimmersion (spMap (algebraMap O C)) := IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  have : IsPreimmersion P.gen := MorphismProperty.of_isPullback P.gen_pull.1.flip ‹_›
  obtain ⟨m, hm, hpm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hp.out)
  obtain ⟨x, hx⟩ := P.G.hom.surjective (⟨m, hm.isPrime⟩ : PrimeSpectrum O)
  have := P.A.isAb.smooth
  have := P.A.isAb.geomConnected
  have : IsIntegral P.A.A.left := isIntegral_of_smooth_of_geometricallyConnected P.A.A.hom
  obtain ⟨a⟩ : Nonempty P.A.A.left := inferInstance
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (P.A.isLB.cover.ge (Set.mem_univ a))
  obtain ⟨W, hW, hWV⟩ := P.gen.isEmbedding.isInducing.isOpen_iff.1 (P.A.L.U i).isOpen
  obtain ⟨U, hU, hUW⟩ := exists_open_generic_le p O h P.G.hom x (by rw [hx]; exact hpm) ⟨W, hW⟩
    ⟨P.gen a, hWV.ge hi⟩
  refine ⟨U, hU, ChartRig.exists_gen_pull _ _ i P.A.isLB fun y _ => hWV.le (hUW _ y.2 ?_)⟩
  rw [← Scheme.Hom.comp_apply, P.gen_pull.1.w, Scheme.Hom.comp_apply]
  have e : ∀ z : PrimeSpectrum C, Ideal.comap (algebraMap O C) z.asIdeal = ⊥ := fun z => by
    rw [Ideal.eq_bot_of_prime z.asIdeal]
    exact Ideal.comap_bot_of_injective _ hinj
  exact e _

theorem hasTrivialisingOpen (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
    (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ) (h : SpecialFibreNotInClosure p O) :
    HasTrivialisingOpen P :=
  hasTrivialisingOpen_of_specialFibreNotInClosure p C v O Λ P h

end GlobalTheory.WeilIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumNormAdelicSchwartzRationalTranslatesLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section

namespace GlobalTheory.UniformTranslateBound

open Filter Topology
open scoped Classical

theorem schwartz_translate_decay {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : SchwartzMap E ℂ) (k : ℕ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x y : E, ‖y‖ ≤ R → ‖f (x + y)‖ ≤ D * ((1 + ‖x‖) ^ k)⁻¹ := by
  set M := 2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f with hM
  have h0 : ∀ w : E, (1 + ‖w‖) ^ k * ‖f w‖ ≤ M := fun w => by
    have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl f w
    rwa [norm_iteratedFDeriv_zero] at h1
  have hM0 : 0 ≤ M := le_trans (by positivity) (h0 0)
  refine ⟨(1 + R) ^ k * M, by positivity, fun x y hy => ?_⟩
  have hx : 0 < (1 + ‖x‖) ^ k := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hx]
  have h2 : 1 + ‖x‖ ≤ (1 + R) * (1 + ‖x + y‖) := by
    have : ‖x‖ ≤ ‖x + y‖ + ‖y‖ := by simpa using norm_sub_le (x + y) y
    nlinarith [norm_nonneg (x + y), norm_nonneg y, mul_nonneg hR (norm_nonneg (x + y))]
  calc ‖f (x + y)‖ * (1 + ‖x‖) ^ k ≤ ‖f (x + y)‖ * ((1 + R) * (1 + ‖x + y‖)) ^ k := by gcongr
    _ = (1 + R) ^ k * ((1 + ‖x + y‖) ^ k * ‖f (x + y)‖) := by rw [mul_pow]; ring
    _ ≤ (1 + R) ^ k * M := by gcongr; exact h0 _

theorem summable_one_add_norm_inv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] :
    Summable fun z : L => ((1 + ‖(z : E)‖) ^ (Module.finrank ℤ L + 1))⁻¹ := by
  refine Summable.of_norm_bounded_eventually (ZLattice.summable_norm_pow_inv L _ (Nat.lt_succ_self _)) ?_
  refine (Set.finite_singleton (0 : L)).subset fun z hz => ?_
  by_contra h0
  apply hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 h0
  show ‖((1 + ‖(z : E)‖) ^ (Module.finrank ℤ L + 1))⁻¹‖ ≤ ‖z‖⁻¹ ^ (Module.finrank ℤ L + 1)
  rw [norm_inv, norm_pow, Real.norm_of_nonneg (by positivity), ← inv_pow]
  gcongr
  show ‖z‖ ≤ 1 + ‖z‖
  linarith

variable (F : Type) [Field F] [NumberField F]

theorem mixed_algebraMap_fst (x : F) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) x).1 = mixedEmbedding F x := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rfl

theorem pureA_bound {κ : Type} [Fintype κ] (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F))
    {K : Set (κ → AdeleRing (𝓞 F) F)} (hK : IsCompact K) :
    ∃ B : ℝ, ∀ z ∈ K, ∀ s : Finset (κ → F),
      ∑ ξ ∈ s, ‖GlobalTheory.WeilM.pureA F f g ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + z)‖ ≤ B := by
  let zi : (κ → AdeleRing (𝓞 F) F) → (κ → mixedEmbedding.mixedSpace F) :=
    fun z i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1
  let zf : (κ → AdeleRing (𝓞 F) F) → (κ → FiniteAdeleRing (𝓞 F) F) := fun z i => (z i).2
  have hzi : Continuous zi :=
    continuous_pi fun i => (GlobalTheory.ThetaTransformMeas.continuous_mixed F).comp (continuous_fst.comp (continuous_apply i))
  have hzf : Continuous zf := continuous_pi fun i => continuous_snd.comp (continuous_apply i)
  obtain ⟨R, hR⟩ := (hK.image hzi).isBounded.subset_closedBall 0
  obtain ⟨Bg, hBg⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  have hBg0 : 0 ≤ Bg := (norm_nonneg _).trans (hBg 0)
  let C : Set (κ → FiniteAdeleRing (𝓞 F) F) := (fun p => p.1 - p.2) '' (tsupport g ×ˢ (zf '' K))
  have hC : IsCompact C := (hg.2.isCompact.prod (hK.image hzf)).image (continuous_fst.sub continuous_snd)
  obtain ⟨N, hN, hNC⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact F hC
  haveI := GlobalTheory.WeilM.discreteTopology_denomLattice F κ hN
  let e : (κ → F) → (κ → mixedEmbedding.mixedSpace F) := fun ξ i => mixedEmbedding F (ξ i)
  let S : Set (κ → F) := {ξ | e ξ ∈ GlobalTheory.WeilM.denomLattice F κ N}
  obtain ⟨D, hD0, hD⟩ := schwartz_translate_decay f (Module.finrank ℤ (GlobalTheory.WeilM.denomLattice F κ N) + 1)
    (max R 0) (le_max_right _ _)
  let h : (κ → F) → ℝ := S.indicator fun ξ =>
    D * ((1 + ‖e ξ‖) ^ (Module.finrank ℤ (GlobalTheory.WeilM.denomLattice F κ N) + 1))⁻¹ * Bg
  have hh : ∀ ξ, 0 ≤ h ξ := fun ξ => Set.indicator_nonneg (fun _ _ => by positivity) ξ
  have hsum : Summable h := by
    rw [← summable_subtype_iff_indicator]
    let j : S → GlobalTheory.WeilM.denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
    have hj : Function.Injective j := fun a b hab => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val hab) i))
    exact (((summable_one_add_norm_inv _).comp_injective hj).mul_left D).mul_right Bg
  refine ⟨∑' ξ, h ξ, fun z hz s => ?_⟩
  refine le_trans (Finset.sum_le_sum fun ξ _ => ?_) (hsum.sum_le_tsum s fun ξ _ => hh ξ)
  have hsplit : GlobalTheory.WeilM.pureA F f g ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + z) =
      f (e ξ + zi z) * g ((fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) + zf z) := by
    unfold GlobalTheory.WeilM.pureA
    congr 2
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((algebraMap F (AdeleRing (𝓞 F) F) (ξ i)).1 + (z i).1) = _
    rw [map_add, mixed_algebraMap_fst]
    rfl
  rw [hsplit, norm_mul]
  by_cases hg0 : g ((fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) + zf z) = 0
  · rw [hg0, norm_zero, mul_zero]; exact hh ξ
  have hmem : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ C :=
    ⟨(_, zf z), ⟨subset_tsupport _ hg0, z, hz, rfl⟩, add_sub_cancel_right _ _⟩
  have hξS : ξ ∈ S := by
    show ∀ i, (N : ℝ) • e ξ i ∈ mixedEmbedding.integerLattice F
    intro i
    obtain ⟨y, hy⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hNC _ hmem i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  show _ ≤ S.indicator _ ξ
  rw [Set.indicator_of_mem hξS]
  have hzR : ‖zi z‖ ≤ max R 0 := le_max_of_le_left (mem_closedBall_zero_iff.1 (hR ⟨z, hz, rfl⟩))
  exact mul_le_mul (hD _ _ hzR) (hBg _) (norm_nonneg _) (by positivity)

theorem schA_bound_compact {κ : Type} [Fintype κ] {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ)
    {K : Set (κ → AdeleRing (𝓞 F) F)} (hK : IsCompact K) :
    ∃ B : ℝ, ∀ z ∈ K, ∀ s : Finset (κ → F),
      ∑ ξ ∈ s, ‖Φ ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + z)‖ ≤ B := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact pureA_bound F f hg hK
  | zero => exact ⟨0, fun z _ s => by simp⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨B1, hB1⟩ := h1
    obtain ⟨B2, hB2⟩ := h2
    refine ⟨B1 + B2, fun z hz s => ?_⟩
    refine le_trans (Finset.sum_le_sum fun ξ _ => norm_add_le (Φ _) (Ψ _)) ?_
    rw [Finset.sum_add_distrib]
    exact add_le_add (hB1 z hz s) (hB2 z hz s)
  | smul c Φ _ h =>
    obtain ⟨B, hB⟩ := h
    refine ⟨‖c‖ * B, fun z hz s => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hB z hz s) (norm_nonneg c)

theorem tsum_norm_translate_le : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι],
    ∀ Φ ∈ GlobalTheory.WeilM.schA F ι,
    ∃ B : ℝ, ∀ z : ι → AF F, ∑' ξ : ι → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + z)‖ ≤ B := by
  intro F _ _ ι _ Φ hΦ
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.RatVecDomain.exists_compact_cover_ratVec F ι
  obtain ⟨B, hB⟩ := schA_bound_compact F hΦ hK
  refine ⟨B, fun z => ?_⟩
  obtain ⟨γ, hγ, hγK⟩ := hcov z
  obtain ⟨η, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff _).1 hγ
  let G : (ι → F) → ℝ := fun ξ =>
    ‖Φ ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (η i)) + z))‖
  have hG : ∀ ξ : ι → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + z)‖ = G (Equiv.subRight η ξ) := by
    intro ξ
    show _ = ‖Φ _‖
    congr 2
    funext i
    simp only [Equiv.subRight_apply, Pi.add_apply, Pi.sub_apply, map_sub]
    abel
  calc ∑' ξ : ι → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + z)‖ = ∑' ξ, G (Equiv.subRight η ξ) := tsum_congr hG
    _ = ∑' ξ, G ξ := (Equiv.subRight η).tsum_eq G
    _ ≤ B := Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) (hB _ hγK)

end GlobalTheory.UniformTranslateBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingLocusClosedSubscheme
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover)

namespace GlobalTheory.ZeroLocus

variable {Y T : Scheme.{0}} {G Q : Y.Modules}

theorem mem_annihilator_cokernel_iff (u : G ⟶ Q) [G.IsQuasicoherent] [Q.IsQuasicoherent]
    {U : Y.Opens} (hU : IsAffineOpen U) {e : Fin 1 → Γ(Q, U)} (he : IsFrame e) (a : Γ(Y, U)) :
    a ∈ Module.annihilator Γ(Y, U) Γ(cokernel u, U) ↔ ∃ t, u.app U t = a • e 0 := by
  have hex := QCoh.exact_cokernel_π_app u hU
  have hsur := QCoh.surjective_cokernel_π_app u hU
  have hsm (b : Γ(Y, U)) (s : Γ(Q, U)) :
      (cokernel.π u).app U (b • s) = b • (cokernel.π u).app U s :=
    Scheme.Modules.Hom.app_smul _ b s
  rw [Module.mem_annihilator]
  constructor
  · intro H
    refine (hex _).1 ?_
    rw [hsm]
    exact H _
  · rintro ⟨t, ht⟩ m
    obtain ⟨s, rfl⟩ := hsur m
    have h0 : a • (cokernel.π u).app U (e 0) = 0 := by
      rw [← hsm]
      exact (hex _).2 ⟨t, ht⟩
    have hs := (he.basis le_rfl).sum_repr s
    rw [Fin.sum_univ_one, IsFrame.basis_apply, resM_self] at hs
    rw [← hs, hsm, smul_comm, h0, smul_zero]

theorem pullbackSections_smul_self (h : T ⟶ Y) {U : Y.Opens} (a : Γ(Y, U)) (s : Γ(Q, U)) :
    QCoh.pullbackSections h Q (le_refl (h ⁻¹ᵁ U)) (a • s) =
      h.app U a • QCoh.pullbackSections h Q (le_refl (h ⁻¹ᵁ U)) s := by
  rw [QCoh.pullbackSections_smul, Scheme.Hom.appLE_eq_app]

theorem eq_zero_of_pullbackSections (f : T ⟶ Y) {E : T.Modules}
    (α : (Scheme.Modules.pullback f).obj G ⟶ E)
    (H : ∀ (V : Y.Opens) (s : Γ(G, V)), α.app _ (QCoh.pullbackSections f G (le_refl (f ⁻¹ᵁ V)) s) = 0) :
    α = 0 := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext s
  have := H V s
  rw [QCoh.pullbackSections_apply] at this
  erw [Twist.resM_self] at this
  exact this

theorem exists_closed_zeroLocus : ∀ (Y : Scheme.{0}) (G Q : Y.Modules) (u : G ⟶ Q), G.IsQuasicoherent → IsVB Q 1 →
    ∃ (Z : Scheme.{0}) (j : Z ⟶ Y), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (h : T ⟶ Y),
      (Scheme.Modules.pullback h).map u = 0 ↔ ∃ h' : T ⟶ Z, h' ≫ j = h := by
  intro Y G Q u hG hQ
  haveI := hQ.isFiniteQC
  let I := QCoh.annihilatorSheaf (cokernel u)
  have hI (U : Y.Opens) (hU : IsAffineOpen U) {e : Fin 1 → Γ(Q, U)} (he : IsFrame e) (a : Γ(Y, U)) :
      (I.subschemeι.app U).hom a = 0 ↔ ∃ t, u.app U t = a • e 0 := by
    rw [← RingHom.mem_ker, I.ker_subschemeι_app ⟨U, hU⟩, QCoh.annihilatorSheaf_ideal]
    exact mem_annihilator_cokernel_iff u hU he a
  refine ⟨I.subscheme, I.subschemeι, inferInstance, fun T h => ⟨fun H => ?_, ?_⟩⟩
  · choose U e hU hy hle he using fun y : Y => hQ.exists_affine (V := ⊤) (x := y) trivial
    refine ProjSpace.exists_lift_of_cover I.subschemeι h U hU
      (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy y⟩) fun y s hs => ?_
    obtain ⟨t, ht⟩ := (hI _ (hU y) (he y) s).1 hs
    have h1 : ((Scheme.Modules.pullback h).map u).app (h ⁻¹ᵁ U y)
        (QCoh.pullbackSections h G (le_refl _) t) = 0 := by rw [H]; rfl
    rw [QCoh.pullback_map_app_pullbackSections, ht, pullbackSections_smul_self] at h1
    have hf := ((he y).pullback h) (h ⁻¹ᵁ U y) le_rfl
    have : (fun _ : Fin 1 => h.app (U y) s) = 0 := hf.1 (by
      simp only [Fintype.linearCombination_apply, Fin.sum_univ_one, resM_self, map_zero]
      exact h1)
    simpa using congrFun this 0
  · rintro ⟨h', rfl⟩
    refine eq_zero_of_pullbackSections _ _ fun V t => ?_
    rw [QCoh.pullback_map_app_pullbackSections]
    choose W e hW hyW hWV he using fun y : V => hQ.exists_affine y.2
    refine sec_ext_of_cover (fun y => (h' ≫ I.subschemeι) ⁻¹ᵁ W y)
      (fun y => Scheme.Hom.preimage_mono _ (hWV y))
      (fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨_, hx⟩, hyW _⟩) fun y => ?_
    rw [map_zero]
    have e1 := QCoh.res_pullbackSections (h' ≫ I.subschemeι) Q (le_refl ((h' ≫ I.subschemeι) ⁻¹ᵁ V))
      (Scheme.Hom.preimage_mono _ (hWV y)) (u.app V t)
    have e2 := QCoh.pullbackSections_res (h' ≫ I.subschemeι) Q (le_refl ((h' ≫ I.subschemeι) ⁻¹ᵁ W y)) (hWV y)
      (u.app V t)
    refine (e1.trans e2.symm).trans ?_
    obtain ⟨c, hc⟩ := (he y (W y) le_rfl).2 (u.app (W y) (resM G (hWV y) t))
    rw [Fintype.linearCombination_apply, Fin.sum_univ_one, resM_self] at hc
    have ha : (I.subschemeι.app (W y)).hom (c 0) = 0 := (hI _ (hW y) (he y) (c 0)).2 ⟨_, hc.symm⟩
    change QCoh.pullbackSections _ Q _ (resM Q (hWV y) (u.app V t)) = 0
    rw [← app_resM, ← hc, pullbackSections_smul_self]
    have hz : (ConcreteCategory.hom ((h' ≫ I.subschemeι).app (W y))) (c 0) = 0 :=
      (congrArg (h'.app (I.subschemeι ⁻¹ᵁ W y)).hom ha).trans (map_zero _)
    rw [hz, zero_smul]

end GlobalTheory.ZeroLocus

end
end

