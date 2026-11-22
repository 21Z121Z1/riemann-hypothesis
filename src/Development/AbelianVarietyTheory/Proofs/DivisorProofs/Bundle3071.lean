import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2979
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2962
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2998
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2905
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2756
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1149
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1362
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3008
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2987
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionOfBasicOpenCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisConjugateHolomorphicUniformization
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.ConjTangent

theorem exists_conj_holUnif_tangent : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X X' : Obj F 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ X.A.left) (g : ℂ ≃+* ℂ)
    (c : 𝔠.elt) (n : ℕ) (u : HolUnif X.A (X.diag c) n) (Ω₀ Ω₁ : ℂ), Ω₀ ≠ 0 → Ω₁ ≠ 0 →
    X'.IsPullBy X (spMap (g : ℂ →+* ℂ)) p →
    ∃ u' : HolUnif X'.A (X'.diag c) n, ∀ (w : Fin n → ℂ) (v : epsR ℂ ⟶ X.A) (v' : epsR ℂ ⟶ X'.A),
      v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → u.IsDiff w v →
        u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v' := by
  intro _ _ _ F _ _ 𝔠 X X' p g c n u Ω₀ Ω₁ h0 h1 hX
  have hn := Obj.holUnif_dim_eq X u
  subst hn
  obtain ⟨L₁, u₁, -, -⟩ := Obj.exists_holUnif_ringHom_lift F 𝔠 X'
  obtain ⟨u₀, -, -, -, -⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif X'.A X'.ab L₁ _ u₁ (X'.diag c)
    (pull_isLB (X'.isLB c) _)
  obtain ⟨-, hu⟩ := GlobalTheory.TorusTransfer.tangent_bijective u X.dim
  obtain ⟨hu₀, -⟩ := GlobalTheory.TorusTransfer.tangent_bijective u₀ X'.dim
  obtain ⟨T, hTi, hT⟩ := GlobalTheory.T.conjugate_uniformization_semilinear_map X.A X'.A p g hX.grp _ _ _ u u₀ hu hu₀
  let ψ : (Fin (Module.finrank ℚ F) → ℂ) → (Fin (Module.finrank ℚ F) → ℂ) :=
    fun w' => Ω₀⁻¹ • fun j => g.symm (Ω₁ * w' j)
  have hψa : ∀ a b, ψ (a + b) = ψ a + ψ b := fun a b => by
    simp only [ψ, ← smul_add]
    congr 1
    ext j
    simp [mul_add]
  have hψs : ∀ (a : ℂ) b, ψ (a • b) = g.symm a • ψ b := fun a b => by
    simp only [ψ, smul_comm (g.symm a) Ω₀⁻¹]
    congr 1
    ext j
    simp [mul_left_comm]
  let φl : (Fin (Module.finrank ℚ F) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ F) → ℂ) :=
    { toFun := fun w' => T (ψ w')
      map_add' := fun a b => by simp only [hψa, map_add]
      map_smul' := fun a b => by
        simp only [hψs, map_smulₛₗ, RingHom.id_apply]
        congr 1
        simp }
  have hinj : Function.Injective φl := by
    intro a b hab
    have hab' := hTi hab
    simp only [ψ] at hab'
    have := smul_right_injective _ (inv_ne_zero h0) hab'
    ext j
    have e := congrFun this j
    simp only [EmbeddingLike.apply_eq_iff_eq] at e
    exact mul_left_cancel₀ h1 e
  let φ := LinearEquiv.ofInjectiveEndo φl hinj
  obtain ⟨u', -, -, -, -, hD⟩ := GlobalTheory.exists_holUnif_reparam X'.A (X'.diag c) _ u₀ φ (fun _ => 1)
    (differentiable_const 1) (fun _ => one_ne_zero) rfl
  refine ⟨u', fun w v v' hv hd => hD _ _ ?_⟩
  by_cases ht : IsTangent v
  · have e : φ (fun j => g (Ω₀ * w j) / Ω₁) = T w := by
      show T (ψ _) = T w
      congr 1
      ext j
      simp only [ψ, Pi.smul_apply, smul_eq_mul]
      rw [mul_div_cancel₀ _ h1, RingEquiv.symm_apply_apply]
      field_simp
    rw [e]
    exact hT w v v' ht hv hd
  · have hw := GlobalTheory.T.differential_zero_of_not_tangent F 𝔠 X _ _ u w v hd ht
    subst hw
    have e : φ (fun j => g (Ω₀ * (0 : Fin (Module.finrank ℚ F) → ℂ) j) / Ω₁) = 0 := by
      have : (fun j => g (Ω₀ * (0 : Fin (Module.finrank ℚ F) → ℂ) j) / Ω₁) = 0 := by
        ext j
        simp
      rw [this, map_zero]
    rw [e]
    exact GlobalTheory.T.conjugate_uniformization_differential_zero X.A X'.A p g hX.grp _ _ _ _ u u₀ v v' hv hd

end GlobalTheory.ConjTangent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisInvariantPointDescendsToSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FinDescent

theorem galoisFixed_point_of_finite : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V], IsIntegrallyClosed V → ∀ (N : Over (Sp V)), IsFinite N.hom → ∀ (nb : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ N), (∀ σ : AlgebraicClosure (FractionRing V) ≃ₐ[FractionRing V] AlgebraicClosure (FractionRing V), spMap σ.toAlgHom.toRingHom ≫ nb.left = nb.left) → ∃ s : 𝟙_ (Over (Sp V)) ⟶ N, nb = toUnit _ ≫ s := by
  first
  | exact @_root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed
  | exact _root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed
  | (apply _root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed <;> assumption)
  | (intros; apply _root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed <;> assumption)
  | (intros; apply @_root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed ..)

end GlobalTheory.FinDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorTorusInvariantOfMultiplicativeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_torus_invariant_of_multiplicative : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f g : G₁ ⟶ G₂} [IsMonHom f] [IsMonHom g] {fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A} [IsMonHom fB] [IsMonHom gB], (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB → (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map gB → ∀ [ConnectedSpace (thickObj R I e G₁).left] (v : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) ((Over.pullback (thick R I e)).map f) ((Over.pullback (thick R I e)).map g) k ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left) mε)), v.IsGen → (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y : T ⟶ thickObj R I e G₁, (Over.map (thick R I e)).map x ≫ (U₁.gt e).pG = 1 → val v (lift (x * x') y).left z J = val v (lift x y).left z J * val v (lift x' y).left z J ∧ val v (lift y (x * x')).left z J = val v (lift y x).left z J * val v (lift y x').left z J) → (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y y' : T ⟶ thickObj R I e G₁, x ≫ (U₁.gt e).q = x' ≫ (U₁.gt e).q → y ≫ (U₁.gt e).q = y' ≫ (U₁.gt e).q → val v (lift x y).left z J = val v (lift x' y').left z J) := by
  first | exact @GlobalTheory.HomMum.gen_invariant_of_mul | exact GlobalTheory.HomMum.gen_invariant_of_mul | (intros; apply GlobalTheory.HomMum.gen_invariant_of_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFiberArithmeticVarietyIntegralProjective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem genericFibre_facts : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (D : ℕ), IsArithVar p D → ∃ (_ : IsIntegral G) (_ : IsLocallyNoetherian G), IsProjOver q ∧ topologicalKrullDim G = D ∧ j (genericPoint G) = genericPoint X ∧ Function.Injective j ∧ (∀ x, IsIso (j.stalkMap x)) ∧ (∀ x, Order.coheight (j x) = Order.coheight x) ∧ ∀ z : X, z ∉ Set.range j → ∀ σ : k →+* ℂ, IsEmpty (CxPts (closι z ≫ p) σ) := by
  intro k K _ _ _ _ X G _ p q j hp D h
  obtain ⟨hG, hd, hη⟩ := GenSmoothCover.genericFibre h hp
  have hq : IsProjOver q := ProjSpace.isProjOver_of_isPullback_spMap _ hp h.isProjOver
  have : IsProper q := CommonModel.isProper_of_isProjOver hq
  have := h.isDomain
  have := IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)
  have : IsPreimmersion j := MorphismProperty.of_isPullback hp.flip this
  have := flat_specMap_localization (nonZeroDivisors k) K
  have : Flat j := MorphismProperty.of_isPullback hp.flip this
  have hs (x : G) : IsIso (j.stalkMap x) := GenSpread.isIso_stalkMap_of_flat j x
  refine ⟨hG, LocallyOfFiniteType.isLocallyNoetherian q, hq, hd, hη, j.isEmbedding.injective, hs,
    fun x => ?_, fun z hz σ => ⟨fun y => hz ?_⟩⟩
  · have := hs x
    have e := ringKrullDim_eq_of_ringEquiv (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at e
    exact_mod_cast e
  · have hr : Set.range j = p ⁻¹' Set.range (spMap (algebraMap k K)) := by
      rw [← Scheme.Pullback.range_fst, ← hp.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
        Function.Surjective.range_comp hp.isoPullback.hom.surjective]
    let c : Sp ℂ := IsLocalRing.closedPoint ℂ
    have hw : closι z (y.1 c) ∈ closure {z} := by
      have : closι z (y.1 c) ∈ Set.range (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z})).subschemeι :=
        ⟨_, rfl⟩
      rw [Scheme.IdealSheafData.range_subschemeι] at this
      simpa using this
    have h₁ : p z ⤳ p (closι z (y.1 c)) := (specializes_iff_mem_closure.2 hw).map p.continuous
    have h₂ : p (closι z (y.1 c)) = spMap σ c := by
      have := y.2
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      exact congrArg (fun f : Sp ℂ ⟶ Sp k => f c) this
    have h₃ : (spMap σ c).asIdeal = ⊥ := by
      change Ideal.comap σ (IsLocalRing.maximalIdeal ℂ) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot]
      exact Ideal.comap_bot_of_injective _ (ChernNull.injective_of_arithVar h σ)
    rw [h₂] at h₁
    have h₄ : (p z).asIdeal ≤ (spMap σ c).asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 h₁
    rw [h₃, le_bot_iff] at h₄
    rw [hr]
    refine ⟨(⟨⊥, inferInstance⟩ : PrimeSpectrum K), PrimeSpectrum.ext ?_⟩
    rw [h₄]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective k K)

end GlobalTheory.Mix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIntersectionFormula
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

noncomputable section

namespace GlobalTheory.GenFibreDegree

theorem interNum_eq_zero_of_not_generic (B Y : Scheme.{0}) [IsIntegral B] (f : Y ⟶ B) (z : Y)
    (hz : f z ≠ genericPoint B) (Z : Scheme.{0}) (i : Z ⟶ Y) [IsIntegral Z]
    (hi : i (genericPoint Z) = z) (G' : Scheme.{0}) (j' : G' ⟶ Z) (s' : G' ⟶ Sp B.functionField)
    (hG' : IsPullback j' s' (i ≫ f) (B.fromSpecStalk (genericPoint B)))
    {ι : Type} [Fintype ι] (P : ι → LB Z) (hP : ∀ a, (P a).IsLB) :
    (letI := algebraΓOfHom s'
     interNum B.functionField (structureModule G') (fun a => (P a).pull j')) = 0 := by
  have hE : IsEmpty G' := by
    refine ⟨fun g => hz ?_⟩
    obtain ⟨_, hr, _, h4⟩ := GlobalTheory.T.generic_fibre_preimmersion_integral B Z (i ≫ f) G' j' s' hG'
    obtain ⟨hGi, hη⟩ := h4 ⟨g⟩
    have hmem : j' (genericPoint G') ∈ Set.range j' := ⟨_, rfl⟩
    rw [hr, hη] at hmem
    simpa [← hi] using hmem
  letI := algebraΓOfHom s'
  exact interNum_eq_zero_of_isZero _ (InterModel.isZero_of_isEmpty _)
    (fun a => LB.isLB_pull (hP a) j')

theorem degree_genericFibre_ratSec : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] [IsLocallyNoetherian Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d e : ℕ), IsArithVar q d → IsArithVar p (d + (e + 1)) → ∀ (f : Y ⟶ B), f ≫ q = p → ∀ (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → ∀ (L : Fin (e + 1) → LB Y) (hL : ∀ a, (L a).IsLB) (r : (L 0).ι → Y.functionFieldˣ) (hr : IsRatSec (L 0) r) (γ : Y → ℤ), (∀ z, (divOfRatSec (hL 0) hr).mult z ≠ 0 → ∃ (Z : Scheme.{0}) (i : Z ⟶ Y) (_ : IsClosedImmersion i) (_ : IsIntegral Z) (G' : Scheme.{0}) (j' : G' ⟶ Z) (s' : G' ⟶ Sp B.functionField), i (genericPoint Z) = z ∧ IsPullback j' s' (i ≫ f) (B.fromSpecStalk (genericPoint B)) ∧ γ z = (letI := algebraΓOfHom s'; interNum B.functionField (structureModule G') (fun a : Fin e => ((L a.succ).pull i).pull j'))) → (letI := algebraΓOfHom s; interNum B.functionField (structureModule G) (fun a => (L a).pull j)) = ∑ᶠ z, (divOfRatSec (hL 0) hr).mult z * γ z := by
  intro k _ B Y _ _ _ q p d e hq hp f hfq G j s hpb L hL r hr γ hγ
  obtain ⟨hpre, hrange, hstalk, hint⟩ := GlobalTheory.T.generic_fibre_preimmersion_integral B Y f G j s hpb
  set F : Y → ℤ := fun z => (divOfRatSec (hL 0) hr).mult z * γ z with hF
  have hoff : ∀ z, z ∉ Set.range j → F z = 0 := by
    intro z hz
    by_cases hm : (divOfRatSec (hL 0) hr).mult z = 0
    · simp [hF, hm]
    obtain ⟨Z, i, _, _, G', j', s', hi, hpb', hγz⟩ := hγ z hm
    have hfz : f z ≠ genericPoint B := by
      intro h
      exact hz (hrange ▸ (show z ∈ f ⁻¹' {genericPoint B} from h))
    simp only [hF]
    rw [hγz, interNum_eq_zero_of_not_generic B Y f z hfz Z i hi G' j' s' hpb'
      (fun a : Fin e => (L a.succ).pull i) (fun a => LB.isLB_pull (hL a.succ) i), mul_zero]
  have hinj : Function.Injective j := j.isEmbedding.injective
  have hs : Function.support F ⊆ Set.range j := fun z hz => by
    by_contra h
    exact hz (hoff z h)
  have hre : ∑ᶠ w, F (j w) = ∑ᶠ z, F z := by
    rw [← finsum_mem_range hinj, ← finsum_mem_inter_support, Set.inter_eq_right.2 hs,
      finsum_mem_support]
  rw [← hre]
  rcases isEmpty_or_nonempty G with hG | hG
  · letI := algebraΓOfHom s
    rw [interNum_eq_zero_of_isZero _ (InterModel.isZero_of_isEmpty _)
      (fun a => LB.isLB_pull (hL a) j)]
    exact (finsum_of_isEmpty _).symm
  · obtain ⟨hGi, hη⟩ := hint hG
    letI := algebraΓOfHom s
    have hsproj : IsProjOver s :=
      GlobalTheory.T.generic_fibre_projective k B Y q p hq.isProjOver hp.isProjOver f hfq G j s hpb
    have hstr : strHom B.functionField G = s := strHom_eq fun _ => rfl
    haveI : AlgebraicGeometry.IsNoetherian G := isNoetherian_of_isProjOver hsproj
    haveI : IsProper q := CommonModel.isProper_of_isProjOver hq.isProjOver
    haveI : IsProper (f ≫ q) := by rw [hfq]; exact CommonModel.isProper_of_isProjOver hp.isProjOver
    haveI : IsProper f := IsProper.of_comp f q
    have hdim : topologicalKrullDim G ≤ ((e + 1 : ℕ) : WithBot ℕ∞) :=
      GlobalTheory.T.generic_fibre_dimension_le B Y (d + 1) (e + 1) hq.dim_eq
        (by rw [hp.dim_eq]; exact le_of_eq (congrArg _ (by omega))) f G j s hpb
    obtain ⟨r', hr', hmult⟩ := GlobalTheory.T.rational_section_divisor_pullback_generic G Y j hη hstalk (L 0) (hL 0) r hr
    have hcyc := GlobalTheory.T.rational_section_cycle_formula_projective B.functionField G (by rw [hstr]; exact hsproj) e hdim
      ((L 0).pull j) (LB.isLB_pull (hL 0) j) (fun a => (L a.succ).pull j)
      (fun a => LB.isLB_pull (hL a.succ) j) r' hr'
    have hcons : (Fin.cons ((L 0).pull j) (fun a : Fin e => (L a.succ).pull j) :
        Fin (e + 1) → LB G) = fun a => (L a).pull j := by
      funext a
      exact Fin.cases rfl (fun b => rfl) a
    rw [hcons] at hcyc
    rw [hcyc]
    congr 1
    funext w
    simp only [hF]
    rw [hmult w]
    by_cases hm : (divOfRatSec (hL 0) hr).mult (j w) = 0
    · simp [hm]
    obtain ⟨Z, i, _, _, G', j', s', hi, hpb', hγz⟩ := hγ (j w) hm
    rw [hγz, GlobalTheory.T.generic_fibre_closed_subvariety B Y f G j s hpb w Z i hi G' j' s' hpb' (Fin e) (fun a => L a.succ)
      (fun a => hL a.succ)]

end GlobalTheory.GenFibreDegree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedSquaredLengthUpperUnitriangularGramEqOfAgr
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

namespace GlobalTheory.FlagCell2

theorem upU_row_eq {s : ℕ} (y y' : Low s → ℂ) (i : Fin s)
    (h : ∀ j : Low s, j.1.2 ≤ i → y' j = y j) (a : Fin s) (ha : a ≤ i) (k : Fin s) :
    upU y' a k = upU y a k := by
  simp only [upU, Matrix.of_apply]
  split_ifs with hk
  · exact h ⟨(k, a), hk⟩ ha
  · rfl
  · rfl

theorem upU_gram_entry_eq {s : ℕ} (G : Matrix (Fin s) (Fin s) ℂ) (y y' : Low s → ℂ) (i : Fin s)
    (h : ∀ j : Low s, j.1.2 ≤ i → y' j = y j) (a c : Fin s) (ha : a ≤ i) (hc : c ≤ i) :
    (upU y' * G * (upU y')ᴴ) a c = (upU y * G * (upU y)ᴴ) a c := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, upU_row_eq y y' i h a ha,
    upU_row_eq y y' i h c hc]

theorem leadMinor_upU_gram_eq {s : ℕ} (G : Matrix (Fin s) (Fin s) ℂ) (y y' : Low s → ℂ) (i : Fin s)
    (h : ∀ j : Low s, j.1.2 ≤ i → y' j = y j) (j : ℕ) (hj : j ≤ (i : ℕ) + 1) :
    leadMinor (upU y' * G * (upU y')ᴴ) j = leadMinor (upU y * G * (upU y)ᴴ) j := by
  unfold leadMinor
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply]
  apply upU_gram_entry_eq G y y' i h
  · rw [Fin.le_def]; have := a.2; omega
  · rw [Fin.le_def]; have := b.2; omega

theorem grD_upU_gram_eq : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ) (y y' : Low s → ℂ) (i : Fin s), (∀ j : Low s, j.1.2 ≤ i → y' j = y j) → grD (upU y' * G * (upU y')ᴴ) i = grD (upU y * G * (upU y)ᴴ) i := by
  intro s G y y' i h
  unfold grD
  rw [leadMinor_upU_gram_eq G y y' i h _ (by simp), leadMinor_upU_gram_eq G y y' i h _ (by omega)]

end GlobalTheory.FlagCell2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorGradedLengthSmoothStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramLowerTriangularFactor_gradedLength_smooth : ∀ (n s : ℕ) (G : V n → Matrix (Fin s) (Fin s) ℂ) (v : V n), MContDiffAt ∞ G v → (G v).PosDef → MContDiffAt ∞ (fun x => ldPart (G x)) v ∧ ∀ i, ContDiffAt ℝ ∞ (fun x => grD (G x) i) v := by
  first | exact @GlobalTheory.ChernCalc.ldPart_grD_smooth | exact GlobalTheory.ChernCalc.ldPart_grD_smooth | (intros; apply GlobalTheory.ChernCalc.ldPart_grD_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorLowerTriangularConjStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramLowerTriangularFactor_lowerTriangular_conj : ∀ (s : ℕ) (G g : Matrix (Fin s) (Fin s) ℂ), G.PosDef → (∀ i j, i < j → g i j = 0) → IsUnit g.det → ldPart (g * G * gᴴ) = g * ldPart G * (Matrix.diagonal fun i => g i i)ᴴ ∧ ∀ i, grD (g * G * gᴴ) i = ‖g i i‖ ^ 2 * grD G i := by
  first | exact @GlobalTheory.ChernCalc.ldPart_conj_lower | exact GlobalTheory.ChernCalc.ldPart_conj_lower | (intros; apply GlobalTheory.ChernCalc.ldPart_conj_lower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorPosDefPropertiesStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramLowerTriangularFactor_posDef_properties : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ), G.PosDef → (∀ j, 0 < (leadMinor G j).re ∧ (leadMinor G j).im = 0) ∧ (∀ i, 0 < grD G i ∧ ldPart G i i = grD G i) ∧ (∀ i j, i < j → ldPart G i j = 0) ∧ IsUnit (ldPart G).det := by
  first | exact @GlobalTheory.ChernCalc.ldPart_posDef_spec | exact GlobalTheory.ChernCalc.ldPart_posDef_spec | (intros; apply GlobalTheory.ChernCalc.ldPart_posDef_spec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupInverseDescendsProperSurjection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem inv_pullback_left_fst {X Y : Scheme.{0}} (f : X ⟶ Y) (G' : Over Y) [GrpObj G'] {T : Over X}
    (z : T ⟶ (Over.pullback f).obj G') :
    (z⁻¹).left ≫ pullback.fst G'.hom f = z.left ≫ pullback.fst G'.hom f ≫ ι[G'].left := by
  show (z ≫ (Over.pullback f).map ι[G']).left ≫ _ = _
  rw [Over.comp_left, Category.assoc]
  congr 1
  simp only [Over.pullback_map_left]
  first | exact pullback.lift_fst _ _ _ | erw [pullback.lift_fst]

theorem exists_inv_descent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom → pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β → ∃ i : G ⟶ G, ∀ (T : Over S) (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → (x₀ ≫ i).left = x⁻¹.left ≫ β := by
  intro R _ _ _ _ S π hP hS hI G' _ G β hsm hpb φ hφ hc
  have hfl : Flat G.hom := inferInstance
  have D := fun (W : Scheme.{0}) => GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S G.left G'.left W π G.hom β G'.hom hP hS hI hfl hpb
  have epi : ∀ {W : Scheme.{0}} (a b : G.left ⟶ W), β ≫ a = β ≫ b → a = b := by
    intro W a b hab
    obtain ⟨h₀, -, hu⟩ := D W (β ≫ a) (by rw [pullback.condition_assoc])
    exact (hu a rfl).trans (hu b hab.symm).symm
  have hw : β ≫ G.hom = G'.hom ≫ π := hpb.w
  set a₁ := pullback.fst β β
  set a₂ := pullback.snd β β
  have hσ : (a₁ ≫ G'.hom) ≫ π = (a₂ ≫ G'.hom) ≫ π := by
    simp only [Category.assoc, ← hw]; rw [pullback.condition_assoc]
  let σ : pullback β β ⟶ pullback π π := pullback.lift _ _ hσ
  let x : Over.mk σ ⟶ (Over.pullback (pullback.fst π π)).obj G' :=
    Over.homMk (pullback.lift a₁ σ (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  have hcx : ∀ y : Over.mk σ ⟶ (Over.pullback (pullback.fst π π)).obj G',
      y.left ≫ pullback.fst G'.hom (pullback.fst π π) ≫ β =
        (y ≫ φ.hom).left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β := by
    intro y; rw [Over.comp_left, Category.assoc, ← hc]
  have h2 : (x ≫ φ.hom).left ≫ pullback.fst G'.hom (pullback.snd π π) = a₂ := by
    apply hpb.hom_ext
    · rw [Category.assoc, ← hcx x]
      show pullback.lift a₁ σ _ ≫ _ ≫ β = _
      rw [pullback.lift_fst_assoc]
      exact pullback.condition
    · rw [Category.assoc, pullback.condition, ← Category.assoc,
        show (x ≫ φ.hom).left ≫ pullback.snd G'.hom (pullback.snd π π) = σ from Over.w (x ≫ φ.hom)]
      exact pullback.lift_snd _ _ _
  have eq : a₁ ≫ ι[G'].left ≫ β = a₂ ≫ ι[G'].left ≫ β := by
    have := hcx x⁻¹
    rw [GrpObj.inv_comp, reassoc_of% inv_pullback_left_fst, reassoc_of% inv_pullback_left_fst,
      reassoc_of% h2] at this
    simp only [x, Over.homMk_left] at this
    rwa [pullback.lift_fst_assoc] at this
  obtain ⟨h₀, hh₀, -⟩ := D G.left (ι[G'].left ≫ β) eq
  have hover : h₀ ≫ G.hom = G.hom := by
    apply epi
    rw [reassoc_of% hh₀, hw, ← Category.assoc, Over.w ι[G']]
  refine ⟨Over.homMk h₀ hover, ?_⟩
  intro T x' x₀ hx
  rw [Over.comp_left]
  show x₀.left ≫ h₀ = _
  rw [hx, Category.assoc, hh₀]
  show _ = (x' ≫ ι[G']).left ≫ β
  rw [Over.comp_left, Category.assoc]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowersStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.group_object_lift_divided_powers : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R R₀ : Type) [CommRing R] [CommRing R₀]
    (I : Ideal R) (κ : DividedPowers I), IsNilDP κ → ∀ (π : R →+* R₀), Function.Surjective π → ∀ (hI : RingHom.ker π = I)
    (X₀ : Obj F 𝔠 (Sp R₀)) (A : Over (Sp R)) [GrpObj A] (i : X₀.A.left ⟶ A.left), IsGrpPullback X₀.A A (spMap π) i →
    IsAbelianScheme A → SmoothOfRelativeDimension (Module.finrank ℚ F) A.hom →
    ∀ (E : Submodule R (Crys κ (spMap π) X₀.A)), (∃ N : Submodule R (Crys κ (spMap π) X₀.A), IsCompl E N) →
      (∀ y : HdR X₀.A, y ∈ Fil X₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor κ hI X₀.A).Corr d y) →
      (∀ (a : 𝓞 F), ∀ d ∈ E, act κ (spMap π) X₀.rm a d ∈ E) →
      (∀ (c : 𝔠.elt) (φ : Crys κ (spMap π) X₀.A →ₗ[R] Crys κ (spMap π) X₀.A →ₗ[R] R),
        GlobalTheory.AbDual.IsCorrForm κ (spMap π) X₀.A X₀.A (X₀.P c) φ → ∀ a ∈ E, ∀ b ∈ E, φ a b = 0) →
      ∃ (X' : Obj F 𝔠 (Sp R)) (i' : X₀.A.left ⟶ X'.A.left) (pull : X₀.IsPullBy X' (spMap π) i'), liftFil κ pull.grp = E := by
  first | exact @GlobalTheory.RMDeform.exists_deform | exact GlobalTheory.RMDeform.exists_deform | (intros; apply GlobalTheory.RMDeform.exists_deform <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionOfBasicOpenCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_lie_condition_of_basicOpen_cover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (S : Scheme.{0})
  (A : Over S) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (R' : Type) [CommRing R'] (β : R →+* R')
  (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
  (∀ r ∈ t, LieAt b act ((algebraMap R' (Localization.Away r)).comp β) (spMap (algebraMap R' (Localization.Away r)) ≫ x)) →
  LieAt b act β x := by
  first | exact @GlobalTheory.UPel.HT.LieLoc.lieAt_of_cover | exact GlobalTheory.UPel.HT.LieLoc.lieAt_of_cover | (intros; apply GlobalTheory.UPel.HT.LieLoc.lieAt_of_cover; all_goals assumption)
end

