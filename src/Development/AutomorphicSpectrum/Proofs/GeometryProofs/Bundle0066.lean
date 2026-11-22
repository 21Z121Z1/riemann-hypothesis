import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BirationalLatticeHeightFormula
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0060
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DedekindConstantsDegreeOne
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0061
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyCoordIdeal
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.ConstClosure

section Chart

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω}

theorem exists_chart_div (h : CoordTie ℤ ξ x) :
    ∃ c, x c ≠ 0 ∧ ∀ ω : Ω, ∃ a b : Ω, a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) ∧
      b ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) ∧ b ≠ 0 ∧ ω = a / b := by
  let η : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  obtain ⟨c, hc⟩ := h.cover η
  refine ⟨c, hc.1, fun ω => ?_⟩
  obtain ⟨U, hU, hmem⟩ := h.affine c hc.1
  have hη : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, hc⟩
  have key : ∀ r : Γ(X, U), (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη r) ∈
      Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
    intro r
    refine (h.ring c hc.1 _).2 fun p hp => ?_
    have hpU : p.1 ∈ U := (hmem p.1).2 ⟨p.2, hp⟩
    exact ⟨X.presheaf.germ U p.1 hpU r, genMap_germ_eq_stalk_closed ξ p U hpU hη r⟩
  obtain ⟨b, rfl⟩ : ∃ b : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom b = ω := h.gen.bij.2 ω
  obtain ⟨r, t, hrt, hunit⟩ := stalk_eq_germ_div_of_affine hU ⟨genPt ξ, hη⟩ b
  replace hrt : b * X.presheaf.germ U (genPt ξ) hη t = X.presheaf.germ U (genPt ξ) hη r := hrt
  replace hunit : IsUnit (X.presheaf.germ U (genPt ξ) hη t) := hunit
  have hne : (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη t) ≠ 0 :=
    (hunit.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  refine ⟨_, _, key r, key t, hne, ?_⟩
  rw [eq_div_iff hne]
  exact ((Scheme.stalkClosedPointTo ξ).hom.map_mul _ _).symm.trans
    (congrArg (Scheme.stalkClosedPointTo ξ).hom hrt)

theorem adjoin_le_subfield (F : Subfield Ω) {c : κ} (h : ∀ j, x j / x c ∈ F) {a : Ω}
    (ha : a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c)) : a ∈ F := by
  induction ha using Algebra.adjoin_induction with
  | mem t ht => obtain ⟨j, rfl⟩ := ht; exact h j
  | algebraMap n => simpa using intCast_mem F n
  | add s t _ _ hs ht => exact add_mem hs ht
  | mul s t _ _ hs ht => exact mul_mem hs ht

theorem subfield_eq_top {c : κ} (hc : ∀ ω : Ω, ∃ a b : Ω, a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) ∧
      b ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) ∧ b ≠ 0 ∧ ω = a / b)
    (F : Subfield Ω) (h : ∀ j, x j / x c ∈ F) : F = ⊤ := by
  refine eq_top_iff.2 fun ω _ => ?_
  obtain ⟨a, b, ha, hb, -, rfl⟩ := hc ω
  exact div_mem (adjoin_le_subfield F h ha) (adjoin_le_subfield F h hb)

end Chart

section Field

variable {Ω : Type} [Field Ω]

theorem charZero_of_isArithVar {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
    {y : (Σ k, J k) → Ω} {n : ℕ} (h : IsArithVar (mCoordIdeal y) n) : CharZero Ω := by
  obtain ⟨-, -, hH, -⟩ := h
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing J) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker]
    have e : mConeMap y (C (n : ℤ)) = C (n : Ω) := by
      simp [mConeMap, aeval_C]
    rw [e, hn, map_zero]
  rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing J) = ⊥ from hH] at hmem
  simpa using hmem

theorem dedekind_finite_of_finite [CharZero Ω] (hf : FiniteDimensional ℚ (algebraicClosure ℚ Ω))
    (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] :
    IsDedekindDomain A ∧ Module.Finite ℤ A := by
  let L := algebraicClosure ℚ Ω
  have hmem : ∀ a : A, algebraMap A Ω a ∈ L := fun a =>
    mem_algebraicClosure_iff'.2 ((IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ)).2 ⟨a, rfl⟩).tower_top
  letI : Algebra A L := ((algebraMap A Ω).codRestrict L.toSubalgebra.toSubring hmem).toAlgebra
  have hcoe : ∀ a : A, ((algebraMap A L a : L) : Ω) = algebraMap A Ω a := fun _ => rfl
  haveI : IsScalarTower ℤ A L := inferInstance
  haveI : NumberField L := ⟨⟩
  haveI : IsIntegralClosure A ℤ L := by
    refine ⟨fun a b hab => IsIntegralClosure.algebraMap_injective A ℤ Ω ?_, fun {v} => ?_⟩
    · rw [← hcoe, ← hcoe, hab]
    · rw [← isIntegral_algebraMap_iff (A := L) (B := Ω) (R := ℤ) (algebraMap L Ω).injective]
      rw [IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := Ω)]
      constructor
      · rintro ⟨a, ha⟩
        exact ⟨a, Subtype.ext ha⟩
      · rintro ⟨a, rfl⟩
        exact ⟨a, rfl⟩
  haveI : IsDomain A := (IsIntegralClosure.algebraMap_injective A ℤ Ω).isDomain _
  exact ⟨IsIntegralClosure.isDedekindDomain ℤ ℚ L A, IsIntegralClosure.finite ℤ ℚ L A⟩

end Field

section Local

variable {Ω : Type} [Field Ω]

theorem isIntegrallyClosedIn_of_atPrime (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω]
    (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω]
    [IsScalarTower A O Ω] : IsIntegrallyClosedIn O Ω := by
  have hA := IsIntegralClosure.algebraMap_injective A ℤ Ω
  have hs : ∀ s : m.primeCompl, algebraMap A Ω s ≠ 0 := fun s h0 =>
    s.2 (by rw [hA (h0.trans (map_zero _).symm)]; exact m.zero_mem)
  refine isIntegrallyClosedIn_iff.2 ⟨?_, fun {w} hw => ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun o ho => ?_
    obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj m.primeCompl o
    have e' := congrArg (algebraMap O Ω) e
    simp only [map_mul, ho, zero_mul, ← IsScalarTower.algebraMap_apply] at e'
    have ha : a = 0 := hA (e'.symm.trans (map_zero _).symm)
    rw [ha, map_zero] at e
    exact (IsLocalization.map_units O s).mul_left_eq_zero.1 e
  · obtain ⟨s, hsw⟩ := IsIntegral.exists_multiple_integral_of_isLocalization m.primeCompl w hw
    haveI : Algebra.IsIntegral ℤ A := IsIntegralClosure.isIntegral_algebra ℤ Ω
    have hz : IsIntegral ℤ (s • w) := isIntegral_trans _ hsw
    obtain ⟨a, ha⟩ := (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ)).1 hz
    refine ⟨IsLocalization.mk' O a s, ?_⟩
    have h1 : algebraMap O Ω (IsLocalization.mk' O a s) * algebraMap A Ω s = algebraMap A Ω a := by
      rw [IsScalarTower.algebraMap_apply A O Ω s, ← map_mul, IsLocalization.mk'_spec,
        ← IsScalarTower.algebraMap_apply]
    have h2 : algebraMap A Ω a = algebraMap A Ω s * w := by
      rw [ha, Submonoid.smul_def, Algebra.smul_def]
    exact mul_right_cancel₀ (hs s) (by rw [h1, h2, mul_comm])

end Local

theorem const_closure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω], IsDedekindDomain A ∧ Module.Finite ℤ A ∧ Function.Injective (algebraMap A Ω) ∧ HasConstants ℤ A y ∧ ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], IsIntegrallyClosedIn O Ω ∧ fnField O y = ⊤ := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV A _ _ _
  classical
  haveI : CharZero Ω := charZero_of_isArithVar hV
  obtain ⟨c₀, -, hdiv⟩ := exists_chart_div 𝔐.tie
  have hfin : FiniteDimensional ℚ (algebraicClosure ℚ Ω) := by
    refine GroundTheory.Heights₂.Heights.Inter.RelAlgClosureFinite.proof ℚ Ω
      (Finset.univ.image fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c₀ k⟩) ?_
    have htop := subfield_eq_top hdiv (IntermediateField.adjoin ℚ
      ((Finset.univ.image fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c₀ k⟩ : Finset Ω) : Set Ω)).toSubfield
      fun j => IntermediateField.subset_adjoin _ _ (by simp)
    refine eq_top_iff.2 fun ω _ => ?_
    have hω : ω ∈ (⊤ : Subfield Ω) := Subfield.mem_top ω
    rw [← htop] at hω
    exact hω
  have hconst : HasConstants ℤ A y := fun c' hc' a =>
    (𝔐.tie.ring c' hc' _).2 fun p _ =>
      IntReg.mem_regAt_of_isIntegral_of_stalk _ _ _ _ 𝔐.tie.gen (𝔐.normal p.1).2 _
        ((IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ)).2 ⟨a, rfl⟩)
  obtain ⟨hd, hfA⟩ := dedekind_finite_of_finite hfin A
  refine ⟨hd, hfA, IsIntegralClosure.algebraMap_injective A ℤ Ω, hconst, ?_⟩
  intro m _ O _ _ _ _ _ _ _
  refine ⟨isIntegrallyClosedIn_of_atPrime A m O, subfield_eq_top hdiv _ fun j => ?_⟩
  show (∏ k, y ⟨k, j k⟩) / (∏ k, y ⟨k, c₀ k⟩) ∈ fnField O y
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun k _ => Subfield.subset_closure (Or.inr ⟨⟨k, j k, c₀ k⟩, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Num.ConstClosure
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BirationalLatticeHeightFormulaStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.birational_lattice_height_formula : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (e₀ : E) (c₀ : Ω) (A : HermLine ι) (r : HeightOneSpectrum (𝓞 F) →₀ ℚ) (cinf : (F →+* ℂ) → ℝ), OverInt y φ → Birational y → IsConjInvariantH A → CoordTie ℤ ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) → NormalCpt ξ → L.IsDegOn Set.univ y A.a e₀ → c₀ ≠ 0 → (∀ p : Cpt ξ, ((∀ a : F, φ a ∈ regAt ξ p) ∧ OrderAt L (c₀ • e₀) 1 1 0 p) ∨ ∃ (v : HeightOneSpectrum (𝓞 F)) (π : F) (m : ℕ) (n : ℤ), (∀ a : F, v.valuation F a ≤ 1 → φ a ∈ regAt ξ p) ∧ v.valuation F π = WithZero.exp (-1 : ℤ) ∧ 0 < m ∧ (n : ℚ) = m * r v ∧ OrderAt L (c₀ • e₀) (φ π) m n p) → (∀ σ, 0 < cinf σ) → (∀ (σ : F →+* ℂ) z (g h : MRing ι) (dg dh : K → ℕ), PtOver y φ σ z → IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h → ‖evC z g‖ = cinf σ * A.h z * ‖evC z h‖) → ∃ S : FlatHerm y φ A, S.ht = ((r.sum fun v q => (q : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) - ∑ σ : F →+* ℂ, Real.log (cinf σ)) / (Module.finrank ℚ F : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_flatHerm_of_adelic | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_flatHerm_of_adelic | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_flatHerm_of_adelic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartBundleFinitelyGeneratedStatement
section
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_bundle_finitely_generated : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (B : ChartBundle O x r (Fin r → Ω)) (c : ι), x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ B.lat c) ∧
      ∀ e ∈ B.lat c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Geo.chartBundle_lat_fg | exact GlobalTheory.CompanionTheory.Ar.Geo.chartBundle_lat_fg | (intros; apply GlobalTheory.CompanionTheory.Ar.Geo.chartBundle_lat_fg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartRingMemAfterMonomialScalingStatement
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_ring_mem_after_monomial_scaling : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (s t : ∀ k, J k), mseg y s ≠ 0 → mseg y t ≠ 0 → ∀ a ∈ chartRing o (mseg y) s, ∃ n : ℕ, (mseg y s / mseg y t) ^ n * a ∈ chartRing o (mseg y) t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.ChartOverlap.pow_mul_mem_chartRing_mseg | exact GlobalTheory.CompanionTheory.Ar.HT.ChartOverlap.pow_mul_mem_chartRing_mseg | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.ChartOverlap.pow_mul_mem_chartRing_mseg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeHostAutPermutationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_host_aut_permutation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (g : HostAut H), ∃ π : CMType H ≃ CMType H, (∀ τ, (π τ).1 = τ.1.comp g.σ.toRingHom) ∧ ∀ s, labelEmb c (Sum.map π π s) = (labelEmb c s).comp g.s.toRingHom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Label.automorphism_permutes_labels | exact GlobalTheory.CompanionTheory.Ar.Label.automorphism_permutes_labels | (intros; apply GlobalTheory.CompanionTheory.Ar.Label.automorphism_permutes_labels <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoherentLatticeChartSpanStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coherent_lattice_chart_span : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E), L.IsCohOn Set.univ → ∃ (d n : ℕ) (z : Fin n → E), ∀ c (p : Cpt M.ξ), InChart M.ξ x c p → L p = Submodule.span (regAt M.ξ p) (Set.range fun k => (x c ^ d)⁻¹ • z k) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lat_twist_globally_generated | exact GlobalTheory.CompanionTheory.Ar.lat_twist_globally_generated | (intros; apply GlobalTheory.CompanionTheory.Ar.lat_twist_globally_generated <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpElementDividesPrimeSqStatement
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cp_element_divides_prime_sq : ∀ (A Ω : Type) [CommRing A] [IsDomain A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] [IsIntegrallyClosed A] [CharZero Ω] (p : ℕ) [Fact p.Prime] (κ : A), IsCp p (algebraMap A Ω κ) → κ ∣ (p : A) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.KappaDvd.kappa_dvd_sq | exact GlobalTheory.CompanionTheory.Ar.HT.KappaDvd.kappa_dvd_sq | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.KappaDvd.kappa_dvd_sq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DedekindConstantsDegreeOneStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dedekind_constants_degree_one : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ d : ℕ, IsArithVar (mCoordIdeal y) (d + 1) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], Function.Injective (algebraMap A Ω) → HasConstants ℤ A y → ∀ (p : ℕ), p.Prime → ∀ (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (E : Type) [AddCommGroup E] [Module Ω E] (r : ℕ) (w : Module.Basis (Fin r) Ω E) (L : Lat ξ E), L.IsFlagVBOn (overPrime ξ p) w → ∃ B : ChartBundle O (segreVec y) r E, (∀ c, segreVec y c ≠ 0 → ∀ v, v ∈ B.lat c ↔ ∀ q : Cpt ξ, InChart ξ (segreVec y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → v ∈ L q) ∧ ∀ (x : Fin r → K → ℤ) (e : Fin r → Ω) (he : ∀ i, e i ≠ 0), (∀ i, (L.gr w i).IsDegOn (overPrime ξ p) y (x i) (e i)) → IsFlagFrame y B (w.unitsSMul fun i => Units.mk0 (e i) (he i)) x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LatChart.exists_chartBundle_of_isFlagVBOn | exact GlobalTheory.CompanionTheory.Ar.Num.LatChart.exists_chartBundle_of_isFlagVBOn | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LatChart.exists_chartBundle_of_isFlagVBOn <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DegreeLatticesPrimeCompareStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_lattices_prime_compare : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ d : ℕ, IsArithVar (mCoordIdeal y) (d + 1) → ∀ (L L' : Lat ξ Ω) (a a' : K → ℤ) (e e' : Ω), L.IsDegOn Set.univ y a e → L'.IsDegOn Set.univ y a' e' → ∀ S : Finset Nat.Primes, (∀ q : Cpt ξ, (∀ p ∈ S, ¬ InFibre ξ p q) → L q = L' q) → ∃ f g : MvPolynomial (Σ k, J k) ℤ, (⟨fun _ => a, fun _ => a', fun _ => f, fun _ => g⟩ : LocPair J ℤ Unit).IsVertOff (mCoordIdeal y) S ∧ aeval y f = e' / e * aeval y g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.lat_vertOff | exact GlobalTheory.CompanionTheory.Ar.Num.lat_vertOff | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.lat_vertOff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DivSuppArithHolds
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem divSuppArith_holds : ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement :=
  ReciprocityTheory.ChartRestriction.G.Geo.divSuppArith

end GlobalTheory.CompanionTheory.Ar.Link
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceFieldExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenspace_field_extension : ∀ (F : Type) [Field F] [NumberField F] (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (ρ : 𝓞 F →+* Module.End Ω V) (ρ' : 𝓞 F →+* Module.End Ω' V') (σ : 𝓞 F →+* Ω), IsExtOver i j → Submodule.span Ω' (Set.range j) = ⊤ → (∀ a e, ρ' a (j e) = j (ρ a e)) → eigSp ρ' (i.comp σ) = Submodule.span Ω' (j '' (eigSp ρ σ : Set V)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EigExt.eigSp_ext | exact GlobalTheory.CompanionTheory.Ar.EigExt.eigSp_ext | (intros; apply GlobalTheory.CompanionTheory.Ar.EigExt.eigSp_ext <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenvectorComplexPoint
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FramesEig

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open LieTangent

section Germ

variable {X : Scheme.{0}} {O : Type} [CommRing O]

def germ (s : X ⟶ Sp O) (p : X) : O →+* X.presheaf.stalk p :=
  (Spec.preimage (X.fromSpecStalk p ≫ s)).hom

theorem spec_germ (s : X ⟶ Sp O) (p : X) :
    Spec.map (CommRingCat.ofHom (germ s p)) = X.fromSpecStalk p ≫ s := by
  simp only [germ, CommRingCat.ofHom_hom, Spec.map_preimage]

theorem map_germ (s : X ⟶ Sp O) (p : X) {K : Type} [CommRing K] (φ : X.presheaf.stalk p →+* K) (i : O →+* K)
    (h : Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p ≫ s = spMap i) (n : O) :
    φ (germ s p n) = i n := by
  have h3 : Spec.map (CommRingCat.ofHom (φ.comp (germ s p))) = Spec.map (CommRingCat.ofHom i) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, spec_germ]
    exact h
  have h4 := Spec.map_injective h3
  exact congrArg (fun g => g.hom n) h4

end Germ

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {V : Type} [AddCommGroup V] [Module Ω V]

theorem valAt_comp (M : LieModel G ξ V) {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ X} (f : G ⟶ G) [IsMonHom f] {e e' : V} (he : M.pt e' = M.pt e ≫ f)
    {w : epsAt z ⟶ G} (h : M.ValAt z e w) : M.ValAt z e' (w ≫ f) := by
  rw [LieModel.valAt_iff] at *
  obtain ⟨h1, v, hv, rfl⟩ := h
  refine ⟨h1, v ≫ f, ?_, by rw [Category.assoc]⟩
  rw [LieModel.extends_iff] at *
  refine ⟨?_, by rw [he, hv.2, Category.assoc]⟩
  have := (isTanAt_iff v).1 hv.1
  rw [isTanAt_iff, ← Category.assoc, this, one_comp]

end Val

theorem mem_eigSp_of_valAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (σ : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) (EC : Type) [AddCommGroup EC] [Module ℂ EC] (N : LieModel Y.t.G (y ≫ Y.j) EC) (ρ : 𝓞 E →+* Module.End ℂ EC) (t : 𝓞 E →+* c.F) (e : Z.V) (w : EC), (∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → y ≫ pullback.snd _ _ = spMap σ → N.IsActOf Y.t.act.act ρ → e ∈ eigSp Z.ρ (Z.inc.comp t) → Z.M.ValAt (y ≫ Y.j) e (N.pt w) → w ∈ eigSp ρ (σ.comp t) := by
  intro E _ _ _ H D l Xo c O _ β Y U Z σ y EC _ _ N ρ t e w hfr hy hN he hv
  have mem : ∀ {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (r : 𝓞 E →+* Module.End R V)
      (τ : 𝓞 E →+* R) (u : V), u ∈ eigSp r τ ↔ ∀ a, r a u = τ a • u := by
    intro R V _ _ _ r τ u
    simp [eigSp, Submodule.mem_iInf, sub_eq_zero]
  rw [mem] at he ⊢
  have h1 : Y.j ≫ Y.s = pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ spMap β := by
    show (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  have hh := hv
  rw [LieModel.valAt_iff] at hh
  obtain ⟨h0, -⟩ := hh
  have hgen : ∀ n, genMap (Z.ξ₀ ≫ Y.j) ⟨centre (y ≫ Y.j), h0⟩ (germ Y.s (centre (y ≫ Y.j)) n) = Z.inc (β n) := by
    intro n
    refine map_germ Y.s _ _ (Z.inc.comp β) ?_ n
    rw [← Category.assoc, spec_genMap, Category.assoc, h1, ← Category.assoc, Z.over_inc]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hcl : ∀ n, (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom (germ Y.s (centre (y ≫ Y.j)) n) = σ (β n) := by
    intro n
    refine map_germ Y.s _ _ (σ.comp β) ?_ n
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Y.s) (spec_centre (y ≫ Y.j))).trans ?_)
    change (y ≫ Y.j) ≫ Y.s = _
    rw [Category.assoc, h1, ← Category.assoc, hy]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  intro a
  obtain ⟨n, d, hd, hnd⟩ := hfr (t a)
  have hva : Z.M.ValAt (y ≫ Y.j) (Z.ρ a e) (N.pt (ρ a w)) := by
    have := Y.t.act.hom a
    rw [hN a w]
    exact valAt_comp Z.M (Y.t.act.act a) (Z.act a e) hv
  have v1 := hva.smul h0 (germ Y.s (centre (y ≫ Y.j)) d)
  have v2 := hv.smul h0 (germ Y.s (centre (y ≫ Y.j)) n)
  rw [hgen, hcl, ← LieModel.pt_smul] at v1 v2
  have e1 : Z.inc (β d) • Z.ρ a e = Z.inc (β n) • e := by
    rw [he a, smul_smul, ← hnd]
    simp [mul_comm]
  rw [e1] at v1
  have e2 := N.inj (v1.unique Z.gen v2)
  rw [← hnd, map_mul, mul_comm, mul_smul] at e2
  have hσ : σ (β d) ≠ 0 := (map_ne_zero σ).2 hd
  exact smul_right_injective EC hσ e2

end GlobalTheory.CompanionTheory.Ar.FramesEig
end
end

