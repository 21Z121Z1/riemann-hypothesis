import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0513
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2527
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2528
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2529
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2483
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2525
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2404
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2530
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureModuliFibreOfMonomialPeriodPreChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FibreDense

theorem isPrime_map_of_flat {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (φ : A →+* R) (hf : φ.Flat) (hm : (maximalIdeal A).map φ = maximalIdeal R) (I : Ideal A)
    [IsRegularLocalRing (A ⧸ I)] : (I.map φ).IsPrime := by
  let _ := φ.toAlgebra
  have : Module.Flat A R := hf
  have hI : I ≤ maximalIdeal A := le_maximalIdeal (Ideal.Quotient.nontrivial_iff.1 inferInstance)
  have hJ : I.map (algebraMap A R) ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h.ge.trans ((Ideal.map_mono hI).trans hm.le)))
  have : Nontrivial (R ⧸ I.map (algebraMap A R)) := Ideal.Quotient.nontrivial_iff.2 hJ
  have : IsLocalRing (R ⧸ I.map (algebraMap A R)) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have : Module.Flat (A ⧸ I) (R ⧸ I.map (algebraMap A R)) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor R I).toLinearEquiv
  have hmap : (maximalIdeal (A ⧸ I)).map (algebraMap (A ⧸ I) (R ⧸ I.map (algebraMap A R))) = maximalIdeal _ := by
    rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
      ← map_maximalIdeal_of_surjective (Ideal.Quotient.mk (I.map (algebraMap A R))) Ideal.Quotient.mk_surjective,
      ← hm, Ideal.map_map, Ideal.map_map]
    rfl
  have : IsLocalHom (algebraMap (A ⧸ I) (R ⧸ I.map (algebraMap A R))) :=
    ((local_hom_TFAE _).out 0 2).2 hmap.le
  have := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.of_flat_of_map_maximalIdeal hmap
  have : IsDomain (R ⧸ I.map (algebraMap A R)) := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain
  exact (Ideal.Quotient.isDomain_iff_prime _).1 this

theorem exists_toStalk (o : Type) [CommRing o] (x : Sp o) : ∃ τ : CommRingCat.of o ⟶ (Sp o).presheaf.stalk x,
    (Sp o).fromSpecStalk x = Spec.map τ ∧ x.asIdeal.map τ.hom = maximalIdeal ((Sp o).presheaf.stalk x) := by
  have := x.isPrime
  let _ : Algebra o ((Spec (CommRingCat.of o)).presheaf.stalk x) := (StructureSheaf.toStalk o x).hom.toAlgebra
  have : IsLocalization.AtPrime ((Spec (CommRingCat.of o)).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk o x
  exact ⟨StructureSheaf.toStalk o x, Spec.fromSpecStalk_eq' (CommRingCat.of o) x,
    IsLocalization.AtPrime.map_eq_maximalIdeal x.asIdeal ((Spec (CommRingCat.of o)).presheaf.stalk x)⟩

theorem isPrime_fibre {o : Type} [CommRing o] {S : Scheme.{0}} (s : S ⟶ Sp o) [Smooth s] {R : Type} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (b : o →+* R) (ξ : Sp R ⟶ S) (hb : ξ ≫ s = spMap b)
    (he : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom) : (((maximalIdeal R).comap b).map b).IsPrime := by
  have hreg := GlobalTheory.FibreRegular.isRegularLocalRing_stalk_quot_maximalIdeal _ _ s (ξ (closedPoint R))
  have hp := isPrime_map_of_flat _ he.1 he.2.1
    ((maximalIdeal ((Sp o).presheaf.stalk (s (ξ (closedPoint R))))).map (s.stalkMap (ξ (closedPoint R))).hom)
  obtain ⟨τ, hτ, hmax⟩ := exists_toStalk o (s (ξ (closedPoint R)))
  have hc : τ ≫ s.stalkMap (ξ (closedPoint R)) ≫ Scheme.stalkClosedPointTo ξ = CommRingCat.ofHom b := by
    apply Spec.map_injective
    refine Eq.trans ?_ hb
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, ← hτ, Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc]
    exact congrArg (· ≫ s) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of R) ξ)
  have hx : (s (ξ (closedPoint R))).asIdeal = (maximalIdeal R).comap b :=
    congrArg (fun f : Sp R ⟶ Sp o => (f (closedPoint R)).asIdeal) hb
  have hb' : (Scheme.stalkClosedPointTo ξ).hom.comp ((s.stalkMap (ξ (closedPoint R))).hom.comp τ.hom) = b :=
    congrArg (fun q => q.hom) hc
  rwa [← hmax, Ideal.map_map, Ideal.map_map, RingHom.comp_assoc, hb', hx] at hp

theorem mem_closure_fibre : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o) (j : F.X ⟶ S) [IsOpenImmersion j] (φ : InvFun ℤ) (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S) [IsNoetherianRing o] [Smooth s], PreChart F s j φ BD d x → x ∈ closure (Set.range j ∩ s ⁻¹' {s x}) := by
  intro o _ ζ g n F S s j _ φ BD d x _ _ h
  obtain ⟨R, _, _, _, b, ξ, m, t, Q, δ, a, G₁, _, y, α₁, ⟨-, -, hb, rfl, he, -⟩, ⟨ht, -, hj⟩, -⟩ := h
  have hq := isPrime_fibre s b ξ hb he
  let q : Sp R := (⟨((maximalIdeal R).comap b).map b, hq⟩ : PrimeSpectrum R)
  have hs : ∀ p : Sp R, s (ξ p) = spMap b p := fun p => congrArg (fun f : Sp R ⟶ Sp o => f p) hb
  have h₁ : ξ q ∈ Set.range j := by
    refine (hj q).2 fun hmem => ?_
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hq)).1 hmem
    have := ht.2 (Pi.single i 1) (Ideal.mem_sup_right (by simpa [Pi.single_apply] using hi)) i
    simp at this
  have h₂ : s (ξ q) = s (ξ (closedPoint R)) := by
    refine (hs q).trans (Eq.trans (PrimeSpectrum.ext (le_antisymm ?_ ?_)) (hs (closedPoint R)).symm)
    · exact Ideal.comap_mono (f := b) (Ideal.map_comap_le (f := b) (K := maximalIdeal R))
    · exact Ideal.le_comap_map (f := b) (I := (maximalIdeal R).comap b)
  have h₃ : ξ q ⤳ ξ (closedPoint R) := (specializes_closedPoint (R := R) q).map ξ.continuous
  exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_inter h₁ h₂)) (specializes_iff_mem_closure.1 h₃)

end GlobalTheory.FibreDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeAppTopOfFibreSquareProjectionsEqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_range_appTop_of_fibreSquare_projections_eq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → IsIntegral S → Function.Injective π.appTop.hom → ∀ x : Γ(S, ⊤), (pullback.fst π π).appTop.hom x = (pullback.snd π π).appTop.hom x → x ∈ Set.range π.appTop.hom := by
  first | exact @GlobalTheory.Mum.mem_range_appTop_of_fst_eq_snd | exact GlobalTheory.Mum.mem_range_appTop_of_fst_eq_snd | (intros; apply GlobalTheory.Mum.mem_range_appTop_of_fst_eq_snd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanSupPowOfForallCompleteDvrLocalTest
section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem dvd_of_forall_mem_span_sup_pow {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {x y : V} (hx : x ≠ 0) (h : ∀ e, y ∈ Ideal.span {x} ⊔ maximalIdeal V ^ e) : x ∣ y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx hϖ
  have hs : Ideal.span {x} = maximalIdeal V ^ k := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
    exact Ideal.span_singleton_eq_span_singleton.mpr hk
  have := h k
  rw [← hs, sup_idem] at this
  exact Ideal.mem_span_singleton.mp this

theorem mem_span_sup_pow_of_forall_complete_dvr : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O] [CharZero O] [Algebra.EssFiniteType ℤ O] (g : O) (b : ℕ → O), g ≠ 0 → (∀ m n, m ≤ n → b m - b n ∈ maximalIdeal O ^ m) → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ ρ : O →+* V, Function.Injective ρ → IsLocalHom ρ → ∀ e, ρ (b e) ∈ Ideal.span {ρ g} ⊔ maximalIdeal V ^ e) → ∀ n, b n ∈ Ideal.span {g} ⊔ maximalIdeal O ^ n := by
  intro O _ _ _ _ _ _ g b hg hb hV n
  haveI : IsNoetherianRing O := Algebra.EssFiniteType.isNoetherianRing ℤ O
  set m := maximalIdeal O with hm
  let R := AdicCompletion m O
  let ι : O →+* R := algebraMap O R
  haveI : IsNoetherianRing R := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion O m
  obtain ⟨hdom, hic⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed O
  have fg : m.FG := m.fg_of_isNoetherianRing
  haveI : Module.Flat O R := AdicCompletion.flat_of_isNoetherian m
  haveI : IsLocalHom (algebraMap O R) := AdicCompletion.algebraMap_isLocalHom_of_fg fg
  haveI : Module.FaithfullyFlat O R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective ι := FaithfulSMul.algebraMap_injective O R
  haveI : CharZero R := charZero_of_injective_ringHom hinj
  have hmR : maximalIdeal R = m.map ι := AdicCompletion.maximalIdeal_eq_map

  have hc : IsAdicComplete (m.map ι) R := AdicCompletion.isAdicComplete_self m fg
  obtain ⟨F, hF⟩ := IsPrecomplete.prec hc.toIsPrecomplete (f := fun k => ι (b k)) (by
    intro k l hkl
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← map_sub, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (hb k l hkl))
  have hF' : ∀ k, ι (b k) - F ∈ maximalIdeal R ^ k := by
    intro k
    have := hF k
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← hmR] at this

  have hgR : ι g ≠ 0 := fun h => hg (hinj (by rw [h, map_zero]))
  have hdvd : ι g ∣ F := by
    refine GlobalTheory.T.dvd_of_forall_complete_dvr_dominating R F (ι g) hgR ?_
    intro V _ _ _ hVc ρ' hρ' _
    let ρ : O →+* V := ρ'.comp ι
    have hρ : Function.Injective ρ := hρ'.comp hinj
    haveI : IsLocalHom ρ := inferInstance
    haveI : CharZero V := charZero_of_injective_ringHom hρ
    have hgV : ρ' (ι g) ≠ 0 := fun h => hgR (hρ' (by rw [h, map_zero]))
    refine dvd_of_forall_mem_span_sup_pow hgV fun e => ?_
    have h1 : ρ (b e) ∈ Ideal.span {ρ g} ⊔ maximalIdeal V ^ e := hV V hVc ρ hρ inferInstance e
    have hmap : ∀ x ∈ maximalIdeal R, ρ' x ∈ maximalIdeal V := by
      intro x hx
      rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
      exact fun h => hx (isUnit_of_map_unit ρ' x h)
    have h2 : ρ' (ι (b e) - F) ∈ maximalIdeal V ^ e := by
      have hle : (maximalIdeal R ^ e).map ρ' ≤ maximalIdeal V ^ e := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hmap) e
      exact hle (Ideal.mem_map_of_mem _ (hF' e))
    have : ρ' F = ρ (b e) - ρ' (ι (b e) - F) := by
      simp [ρ, map_sub]
    rw [this]
    exact Ideal.sub_mem _ h1 (Ideal.mem_sup_right h2)

  have hmem : ι (b n) ∈ (Ideal.span {g} ⊔ m ^ n).map ι := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_pow, ← hmR]
    have h3 : F ∈ Ideal.span {ι g} := Ideal.mem_span_singleton.mpr hdvd
    have : ι (b n) = F + (ι (b n) - F) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left h3) (Ideal.mem_sup_right (hF' n))
  rwa [← Ideal.mem_comap, Ideal.comap_map_eq_self_of_faithfullyFlat] at hmem

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimalPolynomialLinearFactorSplitStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_polynomial_linear_factor_split : ∀ (E : Type) [Field E] [NumberField E] (b : E) (σ : E →+* ℂ), ∃ (Q : Polynomial Qb) (c : ℂ),
    (Polynomial.X - Polynomial.C (σ b)) * Q.map (algebraMap Qb ℂ) = Polynomial.C c * (minpoly ℚ b).map (algebraMap ℚ ℂ) ∧
    (Q.map (algebraMap Qb ℂ)).eval (σ b) = 1 := by
  first | exact @GlobalTheory.EigProj.eigProj_poly | exact GlobalTheory.EigProj.eigProj_poly | (intros; apply GlobalTheory.EigProj.eigProj_poly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelAffinePointEqOfInverseMemIffStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_affine_point_eq_of_inverse_mem_iff : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → ∀ z z' : M.Z, z ∈ U → z' ∈ U → (∀ a ∈ M.ringOn (U : Set M.Z), a ≠ 0 → (a⁻¹ ∈ M.O z ↔ a⁻¹ ∈ M.O z')) → z = z' := by
  first | exact @GlobalTheory.Points.point_eq_of_inv_mem_iff | exact GlobalTheory.Points.point_eq_of_inv_mem_iff | (intros; apply GlobalTheory.Points.point_eq_of_inv_mem_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelStatementOfFrameGaloisStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_statement_of_frame_galois : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.ChebotarevDegreeOne → SmallSt → FrameSt → GlobalTheory.ExpTie.GalSt → ModelSt := by
  first | exact @GlobalTheory.ExpModel.modelSt_of_frames | exact GlobalTheory.ExpModel.modelSt_of_frames | (intros; apply GlobalTheory.ExpModel.modelSt_of_frames <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelWeightGapL1CardBound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.ModelWtGap

def colRot (p q : ℕ) (a : Fin (p + q)) : Fin (p + q) :=
  if h : (a : ℕ) < q then ⟨p + a, by omega⟩ else ⟨a - q, by omega⟩

theorem colRot_val (p q : ℕ) (a : Fin (p + q)) :
    (colRot p q a : ℕ) = if (a : ℕ) < q then p + a else a - q := by
  unfold colRot
  split_ifs <;> rfl

theorem colRot_bijective (p q : ℕ) : Function.Bijective (colRot p q) := by
  refine Finite.injective_iff_bijective.1 fun a b h => ?_
  have h1 := congrArg Fin.val h
  rw [colRot_val, colRot_val] at h1
  have := a.2
  have := b.2
  apply Fin.ext
  split_ifs at h1 <;> omega

theorem model_weight_gap_l1_card : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ (u1 : GlobalTheory.AllWt.Weight Dw) (g : ℝ), (∀ τ (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 → g ≤ (u1 τ a : ℝ) - u1 τ b) → ∀ k : U.Comp, (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ (U.X k).p0 → g ≤ (modelWt U (wtOf Dw u1 0) k τ a : ℝ) - modelWt U (wtOf Dw u1 0) k τ b) ∧ (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → g ≤ (modelWt U (wtOf Dw u1 0) k τ b : ℝ) - modelWt U (wtOf Dw u1 0) k τ a) ∧ (∑ τ, ∑ a, |(modelWt U (wtOf Dw u1 0) k τ a : ℝ)|) = GlobalTheory.CovHt.l1 u1 ∧ (U.X k).Ψ.card = Nat.card (GlobalTheory.AllWt.Psi H) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hp hq u1 g hg k
  obtain rfl := hU.1
  obtain ⟨hp0, hΨ⟩ := hU.2.1 k
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  have hrel : ∀ ρ : E →+* ℂ, ρ (H.rt : E) = H.rt0 → relab c σ ρ (H.rt : E) = H.rt0 := fun ρ h =>
    (congrArg σ (Subtype.ext h)).trans hσ0
  let e : Psi H → (U.X k).Ψ := fun ρ => ⟨relab c σ ρ.1, (hΨ _).2 (hrel _ ρ.2)⟩
  have hsurj : Function.Surjective (relab (E := E) c σ) := Finite.injective_iff_surjective.1 (relab_injective σ)
  have he : Function.Bijective e := by
    refine ⟨fun a b h => Subtype.ext (relab_injective σ (congrArg Subtype.val h)), fun τ => ?_⟩
    obtain ⟨ρ, hρ⟩ := hsurj τ.1
    have hρΨ : ρ (H.rt : E) = H.rt0 := by
      by_contra hn
      have h3 := hrel _ (GlobalTheory.AllWt.conj_mem hn)
      rw [relab_conj, hρ] at h3
      exact GlobalTheory.AllWt.conj_not_mem ⟨τ.1, (hΨ _).1 τ.2⟩ h3
    exact ⟨⟨ρ, hρΨ⟩, Subtype.ext hρ⟩
  have hval : ∀ (ρ : Psi H) (a : Fin (Dw.p + Dw.q)),
      modelWt U (wtOf Dw u1 0) k (e ρ) a = u1 ρ (colRot Dw.p Dw.q a) := by
    rintro ρ ⟨a, ha⟩
    by_cases h : a < Dw.q
    · rw [modelWt_wtOf_small U u1 0 k hp0 ρ (e ρ).2 a h ha]
      congr 1
      apply Fin.ext
      rw [colRot_val]
      simp [h]
    · obtain ⟨i, rfl⟩ : ∃ i, a = Dw.q + i := ⟨a - Dw.q, by omega⟩
      rw [modelWt_wtOf_big U u1 0 k hp0 ρ (e ρ).2 i (by omega) ha]
      congr 1
      apply Fin.ext
      rw [colRot_val]
      simp
  refine ⟨fun τ a b hab hb => ?_, fun τ a b ha hb => ?_, ?_, ?_⟩
  · obtain ⟨ρ, rfl⟩ := he.2 τ
    rw [hval, hval]
    apply hg
    rw [colRot_val, colRot_val]
    rw [hp0] at hb
    split_ifs <;> omega
  · obtain ⟨ρ, rfl⟩ := he.2 τ
    rw [hval, hval]
    apply hg
    rw [colRot_val, colRot_val]
    split_ifs <;> omega
  · unfold GlobalTheory.CovHt.l1
    rw [← he.sum_comp]
    refine Finset.sum_congr (by congr) fun ρ _ => ?_
    simp only [hval]
    exact (colRot_bijective Dw.p Dw.q).sum_comp fun i => |(u1 ρ i : ℝ)|
  · rw [Nat.card_eq_of_bijective e he, Nat.card_eq_fintype_card, Fintype.card_coe]

end GlobalTheory.ModelWtGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleActionOfFieldFibres
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem residueField_exists_algebraMap_mul_eq (R : Type) [CommRing R] (p : Ideal R) [p.IsPrime]
    (k : p.ResidueField) : ∃ a s : R, algebraMap R p.ResidueField s ≠ 0 ∧
      algebraMap R p.ResidueField s * k = algebraMap R p.ResidueField a := by
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective k
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl y
  refine ⟨a, s, ?_, ?_⟩
  · rw [Ne, Ideal.algebraMap_residueField_eq_zero]; exact s.2
  · rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime p) p.ResidueField,
      IsScalarTower.algebraMap_apply R (Localization.AtPrime p) p.ResidueField a]
    simp only [IsLocalRing.ResidueField.algebraMap_eq]
    rw [← map_mul, IsLocalization.mk'_spec']

theorem invertible_of_fibres_invertible : ∀ (R O : Type) [CommRing R] [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O] (M : Type)
    [AddCommGroup M] [Module R M] [Module O M] [SMulCommClass R O M] [Module.Finite R M] [Module.Projective R M],
    (∀ (K : Type) [Field K] [Algebra R K], ∃ (N : Type) (_ : AddCommGroup N) (_ : Module K N) (_ : Module O N)
      (_ : SMulCommClass K O N) (e : K ⊗[R] M ≃ₗ[K] N),
      (∀ (a : O) (m : M), e (1 ⊗ₜ (a • m)) = a • e (1 ⊗ₜ m)) ∧
      letI : Module (K ⊗[ℤ] O) N := TensorProduct.Algebra.module
      Module.Invertible (K ⊗[ℤ] O) N) →
    letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
    Module.Invertible (R ⊗[ℤ] O) M := by
  intro R O _ _ _ _ M _ _ _ _ _ _ hK
  let b := Module.Free.chooseBasis ℤ O
  refine GlobalTheory.T.locally_free_of_maximal_ideal_generator R O _ b M fun p hp => ?_
  obtain ⟨N, _, _, _, _, e, he, hinv⟩ := hK p.ResidueField
  obtain ⟨m, hm⟩ := GlobalTheory.T.module_action_fraction_field R O _ b M p.ResidueField
    (residueField_exists_algebraMap_mul_eq R p) N e he hinv
  obtain ⟨g, hg, h1, h2⟩ := GlobalTheory.T.exists_local_generators_residue_basis R M _ (fun i => b i • m) p hm
  exact ⟨g, hg, m, h1, h2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomorphismTrivialOnKernel
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KernelThickening

theorem exists_closed_equalizer {S : Scheme.{0}} (D : Over S) [IsSeparated D.hom] (n : ℕ) :
    ∀ (A : Over S) (x z : Fin n → (A ⟶ D)), ∃ (K : Over S) (k : K ⟶ A), IsClosedImmersion k.left ∧
      ∀ (T : Over S) (y : T ⟶ A), (∀ j, y ≫ x j = y ≫ z j) ↔ ∃ y' : T ⟶ K, y' ≫ k = y := by
  induction n with
  | zero =>
    intro A x z
    refine ⟨A, 𝟙 A, by rw [Over.id_left]; infer_instance, fun T y => ⟨fun _ => ⟨y, by simp⟩, fun _ j => j.elim0⟩⟩
  | succ n ih =>
    intro A x z
    obtain ⟨K, k, hk, hK⟩ := ih (equalizer (x 0) (z 0)) (fun j => equalizer.ι _ _ ≫ x j.succ)
      (fun j => equalizer.ι _ _ ≫ z j.succ)
    refine ⟨K, k ≫ equalizer.ι _ _, by rw [Over.comp_left]; infer_instance, fun T y => ⟨fun h => ?_, ?_⟩⟩
    · obtain ⟨y', hy'⟩ := (hK T (equalizer.lift y (h 0))).1 fun j => by
        simpa using h j.succ
      exact ⟨y', by rw [← Category.assoc, hy', equalizer.lift_ι]⟩
    · rintro ⟨y', rfl⟩ j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Category.assoc]
        rw [equalizer.condition (x 0) (z 0)]
      · simpa using (hK T (y' ≫ k)).2 ⟨y', rfl⟩ j

theorem mono_of_proper {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (hπ : Function.Surjective π)
    (N : ℕ) (hN : RingHom.ker π ^ N = ⊥) {H : Scheme.{0}} (f : H ⟶ Sp R) [IsProper f] (e : Sp R ⟶ H)
    (h : ∀ (T : Scheme.{0}) (d : T ⟶ H) (t : T ⟶ Sp R₀), d ≫ f = t ≫ spMap π → d = d ≫ f ≫ e) : Mono f := by
  have hnil : ∀ a ∈ RingHom.ker π, a ^ N = 0 := fun a ha => by
    have := Ideal.pow_mem_pow ha N
    rwa [hN, Ideal.mem_bot] at this
  have hinj : Function.Injective f := by
    refine Function.LeftInverse.injective (g := e) fun p => ?_
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (H.fromSpecResidueField p ≫ f)
    have hker : RingHom.ker π ≤ RingHom.ker φ.hom := fun a ha => by
      have : (φ.hom a) ^ N = 0 := by rw [← map_pow, hnil a ha, map_zero]
      exact IsNilpotent.eq_zero ⟨N, this⟩
    let ψ : CommRingCat.of R₀ ⟶ H.residueField p := CommRingCat.ofHom (π.liftOfSurjective hπ ⟨φ.hom, hker⟩)
    have hψ : CommRingCat.ofHom π ≫ ψ = φ := CommRingCat.hom_ext (π.liftOfRightInverse_comp _ _ ⟨φ.hom, hker⟩)
    have h₁ := h _ (H.fromSpecResidueField p) (Spec.map ψ) (by
      rw [← hφ, spMap, ← Spec.map_comp, hψ])
    obtain ⟨q, hq⟩ : ∃ q : Spec (H.residueField p), H.fromSpecResidueField p q = p :=
      ⟨IsLocalRing.closedPoint (H.residueField p), Scheme.fromSpecResidueField_apply _ _⟩
    have h₂ : H.fromSpecResidueField p q = (H.fromSpecResidueField p ≫ f ≫ e) q := congrArg (fun g => g q) h₁
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hq] at h₂
    exact h₂.symm
  have : LocallyQuasiFinite f := LocallyQuasiFinite.of_injective hinj
  have : IsFinite f := IsFinite.of_isProper_of_locallyQuasiFinite f
  refine GlobalTheory.PrincipalModRadical.mono_of_section (RingHom.ker π) ?_ f e fun T d t hd => ?_
  · exact fun a ha => Ideal.radical_le_jacobson ⟨N, hnil a ha⟩
  · refine h T d (t ≫ spMap (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom) ?_
    rw [hd, Category.assoc, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext a
    apply (RingHom.quotientKerEquivOfSurjective hπ).injective
    simp

theorem kernel_trivial_of_nilpotent :
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π →
    (∃ N : ℕ, RingHom.ker π ^ N = ⊥) → ∀ (A : Over (Sp R)) [GrpObj A], IsProper A.hom →
    ∀ (n : ℕ) (D : Over (Sp R)) [GrpObj D], IsSeparated D.hom → ∀ (x : Fin n → (A ⟶ D)), (∀ j, IsMonHom (x j)) →
    (∀ (T₀ : Over (Sp R₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ A), (∀ j, y ≫ x j = 1) → y = 1) →
    ∀ (T : Over (Sp R)) (y : T ⟶ A), (∀ j, y ≫ x j = 1) → y = 1 := by
  intro R R₀ _ _ π hπ ⟨N, hN⟩ A _ hA n D _ hD x hx h₀
  obtain ⟨K, k, hk, hK⟩ := exists_closed_equalizer D n A x fun _ => 1
  simp only [MonObj.comp_one] at hK
  have : IsProper K.hom := by
    rw [← Over.w k]
    infer_instance
  have one : ∀ T : Over (Sp R), ∃ y : T ⟶ K, y ≫ k = 1 := fun T => (hK T 1).1 fun j => by
    have := hx j
    simp [Hom.one_def]
  have hkx := (hK K k).2 ⟨𝟙 K, Category.id_comp k⟩
  obtain ⟨e, he⟩ := one (𝟙_ _)
  have : Mono K.hom := mono_of_proper π hπ N hN K.hom e.left fun T d t hd => by
    let d' : Over.mk ((Over.mk t).hom ≫ spMap π) ⟶ K := Over.homMk d hd
    have h₁ : d' ≫ k = 1 := h₀ (Over.mk t) _ fun j => by rw [Category.assoc, hkx, MonObj.comp_one]
    have : d' ≫ k = d' ≫ toUnit K ≫ e ≫ k := by
      rw [h₁, he, MonObj.comp_one, MonObj.comp_one]
    rw [← cancel_mono k.left, Category.assoc, Category.assoc]
    exact congrArg (·.left) this
  intro T y hy
  obtain ⟨y₁, hy₁⟩ := (hK T y).1 hy
  obtain ⟨y₂, hy₂⟩ := one T
  rw [← hy₁, ← hy₂, Over.OverMorphism.ext ((cancel_mono K.hom).1 ((Over.w y₁).trans (Over.w y₂).symm))]

end GlobalTheory.KernelThickening
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismTrivialOnReducedKernelStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.morphism_trivial_on_reduced_kernel : ∀ (A Y Y' Z : Over (Sp ℂ)) [GrpObj A] [GrpObj Y] [GrpObj Y'] [IsSeparated Y'.hom] (u : A ⟶ Y) (f : A ⟶ Y')
    (i : Z ⟶ A), IsPullback i (toUnit Z) u η[Y] → ∀ [AlgebraicGeometry.IsReduced Z.left] [LocallyOfFiniteType Z.hom],
    (∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ u = 1 → x ≫ f = 1) →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ u = 1 → x ≫ f = 1 := by
  first | exact @GlobalTheory.KernelKill.comp_eq_one_of_kill_closedPoints | exact GlobalTheory.KernelKill.comp_eq_one_of_kill_closedPoints | (intros; apply GlobalTheory.KernelKill.comp_eq_one_of_kill_closedPoints <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesIsAdicCompleteMapCOfNoetherianStatement
section
open IsLocalRing GlobalTheory.FormalOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_isAdicComplete_map_C_of_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ n : ℕ, IsAdicComplete (I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R)) (MvPowerSeries (Fin n) R) := by
  first | exact @GlobalTheory.PowerSeriesComplete.isAdicComplete_map_C | exact GlobalTheory.PowerSeriesComplete.isAdicComplete_map_C | (intros; apply GlobalTheory.PowerSeriesComplete.isAdicComplete_map_C <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormBigOfNonvanishingStatement
section
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_big_of_nonvanishing : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → LNe → NormBig := by
  first | exact @GlobalTheory.NormBigProof.normBig | exact GlobalTheory.NormBigProof.normBig | (intros; apply GlobalTheory.NormBigProof.normBig <;> assumption)
end

