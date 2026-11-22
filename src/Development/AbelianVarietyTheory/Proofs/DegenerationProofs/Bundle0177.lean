import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsPrimitiveRootPadicInt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0002
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTorsionGeneratorsRational
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveOfFormalEmbedding
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemGenusOne
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.RealDimOne

open GlobalTheory.TorsionGenerators GlobalTheory.ZH.DimZero NumberField

theorem isPrimitiveRoot_unitOn {k : Type} [CommRing k] {u : kˣ} {M : ℕ} (h : IsPrimitiveRoot u M) :
    IsPrimitiveRoot (unitOn u) M :=
  h.map_of_injective (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) unitOn_injective

theorem unitOn_zpow {k : Type} [CommRing k] (u : kˣ) (n : ℤ) : unitOn (u ^ n) = unitOn u ^ n :=
  map_zpow (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) u n

theorem exists_level_of_points (hL : Laws) {R K : Type} [CommRing R] [Field K] (P₀ : PolAV (Sp R))
    [IsCommMonObj P₀.A] (j : R →+* K) {M : ℕ} (hM : (M : K) ≠ 0) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ M)
    (b : Fin (2 * P₀.g) → (Over.mk (spMap j) ⟶ P₀.A)) (hb : ∀ i, b i ^ M = 1)
    (hw : ∀ i l, WeilIs P₀.A P₀.L M (b i) (b l) (unitOn (ζ ^ stdSymp P₀.g i l))) :
    ∃ (P : PolAV (Sp K)) (φ : P.A.left ⟶ P₀.A.left), IsPolFibre j P₀ P φ ∧
      Nonempty (Out.Level P M (unitOn ζ)) := by
  obtain ⟨P, φ, β, h, -, H⟩ := exists_fibre hL P₀ j
  refine ⟨P, φ, h, ?_⟩
  have hg := h.1
  generalize P₀.g = g at b hb hw hg
  subst hg
  have hx : ∀ i, β.symm (b i) ^ M = 1 := fun i => by rw [← map_pow, hb, map_one]
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  obtain ⟨lev, -⟩ := exists_level_of_pairing hL.globalFns hL.weil hL.mulN _ P M (unitOn ζ)
    (isPrimitiveRoot_unitOn hζ) (fun F _ s => by
      have : Nontrivial Γ(Sp F, ⊤) :=
        (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.symm.injective.nontrivial
      refine ⟨fun e₀ => hM ?_, (isPrimitiveRoot_unitOn hζ).map_of_injective (Units.map_injective
        fun a b hab => e.symm.injective ((s.appTop.hom.comp e.toRingHom).injective (by simpa using hab)))⟩
      refine (s.appTop.hom.comp e.toRingHom).injective ?_
      refine (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.injective ?_
      rw [map_natCast, map_natCast, map_zero, map_zero]
      exact e₀) (fun i => β.symm (b i)) hx (fun i l => by
      obtain ⟨c, hc, -⟩ := (hL.weil _ P M _).1 _ _ (hx i) (hx l)
      have H' := H M _ _ c hc
      rw [β.apply_symm_apply, β.apply_symm_apply] at H'
      rw [← unitOn_zpow, ← CommutatorPairing.weilIs_unique hL.globalFns P₀.isAb P₀.isLB H' (hw i l)]
      exact hc)
  exact ⟨lev⟩

theorem exists_level_numberField (hL : Laws) {K₀ : Type} [Field K₀] [NumberField K₀] (P₀ : PolAV (Sp K₀)) {M : ℕ}
    (hM : M ≠ 0) : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (j : K₀ →+* K) (P : PolAV (Sp K))
      (φ : P.A.left ⟶ P₀.A.left) (ζ : Kˣ), IsPrimitiveRoot ζ M ∧ IsPolFibre j P₀ P φ ∧
      Nonempty (Out.Level P M (unitOn ζ)) := by
  have := P₀.isAb.comm
  have := P₀.isAb.smooth
  let Q := AlgebraicClosure K₀
  let t : K₀ →+* Q := algebraMap K₀ Q
  have : NeZero M := ⟨hM⟩
  obtain ⟨z₀, hz₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Q M
  have hz := hz₀.isUnit_unit hM
  generalize (hz₀.isUnit hM).unit = z at hz
  obtain ⟨P', φ', β, h, -, H⟩ := exists_fibre hL P₀ t
  obtain ⟨x, hx, hw⟩ := ConstThetaLevel.exists_symplectic_points hL Q P' h.1.symm M (Nat.cast_ne_zero.2 hM) _
    (isPrimitiveRoot_unitOn hz)
  choose s hs hb using fun i => exists_finite_coordinates P₀.A.hom t (β (x i)).left (Over.w _)
  let s' : Set Q := insert (z : Q) (⋃ i, s i)
  have : Finite s' := ((Set.finite_iUnion hs).insert _).to_subtype
  let K := IntermediateField.adjoin K₀ s'
  have : FiniteDimensional K₀ K := IntermediateField.finiteDimensional_adjoin fun y _ =>
    (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  have : NumberField K := NumberField.of_module_finite K₀ K
  let io : K →+* Q := algebraMap K Q
  let j : K₀ →+* K := algebraMap K₀ K
  have hj : io.comp j = t := rfl
  choose b hb' using fun i => hb i K io io.injective (fun c => ⟨j c, rfl⟩) (fun y hy =>
    ⟨⟨y, IntermediateField.subset_adjoin K₀ s' (Set.mem_insert_of_mem _ (Set.mem_iUnion.2 ⟨i, hy⟩))⟩, rfl⟩)
  have hbw : ∀ i, b i ≫ P₀.A.hom = spMap j := fun i => by
    have := TorsionSeparable.epi_specMap io
    rw [← cancel_epi (spMap io), ← Category.assoc, hb', spMap_comp_spMap]
    exact Over.w (β (x i))
  let y : Fin (2 * P₀.g) → (Over.mk (spMap j) ⟶ P₀.A) := fun i => Over.homMk (b i) (hbw i)
  have hy : ∀ i, extPt hj ≫ y i = β (x i) := fun i => Over.OverMorphism.ext (hb' i)
  have hyM : ∀ i, y i ^ M = 1 := fun i => by
    rw [← extPt_eq_one_iff hj, comp_pow, hy, ← map_pow]
    exact (congrArg β (hx i)).trans (map_one β)
  let ζ : Kˣ := Units.mk0 ⟨z, IntermediateField.subset_adjoin K₀ s' (Set.mem_insert _ _)⟩
    fun e => z.ne_zero (congrArg Subtype.val e)
  have hζ : Units.map io.toMonoidHom ζ = z := Units.ext rfl
  have hp : IsPrimitiveRoot ζ M := IsPrimitiveRoot.of_map_of_injective (hζ ▸ hz) (unitsMap_injective io)
  obtain ⟨P, φ, h₁, h₂⟩ := exists_level_of_points hL P₀ j (Nat.cast_ne_zero.2 hM) hp y hyM fun i l => by
    obtain ⟨u, hu⟩ := exists_weilIs hL P₀ j (hyM i) (hyM l)
    have H₁ := weilIs_extPt hL P₀ hj hu
    rw [hy, hy] at H₁
    have e := CommutatorPairing.weilIs_unique hL.globalFns P₀.isAb P₀.isLB H₁ (H _ _ _ _ (hw i l))
    rw [← unitOn_zpow, ← hζ, ← map_zpow] at e
    rwa [← unitsMap_injective io (unitOn_injective e)]
  exact ⟨K, _, this, j, P, φ, ζ, hp, h₁, h₂⟩

theorem exists_real_dim_one : Laws → Laws2 → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : ArithBase o Ω) (S : ThetaSys o Ω), S.g = 1 ∧ S.Big ∧ Nonempty S.Real := by
  intro hL hL2
  obtain ⟨K₀, _, _, _⟩ : ∃ (K : Type) (_ : Field K) (_ : NumberField K), IsCyclotomicExtension {3} ℚ K :=
    ⟨CyclotomicField 3 ℚ, inferInstance, inferInstance, by
      convert CyclotomicField.isCyclotomicExtension 3 ℚ <;> first | rfl | exact Subsingleton.elim _ _⟩
  have hω := (IsCyclotomicExtension.zeta_spec 3 ℚ K₀).geom_sum_eq_zero (by norm_num)
  obtain ⟨P₀, hg, hS⟩ := CubeRootAut.exists_hypS hL K₀ (IsCyclotomicExtension.zeta 3 ℚ K₀) (by
    rw [← hω]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    ring)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = (3 ^ 5 * (3 ^ 2) ^ 2) ^ 2 := ⟨_, rfl⟩
  have hM₀ : M ≠ 0 := by rw [hM]; positivity
  obtain ⟨K, _, _, j, P, φ, ζ, hζ, h, ⟨lev⟩⟩ := exists_level_numberField hL P₀ hM₀
  have := arithBase_intAway K
  have hS' : HypS P.A P.L :=
    SymBaseChange.hypS_baseChange _ _ _ _ _ φ _ _ P₀.isLB P.isLB h.2.1 h.2.2.symm hS
  have hζ' : IsPrimitiveRoot (ζ : K) M := IsPrimitiveRoot.coe_units_iff.2 hζ
  have : NeZero M := ⟨hM₀⟩
  let ze : (intAway K)ˣ := Units.map (algebraMap (𝓞 K) (intAway K)).toMonoidHom
    (hζ'.toInteger_isPrimitiveRoot.isUnit hM₀).unit
  have hze : ζ = Units.map (algebraMap (intAway K) K).toMonoidHom ze := Units.ext rfl
  have h3 : IsUnit ((3 : ℕ) : intAway K) := by simpa using isUnit_three_intAway K
  have hu : IsUnit (M : intAway K) := by
    rw [hM]
    simp only [Nat.cast_pow, Nat.cast_mul]
    exact ((h3.pow _).mul ((h3.pow _).pow _)).pow _
  have frac : ∀ x : K, ∃ a ∈ (⊥ : Subalgebra (intAway K) K), ∃ b ∈ (⊥ : Subalgebra (intAway K) K), x = a / b :=
    fun x => by
      obtain ⟨a, b, -, h⟩ := IsFractionRing.div_surjective (A := intAway K) x
      exact ⟨_, Subalgebra.algebraMap_mem _ a, _, Subalgebra.algebraMap_mem _ b, h.symm⟩
  obtain ⟨R, P', -, lev', hR, fg, hg', hS'', -⟩ :=
    GenSpread.polAV_spreads_out (intAway K) K ⊥ Subalgebra.fg_bot frac P M ze hu hS' (hze ▸ lev) hL
  obtain ⟨S, ρ, -, -, -, hN, hr, hSg, -⟩ := ThetaReal.exists_thetaSys_real hL hL2 (intAway K) K R fg (fun x => by
      obtain ⟨a, ha, b, hb, e⟩ := frac x
      exact ⟨a, hR ha, b, hR hb, e⟩) P' 3 2 5 ze Nat.prime_three (by decide) le_rfl (by norm_num) h3 hS'' (hM ▸ lev')
  have g1 : S.g = 1 := hSg.trans (hg'.trans (h.1.trans hg))
  refine ⟨_, K, _, _, _, arithBase_intAway K, S, g1, ?_, ⟨ρ⟩⟩
  have a₁ : (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (x := 2) one_le_two (show (1 : ℝ) / 2 ≤ 1 by norm_num)
  have a₂ : (2 : ℝ) ^ ((1 : ℝ) / 2 - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by norm_num)
  have a₃ : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 2 - 1) := by positivity
  have a₄ : (2 : ℝ) ^ ((1 : ℝ) / 2 - 1) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by norm_num)
  unfold ThetaSys.Big
  rw [g1, hN, hr]
  simp only [Nat.cast_one, Nat.factorial_one, pow_one]
  refine ⟨?_, ?_, by norm_num⟩
  · push_cast
    linarith
  · push_cast
    linarith

end GlobalTheory.ZH.RealDimOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueHomExtensionSmoothConnSemiAbelianDvrStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_hom_extension_smoothConn_semiAbelian_dvr : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (H G : Over (Sp T)) [GrpObj H] [GrpObj G], SmConn H → IsSemiAbelian G → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj H ⟶ (Over.pullback (spMap (algebraMap T K))).obj G, IsMonHom f → ∃! F : H ⟶ G, IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f := by
  first | exact @GlobalTheory.existsUnique_hom_extension_smConn_semiAbelian_dvr | exact GlobalTheory.existsUnique_hom_extension_smConn_semiAbelian_dvr | (intros; apply GlobalTheory.existsUnique_hom_extension_smConn_semiAbelian_dvr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueHomOfThickenings
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.LocalMorAlg

open GlobalTheory.MorAlg

theorem exists_section_local (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y P : Over (Spec (CommRingCat.of V))) (q : P ⟶ Y)
    [IsSeparated q.left] [IsProper Y.hom] [Flat Y.hom] (hP : IsProjBy P.hom)
    (j : ∀ e, (thickObj V (IsLocalRing.maximalIdeal V) e Y).left ⟶ P.left)
    (hq : ∀ e, j e ≫ q.left = pullback.fst Y.hom (thick V (IsLocalRing.maximalIdeal V) e))
    (hj : ∀ e, thickMap V (IsLocalRing.maximalIdeal V) e Y ≫ j (e + 1) = j e) :
    ∃ g : Y ⟶ P, ∀ e, pullback.fst Y.hom (thick V (IsLocalRing.maximalIdeal V) e) ≫ g.left = j e := by
  obtain ⟨H, hH, n, s, hs⟩ := hP
  have hL : ∀ e, (H.pull (j e)).IsLB := fun e => LB.isLB_pull hH _
  choose t ht using fun e => exists_isPull (j e) hH s
  have hv : ∀ e, IsPull (thickMap V (IsLocalRing.maximalIdeal V) e Y) (t (e + 1)) (t e) := fun e =>
    IsPull.cancel hH (hL _) (hL _) (ht (e + 1)) (by rw [hj]; exact ht e)
  choose v hv cv using hv
  have hjV : ∀ e, j e ≫ P.hom = (thickObj V (IsLocalRing.maximalIdeal V) e Y).hom ≫ thick V (IsLocalRing.maximalIdeal V) e := fun e => by
    rw [← Over.w q, ← Category.assoc, hq]
    exact pullback.condition
  have hci : ∀ e, IsClosedImmersion (thick V (IsLocalRing.maximalIdeal V) e) := fun e =>
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hva : VeryAmpleBy (thickObj V (IsLocalRing.maximalIdeal V) 0 Y).hom (H.pull (j 0)) (t 0) := by
    obtain ⟨w, hw, c⟩ := ht 0
    refine GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull V P.left P.hom H n s hH hs _ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1))) _ _ (j 0) (hjV 0) ?_ _ w _
      (hL 0) hw c
    have h₁ : IsClosedImmersion (j 0 ≫ q.left) := by
      rw [hq]
      have := hci 0
      infer_instance
    have h₂ : IsClosedImmersion (j 0) := IsClosedImmersion.of_comp _ q.left
    have h₃ : IsClosedImmersion (pullback.lift (j 0) (thickObj V (IsLocalRing.maximalIdeal V) 0 Y).hom (hjV 0) ≫
        pullback.fst P.hom (thick V (IsLocalRing.maximalIdeal V) 0)) := by
      rw [pullback.lift_fst]
      exact h₂
    exact IsClosedImmersion.of_comp _ (pullback.fst P.hom (thick V (IsLocalRing.maximalIdeal V) 0))
  have hpb : ∀ e, IsPullback (thickMap V (IsLocalRing.maximalIdeal V) e Y) (thickObj V (IsLocalRing.maximalIdeal V) e Y).hom (thickObj V (IsLocalRing.maximalIdeal V) (e + 1) Y).hom
      (thickTrans V (IsLocalRing.maximalIdeal V) e) := fun e => by
    refine IsPullback.of_right (h₁₂ := pullback.fst Y.hom (thick V (IsLocalRing.maximalIdeal V) (e + 1))) (h₂₂ := thick V (IsLocalRing.maximalIdeal V) (e + 1))
      (v₁₃ := Y.hom) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [thickTrans_comp, pullback.lift_fst, Category.comp_id]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨B, H', s', b, w, hH', hs', hb, -, hw, heq⟩ := GlobalTheory.LocalEmb.exists_projective_of_formal_embedding V (fun e => thickObj V (IsLocalRing.maximalIdeal V) e Y)
    (fun e => thickMap V (IsLocalRing.maximalIdeal V) e Y) hpb (fun e => inferInstanceAs (Flat (pullback.snd Y.hom (thick V (IsLocalRing.maximalIdeal V) e))))
    (fun e => H.pull (j e)) v (fun e => ⟨hL e, hv e⟩) n t cv hva
  obtain ⟨φ, u, hφ, hu, cu⟩ := GlobalTheory.exists_hom_of_veryAmpleBy V P.left P.hom H n s hH hs B.left B.hom H' s' hH' hs'.1
    fun d F hF h0 => heq d F hF fun e k => by
      rw [← hjV]
      exact (ht e).eqn P.hom hH hF h0 k
  have hbφ : ∀ e, b e ≫ φ = j e := fun e => by
    obtain ⟨w₁, hw₁, c₁⟩ := IsPull.comp hH hH' (hL e) ⟨u, hu, cu⟩ ⟨w e, (hw e).1, (hw e).2⟩
    obtain ⟨w₂, hw₂, c₂⟩ := ht e
    refine GlobalTheory.MapUniq.hom_eq_of_pull_sections V P.left P.hom H n s hH hs _ _ (t e) _ _ w₁ w₂ (hL e) ?_ hw₁ hw₂ c₁ c₂
    rw [Category.assoc, hφ, hjV]
    exact (hb e).w
  let φ' : B ⟶ P := Over.homMk φ hφ
  have hbp : ∀ e, b e ≫ (φ' ≫ q).left = pullback.fst Y.hom (thick V (IsLocalRing.maximalIdeal V) e) := fun e => by
    rw [← hq, ← hbφ]
    exact (Category.assoc _ _ _).symm
  have hB : IsProper ((φ' ≫ q).left ≫ Y.hom) := by
    rw [Over.w]
    exact GlobalTheory.AbLaw.isProper_of_isProjBy V _ _ ⟨H', hH', n, s', hs'⟩
  have hp : IsProper (φ' ≫ q).left := IsProper.of_comp _ Y.hom
  have hiso : IsIso (φ' ≫ q) := GlobalTheory.IsoLimit.main V B Y (φ' ≫ q) fun e => by
    have h₁ : (hb e).isoPullback.hom ≫ ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map (φ' ≫ q)).left = 𝟙 _ := by
      apply pullback.hom_ext
      · simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst, Category.id_comp]
        rw [← hbp e, IsPullback.isoPullback_hom_fst_assoc]
      · simp only [Over.pullback_map_left, Category.assoc, pullback.lift_snd, Category.id_comp]
        exact (hb e).isoPullback_hom_snd
    have h₂ : IsIso ((Over.forget _).map ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map (φ' ≫ q))) :=
      @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ (Iso.isIso_hom _) (IsIso.id _) h₁
    exact isIso_of_reflects_iso _ (Over.forget _)
  refine ⟨inv (φ' ≫ q) ≫ φ', fun e => ?_⟩
  rw [← hbp, Category.assoc, ← Over.comp_left, IsIso.hom_inv_id_assoc]
  exact hbφ e

theorem exists_hom_local : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y Z : Over (Spec (CommRingCat.of V))), IsProjBy Y.hom → IsProjBy Z.hom → Flat Y.hom → ∀ f : ∀ e, (thickObj V (IsLocalRing.maximalIdeal V) e Y).left ⟶ Z.left, (∀ e, f e ≫ Z.hom = (fstG (IsLocalRing.maximalIdeal V) e Y).left ≫ Y.hom) → (∀ e, thickMap V (IsLocalRing.maximalIdeal V) e Y ≫ f (e + 1) = f e) → ∃ g : Y ⟶ Z, ∀ e, (fstG (IsLocalRing.maximalIdeal V) e Y).left ≫ g.left = f e := by
  intro V _ _ _ _ _ Y Z hY hZ hfl f hf hc
  have pY := GlobalTheory.AbLaw.isProper_of_isProjBy V _ _ hY
  have pZ := GlobalTheory.AbLaw.isProper_of_isProjBy V _ _ hZ
  have hsep : IsSeparated (fst Y Z).left := inferInstanceAs (IsSeparated (pullback.fst Y.hom Z.hom))
  obtain ⟨g, hg⟩ := exists_section_local V Y (Y ⊗ Z) (fst Y Z) (GlobalTheory.AbLaw.isProjBy_tensor V Y Z hY hZ)
    (fun e => pullback.lift (pullback.fst Y.hom (thick V _ e)) (f e) (hf e).symm)
    (fun e => pullback.lift_fst _ _ _) (fun e => by
      apply pullback.hom_ext
      · erw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst, Category.comp_id]
      · erw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hc])
  refine ⟨g ≫ snd Y Z, fun e => ?_⟩
  have := congrArg (· ≫ pullback.snd Y.hom Z.hom) (hg e)
  exact ((Category.assoc _ _ _).symm.trans this).trans (pullback.lift_snd _ _ _)

theorem comp_eq_of_compatible {R : Type} [CommRing R] (I : Ideal R) (Y : Over (Spec (CommRingCat.of R)))
    {Z T : Scheme.{0}} (f : ∀ e, (thickObj R I e Y).left ⟶ Z) (hc : ∀ e, thickMap R I e Y ≫ f (e + 1) = f e)
    {e n : ℕ} (a : T ⟶ (thickObj R I e Y).left) (b : T ⟶ (thickObj R I n Y).left)
    (h : a ≫ pullback.fst Y.hom (thick R I e) = b ≫ pullback.fst Y.hom (thick R I n)) : a ≫ f e = b ≫ f n := by
  have up : ∀ (e : ℕ) (a : T ⟶ (thickObj R I e Y).left) (k : ℕ), e ≤ k → ∃ a' : T ⟶ (thickObj R I k Y).left,
      a' ≫ pullback.fst Y.hom (thick R I k) = a ≫ pullback.fst Y.hom (thick R I e) ∧ a' ≫ f k = a ≫ f e := by
    intro e a k hk
    induction k, hk using Nat.le_induction with
    | base => exact ⟨a, rfl, rfl⟩
    | succ k _ ih =>
      obtain ⟨a', h₁, h₂⟩ := ih
      have t : thickMap R I k Y ≫ pullback.fst Y.hom (thick R I (k + 1)) = pullback.fst Y.hom (thick R I k) :=
        (pullback.lift_fst _ _ _).trans (Category.comp_id _)
      exact ⟨a' ≫ thickMap R I k Y, (Category.assoc _ _ _).trans ((congrArg (a' ≫ ·) t).trans h₁),
        (Category.assoc _ _ _).trans ((congrArg (a' ≫ ·) (hc k)).trans h₂)⟩
  obtain ⟨a', ha, ha'⟩ := up e a (e + n) (by omega)
  obtain ⟨b', hb, hb'⟩ := up n b (e + n) (by omega)
  have : IsClosedImmersion (thick R I (e + n)) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hm : Mono (pullback.fst Y.hom (thick R I (e + n))) := inferInstance
  have e' : a' = b' := hm.right_cancellation _ _ (ha.trans (h.trans hb.symm))
  rw [← ha', ← hb', e']

theorem existsUnique_hom_of_thickenings : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (Y Z : Over (Spec (CommRingCat.of R))), GlobalTheory.AbLaw.IsProjBy Y.hom → GlobalTheory.AbLaw.IsProjBy Z.hom → Smooth Y.hom → ∀ f : ∀ e, (thickObj R I e Y).left ⟶ Z.left, (∀ e, f e ≫ Z.hom = (fstG I e Y).left ≫ Y.hom) → (∀ e, thickMap R I e Y ≫ f (e + 1) = f e) → ∃! g : Y ⟶ Z, ∀ e, (fstG I e Y).left ≫ g.left = f e := by
  intro _ _ R _ _ _ _ I hI _ _ Y Z hY hZ hsm f hf hc
  have pY := GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ hY
  have pZ := GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ hZ
  have hIm : I ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  have hJ : IsLocalRing.maximalIdeal R ≤ Ideal.jacobson ⊥ := IsLocalRing.maximalIdeal_le_jacobson _
  have hρ : ∀ e, ∃ ρ : (thickObj R (IsLocalRing.maximalIdeal R) e Y).left ⟶ (thickObj R I e Y).left,
      ρ ≫ pullback.fst Y.hom (thick R I e) = pullback.fst Y.hom (thick R (IsLocalRing.maximalIdeal R) e) := fun e =>
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ GlobalTheory.LocalEmb.fac (Ideal.pow_right_mono hIm (e + 1)))
      (by rw [Category.assoc, GlobalTheory.LocalEmb.fac_quo]; exact pullback.condition), pullback.lift_fst _ _ _⟩
  choose ρ hρ using hρ
  obtain ⟨g, hg⟩ := exists_hom_local R Y Z hY hZ inferInstance (fun e => ρ e ≫ f e)
    (fun e => (Category.assoc _ _ _).trans ((congrArg (ρ e ≫ ·) (hf e)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ Y.hom) (hρ e)))))
    (fun e => (Category.assoc _ _ _).symm.trans (comp_eq_of_compatible I Y f hc _ _
      ((Category.assoc _ _ _).trans ((congrArg (thickMap R _ e Y ≫ ·) (hρ (e + 1))).trans
        (((pullback.lift_fst _ _ _).trans (Category.comp_id _)).trans (hρ e).symm)))))
  have key : ∀ e, (fstG I e Y).left ≫ g.left = f e := fun e => by
    have : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (pullback.fst Y.hom (thick R I e) ≫ Y.hom)
    have pY' : IsProper Y'.hom := inferInstanceAs (IsProper (pullback.fst Y.hom (thick R I e) ≫ Y.hom))
    let u : Y' ⟶ Z := Over.homMk (pullback.fst Y.hom (thick R I e) ≫ g.left)
      ((Category.assoc _ _ _).trans (congrArg (pullback.fst Y.hom (thick R I e) ≫ ·) (Over.w g)))
    let u' : Y' ⟶ Z := Over.homMk (f e) (hf e)
    refine congrArg CommaMorphism.left (GlobalTheory.hom_eq_of_thickenings_of_isProper R _ hJ Y' Z u u' fun n => ?_)
    obtain ⟨l, hl⟩ : ∃ l : pullback Y'.hom (thick R (IsLocalRing.maximalIdeal R) n) ⟶
        (thickObj R (IsLocalRing.maximalIdeal R) n Y).left,
        l ≫ pullback.fst Y.hom (thick R (IsLocalRing.maximalIdeal R) n) =
          pullback.fst Y'.hom (thick R (IsLocalRing.maximalIdeal R) n) ≫ pullback.fst Y.hom (thick R I e) :=
      ⟨pullback.lift _ (pullback.snd _ _) ((Category.assoc _ _ _).trans pullback.condition), pullback.lift_fst _ _ _⟩
    have h₁ := comp_eq_of_compatible I Y f hc (l ≫ ρ n) (pullback.fst Y'.hom (thick R (IsLocalRing.maximalIdeal R) n))
      ((Category.assoc _ _ _).trans ((congrArg (l ≫ ·) (hρ n)).trans hl))
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g.left) hl.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (l ≫ ·) (hg n)).trans ((Category.assoc _ _ _).symm.trans h₁))))
  exact ⟨g, key, fun g' hg' => GlobalTheory.hom_eq_of_thickenings_of_isProper R I (hIm.trans hJ) Y Z g' g
    fun e => (hg' e).trans (key e).symm⟩

end GlobalTheory.LocalMorAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FlatAndSurjectiveOfSurjectivePoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

open UnramifiedEndFlat in

theorem flat_of_isDominant_grpHom (K : Type) [Field K] [IsAlgClosed K]
    (G G' : Over (Sp K)) [GrpObj G] [GrpObj G'] [IrreducibleSpace G.left] [IsIntegral G'.left]
    [LocallyOfFiniteType G.hom] [LocallyOfFiniteType G'.hom] (φ : G ⟶ G') [IsMonHom φ]
    [QuasiCompact φ.left] [IsDominant φ.left] : Flat φ.left := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  have : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  have : LocallyOfFiniteType (φ.left ≫ G'.hom) := by rw [Over.w φ]; infer_instance
  have : LocallyOfFiniteType φ.left := locallyOfFiniteType_of_comp _ G'.hom
  have hξ : φ.left (genericPoint G.left) = genericPoint G'.left := by
    have h := (genericPoint_spec G.left).image φ.left.continuous
    rw [Set.image_univ, φ.left.denseRange.closure_range] at h
    exact h.eq (genericPoint_spec G'.left)
  obtain ⟨W, hW, H⟩ := IntDiv.exists_open_flat φ.left hξ
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hW W.2.isLocallyClosed
  refine flat_of_closedPoints _ fun x hx => ?_
  let x' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2
  let y' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨y, hyc⟩).2
  let α := GrpObj.mulRight (A := G) (y'⁻¹ * x')
  let β := GrpObj.mulRight (A := G') ((y'⁻¹ * x') ≫ φ)
  have hαβ : α.hom ≫ φ = φ ≫ β.hom := by
    simp only [α, β]
    generalize y'⁻¹ * x' = z
    simp [comp_lift_assoc]
  have hα : y' ≫ α.hom = x' := by
    have : y' ≫ α.hom = y' * (y'⁻¹ * x') := by
      simp [α, comp_lift_assoc, Hom.mul_def]
    rw [this, mul_inv_cancel_left]
  have hα' : α.hom.left y = x := by
    have h := congr(($hα).left (IsLocalRing.closedPoint K))
    rw [← pointOfClosedPoint_apply G.hom x hx (IsLocalRing.closedPoint K),
      ← pointOfClosedPoint_apply G.hom y hyc (IsLocalRing.closedPoint K)]
    exact h
  have : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).map α.hom))
  have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  have h1 : ((φ.left ≫ β.hom.left).stalkMap y).hom.Flat := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (Flat.stalkMap β.hom.left _).comp (H y hy)
  rw [← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp] at h1
  rw [← hα']
  exact (RingHom.Flat.respectsIso.cancel_right_isIso
    (φ.left.stalkMap (α.hom.left y)) (α.hom.left.stalkMap y)).mp h1

theorem flat_and_surjective_of_surjective_points : ∀ (k : Type) [Field k] [IsAlgClosed k] (G G' : Over (Sp k)) [GrpObj G] [GrpObj G'], SmConn G → SmConn G' → ∀ i : G ⟶ G', IsMonHom i → (∀ y : (𝟙_ (Over (Sp k)) ⟶ G'), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ≫ i = y) → Flat i.left ∧ Surjective i.left := by
  intro k _ _ G G' _ _ ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ i _ hi
  have := grpObj_geometricallyIntegral_of_smooth _ G
  have := grpObj_geometricallyIntegral_of_smooth _ G'
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_subsingleton G.hom
  have : IsIntegral G'.left := GeometricallyIntegral.isIntegral_of_subsingleton G'.hom
  have : QuasiCompact (i.left ≫ G'.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact i.left := .of_comp _ G'.hom
  have : Surjective i.left := DivisiblePart.surjective_of_rationalPoints i hi
  exact ⟨flat_of_isDominant_grpHom k G G' i, this⟩

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemiAbelianReductionOfRetract
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

private theorem smConn_of_semiAbelian {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (hG : IsSemiAbelian G) : SmConn G := by
  obtain ⟨c, sm, se, qc, gc, -⟩ := hG
  exact ⟨c, sm, se, qc, gc⟩

theorem exists_semiAbelian_model_of_retract (W L : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L]
    (G : Over (Sp W)) [GrpObj G] (hG : IsSemiAbelian G) (C : Over (Sp L)) [GrpObj C]
    (a : C ⟶ (Over.pullback (spMap (algebraMap W L))).obj G)
    (b : (Over.pullback (spMap (algebraMap W L))).obj G ⟶ C) [IsMonHom a] [IsMonHom b]
    (hab : a ≫ b = 𝟙 C) :
    ∃ (G₁ : Over (Sp W)) (_ : GrpObj G₁), IsSemiAbelian G₁ ∧
      ∃ e : (Over.pullback (spMap (algebraMap W L))).obj G₁ ≅ C, IsMonHom e.hom := by

  obtain ⟨F, ⟨hF, hFe⟩, huniq⟩ :=
    GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W L G G hG hG (b ≫ a) inferInstance
  have hFF : F ≫ F = F := huniq (F ≫ F) ⟨inferInstance, by
    simp only [CategoryTheory.Functor.map_comp, hFe, Category.assoc, reassoc_of% hab]⟩

  obtain ⟨G₁, _, i, r, hSm₁, hi, hr, hir, hri⟩ :=
    GlobalTheory.T.exists_retract_of_smConn_idempotent (Sp W) G (smConn_of_semiAbelian G hG) F hF hFF
  have hG₁ : IsSemiAbelian G₁ := GlobalTheory.T.isSemiAbelian_of_retract' (Sp W) G G₁ hG hSm₁ i r hr hir
  subst hri

  refine ⟨G₁, inferInstance, hG₁,
    { hom := (Over.pullback (spMap (algebraMap W L))).map i ≫ b
      inv := a ≫ (Over.pullback (spMap (algebraMap W L))).map r
      hom_inv_id := ?_
      inv_hom_id := ?_ }, ?_⟩
  · calc ((Over.pullback (spMap (algebraMap W L))).map i ≫ b) ≫ a ≫ (Over.pullback (spMap (algebraMap W L))).map r = (Over.pullback (spMap (algebraMap W L))).map i ≫ (Over.pullback (spMap (algebraMap W L))).map (r ≫ i) ≫ (Over.pullback (spMap (algebraMap W L))).map r := by
          rw [hFe]; simp only [Category.assoc]
      _ = (Over.pullback (spMap (algebraMap W L))).map (i ≫ r ≫ i ≫ r) := by simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      _ = 𝟙 _ := by rw [reassoc_of% hir, hir, CategoryTheory.Functor.map_id]
  · calc (a ≫ (Over.pullback (spMap (algebraMap W L))).map r) ≫ (Over.pullback (spMap (algebraMap W L))).map i ≫ b = a ≫ (Over.pullback (spMap (algebraMap W L))).map (r ≫ i) ≫ b := by
          simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      _ = 𝟙 C := by rw [hFe, Category.assoc, reassoc_of% hab, hab]
  · show IsMonHom ((Over.pullback (spMap (algebraMap W L))).map i ≫ b)
    infer_instance

theorem potModel_semiAbelian_of_retract : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (B Q : Over (Sp K)) [GrpObj B] [GrpObj Q] (i : B ⟶ Q) (r : Q ⟶ B), IsMonHom i → IsMonHom r → i ≫ r = 𝟙 B → PotModel V K Q (fun _ _ _ G _ => IsSemiAbelian G) → PotModel V K B (fun _ _ _ G _ => IsSemiAbelian G) := by
  intro V K _ _ _ _ _ _ _ _ B Q _ _ i r hi hr hir hQ
  obtain ⟨W, L, _, _, _, _, _, _, _, _, hcomp, hfin, hloc, hcompl, G, _, ⟨e, he⟩, hG⟩ := hQ

  have hab : ((Over.pullback (spMap (algebraMap K L))).map i ≫ e.inv) ≫ e.hom ≫ (Over.pullback (spMap (algebraMap K L))).map r = 𝟙 ((Over.pullback (spMap (algebraMap K L))).obj B) := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← CategoryTheory.Functor.map_comp, hir, CategoryTheory.Functor.map_id]
  obtain ⟨G₁, _, hG₁, e₁, he₁⟩ :=
    exists_semiAbelian_model_of_retract W L G hG ((Over.pullback (spMap (algebraMap K L))).obj B) ((Over.pullback (spMap (algebraMap K L))).map i ≫ e.inv) (e.hom ≫ (Over.pullback (spMap (algebraMap K L))).map r) hab
  exact ⟨W, L, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, hcomp, hfin, hloc, hcompl, G₁, ‹_›, ⟨e₁, he₁⟩, hG₁⟩

end GlobalTheory.SS
end

