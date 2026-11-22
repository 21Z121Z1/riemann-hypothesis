import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationConstantOfPowerEq
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1686
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1652
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2203
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1953
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PackingStatementHolds
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem exists_alg_norm_eq (p : ℕ) [Fact p.Prime] (x : ℂ_[p]) (hx : x ≠ 0) :
    ∃ a : PadicAlgCl p, ‖(a : ℂ_[p])‖ = ‖x‖ := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  obtain ⟨a, ha⟩ := (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)).exists_dist_lt x hpos
  refine ⟨a, ?_⟩
  rw [dist_eq_norm] at ha
  have h1 : ‖(a : ℂ_[p])‖ ≤ max ‖x‖ ‖x - (a : ℂ_[p])‖ := by
    have := IsUltrametricDist.norm_add_le_max x (-(x - (a : ℂ_[p])))
    rwa [norm_neg, show x + -(x - (a : ℂ_[p])) = (a : ℂ_[p]) by ring] at this
  have h2 : ‖x‖ ≤ max ‖(a : ℂ_[p])‖ ‖x - (a : ℂ_[p])‖ := by
    have := IsUltrametricDist.norm_add_le_max (a : ℂ_[p]) (x - (a : ℂ_[p]))
    rwa [show (a : ℂ_[p]) + (x - (a : ℂ_[p])) = x by ring] at this
  rw [max_eq_left ha.le] at h1
  refine le_antisymm h1 ?_
  rcases le_max_iff.1 h2 with h | h
  · exact h
  · exact absurd h (not_le.2 ha)

theorem norm_unit_int (p : ℕ) [Fact p.Prime] {u : 𝓞_ℂ_[p]} (hu : IsUnit u) : ‖(u : ℂ_[p])‖ = 1 := by
  rw [← coe_valued]
  have := (PadicComplexInt.integers p).one_of_isUnit hu
  exact_mod_cast this

theorem norm_eq_unif_pow (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) (φ : O →+* 𝓞_ℂ_[p]) {n : O} (hn : n ≠ 0) :
    ∃ m : ℕ, ‖((φ n : 𝓞_ℂ_[p]) : ℂ_[p])‖ = ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ ^ m := by
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hn hϖ
  refine ⟨m, ?_⟩
  rw [map_mul, map_pow, Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow,
    norm_unit_int p ((Units.isUnit u).map φ), _root_.one_mul]

theorem exists_frac_model (p : ℕ) [Fact p.Prime] (a : PadicAlgCl p) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (φ : O →+* 𝓞_ℂ_[p]) (n d : O),
      Function.Injective φ ∧ IsLocalHom φ ∧ d ≠ 0 ∧
        ((φ n : 𝓞_ℂ_[p]) : ℂ_[p]) = (a : ℂ_[p]) * ((φ d : 𝓞_ℂ_[p]) : ℂ_[p]) := by
  let L := IntermediateField.adjoin ℚ_[p] ({a} : Set (PadicAlgCl p))
  haveI : FiniteDimensional ℚ_[p] L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  obtain ⟨W, _, _, _, _, _, _, _, hc, hfin, -, -, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension ℤ_[p] ℚ_[p] L
  let φ₀ : W →+* ℂ_[p] :=
    (algebraMap (PadicAlgCl p) ℂ_[p]).comp (L.val.toRingHom.comp (algebraMap W L))
  have hcomp : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (padicIntHom p) = φ₀.comp (algebraMap ℤ_[p] W) := by
    ext z
    have h1 := congrArg (fun g => g z) hc
    simp only [RingHom.comp_apply] at h1
    simp only [RingHom.comp_apply, φ₀, h1]
    rfl
  have hint : ∀ b : W, φ₀ b ∈ 𝓞_ℂ_[p] := by
    intro b
    haveI : Algebra.IsIntegral ℤ_[p] W := Algebra.IsIntegral.of_finite ℤ_[p] W
    have h1 : IsIntegral 𝓞_ℂ_[p] (φ₀ b) :=
      IsIntegral.map_of_comp_eq (padicIntHom p) φ₀ hcomp (Algebra.IsIntegral.isIntegral b)
    exact (PadicComplexInt.integers p).mem_of_integral h1
  let φ : W →+* 𝓞_ℂ_[p] := φ₀.codRestrict 𝓞_ℂ_[p] hint
  have hinj0 : Function.Injective φ₀ :=
    (algebraMap (PadicAlgCl p) ℂ_[p]).injective.comp
      (Subtype.val_injective.comp (IsFractionRing.injective W L))
  have hinj : Function.Injective φ := fun b c h => hinj0 (congrArg Subtype.val h)
  have hle : ∀ u : 𝓞_ℂ_[p], ‖(u : ℂ_[p])‖ ≤ 1 := fun u => by
    rw [← coe_valued]
    exact_mod_cast u.2
  have hpn : ‖((φ ((p : ℕ) : W) : 𝓞_ℂ_[p]) : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [map_natCast]
    rw [show (((p : ℕ) : 𝓞_ℂ_[p]) : ℂ_[p]) = ((p : ℕ) : ℂ_[p]) from map_natCast (algebraMap 𝓞_ℂ_[p] ℂ_[p]) p]
    rw [← coe_valued, PadicComplex.valuation_p]
    simp
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 (Fact.out : p.Prime).pos)
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hloc : IsLocalHom φ := by
    refine ⟨fun b hb => ?_⟩
    by_contra hnb
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
    have hp0 : ((p : ℕ) : W) ≠ 0 := fun h => by
      rw [h, map_zero] at hpn
      simp only [ZeroMemClass.coe_zero, norm_zero] at hpn
      exact hpos.ne hpn
    obtain ⟨e, he⟩ := norm_eq_unif_pow p hϖ φ hp0
    have hϖ1 : ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ < 1 := by
      refine lt_of_le_of_ne (hle _) fun h => ?_
      rw [h, one_pow, hpn] at he
      exact hp1.ne he
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [map_zero] at hb
      exact not_isUnit_zero hb
    obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
    have hm : m ≠ 0 := by
      rintro rfl
      exact hnb (by rw [pow_zero, _root_.mul_one]; exact u.isUnit)
    have h1 := norm_unit_int p hb
    rw [map_mul, map_pow, Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow,
      norm_unit_int p ((Units.isUnit u).map φ), _root_.one_mul] at h1
    have h2 : ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ ^ m ≤ ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ :=
      pow_le_of_le_one (norm_nonneg _) (hle _) hm
    linarith
  let a' : L := ⟨a, IntermediateField.mem_adjoin_simple_self ℚ_[p] a⟩
  obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := W) a'
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdL : algebraMap W L d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective W L)).2 hd0
  have e1 : algebraMap W L n = a' * algebraMap W L d := by rw [← hnd, div_mul_cancel₀ _ hdL]
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, φ, n, d, hinj, hloc, hd0, ?_⟩
  have e2 := congrArg (fun z : L => algebraMap (PadicAlgCl p) ℂ_[p] (z : PadicAlgCl p)) e1
  simp only [MulMemClass.coe_mul, map_mul] at e2
  exact e2

theorem exists_unif_norm (p : ℕ) [Fact p.Prime] (x : ℂ_[p]) (hx : x ≠ 0) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (ϖ : O) (_ : Irreducible ϖ)
      (φ : O →+* 𝓞_ℂ_[p]) (k : ℤ),
      Function.Injective φ ∧ IsLocalHom φ ∧ ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ ^ k = ‖x‖ := by
  obtain ⟨a, ha⟩ := exists_alg_norm_eq p x hx
  obtain ⟨O, _, _, _, _, φ, n, d, hinj, hloc, hd, hnd⟩ := exists_frac_model p a
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hne : ∀ b : O, b ≠ 0 → ((φ b : 𝓞_ℂ_[p]) : ℂ_[p]) ≠ 0 := fun b hb h =>
    hb (hinj (by rw [map_zero]; exact Subtype.ext h))
  have hxa : (a : ℂ_[p]) ≠ 0 := fun h => hx (norm_eq_zero.1 (ha ▸ (norm_eq_zero.2 h)))
  have hn : n ≠ 0 := by
    rintro rfl
    rw [map_zero, ZeroMemClass.coe_zero] at hnd
    exact mul_ne_zero hxa (hne d hd) hnd.symm
  obtain ⟨m₁, h₁⟩ := norm_eq_unif_pow p hϖ φ hn
  obtain ⟨m₂, h₂⟩ := norm_eq_unif_pow p hϖ φ hd
  have hϖ0 : ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ ≠ 0 := norm_ne_zero_iff.2 (hne ϖ hϖ.ne_zero)
  refine ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, ϖ, hϖ, φ, (m₁ : ℤ) - m₂,
    hinj, hloc, ?_⟩
  have e := congrArg norm hnd
  rw [norm_mul, h₁, h₂, ha] at e
  rw [zpow_sub₀ hϖ0, zpow_natCast, zpow_natCast, e, mul_div_cancel_right₀ _ (pow_ne_zero _ hϖ0)]

end GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

open GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.ValConstOfPowEq in

theorem packSt : PackSt := by
  intro p _ x hx
  obtain ⟨O, _, _, _, _, ϖ, hϖ, φ, k, hinj, hloc, hk⟩ := exists_unif_norm p x hx
  obtain ⟨hI, hN, hP, hF, -, hD, ht⟩ := hyp_spec O
  let f : Spec (.of O) ⟶ Spec (.of O) := 𝟙 _
  let D := trivLB (Spec (.of O))
  let sig : (D.pull (genericι f)).Gen :=
    ⟨fun _ => res le_top (constUnit (genericStr f) (unifUnit ϖ hϖ ^ k))⟩
  have hsig : sig.IsGen := by
    intro i j
    rw [show (D.pull (genericι f)).g i j = 1 from linComb_g_one D (fun _ _ => rfl) _ _ i j, _root_.one_mul]
    exact (res_res' _ _ _).trans (res_res' _ _ _).symm
  have hg : Function.Injective ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ) :=
    (IsFractionRing.injective 𝓞_ℂ_[p] ℂ_[p]).comp hinj
  let ψ : FractionRing O →+* ℂ_[p] := IsFractionRing.lift hg
  let ybar : Spec (.of 𝓞_ℂ_[p]) ⟶ Spec (.of O) := Spec.map (CommRingCat.ofHom φ)
  have hw : (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ ybar) ≫ f =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O))) := by
    simp only [f, ybar, Category.comp_id, ← Spec.map_comp]
    congr 1
    ext a
    simp [ψ, IsFractionRing.lift_algebraMap]
  let y : Spec (.of ℂ_[p]) ⟶ genericFibre f := pullback.lift _ _ hw
  have hy : y ≫ genericι f = Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ ybar :=
    pullback.lift_fst _ _ _
  have hj₀ : ybar ⁻¹ᵁ D.U PUnit.unit = ⊤ := by simp [D, trivLB]
  have htop := top_le_generic D ybar y hy PUnit.unit hj₀
  let cc : ℂ_[p]ˣ := Units.map (Scheme.ΓSpecIso (.of ℂ_[p])).hom.hom.toMonoidHom
    (res htop (pullU y _ (sig.s (fun _ => PUnit.unit))))
  have hcc : (cc : ℂ_[p]) = (algebraMap 𝓞_ℂ_[p] ℂ_[p] (φ ϖ)) ^ k := by
    have e0 : constUnit (genericStr f) (unifUnit ϖ hϖ ^ k) = constUnit (genericStr f) (unifUnit ϖ hϖ) ^ k := by
      simp only [constUnit, map_zpow]
    have e1 : res htop (pullU y _ (sig.s (fun _ => PUnit.unit))) =
        (res (le_top : ⊤ ≤ y ⁻¹ᵁ ⊤) (pullU y ⊤ (constUnit (genericStr f) (unifUnit ϖ hϖ)))) ^ k := by
      show res htop (pullU y _ (res le_top (constUnit (genericStr f) (unifUnit ϖ hϖ ^ k)))) = _
      rw [res_pullU_res', e0, map_zpow, map_zpow]
      all_goals rfl
    show ((Units.map (Scheme.ΓSpecIso (.of ℂ_[p])).hom.hom.toMonoidHom
      (res htop (pullU y _ (sig.s (fun _ => PUnit.unit)))) : ℂ_[p]ˣ) : ℂ_[p]) = _
    rw [e1, map_zpow, Units.val_zpow_eq_zpow_val]
    congr 1
    exact eval_constUnit ϖ hϖ φ ybar (Category.comp_id _) y hy le_top
  refine ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, ϖ, hϖ, Spec (.of O), f, D,
    hI, hN, hP, hF, hD, ht, sig, hsig, φ, hinj, hloc, ybar, y, chartGen D ybar PUnit.unit hj₀, cc,
    Category.comp_id _, hy, chartGen_isGen D hD ybar PUnit.unit hj₀,
    isCoord_chartGen D sig hsig ybar y hy PUnit.unit hj₀, ?_⟩
  rw [hcc, norm_zpow, ← hk]
  rfl

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivPointValuationProperty
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.Frames GlobalTheory.HTLat
open scoped NNReal

namespace GlobalTheory.CompHt

open GlobalTheory.HodgeTateCompare GlobalTheory.EigenLieCompare GlobalTheory.EigenSplit GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel ReciprocityTheory.ChartRestriction.G.Pdiv TensorProduct in

theorem finrank_eigW_embInt_eq_mult : GlobalTheory.CovTop.Hypotheses2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
    [Algebra c.F C] [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), y₀.IsAlg →
    ∀ (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O) (P : Point p v O (𝓞 E))
      (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (z : FrPt Xo c C),
      (letI := io.toAlgebra; PointOver P y₀.1.x k.toRingHom kO ψ) → (letI := io.toAlgebra; FrMap k y₀.1 z) →
      ∀ σ : E →+* ℂ, Module.finrank C (P.eigW (embInt c P.integers σ)) = Dw.mult σ := by
  intro hPr E _ _ _ H Dw l Xo c p _ C _ _ _ v O _ _ _ _ _ _ _ _ _ T io y₀ hy k kO P ψ z hPO hFr σ
  obtain ⟨-, -, hcok, hshape⟩ := GlobalTheory.HTKernel.hodgeTateKernelAtPoint hPr p C v O (𝓞 E) P
  have hW : P.W = Submodule.span C (Set.range P.bLie) := hshape.2.2.2.2.2.2
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v P.integers
  haveI : IsFractionRing O C := P.integers.isFractionRing
  haveI := (GlobalTheory.UnitRigidity.smooth_geometricallyConnected_of_isGt _ _ ⟨P.D⟩).1
  obtain ⟨-, -, hb⟩ := Point.omega_free_finite_bijective p C v O (𝓞 E) P
  have hp : algebraMap O C ((p : O) ^ 2) ≠ 0 := by
    rw [map_pow, map_natCast]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hinj : Function.Injective P.bLie := by
    intro x y hxy
    have h0 : ∀ t, (P.al₀ t).1 x = (P.al₀ t).1 y := fun t => P.integers.hom_inj (by
      rw [← P.pairV_bLie, ← P.pairV_bLie, hxy])
    have h1 : ∀ z, (P.al z).1 x = (P.al z).1 y := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, Submodule.coe_add, Pi.add_apply, hz, hz']
      | tmul c t => simp only [Point.al_tmul, Submodule.coe_smul, Pi.smul_apply, h0]
    refine hb.1 (LinearMap.ext fun f => ?_)
    obtain ⟨z, hz⟩ := hcok f
    have h2 := h1 z
    rw [hz] at h2
    exact mul_left_cancel₀ (fun h => hp (by rw [h, map_zero])) h2
  have hE : P.eigW (embInt c P.integers σ) =
      Submodule.span C (P.wRec (embInt c P.integers σ) : Set P.V) := by
    refine le_antisymm ?_ (Submodule.span_le.2 fun w hw => ?_)
    · rintro w ⟨hw, hwτ⟩
      rw [hW] at hw
      obtain ⟨s, hs, x, hx⟩ := GlobalTheory.HodgeTateEigenRank.exists_smul_mem_of_mem_span (C := C) P.latLie hw
      have hs' : algebraMap O C s ≠ 0 := fun h => hs (P.integers.hom_inj (by rw [h, map_zero]))
      have hxτ : P.bLie x ∈ P.eigV (embInt c P.integers σ) := by
        rw [hx, ← algebraMap_smul C s]
        exact Submodule.smul_mem _ _ hwτ
      have hx' : AvDefs.IsEig P.Gt P.oGt (embInt c P.integers σ) x := fun a => hinj (by
        rw [P.bLie_act, P.bLie_scale, mem_eigenSub.1 hxτ a, RingHom.comp_apply, algebraMap_smul])
      have : w = (algebraMap O C s)⁻¹ • P.bLie x := by
        rw [hx, ← algebraMap_smul C s, smul_smul, inv_mul_cancel₀ hs', one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨x, hx'⟩, rfl⟩)
    · have h := P.wRec_le _ hw
      refine ⟨?_, h.2⟩
      rw [hW]
      exact Submodule.subset_span h.1
  obtain ⟨x, hx⟩ := TieFrame.exists_lieTie_of_frMap E H Dw l Xo c p C v O T io y₀ k kO P ψ z hPO hFr
  have hli := linearIndependent_evLie_of_lieTie E H Dw l Xo c p C v O T io y₀ k kO P ψ z hPO hFr σ (x σ) (hx σ)
  have hht : HTChar p v P.Gt := by
    letI := io.toAlgebra
    exact htChar_of_pointOver E H Dw l Xo c p C v O T io y₀ hy k.toRingHom kO P ψ hPO
  have hbl := (alC_surjective_and_linearIndependent_bLie p C v O (𝓞 E) P hht).2 _ _ hli
  have hsp := RecSpan.span_bLie_eq_wRec E H Dw l Xo c p C v O T io y₀ k kO P ψ z hPO hFr σ (x σ) (hx σ)
  rw [hE, ← hsp, Submodule.span_span_of_tower, finrank_span_eq_card hbl, Fintype.card_fin]

end GlobalTheory.CompHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
section
noncomputable section

namespace GlobalTheory.CovTop.VolUp

open NumberField MeasureTheory Matrix Formalism.BasicNotions GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

def dg {ι : Type} [DecidableEq ι] (a₀ : ι) (z : ℂ) : Matrix ι ι ℂ := Matrix.diagonal (Function.update 1 a₀ z)

def sMat {p q : ℕ} (a₀ : Fin p ⊕ Fin q) (u : UpqT p q) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  UpqT.mat u * dg a₀ (UpqT.mat u).det⁻¹

def permM {ι : Type} {r : ℕ} (e : ι ≃ Fin r) : Matrix ι (Fin r) ℂ := Matrix.of fun i j => if e i = j then 1 else 0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def frBall (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (ε : ℝ) : Set (realSU Ψ G) :=
  {s | ∀ τ a b, ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖ < ε}

def IsIdent {κ : Type} (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ)
    (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) : Prop :=
  ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * A ρ = -(G.map (σ ρ).1)ᵀ ∧ A ρ * mat x (σ ρ) = permM (e ρ)

def IsProj {κ : Type} (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (σ : κ ≃ Ψ)
    (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ))
    (π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G) : Prop :=
  ∀ b ρ, A ρ * (((π b).1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = sMat (a₀ ρ) (b ρ) * A ρ

section Adelic

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Datum GlobalTheory.AdelicScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IsRealPart {D : D7} (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V → ∀ ρ, Upq V ρ) : Prop :=
  ∀ h ρ, UpqT.mat (rp h ρ) * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h

end Adelic

theorem permM_mul_transpose {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin r) : permM e * (permM e)ᵀ = 1 := by
  ext i j
  simp [permM, Matrix.mul_apply, Matrix.one_apply, eq_comm]

theorem transpose_mul_permM {ι : Type} [Fintype ι] (e : ι ≃ Fin r) : (permM e)ᵀ * permM e = 1 := by
  ext i j
  rw [Matrix.mul_apply, ← e.symm.sum_comp]
  simp [permM, Matrix.one_apply, eq_comm]

theorem det_dg {ι : Type} [Fintype ι] [DecidableEq ι] (a₀ : ι) (z : ℂ) : (dg a₀ z).det = z := by
  rw [dg, Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
  simp

end GlobalTheory.CovTop.VolUp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationSectionFirstPower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.MBLow.TrSec

variable {S : Scheme.{0}} (P : PolAV S)

lemma chart_le (j : Fin 1 → P.L.ι) :
    (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver S)).U j ≤ (snd (baseOver S) P.A).left ⁻¹ᵁ P.L.U (j 0) :=
  LB.wchart_le P.L _ j 0

def thSec (s : P.L.Sec) : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver S)) where
  f j := ReciprocityTheory.ChartRestriction.G.DVR.rs (chart_le P j) (((snd (baseOver S) P.A).left.app (P.L.U (j 0))).hom (s.f (j 0)))
  compat i j := by
    refine ReciprocityTheory.ChartRestriction.G.DVR.app_compat_generic (snd (baseOver S) P.A).left (chart_le P i) (chart_le P j)
      (s.f (i 0)) (s.f (j 0)) (P.L.g (i 0) (j 0)) (s.compat _ _) _ ?_
    simp only [LPow, LB.LinComb, Fin.prod_univ_one, Nat.cast_one, zpow_one]
    rfl

lemma projectionPullbackSectionBaseProduct_isInverseImage (s : P.L.Sec) : IsPolAVSectionInverseImage P (baseOver S) s (thSec P s) := by
  intro i h
  rfl

lemma snd_inv (p : P.A.left) : (snd (baseOver S) P.A).left.base ((λ_ P.A).inv.left.base p) = p := by
  have e : (λ_ P.A).inv ≫ snd (baseOver S) P.A = 𝟙 P.A := (λ_ P.A).inv_hom_id
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e]
  rfl

lemma nonzero_thSec (s : P.L.Sec) (p : P.A.left) (hp : p ∈ nonzeroLocus s) :
    (λ_ P.A).inv.left.base p ∈ nonzeroLocus (thSec P s) := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => k, ?_⟩
  have hq : (snd (baseOver S) P.A).left.base ((λ_ P.A).inv.left.base p) = p := snd_inv P p
  show _ ∈ (baseOver S ⊗ P.A).left.basicOpen
    (((baseOver S ⊗ P.A).left.presheaf.map (homOfLE (chart_le P (fun _ => k))).op).hom
      (((snd (baseOver S) P.A).left.app (P.L.U k)).hom (s.f k)))
  rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
  refine ⟨?_, ?_⟩
  · show _ ∈ LB.wchart P.L _ _
    refine Set.mem_iInter.2 fun _ => ?_
    show (snd (baseOver S) P.A).left.base ((λ_ P.A).inv.left.base p) ∈ (P.L.U k : Set P.A.left)
    rw [hq]; exact P.A.left.basicOpen_le _ hk
  · show (snd (baseOver S) P.A).left.base ((λ_ P.A).inv.left.base p) ∈ P.A.left.basicOpen (s.f k)
    rw [hq]; exact hk

end GlobalTheory.MBLow.TrSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesReparamBoundedCoefficients
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem regroup_fib_tsum {X M : Type} [AddCommMonoid M] [TopologicalSpace M] (n : X → ℕ) (i : ℕ)
    (h : {α | n α = i}.Finite) (f : X → M) :
    ∑' b : n ⁻¹' {i}, f b = ∑ α ∈ h.toFinset, f α := by
  have hs : n ⁻¹' {i} = (h.toFinset : Set X) := by ext; simp
  rw [← Finset.tsum_subtype', ← hs]

theorem lattice_series_regroup : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (X : Type) (n : X → ℕ) (π : C) (a : X → C) (b : ℝ), π ≠ 0 → ‖π‖ < 1 → (∀ i, {α | n α = i}.Finite) → (∀ α, ‖a α‖ ≤ b * ‖π‖ ^ n α) → ∃ Θ : PowerSeries C, (∀ i, ‖PowerSeries.coeff i Θ‖ ≤ max b 0) ∧ ∑' i, PowerSeries.coeff i Θ * π ^ i = ∑' α, a α ∧ ∀ (e : C →+* ℂ) (u : ℂ), (Summable fun α => ‖e (a α) * (u / e π) ^ n α‖) → (Summable fun i => ‖e (PowerSeries.coeff i Θ) * u ^ i‖) ∧ ∑' i, e (PowerSeries.coeff i Θ) * u ^ i = ∑' α, e (a α) * (u / e π) ^ n α := by
  intro C _ _ _ X n π a b hπ0 hπ1 hfin hb
  classical
  have hmem : ∀ i α, α ∈ (hfin i).toFinset ↔ n α = i := fun i α => by simp
  have hn : Filter.Tendsto n Filter.cofinite Filter.atTop := by
    refine Filter.tendsto_atTop.2 fun N => Filter.eventually_cofinite.2 ?_
    refine ((Set.finite_lt_nat N).biUnion fun i _ => hfin i).subset ?_
    intro α hα
    simp only [Set.mem_setOf_eq, not_le] at hα
    exact Set.mem_biUnion (x := n α) hα rfl
  have hpow : Filter.Tendsto (fun α => b * ‖π‖ ^ n α) Filter.cofinite (nhds 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg π) hπ1).comp hn).const_mul b
  have ha0 : Filter.Tendsto a Filter.cofinite (nhds 0) := squeeze_zero_norm hb hpow
  have ha : Summable a := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ha0
  refine ⟨PowerSeries.mk fun i => ∑ α ∈ (hfin i).toFinset, a α / π ^ i, ?_, ?_, ?_⟩
  · intro i
    rw [PowerSeries.coeff_mk]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (le_max_right _ _) fun α hα => ?_
    have hpi : 0 < ‖π‖ ^ i := pow_pos (norm_pos_iff.2 hπ0) _
    rw [norm_div, norm_pow, div_le_iff₀ hpi]
    have := hb α
    rw [(hmem i α).1 hα] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpi.le)
  · rw [← ((ha.hasSum.tsum_fiberwise n).tsum_eq)]
    refine tsum_congr fun i => ?_
    rw [PowerSeries.coeff_mk, regroup_fib_tsum n i (hfin i), Finset.sum_mul]
    exact Finset.sum_congr rfl fun α _ => div_mul_cancel₀ _ (pow_ne_zero _ hπ0)
  · intro e u hsum
    have heπ : e π ≠ 0 := (map_ne_zero e).2 hπ0
    have hkey : ∀ i, e (PowerSeries.coeff i (PowerSeries.mk fun i => ∑ α ∈ (hfin i).toFinset, a α / π ^ i)) * u ^ i
        = ∑ α ∈ (hfin i).toFinset, e (a α) * (u / e π) ^ n α := by
      intro i
      rw [PowerSeries.coeff_mk, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [(hmem i α).1 hα, map_div₀, map_pow, div_pow]
      field_simp
    simp_rw [hkey]
    have hf : Summable fun α => e (a α) * (u / e π) ^ n α := hsum.of_norm
    refine ⟨?_, ?_⟩
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => norm_sum_le _ _) ?_
      have := (hsum.hasSum.tsum_fiberwise n).summable
      exact this.congr fun i => regroup_fib_tsum n i (hfin i) (fun α => ‖e (a α) * (u / e π) ^ n α‖)
    · rw [← ((hf.hasSum.tsum_fiberwise n).tsum_eq)]
      exact tsum_congr fun i => (regroup_fib_tsum n i (hfin i) _).symm

end GlobalTheory.MBLow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLocalApproximationStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_local_approximation : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) →
    ∀ t : E →ₐ[F] Fv F v, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₀ ∈ G.M'.SoLoc B.ψ t, φ - φ₀ ∈ augAt om' v := by
  first | exact @GlobalTheory.RankCoinv.exists_soLoc_sub_mem_augAt | exact GlobalTheory.RankCoinv.exists_soLoc_sub_mem_augAt | (intros; apply GlobalTheory.RankCoinv.exists_soLoc_sub_mem_augAt <;> assumption)
end

