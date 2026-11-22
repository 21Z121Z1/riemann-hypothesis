import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0885
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0883
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianMeasureLieAlgebraEqSmulMapChartLebesgu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0878
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0869
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0379
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0750
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationBoundOverDvr
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

namespace GlobalTheory.PlaceLocalRing

section

variable {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {O : Type} [CommRing O] {β : O →+* K}

theorem exists_unit (hinj : Function.Injective β) (hr : ∀ x : K, x ∈ Set.range β ↔ la.valuation K x ≤ 1)
    {x : K} (hx : la.valuation K x = 1) : ∃ u : Oˣ, β u = x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨a, ha⟩ := (hr x).2 hx.le
  obtain ⟨c, hc⟩ := (hr x⁻¹).2 (by rw [map_inv₀, hx, inv_one])
  have : IsUnit a := IsUnit.of_mul_eq_one c (hinj (by rw [map_mul, ha, hc, mul_inv_cancel₀ hx0, map_one]))
  exact ⟨this.unit, ha⟩

theorem exists_unit_mul_zpow (hinj : Function.Injective β) (hr : ∀ x : K, x ∈ Set.range β ↔ la.valuation K x ≤ 1)
    {p : K} (hp : la.valuation K p = WithZero.exp (-1 : ℤ)) {x : K} (hx : x ≠ 0) :
    ∃ u : Oˣ, x = β u * p ^ vLa la x := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  have hv : la.valuation K x ≠ 0 := by simpa using hx
  obtain ⟨u, hu⟩ := exists_unit hinj hr (x := x * p ^ (-vLa la x)) (by
    rw [map_mul, map_zpow₀, hp, ← WithZero.exp_zsmul, ← WithZero.exp_log hv, ← WithZero.exp_add]
    simp [vLa])
  refine ⟨u, ?_⟩
  rw [hu, mul_assoc, ← zpow_add₀ hp0]
  simp

theorem vLa_nonneg (hr : ∀ x : K, x ∈ Set.range β ↔ la.valuation K x ≤ 1) {a : O} (ha : β a ≠ 0) :
    0 ≤ vLa la (β a) := by
  have hv : la.valuation K (β a) ≠ 0 := by simpa using ha
  have h := (hr _).1 ⟨a, rfl⟩
  rw [← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  simp only [vLa]
  omega

theorem irreducible_of_valuation (hinj : Function.Injective β)
    (hr : ∀ x : K, x ∈ Set.range β ↔ la.valuation K x ≤ 1)
    {π : O} (hp : la.valuation K (β π) = WithZero.exp (-1 : ℤ)) : Irreducible π := by
  have hle : ∀ a : O, la.valuation K (β a) ≤ 1 := fun a => (hr _).1 ⟨a, rfl⟩
  have hun : ∀ a : O, la.valuation K (β a) = 1 → IsUnit a := fun a ha => by
    obtain ⟨u, hu⟩ := exists_unit hinj hr ha
    exact hinj hu ▸ u.isUnit
  refine ⟨fun h => ?_, fun a c h => ?_⟩
  · obtain ⟨c, hc⟩ := h.exists_right_inv
    have h1 : la.valuation K (β π) * la.valuation K (β c) = 1 := by
      rw [← map_mul, ← map_mul, hc, map_one, map_one]
    have h2 : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (-1 : ℤ) := by
      calc (1 : WithZero (Multiplicative ℤ)) = _ := h1.symm
        _ ≤ la.valuation K (β π) * 1 := by gcongr; exact hle c
        _ = _ := by rw [mul_one, hp]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h2
    omega
  · rw [h, map_mul, map_mul] at hp
    have h0 := mul_ne_zero_iff.1 (hp.trans_ne WithZero.exp_ne_zero)
    have ha := hle a
    have hc := hle c
    rw [← WithZero.exp_log h0.1, ← WithZero.exp_zero, WithZero.exp_le_exp] at ha
    rw [← WithZero.exp_log h0.2, ← WithZero.exp_zero, WithZero.exp_le_exp] at hc
    rw [← WithZero.exp_log h0.1, ← WithZero.exp_log h0.2, ← WithZero.exp_add, WithZero.exp_inj] at hp
    by_cases h1 : WithZero.log (la.valuation K (β a)) = 0
    · exact Or.inl (hun a (by rw [← WithZero.exp_log h0.1, h1, WithZero.exp_zero]))
    · exact Or.inr (hun c (by
        rw [← WithZero.exp_log h0.2, show WithZero.log (la.valuation K (β c)) = 0 by omega, WithZero.exp_zero]))

end

theorem dvr_and_overLa : ∀ (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (O : Type) [CommRing O] (β : O →+* K), Function.Injective β → (∀ x : K, x ∈ Set.range β ↔ la.valuation K x ≤ 1) → ∃ (_ : IsDomain O) (_ : IsDiscreteValuationRing O), (letI := β.toAlgebra; IsFractionRing O K) ∧ ∀ (T : CDVR) (io : K →+* T.Fr) (b : O →+* T.V), IsLocalHom b → (algebraMap T.V T.Fr).comp b = io.comp β → ∃ e : ℕ, OverLa la T.V io e := by
  intro K _ _ la O _ β hinj hr
  obtain ⟨p, hp⟩ := la.valuation_exists_uniformizer K
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  obtain ⟨π, rfl⟩ := (hr p).2 (by
    rw [hp, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have hπ := irreducible_of_valuation hinj hr hp
  have hdom : IsDomain O := hinj.isDomain β
  have hdvr : IsDiscreteValuationRing O :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨π, hπ, fun {x} hx => by
      have hx' : β x ≠ 0 := (map_ne_zero_iff β hinj).2 hx
      obtain ⟨u, hu⟩ := exists_unit_mul_zpow hinj hr hp hx'
      have h0 := vLa_nonneg hr hx'
      refine ⟨(vLa la (β x)).toNat, u, hinj ?_⟩
      rw [map_mul, map_pow, ← zpow_natCast, Int.toNat_of_nonneg h0, mul_comm, ← hu]⟩
  refine ⟨hdom, hdvr, ?_, ?_⟩
  · letI := β.toAlgebra
    haveI : FaithfulSMul O K := (faithfulSMul_iff_algebraMap_injective O K).2 hinj
    refine IsFractionRing.of_field O K fun x => ?_
    rcases le_total (la.valuation K x) 1 with h | h
    · obtain ⟨a, ha⟩ := (hr x).2 h
      exact ⟨a, 1, by rw [map_one, div_one]; exact ha.symm⟩
    · obtain ⟨a, ha⟩ := (hr x⁻¹).2 (by rw [map_inv₀]; exact inv_le_one_of_one_le₀ h)
      exact ⟨1, a, by rw [map_one, one_div]; change x = (β a)⁻¹; rw [ha, inv_inv]⟩
  · intro T io b hb hc
    have hc' : ∀ a, io (β a) = algebraMap T.V T.Fr (b a) := fun a => (RingHom.congr_fun hc a).symm
    have hlt : valV T.V (io (β π)) < 1 := by
      rw [hc']
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 fun h => hπ.not_isUnit (isUnit_of_map_unit b _ h)
    have hne : valV T.V (io (β π)) ≠ 0 := valV_ne_zero ((map_ne_zero io).2 hp0)
    have hpos : 0 < vV T.V (io (β π)) := by
      rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      simp only [vV]
      omega
    refine ⟨(vV T.V (io (β π))).toNat, by omega, fun a => ?_⟩
    by_cases ha : a = 0
    · simp [ha, vV, vLa]
    obtain ⟨u, hu⟩ := exists_unit_mul_zpow hinj hr hp ha
    have h1 : valV T.V (io (β u)) = 1 := by
      rw [hc']
      refine le_antisymm (HeightOneSpectrum.valuation_le_one _ _) (not_lt.mp fun h => ?_)
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).1 h (u.isUnit.map b)
    rw [Int.toNat_of_nonneg hpos.le]
    generalize vLa la a = n at hu
    rw [hu]
    simp only [vV, map_mul, map_zpow₀, h1, one_mul, WithZero.log_zpow]
    simp [mul_comm]

end GlobalTheory.PlaceLocalRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannRelationConverseConjAffineStatement
section
open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_relation_converse_conjAffine : ∀ {g : ℕ} (M₀ C : Matrix (Fin g) (Fin g) ℂ), M₀ᴴ = M₀ → M₀.det ≠ 0 → (Cᵀ * M₀)ᵀ = Cᵀ * M₀ → (1 - C.map star * C).det ≠ 0 → (M₀ * (1 - C.map star * C)⁻¹)ᴴ = M₀ * (1 - C.map star * C)⁻¹ ∧ ∀ z w : Fin g → ℂ, (hermForm (M₀ * (1 - C.map star * C)⁻¹) (z + C *ᵥ star z) (w + C *ᵥ star w)).im = (hermForm M₀ z w).im := by
  first | exact @GlobalTheory.PeriodCoord.riemann_converse | exact GlobalTheory.PeriodCoord.riemann_converse | (intros; apply GlobalTheory.PeriodCoord.riemann_converse; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieVolumeFormulaStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannian_lie_volume_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Λ : Submodule (𝓞 E) (Fin r → E)) (x : Frame X.Ψ r) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), 2 ≤ r → Unr E → SelfDualLat X.Gm Λ → IsOrth X x → (∀ i, e i ∈ lieLat X.Gm Λ) → LinearIndependent (maximalRealSubfield E) e → riemLie X.Ψ X.Gm x = ENNReal.ofReal (Real.sqrt r ^ fdeg E * ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat X.Gm Λ) : ℝ)) • formLie X.Ψ e := by
  first | exact @GlobalTheory.LieCovol.riemLie_eq_sqrt_index_smul_formLie | exact GlobalTheory.LieCovol.riemLie_eq_sqrt_index_smul_formLie | (intros; apply GlobalTheory.LieCovol.riemLie_eq_sqrt_index_smul_formLie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianMeasureLieAlgebraEqSmulMapChartLebesguStatement
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianMeasure_lieAlgebra_eq_smul_map_chartLebesgue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), 1 ≤ r → IsOrth X x → ∀ D : ChartSp X →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ), (∀ w : ChartSp X, D w ∈ realLie X.Ψ X.Gm ∧ (∀ τ a b, b < a → inFrame x (D w) τ a b = nmat X w.1 τ a b) ∧ ∀ τ a, inFrame x (D w) τ a a = Complex.I * (angles (w.2 τ) a : ℂ)) → Function.Injective D ∧ riemLie X.Ψ X.Gm x = ENNReal.ofReal (2 ^ nd X * Real.sqrt r ^ X.Ψ.card) • (volume : Measure (ChartSp X)).map D := by
  first | exact @GlobalTheory.RiemConst.Jac.riemLie_eq_smul_map | exact GlobalTheory.RiemConst.Jac.riemLie_eq_smul_map | (intros; apply GlobalTheory.RiemConst.Jac.riemLie_eq_smul_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomCharacterEndOfTorusExtensionAction
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory
namespace TorusActRing

theorem chV_id_eq {k : Type} [Field k] (X : Type) [AddCommGroup X] (χ : X) :
    chV (𝟙 (splitTorus (Sp k) X)) χ = charUnit (Sp k) X χ := by
  ext1
  rw [chV_val]
  simp

theorem charUnit_add' {k : Type} [Field k] (X : Type) [AddCommGroup X] (χ ψ : X) :
    charUnit (Sp k) X (χ + ψ) = charUnit (Sp k) X χ * charUnit (Sp k) X ψ := by
  rw [← chV_id_eq, ← chV_id_eq, ← chV_id_eq, chV_add]

end TorusActRing

theorem ringHom_charEnd_of_torusExtension : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (E : TorusExtension G) (O : Type) [Ring O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → letI := E.addCommGroup; ∃ ρ : O →+* Module.End ℤ E.X, ∀ a, ∃ τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X, τ ≫ E.i = E.i ≫ act a ∧ ∀ χ, chV τ χ = charUnit (Sp k) E.X (ρ a χ) := by
  intro k _ G _ _ E O _ act hmon h1 hmul hadd
  letI := E.addCommGroup
  have hex := fun a => GlobalTheory.TorusEndChar.main k G E (act a) (hmon a)
  choose ρ₀ hρ₀ using fun a => (hex a).exists
  have uniq : ∀ a (σ : E.X →+ E.X) (τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X),
      τ ≫ E.i = E.i ≫ act a → (∀ χ, chV τ χ = charUnit (Sp k) E.X (σ χ)) → σ = ρ₀ a :=
    fun a σ τ e₁ e₂ => (hex a).unique ⟨τ, e₁, e₂⟩ (hρ₀ a)
  have compχ : ∀ (σ : E.X →+ E.X) (τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X),
      (∀ χ, chV τ χ = charUnit (Sp k) E.X (σ χ)) → ∀ (Z : Over (Sp k)) (s : Z ⟶ splitTorus (Sp k) E.X) χ,
      chV (s ≫ τ) χ = chV s (σ χ) :=
    fun σ τ hτ Z s χ => ((splitTorus_map_of_charHom (Sp k) E.X E.X σ).2 τ hτ).2.2 Z s χ
  have one : ρ₀ 1 = AddMonoidHom.id _ := by
    refine (uniq 1 (AddMonoidHom.id _) (𝟙 _) ?_ (fun χ => ?_)).symm
    swap
    · rw [AddMonoidHom.id_apply]; exact TorusActRing.chV_id_eq E.X χ
    rw [h1, Category.id_comp, Category.comp_id]
  have mul : ∀ a b, ρ₀ (a * b) = (ρ₀ a).comp (ρ₀ b) := by
    intro a b
    obtain ⟨τa, ha1, ha2⟩ := hρ₀ a
    obtain ⟨τb, hb1, hb2⟩ := hρ₀ b
    refine (uniq (a * b) _ (τa ≫ τb) ?_ ?_).symm
    · rw [Category.assoc, hb1, ← Category.assoc, ha1, Category.assoc, hmul]
    · intro χ
      rw [compχ _ τb hb2, ha2]
      rfl
  have add : ∀ a b, ρ₀ (a + b) = ρ₀ a + ρ₀ b := by
    intro a b
    obtain ⟨τa, ha1, ha2⟩ := hρ₀ a
    obtain ⟨τb, hb1, hb2⟩ := hρ₀ b
    haveI := E.i_hom
    refine (uniq (a + b) _ (τa * τb) ?_ ?_).symm
    · rw [MonObj.mul_comp, ha1, hb1, hadd, Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]
    · intro χ
      rw [chV_mul, ha2, hb2, AddMonoidHom.add_apply, TorusActRing.charUnit_add']
  have zero : ρ₀ 0 = 0 := by
    have := add 0 0
    rw [add_zero] at this
    simpa using this
  refine ⟨{ toFun := fun a => (ρ₀ a).toIntLinearMap
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun a => ?_⟩
  · ext x; simp [one]
  · intro a b; ext x; simp [mul]
  · ext x; simp [zero]
  · intro a b; ext x; simp [add]
  · obtain ⟨τ, e₁, e₂⟩ := hρ₀ a
    exact ⟨τ, e₁, fun χ => e₂ χ⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowLevelPrincipalFirstBlockIndexEqCardStatement
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowLevel_principal_firstBlock_index_eq_card : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (P : LevFam X.E X.K R.r Pr.vGs), ∃ ι : (mtildeKGSD W Ch sel mu).G →* (mtildeGSD W Ch sel mu P).G, Function.Injective ι ∧ (∀ (a : (mtildeKGSD W Ch sel mu).G) (d : (mtildeKGSD W Ch sel mu).D), ι a • d = a • d) ∧ ι.range.index = Nat.card P.grp := by
  first | exact @GlobalTheory.RowLevIndex.index_eq | exact GlobalTheory.RowLevIndex.index_eq | (intros; apply GlobalTheory.RowLevIndex.index_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzRapidDecayColumn
section
noncomputable section

open Classical MeasureTheory NumberField

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

theorem isRapidInf_colU : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (r : ℕ)
    (f : SchwartzMap (Fin a → GlobalTheory.CuspRep.Cinf E) ℂ),
    GlobalTheory.JSW.IsRapidInf (volume : Measure (Fin a → GlobalTheory.CuspRep.Cinf E)) (fun x => f x) (GlobalTheory.JSW.colU r) := by
  intro E _ _ _ a r f
  haveI : (volume : Measure (Fin a → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hc : Continuous fun x : Fin a → Cinf E => toL (colU r x).val := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous fun x : Fin a → Cinf E =>
      (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j + (if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0)
    split_ifs
    · exact continuous_const.add (continuous_apply i)
    · exact continuous_const.add continuous_const
  have hci : Continuous fun x : Fin a → Cinf E => toL ((colU r x)⁻¹).val := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous fun x : Fin a → Cinf E =>
      (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j - (if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0)
    split_ifs
    · exact continuous_const.sub (continuous_apply i)
    · exact continuous_const.sub continuous_const
  set c₁ : ℝ := ‖(1 : Cinf E)‖
  have hent : ∀ (s : Cinf E) (x : Fin a → Cinf E), ‖s‖ ≤ 1 →
      ‖toL ((1 : Matrix (Fin a) (Fin a) (Cinf E)) + Matrix.of
        (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then s * x i else 0))‖ ≤ c₁ + ‖x‖ := by
    intro s x hs
    refine pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun i => pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun j => ?_
    change ‖(1 : Matrix (Fin a) (Fin a) (Cinf E)) i j + (if (j : ℕ) = r ∧ (i : ℕ) < r then s * x i else 0)‖ ≤ _
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [Matrix.one_apply]; split_ifs
      · exact le_rfl
      · simp [c₁]
    · split_ifs
      · exact (norm_mul_le _ _).trans ((mul_le_mul hs (norm_le_pi_norm x i) (norm_nonneg _) zero_le_one).trans (by simp))
      · simp
  have hH : ∀ x : Fin a → Cinf E, height (colU r x) ≤ (1 + 2 * c₁) + 2 * ‖x‖ := by
    intro x
    have e1 : (colU r x).val = (1 : Matrix (Fin a) (Fin a) (Cinf E)) + Matrix.of
        (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then (1 : Cinf E) * x i else 0) := by
      simp [colU]
    have e2 : ((colU r x)⁻¹).val = (1 : Matrix (Fin a) (Fin a) (Cinf E)) + Matrix.of
        (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then (-1 : Cinf E) * x i else 0) := by
      change 1 - _ = _
      rw [sub_eq_add_neg]
      congr 1
      ext i j w
      simp only [Matrix.neg_apply, Matrix.of_apply]
      split_ifs <;> simp
    have n1 : ‖(-1 : Cinf E)‖ ≤ 1 := by
      rw [norm_neg]; exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => by simp
    have n0 : ‖(1 : Cinf E)‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => by simp
    unfold height
    rw [e1, e2]
    linarith [hent 1 x n0, hent (-1) x n1]
  refine ⟨f.continuous.measurable, ?_, fun N => ?_⟩
  · refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    exact ((continuous_apply j).comp ((continuous_apply i).comp hc)).measurable
  · set A : ℝ := 1 + 2 * c₁
    have hA : 0 ≤ A := by positivity
    have hdom : Integrable fun x : Fin a → Cinf E => (A + 2 * ‖x‖) ^ N * ‖f x‖ := by
      have e : (fun x : Fin a → Cinf E => (A + 2 * ‖x‖) ^ N * ‖f x‖) = fun x =>
          ∑ m ∈ Finset.range (N + 1), (2 ^ m * A ^ (N - m) * (N.choose m : ℝ)) * (‖x‖ ^ m * ‖f x‖) := by
        funext x
        rw [add_comm, add_pow, Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [mul_pow]; ring
      rw [e]
      exact integrable_finset_sum _ fun m _ => (f.integrable_pow_mul volume m).const_mul _
    have hht : Continuous fun x : Fin a → Cinf E => height (colU r x) := by
      unfold height
      exact (continuous_const.add hc.norm).add hci.norm
    refine Integrable.mono' hdom ((f.continuous.norm.mul (hht.pow N)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    have h1 : 1 ≤ height (colU r x) := one_le_height _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (hH x) N) (norm_nonneg _)

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallAffineBasisAndTransitionUnitsLiftStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_affine_basis_and_transition_units_lift : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (X X₀ : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (L : LB X₀), IsThick I s i → L.IsLB → IsBasis (smallG i L) ∧ (∃ u, IsLift s i L u) ∧ ∀ u, IsLift s i L u → (∀ t t' a, IsUnit (u t t' a)) ∧ In2 I _ (mdef _ u) ∧ ∀ u', In1 I _ (u' - u) → IsLift s i L u' := by
  first | exact @GlobalTheory.LBLift.small_basis_lift | exact GlobalTheory.LBLift.small_basis_lift | (intros; apply GlobalTheory.LBLift.small_basis_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallOfSeparatedPresheafOpenCharts
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem small_of_separated_of_open_charts : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type 1), (∀ (T : Scheme.{0}) (y y' : F.obj (op T)), (∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧ F.map z.op y = F.map z.op y') → y = y') → ∀ (Ix : Type) (U : Ix → Scheme.{0}) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (T : Scheme.{0}) (y : F.obj (op T)), ∃ W : T.Opens, ∀ (Y : Scheme.{0}) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W) → (∀ (T : Scheme.{0}) (y : F.obj (op T)) (p : T), ∃ (i : Ix) (Y : Scheme.{0}) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a ∧ F.map a.op y = F.map u.op (x i)) → ∀ T : Scheme.{0}ᵒᵖ, Small.{0} (F.obj T) := by
  intro F hsep Ix U x hchart hcov T
  let S : F.obj T → Set (Σ (i : Ix) (V : T.unop.Opens), (V.toScheme ⟶ U i)) :=
    fun y => {q | F.map q.2.1.ι.op y = F.map q.2.2.op (x q.1)}
  refine small_of_injective (f := S) ?_
  intro y y' h
  apply hsep T.unop y y'
  intro p
  obtain ⟨i, Y, a, u, hp, ha⟩ := hcov T.unop y p
  obtain ⟨W, hW⟩ := hchart i T.unop y
  have hpW : p ∈ W := by
    obtain ⟨q, rfl⟩ := hp
    exact (hW Y a).1 ⟨u, ha⟩ q
  obtain ⟨u', hu'⟩ := (hW W.toScheme W.ι).2 (fun q => by
    have hq : W.ι q ∈ Set.range W.ι := Set.mem_range_self q
    rwa [W.range_ι] at hq)
  have hmem : (⟨i, W, u'⟩ : Σ (i : Ix) (V : T.unop.Opens), (V.toScheme ⟶ U i)) ∈ S y := hu'
  rw [h] at hmem
  refine ⟨W.toScheme, W.ι, inferInstance, ?_, ?_⟩
  · rw [W.range_ι]; exact hpW
  · exact hu'.trans hmem.symm

end GlobalTheory.PicGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveDegreeTwoClassDiesOnPrincipalOp
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem smoothAffineCurve_degreeTwo_class_dies_on_principalOpen : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k]
    [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) →
    ∀ (i : ℤ) (x : Ht q (sp B) 2 i), ∃ f : B, f ≠ 0 ∧
      pull _ (spMap (algebraMap B (Localization.Away f))) _ _ x = 0 := by
  intro q _ k B _ _ _ _ _ _ hq i x
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  by_cases hB : IsField B
  · have hSH : SH B := GlobalTheory.T.sH_of_isField_finiteType_of_isAlgClosed k B hB
    haveI : Subsingleton (Ht q (sp B) 2 i) := GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) B hSH (tw q i) 2 (by norm_num)
    refine ⟨1, one_ne_zero, ?_⟩
    rw [Subsingleton.elim x 0, map_zero]
  · obtain ⟨inst, halg⟩ := GlobalTheory.T.exists_isAlgebraic_ratFunc_fractionRing_dedekind k B hB
    letI := inst
    haveI := halg
    have hqK : IsUnit (q : FractionRing B) := by simpa using hqB.map (algebraMap B (FractionRing B))
    haveI : Subsingleton (Ht q (sp (FractionRing B)) 2 i) :=
      GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc q k (FractionRing B) hqK 2 i le_rfl
    obtain ⟨f, hf, -, hx⟩ := GlobalTheory.T.class_vanishes_away_nonzero_nonunit_domain q B hB hqB 2 i x (Subsingleton.elim _ _)
    exact ⟨f, hf, hx⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionTensorObjDual
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.TensorDualDim

theorem finrank_dual_eq (O X : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Projective O X] :
    Module.finrank O (Module.Dual O X) = Module.finrank O X := by
  haveI : Module.FinitePresentation O X := Module.finitePresentation_of_projective O X
  let F := FractionRing O
  let f : X →ₗ[O] F ⊗[O] X := TensorProduct.mk O F X 1
  have h1 := IsLocalizedModule.finrank_eq (nonZeroDivisors O) f le_rfl
  let g := IsLocalizedModule.map (nonZeroDivisors O) f (Algebra.linearMap O F)
  have h2 := IsLocalizedModule.finrank_eq (nonZeroDivisors O) g le_rfl
  rw [← h1, ← h2, ← IsLocalization.finrank_eq F (nonZeroDivisors O) le_rfl,
    ← IsLocalization.finrank_eq F (nonZeroDivisors O) le_rfl,
    (LinearMap.extendScalarsOfIsLocalizationEquiv (nonZeroDivisors O) F).finrank_eq]
  exact Subspace.dual_finrank_eq

theorem smoothOfRelativeDimension_tensorObj_dual : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] (a : OAct O B) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (g : ℕ), SmoothOfRelativeDimension g B.hom → SmoothOfRelativeDimension (Module.finrank O X * g) (tensorObj (Module.Dual O X) a).hom := by
  intro S B _ _ O _ _ _ a X _ _ _ _ g hg
  have h := GlobalTheory.SerreDim.smoothOfRelativeDimension_tensor S O (Module.Dual O X) B
    (tensorObj (Module.Dual O X) a) a (tensorAct (Module.Dual O X) a) g
    ⟨GlobalTheory.Serre.isTensor (Module.Dual O X) a⟩ hg
  rwa [finrank_dual_eq] at h

end GlobalTheory.TensorDualDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharFiniteSuperDiagonalSumIntegral
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

namespace GlobalTheory.WhitBump

theorem psiFin_superDiag_eq_one_of_integral : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ)
    (u : GL (Fin n) (Af E)), u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n) →
    u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n → psiFin (GlobalTheory.Whittaker.superDiag u) = 1 := by
  intro E _ _ _ n u _ hk
  have hent := ((GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E n).1 hk).1
  have hs : GlobalTheory.Whittaker.superDiag u ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
    unfold GlobalTheory.Whittaker.superDiag
    exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => hent i j
  have hd : sFin E (GlobalTheory.Whittaker.superDiag u) ∈ GroundTheory.Global.invDifferentAdeles E :=
    GroundTheory.Global.mem_invDifferentAdeles.mpr
      (GroundTheory.Global.mem_finiteInvDifferent_of_mem_integralFiniteAdeles hs)
  unfold psiFin
  rw [GroundTheory.Global.adelicChar_of_mem_invDifferentAdeles hd]
  have h0 : (sFin E (GlobalTheory.Whittaker.superDiag u)).1 = 0 := rfl
  rw [h0, map_zero, neg_zero, AddChar.map_zero_eq_one]
  simp

end GlobalTheory.WhitBump
end

