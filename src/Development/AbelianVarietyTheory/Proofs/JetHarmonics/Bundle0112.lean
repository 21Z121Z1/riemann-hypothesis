import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsWeightBasisFiltration
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0108
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0004
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0008
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomTA
import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ParabolicPointMembership
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0104
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0013
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0099

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralTypesAndDirections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

theorem exists_lift_ringOfIntegers {E : Type} [Field E] [NumberField E] {V K : Type} [CommRing V] [IsDomain V]
    [IsIntegrallyClosed V] [Field K] [Algebra V K] [IsFractionRing V K] (φ : 𝓞 E →+* K) :
    ∃ ψ : 𝓞 E →+* V, ∀ a, algebraMap V K (ψ a) = φ a := by
  have hint : ∀ a, ∃ x : V, algebraMap V K x = φ a := by
    intro a
    have h1 : IsIntegral ℤ a := Algebra.IsIntegral.isIntegral a
    have h2 : IsIntegral ℤ (φ a) := map_isIntegral_int φ h1
    exact IsIntegrallyClosed.isIntegral_iff.1 h2.tower_top
  choose f hf using hint
  have hinj := IsFractionRing.injective V K
  refine ⟨{ toFun := f
            map_one' := hinj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => hinj (by rw [map_mul, hf, hf, hf, map_mul])
            map_zero' := hinj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => hinj (by rw [map_add, hf, hf, hf, map_add]) }, hf⟩

theorem exists_dual_of_extends {V : Type} [CommRing V] {d r : ℕ} (u : Fin r → Fin d → V)
    (w : Fin d → Fin d → V) (emb : Fin r ↪ Fin d) (hw : ∀ i, w (emb i) = u i)
    (hb : ∀ x : Fin d → V, ∃! a : Fin d → V, ∀ j, ∑ k, a k * w k j = x j) :
    ∃ lam : Fin r → Fin d → V, ∀ i i', ∑ s, lam i s * u i' s = if i = i' then 1 else 0 := by
  have hsurj : Function.Surjective (Matrix.of w).vecMul := by
    intro x
    obtain ⟨a, ha, -⟩ := hb x
    exact ⟨a, funext fun j => by simpa [Matrix.vecMul, dotProduct] using ha j⟩
  have hU : IsUnit (Matrix.of w) := Matrix.vecMul_surjective_iff_isUnit.1 hsurj
  obtain ⟨N, hN⟩ := hU.exists_right_inv
  refine ⟨fun i s => N s (emb i), fun i i' => ?_⟩
  have h := congrFun (congrFun hN (emb i')) (emb i)
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  simp only [Matrix.of_apply, hw, EmbeddingLike.apply_eq_iff_eq] at h
  simp only [mul_comm (N _ _), h, eq_comm]

theorem isUnit_Ov_iff {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (x : TWO.Ov v) :
    IsUnit x ↔ ¬ 0 < v (x : F) := by
  constructor
  · rintro ⟨u, rfl⟩
    rw [TWO.v_unit]
    exact lt_irrefl _
  · intro h
    have hx : (x : F) ≠ 0 := by
      intro h0
      apply h
      rw [h0, AddValuation.map_zero]
      exact WithTop.coe_lt_top (0 : ℚ)
    have hi : (x : F)⁻¹ ∈ TWO.Ov v := by
      refine TWO.exists_weight_basis_filtration (a := v (x : F)) ?_ (not_lt.1 h)
      rw [← AddValuation.map_mul, mul_inv_cancel₀ hx, AddValuation.map_one]
    exact IsUnit.of_mul_eq_one (⟨_, hi⟩ : TWO.Ov v) (Subtype.ext (mul_inv_cancel₀ hx))

theorem exists_integral_types_and_directions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (ϖ : T.V), Irreducible ϖ → ∀ (g : ℕ), g.Prime → ¬ IsUnit ((g : ℕ) : T.V) → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup → ∀ (F : Type) [Field F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → letI := io.toAlgebra; ∃ (σ : (E →+* ℂ) → 𝓞 E →+* TWO.Ov v) (e : Lt1 Dw → Fin (chD C.ch) → TWO.Ov v), (∀ τ a, (σ τ a : F) = algebraMap T.Fr F (io (embK c τ a))) ∧ (∀ ℓ i, (e ℓ i : F) = algebraMap T.V F (C.uvecT ℓ i)) ∧ (∀ ℓ i, (e ℓ i : F) = algebraMap T.Fr F (C.ch.uvec ℓ i)) ∧ (∀ (a : 𝓞 E) ℓ, (dAct F C.ch.B a).mulVec (fun i => (e ℓ i : F)) = (σ ℓ.1 a : F) • fun i => (e ℓ i : F)) ∧ (∀ τ a, (0 < v (σ τ a : F) → σ τ a ∈ Ideal.span {((g : ℕ) : TWO.Ov v)}) ∧ (¬ 0 < v (σ τ a : F) → IsUnit (σ τ a))) ∧ (∀ τ a, σ (ComplexEmbedding.conjugate τ) a = σ τ (star a)) ∧ (open Classical in ∃ lam : Lt1 Dw → Fin (chD C.ch) → TWO.Ov v, ∀ l l', ∑ s, lam l s * e l' s = if l = l' then 1 else 0) ∧ (open Classical in ∃ ε : (E →+* ℂ) → 𝓞 E, ∀ τ τ', σ τ' (ε τ) - (if τ = τ' then 1 else 0) ∈ Ideal.span {((g : ℕ) : TWO.Ov v)}) ∧ ¬ IsUnit ((g : ℕ) : TWO.Ov v) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C ϖ hϖ g hg hgu hcard hnd F _ _ _ _ _ v hv
  letI := io.toAlgebra
  classical
  have hfrob := GlobalTheory.pow_sub_self_mem_span_of_splits_completely E g hg hcard hnd
  have hinj := IsFractionRing.injective T.V T.Fr
  choose σV hσV using fun τ : E →+* ℂ => exists_lift_ringOfIntegers (V := T.V) (io.comp (embK c τ))
  have hσV' : ∀ τ a, algebraMap T.V T.Fr (σV τ a) = io (embK c τ a) := hσV
  have huv : ∀ ℓ i, C.ch.uvec ℓ i = algebraMap T.V T.Fr (C.uvecT ℓ i) := C.gen.1.2.2.2.2.2.2
  have hact : ∀ a j, C.ch.B.A.act a j = MvPowerSeries.map (algebraMap T.V T.Fr) (C.actT a j) := C.gen.1.2.1
  have hσinj : Function.Injective σV := by
    intro τ τ' h
    refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun a => ?_
    have h1 : embK c τ a = embK c τ' a := io.injective (by rw [← hσV', ← hσV', h])
    have h2 := congrArg (fun z : c.F => (z : ℂ)) h1
    exact h2
  let ρ : 𝓞 E → Matrix (Fin (chD C.ch)) (Fin (chD C.ch)) T.V := fun a i j =>
    MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (C.actT a i)
  have hρK : ∀ a i j, dAct T.Fr C.ch.B a i j = algebraMap T.V T.Fr (ρ a i j) := by
    intro a i j
    simp only [dAct, FB.actK, hact, MvPowerSeries.coeff_map, ρ]
    rfl
  have hρF : ∀ a i j, dAct F C.ch.B a i j = algebraMap T.V F (ρ a i j) := by
    intro a i j
    simp only [dAct, FB.actK, hact, MvPowerSeries.coeff_map, ρ]
    exact (IsScalarTower.algebraMap_apply T.V T.Fr F _).symm
  have heig : ∀ (a : 𝓞 E) (ℓ : Lt1 Dw), (ρ a).mulVec (C.uvecT ℓ) = σV ℓ.1 a • C.uvecT ℓ := by
    intro a ℓ
    funext i
    apply hinj
    have h := congrFun (GlobalTheory.T.integral_chart_directions_are_eigenvectors E H Dw l Xo c T io y C a ℓ) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hρK, huv, ← hσV'] at h
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
    exact h
  obtain ⟨lam, hlam⟩ := GlobalTheory.exists_dual_forms_of_separated_types T.V (𝓞 E) (chD C.ch) ρ (E →+* ℂ) Dw.mult
    (fun τ a => σV τ a) C.uvecT
    (fun τ τ' hne => GlobalTheory.exists_isUnit_sub_of_ringHom_ne (𝓞 E) T.V g hg hgu hfrob _ _ (fun h => hne (hσinj h)))
    heig (fun τ => by
      obtain ⟨⟨w, emb, hw, hb⟩, -⟩ := Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds Xo c T io y C τ
      exact exists_dual_of_extends (fun i => C.uvecT ⟨τ, i⟩) w emb hw hb)
  choose ε hε using fun τ => GlobalTheory.exists_separating_mod_prime_pow (𝓞 E) T.V g hg hgu hfrob (E →+* ℂ) σV hσinj 1 τ
  let f : T.V →+* TWO.Ov v := TWO.fO v hϖ hv
  have hf : ∀ x, (f x : F) = algebraMap T.V F x := fun x => (IsScalarTower.algebraMap_apply T.V T.Fr F x).symm
  have hgO : ¬ IsUnit ((g : ℕ) : TWO.Ov v) := by
    intro h
    rw [← map_natCast f] at h
    exact hgu ((isUnit_map_iff f _).1 h)
  refine ⟨fun τ => f.comp (σV τ), fun ℓ i => f (C.uvecT ℓ i), fun τ a => ?_, fun ℓ i => hf _, fun ℓ i => ?_,
    fun a ℓ => ?_, fun τ a => ⟨fun h => ?_, fun h => (isUnit_Ov_iff v _).2 h⟩, fun τ a => ?_,
    ⟨fun ℓ s => f (lam ℓ s), fun ℓ ℓ' => ?_⟩, ⟨ε, fun τ τ' => ?_⟩, hgO⟩
  · rw [RingHom.comp_apply, hf, ← hσV', ← IsScalarTower.algebraMap_apply]
  · rw [hf, huv, ← IsScalarTower.algebraMap_apply]
  · funext i
    have h := congrArg (algebraMap T.V F) (congrFun (heig a ℓ) i)
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_sum, map_mul] at h
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hρF, hf, RingHom.comp_apply]
    exact h
  · exact (GlobalTheory.hom_value_congruent_int_mod_prime (𝓞 E) (TWO.Ov v) g hg hgO hfrob _ a).2
      (fun hu => (isUnit_Ov_iff v _).1 hu h)
  · have h : embK c (ComplexEmbedding.conjugate τ) a = embK c τ (H.bar a) := by
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq,
        IsCMField.complexEmbedding_complexConj]
    have h2 : σV (ComplexEmbedding.conjugate τ) a = σV τ (H.bar a) := hinj (by rw [hσV', hσV', h])
    exact congrArg f h2
  · have h := congrArg f (hlam ℓ ℓ')
    simp only [map_sum, map_mul] at h
    rw [h]
    by_cases hl : ℓ = ℓ'
    · rw [if_pos hl, if_pos hl, map_one]
    · rw [if_neg hl, if_neg hl, map_zero]
  · obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hε τ τ')
    refine Ideal.mem_span_singleton'.2 ⟨f b, ?_⟩
    have h := congrArg f hb
    rw [pow_one, map_mul, map_natCast, map_sub] at h
    rw [h, RingHom.comp_apply]
    by_cases ht : τ = τ'
    · rw [if_pos ht, if_pos ht.symm, map_one]
    · rw [if_neg ht, if_neg (Ne.symm ht), map_zero]

end GlobalTheory.PowGerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMahlerExpansion
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership

namespace GlobalTheory.MonomialDense
open GlobalTheory.MultiMahler

variable {p : ℕ} [Fact p.Prime]

noncomputable def incl (p : ℕ) [Fact p.Prime] : ℤ_[p] →+* ℂ_[p] :=
  (algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom

theorem continuous_incl : Continuous (incl p) :=
  (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val

theorem factorial_mul_binomC (k : ℕ) (x : ℤ_[p]) :
    (k.factorial : ℂ_[p]) * binomC k x
      = incl p (Polynomial.aeval x (descPochhammer ℤ k)) := by
  have h1 : binomC k x = incl p (Ring.choose x k) := rfl
  have h2 := Ring.descPochhammer_eq_factorial_smul_choose x k
  rw [← Polynomial.aeval_eq_smeval] at h2
  rw [h1, h2, nsmul_eq_mul, map_mul, map_natCast]

theorem exists_mahler_expansion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
    [IsUltrametricDist E] [CompleteSpace E] (f : C(ℤ_[p], E)) :
    ∃ t : ℕ → C(ℤ_[p], E), HasSum t f ∧
      ∀ n, ∃ a : E, ∀ x, t n x = ((mahler n x : ℤ_[p]) : ℚ_[p]) • a := by
  letI : Module ℤ_[p] E := Module.compHom E (algebraMap ℤ_[p] ℚ_[p])
  haveI : IsBoundedSMul ℤ_[p] E := IsBoundedSMul.of_norm_smul_le fun r x =>
    norm_smul_le (r : ℚ_[p]) x
  exact ⟨_, PadicInt.hasSum_mahler f, fun n => ⟨_, fun _ => rfl⟩⟩

variable {Z : Type} [TopologicalSpace Z] [CompactSpace Z]

omit [CompactSpace Z] in
theorem binomC_comp_mem (S : Subalgebra ℂ_[p] C(Z, ℂ_[p])) (φ : C(Z, ℤ_[p]))
    (X : C(Z, ℂ_[p])) (hX : ∀ z, X z = incl p (φ z)) (hS : X ∈ S) (k : ℕ) :
    (binomC k).comp φ ∈ S := by
  have hmem : ∀ P : Polynomial ℤ, ∃ G ∈ S, ∀ z, G z = incl p (Polynomial.aeval (φ z) P) := by
    intro P
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ =>
      obtain ⟨G, hG, hG'⟩ := hP
      obtain ⟨G₂, hG₂, hG₂'⟩ := hQ
      exact ⟨G + G₂, S.add_mem hG hG₂, fun z => by simp [hG', hG₂']⟩
    | monomial n a =>
      refine ⟨(a : ℂ_[p]) • X ^ n, S.smul_mem (S.pow_mem hS n) _, fun z => ?_⟩
      simp [hX, Polynomial.aeval_monomial]
  obtain ⟨G, hG, hG'⟩ := hmem (descPochhammer ℤ k)
  have hk : (k.factorial : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have : (binomC k).comp φ = (k.factorial : ℂ_[p])⁻¹ • G := by
    ext z
    change binomC k (φ z) = (k.factorial : ℂ_[p])⁻¹ * G z
    rw [hG', ← factorial_mul_binomC, inv_mul_cancel_left₀ hk]
  rw [this]
  exact S.smul_mem hG _

noncomputable def evalAlong {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (φ : C(Z, ℤ_[p])) (ψ : C(Z, Y)) :
    C(ℤ_[p], C(Y, ℂ_[p])) →L[ℂ_[p]] C(Z, ℂ_[p]) :=
  LinearMap.mkContinuous
    { toFun := fun G => ⟨fun z => G (φ z) (ψ z), by fun_prop⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (fun G => by
      rw [one_mul, ContinuousMap.norm_le _ (norm_nonneg _)]
      intro z
      exact ((G (φ z)).norm_coe_le_norm _).trans (G.norm_coe_le_norm _))

theorem comp_mem (S : Subalgebra ℂ_[p] C(Z, ℂ_[p])) (hS : IsClosed (S : Set C(Z, ℂ_[p])))
    (g : ℕ) : ∀ (φ : C(Z, Fin g → ℤ_[p])),
      (∀ i, ∃ X ∈ S, ∀ z, X z = incl p (φ z i)) →
      ∀ F : C(Fin g → ℤ_[p], ℂ_[p]), F.comp φ ∈ S := by
  induction g with
  | zero =>
    intro φ _ F
    have : F.comp φ = algebraMap ℂ_[p] C(Z, ℂ_[p]) (F 0) := by
      ext z
      simp [Subsingleton.elim (φ z) 0]
    rw [this]
    exact S.algebraMap_mem _
  | succ g ih =>
    intro φ hφ F
    obtain ⟨t, ht, ht'⟩ := exists_mahler_expansion (curryFirst F)
    let φ0 : C(Z, ℤ_[p]) := ⟨fun z => φ z 0, by fun_prop⟩
    let ψ : C(Z, Fin g → ℤ_[p]) := ⟨fun z i => φ z i.succ, by fun_prop⟩
    have h := (evalAlong φ0 ψ).hasSum ht
    have e : evalAlong φ0 ψ (curryFirst F) = F.comp φ := by
      ext z
      exact congrArg F (Fin.cons_self_tail (φ z))
    rw [e] at h
    refine hS.mem_of_tendsto h (Filter.Eventually.of_forall fun s => S.sum_mem fun n _ => ?_)
    obtain ⟨a, ha⟩ := ht' n
    have e2 : evalAlong φ0 ψ (t n) = (binomC n).comp φ0 * a.comp ψ := by
      ext z
      change t n (φ0 z) (ψ z) = _
      rw [ha]
      change ((mahler n (φ0 z) : ℤ_[p]) : ℚ_[p]) • a (ψ z) = _
      rw [Algebra.smul_def]
      rfl
    rw [e2]
    obtain ⟨X, hX, hX'⟩ := hφ 0
    exact S.mul_mem (binomC_comp_mem S φ0 X hX' hX n) (ih ψ (fun i => hφ i.succ) a)

theorem eq_zero_of_monomials : ∀ (p r : ℕ) [Fact p.Prime] (μ : C(Fin r → ℤ_[p], ℂ_[p]) →L[ℂ_[p]] ℂ_[p]), (∀ (m : ℕ) (k : Fin m → Fin r) (g : C(Fin r → ℤ_[p], ℂ_[p])), (∀ a, g a = ∏ j, zc (a (k j))) → μ g = 0) → μ = 0 := by
  intro p r _ μ hμ
  let X : Fin r → C(Fin r → ℤ_[p], ℂ_[p]) := fun i =>
    ⟨fun a => incl p (a i), continuous_incl.comp (continuous_apply i)⟩
  let A : Subalgebra ℂ_[p] C(Fin r → ℤ_[p], ℂ_[p]) := Algebra.adjoin ℂ_[p] (Set.range X)
  have hA : ∀ f ∈ A, μ f = 0 := by
    intro f hf
    have hf' : f ∈ Submodule.span ℂ_[p] (Submonoid.closure (Set.range X) : Set _) := by
      rw [← Algebra.adjoin_eq_span]; exact hf
    refine (Submodule.span_le (p := LinearMap.ker μ.toLinearMap)).mpr ?_ hf'
    intro g hg
    have : ∃ (m : ℕ) (k : Fin m → Fin r), ∀ a, g a = ∏ j, zc (a (k j)) := by
      induction hg using Submonoid.closure_induction_left with
      | one => exact ⟨0, Fin.elim0, fun a => by simp⟩
      | mul_left x hx y _ ih =>
        obtain ⟨i, rfl⟩ := hx
        obtain ⟨m, k, hk⟩ := ih
        refine ⟨m + 1, Fin.cons i k, fun a => ?_⟩
        rw [Fin.prod_univ_succ, ContinuousMap.mul_apply, hk]
        rfl
    obtain ⟨m, k, hk⟩ := this
    exact hμ m k g hk
  ext F
  have hF := comp_mem A.topologicalClosure A.isClosed_topologicalClosure r (ContinuousMap.id _)
    (fun i => ⟨X i, A.le_topologicalClosure (Algebra.subset_adjoin ⟨i, rfl⟩), fun _ => rfl⟩) F
  have hcl : closure (A : Set C(Fin r → ℤ_[p], ℂ_[p])) ⊆ {f | μ f = 0} :=
    closure_minimal hA (isClosed_eq μ.continuous continuous_const)
  exact hcl hF

end GlobalTheory.MonomialDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPelUnifOfUnifPow
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_pelUnif_of_unifPow : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (n : ℕ) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' t.G n) (U' : Unif (maximalIdeal V) D' A' G') (_PU : UnifPowOf3 pD pA pG U' P.U), letI := H.starRing; ∀ [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∃ (oA' : A'.OAct (𝓞 E)), (∀ (a : 𝓞 E) (i : Fin n), oA'.act a ≫ pA.pr i = pA.pr i ≫ P.oA.act a) ∧ ∃ (t' : SAB H (Sp V)) (P' : PELUnif (maximalIdeal V) t'), t'.G = G' ∧ HEq t'.grp (inferInstance : GrpObj G') ∧ HEq t'.comm (inferInstance : IsCommMonObj G') ∧ P'.D = D' ∧ HEq P'.mod (inferInstance : Module (𝓞 E) D'.toPre.X) ∧ HEq P'.oD oD' ∧ P'.A = A' ∧ HEq P'.oA oA' ∧ HEq P'.U U' := by
  intro _ _ _ _ V _ _ _ _ E _ _ _ H t P n D' A' G' _ _ pD pA pG U' Q
  letI := H.starRing
  intro md oD' hxi hoD
  have hx : ∀ (a : 𝓞 E) (x : D'.toPre.X), pD.xe (a • x) = a • pD.xe x := fun a x => funext fun i => hxi a x i
  obtain ⟨act', hact⟩ := (GlobalTheory.exists_powAct _ _ _ n pG).2 _ t.act
  have iso : LBIso U'.LG.L (boxLB t.PP.L pG.pr) := by
    rw [← P.bundle]; exact ⟨Q.wL, Q.wL_gen⟩
  let t' : SAB H (Sp V) :=
    { G := G'
      semi := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ n pG t.semi
      act := act'
      PP := U'.LG
      cub := U'.cubG
      sym := isSymmetric_of_symmetry_generator U'.LG U'.symG U'.symG_gen U'.symG_rig
      adj := fun a => GlobalTheory.PowAdj.lbIso_cube_pow _ _ _ n pG _ _ t.PP.isLB U'.LG.isLB iso _ _ _ _ (hact a) (hact (H.bar a)) (t.adj a)
      prim := GlobalTheory.PowPrimitive.lbIso_cube_pow _ _ _ n pG _ _ t.PP.isLB U'.LG.isLB iso _ _ (hact H.w0) t.prim }
  obtain ⟨rA, hrA⟩ := (GlobalTheory.exists_powAct _ _ _ n pA.toIsPowGrp).1 _ P.oA.toRingAct
  let oA' : A'.OAct (𝓞 E) :=
    { toRingAct := rA
      rosati := fun a => GlobalTheory.rosatiAdj_pow _ _ _ n pA.toIsPowGrp _ _ P.A.isLB A'.isLB ⟨pA.w, pA.w_gen⟩ _ _ _ _ (hrA a)
        (hrA (star a)) (P.oA.rosati a) }
  let P' : PELUnif (maximalIdeal V) t' :=
    { D := D'
      oD := oD'
      A := A'
      oA := oA'
      U := U'
      bundle := rfl
      lin := GlobalTheory.oLinear_of_unifPow V (maximalIdeal V) n _ _ _ _ _ _ pD pA pG U' P.U Q _ hx P.oD oD' P.oA oA'
        t.act.toRingAct act'.toRingAct hoD hrA hact P.lin
      w0 := GlobalTheory.PsiWZeroProd.main V n _ _ pD _ hx P.oD oD' hoD H.w0 P.w0 }
  exact ⟨oA', hrA, t', P', rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRatNear
section
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership GlobalTheory.PlaceComponents GlobalTheory.QuadSubfield

namespace GlobalTheory.PlaceApprox

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem exists_rat_near (h : ∀ m : ℕ, ∃ ε : 𝓞 D.host.K, IsIdem D lam m ε) (c : D.host.K) (η : ℝ) (hη : 0 < η) :
    ∃ t : ℚ, ‖homP D lam c - (t : ℂ_[p])‖ < η := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  set S := ‖homP D lam c‖ + ‖homPbar D lam c‖ + 1 with hS
  have hS0 : 0 < S := by positivity
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hη hS0) (inv_lt_one_of_one_lt₀ hp)
  obtain ⟨ε, hε⟩ := h m
  rw [isIdem_iff, zpow_neg, zpow_natCast, ← inv_pow] at hε
  obtain ⟨t, -, ht, -⟩ := exists_trace_norm D ((ε : D.host.K) * c)
  refine ⟨t, ?_⟩
  have h1 := congrArg (homP D lam) ht
  rw [map_add, homP_conjK, map_mul, map_mul, map_ratCast] at h1
  have h2 : homP D lam c - (t : ℂ_[p]) =
      -((homP D lam (ε : D.host.K) - 1) * homP D lam c + homPbar D lam (ε : D.host.K) * homPbar D lam c) := by
    rw [← h1]; ring
  rw [h2, norm_neg]
  rw [lt_div_iff₀ hS0] at hm
  have hq : (0 : ℝ) ≤ (p : ℝ)⁻¹ ^ m := by positivity
  calc _ ≤ ‖homP D lam (ε : D.host.K) - 1‖ * ‖homP D lam c‖ +
        ‖homPbar D lam (ε : D.host.K)‖ * ‖homPbar D lam c‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ (p : ℝ)⁻¹ ^ m * ‖homP D lam c‖ + (p : ℝ)⁻¹ ^ m * ‖homPbar D lam c‖ := by
        gcongr
        exacts [hε.1, hε.2]
    _ ≤ (p : ℝ)⁻¹ ^ m * S := by rw [hS]; nlinarith
    _ < η := hm

theorem exists_padic (h : ∀ m : ℕ, ∃ ε : 𝓞 D.host.K, IsIdem D lam m ε) (c : D.host.K) :
    ∃ x : ℚ_[p], algebraMap ℚ_[p] ℂ_[p] x = homP D lam c := by
  have hc : IsClosed (Set.range (algebraMap ℚ_[p] ℂ_[p])) :=
    (algebraMap_isometry ℚ_[p] ℂ_[p]).isClosedEmbedding.isClosed_range
  have : homP D lam c ∈ closure (Set.range (algebraMap ℚ_[p] ℂ_[p])) := by
    rw [Metric.mem_closure_iff]
    intro η hη
    obtain ⟨t, ht⟩ := exists_rat_near D lam h c η hη
    exact ⟨t, ⟨t, map_ratCast _ t⟩, by rwa [dist_eq_norm]⟩
  rwa [hc.closure_eq] at this

theorem exists_padicInt (h : ∀ m : ℕ, ∃ ε : 𝓞 D.host.K, IsIdem D lam m ε) (c : D.host.K)
    (hc : ‖homP D lam c‖ ≤ 1) : ∃ z : ℤ_[p], zc z = homP D lam c := by
  obtain ⟨x, hx⟩ := exists_padic D lam h c
  rw [← hx, norm_algebraMap'] at hc
  exact ⟨⟨x, hc⟩, hx⟩

theorem approx : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]),
    (∀ m : ℕ, ∃ ε : 𝓞 D.host.K, IsIdem D lam m ε) → ∀ c : D.host.K,
      (‖atP D lam c‖ ≤ 1 → ∀ n : ℕ, ∃ k : ℕ, k < p ^ n ∧ ‖atP D lam c - (k : ℂ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ))) ∧
      (‖atPbar D lam c‖ ≤ 1 → ∃ z : ℤ_[p], zc z = atPbar D lam c) := by
  intro D p _ lam h c
  rw [atP₂, atPbar_eq]
  refine ⟨fun hc n => ?_, fun hc => exists_padicInt D lam h (conjK D c) hc⟩
  obtain ⟨z, hz⟩ := exists_padicInt D lam h c hc
  refine ⟨z.appr n, z.appr_lt n, ?_⟩
  have h1 := (PadicInt.norm_le_pow_iff_mem_span_pow _ n).2 (z.appr_spec n)
  have h2 : homP D lam c - (z.appr n : ℂ_[p]) =
      algebraMap ℚ_[p] ℂ_[p] ((z - (z.appr n : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) := by
    rw [← hz, PadicInt.coe_sub, map_sub, PadicInt.coe_natCast, map_natCast]; rfl
  rw [h2, norm_algebraMap']
  exact h1

end GlobalTheory.PlaceApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupCayleyRecursion
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Moment

theorem n1_sub_single_one_le_add_one {n : ℕ} (ν : Fin n → ℤ) (s : Fin n) :
    n1 (ν - Pi.single s 1) ≤ n1 ν + 1 := by
  have h1 : (∑ i, ((Pi.single s (1 : ℤ) : Fin n → ℤ) i).natAbs) = 1 := by
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  unfold n1
  rw [← h1, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Int.natAbs_sub_le _ _

theorem moment_first_length : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ (q : ℕ) ν, n1 ν + q ≤ q0 → ∀ j : ℕ, j + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 → ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) ^ q * ‖w‖ ^ 2) := by
  intro H k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE q
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := hS.2.2.1.2.1
  have hC : 0 ≤ (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) := by
    have h6 : 0 ≤ (6 * bv) ^ (2 * (2 * r + 2)) := by rw [pow_mul]; positivity
    positivity
  induction q with
  | zero =>
    intro ν hν j _ w _
    have := (GlobalTheory.T.bessel_functional_l2_bound_and_isometry H k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν (by omega)).1 w w.2
    simpa using this
  | succ q ih =>
    intro ν hν j hj w hw
    have := GlobalTheory.T.family_setup_cayley_moment H k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν (by omega) j q _
      (by omega) (pow_nonneg hC q)
      (fun s y hy => ih (ν - Pi.single s 1) (by have := n1_sub_single_one_le_add_one ν s; omega) (j + 2) (by omega) y hy) w hw
    rw [pow_succ' _ q]
    exact this

end GlobalTheory.Moment
end

