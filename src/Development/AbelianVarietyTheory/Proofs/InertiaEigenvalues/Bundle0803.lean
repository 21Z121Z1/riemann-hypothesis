import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0441
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0439
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0795
import GroundTheory.AutomorphicForms.ReductionMeasure
import GroundTheory.GlobalFields.Adele.Topology
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0756
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0796
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0758
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0797
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
import Formalism.AdmissibleDesigns.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0724
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0783
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HaarMeasureUniformizerTranslate
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CellDec.ModulusPf

variable {E : Type} [Field E] [NumberField E]

theorem adl_add (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m m' : HeightOneSpectrum (𝓞 E) →₀ ℤ) :
    GlobalTheory.CellDec.adl ϖ (m + m') = GlobalTheory.CellDec.adl ϖ m * GlobalTheory.CellDec.adl ϖ m' := by
  apply Units.ext
  apply FiniteAdeleRing.ext
  intro v
  change ((ϖ v ^ (m + m') v : (v.adicCompletion E)ˣ) : v.adicCompletion E) =
    ((ϖ v ^ m v : (v.adicCompletion E)ˣ) : v.adicCompletion E) * ((ϖ v ^ m' v : (v.adicCompletion E)ˣ) : v.adicCompletion E)
  rw [Finsupp.add_apply, _root_.zpow_add, Units.val_mul]

theorem adl_sub (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m m' : HeightOneSpectrum (𝓞 E) →₀ ℤ) :
    GlobalTheory.CellDec.adl ϖ (m - m') = GlobalTheory.CellDec.adl ϖ m * (GlobalTheory.CellDec.adl ϖ m')⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, ← adl_add, sub_add_cancel]

theorem zpow_sum_real {ι : Type} (q : ℝ) (hq : q ≠ 0) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, q ^ f i = q ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq]

theorem sum_pairs_eq_wtS {n : ℕ} (a : Fin n → ℤ) :
    ∑ p : {p : Fin n × Fin n // p.1 < p.2}, (a p.1.1 - a p.1.2) = GlobalTheory.CellDec.wtS n a := by
  classical
  rw [GlobalTheory.CellDec.wtS, ← Finset.sum_subtype (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2)
    (by simp) (fun p : Fin n × Fin n => a p.1 - a p.2), Finset.sum_filter, Fintype.sum_prod_type]

end GlobalTheory.CellDec.ModulusPf

namespace GlobalTheory.CellDec.ModulusPf

theorem modulus_conj : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (ν : Measure (GlobalTheory.CellDec.NA E n)) [ν.IsHaarMeasure] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ))
    (A : Set (GlobalTheory.CellDec.NA E n)), MeasurableSet A →
    ν {u : GlobalTheory.CellDec.NA E n | ∃ a ∈ A, (a : GA E n) = GlobalTheory.CellDec.tl n ϖ l * (u : GA E n) * (GlobalTheory.CellDec.tl n ϖ l)⁻¹} =
      ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) * ν A := by
  intro E _ _ n _ _ ν _ ϖ hϖ l A hA
  classical
  set t := GlobalTheory.CellDec.tl n ϖ l with ht
  let d : Fin n → (AdeleRing (𝓞 E) E)ˣ := fun i => finId E (GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l))
  have htd : t = GlobalTheory.SmGL.diagT (Ad E) (Fin n) d := GlobalTheory.CellDec.tl_eq_diagT ϖ l
  let φ : GlobalTheory.CellDec.NA E n → GlobalTheory.CellDec.NA E n := fun u => ⟨t * u * t⁻¹, GlobalTheory.CellDec.tl_conj_mem ϖ l u.2⟩
  have hφc : Continuous φ :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  have hset : {u : GlobalTheory.CellDec.NA E n | ∃ a ∈ A, (a : GA E n) = t * (u : GA E n) * t⁻¹} = φ ⁻¹' A := by
    ext u
    constructor
    · rintro ⟨a, ha, h⟩
      have : φ u = a := Subtype.ext h.symm
      simpa [Set.mem_preimage, this] using ha
    · intro hu
      exact ⟨φ u, hu, rfl⟩
  rw [hset, ← Measure.map_apply hφc.measurable hA]

  let co : GlobalTheory.CellDec.NA E n → ({p : Fin n × Fin n // p.1 < p.2} → Ad E) :=
    fun u p => ((u : GL (Fin n) (Ad E)) : Matrix (Fin n) (Fin n) (Ad E)) p.1.1 p.1.2
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_upperUnitriangular_entries_homeomorph (Ad E) n
  have hco : ⇑e = co := funext he
  let μR : Measure (Ad E) := Measure.addHaar
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_map_entries_haar_unitriangular_eq_smul_pi (Ad E) n μR ν
  let mm : {p : Fin n × Fin n // p.1 < p.2} → (HeightOneSpectrum (𝓞 E) →₀ ℤ) := fun p =>
    Finsupp.mapRange (fun x : Fin n → ℤ => x p.1.1) rfl l - Finsupp.mapRange (fun x : Fin n → ℤ => x p.1.2) rfl l
  let a : {p : Fin n × Fin n // p.1 < p.2} → Ad E := fun p => ((finId E (GlobalTheory.CellDec.adl ϖ (mm p)) : (Ad E)ˣ) : Ad E)
  let S : ({p : Fin n × Fin n // p.1 < p.2} → Ad E) → ({p : Fin n × Fin n // p.1 < p.2} → Ad E) := fun x p => a p * x p
  have hentry : ∀ (u : GA E n) (i j : Fin n), ((t * u * t⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j =
      ((d i : Ad E) * (((d j)⁻¹ : (Ad E)ˣ) : Ad E)) * (u : Matrix (Fin n) (Fin n) (Ad E)) i j := by
    intro u i j
    rw [htd, ← map_inv, Units.val_mul, Units.val_mul, GlobalTheory.SmGL.val_diagT, GlobalTheory.SmGL.val_diagT, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    simp only [Pi.inv_apply]
    ring
  have ha : ∀ p, a p = (d p.1.1 : Ad E) * (((d p.1.2)⁻¹ : (Ad E)ˣ) : Ad E) := by
    intro p
    simp only [a, mm, d, adl_sub, map_mul, map_inv, Units.val_mul]
  have hSco : co ∘ φ = S ∘ co := by
    funext u p
    simp only [Function.comp_apply, co, S, φ]
    rw [hentry, ha]
  let k : {p : Fin n × Fin n // p.1 < p.2} → ℝ≥0∞ := fun p => ENNReal.ofReal (∏ v ∈ l.support, (qV E v : ℝ) ^ (mm p v))
  have hk : ∀ p, Measure.map (fun x : Ad E => a p * x) μR = k p • μR := fun p =>
    GlobalTheory.T.addHaar_map_mul_finiteIdeleOfUniformizerPowers E ϖ hϖ (mm p) l.support (fun v hv => by simp [mm, Finsupp.notMem_support_iff.1 hv]) μR
  haveI : ∀ p, SigmaFinite (k p • μR) := fun p => (inferInstance : SigmaFinite ((Real.toNNReal _) • μR))
  have hSm : Measurable S := by
    refine measurable_pi_lambda _ fun p => ?_
    exact (measurable_const_mul (a p)).comp (measurable_pi_apply p)
  have hS : Measure.map S (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR) =
      (∏ p, k p) • Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR := by
    have h1 : Measure.pi (fun p => k p • μR) = Measure.map S (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR) := by
      refine Measure.pi_eq fun s hs => ?_
      rw [Measure.map_apply hSm (MeasurableSet.univ_pi hs)]
      rw [show S ⁻¹' Set.univ.pi s = Set.univ.pi fun p => (fun x : Ad E => a p * x) ⁻¹' s p from
        Set.preimage_pi Set.univ s fun p (x : Ad E) => a p * x]
      rw [Measure.pi_pi]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [← hk p, Measure.map_apply (measurable_const_mul _) (hs p)]
    have h2 : Measure.pi (fun p => k p • μR) = (∏ p, k p) • Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR := by
      refine Measure.pi_eq fun s hs => ?_
      rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
      rfl
    rw [← h1, h2]
  have hK : (∏ p, k p) = ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) := by
    simp only [k]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun p _ => Finset.prod_nonneg fun v _ => zpow_nonneg (Nat.cast_nonneg _) _)]
    congr 1
    rw [Finset.prod_comm, GlobalTheory.CellDec.dinv]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hq : (qV E v : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by rw [qV, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
    rw [zpow_sum_real _ hq, ← sum_pairs_eq_wtS]
    congr 1
  have key : Measure.map φ ν = ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) • ν := by
    have hem : Measurable e := e.continuous.measurable
    have h3 : Measure.map e (Measure.map φ ν) = Measure.map e (ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) • ν) := by
      have hc' : Measure.map e ν = c • Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR := by
        rw [hco]; exact hc
      rw [Measure.map_map hem hφc.measurable, hco, hSco, ← Measure.map_map hSm (hco ▸ hem), ← hco, hc',
        Measure.map_smul, Measure.map_smul, hS, hc', ← hK, smul_comm]
    have h4 := congrArg (Measure.map e.toMeasurableEquiv.symm) h3
    rwa [show (⇑e : GlobalTheory.CellDec.NA E n → _) = ⇑e.toMeasurableEquiv from rfl, MeasurableEquiv.map_symm_map,
      MeasurableEquiv.map_symm_map] at h4
  rw [key]
  rfl
end GlobalTheory.CellDec.ModulusPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertSatakeHeckeEigenvaluesAlgebraicAutomorphic
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.InertHeckeCmp.satU_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.SatAt π Dv α → ∀ α0 : Fin (n / 2) → ℂˣ, HasSatAt U w Dv.σw Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) α0 → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h (fun i => (α0 i : ℂ)) := by
  intro L _ _ _ n F π U hD v w hw Dv α hα α0 hα0 h hh
  rcases Nat.eq_zero_or_pos (n / 2) with h2 | h2
  · congr 1
    funext i
    exact absurd i.2 (by omega)
  have hn : 0 < n := by omega
  obtain ⟨b, hbK, hbJ, p, hp, σ, hcomp, hsat⟩ := hα0
  obtain ⟨hs, hsurj⟩ := GlobalTheory.T.inert_frame_conj_extends_and_frame_map_surjective L n hn v w hw Dv b hbK hbJ p hp
  obtain ⟨φ, hφU, hφ0, hfix, hAe⟩ := GlobalTheory.T.exists_lift_satake_vector_local_hecke_eigen L n F π U hD v w hw Dv α hα hs b hbK hbJ p hp
  have e1 := (hAe h hh).symm.trans (GlobalTheory.T.satake_parameters_unramified_unitary L n U hD.1 w Dv.σw Dv.ϖ _ Dv.unram p hsurj σ hcomp α0 hsat φ hφU hfix h hh)
  rw [← sub_eq_zero, ← sub_smul] at e1
  exact sub_eq_zero.1 ((smul_eq_zero.1 e1).resolve_right hφ0)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralCombIdempotentSectionsNonnegOverPlace
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IdemInt

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39

section Val

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
  {la : HeightOneSpectrum (𝓞 K)} {u : R → EReal}

theorem nonneg_of_idem (hu : IsVal la u) {x : R} (hx : x * x = x) : 0 ≤ u x := by
  have h := hu.mul x x
  rw [hx] at h
  rcases eq_or_ne (u x) ⊤ with h0 | h0
  · rw [h0]
    exact le_top
  · have hr : (((u x).toReal : ℝ) : EReal) = u x := EReal.coe_toReal h0 (hu.ne_bot x)
    rw [← hr] at h ⊢
    rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at h
    exact EReal.coe_nonneg.mpr (by linarith)

theorem nonneg_smul (hu : IsVal la u) {a : K} (ha : la.valuation K a ≤ 1) {x : R} (hx : 0 ≤ u x) :
    0 ≤ u (a • x) := by
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_smul, hu.zero]
    exact le_top
  · rw [hu.smul a x ha0]
    have hv0 : la.valuation K a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha0
    have hlog : (la.valuation K a).log ≤ 0 := by
      rw [WithZero.log_le_iff_le_exp hv0, WithZero.exp_zero]
      exact ha
    refine add_nonneg ?_ hx
    unfold Formalism.BasicNotions.vAdd
    have hn : (0 : ℤ) ≤ -(la.valuation K a).log := neg_nonneg.mpr hlog
    exact_mod_cast hn

theorem nonneg_sum (hu : IsVal la u) {ι : Type} (s : Finset ι) (x : ι → R) (hx : ∀ i ∈ s, 0 ≤ u (x i)) :
    0 ≤ u (∑ i ∈ s, x i) := by
  refine Finset.sum_induction x (fun y => 0 ≤ u y) (fun a b ha hb => ?_) ?_ hx
  · exact le_trans (le_min ha hb) (hu.add a b)
  · show (0 : EReal) ≤ u 0
    rw [hu.zero]
    exact le_top

end Val

theorem idem_comb_mul_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (m : ℕ) (χ : Fin m → Rul Xo c) (v : Fin m → c.F), (∀ i, χ i ∈ sec Xo c 0 0 ∧ χ i * χ i = χ i) → (∀ i, la.valuation c.F (v i) ≤ 1) → ∀ f : Rul Xo c, (∀ u ∈ valSet Xo c (algCls Xo c) la, 0 ≤ u f) → ∀ u ∈ valSet Xo c (algCls Xo c) la, 0 ≤ u ((∑ i, v i • χ i) * f) := by
  intro E _ _ _ H Dw l Xo c la m χ v hχ hv f hf u hu
  have hV : IsVal la u := isVal_valSet la u hu
  have h1 : 0 ≤ u (∑ i, v i • χ i) :=
    nonneg_sum hV Finset.univ _ fun i _ => nonneg_smul hV (hv i) (nonneg_of_idem hV (hχ i).2)
  rw [hV.mul]
  exact add_nonneg h1 (hf u hu)

end GlobalTheory.IdemInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatAtTrivAtOfSplit
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.StdAtPrime

theorem isIdemSum_idem (D : D7) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (hQ : GlobalTheory.ExportSeries.SplitSet Q) : IsIdemSum (idem Q) Q := by
  obtain ⟨e, he⟩ := hQ
  have : idem Q = e := by
    obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
    rw [hsum, GlobalTheory.ExportSeries.idem]
    exact Finset.sum_congr rfl fun PP hPP => GlobalTheory.ExportSeries.idemAt_eq (hes PP hPP)
  rw [this]
  exact he

theorem bnd_inv_of_hLat_std (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (h1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x)
    (h2 : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1)
    (V : HSp D) (hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank) (p : ℕ) (k : Bridge.Gf V)
    (hk : Bridge.hLat V k = Formalism.L2.Pj.stdLat D.host.E V.rank) :
    Bnd p (Matrix.GeneralLinearGroup.map ι.toRingHom k.1)⁻¹.1 := by
  refine ⟨1, Nat.coprime_one_left p, fun i j Q => ?_⟩
  have hx : (Pi.single j (1 : D.host.E) : Fin V.rank → D.host.E) ∈ Bridge.hLat V k := by
    rw [hk]
    refine Submodule.mem_pi.2 fun i' _ => ?_
    by_cases h : i' = j
    · subst h; rw [Pi.single_eq_same]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  have := (GlobalTheory.ClassScalarValue.mem_hLat ι h1 h2 V hL k _).1 hx i Q
  have e : (fun j' => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)
      ((Pi.single j (1 : D.host.E) : Fin V.rank → D.host.E) j')) = Pi.single j 1 := by
    funext j'
    by_cases h : j' = j
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  rw [e, Matrix.mulVec_single_one] at this
  rw [Nat.cast_one, one_mul]
  exact this

set_option maxHeartbeats 1600000 in

theorem latAt_trivAt_of_split : ∀ (D : D7) (V W : HSp D) (B : Base V W), B.Good → StdBase B → ∀ (p bad : ℕ), p.Prime → p ∣ bad → ∀ (Q : Finset (Formalism.L2.DIV.Pl D.host.E)), GlobalTheory.ExportSeries.SplitSet Q → (∀ PP ∈ Q, (p : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ hQ : GA D V, SuppAt (idem Q) V hQ → hQ ∈ GfC V ∧ ∀ (h h' : GA D V) (γ : GQ V) (k : Bridge.Gf V), SplitOffBad V bad h' → Formalism.UG.bc (Lev.swapAE D) k.1 ∈ Formalism.L2.DIV.St B.F.βS → finPt V (h * hQ) = Bridge.ratF V γ * finPt V h' * k → (⟨B.latAt (Bridge.ratF V γ⁻¹ * finPt V h * 1)⟩ : GenLat D.host.E V.rank).TrivAt p := by
  intro D V W B hB hS p bad hp hpb Q hQs hpQ hQ hsQ
  have hQsum := isIdemSum_idem D Q hQs
  have hinf : infPart D (idem Q) = 0 := by
    obtain ⟨⟨es, hes, hsum⟩, -⟩ := hQsum
    rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun PP hPP => GlobalTheory.ExportSeries.SpecGood.infPart_eq_zero_of_isIdemAt D PP _ (hes PP hPP)
  refine ⟨GlobalTheory.WeilProduct.mem_GfC_of_supp (a := idem Q + cA D (idem Q)) ?_ hsQ, ?_⟩
  · rw [map_add, GlobalTheory.PlaceIdem.infPart_cA, hinf, map_zero, add_zero]
  intro h h' γ k hh' hk heq
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨hid, hcj⟩ := GlobalTheory.T.placeIdempotent_components_conj_valuation D ι h1 h2 h4
  have hL0 : (B.F.ΛS : Set (Fin V.rank → D.host.E)) = L0c D V := hS.2.2.1
  have hstd : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank := by
    apply SetLike.coe_injective
    rw [GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice, ← hL0, hS.2.2.2.2]
  rw [GlobalTheory.LatAtHLat.latAt_eq_hLat D V W B hL0]
  have hg : Bridge.ratF V γ⁻¹ * finPt V h * 1 = finPt V h' * k * (finPt V hQ)⁻¹ := by
    have e1 : finPt V (h * hQ) = finPt V h * finPt V hQ := map_mul _ _ _
    have e2 : finPt V h = Bridge.ratF V γ * finPt V h' * k * (finPt V hQ)⁻¹ :=
      eq_mul_inv_of_mul_eq (e1.symm.trans heq)
    have e3 : Bridge.ratF V γ⁻¹ = (Bridge.ratF V γ)⁻¹ := map_inv (Bridge.ratF V) γ
    have key : ∀ {G : Type} [Group G] (a b c d f : G), b = a * c * d * f⁻¹ → a⁻¹ * b * 1 = c * d * f⁻¹ := by
      intro G _ a b c d f hb
      rw [hb, mul_one, mul_assoc, mul_assoc, inv_mul_cancel_left, ← mul_assoc]
    exact (congrArg (fun x => x * finPt V h * 1) e3).trans (key _ _ _ _ _ e2)
  rw [hg]
  have hk1 : ∀ k : Bridge.Gf V, Formalism.UG.bc (Lev.swapAE D) k.1 ∈ Formalism.L2.DIV.St B.F.βS →
      Bridge.hLat V k = Formalism.L2.Pj.stdLat D.host.E V.rank := by
    intro k hk
    have hr : Bridge.IsRatMat V 1 1 := by
      simp [Bridge.IsRatMat]
    have e4 : Bridge.ratF V 1 * 1 * k = k := by
      rw [map_one (Bridge.ratF V), one_mul, one_mul]
    have e5 : B.latAt k = B.latAt 1 := by
      ext x
      have := GlobalTheory.ExportSeries.Base.mem_latAt_iff hB.frame hr 1 k hk x
      rw [e4, inv_one, Units.val_one, Matrix.one_mulVec] at this
      exact this
    exact (GlobalTheory.LatAtHLat.latAt_eq_hLat D V W B hL0 k).symm.trans
      (e5.trans ((GlobalTheory.LatAtHLat.latAt_eq_hLat D V W B hL0 1).trans hstd))
  have hkS : Bridge.hLat V k = Formalism.L2.Pj.stdLat D.host.E V.rank := hk1 k hk
  have hkS' : Bridge.hLat V k⁻¹ = Formalism.L2.Pj.stdLat D.host.E V.rank := by
    refine hk1 k⁻¹ ?_
    rw [Subgroup.coe_inv, map_inv]
    exact inv_mem hk
  set M := Matrix.GeneralLinearGroup.map (n := Fin V.rank) ι.toRingHom with hM
  have hsupp : ∀ (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (g : GA D V), IsIdemSum e P →
      (∀ PP ∈ P, (p : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e V g →
      Bnd p (M (finPt V g).1).1 ∧ Bnd p (M (finPt V g).1)⁻¹.1 := by
    intro e P g he hp' hs
    obtain ⟨S, hSf, hSp, hS0⟩ := GlobalTheory.T.idempotent_add_conj_support_finite_prime_to_p D ι hid hcj p e P he hp'
    exact GlobalTheory.T.isBoundedPrimeToDenom_GL_and_inv_of_eq_one_off_finite p hp _ (M (finPt V g).1) S hSf hSp fun Q hQ i j => GlobalTheory.T.supported_adelic_point_eq_one_where_idempotent_vanishes D ι V e g hs Q (hS0 Q hQ) i j
  obtain ⟨-, e', P', he', hb', hs'⟩ := hh'
  have hp' : ∀ PP ∈ P', (p : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hPP hpP
    obtain ⟨c, rfl⟩ := hpb
    exact hb' PP hPP (by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hpP)
  obtain ⟨b1, b1'⟩ := hsupp e' P' h' he' hp' hs'
  obtain ⟨b3, b3'⟩ := hsupp (idem Q) Q hQ hQsum hpQ hsQ
  have b2' : Bnd p (M k.1)⁻¹.1 := bnd_inv_of_hLat_std D ι h1 h2 V hstd p k hkS
  have b2 : Bnd p (M k.1).1 := by
    have := bnd_inv_of_hLat_std D ι h1 h2 V hstd p k⁻¹ hkS'
    rwa [Subgroup.coe_inv, map_inv, inv_inv] at this
  have eM : M (finPt V h' * k * (finPt V hQ)⁻¹).1 = M (finPt V h').1 * M k.1 * (M (finPt V hQ).1)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv]
  refine GlobalTheory.T.bounded_entries_integral D ι h1 h2 V hstd p _ ?_ ?_
  · rw [eM, Units.val_mul, Units.val_mul]
    exact bnd_mul p _ _ _ (bnd_mul p _ _ _ b1 b2) b3'
  · rw [eM, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
    exact bnd_mul p _ _ _ b3 (bnd_mul p _ _ _ b2' b1')

end GlobalTheory.StdAtPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthBoundOfRowConditionsAndDualityTheoremsStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lengthBound_of_rowConditions_and_dualityTheorems : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.AllDesignConditions D → TruncatedSeriesCountingIdentities.Stmt D := by
  first | exact @GlobalTheory.InertiaEigenvalues.LengthBoundClosing.stmt_closed | exact GlobalTheory.InertiaEigenvalues.LengthBoundClosing.stmt_closed | (intros; apply GlobalTheory.InertiaEigenvalues.LengthBoundClosing.stmt_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftThroughCompletionIsoStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_through_completion_iso : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E), s.w = D.naut.plGw k v → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ L : G0g D.nd → GAf D.host.E D.R.nV, IsTypeGroupBlockLift D D.R.nV L → ∀ F ∈ D.naut.typeV i PI, ∀ (h : GL (Fin D.R.r) (ZMod (D.host.g k))) (g : G0g D.nd), g ⟨k, v⟩ = h → (∀ kv, kv ≠ ⟨k, v⟩ → g kv = 1) → ∃ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x ∧ IsLiftN h (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) ∧ NG.rt D.host.E D.R.nV (L g) ((P.M.loc i).real F) = NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) := by
  first | exact @GlobalTheory.LiftOther.main | exact GlobalTheory.LiftOther.main | (intros; apply GlobalTheory.LiftOther.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearRelationSectionsSpanEqStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_relation_sections_span_eq : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ), Formalism.L2.Pj.RdIndep (T.Q.Xo j) T.Q.c (T.U j) σ → ∀ (w : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom w n → ∀ (κ ι : Type) [Fintype κ] [Fintype ι] (A : κ → ι → Rul (T.Q.Xo j) T.Q.c), (∀ k i, A k i ∈ sec (T.Q.Xo j) T.Q.c w n) → ∀ z : κ → ℂ, (∀ i, ∑ k, z k • rdU (T.U j σ) (A k i) = 0) → z ∈ Submodule.span ℂ ((fun c : κ → T.Q.c.F => fun k => σ (c k)) '' {c | ∀ i, ∑ k, c k • A k i = 0}) := by
  first | exact @GlobalTheory.kerC_span_rat | exact GlobalTheory.kerC_span_rat | (intros; apply GlobalTheory.kerC_span_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialOfNotRangeSubsetAbLocusStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nontrivial_X_of_not_range_subset_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (S : Scheme.{0}) (t₀ : SAB H S) (T T' : Formalism.L2.Pj.CDVR) (g : T.V →+* T'.V) (y : Sp T.V ⟶ S) (t : SAB H (Sp T'.V)) (_ : SABMap t t₀ (spMap g ≫ y)) (P : PELUnif (IsLocalRing.maximalIdeal T'.V) t), Function.Injective g → g.Finite → ¬ Set.range y ⊆ abLocus t₀.G → Nontrivial P.D.toPre.X := by
  first | exact @GlobalTheory.BadReductionLattice.nontrivial_of_not_range_subset_abLocus | exact GlobalTheory.BadReductionLattice.nontrivial_of_not_range_subset_abLocus | (intros; apply GlobalTheory.BadReductionLattice.nontrivial_of_not_range_subset_abLocus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteral
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem isRec_of_isRecLit : DepthZeroCuspidalLL → DepthZeroInduction → LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRecLit h rc → IsRec h rc := by
  intro hDZ hDI hEx hLM hSC hZP hGL hBZ E Ω _ _ _ _ _ A w h rc H
  obtain ⟨a, ha, ε, hε, L⟩ := H
  refine ⟨a, ha, ε, hε, ?_⟩
  exact
    { bij := L.bij, dim := L.dim, one := L.one, eps := L.eps, cusp := L.cusp, langlands := L.langlands,
      twist := L.twist, central := L.central, dual := L.dual,
      det := GlobalTheory.T.determinant_rec_compatible hSC E Ω A w h a ha _ rc L
      prod := GlobalTheory.T.twist_rec_compatible hEx hLM hSC E Ω A w h a ha _ rc L
      supp := GlobalTheory.T.central_character_rec_compatible hEx hZP hGL hBZ E Ω A w h a ha _ rc L
      sph := GlobalTheory.T.l_factor_rec_compatible hEx hLM hSC hZP hGL hBZ E Ω A w h a ha _ rc L
      sat := GlobalTheory.T.epsilon_factor_rec_compatible hEx hLM hSC hZP hGL hBZ E Ω A w h a ha _ rc L
      depth := GlobalTheory.T.conductor_rec_compatible hDZ hDI hEx hZP hGL hBZ E Ω A w h rc ⟨a, ha, ε, hε, L⟩ }

end GlobalTheory.LocLanglands
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIsoStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rec_transport_field_iso : GlobalArtinReciprocity → ChevalleyUnits → BrauerDegreeZero → LocalLanglandsExists → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i → ∀ (ε : EpsFamily A) (ε' : EpsFamily A'), IsDeligneEps ε → IsDeligneEps ε' → ∀ (ψ : AddChar (w.adicCompletion E) Circle) (ψ' : AddChar (w'.adicCompletion E') Circle), Continuous ψ → ψ ≠ 1 → (∀ x, ψ' (i x) = ψ x) → ∀ (y : WD h) (y' : WD h'), WDRel φ y y' → ε E w h ψ y = ε' E' w' h' ψ' y' := by
  first | exact @GlobalTheory.LocLanglands.EpsUnique.eps_eq_of_placeIso | exact GlobalTheory.LocLanglands.EpsUnique.eps_eq_of_placeIso | (intros; apply GlobalTheory.LocLanglands.EpsUnique.eps_eq_of_placeIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenFrobeniusStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_eigen_frobenius : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tp.tup big L → ∀ (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), D.what₂.muAt w ≠ D.what₂.mu0 → ∀ c ∈ EigSet (M (D.what₂.muTw w) j h1 h2) (D.what₂.places.resChar w) (C.Q w), ∃ i ∈ L.X.nd.locs j w, ∃ x : L.X.nd.X i, ∀ (v : PlE D.host) (k : ℕ), GenAt D (D.what₂.places.resChar w) (C.Q w) v k → iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) = c v k := by
  first | exact @GlobalTheory.EigOnto.main | exact GlobalTheory.EigOnto.main | (intros; apply GlobalTheory.EigOnto.main <;> assumption)
end

