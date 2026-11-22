import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0786
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0001
import GroundTheory.AutomorphicForms.AdelicGLn
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0771
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0777
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0049
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0773
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.MatrixInfinitySpan.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarRightInvariant
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
open scoped RestrictedProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.AdelicUnimod

open GroundTheory.Automorphic

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem modularCharacter_eq_one_of_map (μ : Measure G) [μ.IsHaarMeasure] {z : G}
    (h : μ.map (fun x => x * z) = μ) : (Measure.modularCharacter z : ℝ≥0) = 1 := by
  have h1 := Measure.map_right_mul_eq_modularCharacterFun_smul μ z
  rw [h] at h1
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : G)
  have h2 := congrArg (fun m : Measure G => m C) h1
  have hne : μ C ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hC1).ne'
  have hnt : μ C ≠ ⊤ := hC.measure_lt_top.ne
  simp only [Measure.coe_nnreal_smul_apply] at h2
  have h3 : (Measure.modularCharacterFun z : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj hne hnt).1 (by rw [one_mul]; exact h2.symm)
  exact_mod_cast h3

theorem modularCharacter_eq_one_of_central (μ : Measure G) [μ.IsHaarMeasure] {z : G}
    (hz : ∀ h, z * h = h * z) : (Measure.modularCharacter z : ℝ≥0) = 1 := by
  refine modularCharacter_eq_one_of_map μ ?_
  rw [show (fun x => x * z) = fun x => z * x from funext fun x => (hz x).symm,
    Measure.IsMulLeftInvariant.map_mul_left_eq_self]

theorem modularCharacter_eq_one_of_compact (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G)
    (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) : (Measure.modularCharacter k : ℝ≥0) = 1 :=
  modularCharacter_eq_one_of_map μ
    (GlobalTheory.CompanionTheory.Xa1.map_mul_right_eq_of_mem_compact_subgroup G μ inferInstance inferInstance K hK k hk)

theorem isMulRightInvariant_of_modularCharacter (μ : Measure G) [μ.IsHaarMeasure]
    (h : ∀ g : G, (Measure.modularCharacter g : ℝ≥0) = 1) : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g,
    show Measure.modularCharacterFun g = 1 from h g, one_smul]

end General

section Products

theorem pi_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] {H : ι → Type*} [∀ i, Group (H i)]
    (Δ : (∀ i, H i) →* ℝ≥0) (h : ∀ i (x : H i), Δ (Pi.mulSingle i x) = 1) (x : ∀ i, H i) :
    Δ x = 1 := by
  have key : ∀ (S : Finset ι) (x : ∀ i, H i), (∀ i, i ∉ S → x i = 1) → Δ x = 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro x hx
      rw [show x = 1 from funext fun i => hx i (by simp), map_one]
    | insert a S _ ih =>
      intro x hx
      have e : x = (x * (Pi.mulSingle a (x a))⁻¹) * Pi.mulSingle a (x a) := by simp
      rw [e, map_mul, h, mul_one]
      refine ih _ fun i hi => ?_
      by_cases hia : i = a
      · subst hia
        simp
      · simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_of_ne hia, inv_one, mul_one]
        exact hx i (by simp [hia, hi])
  exact key Finset.univ x (by simp)

theorem restricted_eq_one {ι : Type*} [DecidableEq ι] {H : ι → Type*} [∀ i, Group (H i)]
    {A : ∀ i, Subgroup (H i)} (Δ : (Πʳ i, [H i, A i]) →* ℝ≥0)
    (h1 : ∀ i (x : H i), Δ (RestrictedProduct.mulSingle A i x) = 1)
    (h2 : ∀ x : Πʳ i, [H i, A i], (∀ i, x i ∈ A i) → Δ x = 1) (x : Πʳ i, [H i, A i]) :
    Δ x = 1 := by
  have key : ∀ (S : Finset ι) (x : Πʳ i, [H i, A i]), (∀ i, i ∉ S → x i ∈ A i) → Δ x = 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun x hx => h2 x fun i => hx i (by simp)
    | insert a S _ ih =>
      intro x hx
      have e : x = (x * (RestrictedProduct.mulSingle A a (x a))⁻¹) *
          RestrictedProduct.mulSingle A a (x a) := by simp
      rw [e, map_mul, h1, mul_one]
      refine ih _ fun i hi => ?_
      by_cases hia : i = a
      · subst hia
        simp [RestrictedProduct.mulSingle_eq_same, one_mem]
      · simp only [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply,
          RestrictedProduct.mulSingle_eq_of_ne A _ hia, inv_one, mul_one]
        exact hx i (by simp [hia, hi])
  have hfin : {i | x i ∉ A i}.Finite := x.2
  exact key hfin.toFinset x fun i hi => by simpa using hi

def singleHom {ι : Type*} [DecidableEq ι] {H : ι → Type*} [∀ i, Group (H i)]
    (A : ∀ i, Subgroup (H i)) (i : ι) : H i →* Πʳ i, [H i, A i] where
  toFun := RestrictedProduct.mulSingle A i
  map_one' := by
    ext j
    by_cases h : j = i
    · subst h; simp [RestrictedProduct.mulSingle_eq_same]
    · simp [RestrictedProduct.mulSingle_eq_of_ne A _ h]
  map_mul' x y := by
    ext j
    by_cases h : j = i
    · subst h; simp [RestrictedProduct.mulSingle_eq_same]
    · simp [RestrictedProduct.mulSingle_eq_of_ne A _ h]

end Products

section Adelic

variable (E : Type) [Field E] [NumberField E] (N : ℕ)

abbrev PInf : Type := ∀ w : InfinitePlace E, GL (Fin N) w.Completion

abbrev AInt (v : HeightOneSpectrum (𝓞 E)) : Subgroup (GL (Fin N) (v.adicCompletion E)) :=
  GLnLocal.integralGL (v.adicCompletion E) N

abbrev PFin : Type := Πʳ v : HeightOneSpectrum (𝓞 E), [GL (Fin N) (v.adicCompletion E), AInt E N v]

open GroundTheory.Automorphic.AdelicGLn in

def finInc : FiniteAdelicGL E N →* GA E N :=
  ((prodEquiv E N).symm.toMulEquiv.toMonoidHom).comp (MonoidHom.inr _ _)

open GroundTheory.Automorphic.AdelicGLn in
theorem continuous_finInc : Continuous (finInc E N) :=
  (prodEquiv E N).symm.continuous.comp (continuous_const.prodMk continuous_id)

open GroundTheory.Automorphic.AdelicGLn in

theorem isMulRightInvariant_GA (μ : Measure (GA E N)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  classical
  refine isMulRightInvariant_of_modularCharacter μ fun g => ?_
  let e := restrictedProductEquiv E N
  let Δ : PInf E N × PFin E N →* ℝ≥0 := (Measure.modularCharacter : GA E N →* ℝ≥0).comp e.symm.toMulEquiv.toMonoidHom
  have hΔ : ∀ z, Δ z = Measure.modularCharacter (e.symm z) := fun _ => rfl
  have hcen : ∀ z, (∀ h, z * h = h * z) → Δ z = 1 := fun z hz => by
    rw [hΔ]
    refine modularCharacter_eq_one_of_central μ fun h => ?_
    have := hz (e h)
    apply e.injective
    simpa [map_mul] using this
  have hinf : ∀ (w : InfinitePlace E) (x : GL (Fin N) w.Completion),
      Δ (Pi.mulSingle w x, 1) = 1 := fun w x => by
    let ι : GL (Fin N) w.Completion →* PInf E N × PFin E N :=
      (MonoidHom.inl (PInf E N) (PFin E N)).comp (MonoidHom.mulSingle (fun w : InfinitePlace E => GL (Fin N) w.Completion) w)
    refine GlobalTheory.SplitFlip.hom_eq_one_of_center (Δ.comp ι) (fun c hc => hcen _ fun h => ?_) x
    refine Prod.ext (funext fun u => ?_) (by simp [ι])
    by_cases hu : u = w
    · subst hu
      simpa [ι] using hc (h.1 u)
    · simp [ι, Pi.mulSingle_eq_of_ne hu]
  have hfin : ∀ (v : HeightOneSpectrum (𝓞 E)) (x : GL (Fin N) (v.adicCompletion E)),
      Δ (1, RestrictedProduct.mulSingle (AInt E N) v x) = 1 := fun v x => by
    let ι : GL (Fin N) (v.adicCompletion E) →* PInf E N × PFin E N :=
      (MonoidHom.inr (PInf E N) (PFin E N)).comp (singleHom (AInt E N) v)
    refine GlobalTheory.SplitFlip.hom_eq_one_of_center (Δ.comp ι) (fun c hc => hcen _ fun h => ?_) x
    refine Prod.ext (by simp [ι]) ?_
    ext u : 1
    by_cases hu : u = v
    · subst hu
      simpa [ι, singleHom, RestrictedProduct.mulSingle_eq_same] using hc (h.2 u)
    · simp [ι, singleHom, RestrictedProduct.mulSingle_eq_of_ne _ _ hu]
  have hint : ∀ b : PFin E N, (∀ v, b v ∈ AInt E N v) → Δ (1, b) = 1 := fun b hb => by
    have hk : (finiteRestrictedEquiv E N).symm b ∈ integralFiniteGL E N :=
      (mem_integralFiniteGL_iff_forall E N).2 (by simpa using hb)
    have hcomp : IsCompact (((integralFiniteGL E N).map (finInc E N) : Subgroup (GA E N)) : Set (GA E N)) := by
      rw [Subgroup.coe_map]
      exact (isCompact_integralFiniteGL E N).image (continuous_finInc E N)
    have he : e.symm (1, b) = finInc E N ((finiteRestrictedEquiv E N).symm b) := by
      apply e.injective
      rw [ContinuousMulEquiv.apply_symm_apply]
      refine Prod.ext ?_ ?_
      · show 1 = infiniteEquiv E N ((prodEquiv E N) ((prodEquiv E N).symm (1, _))).1
        simp
      · show b = finiteRestrictedEquiv E N ((prodEquiv E N) ((prodEquiv E N).symm (1, _))).2
        simp
    rw [hΔ, he]
    exact modularCharacter_eq_one_of_compact μ _ hcomp (Subgroup.mem_map_of_mem _ hk)
  have hall : ∀ z, Δ z = 1 := fun z => by
    have hz : z = (z.1, 1) * (1, z.2) := by simp
    rw [hz, map_mul]
    have a1 : Δ (z.1, 1) = 1 :=
      pi_eq_one (Δ.comp (MonoidHom.inl (PInf E N) (PFin E N))) (fun w x => hinf w x) z.1
    have a2 : Δ (1, z.2) = 1 :=
      restricted_eq_one (Δ.comp (MonoidHom.inr (PInf E N) (PFin E N))) (fun v x => hfin v x) (fun b hb => hint b hb) z.2
    rw [a1, a2, one_mul]
  have := hall (e g)
  rwa [hΔ, ContinuousMulEquiv.symm_apply_apply] at this

end Adelic

theorem isMulRightInvariant_GA_CM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (μ : Measure (GA E N)) [μ.IsHaarMeasure], μ.IsMulRightInvariant :=
  fun E _ _ _ N μ _ => isMulRightInvariant_GA E N μ

end GlobalTheory.CompanionTheory.AdelicUnimod
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterOrthogonality
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem integral_mul_tsum_unimod {ι X : Type} [Countable ι] [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    {c : ι → X → ℂ} {h : X → ℂ} {a : ι → ℂ} (hc : ∀ i, AEStronglyMeasurable (c i) ν)
    (hc1 : ∀ i x, ‖c i x‖ = 1) (hh : AEStronglyMeasurable h ν) {B : ℝ} (hB : ∀ x, ‖h x‖ ≤ B)
    (ha : Summable fun i => ‖a i‖) :
    ∫ x, h x * ∑' i, c i x * a i ∂ν = ∑' i, (∫ x, h x * c i x ∂ν) * a i := by
  have hbd : ∀ i x, ‖h x * (c i x * a i)‖ ≤ B * ‖a i‖ := fun i x => by
    rw [norm_mul, norm_mul, hc1, one_mul]
    exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)
  have hint : ∀ i, Integrable (fun x => h x * (c i x * a i)) ν := fun i =>
    Integrable.of_bound (hh.mul ((hc i).mul aestronglyMeasurable_const)) (B * ‖a i‖)
      (Eventually.of_forall (hbd i))
  have hsum : Summable fun i => ∫ x, ‖h x * (c i x * a i)‖ ∂ν := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun x => norm_nonneg _) (fun i => ?_)
      ((ha.mul_left B).mul_left (ν.real Set.univ))
    calc ∫ x, ‖h x * (c i x * a i)‖ ∂ν ≤ ∫ _, B * ‖a i‖ ∂ν :=
          integral_mono (hint i).norm (integrable_const _) (hbd i)
      _ = ν.real Set.univ * (B * ‖a i‖) := by simp [integral_const]
  have key := hasSum_integral_of_summable_integral_norm hint hsum
  have e1 : ∀ x, ∑' i, h x * (c i x * a i) = h x * ∑' i, c i x * a i := fun x => tsum_mul_left
  have e2 : ∀ i, ∫ x, h x * (c i x * a i) ∂ν = (∫ x, h x * c i x ∂ν) * a i := fun i => by
    rw [← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only [mul_assoc])
  simp only [e1, e2] at key
  exact key.tsum_eq.symm

theorem parseval {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (b₀ : HermE D ρ) (hb₀ : b₀.1.det ≠ 0) (a b : Matrix (Fin ρ) (Fin p) D.host.E → ℂ)
    (ha : Summable (fun η => ‖a η‖)) (hb : Summable (fun η => ‖b η‖)) :
    ∫ x in m.𝓕, (∑' η : Matrix (Fin ρ) (Fin p) D.host.E, chv ψ b₀ x (rt η) * a η) *
        conj (∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, chv ψ b₀ x (rt ξ) * b ξ) ∂m.μ =
      ∑' η : Matrix (Fin ρ) (Fin p) D.host.E, a η * conj (b η) := by
  classical
  obtain ⟨-, hadd, hnorm, hneg, -, hcont⟩ := GlobalTheory.T.heisenberg_character_bilinear_laws (p := p) ψ hψ b₀
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : Countable (Matrix (Fin ρ) (Fin p) D.host.E) :=
    inferInstanceAs (Countable (Fin ρ → Fin p → D.host.E))
  haveI : IsProbabilityMeasure (m.μ.restrict m.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact m.hμ.2.2⟩
  have hcm : ∀ η : Matrix (Fin ρ) (Fin p) D.host.E,
      StronglyMeasurable (fun x : Mx D ρ p => chv ψ b₀ x (rt η)) := fun η =>
    (hcont.comp (Continuous.prodMk continuous_id continuous_const)).stronglyMeasurable
  have hcm' : ∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E,
      StronglyMeasurable (fun x : Mx D ρ p => conj (chv ψ b₀ x (rt ξ))) := fun ξ =>
    Complex.continuous_conj.comp_stronglyMeasurable (hcm ξ)
  have hc1 : ∀ (η : Matrix (Fin ρ) (Fin p) D.host.E) (x : Mx D ρ p), ‖chv ψ b₀ x (rt η)‖ = 1 :=
    fun η x => hnorm x _
  have hc1' : ∀ (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (x : Mx D ρ p),
      ‖conj (chv ψ b₀ x (rt ξ))‖ = 1 := fun ξ x => by rw [RCLike.norm_conj]; exact hc1 ξ x
  have horth : ∀ ξ η : Matrix (Fin ρ) (Fin p) D.host.E,
      ∫ x in m.𝓕, conj (chv ψ b₀ x (rt ξ)) * chv ψ b₀ x (rt η) ∂m.μ = if η = ξ then 1 else 0 := by
    intro ξ η
    by_cases h : η = ξ
    · subst h
      have e : ∀ x : Mx D ρ p, conj (chv ψ b₀ x (rt η)) * chv ψ b₀ x (rt η) = 1 := fun x => by
        rw [Complex.conj_mul', hc1]; simp
      simp [e]
    · have e : ∀ x : Mx D ρ p, conj (chv ψ b₀ x (rt ξ)) * chv ψ b₀ x (rt η) =
          chv ψ b₀ x (rt (η - ξ)) := fun x => by
        have hr : (rt (η - ξ) : Mx D ρ p) = rt η + -rt ξ := by
          rw [← sub_eq_add_neg]; exact rat_sub η ξ
        rw [hr, hadd, hneg, mul_comm]
      simp only [e, if_neg h]
      exact GlobalTheory.T.heisenberg_character_integral_vanishes m ψ hψ b₀ hb₀ (η - ξ) (sub_ne_zero.2 h)
  have hs : ∀ x : Mx D ρ p, Summable fun η => chv ψ b₀ x (rt η) * a η := fun x =>
    Summable.of_norm (by simpa only [norm_mul, hc1, one_mul] using ha)
  have hfm : StronglyMeasurable fun x : Mx D ρ p => ∑' η, chv ψ b₀ x (rt η) * a η :=
    tsum_meas (fun η => (hcm η).mul_const _) hs
  have hfB : ∀ x : Mx D ρ p, ‖∑' η, chv ψ b₀ x (rt η) * a η‖ ≤ ∑' η, ‖a η‖ := fun x => by
    have h1 := norm_tsum_le_tsum_norm (f := fun η => chv ψ b₀ x (rt η) * a η)
      (by simpa only [norm_mul, hc1, one_mul] using ha)
    simpa only [norm_mul, hc1, one_mul] using h1
  have hcoef : ∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E,
      ∫ x in m.𝓕, (∑' η, chv ψ b₀ x (rt η) * a η) * conj (chv ψ b₀ x (rt ξ)) ∂m.μ = a ξ := by
    intro ξ
    have h1 := integral_mul_tsum_unimod (m.μ.restrict m.𝓕)
      (c := fun (η : Matrix (Fin ρ) (Fin p) D.host.E) (x : Mx D ρ p) => chv ψ b₀ x (rt η))
      (h := fun x => conj (chv ψ b₀ x (rt ξ))) (a := a) (B := 1)
      (fun η => (hcm η).aestronglyMeasurable) hc1 (hcm' ξ).aestronglyMeasurable
      (fun x => (hc1' ξ x).le) ha
    simp only [horth, ite_mul, one_mul, zero_mul, tsum_ite_eq] at h1
    rw [← h1]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have hconj : ∀ x : Mx D ρ p, conj (∑' ξ, chv ψ b₀ x (rt ξ) * b ξ) =
      ∑' ξ, conj (chv ψ b₀ x (rt ξ)) * conj (b ξ) := fun x => by
    rw [Complex.conj_tsum]; simp only [map_mul]
  have h2 := integral_mul_tsum_unimod (m.μ.restrict m.𝓕)
    (c := fun (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (x : Mx D ρ p) => conj (chv ψ b₀ x (rt ξ)))
    (h := fun x => ∑' η, chv ψ b₀ x (rt η) * a η) (a := fun ξ => conj (b ξ))
    (fun ξ => (hcm' ξ).aestronglyMeasurable) hc1' hfm.aestronglyMeasurable hfB
    (by simpa only [RCLike.norm_conj] using hb)
  simp only [hconj, h2, hcoef]

end GlobalTheory.CompanionTheory.FJE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFormPrimitiveVectorPairing
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreePartner

theorem isReduced_tens (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] [IsReduced R] : IsReduced (R ⊗[F] E) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Algebra.FormallyEtale F E := Algebra.FormallyEtale.of_isSeparable F E
  haveI : Algebra.FormallySmooth F E := inferInstance
  haveI : Algebra.FinitePresentation F E := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Algebra.Smooth F E := ⟨inferInstance, inferInstance⟩
  haveI : Algebra.Smooth R (R ⊗[F] E) := inferInstance
  exact GlobalTheory.isReduced_algebra_of_smooth_of_isReduced R (R ⊗[F] E)

theorem isUnit_det_JR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (h : J.det ≠ 0) :
    IsUnit (JR (F := F) R J).det := by
  have e : (JR (F := F) R J).det = inclR (F := F) R J.det := by
    rw [RingHom.map_det]
    rfl
  rw [e]
  exact (IsUnit.mk0 _ h).map _

theorem exists_partner : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ x : Fin M → R ⊗[F] E, LinearIndependent (R ⊗[F] E) (fun _ : Fin 1 => x) → ∃ y : Fin M → R ⊗[F] E, hR R σ J x y = 1 := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hloc x hx
  obtain ⟨-, -, -, -, hA, hRed, -, -⟩ := hloc
  haveI := hA
  haveI := hRed
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsArtinianRing (R ⊗[F] E) := IsArtinianRing.of_finite R _
  haveI : IsReduced (R ⊗[F] E) := isReduced_tens F E R
  have hinv : ∀ z : R ⊗[F] E, sigR R σ (sigR R σ z) = z :=
    HermTop.sigR_sigR R (HermTop.sigma_sigma hσ)
  have hlip := FreeOpen.lip_of_artinian_reduced (R ⊗[F] E)
  obtain ⟨P, hP⟩ := hlip (Fin M) (Fin 1)
    (Matrix.of fun i (_ : Fin 1) => sigR R σ (x i)) (by
      intro c hc
      have h1 : ∀ i, sigR R σ (x i) * c 0 = 0 := by
        intro i
        have := congrFun hc i
        simpa [Matrix.mulVec, dotProduct] using this
      have h2 : sigR R σ (c 0) • x = 0 := by
        funext i
        have := congrArg (sigR R σ) (h1 i)
        rw [map_mul, hinv, map_zero] at this
        simpa [mul_comm] using this
      have h3 := Fintype.linearIndependent_iff.mp hx (fun _ => sigR R σ (c 0)) (by simpa using h2) 0
      have h4 : c 0 = 0 := by
        have := congrArg (sigR R σ) h3
        simpa [hinv] using this
      funext j
      rw [Subsingleton.elim j 0]
      simpa using h4)
  have hu := isUnit_det_JR (F := F) R hJ.2
  refine ⟨(JR R J)⁻¹ *ᵥ (fun j => P 0 j), ?_⟩
  have hv : JR R J *ᵥ ((JR R J)⁻¹ *ᵥ (fun j => P 0 j)) = fun j => P 0 j := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have h00 := congrFun (congrFun hP 0) 0
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply_eq] at h00
  have hform' : hR R σ J x ((JR R J)⁻¹ *ᵥ (fun j => P 0 j)) =
      ∑ i, sigR R σ (x i) * (JR R J *ᵥ ((JR R J)⁻¹ *ᵥ (fun j => P 0 j))) i := by
    simp only [hR, hform, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [hform', hv, ← h00]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GlobalTheory.CompanionTheory.WeilSiegel.FreePartner
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisAlt
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.PfSWUS.MonoSplit

theorem main : ∀ (D : D7) (n : ℕ) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (fr : D.what₂.Tau → GL (Fin V.rank) ℂ) (e : D.what₂.Tau × Fin V.rank × Fin n × Bool →₀ ℕ) (c : ℂ), Nonempty D.what₂.Tau → (∀ τ, ((fr τ).1)ᴴ * (gramAt D V τ * s τ) * (fr τ).1 = 1) → ∃ P : D.what₂.Tau → PositivityTheory.Rg.Sw.PX V.rank n, ∀ z : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ, evalPoly (MvPolynomial.monomial e c) z * gauss V l s z = ∏ τ, PositivityTheory.Rg.Sw.evX (P τ) (((fr τ)⁻¹).1 * z τ) * PositivityTheory.Rg.Sw.gs (2 * Real.pi * |l τ|) (((fr τ)⁻¹).1 * z τ) := by
  classical
  intro D n V l s fr e c hne hfr
  obtain ⟨τ0⟩ := hne
  obtain ⟨PG, hPG⟩ : ∃ PG : D.what₂.Tau → PositivityTheory.Rg.Sw.PX V.rank n, ∀ τ,
      PG τ = MvPolynomial.C (if τ = τ0 then c else 1) *
        ∏ k ∈ e.support, (if k.1 = τ then PositivityTheory.PfSWUS.SwSpanR.lz (fr τ).1 k.2 else 1) ^ (e k) :=
    ⟨_, fun τ => rfl⟩
  refine ⟨PG, fun z => ?_⟩
  have hinv : ∀ τ, (fr τ).1 * ((fr τ)⁻¹).1 = 1 := fun τ => Units.mul_inv (fr τ)
  have hZ : ∀ τ, (fr τ).1 * (((fr τ)⁻¹).1 * z τ) = z τ := fun τ => by
    rw [← Matrix.mul_assoc, hinv τ, Matrix.one_mul]

  have hG : gauss V l s z = ∏ τ, PositivityTheory.Rg.Sw.gs (2 * Real.pi * |l τ|) (((fr τ)⁻¹).1 * z τ) := by
    unfold gauss PositivityTheory.Rg.Sw.gs
    rw [← Complex.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [PositivityTheory.PfSWUS.SwSpanR.trace_frame (fr τ).1 ((fr τ)⁻¹).1 _ _ (hinv τ) (hfr τ),
      PositivityTheory.PfSWUS.SwSpanR.trace_ct_mul_self]
    push_cast
    ring

  have hP : evalPoly (MvPolynomial.monomial e c) z =
      ∏ τ, PositivityTheory.Rg.Sw.evX (PG τ) (((fr τ)⁻¹).1 * z τ) := by
    set f : D.what₂.Tau × Fin V.rank × Fin n × Bool → ℂ := fun k =>
      if k.2.2.2 then (starRingEnd ℂ) (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1 with hf
    have hτ : ∀ τ, PositivityTheory.Rg.Sw.evX (PG τ) (((fr τ)⁻¹).1 * z τ) =
        (if τ = τ0 then c else 1) * ∏ k ∈ e.support, (if k.1 = τ then f k else 1) ^ (e k) := fun τ => by
      rw [hPG τ]
      simp only [PositivityTheory.Rg.Sw.evX, map_mul, MvPolynomial.eval_C, map_prod, map_pow]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      by_cases h : k.1 = τ
      · subst h
        rw [if_pos rfl, if_pos rfl]
        have := PositivityTheory.PfSWUS.SwSpanR.evX_lz (fr k.1).1 (((fr k.1)⁻¹).1 * z k.1) k.2
        unfold PositivityTheory.Rg.Sw.evX at this
        rw [this, hZ k.1, hf]
        simp only [starRingEnd_apply]
      · rw [if_neg h, if_neg h, map_one]
    simp only [hτ]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ τ0, if_pos (Finset.mem_univ _),
      Finset.prod_comm]
    unfold evalPoly
    rw [MvPolynomial.eval_monomial]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [ite_pow, one_pow]
    rw [Finset.prod_ite_eq Finset.univ k.1, if_pos (Finset.mem_univ _)]
    simp only [hf, ite_pow]
  rw [hP, hG, ← Finset.prod_mul_distrib]

end GlobalTheory.CompanionTheory.PfSWUS.MonoSplit
end
end

