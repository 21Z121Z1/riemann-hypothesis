import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0615
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0603
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0258
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0610
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0244
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0033
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0611
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0616
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableSeedOfAcrisPeriods

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialRankinSelbergProductConjSwapRealStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_rankinSelberg_product_conj_swap_real : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' → ∀ x : ℝ, 1 < x → ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ (x : ℂ) w.1 = starRingEnd ℂ (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1) := by
  first | exact @GlobalTheory.RSConj.partial_conj | exact GlobalTheory.RSConj.partial_conj | (intros; apply GlobalTheory.RSConj.partial_conj; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDataDualExact
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

open Formalism.MainNotions.N (twistRep coefRep)

namespace GlobalTheory.AdmLoc

theorem mk_mem_H1fX_iff_inHfX {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀]
    [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module O V]
    [IsScalarTower O LL V] {ρ : Representation LL G V} [TopologicalSpace V] [ContinuousAdd V]
    [ContinuousConstSMul LL V] (L : Lattice (O := O) ρ) (ρ' : Representation LL G V) (L' : Lattice (O := O) ρ')
    (X : Type) [AddCommGroup X] [Module O X] (χ : G →* Oˣ) :
    (∀ g, ρ' g = ((tableLineDegreeTwo.charL (LL := LL) χ g)⁻¹ : LLˣ).val • ρ g) → L'.T = L.T →
    ∀ (z : G → ↥L.T ⊗[O] X) (hz : z ∈ Z1 (twCoef (latRep L) χ X) ⊤),
      (Submodule.Quotient.mk ⟨z, hz⟩ ∈ finiteSelmer PD L χ X ↔ tableLineDegreeTwo.InHfX PD L L' X χ z) := by
  intro hρ hT z hz
  have e1 : ρ' = twistRep ρ (chiLL LL χ⁻¹) := by
    ext g v
    rw [hρ g, twistRep_apply]
    simp [chiLL, tableLineDegreeTwo.charL]
  subst e1
  have e2 : L' = twLattice L χ⁻¹ := by
    cases L'
    simp only at hT
    subst hT
    rfl
  subst e2
  have hact : ∀ g (m : ↥L.T ⊗[O] X), twCoef (latRep L) χ X g m = tableLineDegreeTwo.actTw L X χ g m := by
    intro g m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      rw [coefRep_tmul, twistRep_apply]
      simp only [tableLineDegreeTwo.actTw, LinearMap.smul_apply, LinearMap.rTensor_tmul, smul_tmul']
      rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  have hA : toAmb (twCoef (latRep L) χ X) (Submodule.Quotient.mk ⟨z, hz⟩) = Submodule.Quotient.mk z := rfl
  rw [finiteSelmer, Submodule.mem_comap, hA, LinearMap.mem_range]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨S, rfl⟩ := TensorProduct.exists_finset u
    have hrep : ∀ p : ↥(latticeFiniteCohomology PD (twLattice L χ⁻¹)), ∃ c : ↥(latticeCocycles (twLattice L χ⁻¹)),
        (c : G → V) ∈ latticeFiniteCocycles PD (twLattice L χ⁻¹) ∧ Submodule.Quotient.mk c = (p : LatticeCohomology (twLattice L χ⁻¹)) := by
      rintro ⟨p, hp⟩
      obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hp
      exact ⟨c, hc, rfl⟩
    choose rep hrepf hrepmk using hrep
    let e := S.equivFin
    let cc : Fin S.card → ↥(latticeCocycles (twLattice L χ⁻¹)) := fun j => rep (e.symm j).1.1
    let xx : Fin S.card → X := fun j => (e.symm j).1.2
    have key : (tensAmb L χ X ∘ₗ (latticeFiniteCohomology PD (twLattice L χ⁻¹)).subtype.rTensor X)
        (∑ p ∈ S, p.1 ⊗ₜ[O] p.2) = Submodule.Quotient.mk (∑ j, tensCoc L χ X (cc j) (xx j)) := by
      rw [map_sum, ← Finset.sum_coe_sort S, ← e.symm.sum_comp]
      refine Eq.trans ?_ (map_sum (Submodule.mkQ _) _ _).symm
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [LinearMap.comp_apply, LinearMap.rTensor_tmul, Submodule.subtype_apply, ← hrepmk, tensAmb_tmul]
      rfl
    rw [key] at hu
    obtain ⟨m, -, hm⟩ := (Submodule.Quotient.eq _).mp hu
    refine ⟨S.card, fun j g => evT (twLattice L χ⁻¹) g (cc j), xx, -m, fun j => hrepf _, fun g => ?_⟩
    have h1 : twCoef (latRep L) χ X g m - m = (∑ j, tensCoc L χ X (cc j) (xx j)) g - z g := congrFun hm g
    simp only [Finset.sum_apply] at h1
    rw [hact] at h1
    simp only [map_neg]
    have h2 : ∀ j, tensCoc L χ X (cc j) (xx j) g = evT (twLattice L χ⁻¹) g (cc j) ⊗ₜ[O] xx j := fun j => rfl
    simp only [h2] at h1
    have h3 : z g = ∑ j, evT (twLattice L χ⁻¹) g (cc j) ⊗ₜ[O] xx j - (tableLineDegreeTwo.actTw L X χ g m - m) := by
      rw [h1]; abel
    rw [h3]
    abel
  · rintro ⟨k, c, x, m, hc, hzc⟩
    let cc : Fin k → ↥(latticeCocycles (twLattice L χ⁻¹)) := fun j => ⟨fun g => (c j g : V), (hc j).1⟩
    refine ⟨∑ j, (⟨Submodule.Quotient.mk (cc j), Submodule.mem_map_of_mem (hc j)⟩ :
      ↥(latticeFiniteCohomology PD (twLattice L χ⁻¹))) ⊗ₜ[O] x j, ?_⟩
    rw [map_sum]
    have h1 : ∀ j, (tensAmb L χ X ∘ₗ (latticeFiniteCohomology PD (twLattice L χ⁻¹)).subtype.rTensor X)
        ((⟨Submodule.Quotient.mk (cc j), Submodule.mem_map_of_mem (hc j)⟩ :
          ↥(latticeFiniteCohomology PD (twLattice L χ⁻¹))) ⊗ₜ[O] x j) = Submodule.mkQ _ (tensCoc L χ X (cc j) (x j)) := fun j => rfl
    simp only [h1]
    rw [← map_sum, Submodule.mkQ_apply]
    refine (Submodule.Quotient.eq _).mpr ?_
    refine Submodule.mem_map.mpr ⟨-m, Submodule.mem_top, ?_⟩
    funext g
    change twCoef (latRep L) χ X g (-m) - (-m) = (∑ j, tensCoc L χ X (cc j) (x j)) g - z g
    simp only [Finset.sum_apply, hact, map_neg, hzc g]
    have h2 : ∀ j, tensCoc L χ X (cc j) (x j) g = c j g ⊗ₜ[O] x j := fun j => rfl
    simp only [h2]
    abel

end GlobalTheory.AdmLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingsRegularPhiSurjectiveFilStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodRings_regular_phi_surjective_fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) ∧ (∀ u : P.R.B, ∃ x, x - P.φB x = u) ∧ ∀ (K : FinExt l) (w : P.R.BdR), ∃ x : P.R.B, P.φB x = x ∧ P.ιB x - w ∈ (P.PD K).Fil 0 := by
  first | exact @GlobalTheory.MemLoc.tied_regular_and_onto | exact GlobalTheory.MemLoc.tied_regular_and_onto | (intros; apply GlobalTheory.MemLoc.tied_regular_and_onto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodicEqZeroOfFourierCoefficientsZero
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

variable {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι]

theorem dot_add_right (ξ : ι → E) (x y : ι → Ad E) : dot ξ (x + y) = dot ξ x + dot ξ y := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dot_add_left (ξ η : ι → E) (x : ι → Ad E) : dot (ξ + η) x = dot ξ x + dot η x := by
  simp only [dot, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem dot_zero_left (x : ι → Ad E) : dot (0 : ι → E) x = 0 := by
  simp [dot]

theorem dot_rat (ξ c : ι → E) :
    dot ξ (fun t => algebraMap E (Ad E) (c t)) = algebraMap E (Ad E) (∑ t, ξ t * c t) := by
  simp only [dot, map_sum, map_mul]

theorem dot_single [DecidableEq ι] (t : ι) (c : E) (x : ι → Ad E) :
    dot (Pi.single t c) x = algebraMap E (Ad E) c * x t := by
  rw [dot, Finset.sum_eq_single t]
  · simp
  · intro s _ hs
    simp [Pi.single_eq_of_ne hs]
  · simp

theorem StdPsi.forall_dot_eq_one_iff {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (x : ι → Ad E) :
    (∀ ξ : ι → E, ψ (-dot ξ x) = 1) ↔ x ∈ ratV E ι := by
  classical
  constructor
  · intro h
    have hx : ∀ t, ∃ d : E, x t = algebraMap E (Ad E) d := by
      intro t
      refine hψ.ann _ fun c => ?_
      have h1 := h (Pi.single t c)
      rw [dot_single, AddChar.map_neg_eq_inv, inv_eq_one] at h1
      rwa [mul_comm]
    choose d hd using hx
    exact ⟨d, funext fun t => (hd t).symm⟩
  · rintro ⟨c, rfl⟩ ξ
    have e : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom ι) c =
        fun t => algebraMap E (Ad E) (c t) := rfl
    rw [e, dot_rat, AddChar.map_neg_eq_inv, hψ.rat, inv_one]

theorem StdPsi.per_twist {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {Φ : (ι → Ad E) → ℂ} (hΦ : Per (ratV E ι) Φ)
    (ξ : ι → E) : Per (ratV E ι) (fun x => ψ (-dot ξ x) * Φ x) := by
  refine ⟨(hψ.cont.comp (continuous_dot ξ).neg).mul hΦ.1, ?_⟩
  rintro _ ⟨c, rfl⟩ x
  have e : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom ι) c =
      fun t => algebraMap E (Ad E) (c t) := rfl
  have h2 := hΦ.2 _ ⟨c, rfl⟩ x
  simp only
  rw [h2, AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv, e, hψ.map_dot ξ c x]

theorem eq_zero_of_avg_character_eq_zero : ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι]
    (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ Φ : (ι → Ad E) → ℂ, Per (ratV E ι) Φ →
    (∀ ξ : ι → E, avg (ratV E ι) (fun x => ψ (-dot ξ x) * Φ x) = 0) → Φ = 0 := by
  intro E _ _ ι _ ψ hψ Φ hΦ hco
  letI : MeasurableSpace (ι → Ad E) := borel _
  haveI : BorelSpace (ι → Ad E) := ⟨rfl⟩
  have hL := isCoLat_ratV E ι
  obtain ⟨hd, K, hK, hcov⟩ := id hL
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice (ι → Ad E) (ratV E ι) hL
  haveI := hd
  refine GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (ι → Ad E) (ratV E ι) K hK hcov (ι → E)
    (fun ξ x => ψ (-dot ξ x)) (fun ξ => hψ.cont.comp (continuous_dot ξ).neg) ?_ ?_ ?_
    (fun ξ x => hψ.norm _) (hψ.forall_dot_eq_one_iff) μ 𝓕 hμ h𝓕 Φ hΦ.1 hΦ.2 ?_
  · intro ξ x y
    rw [dot_add_right, neg_add, AddChar.map_add_eq_mul]
  · intro ξ η x
    rw [dot_add_left, neg_add, AddChar.map_add_eq_mul]
  · intro x
    rw [dot_zero_left, neg_zero, AddChar.map_zero_eq_one]
  · intro ξ
    have h2 := (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average (ι → Ad E) (ratV E ι) hL μ 𝓕 hμ h𝓕 _ (hψ.per_twist hΦ ξ)).2.2.2
    rw [h2, hco ξ, mul_zero]

end GlobalTheory.CuspGeneric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageAddOfPeriodic
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem avg_add_of_per : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ →
    ∀ Φ Φ' : G → ℂ, Per Γ Φ → Per Γ Φ' → avg Γ (fun x => Φ x + Φ' x) = avg Γ Φ + avg Γ Φ' := by
  intro G _ _ _ _ _ _ Γ hΓ Φ Φ' h h'
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, hF, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G Γ hΓ
  have hs : Per Γ (fun x => Φ x + Φ' x) :=
    ⟨h.1.add h'.1, fun γ hγ x => by simp only [h.2 γ hγ x, h'.2 γ hγ x]⟩
  obtain ⟨-, -, i1, e1⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ 𝓕 hμ hF Φ h
  obtain ⟨-, -, i2, e2⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ 𝓕 hμ hF Φ' h'
  obtain ⟨-, -, -, e3⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ 𝓕 hμ hF _ hs
  rw [h1] at e1 e2 e3
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at e1 e2 e3
  rw [← e1, ← e2, ← e3]
  exact integral_add i1 i2

end GlobalTheory.CuspGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageMapLatticeEquiv
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem avg_equiv : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (G' : Type) [AddCommGroup G'] [TopologicalSpace G'] [IsTopologicalAddGroup G'] [LocallyCompactSpace G'] [SecondCountableTopology G'] [T2Space G'] (Γ : AddSubgroup G) (Γ' : AddSubgroup G'), IsCoLat Γ → IsCoLat Γ' → ∀ e : G ≃ₜ+ G', (∀ x, e x ∈ Γ' ↔ x ∈ Γ) → ∀ Φ : G' → ℂ, Per Γ' Φ → avg Γ (fun x => Φ (e x)) = avg Γ' Φ := by
  intro G _ _ _ _ _ _ G' _ _ _ _ _ _ Γ Γ' hΓ hΓ' e he Φ hΦ
  letI mG : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  letI mG' : MeasurableSpace G' := borel G'
  haveI : BorelSpace G' := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G Γ hΓ
  let f : G ≃ᵐ G' := e.toHomeomorph.toMeasurableEquiv
  haveI := hμ
  have hμ' : (μ.map f).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  let eΓ : Γ' ≃ Γ :=
    { toFun := fun g => ⟨e.symm g, (he _).1 (by simpa using g.2)⟩
      invFun := fun x => ⟨e x, (he x).2 x.2⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  have hqmp : Measure.QuasiMeasurePreserving f.toEquiv.symm (μ.map f) μ :=
    MeasurePreserving.quasiMeasurePreserving ⟨f.symm.measurable, f.map_symm_map⟩
  have h𝓕' : IsAddFundamentalDomain Γ' (f '' 𝓕) (μ.map f) := by
    refine h𝓕.image_of_equiv f.toEquiv hqmp eΓ fun g x => ?_
    show e (e.symm (g : G') + x) = (g : G') + e x
    rw [map_add, ContinuousAddEquiv.apply_symm_apply]
  have hm : (μ.map f) (f '' 𝓕) = 1 := by
    rw [MeasurableEquiv.map_apply, Set.preimage_image_eq _ f.injective, h1]
  have hΦ' : Per Γ (fun x => Φ (e x)) :=
    ⟨hΦ.1.comp e.continuous, fun γ hγ x => by show Φ (e (γ + x)) = Φ (e x); rw [map_add]; exact hΦ.2 _ ((he γ).2 hγ) _⟩
  have A := (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G' Γ' hΓ' (μ.map f) (f '' 𝓕) hμ' h𝓕' Φ hΦ).2.2.2
  have B := (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ 𝓕 hμ h𝓕 _ hΦ').2.2.2
  rw [hm] at A
  rw [h1] at B
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at A B
  rw [← A, ← B, f.measurableEmbedding.setIntegral_map, Set.preimage_image_eq _ f.injective]
  rfl

end GlobalTheory.CuspGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageProdFubini
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

section Prod

variable {G₁ : Type} [AddCommGroup G₁] [TopologicalSpace G₁] [IsTopologicalAddGroup G₁]
  {G₂ : Type} [AddCommGroup G₂] [TopologicalSpace G₂] [IsTopologicalAddGroup G₂]

theorem isCoLat_prod {Γ₁ : AddSubgroup G₁} {Γ₂ : AddSubgroup G₂} (h₁ : IsCoLat Γ₁) (h₂ : IsCoLat Γ₂) :
    IsCoLat (Γ₁.prod Γ₂) := by
  obtain ⟨d₁, K₁, hK₁, c₁⟩ := h₁
  obtain ⟨d₂, K₂, hK₂, c₂⟩ := h₂
  refine ⟨?_, K₁ ×ˢ K₂, hK₁.prod hK₂, fun z => ?_⟩
  · refine DiscreteTopology.of_continuous_injective
      (f := fun z : Γ₁.prod Γ₂ => ((⟨z.1.1, (AddSubgroup.mem_prod.1 z.2).1⟩ : Γ₁),
        (⟨z.1.2, (AddSubgroup.mem_prod.1 z.2).2⟩ : Γ₂))) ?_ ?_
    · exact ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
    · intro a b h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      exact Subtype.ext (Prod.ext h.1 h.2)
  · obtain ⟨γ₁, hγ₁, e₁⟩ := c₁ z.1
    obtain ⟨γ₂, hγ₂, e₂⟩ := c₂ z.2
    exact ⟨(γ₁, γ₂), AddSubgroup.mem_prod.2 ⟨hγ₁, hγ₂⟩, ⟨e₁, e₂⟩⟩

end Prod

section FD

open Pointwise

variable {G₁ : Type} [AddCommGroup G₁] [MeasurableSpace G₁]
  {G₂ : Type} [AddCommGroup G₂] [MeasurableSpace G₂]

theorem vadd_prod_set {Γ₁ : AddSubgroup G₁} {Γ₂ : AddSubgroup G₂} (g : Γ₁.prod Γ₂) (A : Set G₁) (B : Set G₂) :
    g +ᵥ (A ×ˢ B) = ((g : G₁ × G₂).1 +ᵥ A) ×ˢ ((g : G₁ × G₂).2 +ᵥ B) := by
  ext ⟨x, y⟩
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_prod]
  rfl

theorem isAddFundamentalDomain_prod {Γ₁ : AddSubgroup G₁} {Γ₂ : AddSubgroup G₂} {μ₁ : Measure G₁} {μ₂ : Measure G₂}
    [SFinite μ₁] [SFinite μ₂] {𝓕₁ : Set G₁} {𝓕₂ : Set G₂}
    (h₁ : IsAddFundamentalDomain Γ₁ 𝓕₁ μ₁) (h₂ : IsAddFundamentalDomain Γ₂ 𝓕₂ μ₂) :
    IsAddFundamentalDomain (Γ₁.prod Γ₂) (𝓕₁ ×ˢ 𝓕₂) (μ₁.prod μ₂) where
  nullMeasurableSet := h₁.nullMeasurableSet.prod h₂.nullMeasurableSet
  ae_covers := by
    have a₁ : ∀ᵐ z ∂μ₁.prod μ₂, ∃ γ : Γ₁, γ +ᵥ z.1 ∈ 𝓕₁ := Measure.quasiMeasurePreserving_fst.ae h₁.ae_covers
    have a₂ : ∀ᵐ z ∂μ₁.prod μ₂, ∃ γ : Γ₂, γ +ᵥ z.2 ∈ 𝓕₂ := Measure.quasiMeasurePreserving_snd.ae h₂.ae_covers
    filter_upwards [a₁, a₂] with z ⟨γ₁, e₁⟩ ⟨γ₂, e₂⟩
    exact ⟨⟨((γ₁ : G₁), (γ₂ : G₂)), AddSubgroup.mem_prod.2 ⟨γ₁.2, γ₂.2⟩⟩, ⟨e₁, e₂⟩⟩
  aedisjoint := by
    intro g g' hne
    change μ₁.prod μ₂ ((g +ᵥ (𝓕₁ ×ˢ 𝓕₂)) ∩ (g' +ᵥ (𝓕₁ ×ˢ 𝓕₂))) = 0
    rw [vadd_prod_set, vadd_prod_set, Set.prod_inter_prod, Measure.prod_prod]
    by_cases e : (g : G₁ × G₂).1 = (g' : G₁ × G₂).1
    · have e2 : (g : G₁ × G₂).2 ≠ (g' : G₁ × G₂).2 := fun e2 => hne (Subtype.ext (Prod.ext e e2))
      have := h₂.aedisjoint (i := ⟨(g : G₁ × G₂).2, (AddSubgroup.mem_prod.1 g.2).2⟩)
        (j := ⟨(g' : G₁ × G₂).2, (AddSubgroup.mem_prod.1 g'.2).2⟩) (fun h => e2 (congrArg Subtype.val h))
      rw [show μ₂ (((g : G₁ × G₂).2 +ᵥ 𝓕₂) ∩ ((g' : G₁ × G₂).2 +ᵥ 𝓕₂)) = 0 from this, mul_zero]
    · have := h₁.aedisjoint (i := ⟨(g : G₁ × G₂).1, (AddSubgroup.mem_prod.1 g.2).1⟩)
        (j := ⟨(g' : G₁ × G₂).1, (AddSubgroup.mem_prod.1 g'.2).1⟩) (fun h => e (congrArg Subtype.val h))
      rw [show μ₁ (((g : G₁ × G₂).1 +ᵥ 𝓕₁) ∩ ((g' : G₁ × G₂).1 +ᵥ 𝓕₁)) = 0 from this, zero_mul]

end FD

section Main

theorem avg_prod (G₁ : Type) [AddCommGroup G₁] [TopologicalSpace G₁] [IsTopologicalAddGroup G₁]
    [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁]
    (G₂ : Type) [AddCommGroup G₂] [TopologicalSpace G₂] [IsTopologicalAddGroup G₂]
    [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂]
    (Γ₁ : AddSubgroup G₁) (Γ₂ : AddSubgroup G₂) (h₁ : IsCoLat Γ₁) (h₂ : IsCoLat Γ₂)
    (Φ : G₁ × G₂ → ℂ) (hΦ : Per (Γ₁.prod Γ₂) Φ) :
    avg (Γ₁.prod Γ₂) Φ = avg Γ₁ (fun x => avg Γ₂ (fun y => Φ (x, y))) := by
  letI m₁ : MeasurableSpace G₁ := borel G₁
  haveI : BorelSpace G₁ := ⟨rfl⟩
  letI m₂ : MeasurableSpace G₂ := borel G₂
  haveI : BorelSpace G₂ := ⟨rfl⟩
  have e₁ : ∃ p : Measure G₁ × Set G₁, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ₁ p.2 p.1 ∧ p.1 p.2 = 1 := by
    obtain ⟨μ, F, a, b, c⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G₁ Γ₁ h₁
    exact ⟨(μ, F), a, b, c⟩
  have e₂ : ∃ p : Measure G₂ × Set G₂, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ₂ p.2 p.1 ∧ p.1 p.2 = 1 := by
    obtain ⟨μ, F, a, b, c⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G₂ Γ₂ h₂
    exact ⟨(μ, F), a, b, c⟩
  have A₁ : ∀ Ψ : G₁ → ℂ, avg Γ₁ Ψ = ∫ x in e₁.choose.2, Ψ x ∂e₁.choose.1 := fun Ψ => dif_pos e₁
  have A₂ : ∀ Ψ : G₂ → ℂ, avg Γ₂ Ψ = ∫ y in e₂.choose.2, Ψ y ∂e₂.choose.1 := fun Ψ => dif_pos e₂
  obtain ⟨H₁, F₁, M₁⟩ := e₁.choose_spec
  obtain ⟨H₂, F₂, M₂⟩ := e₂.choose_spec
  set μ₁ := e₁.choose.1
  set 𝓕₁ := e₁.choose.2
  set μ₂ := e₂.choose.1
  set 𝓕₂ := e₂.choose.2
  have hFD : IsAddFundamentalDomain (Γ₁.prod Γ₂) (𝓕₁ ×ˢ 𝓕₂) (μ₁.prod μ₂) := isAddFundamentalDomain_prod F₁ F₂
  have hM : μ₁.prod μ₂ (𝓕₁ ×ˢ 𝓕₂) = 1 := by rw [Measure.prod_prod, M₁, M₂, one_mul]
  obtain ⟨-, -, hI, hE⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average (G₁ × G₂) (Γ₁.prod Γ₂) (isCoLat_prod h₁ h₂) (μ₁.prod μ₂) (𝓕₁ ×ˢ 𝓕₂)
    inferInstance hFD Φ hΦ
  rw [hM, ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hE
  rw [← hE, setIntegral_prod _ hI, A₁]
  simp only [A₂]

end Main

end GlobalTheory.CuspGeneric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageTranslateInvariant
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem avg_add_right (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G) (hΓ : IsCoLat Γ) (Φ : G → ℂ) (hΦ : Per Γ Φ) (y : G) :
    avg Γ (fun x => Φ (x + y)) = avg Γ Φ := by
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G Γ hΓ
  have hΨ : Per Γ (fun x => Φ (x + y)) :=
    ⟨hΦ.1.comp (continuous_add_right y), fun γ hγ x => by simp only [add_assoc, hΦ.2 γ hγ]⟩

  have hpres : MeasurePreserving (fun x : G => x - y) μ μ := by
    simpa [sub_eq_add_neg] using measurePreserving_add_right μ (-y)
  have h𝓕' : IsAddFundamentalDomain Γ ((fun x : G => x - y) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv hpres.quasiMeasurePreserving (e := id) Function.bijective_id (fun γ x => by
      simp only [id, AddSubgroup.vadd_def, vadd_eq_add]; abel)
  have hm' : μ ((fun x : G => x - y) ⁻¹' 𝓕) = 1 := by
    rw [hpres.measure_preimage h𝓕.nullMeasurableSet, h1]
  have hA := (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ 𝓕 hμ h𝓕 _ hΨ).2.2.2
  have hB := (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ _ hμ h𝓕' Φ hΦ).2.2.2
  rw [h1] at hA
  rw [hm'] at hB
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hA hB
  rw [← hA, ← hB]
  have hpres2 : MeasurePreserving (fun x : G => x + y) μ μ := measurePreserving_add_right μ y
  have hemb : MeasurableEmbedding (fun x : G => x + y) := (MeasurableEquiv.addRight y).measurableEmbedding
  have := hpres2.setIntegral_preimage_emb hemb Φ ((fun x : G => x - y) ⁻¹' 𝓕)
  rw [← this]
  have hs : (fun x : G => x + y) ⁻¹' ((fun x : G => x - y) ⁻¹' 𝓕) = 𝓕 := by
    ext x; simp
  rw [hs]

end GlobalTheory.CuspGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelGaloisComparisonMatrixStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rel_galois_comparison_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (g : ↥(GK K)) (ε : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ε → bk.iA τ ^ s.N • (((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * ht.Y.map (Per.σA (g : GQ l))).map bk.iA) = bk.iA (Per.σA (g : GQ l) τ) ^ s.N • (ht.Y.map bk.iA * ε) := by
  first | exact @GlobalTheory.BSP.Height.rel_gal | exact GlobalTheory.BSP.Height.rel_gal | (intros; apply GlobalTheory.BSP.Height.rel_gal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrameIsDeRhamStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistablePeriodFrame_isDeRham : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (N : ℕ) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T → IsUnit Z → (∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev i → s.W * Z.map i = Y.map bk.iA) → (∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G → IsDiscMap bk.ev i → G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * (F.ε g).map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G)) → F.IsDR := by
  first | (exact @GlobalTheory.BKLim.WDR.frame_isDR) | (exact GlobalTheory.BKLim.WDR.frame_isDR) | (intros; apply GlobalTheory.BKLim.WDR.frame_isDR  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableSeedModuleLAdicClosedStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistableSeed_module_lAdic_closed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ y : ℕ → Fin d → Ainf l, (∀ n, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (y n)) → (∀ n a, (l : Ainf l) ^ n ∣ y (n + 1) a - y n a) → ∀ z : Fin d → Ainf l, (∀ n a, (l : Ainf l) ^ n ∣ z a - y n a) → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) z := by
  first | exact @GlobalTheory.BKLim.wseed_module_lAdic_closed | exact GlobalTheory.BKLim.wseed_module_lAdic_closed | (intros; apply GlobalTheory.BKLim.wseed_module_lAdic_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableSeedOfAcrisPeriodsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistableSeed_of_acris_periods : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (N c₁ c₂ c₃ k₀ : ℕ) (F F' : Matrix (Fin d) (Fin d) (Wq l bk.a)) (X X' : Matrix (Fin d) (Fin d) (bk.S)) (Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l)) (κ : ↥(GK K) → Matrix (Fin d) (Fin d) (Per.Acris l)), (F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) ∧ X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), (C.t ^ N * (l : Per.Acris l) ^ k₀) • ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • (Z * κ g)) ∧ (∀ g : ↥(GK K), bk.FixFlat g → κ g = (l : Per.Acris l) ^ k₀ • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N)) ∧ ∀ m : ℕ, ∃ (k : ℕ) (Λ : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, bk.E ∣ (Λ - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) (bk.S))) i j) ∧ ∀ (g : ↥(GK K)) i j, C.j ((κ g * (Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l)) - (l : Per.Acris l) ^ k₀ • Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l m) → Nonempty (WSeed bk d ρ τ) := by
  first | exact @GlobalTheory.BKLim.wseed_of_periods | exact GlobalTheory.BKLim.wseed_of_periods | (intros; apply GlobalTheory.BKLim.wseed_of_periods <;> assumption)
end

