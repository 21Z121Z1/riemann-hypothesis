import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0348
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0188
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0349
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0307

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorOfRationalLocalDuality
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BkCoeff

open GlobalTheory.PstCoeff

variable {l : ℕ} [Fact l.Prime]

section Cob

variable {G : Type} [Group G] [TopologicalSpace G] {K₀ K : Type} [Field K₀] [Field K]
    [Algebra ℚ_[l] K₀] [Algebra ℚ_[l] K] [Algebra K₀ K] [IsScalarTower ℚ_[l] K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra ℚ_[l] B] [Algebra K₀ B] [IsScalarTower ℚ_[l] K₀ B]
    [Algebra ℚ_[l] BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower ℚ_[l] K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower ℚ_[l] K₀ BdR]
    (PD : PeriodData G ℚ_[l] K₀ K B BdR)

theorem cyclotomicTwist_differential_apply {LL : Type} [Field LL] [Algebra ℚ_[l] LL] (f : G → LL) (x : G × G) :
    ReciprocityTheory.Def.d1 (charRep (cycLL PD LL)) f x =
      algebraMap ℚ_[l] LL (PD.χ x.1 : ℚ_[l]) * f x.2 - f (x.1 * x.2) + f x.1 := by
  simp [ReciprocityTheory.Def.d1, charRep, cycLL, Algebra.smul_def]

theorem cobL_iff_trace {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
    [FiniteDimensional ℚ_[l] LL] [IsModuleTopology ℚ_[l] LL] (z : G × G → LL) :
    CobL PD z ↔ ∀ c : LL, CobL PD (fun x => Algebra.trace ℚ_[l] LL (c * z x)) := by
  haveI : ContinuousAdd LL := IsModuleTopology.toContinuousAdd ℚ_[l] LL
  haveI : ContinuousSMul ℚ_[l] LL := IsModuleTopology.toContinuousSMul ℚ_[l] LL
  constructor
  · rintro ⟨f, hf, rfl⟩ c
    refine ⟨fun g => Algebra.trace ℚ_[l] LL (c * f g), ?_, ?_⟩
    · exact (IsModuleTopology.continuous_of_linearMap
        ((Algebra.trace ℚ_[l] LL).comp (LinearMap.mulLeft ℚ_[l] c))).comp hf
    · funext x
      rw [cyclotomicTwist_differential_apply, cyclotomicTwist_differential_apply]
      have e1 : c * (algebraMap ℚ_[l] LL (PD.χ x.1 : ℚ_[l]) * f x.2 - f (x.1 * x.2) + f x.1) =
          (PD.χ x.1 : ℚ_[l]) • (c * f x.2) - c * f (x.1 * x.2) + c * f x.1 := by
        rw [Algebra.smul_def]; ring
      rw [e1, map_add, map_sub, map_smul, smul_eq_mul]
      simp
  · intro h
    choose f hf using h
    have hB := traceForm_nondegenerate ℚ_[l] LL
    let b := Module.finBasis ℚ_[l] LL
    let d := (Algebra.traceForm ℚ_[l] LL).dualBasis hB b
    refine ⟨fun g => ∑ i, f (b i) g • d i, ?_, ?_⟩
    · exact continuous_finsetSum _ fun i _ => ((hf (b i)).1).smul continuous_const
    · funext x
      rw [cyclotomicTwist_differential_apply]
      have hz : z x = ∑ i, (d.repr (z x) i) • d i := (d.sum_repr (z x)).symm
      have hc : ∀ i, d.repr (z x) i = (PD.χ x.1 : ℚ_[l]) * f (b i) x.2 - f (b i) (x.1 * x.2) + f (b i) x.1 := by
        intro i
        rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm,
          ← congrFun (hf (b i)).2 x, cyclotomicTwist_differential_apply]
        simp
      rw [hz]
      simp_rw [hc, add_smul, sub_smul, mul_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.smul_sum, Algebra.smul_def]

end Cob

section Main

variable (P : LocPrime l) {K : FinExt l}

def trPair {LL V V' : Type} [Field LL] [Algebra ℚ_[l] LL]
    [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    (Pr : V →ₗ[LL] V' →ₗ[LL] LL) : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l] :=
  LinearMap.mk₂ ℚ_[l] (fun x y => Algebra.trace ℚ_[l] LL (Pr x y))
    (fun x x' y => by simp)
    (fun c x y => by simp [LinearMap.map_smul_of_tower])
    (fun x y y' => by simp)
    (fun c x y => by simp [LinearMap.map_smul_of_tower])

theorem trPair_apply {LL V V' : Type} [Field LL] [Algebra ℚ_[l] LL]
    [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    (Pr : V →ₗ[LL] V' →ₗ[LL] LL) (x : V) (y : V') :
    trPair Pr x y = Algebra.trace ℚ_[l] LL (Pr x y) := rfl

theorem isDual1_trPair {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL]
    {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'} {Pr : V →ₗ[LL] V' →ₗ[LL] LL}
    (hP : IsDual1 (P.PD K) ρ ρ' Pr) : IsDual1 (P.PD K) (resQ ρ) (resQ ρ') (trPair Pr) := by
  have hB := traceForm_nondegenerate ℚ_[l] LL
  obtain ⟨h1, h2, h3, h4⟩ := hP
  refine ⟨fun g x y => ?_, fun x hx => h2 x fun y => ?_, fun y hy => h3 y fun x => ?_, ?_⟩
  · rw [resQ_apply, resQ_apply, trPair_apply, trPair_apply, h1]
    have e : ((cycLL (P.PD K) LL g : LLˣ) : LL) * Pr x y = ((P.PD K).χ g : ℚ_[l]) • Pr x y := by
      simp [cycLL, Algebra.smul_def]
    rw [e, map_smul, smul_eq_mul]
    simp [cycLL]
  · refine hB.1 _ fun c => ?_
    rw [Algebra.traceForm_apply, mul_comm, ← smul_eq_mul, ← map_smul]
    exact hx (c • y)
  · refine hB.1 _ fun c => ?_
    rw [Algebra.traceForm_apply, mul_comm, ← smul_eq_mul, ← LinearMap.smul_apply, ← map_smul]
    exact hy (c • x)
  · rw [← Module.finrank_mul_finrank ℚ_[l] LL V, ← Module.finrank_mul_finrank ℚ_[l] LL V', h4]

end Main

end GlobalTheory.BkCoeff

namespace GlobalTheory

open GlobalTheory.PstCoeff GlobalTheory.BkCoeff

theorem bkACore_of_rationalDuality (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l)
    (h : GlobalTheory.Published.BlochKato.RationalDuality (P.PD K)) : bkACore (P.PD K) := by
  intro LL _ _ _ O _ _ hO A A' Pr hdR hP
  obtain ⟨-, hfin, hmt, htr, -⟩ := hO
  haveI := hfin
  haveI := hmt
  haveI := htr
  haveI : FiniteDimensional ℚ_[l] A.V := Module.Finite.trans LL A.V
  haveI : FiniteDimensional ℚ_[l] A'.V := Module.Finite.trans LL A'.V
  haveI : IsModuleTopology ℚ_[l] A.V := isModuleTopology_of_tower ℚ_[l] LL A.V
  haveI : IsModuleTopology ℚ_[l] A'.V := isModuleTopology_of_tower ℚ_[l] LL A'.V
  haveI : ContinuousConstSMul ℚ_[l] A.V := ⟨fun c => by
    have hc : Continuous fun x : A.V => algebraMap ℚ_[l] LL c • x := continuous_const_smul _
    simpa only [algebraMap_smul] using hc⟩
  haveI : ContinuousConstSMul ℚ_[l] A'.V := ⟨fun c => by
    have hc : Continuous fun x : A'.V => algebraMap ℚ_[l] LL c • x := continuous_const_smul _
    simpa only [algebraMap_smul] using hc⟩
  have key := h A.V A'.V (resQ A.ρ) (resQ A'.ρ) (trPair Pr) A.cont A'.cont
    ((isDR_resQ_iff P A.ρ).mpr hdR) (isDual1_trPair P hP)
  have cupS : ∀ (c : LL) (a : ↥(GK K) → A.V) (b : ↥(GK K) → A'.V),
      cupL (resQ A'.ρ) (trPair Pr) a (c • b) = fun x => Algebra.trace ℚ_[l] LL (c * cupL A'.ρ Pr a b x) := by
    intro c a b; funext x
    simp [cupL, trPair_apply]
  have cupS' : ∀ (c : LL) (a : ↥(GK K) → A.V) (b : ↥(GK K) → A'.V),
      cupL (resQ A'.ρ) (trPair Pr) (c • a) b = fun x => Algebra.trace ℚ_[l] LL (c * cupL A'.ρ Pr a b x) := by
    intro c a b; funext x
    simp [cupL, trPair_apply]
  have cup1 : ∀ (a : ↥(GK K) → A.V) (b : ↥(GK K) → A'.V),
      cupL (resQ A'.ρ) (trPair Pr) a b = fun x => Algebra.trace ℚ_[l] LL (1 * cupL A'.ρ Pr a b x) := by
    intro a b; funext x
    simp [cupL, trPair_apply]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rw [← mem_finiteCocycles_restrictScalars_Ql P, (key.1 a ha)]
    constructor
    · intro H b hb
      rw [cobL_iff_trace]
      intro c
      rw [← cupS]
      exact H (c • b) ((mem_finiteCocycles_restrictScalars_Ql P _ _).mpr ((finiteCocycles (P.PD K) A'.ρ).smul_mem c hb))
    · intro H b hb
      have := (cobL_iff_trace (P.PD K) _).mp (H b ((mem_finiteCocycles_restrictScalars_Ql P _ _).mp hb)) 1
      rwa [← cup1] at this
  · rw [← mem_finiteCocycles_restrictScalars_Ql P, (key.2 b hb)]
    constructor
    · intro H a ha
      rw [cobL_iff_trace]
      intro c
      rw [← cupS']
      exact H (c • a) ((mem_finiteCocycles_restrictScalars_Ql P _ _).mpr ((finiteCocycles (P.PD K) A.ρ).smul_mem c ha))
    · intro H a ha
      have := (cobL_iff_trace (P.PD K) _).mp (H a ((mem_finiteCocycles_restrictScalars_Ql P _ _).mp ha)) 1
      rwa [← cup1] at this

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockSumSemisimple
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem isSS_blockSum_of_isIrred {k Γ : Type} [Field k] [Group Γ] {r t : ℕ}
    (ρ : Γ →* Matrix (Fin r) (Fin r) k) (χ : Fin t → (Γ →* kˣ))
    (hρ : GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsIrred (matRep ρ)) : IsSS (GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum ρ χ) := by
  classical
  refine isSS_of_sSup_irreducible_eq_top _
    ({LinearMap.range (LinearMap.inl k (Fin r → k) (Fin t → k))} ∪
      Set.range fun c : Fin t =>
        Submodule.span k {((0, Pi.single c 1) : (Fin r → k) × (Fin t → k))}) ?_ ?_
  · rintro U (rfl | ⟨c, rfl⟩)
    · have key : ∀ g (v : Fin r → k), GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum ρ χ g
          (LinearMap.inl k (Fin r → k) (Fin t → k) v) =
          LinearMap.inl k (Fin r → k) (Fin t → k) (matRep ρ g v) := by
        intro g v
        rw [GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum_apply]
        refine Prod.ext rfl (funext fun c => ?_)
        simp
      refine ⟨?_, fun U' hle hU' => ?_⟩
      · rintro g _ ⟨v, rfl⟩
        exact ⟨_, (key g v).symm⟩
      · have hst : Stable (matRep ρ) (U'.comap (LinearMap.inl k (Fin r → k) (Fin t → k))) := by
          intro g v hv
          rw [Submodule.mem_comap, ← key]
          exact hU' g _ hv
        have hmap := Submodule.map_comap_eq_self hle
        rcases hρ.2 _ hst with h | h
        · left
          rw [← hmap, h, Submodule.map_bot]
        · right
          rw [← hmap, h, Submodule.map_top]
    · refine ⟨?_, fun U' hle _ => ?_⟩
      · intro g v hv
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
        refine Submodule.mem_span_singleton.2 ⟨a * ((χ c g : kˣ) : k), ?_⟩
        rw [GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum_apply]
        refine Prod.ext ?_ (funext fun c' => ?_)
        · simp
        · by_cases h : c' = c
          · subst h
            simp [mul_comm]
          · simp [h]
      · have hne : ((0, Pi.single c 1) : (Fin r → k) × (Fin t → k)) ≠ 0 := by
          intro h
          have := congrFun (congrArg Prod.snd h) c
          simp at this
        exact (nonzero_span_atom _ hne).le_iff.1 hle
  · rw [eq_top_iff]
    rintro ⟨v, w⟩ -
    have hdec : ((v, w) : (Fin r → k) × (Fin t → k)) =
        LinearMap.inl k (Fin r → k) (Fin t → k) v +
          ∑ c : Fin t, w c • ((0, Pi.single c 1) : (Fin r → k) × (Fin t → k)) := by
      refine Prod.ext ?_ (funext fun c' => ?_)
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    rw [hdec]
    refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_)
    · exact Submodule.mem_sSup.2 fun N hN => hN _ (Or.inl rfl) ⟨v, rfl⟩
    · exact Submodule.mem_sSup.2 fun N hN =>
        hN _ (Or.inr ⟨c, rfl⟩) (Submodule.mem_span_singleton_self _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEvWIsUnitInjectiveDvdStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_evW_isUnit_injective_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), IsUnit (bk.evW bk.E) ∧ Function.Injective bk.evW ∧ ∀ x : bk.S, ((l : ℕ) : Ainf l) ∣ bk.ev x → ((l : ℕ) : bk.S) ∣ x := by
  first | exact @GlobalTheory.BSP.BK.evW_isUnit_injective_dvd | exact GlobalTheory.BSP.BK.evW_isUnit_injective_dvd | (intros; apply GlobalTheory.BSP.BK.evW_isUnit_injective_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinExistsAdicSumOfNullFamilyStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_exists_adic_sum_of_null_family : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type) (TB : TopBasis bk.ev bk.J ι) (σ : ι → bk.S), (∀ n : ℕ, {i | σ i ∉ bk.J ^ n}.Finite) → ∃ L : Ainf l, ∀ n : ℕ, ∃ F : Finset ι, ∀ G : Finset ι, F ⊆ G → L - ∑ i ∈ G, bk.ev (σ i) * TB.b i ∈ (bk.J ^ n).map bk.ev := by
  first | exact @GlobalTheory.BSP.exists_sum_null_ev | exact GlobalTheory.BSP.exists_sum_null_ev | (intros; apply GlobalTheory.BSP.exists_sum_null_ev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFactsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_flat_radius_ideal_facts : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), bk.flat ≠ 0 ∧ ¬ IsUnit bk.flat ∧ (0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹) ∧ Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S) ^ bk.Ep.natDegree} = bk.J := by
  first | exact @GlobalTheory.BSP.flat_disc | exact GlobalTheory.BSP.flat_disc | (intros; apply GlobalTheory.BSP.flat_disc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomImageXDeltaZeroLiftsUniformizer
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem hf_X_δ_and_str : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Obj l ↥(OL K)) (g : Hom bk.prism C), C.D.δ (BK.hf g X) = 0 ∧ Ideal.Quotient.mk C.I (BK.hf g X) = C.str (bk.str.symm (Ideal.Quotient.mk _ X)) := by
  intro l _ K bk C g
  have hδX : (deltaS l bk.a).δ (X : (Wq l bk.a)⟦X⟧) = 0 := by
    have h := (deltaS l bk.a).φ_eq (X : (Wq l bk.a)⟦X⟧)
    have h2 : (deltaS l bk.a).φ (X : (Wq l bk.a)⟦X⟧) = X ^ l := frobS_X l bk.a
    rw [h2] at h
    have h3 : (l : (Wq l bk.a)⟦X⟧) * (deltaS l bk.a).δ X = 0 := by linear_combination -h
    exact (mul_eq_zero.1 h3).resolve_left (l_ne_zero l bk.a)
  refine ⟨?_, ?_⟩
  · have h := g.f_δ (X : (Wq l bk.a)⟦X⟧)
    change C.D.δ (g.f X) = 0
    rw [← h]
    change g.f ((deltaS l bk.a).δ X) = 0
    rw [hδX]
    exact g.f.map_zero
  · refine g.f_str (bk.str.symm (Ideal.Quotient.mk _ X)) X ?_
    change Ideal.Quotient.mk (Ideal.span {bk.E}) X = bk.str (bk.str.symm (Ideal.Quotient.mk _ X))
    rw [RingEquiv.apply_symm_apply]

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeFrameCocyclesLinked
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.LinkCocycle

theorem dvd_of_inclW {l : ℕ} [Fact l.Prime] (n : ℕ) : ∀ (a : Ainf l) (w : WCb l),
    inclW l a = (l : WCb l) ^ n * w → (l : Ainf l) ^ n ∣ a := by
  induction n with
  | zero => intro a w _; exact ⟨a, by simp⟩
  | succ n ih =>
    intro a w h
    obtain ⟨a₁, ha₁⟩ := GlobalTheory.HWL.TensorWitt.ainf_saturated_in_tiltWitt_prime a ((l : WCb l) ^ n * w) (by rw [h]; ring)
    obtain ⟨c, hc⟩ := ih a₁ w ha₁
    have h1 : a = (l : Ainf l) * a₁ := GlobalTheory.HWL.TensorWitt.inclW_injective (by
      rw [map_mul, map_natCast, ha₁, h]; ring)
    exact ⟨c, by rw [h1, hc]; ring⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N N' d d' n : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') (ℤ_[l])) (F : Frame bk N d ρ) (F' : Frame bk N' d' ρ') (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])) (R : Matrix (Fin d) (Fin d') (bk.S)), (∀ g i j, (l : ℤ_[l]) ^ n ∣ (Pi * ρ' g - ρ g * Pi) i j) → (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - F.T * R.map bk.evW) i j) → ∀ (g : ↥(GK K)) i j, (l : Ainf l) ^ n ∣ (F.ε g * (R.map bk.ev).map (Per.σA (g : GQ l)) - R.map bk.ev * F'.ε g) i j := by
  intro l _ K bk N N' d d' n ρ ρ' F F' Pi R hPi hR g i j
  classical
  choose M hM using hPi g
  choose D hD using hR
  set c : WCb l := (l : WCb l) ^ n with hc
  set σ : WCb l →+* WCb l := ((galW l (g : GQ l) : WCb l ≃ₐ[ℤ_[l]] WCb l) : WCb l →+* WCb l) with hσ
  set T := F.T
  set T' := F'.T
  set P := zW Pi
  set A := zW (ρ g)
  set A' := zW (ρ' g)
  set Rw := (R.map bk.ev).map (inclW l)
  set Rgw := ((R.map bk.ev).map (Per.σA (g : GQ l))).map (inclW l)
  set E := (F.ε g).map (inclW l)
  set E' := (F'.ε g).map (inclW l)
  set Ds : Matrix (Fin d) (Fin d') (WCb l) := Matrix.of D
  set Mw : Matrix (Fin d) (Fin d') (WCb l) := zW (Matrix.of M)
  have e1 : A * T.map σ = T * E := F.gal g
  have e2 : A' * T'.map σ = T' * E' := F'.gal g
  have e3 : P * T' - T * Rw = c • Ds := Matrix.ext fun i j => by
    simpa [Ds, Rw, BK.evW, Matrix.map_map] using hD i j
  have e4 : P * T'.map σ - T.map σ * Rgw = c • Ds.map σ := by
    have hP : P.map σ = P := Matrix.ext fun i j => by simp [P, zW, σ]
    have hRg : Rw.map σ = Rgw := Matrix.ext fun i j => by simp [Rw, Rgw, σ, galW_inclW]
    have : (P * T' - T * Rw).map σ = (c • Ds).map σ := by rw [e3]
    rw [Matrix.map_sub _ (map_sub σ), Matrix.map_mul, Matrix.map_mul] at this
    rw [hP, hRg] at this
    rw [this]; ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hc, map_pow, map_natCast]
  have e5 : P * A' - A * P = c • Mw := by
    have hM' : Pi * ρ' g - ρ g * Pi = ((l : ℤ_[l]) ^ n) • Matrix.of M := Matrix.ext fun i j => by simpa using hM i j
    have : (Pi * ρ' g - ρ g * Pi).map (algebraMap ℤ_[l] (WCb l)) = (((l : ℤ_[l]) ^ n) • Matrix.of M).map (algebraMap ℤ_[l] (WCb l)) := by rw [hM']
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul] at this
    rw [this]; ext i j; simp [Mw, zW, c]
  have key : T * (E * Rgw - Rw * E') = (c • Ds) * E' - (c • Mw) * T'.map σ - A * (c • Ds.map σ) := by
    rw [← e3, ← e4, ← e5]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc T E, ← e1, ← e2]
    simp only [Matrix.mul_assoc]
    abel
  have key2 : T * (E * Rgw - Rw * E') = c • (Ds * E' - Mw * T'.map σ - A * Ds.map σ) := by
    rw [key, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_sub]
  have hT : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T ((Matrix.isUnit_iff_isUnit_det T).mp F.unit)
  have hX : E * Rgw - Rw * E' = c • (T⁻¹ * (Ds * E' - Mw * T'.map σ - A * Ds.map σ)) := by
    rw [← Matrix.mul_smul, ← key2, ← Matrix.mul_assoc, hT, Matrix.one_mul]
  have hY : (F.ε g * (R.map bk.ev).map (Per.σA (g : GQ l)) - R.map bk.ev * F'.ε g).map (inclW l) =
      E * Rgw - Rw * E' := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul]
  refine dvd_of_inclW n _ ((T⁻¹ * (Ds * E' - Mw * T'.map σ - A * Ds.map σ)) i j) ?_
  have := congrFun (congrFun (hY.trans hX) i) j
  simpa [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hc] using this
end GlobalTheory.BKLim.LinkCocycle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinMemIdealPowOfXPowMulMemStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_mem_ideal_pow_of_X_pow_mul_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N : ℕ), ∃ n : ℕ, ∀ m : ℕ, ∃ n' : ℕ, ∀ s : bk.S, (X : bk.S) ^ m * s ∈ bk.J ^ n' ⊔ Ideal.span {(l : bk.S) ^ n} → s ∈ bk.J ^ N := by
  first | exact @GlobalTheory.BSP.BK.mem_J_pow_of_X_pow_mul_mem | exact GlobalTheory.BSP.BK.mem_J_pow_of_X_pow_mul_mem | (intros; apply GlobalTheory.BSP.BK.mem_J_pow_of_X_pow_mul_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinNormEisensteinLeRadiusStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_norm_eisenstein_le_radius : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A), 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ ((l : ℝ)⁻¹ ≤ bk.ρ₀) ∧ ‖toDisc l (s X) bk.ρ₀ (s bk.E)‖ ≤ (l : ℝ)⁻¹ := by
  first | exact @GlobalTheory.BSP.norm_E_le_radius | exact GlobalTheory.BSP.norm_E_le_radius | (intros; apply GlobalTheory.BSP.norm_E_le_radius <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitAndAinfSaturatedStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_period_isUnit_and_ainf_saturated : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → IsUnit (inclW l τ) ∧ (∀ g : GQ l, IsUnit (inclW l (Per.σA g τ))) ∧ ∀ (k : ℕ) (a : Ainf l), ((l : ℕ) : WCb l) ^ k ∣ inclW l a → ((l : ℕ) : Ainf l) ^ k ∣ a := by
  first | exact @GlobalTheory.BSP.isUnit_inclW_per_and_saturated | exact GlobalTheory.BSP.isUnit_inclW_per_and_saturated | (intros; apply GlobalTheory.BSP.isUnit_inclW_per_and_saturated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrimeUniformizerClassStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_prime_uniformizer_class : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), Prime (bk.str.symm (Ideal.Quotient.mk _ (X : bk.S))) ∧ intToOC K (bk.str.symm (Ideal.Quotient.mk _ (X : bk.S))) = bk.flat.untilt := by
  first | exact @GlobalTheory.BSP.BK.prime_unif | exact GlobalTheory.BSP.BK.prime_unif | (intros; apply GlobalTheory.BSP.BK.prime_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCoproductHomEqOfAgreeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinPrismCoproduct_hom_eq_of_agree : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (d p : B.A) (En : Env bk B d p) (C : Type) [CommRing C] (φ : C →+* C) (F F' : En.Q.A →+* C), (∀ c : C, ((l : ℕ) : C) * c = 0 → c = 0) → (∀ a, F (En.Q.D.φ a) = φ (F a)) → (∀ a, F' (En.Q.D.φ a) = φ (F' a)) → (∀ b, F (En.inl.f b) = F' (En.inl.f b)) → F (BK.hf En.inr X) = F' (BK.hf En.inr X) → F (En.inl.f d) ∈ nonZeroDivisors C → IsHausdorff ((Ideal.span {((l : ℕ) : B.A)} ⊔ B.I).map (F.comp En.inl.f)) C → F = F' := by
  first | exact @GlobalTheory.BSP.envExt_agree | exact GlobalTheory.BSP.envExt_agree | (intros; apply GlobalTheory.BSP.envExt_agree <;> assumption)
end

