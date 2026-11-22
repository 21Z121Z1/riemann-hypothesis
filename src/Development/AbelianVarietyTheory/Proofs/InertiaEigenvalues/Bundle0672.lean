import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0662
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import BuildAid.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0663
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0552
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0647
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0629
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0479
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0523
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0598
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0551
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0135
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0144
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0122
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0125
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0123
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0146
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0124
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0665
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.MainFinal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0661
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyLocalisedFormsTypeSectionHecke
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsQuotientOfSpehTypeProductIsLStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlandsQuotient_of_speh_type_product_isL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
    GlobalTheory.Published.StandardCosocleGL → (∀ (δ δ' : IrrGL k) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
    IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) → (∀ (d h : ℕ) (y : Fin d → Fin h → IrrGL k) (N : Fin d → ℕ) (M : ℕ) (hN : ∀ i, ∑ j, (y i j).1 = N i)
    (hM : ∑ i, N i = M)
    (hM' : ∑ p : Fin (d * h), (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1 = M),
    Nonempty ((multiProd (stdBlocks N hM) fun i => prodIrr (y i) (hN i)).Equiv
      (prodIrr (fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) hM'))) →
    ∀ (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin a) k) V)
    (m : ℕ) (δ : Fin m → IrrGL k) (Δ : Fin m → Segment k) (s : Fin m → ℝ), (∀ j, IsLSeg (Δ j) (δ j).rep) →
      (∀ j, IsUnitarisable (δ j).rep) → (∀ j, |s j| < 1 / 2) → ∀ hd : ∑ j, ((δ j).nu (s j)).1 = a,
      Nonempty (σ.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd)) →
    ∀ (d n : ℕ) (hdn : ∑ _ : Fin d, a = n) (W : Type) [AddCommGroup W] [Module ℂ W]
      (σ' : Representation ℂ (GL (Fin n) k) W), σ'.IsIrreducible →
      (∃ f : (multiProd (stdBlocks (fun _ : Fin d => a) hdn) fun i : Fin d =>
        twist σ (detChar (Fin a) (absPow k (((d : ℂ) - 1) / 2 - (i : ℕ))))).IntertwiningMap σ',
        Function.Surjective f) →
      IsL ↑((List.range d).flatMap fun i : ℕ =>
        (List.ofFn fun j => (Δ j).nu (s j)).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ)) σ' := by
  first | exact @GlobalTheory.speh_quotient_isL | exact GlobalTheory.speh_quotient_isL | (intros; apply GlobalTheory.speh_quotient_isL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeApproximationMittagLefflerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeApproximation_mittagLeffler : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), IsUnit T0 → (∀ n i j, R n i j ∈ bk.OE) → (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → ∀ n, ∃ c : ℕ, ∀ m, n ≤ m → ∀ s : Fin (tw.d' n) → bk.S, ∃ s' : Fin (tw.d' m) → bk.S, ∀ i, (l : WCb l) ^ n ∣ ((R n *ᵥ fun j => bk.evW (X ^ c * s j)) - R m *ᵥ fun j => bk.evW (s' j)) i := by
  first | (exact @GlobalTheory.BKLim.mittagLeffler_approx) | (exact GlobalTheory.BKLim.mittagLeffler_approx) | (intros; apply GlobalTheory.BKLim.mittagLeffler_approx  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieDSingleLeviEmbEqZero
section
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace GlobalTheory.UnipZero

theorem mem_unipRad_of_eq_one {R : Type} [CommRing R] {c N : ℕ} {n : Fin c → ℕ}
    {e : (Σ i, Fin (n i)) ≃ Fin N} {p q : Fin N} (hpq : blk e p < blk e q) (u : GL (Fin N) R)
    (hu : ∀ i j, ¬ (i = p ∧ j = q) → (u : Matrix (Fin N) (Fin N) R) i j = (1 : Matrix (Fin N) (Fin N) R) i j) :
    u ∈ unipRad R e := by
  refine mem_unipRad.2 ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
  · have hne : ¬ (i = p ∧ j = q) := by
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hij hpq
    rw [hu i j hne, Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hij
  · have hne : ¬ (e ⟨a, i⟩ = p ∧ e ⟨a, j⟩ = q) := by
      rintro ⟨h1, h2⟩
      have h1' : blk e p = a := by rw [← h1, blk_apply]
      have h2' : blk e q = a := by rw [← h2, blk_apply]
      rw [h1', h2'] at hpq
      exact lt_irrefl _ hpq
    rw [hu _ _ hne]
    simp [Matrix.one_apply, e.injective.eq_iff]

end GlobalTheory.UnipZero

namespace GlobalTheory.UnipZero

theorem lieD_single_leviEmb_eq_zero (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ}
    (n : Fin c → ℕ) (e : (Σ i, Fin (n i)) ≃ Fin N) (ψ : Sm E N)
    (hψ : ∀ u ∈ unipRad (Ad E) e, ∀ g, ψ.1 (u * g) = ψ.1 g) (p q : Fin N) (hpq : blk e p < blk e q)
    (x : Cinf E) (m : ∀ i, GA E (n i)) :
    (lie E N (toL (Matrix.single p q x)) ψ).1 (leviEmb (Ad E) e m) = 0 := by
  set S : Matrix (Fin N) (Fin N) (Cinf E) := Matrix.single p q x with hS
  have hpq' : p ≠ q := by rintro rfl; exact lt_irrefl _ hpq
  have hSS : S * S = 0 := by rw [hS]; simp [hpq'.symm]
  let cc : ℝ → GL (Fin N) (Cinf E) := fun t =>
    ⟨1 + t • S, 1 - t • S, by
      rw [add_mul, one_mul, mul_sub, mul_one, smul_mul_smul_comm, hSS, smul_zero]; abel, by
      rw [sub_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, hSS, smul_zero]; abel⟩
  have h0 : cc 0 = 1 := Units.ext (by simp [cc])
  have hc : HasDerivAt (fun t => toL (cc t).val) (toL S) 0 := by
    have h : HasDerivAt (fun t : ℝ => toL (1 : Matrix (Fin N) (Fin N) (Cinf E)) + t • toL S) ((1 : ℝ) • toL S) 0 :=
      ((hasDerivAt_id (0 : ℝ)).smul_const (toL S)).const_add _
    rw [one_smul] at h
    exact h
  set g := leviEmb (Ad E) e m
  have hmem : ∀ t, infGL E N (cc t) ∈ unipRad (Ad E) e := by
    intro t
    refine mem_unipRad_of_eq_one hpq _ fun i j hij => ?_
    have hij' : ((cc t : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E)) i j =
        (1 : Matrix (Fin N) (Fin N) (Cinf E)) i j := by
      change ((1 : Matrix (Fin N) (Fin N) (Cinf E)) + t • S) i j = _
      have h1 : S i j = 0 := by
        rw [hS, Matrix.single_apply_of_ne]
        exact fun h => hij ⟨h.1.symm, h.2.symm⟩
      rw [Matrix.add_apply, Matrix.smul_apply, h1, smul_zero, add_zero]
    change (1 : Matrix (Fin N) (Fin N) (Ad E)) i j - sInf E ((1 : Matrix (Fin N) (Fin N) (Cinf E)) i j) +
      sInf E (((cc t : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E)) i j) = _
    rw [hij', sub_add_cancel]
  have hconst : (fun t => ψ.1 (g * infGL E N (cc t))) = fun _ => ψ.1 g := by
    funext t
    have hconj : g * infGL E N (cc t) * g⁻¹ ∈ unipRad (Ad E) e :=
      (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer (Ad E) e m) _).1 (hmem t)
    have := hψ _ hconj g
    rwa [inv_mul_cancel_right] at this
  have hd := hasDerivAt_curve ψ g cc (toL S) h0 hc
  rw [hconst] at hd
  rw [lie_apply]
  exact hd.unique (hasDerivAt_const _ _)

end GlobalTheory.UnipZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieMemCompactFiniteVectorsOfMem
section
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace GlobalTheory.LieFin

theorem lie_mem_finVec : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} (X : Lie E N) (φ : Sm E N),
    φ ∈ finVec (cptRep E N) → lie E N X φ ∈ finVec (cptRep E N) := by
  intro E _ _ _ N X φ hφ
  let S : Submodule ℂ (Sm E N) := Submodule.span ℂ (Set.range fun k => cptRep E N k φ)
  haveI : FiniteDimensional ℂ S := hφ
  let b := Module.finBasis ℝ (Lie E N)
  let T : Submodule ℂ (Sm E N) := ⨆ s, S.map (lie E N (b s))
  haveI : FiniteDimensional ℂ T := by
    haveI : ∀ s, FiniteDimensional ℂ (S.map (lie E N (b s))) := fun s => inferInstance
    exact Submodule.finiteDimensional_iSup _
  have key : ∀ (Z : Lie E N) (ψ : Sm E N), ψ ∈ S → lie E N Z ψ ∈ T := by
    intro Z ψ hψ
    rw [← b.sum_repr Z, map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun s _ => ?_
    rw [map_smul, LinearMap.smul_apply]
    have h1 : lie E N (b s) ψ ∈ T :=
      (le_iSup (fun s => S.map (lie E N (b s))) s) (Submodule.mem_map_of_mem hψ)
    have h2 : ((b.repr Z s : ℝ) : ℂ) • lie E N (b s) ψ ∈ T := T.smul_mem _ h1
    simpa [Complex.coe_smul] using h2
  show FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E N k (lie E N X φ)))
  refine Submodule.finiteDimensional_of_le (S₂ := T) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  have e := congrArg (fun f : Module.End ℂ (Sm E N) => f φ) (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) (Matrix.of X))
  simp only [Module.End.mul_apply] at e
  change rt E N (infGL E N (Unitary.toUnits k)) (lie E N X φ) ∈ T
  have eX : toL (Matrix.of X) = X := rfl
  rw [eX] at e
  rw [e]
  exact key _ _ (Submodule.subset_span ⟨k, rfl⟩)

end GlobalTheory.LieFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitVectorMemOEAndAinfStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limitVector_mem_OE_and_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), (∀ n i j, R n i j ∈ bk.OE) → (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → ∀ v : Fin d → WCb l, (∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ i, v i ∈ bk.OE) ∧ ∃ y : Fin d → Ainf l, (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ v) := by
  first | (exact @GlobalTheory.BKLim.limvec_mem) | (exact GlobalTheory.BKLim.limvec_mem) | (intros; apply GlobalTheory.BKLim.limvec_mem  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitVectorsInvertibleBasisOverOEStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limitVectors_invertible_basis_over_OE : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (d' : ℕ → ℕ) (R : ∀ n, Matrix (Fin d) (Fin (d' n)) (WCb l)), (∀ n, ∃ R' : Matrix (Fin (d' n)) (Fin d) (WCb l), (∀ i j, R' i j ∈ bk.OE) ∧ ∀ i j, (l : WCb l) ^ n ∣ (R n * R' - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → (∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ n i j, R n i j ∈ bk.OE) → ∃ V V' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, V i j ∈ bk.OE) ∧ (∀ i j, V' i j ∈ bk.OE) ∧ V * V' = 1 ∧ ∀ j k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ ((fun i => V i j) - R k *ᵥ fun a => bk.evW (s' a)) i := by
  first | (exact @GlobalTheory.LimVec.invertible_basis) | (exact GlobalTheory.LimVec.invertible_basis) | (intros; apply GlobalTheory.LimVec.invertible_basis  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearLatticeCountDescentProof
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open Classical

theorem frame_exists (K : UQ) (B : InvAlg K) (hs : B.P.Separable) :
    ∃ (ι : Type) (_ : Fintype ι) (e π : ι → B.A) (S : Finset ι), IsFrame B e π S := by
  obtain ⟨ι, _, e, S, hP⟩ := GlobalTheory.T.involutionIdempotentDecomposition_of_separable_charpoly K B hs
  have : ∀ i, ∃ y : B.A, i ∈ S → B.Plus y ∧ y * (1 - e i) = 1 - e i ∧ K.eta (Algebra.norm K.E y) = -1 := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨f, hf, hf0, hfld, hS, -⟩ := hP.2 i
      obtain ⟨he, hσ⟩ := hS hi
      obtain ⟨y, hy⟩ := GlobalTheory.T.exists_plus_element_eta_norm_neg_one K B f hf hf0 hfld hσ
      exact ⟨y, fun _ => by rw [he]; exact hy⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose π hπ using this
  exact ⟨ι, inferInstance, e, π, S, hP, fun i hi => hπ i hi⟩

theorem plus_mul {K : UQ} (B : InvAlg K) {x y : B.A} (hx : B.Plus x) (hy : B.Plus y) : B.Plus (x * y) :=
  ⟨hx.1.mul hy.1, by rw [map_mul, hx.2, hy.2]⟩

theorem plus_one {K : UQ} (B : InvAlg K) : B.Plus 1 := ⟨isUnit_one, map_one _⟩

theorem plus_prod {K : UQ} (B : InvAlg K) {ι : Type} (π : ι → B.A) (J : Finset ι) (h : ∀ j ∈ J, B.Plus (π j)) :
    B.Plus (∏ j ∈ J, π j) :=
  Finset.prod_induction _ B.Plus (fun _ _ => plus_mul B) (plus_one B) h

theorem isUnit_a {K : UQ} (B : InvAlg K) (a : K.O) (ha : K.Small a) : IsUnit (algebraMap K.O B.A a) := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A]
  refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
  intro h
  exact ha.1 (IsFractionRing.injective K.O K.E (by rw [h, map_zero]))

theorem lim_HH {K : UQ} (B : InvAlg K) {ι : Type} [Fintype ι] [DecidableEq ι] (e π : ι → B.A) (S : Finset ι) (a : K.O)
    (hB : B.LieReg) (ha : K.Small a) (hF : IsFrame B e π S) (ℓ : B.A → ℝ)
    (hℓ : ∀ x, B.Plus x → B.LinLim a x (ℓ x)) (I : Finset ι) (hI : I ⊆ S) (x : B.A) (hx : B.Plus x) :
    Tendsto (fun k : ℕ => ((HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) atTop
      (𝓝 (∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ ((∏ j ∈ J, π j) * x))) := by
  have hπ : ∀ J ∈ S.powerset, B.Plus ((∏ j ∈ J, π j) * x) := fun J hJ =>
    plus_mul B (plus_prod B π J fun j hj => (hF.2 j (Finset.mem_powerset.1 hJ hj)).1) hx
  have hu : ∀ k : ℕ, IsUnit (x * algebraMap K.O B.A a ^ (2 * k)) := fun k => hx.1.mul ((isUnit_a B a ha).pow _)
  have heq : ∀ k : ℕ, ((HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ) = ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card *
        ((B.GG ((∏ j ∈ J, π j) * x * algebraMap K.O B.A a ^ (2 * k)) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) := by
    intro k
    rw [GlobalTheory.T.signedInvolutionStableLatticeSum_eq_alternating_sum K B ι e π S hB hF I hI _ (hu k)]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [mul_assoc, mul_div_assoc]
  simp_rw [heq]
  exact tendsto_finset_sum _ fun J hJ => (hℓ _ (hπ J hJ)).const_mul _

theorem sum_formula {K : UQ} (B : InvAlg K) {ι : Type} [Fintype ι] [DecidableEq ι] (e π : ι → B.A) (S : Finset ι) (a : K.O)
    (hB : B.LieReg) (ha : K.Small a) (hF : IsFrame B e π S) (ℓ : B.A → ℝ)
    (hℓ : ∀ x, B.Plus x → B.LinLim a x (ℓ x)) (I : Finset ι) (hI : I ⊆ S) :
    Tendsto (fun k : ℕ => ((HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) atTop
      (𝓝 (∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ (∏ j ∈ J, π j))) ∧
    ∑ᶠ k : B.Cl, (chi B e I k.rep : ℝ) * ℓ k.rep = (Nat.card B.Cl : ℝ) / 2 ^ S.card *
      ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ (∏ j ∈ J, π j) := by
  set h : Finset ι → ℝ := fun I => ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ (∏ j ∈ J, π j) with hh
  have lim1 : ∀ I ⊆ S, Tendsto (fun k : ℕ => ((HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) atTop (𝓝 (h I)) := by
    intro I hI
    have := lim_HH B e π S a hB ha hF ℓ hℓ I hI 1 (plus_one B)
    simp only [one_mul, mul_one] at this
    exact this
  have key : ∀ I ⊆ S, ∀ x, B.Plus x → ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ ((∏ j ∈ J, π j) * x) =
      (chi B e I x : ℝ) * h I := by
    intro I hI x hx
    have t1 := lim_HH B e π S a hB ha hF ℓ hℓ I hI x hx
    have t2 := GlobalTheory.T.tendsto_signedLatticeSum_sub_normCharacter_mul K B ι e π S a hB ha hF I hI x hx
    have t3 := (lim1 I hI).const_mul (chi B e I x : ℝ)
    have t4 := t2.add t3
    rw [zero_add] at t4
    refine tendsto_nhds_unique t1 (t4.congr fun k => ?_)
    push_cast
    ring
  refine ⟨lim1 I hI, ?_⟩
  haveI : Finite B.Cl := GlobalTheory.T.finite_classes_of_separable_charPoly K B hB.2
  exact GlobalTheory.T.normCharacterOnIdempotentPart_orthogonality_classes K B ι e π S hF this ℓ h key I hI

theorem linearDescent : LinearDescent := by
  intro K B₁ B₂ hg₁ hg₂ hsep a ha ℓ ℓ₁ ℓ₂ hℓ hℓ₁ hℓ₂
  have hs₁ : B₁.P.Separable := hsep.of_mul_left
  have hs₂ : B₂.P.Separable := hsep.of_mul_right
  have hP : (B₁.prod B₂).P = B₁.P * B₂.P := by
    have h1 : LinearMap.mulLeft K.E (B₁.prod B₂).g =
        (LinearMap.mulLeft K.E B₁.g).prodMap (LinearMap.mulLeft K.E B₂.g) := by
      exact LinearMap.ext fun _ => rfl
    have h2 := LinearMap.charpoly_prodMap (LinearMap.mulLeft K.E B₁.g) (LinearMap.mulLeft K.E B₂.g)
    rw [← h1] at h2
    exact h2
  obtain ⟨ι₁, _, e₁, π₁, S₁, hF₁⟩ := frame_exists K B₁ hs₁
  obtain ⟨ι₂, _, e₂, π₂, S₂, hF₂⟩ := frame_exists K B₂ hs₂
  have hF := GlobalTheory.T.isUniformizerIdempotentFrame_prod K B₁ B₂ ι₁ ι₂ e₁ π₁ e₂ π₂ S₁ S₂ hF₁ hF₂
  have hL₁ : B₁.LieReg := ⟨hg₁, hs₁⟩
  have hL₂ : B₂.LieReg := ⟨hg₂, hs₂⟩
  have hL : (B₁.prod B₂).LieReg := ⟨by
    show ((B₁.σ B₁.g, B₂.σ B₂.g) : B₁.A × B₂.A) = (B₁.g, B₂.g)
    rw [hg₁, hg₂], hP ▸ hsep⟩
  have hΛ : (S₁.disjSum S₂) \ S₁.map Function.Embedding.inl = S₂.map Function.Embedding.inr := by
    ext x; cases x <;> simp
  have hΛS : S₁.map Function.Embedding.inl ⊆ S₁.disjSum S₂ := by
    intro x; cases x <;> simp
  obtain ⟨l₁, c₁⟩ := sum_formula B₁ e₁ π₁ S₁ a hL₁ ha hF₁ ℓ₁ hℓ₁ S₁ subset_rfl
  obtain ⟨l₂, c₂⟩ := sum_formula B₂ e₂ π₂ S₂ a hL₂ ha hF₂ ℓ₂ hℓ₂ ∅ (Finset.empty_subset _)
  obtain ⟨l, c⟩ := sum_formula (B₁.prod B₂) _ _ _ a hL ha hF ℓ hℓ _ hΛS
  rw [Finset.sdiff_self] at l₁
  rw [Finset.sdiff_empty] at l₂
  rw [hΛ] at l
  change Tendsto (fun k : ℕ => ((HH (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 : ℚ) : ℝ) / ((B₁.prod B₂).rho (algebraMap K.O (B₁.A × B₂.A) a ^ k) : ℝ)) atTop _ at l
  set h₁ := ∑ J ∈ S₁.powerset, (-1 : ℝ) ^ (J ∩ S₁).card * ℓ₁ (∏ j ∈ J, π₁ j)
  set h₂ := ∑ J ∈ S₂.powerset, (-1 : ℝ) ^ (J ∩ ∅).card * ℓ₂ (∏ j ∈ J, π₂ j)
  set h := ∑ J ∈ (S₁.disjSum S₂).powerset, (-1 : ℝ) ^ (J ∩ S₁.map Function.Embedding.inl).card *
    ℓ (∏ j ∈ J, Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)) j)
  have hd := GlobalTheory.T.tendsto_signedLatticeSum_product_sub_factors K B₁ B₂ ι₁ ι₂ e₁ π₁ e₂ π₂ S₁ S₂ a hL₁ hL₂ hsep ha hF₁ hF₂
  set v := val K.O (resultant B₁.P B₂.P)
  have hrho : ∀ k : ℕ, (B₁.prod B₂).rho (algebraMap K.O (B₁.A × B₂.A) a ^ k) =
      B₁.rho (algebraMap K.O B₁.A a ^ k) * B₂.rho (algebraMap K.O B₂.A a ^ k) := fun k =>
    GlobalTheory.T.rho_prod_finiteAlgebraWithInvolution K B₁ B₂ _ _
  have hh : h = (-(K.q : ℝ)) ^ v * (h₁ * h₂) := by
    have t1 := (l₁.mul l₂).const_mul ((-(K.q : ℝ)) ^ v)
    have t2 := hd.add t1
    rw [zero_add] at t2
    refine tendsto_nhds_unique l (t2.congr fun k => ?_)
    rw [hrho k]
    push_cast
    ring
  have e₁' : ∑ᶠ k : B₁.Cl, (K.eta (Algebra.norm K.E k.rep) : ℝ) * ℓ₁ k.rep =
      ∑ᶠ k : B₁.Cl, (chi B₁ e₁ S₁ k.rep : ℝ) * ℓ₁ k.rep := by
    refine finsum_congr fun k => ?_
    rw [((GlobalTheory.T.normCharacterOnIdempotentPart_frame_properties K B₁ ι₁ e₁ π₁ S₁ hF₁).2.2.2 (InvAlg.Cl.rep k) ⟨Units.isUnit _, (Quot.out k).2⟩)]
  have e₂' : ∑ᶠ k : B₂.Cl, ℓ₂ k.rep = ∑ᶠ k : B₂.Cl, (chi B₂ e₂ ∅ k.rep : ℝ) * ℓ₂ k.rep := by
    refine finsum_congr fun k => ?_
    simp [chi, eS, UQ.eta, val]
  have e' : ∑ᶠ k : (B₁.prod B₂).Cl, (K.eta (Algebra.norm K.E (InvAlg.Cl.rep k).1) : ℝ) * ℓ k.rep =
      ∑ᶠ k : (B₁.prod B₂).Cl, (chi (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A))
        (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) k.rep : ℝ) * ℓ k.rep := by
    refine finsum_congr fun k => ?_
    rw [GlobalTheory.T.normCharacterOnIdempotentPart_prod_inl K B₁ B₂ ι₁ ι₂ e₁ e₂ S₁ (InvAlg.Cl.rep k)]
    have hk : (B₁.prod B₂).Plus k.rep := ⟨Units.isUnit _, (Quot.out k).2⟩
    have hk1 : B₁.Plus (InvAlg.Cl.rep k).1 :=
      ⟨(Prod.isUnit_iff.1 hk.1).1, congrArg Prod.fst hk.2⟩
    rw [((GlobalTheory.T.normCharacterOnIdempotentPart_frame_properties K B₁ ι₁ e₁ π₁ S₁ hF₁).2.2.2 (InvAlg.Cl.rep k).1 hk1)]
  rw [e₁', e₂', e', c, c₁, c₂, hh, GlobalTheory.T.card_cl_prod_finiteAlgebraWithInvolution, Finset.card_disjSum]
  push_cast
  ring

end GlobalTheory.UnitLemma.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingOfEtaleExactDeRhamCrystallineConst
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.TheoremAFinal

theorem integralityFromMetric_of_le : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ CA CB CK C : ℝ, 160 ≤ C → ElementDenominator.IntegralityFromMetric D HW F Cm CA CB CK C := by
  intro D HW F Cm CA CB CK C hC
  exact Formalism.MainNotions.N.Ln34.integrality_from_metric_of_large_constant D HW F Cm CA CB CK C hC
    (fun l _ K s LL hG T₀ T₁ T₂ ι π h => GlobalTheory.LatExact.W_exact D HW F l K s LL hG T₀ T₁ T₂ ι π h)
    (GlobalTheory.CrysDdR.finrank_DdRE_of_isCrys D) (GlobalTheory.NL.IotaLetterRank.finrank_iota_letter D HW F Cm)

end GlobalTheory.TheoremAFinal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMulRightUnitaryAdelicMatrixAddHaarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_mul_right_unitaryAdelicMatrix_addHaar : ∀ (D : D7) (V : HSp D) (m : ℕ) (g : GA D V) (μ : Measure (Mx D m V.rank)), μ.IsAddHaarMeasure → μ.map (fun x : Mx D m V.rank => (HMul.hMul (x : Matrix (Fin m) (Fin V.rank) (AE D)) (mt V g) : Mx D m V.rank)) = μ := by
  first | exact @GlobalTheory.AdelicModulus.map_mul_right_unitary | exact GlobalTheory.AdelicModulus.map_mul_right_unitary | (intros; apply GlobalTheory.AdelicModulus.map_mul_right_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyLocalisedFormsTypeSectionHeckeStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_localised_forms_type_section_hecke : ∀ (D : D7) (M : MtFam D) (i : D.nd.Loc), HeckeTied D M → HeckeRational D M → AVTied D M → GlobalTheory.EtaJoin.SplitUnif D → GlobalTheory.EtaJoin.HeckeScalar M i → Nonempty (Sec D i) := by
  first | exact @GlobalTheory.PendOf.SecProof.main | exact GlobalTheory.PendOf.SecProof.main | (intros; apply GlobalTheory.PendOf.SecProof.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedJacquetTwoBlocksFinitelyGeneratedStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedJacquetTwoBlocks_finitelyGenerated : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b n : ℕ) (h : a + b = n) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible → ∃ s : Finset (Jacquet π (unipRad k (two (stdSum h)))), Submodule.span ℂ {w | ∃ g : GL (Fin a) k × GL (Fin b) k, ∃ v ∈ s, w = jac₂ (stdSum h) π g v} = ⊤ := by
  first | exact @GlobalTheory.JacquetFinGen.jacquet_fg | exact GlobalTheory.JacquetFinGen.jacquet_fg | (intros; apply GlobalTheory.JacquetFinGen.jacquet_fg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceIdempotentFiniteAdeleZeroElsewhereStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_idempotent_finite_adele_zero_elsewhere : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ k : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] k) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) k) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → ∀ (P : Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ P' : Pl D.host.E, P' ≠ P → ι (finPart D e) P' = 0 := by
  first | exact @GlobalTheory.ExportSeries.idem_apply_eq_zero_of_ne | exact GlobalTheory.ExportSeries.idem_apply_eq_zero_of_ne | (intros; apply GlobalTheory.ExportSeries.idem_apply_eq_zero_of_ne <;> assumption)
end

