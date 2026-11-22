import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0849
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0851
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ProjectiveOfIsLocallyConstantFinrankFiber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0687
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
import Formalism.PolynomialDimension.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsDescentSymmetricLinearisedBundle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0850
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2ExtensionEtaleCoordinatesFiniteZeros
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDevissageGenerationStep
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomologyOneTwoDualResolution
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FirstBetti

theorem finrank_homology_succ_add (O : Type) [CommRing O] (K : Type) [Field K] [Algebra O K]
    (C : CochainComplex (ModuleCat.{0} O) ℕ) [∀ i, Module.Finite O (C.X i)] (n : ℕ) :
    Module.finrank K ((((ModuleCat.extendScalars (algebraMap O K)).mapHomologicalComplex _).obj
        C).homology (n + 1))
      + Module.finrank K (LinearMap.range ((C.d n (n + 1)).hom.baseChange K))
      + Module.finrank K (LinearMap.range ((C.d (n + 1) (n + 2)).hom.baseChange K))
      = Module.finrank K (K ⊗[O] C.X (n + 1)) := by
  let D := ((ModuleCat.extendScalars (algebraMap O K)).mapHomologicalComplex _).obj C
  have e1 := (D.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).toLinearEquiv
  obtain ⟨e2⟩ := GlobalTheory.Semicont.nonempty_homology_map_extendScalars_equiv K (C.sc' n (n + 1) (n + 2))
  have h := GlobalTheory.Semicont.finrank_homology_add_finrank_range
    ((C.d n (n + 1)).hom.baseChange K) ((C.d (n + 1) (n + 2)).hom.baseChange K)
    (by rw [← LinearMap.baseChange_comp, ← ModuleCat.hom_comp, C.d_comp_d, ModuleCat.hom_zero,
      LinearMap.baseChange_zero])
  rw [(e1.trans e2).finrank_eq]
  exact h

theorem smul_eq_zero_of_algebraMap_eq_zero {O : Type} [CommRing O] {K : Type} [Field K]
    [Algebra O K] {M : Type} [AddCommGroup M] [Module O M] {r : O} (hr : algebraMap O K r = 0)
    (z : K ⊗[O] M) : r • z = 0 := by
  rw [← algebraMap_smul K r z, hr, zero_smul]

theorem baseChange_eq_zero_of_ring {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
    {M : Type} [AddCommGroup M] [Module O M] (e : M →ₗ[O] O)
    (he : ∀ x, algebraMap O K (e x) = 0) : e.baseChange K = 0 := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul k x =>
    rw [LinearMap.baseChange_tmul, LinearMap.zero_apply, ← mul_one (e x), ← smul_eq_mul,
      TensorProduct.tmul_smul, smul_eq_zero_of_algebraMap_eq_zero (he x)]
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.zero_apply, add_zero]

theorem baseChange_eq_zero_of_pi {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
    {M : Type} [AddCommGroup M] [Module O M] {n : ℕ} (e : M →ₗ[O] (Fin n → O))
    (he : ∀ x i, algebraMap O K (e x i) = 0) : e.baseChange K = 0 := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul k x =>
    rw [LinearMap.baseChange_tmul, LinearMap.zero_apply, pi_eq_sum_univ (e x),
      TensorProduct.tmul_sum]
    exact Finset.sum_eq_zero fun i _ => by
      rw [TensorProduct.tmul_smul, smul_eq_zero_of_algebraMap_eq_zero (he x i)]
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.zero_apply, add_zero]

end GlobalTheory.FirstBetti

namespace GlobalTheory

open FirstBetti in

theorem finrank_homology_one_two_of_dual_resolution : ∀ (O : Type) [CommRing O] [IsRegularLocalRing O] (g : ℕ), ringKrullDim O = g → ∀ (f : Fin g → O), Ideal.span (Set.range f) ≠ ⊤ → IsArtinianRing (O ⧸ Ideal.span (Set.range f)) → ∀ (C : CochainComplex (ModuleCat.{0} O) ℕ), (∀ i, Module.Free O (C.X i) ∧ Module.Finite O (C.X i)) → (∀ i, Function.Exact (C.d (i + 1) (i + 2)).hom.dualMap (C.d i (i + 1)).hom.dualMap) → Nonempty ((Module.Dual O (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[O] (O ⧸ Ideal.span (Set.range f))) → ∀ (K : Type) [Field K] (φ : O →+* K), RingHom.ker φ = IsLocalRing.maximalIdeal O → Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 1) = g ∧ Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 2) ≤ g.choose 2 := by
  intro O _ _ g hdim f hne hart C hC hex hN K _ φ hker
  obtain ⟨eN⟩ := hN
  letI := φ.toAlgebra
  haveI : ∀ i, Module.Free O (C.X i) := fun i => (hC i).1
  haveI : ∀ i, Module.Finite O (C.X i) := fun i => (hC i).2
  have hIm : Ideal.span (Set.range f) ≤ IsLocalRing.maximalIdeal O := IsLocalRing.le_maximalIdeal hne
  have hIφ : ∀ x ∈ Ideal.span (Set.range f), algebraMap O K x = 0 := fun x hx => by
    have : x ∈ RingHom.ker φ := hker ▸ hIm hx
    exact this

  have hreg : RingTheory.Sequence.IsRegular O (List.ofFn f) := by
    refine GlobalTheory.isRegular_ofFn_of_ringKrullDim_quotient_add_le O g g f hdim
      (fun i => hIm (Ideal.subset_span ⟨i, rfl⟩)) ?_
    have h0 : ringKrullDim (O ⧸ Ideal.span (Set.range f)) ≤ 0 := Ring.krullDimLE_iff.1 inferInstance
    calc ringKrullDim (O ⧸ Ideal.span (Set.range f)) + (g : WithBot ℕ∞) ≤ 0 + (g : WithBot ℕ∞) :=
          add_le_add_left h0 _
      _ = g := zero_add _
  obtain ⟨e₁, e₂, hx1, hx2, he1, he2⟩ := GlobalTheory.T.koszul_resolution_three_terms_exact O g f hreg.toIsWeaklyRegular

  let ε : Module.Dual O (C.X 0) →ₗ[O] O ⧸ Ideal.span (Set.range f) :=
    eN.toLinearMap ∘ₗ (LinearMap.range (C.d 0 1).hom.dualMap).mkQ
  have hεs : Function.Surjective ε := eN.surjective.comp (Submodule.mkQ_surjective _)
  have hεx : Function.Exact (C.d 0 1).hom.dualMap ε := by
    rw [LinearMap.exact_iff, LinearEquiv.ker_comp, Submodule.ker_mkQ]
  obtain ⟨hA, hB⟩ := GlobalTheory.T.finrank_homology_resolutions_residueField O K (O ⧸ Ideal.span (Set.range f))
    (Module.Dual O (C.X 0)) (Module.Dual O (C.X 1)) (Module.Dual O (C.X 2)) (Module.Dual O (C.X 3))
    O (Fin g → O) (Fin (g.choose 2) → O) ε (C.d 0 1).hom.dualMap (C.d 1 2).hom.dualMap
    (C.d 2 3).hom.dualMap (Ideal.span (Set.range f)).mkQ e₁ e₂ hεs hεx (hex 0) (hex 1)
    (Submodule.mkQ_surjective _) hx1 hx2

  have hz1 : e₁.baseChange K = 0 := baseChange_eq_zero_of_ring e₁ fun x => hIφ _ (he1 x)
  have hz2 : e₂.baseChange K = 0 := baseChange_eq_zero_of_pi e₂ fun x i => hIφ _ (he2 x i)
  have hk1 : Module.finrank K (LinearMap.ker (e₁.baseChange K)) = g := by
    rw [hz1, LinearMap.ker_zero, finrank_top, GlobalTheory.Semicont.finrank_baseChange_fin]
  have hr2 : Module.finrank K (LinearMap.range (e₂.baseChange K)) = 0 := by
    rw [hz2, LinearMap.range_zero, finrank_bot]
  have hc2 : Module.finrank K (K ⊗[O] (Fin (g.choose 2) → O)) = g.choose 2 :=
    GlobalTheory.Semicont.finrank_baseChange_fin _ _

  obtain ⟨r0, n0⟩ := GlobalTheory.T.finrank_range_baseChange_eq_finrank_range_dualMap O K (C.X 0) (C.X 1) (C.d 0 1).hom
  obtain ⟨r1, n1⟩ := GlobalTheory.T.finrank_range_baseChange_eq_finrank_range_dualMap O K (C.X 1) (C.X 2) (C.d 1 2).hom
  obtain ⟨r2, n2⟩ := GlobalTheory.T.finrank_range_baseChange_eq_finrank_range_dualMap O K (C.X 2) (C.X 3) (C.d 2 3).hom
  have k1 := LinearMap.finrank_range_add_finrank_ker ((C.d 0 1).hom.dualMap.baseChange K)
  have k2 := LinearMap.finrank_range_add_finrank_ker ((C.d 1 2).hom.dualMap.baseChange K)

  have h1 : Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 1)
      + Module.finrank K (LinearMap.range ((C.d 0 1).hom.baseChange K))
      + Module.finrank K (LinearMap.range ((C.d 1 2).hom.baseChange K))
      = Module.finrank K (K ⊗[O] C.X 1) := finrank_homology_succ_add O K C 0
  have h2 : Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 2)
      + Module.finrank K (LinearMap.range ((C.d 1 2).hom.baseChange K))
      + Module.finrank K (LinearMap.range ((C.d 2 3).hom.baseChange K))
      = Module.finrank K (K ⊗[O] C.X 2) := finrank_homology_succ_add O K C 1
  constructor <;> omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPairingLastRowMonomialReadsCoefficient
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

noncomputable section

namespace GlobalTheory.BrCoefFock

variable {K : Type} [Field K] {n : ℕ}

def spl (K : Type) [Field K] (n : ℕ) : BP K n →+* MvPolynomial (Unit × Fin n) (MvPolynomial (Fin n × Fin n) K) :=
  (map (rename (Prod.snd : Unit × Fin n × Fin n → Fin n × Fin n) :
      MvPolynomial (Unit × Fin n × Fin n) K →ₐ[K] MvPolynomial (Fin n × Fin n) K).toRingHom).comp
    ((GlobalTheory.BranchFormula.splitLast K Unit (rfl : n + 1 = n + 1)).toRingHom.comp
      ((rename (fun v : Fin (n + 1) × Fin (n + 1) => (((), v) : Unit × Fin (n + 1) × Fin (n + 1))) :
        _ →ₐ[K] _).toRingHom.comp (incl K n).toRingHom))

theorem coefOne_eq (b : Fin n → ℕ) (x : BP K n) :
    coefOne K n b (incl K n x) = coeff (GlobalTheory.BranchFormula.expOf fun _ : Unit => b) (spl K n x) := by
  unfold coefOne
  rw [GlobalTheory.BranchFormula.coefLast_eq_coeff]
  simp [spl, coeff_map]

theorem spl_C (a : K) : spl K n (C a) = C (C a) := by
  simp [spl, incl, GlobalTheory.BranchFormula.splitLast]

theorem spl_up (a s : Fin n) : spl K n (X (a.castSucc, s)) = C (X (a, s)) := by
  simp [spl, incl, GlobalTheory.BranchFormula.splitLast]

theorem spl_last (s : Fin n) : spl K n (X (Fin.last n, s)) = X ((), s) := by
  simp [spl, incl, GlobalTheory.BranchFormula.splitLast]

def lastV (n : ℕ) (p : Unit × Fin n) : Fin (n + 1) × Fin n := (Fin.last n, p.2)

theorem lastV_inj : Function.Injective (lastV n) := fun _ _ h =>
  Prod.ext rfl (Prod.ext_iff.1 h).2

theorem pderiv_rename_of_ne {σ τ : Type} (e : σ → τ) (v : τ) (h : ∀ u, e u ≠ v) (f : MvPolynomial σ K) :
    pderiv v (rename e f) = 0 := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p u hp => simp [hp, pderiv_X_of_ne (h u)]

theorem fockB_C_left {σ : Type} (a : K) (g : MvPolynomial σ K) : fockB (C a) g = a * constantCoeff g :=
  @fockL_C_left K _ starRingOfComm _ a g

theorem emb_inj : Function.Injective (fun v : Fin n × Fin n => ((v.1.castSucc, v.2) : Fin (n + 1) × Fin n)) :=
  (Fin.castSucc_injective n).prodMap Function.injective_id

theorem key (x : BP K n) (β : Unit × Fin n →₀ ℕ) (p : MvPolynomial (Fin n × Fin n) K) :
    fockB x (rename (lastV n) (monomial β (1 : K)) * emb K n p) =
      ((∏ u, (β u).factorial : ℕ) : K) * fockB (coeff β (spl K n x)) p := by
  classical
  induction x using MvPolynomial.induction_on generalizing β p with
  | C a =>
    rw [fockB_C_left, spl_C, coeff_C, map_mul, constantCoeff_rename, constantCoeff_monomial, emb, constantCoeff_rename]
    by_cases h : β = 0
    · subst h; simp [fockB_C_left]
    · rw [if_neg h, if_neg (Ne.symm h), ← fockBL_apply]; simp
  | add f g hf hg =>
    simp only [← fockBL_apply, map_add, LinearMap.add_apply, coeff_add] at *
    rw [hf, hg, mul_add]
  | mul_X f v hf =>
    obtain ⟨a, s⟩ := v
    rw [mul_comm f, fockB_X_mul, map_mul (spl K n), Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    induction a using Fin.lastCases with
    | cast a =>
      rw [pderiv_rename_of_ne (lastV n) (a.castSucc, s) (fun u h => (Fin.castSucc_lt_last a).ne' (Prod.ext_iff.1 h).1),
        mul_zero, add_zero, spl_up, coeff_C_mul, fockB_X_mul, ← hf]
      congr 2
      exact pderiv_rename emb_inj (a, s) p
    | last =>
      have h1 : pderiv (Fin.last n, s) (emb K n p) = 0 :=
        pderiv_rename_of_ne _ _ (fun u h => (Fin.castSucc_lt_last u.1).ne (congrArg Prod.fst h)) p
      have h2 : pderiv (Fin.last n, s) (rename (lastV n) (monomial β (1 : K))) =
          (β ((), s) : K) • rename (lastV n) (monomial (β - Finsupp.single ((), s) 1) (1 : K)) := by
        have := pderiv_rename (R := K) lastV_inj ((), s) (monomial β (1 : K))
        rw [pderiv_monomial] at this
        rw [← map_smul, smul_monomial, smul_eq_mul, mul_comm]
        exact this
      rw [h1, mul_zero, zero_add, h2, mul_comm, smul_mul_assoc, ← fockBL_apply, map_smul, fockBL_apply, hf,
        spl_last, coeff_X_mul', smul_eq_mul]
      split_ifs with h
      · rw [← mul_assoc, ← Nat.cast_mul]
        congr 2
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ((), s)),
          ← Finset.mul_prod_erase _ (fun u => (β u).factorial) (Finset.mem_univ ((), s)), ← mul_assoc]
        congr 1
        · simpa using Nat.mul_factorial_pred (Finsupp.mem_support_iff.1 h)
        · refine Finset.prod_congr rfl fun u hu => ?_
          simp [Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hu)]
      · rw [Finsupp.notMem_support_iff.1 h, ← fockBL_apply (0 : MvPolynomial (Fin n × Fin n) K)]
        simp

theorem zmon_eq (b : Fin n → ℕ) :
    zmon K n b = rename (lastV n) (monomial (GlobalTheory.BranchFormula.expOf fun _ : Unit => b) (1 : K)) := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), map_prod, Fintype.prod_prod_type]
  simp [zmon, lastV]

theorem spl_zmon (b : Fin n → ℕ) :
    spl K n (zmon K n b) = monomial (GlobalTheory.BranchFormula.expOf fun _ : Unit => b) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]
  simp [zmon, spl_last]

theorem spl_emb (q : MvPolynomial (Fin n × Fin n) K) : spl K n (emb K n q) = C q := by
  induction q using MvPolynomial.induction_on with
  | C a => rw [emb, rename_C, spl_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => rw [map_mul, map_mul, hp, bmF_emb_X, spl_up, map_mul]

theorem fockB_zmon_emb : ∀ (K : Type) [Field K] (n : ℕ) (b : Fin n → ℕ), (∀ (x : BP K n) (p : MvPolynomial (Fin n × Fin n) K), fockB x (zmon K n b * emb K n p) = (bfact b : K) * fockB (coefOne K n b (incl K n x)) p) ∧ ∀ p q : MvPolynomial (Fin n × Fin n) K, fockB (zmon K n b * emb K n q) (zmon K n b * emb K n p) = (bfact b : K) * fockB q p := by
  intro K _ n b
  have h1 : ∀ (x : BP K n) (p : MvPolynomial (Fin n × Fin n) K), fockB x (zmon K n b * emb K n p) =
      (bfact b : K) * fockB (coefOne K n b (incl K n x)) p := by
    intro x p
    rw [zmon_eq, key, coefOne_eq, Fintype.prod_prod_type]
    simp [bfact]
  refine ⟨h1, fun p q => ?_⟩
  rw [h1, coefOne_eq, map_mul, spl_zmon, spl_emb, mul_comm (monomial _ _), coeff_C_mul]
  simp

end GlobalTheory.BrCoefFock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOrbitProjectorEigen
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory

theorem freeOrbit_projector_eigen : ∀ (K V G C : Type) [Field K] [AddCommGroup V] [Module K V] [Group G] [Fintype G] [Fintype C] [MulAction G C] (e : C → V →ₗ[K] V) (ρ : Representation K G V) (χ : G →* Kˣ), (∀ (g : G) (Z : C), g • Z = Z → g = 1) → (∀ Z v, e Z (e Z v) = e Z v) → (∀ Z Z' v, Z ≠ Z' → e Z (e Z' v) = 0) → (∀ v, ∑ Z, e Z v = v) → (∀ g Z v, ρ g (e Z v) = e (g • Z) (ρ g v)) → ∃ O : Finset C, (∀ Z, ∃ g : G, ∃ o ∈ O, Z = g • o) ∧ (∀ F, (∀ g, ρ g F = (χ g : K) • F) → F = ∑ o ∈ O, ∑ g, ((χ g)⁻¹ : Kˣ) • ρ g (e o F)) ∧ ∀ f : C → V, (∀ o, e o (f o) = f o) → (∀ h, ρ h (∑ o ∈ O, ∑ g, ((χ g)⁻¹ : Kˣ) • ρ g (f o)) = (χ h : K) • ∑ o ∈ O, ∑ g, ((χ g)⁻¹ : Kˣ) • ρ g (f o)) ∧ ∀ g, ∀ o ∈ O, e (g • o) (∑ o' ∈ O, ∑ g', ((χ g')⁻¹ : Kˣ) • ρ g' (f o')) = ((χ g)⁻¹ : Kˣ) • ρ g (f o) := by
  intro K V G C _ _ _ _ _ _ _ e ρ χ hfree hidem horth hsum1 hequi
  classical
  let O : Finset C := Finset.univ.image (fun Z : C => (Quotient.mk (MulAction.orbitRel G C) Z).out)
  have hq : ∀ (g : G) (x : C), Quotient.mk (MulAction.orbitRel G C) (g • x) = Quotient.mk (MulAction.orbitRel G C) x :=
    fun g x => Quotient.sound (MulAction.mem_orbit x g)
  have hinj : ∀ (g : G) (o : C) (g' : G) (o' : C), o ∈ O → o' ∈ O → g • o = g' • o' → g = g' ∧ o = o' := by
    intro g o g' o' ho ho' h
    obtain ⟨Z1, -, rfl⟩ := Finset.mem_image.1 ho
    obtain ⟨Z2, -, rfl⟩ := Finset.mem_image.1 ho'
    have hZ : Quotient.mk (MulAction.orbitRel G C) Z1 = Quotient.mk (MulAction.orbitRel G C) Z2 := by
      calc Quotient.mk (MulAction.orbitRel G C) Z1
          = Quotient.mk (MulAction.orbitRel G C) (Quotient.mk (MulAction.orbitRel G C) Z1).out := (Quotient.out_eq _).symm
        _ = Quotient.mk (MulAction.orbitRel G C) (g • (Quotient.mk (MulAction.orbitRel G C) Z1).out) := (hq g _).symm
        _ = Quotient.mk (MulAction.orbitRel G C) (g' • (Quotient.mk (MulAction.orbitRel G C) Z2).out) := by rw [h]
        _ = Quotient.mk (MulAction.orbitRel G C) (Quotient.mk (MulAction.orbitRel G C) Z2).out := hq g' _
        _ = Quotient.mk (MulAction.orbitRel G C) Z2 := Quotient.out_eq _
    rw [hZ] at h ⊢
    refine ⟨?_, rfl⟩
    have h2 : (g'⁻¹ * g) • (Quotient.mk (MulAction.orbitRel G C) Z2).out = (Quotient.mk (MulAction.orbitRel G C) Z2).out := by
      rw [mul_smul, h, inv_smul_smul]
    have := hfree _ _ h2
    rw [inv_mul_eq_one] at this
    exact this.symm
  have hsurj : ∀ Z, ∃ g : G, ∃ o ∈ O, Z = g • o := by
    intro Z
    have hm : (Quotient.mk (MulAction.orbitRel G C) Z).out ∈ MulAction.orbit G Z := @Quotient.mk_out _ (MulAction.orbitRel G C) Z
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 hm
    exact ⟨g⁻¹, _, Finset.mem_image_of_mem _ (Finset.mem_univ Z), by rw [← hg, inv_smul_smul]⟩
  have hsum : ∀ φ : C → V, ∑ Z, φ Z = ∑ o ∈ O, ∑ g : G, φ (g • o) := by
    intro φ
    rw [← Finset.sum_product (s := O) (t := Finset.univ) (f := fun x : C × G => φ (x.2 • x.1))]
    symm
    refine Finset.sum_bij (fun x _ => x.2 • x.1) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
    · rintro ⟨o, g⟩ h ⟨o', g'⟩ h' he
      simp only [Finset.mem_product] at h h'
      obtain ⟨h1, h2⟩ := hinj g o g' o' h.1 h'.1 he
      simp [h1, h2]
    · intro Z _
      obtain ⟨g, o, ho, rfl⟩ := hsurj Z
      exact ⟨(o, g), Finset.mem_product.2 ⟨ho, Finset.mem_univ _⟩, rfl⟩
  refine ⟨O, hsurj, ?_, ?_⟩
  · intro F hF
    conv_lhs => rw [← hsum1 F, hsum (fun Z => e Z F)]
    refine Finset.sum_congr rfl (fun o _ => Finset.sum_congr rfl (fun g _ => ?_))
    rw [hequi, hF, LinearMap.map_smul, ← Units.smul_def, inv_smul_smul]
  · intro f hf
    refine ⟨?_, ?_⟩
    · intro h
      simp only [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun o _ => ?_)
      refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => ?_)
      simp only [Equiv.coe_mulLeft]
      rw [Units.smul_def, Units.smul_def, LinearMap.map_smul, map_mul, map_mul, Module.End.mul_apply, smul_smul]
      congr 1
      rw [← Units.val_mul]
      congr 1
      rw [mul_inv_rev, mul_comm, mul_assoc, inv_mul_cancel, mul_one]
    · intro g o ho
      have key : ∀ o' ∈ O, ∀ g', e (g • o) (((χ g')⁻¹ : Kˣ) • ρ g' (f o')) =
          if g' = g ∧ o' = o then ((χ g)⁻¹ : Kˣ) • ρ g (f o) else 0 := by
        intro o' ho' g'
        have hw : ρ g' (f o') = e (g' • o') (ρ g' (f o')) := by rw [← hequi g' o' (f o'), hf o']
        split_ifs with hc
        · obtain ⟨rfl, rfl⟩ := hc
          rw [Units.smul_def, LinearMap.map_smul]
          congr 1
          rw [hw, hidem]
        · rw [Units.smul_def, LinearMap.map_smul, hw, horth, smul_zero]
          intro hZ
          obtain ⟨h1, h2⟩ := hinj g o g' o' ho ho' hZ
          exact hc ⟨h1.symm, h2.symm⟩
      rw [map_sum, Finset.sum_eq_single_of_mem o ho]
      · rw [map_sum, Fintype.sum_eq_single g]
        · rw [key o ho g, if_pos ⟨rfl, rfl⟩]
        · intro g' hg'
          rw [key o ho g', if_neg (fun h => hg' h.1)]
      · intro o' ho' hne
        rw [map_sum]
        refine Finset.sum_eq_zero (fun g' _ => ?_)
        rw [key o' ho' g', if_neg (fun h => hne h.2)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpSchemeMonHomSquareLiftOneRight
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke.PullInj

variable {X Y Z : Scheme.{0}}

theorem gen_germ {L : LB X} {w : LB.Gen L} (hw : w.IsGen) (r : Z ⟶ X) (z : Z) {k l : L.ι}
    (hk : r z ∈ L.U k) (hl : r z ∈ L.U l) :
    gm r z _ (w.s k) = gm r z (L.U k ⊓ L.U l) (L.g k l) * gm r z _ (w.s l) := by
  have hm : r z ∈ L.U k ⊓ L.U l := ⟨hk, hl⟩
  exact (gm_res r z inf_le_left hm _).symm.trans ((congrArg (gm r z _) (hw k l)).trans
    ((map_mul _ _ _).trans (congrArg _ (gm_res r z inf_le_right hm _))))

theorem gm_pull_g (Q : LB Y) (F : X ⟶ Y) (r : Z ⟶ X) (z : Z) {j j' : PUnit → Q.ι}
    (hj : F (r z) ∈ Q.U (j PUnit.unit)) (hj' : F (r z) ∈ Q.U (j' PUnit.unit)) :
    gm r z ((Q.pull F).U j ⊓ (Q.pull F).U j') ((Q.pull F).g j j') =
      gm (r ≫ F) z (Q.U (j PUnit.unit) ⊓ Q.U (j' PUnit.unit)) (Q.g (j PUnit.unit) (j' PUnit.unit)) := by
  have hp : r z ∈ (Q.pull F).U j ⊓ (Q.pull F).U j' := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm r z _ (∏ _k : PUnit, (res _ (pullU F _ (Q.g _ _))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res r z _ hp _).trans (gm_pull r F z (Q.U (j PUnit.unit) ⊓ Q.U (j' PUnit.unit)) ⟨hj, hj'⟩ _)

theorem germ_div_g (M L : LB X) (r : Z ⟶ X) (z : Z) {p q : M.ι × L.ι}
    (hp : r z ∈ (LB.div M L).U p) (hq : r z ∈ (LB.div M L).U q) :
    gm r z _ ((LB.div M L).g p q) =
      gm r z (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) * (gm r z (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹ := by
  have hm : r z ∈ (LB.div M L).U p ⊓ (LB.div M L).U q := ⟨hp, hq⟩
  show gm r z _ (res _ (M.g _ _) * (res _ (L.g _ _))⁻¹) = _
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hm _) ((map_inv _ _).trans (congrArg _ (gm_res r z _ hm _))))

theorem mem_divPull {Q₁ Q₂ : LB Y} {F : X ⟶ Y} {x : X} {k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)} :
    x ∈ (LB.div (Q₂.pull F) (Q₁.pull F)).U k ↔ F x ∈ Q₂.U (k.1 PUnit.unit) ∧ F x ∈ Q₁.U (k.2 PUnit.unit) :=
  ⟨fun h => ⟨mem_pull.1 h.1, mem_pull.1 h.2⟩, fun h => ⟨mem_pull.2 h.1, mem_pull.2 h.2⟩⟩

theorem gm_top_eq {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (g : Γ(A.left, ⊤)ˣ)
    (r r' : Z ⟶ A.left) (e : r ≫ A.hom = r' ≫ A.hom) (z : Z) : gm r z ⊤ g = gm r' z ⊤ g := by
  obtain ⟨c, hc⟩ := (GlobalTheory.globalFns_holds S A hA).2 g.val
  have h1 : ∀ r₀ : Z ⟶ A.left, gs r₀ z ⊤ g.val = gs (r₀ ≫ A.hom) z ⊤ c := fun r₀ => by
    rw [← hc]; exact gs_pull r₀ A.hom z ⊤ trivial c
  apply Units.ext
  rw [← gs_unit r z ⊤ trivial, ← gs_unit r' z ⊤ trivial, h1, h1, e]

end GlobalTheory.UPel.HT.Hecke.PullInj

namespace GlobalTheory.UPel.HT.Hecke.PullInj

variable {S : Scheme.{0}}

theorem transl_axis₁ (A : Over S) [GrpObj A] [IsCommMonObj A] (h : 𝟙_ (Over S) ⟶ A) :
    lift (1 : A ⟶ A) (𝟙 A) ≫ transl (lift (1 : 𝟙_ (Over S) ⟶ A) h : 𝟙_ (Over S) ⟶ G2 A) =
      transl h ≫ lift (1 : A ⟶ A) (𝟙 A) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [transl, MonObj.mul_comp, MonObj.comp_mul]
  · simp [transl, MonObj.mul_comp, MonObj.comp_mul]

theorem transl_axis₂ (A : Over S) [GrpObj A] [IsCommMonObj A] (h : 𝟙_ (Over S) ⟶ A) :
    lift (𝟙 A) (1 : A ⟶ A) ≫ transl (lift h (1 : 𝟙_ (Over S) ⟶ A) : 𝟙_ (Over S) ⟶ G2 A) =
      transl h ≫ lift (𝟙 A) (1 : A ⟶ A) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [transl, MonObj.mul_comp, MonObj.comp_mul]
  · simp [transl, MonObj.mul_comp, MonObj.comp_mul]

theorem grpScheme_monHom_square_lift_one_left {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A')
    [IsMonHom ψ] : lift (1 : A ⟶ A) (𝟙 A) ≫ lift (fst A A ≫ ψ) (snd A A ≫ ψ) = ψ ≫ lift (1 : A' ⟶ A') (𝟙 A') := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp

theorem grpScheme_monHom_square_lift_one_right {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A')
    [IsMonHom ψ] : lift (𝟙 A) (1 : A ⟶ A) ≫ lift (fst A A ≫ ψ) (snd A A ≫ ψ) = ψ ≫ lift (𝟙 A') (1 : A' ⟶ A') := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp

end GlobalTheory.UPel.HT.Hecke.PullInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGramFrameEmbeddingMatrixNormOfVector
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.DefPt

theorem isGram_matNorm : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] [DecidableEq ι] (Y : (K →+* ℂ) → Matrix ι ι ℂ), (∀ σ, (Y σ).det ≠ 0) → IsGram (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) (matNorm Y) ∧ HasGram (matNorm Y) := by
  intro K _ _ ι _ _ Y hY
  have h : IsGram (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) (matNorm Y) := by
    intro v
    have hu : IsUnit (Y v.embedding).det := (hY _).isUnit
    refine ⟨Matrix.isUnit_nonsing_inv_det _ hu, fun x => ?_⟩
    have hv : Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K ι) v x = fun j => v.embedding (x j) := by
      funext j
      simp [Formalism.HermitianLatticesTheory.vecAt]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord, matNorm, Matrix.nonsing_inv_nonsing_inv _ hu, hv]
  exact ⟨h, h.hasGram⟩

end GlobalTheory.DefPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularOnOpenUniformisedOfLocallyStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegularOnOpenUniformised_of_locally : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (k : (Fin g → ℂ) → ℂ), (∀ z ∈ pre u.ex U, ∃ W : A.left.Opens, W ≤ U ∧ z ∈ pre u.ex W ∧ IsReg u.ex W k) → IsReg u.ex U k := by
  first | exact @GlobalTheory.CechPer.isReg_of_locally | exact GlobalTheory.CechPer.isReg_of_locally | (intros; apply GlobalTheory.CechPer.isReg_of_locally <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTestHomMatrixOfProportionalGeneratingCombinatiStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTestHomMatrix_of_proportional_generating_combinations : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c → GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom (Φ'.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B) c → GlobalTheory.HomFixUniv.Normal t c αA βB → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c := by
  first | (exact @GlobalTheory.HomFixCond.isMat_of_conditions) | (exact GlobalTheory.HomFixCond.isMat_of_conditions) | (intros; apply GlobalTheory.HomFixCond.isMat_of_conditions  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2ExtensionEtaleCoordinatesFiniteZerosStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.l2_extension_etale_coordinates_finite_zeros : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), 1 ≤ n → ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ hS : (A.zeroSet s).Finite, (∀ P ∈ A.zeroSet s, jacAt A s P ≠ 0) → (∀ y, A.sqn L s y ≤ 1) → ∀ δ : ℝ, 0 < δ → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), ∀ i y, y ∈ (A.chart i).source → y ∉ A.zeroSet s → ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i (fun x => A.ph E i x + α * psi A L s x) y ξ) → ∀ (Λ : La) (τ : ι → Y → ℂ) (z : Y → V n) (β : ι → Y → ℂ), (A.IsSec Λ τ ∧ A.Pos Λ (fun _ => 0) ∧ Etale A (nz A τ) z ∧ A.IsFrameOn (A.kap + E) (nz A τ) β ∧ Dense (nz A τ) ∧ ∃ C : ℝ, 0 < C ∧ ∀ y, A.nsq Λ τ y ≤ C * A.sqn L s y) → ∀ f : Y → ℂ, ∃ F : ι → Y → ℂ, A.IsSec (A.kap + E) F ∧ (∀ P ∈ A.zeroSet s, F (A.pick P) P = f P) ∧ ∫⁻ y, ENNReal.ofReal (2 ^ n * (1 / (1 + (δ * psi A L s y) ^ 2) * A.nsq (A.kap + E) F y * Real.exp (-psi A L s y))) ∂A.mu ≤ ENNReal.ofReal (34 / δ * (resConst n * ∑ P ∈ hS.toFinset, resSq A E L s P (f P))) := by
  first | exact @GlobalTheory.l2_extension_of_etale_coordinates | exact GlobalTheory.l2_extension_of_etale_coordinates | (intros; apply GlobalTheory.l2_extension_of_etale_coordinates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDevissageGenerationStepStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_devissage_generation_step : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (C : Type) [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ Θ : Q →+* C, (∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b)) → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q), (∀ i, QL μ ⊤ (e i)) → IsBasis (fun i => map θ (μ i)) (fun i => map Θ (e i)) → ∀ N' N : Ideal B, IsStep p θ N' N → ∀ f, QL μ N f → ∃ (b : ι → B) (s : MvPowerSeries (Fin d) Q), (∀ i, b i ∈ N) ∧ In N s ∧ QL μ N' (f - comb b e - s) := by
  first | exact @GlobalTheory.QLog.StepGen.step_generation | exact GlobalTheory.QLog.StepGen.step_generation | (intros; apply GlobalTheory.QLog.StepGen.step_generation <;> assumption)
end

