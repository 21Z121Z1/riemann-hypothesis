import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0328
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0337
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0329
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0330
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryModIffForallTraceFormCoboundary
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

open Submodule in

theorem cobO_iff_forall_lam : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL] (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
    (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) →
    (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) →
    (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) →
    ∀ (L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL))),
    L1.T = LinearMap.range (Algebra.linearMap O LL) →
    ∀ (L1Z : Lattice (O := ℤ_[l]) (charRep (cycLL (P.PD K) ℚ_[l]))),
    L1Z.T = LinearMap.range (Algebra.linearMap ℤ_[l] ℚ_[l]) →
    ∀ (z : ↥(GK K) × ↥(GK K) → LL),
    (CobO (P.PD K) L1 z ↔ ∀ o : O, CobO (P.PD K) L1Z (fun x => lam (algebraMap O LL o * z x))) := by
  intro l _ P K LL _ _ O _ _ lam n e f h1 h2 h3 L1 hL1 L1Z hL1Z z
  classical
  have memT : ∀ x : LL, x ∈ L1.T ↔ ∃ o : O, algebraMap O LL o = x := by
    intro x; rw [hL1]; simp [LinearMap.mem_range]
  have memZ : ∀ q : ℚ_[l], q ∈ L1Z.T ↔ ∃ w : ℤ_[l], (w : ℚ_[l]) = q := by
    intro q; rw [hL1Z]; simp [LinearMap.mem_range]
  have actT : ∀ g (a : LL), (repD L1 g) (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (algebraMap ℚ_[l] LL ((P.PD K).χ g : ℚ_[l]) * a) := by
    intro g a
    simp [repD, Submodule.mapQ_apply, charRep, cycLL, Algebra.smul_def]
  have actZ : ∀ g (q : ℚ_[l]), (repD L1Z g) (Submodule.Quotient.mk q) =
      Submodule.Quotient.mk (((P.PD K).χ g : ℚ_[l]) * q) := by
    intro g q
    simp [repD, Submodule.mapQ_apply, charRep, cycLL]
  have lamc : ∀ (o : O) (c : ℚ_[l]) (y : LL),
      lam (algebraMap O LL o * (algebraMap ℚ_[l] LL c * y)) = c * lam (algebraMap O LL o * y) := by
    intro o c y
    have : algebraMap O LL o * (algebraMap ℚ_[l] LL c * y) = c • (algebraMap O LL o * y) := by
      rw [Algebra.smul_def]; ring
    rw [this, map_smul, smul_eq_mul]
  unfold CobO ReciprocityTheory.Def.B2
  constructor
  · intro H o
    obtain ⟨F, ⟨hFc, -⟩, hF⟩ := Submodule.mem_map.1 H
    choose Ft hFt using fun g => Submodule.Quotient.mk_surjective L1.T (F g)
    have hFeq : F = fun g => Submodule.Quotient.mk (Ft g) := funext fun g => (hFt g).symm
    subst hFeq
    let φ : LL ⧸ L1.T → ℚ_[l] ⧸ L1Z.T := fun q =>
      Submodule.Quotient.mk (lam (algebraMap O LL o * (Submodule.Quotient.mk_surjective L1.T q).choose))
    have hφ : ∀ a, φ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (lam (algebraMap O LL o * a)) := by
      intro a
      have hc := (Submodule.Quotient.mk_surjective L1.T (Submodule.Quotient.mk a)).choose_spec
      rw [Submodule.Quotient.eq] at hc
      obtain ⟨o', ho'⟩ := (memT _).1 hc
      obtain ⟨w, hw⟩ := h2 (o * o')
      show Submodule.Quotient.mk _ = _
      rw [Submodule.Quotient.eq, memZ]
      exact ⟨w, by rw [← hw, map_mul, ho', mul_sub, map_sub]⟩
    refine Submodule.mem_map.2 ⟨φ ∘ (fun g => Submodule.Quotient.mk (Ft g)), ⟨hFc.comp φ, fun _ => trivial⟩, ?_⟩
    funext x
    have hx := congrFun hF x
    simp only [ReciprocityTheory.Def.d1, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply] at hx ⊢
    rw [actT, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq] at hx
    obtain ⟨o', ho'⟩ := (memT _).1 hx
    obtain ⟨w, hw⟩ := h2 (o * o')
    rw [hφ, hφ, hφ, actZ, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, memZ]
    refine ⟨w, ?_⟩
    rw [← hw, map_mul, ho', mul_sub, mul_add, mul_sub, map_sub, map_add, map_sub, lamc]
  · intro H
    choose Fz hFzc hFz using fun i => Submodule.mem_map.1 (H (f i))
    choose Ft hFt using fun i g => Submodule.Quotient.mk_surjective L1Z.T (Fz i g)
    refine Submodule.mem_map.2 ⟨fun g => Submodule.Quotient.mk
      (∑ i, algebraMap ℚ_[l] LL (Ft i g) * algebraMap O LL (e i)), ⟨?_, fun _ => trivial⟩, ?_⟩
    · rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      have hev : ∀ᶠ y in nhds x, ∀ i, Fz i y = Fz i x :=
        Filter.eventually_all.2 fun i => (IsLocallyConstant.iff_eventually_eq _).1 (hFzc i).1 x
      filter_upwards [hev] with y hy
      rw [Submodule.Quotient.eq, ← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hyi := hy i
      rw [← hFt i y, ← hFt i x, Submodule.Quotient.eq, memZ] at hyi
      obtain ⟨w, hw⟩ := hyi
      obtain ⟨o, ho⟩ := h1 w
      rw [memT]
      exact ⟨o * e i, by rw [map_mul, ho, hw, ← sub_mul, map_sub]⟩
    · funext x
      have key : ∀ i, ∃ w : ℤ_[l], (w : ℚ_[l]) = ((P.PD K).χ x.1 : ℚ_[l]) * Ft i x.2 - Ft i (x.1 * x.2)
          + Ft i x.1 - lam (algebraMap O LL (f i) * z x) := by
        intro i
        have hx := congrFun (hFz i) x
        simp only [ReciprocityTheory.Def.d1, LinearMap.coe_mk, AddHom.coe_mk] at hx
        rw [← hFt i x.2, ← hFt i (x.1 * x.2), ← hFt i x.1, actZ, ← Submodule.Quotient.mk_sub,
          ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, memZ] at hx
        exact hx
      choose w hw using key
      choose o ho using fun i => h1 (w i)
      simp only [ReciprocityTheory.Def.d1, LinearMap.coe_mk, AddHom.coe_mk]
      rw [actT, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, memT]
      refine ⟨∑ i, o i * e i, ?_⟩
      have hl : ∀ i, lam (algebraMap O LL (f i) * z x) = ((P.PD K).χ x.1 : ℚ_[l]) * Ft i x.2
          - Ft i (x.1 * x.2) + Ft i x.1 - (w i : ℚ_[l]) := fun i => by rw [hw i]; ring
      conv_rhs => rw [h3 (z x)]
      simp_rw [hl]
      rw [map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ho, Algebra.smul_def]
      simp only [map_sub, map_add, map_mul]
      ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleMemCoboundariesOfTateOrthogonalStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_mem_coboundaries_of_tate_orthogonal : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∀ b ∈ continuousCocycles A'.ρ, (∀ a ∈ continuousCocycles A.ρ, CobL (P.PD K) (cupL A'.ρ m a b)) → b ∈ B1 A'.ρ := by
  first | exact @GlobalTheory.TateOrthV.cocycle_mem_coboundaries_of_tate_orthogonal' | exact GlobalTheory.TateOrthV.cocycle_mem_coboundaries_of_tate_orthogonal' | (intros; apply GlobalTheory.TateOrthV.cocycle_mem_coboundaries_of_tate_orthogonal' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleRestrictionScalarsRationalCoordsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_restrictionScalars_rational_coords : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l)) (c₀ : ↥(GK K) → n × Fin r → ℚ_[l]),
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1)) →
    (∀ g h, c (g * h) = c g + (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).mulVec (c h)) →
    ∀ g h, c₀ (g * h) = c₀ g + (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).mulVec (c₀ h) := by
  first | exact @GlobalTheory.PMon.cocycle_rat_coords | exact GlobalTheory.PMon.cocycle_rat_coords | (intros; apply GlobalTheory.PMon.cocycle_rat_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroMapPowNullFacts
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.TopBasis

variable {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}

theorem pow_smul_top_eq {R : Type} [CommRing R] (J : Ideal R) (n : ℕ) :
    (J ^ n • ⊤ : Submodule R R) = J ^ n := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem c_mem_of_mem (tb : TopBasis s I ι) (n : ℕ) {x : A} (hx : x ∈ (I ^ n).map s) (i : ι) :
    tb.c i x ∈ I ^ n := by
  have key : ∀ a : A, tb.c i (a * x) ∈ I ^ n := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      intro a
      rw [mul_comm, tb.c_mul]
      exact Ideal.mul_mem_right _ _ hz
    | zero => intro a; simp
    | add y z _ _ hy hz => intro a; rw [mul_add, map_add]; exact add_mem (hy a) (hz a)
    | smul b y _ hy => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hy (a * b)
  simpa using key 1

theorem mem_map_pow_iff (tb : TopBasis s I ι) (n : ℕ) (x : A) :
    x ∈ (I ^ n).map s ↔ ∀ i, tb.c i x ∈ I ^ n :=
  ⟨fun h i => c_mem_of_mem tb n h i, fun h => by simpa using tb.approx x n ∅ (fun i _ => h i)⟩

theorem eq_zero_of_c_eq_zero (tb : TopBasis s I ι) (x : A) (h : ∀ i, tb.c i x = 0) : x = 0 := by
  refine tb.complete.toIsHausdorff.haus x fun n => ?_
  rw [SModEq.sub_mem, sub_zero, pow_smul_top_eq, ← Ideal.map_pow]
  exact (mem_map_pow_iff tb n x).2 fun i => by rw [h i]; exact zero_mem _

theorem exists_coeffs_eq_of_null (tb : TopBasis s I ι) (hS : IsHausdorff I S) (a : ι → S)
    (ha : ∀ n : ℕ, {i | a i ∉ I ^ n}.Finite) : ∃ x, ∀ i, tb.c i x = a i := by
  classical
  let F : ℕ → Finset ι := fun n => (ha n).toFinset
  have hF : ∀ n i, i ∉ F n → a i ∈ I ^ n := fun n i hi => by
    simpa [F] using hi
  have hFm : Monotone F := by
    intro m n hmn i hi
    simp only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢
    exact fun h => hi (Ideal.pow_le_pow_right hmn h)
  let y : ℕ → A := fun n => ∑ i ∈ F n, s (a i) * tb.b i
  have hy : ∀ m n, m ≤ n → y n - y m ∈ (I ^ m).map s := by
    intro m n hmn
    have e : y n - y m = ∑ i ∈ F n \ F m, s (a i) * tb.b i := by
      simp only [y]; rw [← Finset.sum_sdiff (hFm hmn)]; ring
    rw [e]
    exact Ideal.sum_mem _ fun i hi =>
      Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hF m i (Finset.mem_sdiff.1 hi).2))
  obtain ⟨x, hx⟩ := tb.complete.toIsPrecomplete.prec (f := y) (fun {m n} hmn => by
    rw [SModEq.sub_mem, pow_smul_top_eq, ← Ideal.map_pow, ← neg_sub]
    exact neg_mem (hy m n hmn))
  refine ⟨x, fun i => ?_⟩
  rw [← sub_eq_zero]
  refine hS.haus _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, pow_smul_top_eq]
  have h1 : tb.c i (x - y n) ∈ I ^ n := by
    have h := hx n
    rw [SModEq.sub_mem, pow_smul_top_eq, ← Ideal.map_pow, ← neg_sub] at h
    exact c_mem_of_mem tb n (by simpa using neg_mem h) i
  have h2 : tb.c i (y n) - a i ∈ I ^ n := by
    have e : tb.c i (y n) = ∑ j ∈ F n, a j * tb.c i (tb.b j) := by
      simp only [y, map_sum, tb.c_mul]
    rw [e]
    by_cases hi : i ∈ F n
    · rw [Finset.sum_eq_single i (fun j _ hj => by rw [tb.c_ne i j (Ne.symm hj), mul_zero])
        (fun h => (h hi).elim), tb.c_self, mul_one, sub_self]
      exact zero_mem _
    · rw [Finset.sum_eq_zero (fun j hj => by rw [tb.c_ne i j (fun h => hi (h ▸ hj)), mul_zero]), zero_sub]
      exact neg_mem (hF n i hi)
  have e : tb.c i x - a i = tb.c i (x - y n) + (tb.c i (y n) - a i) := by rw [map_sub]; ring
  rw [e]
  exact add_mem h1 h2

end GlobalTheory.BSP.TopBasis

theorem GlobalTheory.BSP.TopBasis.coeff_facts : ∀ (S A ι : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S)
    (tb : TopBasis s I ι), (∀ x, (∀ i, tb.c i x = 0) → x = 0) ∧ (∀ (n : ℕ) x, x ∈ (I ^ n).map s ↔ ∀ i, tb.c i x ∈ I ^ n) ∧
    (IsHausdorff I S → ∀ a : ι → S, (∀ n : ℕ, {i | a i ∉ I ^ n}.Finite) → ∃ x, ∀ i, tb.c i x = a i) :=
  fun _ _ _ _ _ _ _ tb => ⟨GlobalTheory.BSP.TopBasis.eq_zero_of_c_eq_zero tb, GlobalTheory.BSP.TopBasis.mem_map_pow_iff tb,
    fun hS a ha => GlobalTheory.BSP.TopBasis.exists_coeffs_eq_of_null tb hS a ha⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutatorMemOfCoboundaryDetectsQuotient
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem commutator_mem_of_detects : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E r : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → OrdIs L p E → Detects p r A B → ∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ B := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ p E r A B hp hE hord hdet σ hσ τ hτ
  by_contra hc
  have hcA : σ * τ * σ⁻¹ * τ⁻¹ ∈ A :=
    A.mul_mem (A.mul_mem (A.mul_mem hσ hτ) (A.inv_mem hσ)) (A.inv_mem hτ)
  obtain ⟨x, a, hx, hnd⟩ := hdet _ hcA hc
  have hadd := GlobalTheory.PMon.Ram.coboundary_int_additive_mod K L p E r A x a hp hE hord hx
  have h1 : (p : ℤ) ^ r ∣ a 1 := by
    have := hadd 1 A.one_mem 1 A.one_mem
    simp only [mul_one] at this
    have h' : a 1 = -(a 1 - a 1 - a 1) := by ring
    rw [h']; exact this.neg_right
  have hinv : ∀ g ∈ A, (p : ℤ) ^ r ∣ a g⁻¹ + a g := by
    intro g hg
    have := hadd g⁻¹ (A.inv_mem hg) g hg
    rw [inv_mul_cancel] at this
    have h' : a g⁻¹ + a g = a 1 - (a 1 - a g⁻¹ - a g) := by ring
    rw [h']; exact dvd_sub h1 this
  have e1 := hadd (σ * τ * σ⁻¹) (A.mul_mem (A.mul_mem hσ hτ) (A.inv_mem hσ)) τ⁻¹ (A.inv_mem hτ)
  have e2 := hadd (σ * τ) (A.mul_mem hσ hτ) σ⁻¹ (A.inv_mem hσ)
  have e3 := hadd σ hσ τ hτ
  have e4 := hinv σ hσ
  have e5 := hinv τ hτ
  apply hnd
  have h' : a (σ * τ * σ⁻¹ * τ⁻¹) =
      (a (σ * τ * σ⁻¹ * τ⁻¹) - a (σ * τ * σ⁻¹) - a τ⁻¹) + (a (σ * τ * σ⁻¹) - a (σ * τ) - a σ⁻¹)
        + (a (σ * τ) - a σ - a τ) + (a σ⁻¹ + a σ) + (a τ⁻¹ + a τ) := by ring
  rw [h']
  exact dvd_add (dvd_add (dvd_add (dvd_add e1 e2) e3) e4) e5

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonCocycles
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

noncomputable section

namespace GlobalTheory.NewPrime

section
variable {A : Type} [CommRing A] {a r : ℕ}

theorem rect_map {B B' : Type} [AddCommGroup B] [Module A B] [AddCommGroup B'] [Module A B'] (p : B →ₗ[A] B')
    (Z : Matrix (Fin r) (Fin a) A) (x : Fin a → B) : p.compLeft (Fin r) (rect Z x) = rect Z (p ∘ x) := by
  funext c
  simp [rect, map_sum]

theorem matAct_map {B B' : Type} [AddCommGroup B] [Module A B] [AddCommGroup B'] [Module A B'] (p : B →ₗ[A] B')
    (Φ : Matrix (Fin a) (Fin a) A) (x : Fin a → B) : p ∘ matAct Φ x = matAct Φ (p ∘ x) := by
  funext c
  simp [matAct, map_sum]

end

theorem comparison_cocycles : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q Q' : Finset (PlE D.host)) (a a' : ℕ) (Φ : Matrix (Fin a) (Fin a) A) (Φ' : Matrix (Fin a') (Fin a') A) Z Z' (γ σ : Bool → GE N), Univ bkP i s κ Q Φ Z → Univ bkP i s κ Q' Φ' Z' → (∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (f : GE N → Fin D.R.r → Y), SelC bkP i s κ Y Q' f → (∀ b, f (γ b) = 0) → SelC bkP i s κ Y Q f) → (∀ (Y : Type) [AddCommGroup Y] [Module A Y] b m, repOn (Tgl i s) κ Y (σ b) m = m) → ∃ E : Matrix (Fin a) (Fin a') A, what₂ E ⊔ (what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2)) = ⊤ ∧ (∀ b, (Φ * E) b ∈ what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2)) ∧ ∀ j : Bool × Fin D.R.r, Z' (σ j.1) j.2 - Matrix.vecMul (Z (σ j.1) j.2) E ∈ what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2) := by
  intro D N X bkP i s A _ _ κ Q Q' a a' Φ Φ' Z Z' γ σ hU hU' hSel hσ
  set W : Submodule A (Fin a' → A) := what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2) with hW
  letI tY : TopologicalSpace ((Fin a' → A) ⧸ W) := ⊥
  haveI : DiscreteTopology ((Fin a' → A) ⧸ W) := ⟨rfl⟩
  let gens : Fin a' → (Fin a' → A) ⧸ W := fun j => W.mkQ (Pi.single j 1)
  have hsum : ∀ v : Fin a' → A, ∑ j, v j • gens j = W.mkQ v := by
    intro v
    have : v = ∑ j, v j • (Pi.single j (1 : A) : Fin a' → A) := by
      funext c
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [this]
    simp [gens, map_sum]
  have hrect : ∀ g c, rect (Z' g) gens c = W.mkQ (Z' g c) := fun g c => hsum _
  have hgens : matAct Φ' gens = 0 := by
    funext b
    have : matAct Φ' gens b = W.mkQ (Φ' b) := hsum (Φ' b)
    rw [this]
    exact (Submodule.Quotient.mk_eq_zero W).2 ((le_sup_left : what₂ Φ' ≤ W) (Submodule.subset_span ⟨b, rfl⟩))
  have hf' := (hU' ((Fin a' → A) ⧸ W)).1 gens hgens
  have hγ : ∀ b, (fun g => rect (Z' g) gens) (γ b) = 0 := by
    intro b
    funext c
    show rect (Z' (γ b)) gens c = 0
    rw [hrect]
    exact (Submodule.Quotient.mk_eq_zero W).2
      ((le_sup_right : what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2) ≤ W) (Submodule.subset_span ⟨(b, c), rfl⟩))
  have hf := hSel _ _ hf' hγ
  obtain ⟨x, hx, m, hm⟩ := (hU ((Fin a' → A) ⧸ W)).2.2 _ hf
  obtain ⟨E, hE⟩ : ∃ E : Matrix (Fin a) (Fin a') A, ∀ b, W.mkQ (E b) = x b :=
    ⟨fun b => (Submodule.mkQ_surjective W (x b)).choose, fun b => (Submodule.mkQ_surjective W (x b)).choose_spec⟩
  have hvm : ∀ v : Fin a → A, W.mkQ (∑ k, v k • E k) = ∑ k, v k • x k := fun v => by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smul, hE]
  refine ⟨E, ?_, ?_, ?_⟩
  · let S : Submodule A ((Fin a' → A) ⧸ W) := Submodule.span A (Set.range x)
    letI tS : TopologicalSpace (((Fin a' → A) ⧸ W) ⧸ S) := ⊥
    haveI : DiscreteTopology (((Fin a' → A) ⧸ W) ⧸ S) := ⟨rfl⟩
    have hpx : S.mkQ ∘ x = 0 := by
      funext b
      exact (Submodule.Quotient.mk_eq_zero S).2 (Submodule.subset_span ⟨b, rfl⟩)
    have hz : S.mkQ ∘ gens = 0 := by
      refine (hU' (((Fin a' → A) ⧸ W) ⧸ S)).2.1 _ ?_ ⟨S.mkQ.compLeft (Fin D.R.r) m, fun g => ?_⟩
      · rw [← matAct_map, hgens]
        funext b
        simp
      · have e := congrArg (S.mkQ.compLeft (Fin D.R.r)) (hm g)
        rw [map_sub, map_sub, rect_map, rect_map, hpx, repOn_map] at e
        have h0 : rect (Z g) (0 : Fin a → ((Fin a' → A) ⧸ W) ⧸ S) = 0 := by
          funext c
          simp [rect]
        rw [h0, sub_zero] at e
        exact e
    have hgS : ∀ j, gens j ∈ S := fun j =>
      (Submodule.Quotient.mk_eq_zero S).1 (congrFun hz j)
    rw [eq_top_iff]
    intro v _
    have hvS : W.mkQ v ∈ S := by
      rw [← hsum]
      exact S.sum_mem fun j _ => S.smul_mem _ (hgS j)
    have hSm : S = (what₂ E).map W.mkQ := by
      show Submodule.span A (Set.range x) = (Submodule.span A (Set.range E)).map W.mkQ
      rw [Submodule.map_span]
      congr 1
      ext y
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨E b, ⟨b, rfl⟩, hE b⟩
      · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
        exact ⟨b, (hE b).symm⟩
    rw [hSm] at hvS
    obtain ⟨e, he, hev⟩ := hvS
    have hd : v - e ∈ W := by
      rw [← Submodule.Quotient.mk_eq_zero W, ← Submodule.mkQ_apply, map_sub, hev, sub_self]
    have : v = e + (v - e) := by abel
    rw [this]
    exact Submodule.add_mem_sup he hd
  · intro b
    rw [← Submodule.Quotient.mk_eq_zero W, ← Submodule.mkQ_apply]
    have e1 : (Φ * E) b = ∑ k, Φ b k • E k := by
      funext c
      simp [Matrix.mul_apply, Finset.sum_apply]
    rw [e1, hvm (Φ b)]
    exact congrFun hx b
  · rintro ⟨b, c⟩
    rw [← Submodule.Quotient.mk_eq_zero W, ← Submodule.mkQ_apply]
    have e1 : Matrix.vecMul (Z (σ b) c) E = ∑ k, Z (σ b) c k • E k := by
      funext t
      simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
    have e2 := congrFun (hm (σ b)) c
    rw [hσ, sub_self] at e2
    show W.mkQ (Z' (σ b) c - Matrix.vecMul (Z (σ b) c) E) = 0
    rw [map_sub, e1, hvm (Z (σ b) c), ← hrect]
    exact e2

end GlobalTheory.NewPrime
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonMapIntertwinesGroupAlgebraAction
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf Formalism.MainNotions.PairedCharacterCondition
open scoped TensorProduct

namespace GlobalTheory.PendOf.CenKey

theorem stable (D : D7) (i : D.nd.Loc) (h : OnMtPreservesTypeV D) (c : MonoidAlgebra ℂ (G0g D.nd))
    (s : Set (D.naut.AV i)) (F : D.what₂.Mt (D.nd.mu i) (D.nd.j i))
    (hF : F ∈ ⨆ P ∈ s, D.naut.typeV i P) :
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c F ∈ ⨆ P ∈ s, D.naut.typeV i P := by
  have : (⨆ P ∈ s, D.naut.typeV i P) ≤
      (⨆ P ∈ s, D.naut.typeV i P).comap (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c) := by
    refine iSup₂_le fun P hP G hG => ?_
    exact le_biSup (D.naut.typeV i) hP (h i P c G hG)
  exact this hF

theorem phi_mem (D : D7) (i : D.nd.Loc) (S : Sec D i)
    (u : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) :
    S.Φ u ∈ ⨆ P ∈ {P | D.naut.ptV i P ≠ none}, D.naut.typeV i P := by
  have hu : u ∈ ⨆ x, heckeEig (D.nd.T i) (D.nd.act i) x := by
    rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.EigSpan_holds D.nd i]; exact Submodule.mem_top
  induction hu using Submodule.iSup_induction' with
  | mem x u hu =>
    have hle : typeSum D i (some x) ≤ ⨆ P ∈ {P | D.naut.ptV i P ≠ none}, D.naut.typeV i P := by
      refine iSup₂_le fun P hP => ?_
      have hP' : D.naut.ptV i P = some x := hP
      exact le_biSup (D.naut.typeV i)
        (show P ∈ {P | D.naut.ptV i P ≠ none} from by simp [hP'])
    exact hle (S.eig x u hu)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb

theorem phi_onMt : ∀ (D : D7) (i : D.nd.Loc) (S : Sec D i), OnMtPreservesTypeV D →
    ∀ (c : MonoidAlgebra ℂ (G0g D.nd)) (x y : D.what₂.MtL (D.nd.mu i) (D.nd.j i)),
    D.what₂.jMt _ _ y = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (D.what₂.jMt _ _ x) →
    S.Φ (D.nd.prMt i y) = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (S.Φ (D.nd.prMt i x)) := by
  intro D i S h c x y hxy
  have hd : Disjoint (⨆ P ∈ {P | D.naut.ptV i P ≠ none}, D.naut.typeV i P)
      (⨆ P ∈ {P | D.naut.ptV i P = none}, D.naut.typeV i P) :=
    (D.naut.typeV_indep i).disjoint_biSup_biSup
      (Set.disjoint_left.2 fun P h1 h2 => h1 h2)
  have h1 := Submodule.sub_mem _ (phi_mem D i S (D.nd.prMt i y))
    (stable D i h c _ _ (phi_mem D i S (D.nd.prMt i x)))
  have h2 := Submodule.sub_mem _ (stable D i h c {P | D.naut.ptV i P = none} _ (S.split x)) (S.split y)
  have e : D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (D.what₂.jMt _ _ x - S.Φ (D.nd.prMt i x)) -
      (D.what₂.jMt _ _ y - S.Φ (D.nd.prMt i y)) =
      S.Φ (D.nd.prMt i y) - D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (S.Φ (D.nd.prMt i x)) := by
    rw [map_sub, hxy]; abel
  rw [e] at h2
  exact sub_eq_zero.1 (Submodule.disjoint_def.1 hd _ h1 h2)

end GlobalTheory.PendOf.CenKey
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorExponentAtPlacesStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conductor_exponent_at_places : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)), PlacesOk H q0 w0 → ∀ w : HeightOneSpectrum (𝓞 H.E), (Over4 H w → expIn (cond0 H w0) (below w) = 2) ∧ (below w = below w0 → ¬ Over4 H w ∧ expIn (cond0 H w0) (below w) = 1) ∧ (¬ Over4 H w → below w ≠ below w0 → expIn (cond0 H w0) (below w) = 0) := by
  first | exact @GlobalTheory.LamTie.expIn_cond0 | exact GlobalTheory.LamTie.expIn_cond0 | (intros; apply GlobalTheory.LamTie.expIn_cond0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateEmbeddingIsCMTypeSqrtMinusDStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateEmbedding_isCMType_sqrtMinusD : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), IsCMType (phi H) ∧ ∀ g g', phi H g H.sqrtMinusD = phi H g' H.sqrtMinusD := by
  first | exact @GlobalTheory.LamTie.CMType.phi_cmType | exact GlobalTheory.LamTie.CMType.phi_cmType | (intros; apply GlobalTheory.LamTie.CMType.phi_cmType <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCochainOfDeRhamCoboundaryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_cochain_of_deRham_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ (k : ℕ) (x : Fin k → V ⊗[ℚ_[l]] P.R.BdR) (β : Fin k → ↥(GK K) → ℚ_[l]), (∀ i, Continuous (β i)) → ∀ (x' : V ⊗[ℚ_[l]] P.R.BdR) (f : ↥(GK K) → V), (∀ g, f g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = ∑ i, β i g • x i + (actVdR (P.PD K) ρ g x' - x')) → Continuous f := by
  first | exact @GlobalTheory.ContDR.cont_dR | exact GlobalTheory.ContDR.cont_dR | (intros; apply GlobalTheory.ContDR.cont_dR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutCongruenceValEqHeckeValueIdealOffSupportValStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutCongruenceVal_eq_heckeValueIdealOffSupportVal : ∀ (D : D7) (i : D.nd.Loc) (Xs : Set (D.nd.X i)) (π : D.nd.X i), PairedCharacterCondition.CongruenceModules.vccCut i Xs π = GlobalTheory.Cut.vccOff i Xs π := by
  first | exact @GlobalTheory.Pass.CutEq.main | exact GlobalTheory.Pass.CutEq.main | (intros; apply GlobalTheory.Pass.CutEq.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicIntegersEqWittZetaSubOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism GlobalTheory.PrismS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomic_integers_eq_witt_zeta_sub_one : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), 1 ≤ s → ∀ ζ : Om l, IsPrimitiveRoot ζ (l ^ s) → ∀ t : OC l, (t : ℂ_[l]) = ((ζ - 1 : Om l) : ℂ_[l]) → (∀ r : Polynomial (WK K), r.natDegree < l ^ (s - 1) * (l - 1) → r.eval₂ (intToOC (unr K)) t = 0 → r = 0) ∧ (K.1 ≤ Ks K s → ∀ x : ↥(OL K), ∃ r : Polynomial (WK K), r.eval₂ (intToOC (unr K)) t = intToOC K x) := by
  first | exact @GlobalTheory.PrismS.Poly.main | exact GlobalTheory.PrismS.Poly.main | (intros; apply GlobalTheory.PrismS.Poly.main <;> assumption)
end

