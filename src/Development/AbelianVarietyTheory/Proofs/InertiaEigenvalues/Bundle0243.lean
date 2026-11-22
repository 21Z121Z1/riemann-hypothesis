import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionEveryLocalisation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralOfBounded
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0230
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Formalism.UnipotentAdelicQuotients.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemRootsBarXSubC
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTwistCocycleCoboundary
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0239

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1H0TransportLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.GaloisTransport

section Generic

variable {R G' G Q M : Type} [CommRing R] [Group G'] [TopologicalSpace G'] [Group G]
  [TopologicalSpace G] [AddCommGroup Q] [Module R Q] {N : ℕ} [AddCommGroup M] [Module (ZMod N) M]
  [TopologicalSpace M] [DiscreteTopology M]

theorem card_H1_transport (φ : G' ≃* G) (hφ : Continuous φ ∧ Continuous φ.symm)
    (act : G' → Q → Q) (Z B : Submodule R (G' → Q))
    (hZ : ∀ c, c ∈ Z ↔ IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + act g (c h))
    (hB : ∀ c, c ∈ B ↔ ∃ t, ∀ g, c g = act g t - t)
    (e : Q ≃+ M) (rho : Representation (ZMod N) G M)
    (hr : ∀ g x, rho g (e x) = e (act (φ.symm g) x)) :
    Nat.card (↥Z ⧸ B.comap Z.subtype) = Nat.card (ReciprocityTheory.Gal.H1 rho) := by
  have hr' : ∀ g x, rho (φ g) (e x) = e (act g x) := fun g x => by
    rw [hr, MulEquiv.symm_apply_apply]
  let F : (G' → Q) → (G → M) := fun c g => e (c (φ.symm g))
  have hF : ∀ c g, F c (φ g) = e (c g) := fun c g => by simp only [F, MulEquiv.symm_apply_apply]
  have hFB : ∀ c, c ∈ B ↔ F c ∈ ReciprocityTheory.Gal.B1 rho := by
    intro c
    rw [hB, ReciprocityTheory.Gal.mem_coboundaries1]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨e t, fun g => ?_⟩
      simp only [F, ht, map_sub, hr]
    · rintro ⟨m, hm⟩
      refine ⟨e.symm m, fun g => ?_⟩
      have h1 := hm (φ g)
      rw [hF] at h1
      apply e.injective
      rw [h1, map_sub, ← hr', e.apply_symm_apply]
  have hZf : ∀ c : ↥Z, F c.1 ∈ ReciprocityTheory.Gal.Z1 rho := fun c => by
    obtain ⟨hc1, hc2⟩ := (hZ c.1).1 c.2
    refine ⟨((hc1.comp_continuous hφ.2).comp e).continuous, fun g h => ?_⟩
    simp only [F, map_mul, hc2, map_add, hr]
  have hZb : ∀ f : ↥(ReciprocityTheory.Gal.Z1 rho), (fun g => e.symm (f.1 (φ g))) ∈ Z := fun f => by
    obtain ⟨hf1, hf2⟩ := (ReciprocityTheory.Gal.mem_Z1_iff_cocycle _ _).1 f.2
    refine (hZ _).2 ⟨((IsLocallyConstant.iff_continuous _).2 (hf1.comp hφ.1)).comp e.symm,
      fun g h => ?_⟩
    apply e.injective
    have h2 := hr' g (e.symm (f.1 (φ h)))
    rw [e.apply_symm_apply] at h2
    simp only [map_mul, hf2, map_add, AddEquiv.apply_symm_apply, h2]
  let E : ↥Z ≃ ↥(ReciprocityTheory.Gal.Z1 rho) :=
    { toFun := fun c => ⟨F c.1, hZf c⟩
      invFun := fun f => ⟨fun g => e.symm (f.1 (φ g)), hZb f⟩
      left_inv := fun c => Subtype.ext (funext fun g => by
        show e.symm (F c.1 (φ g)) = c.1 g
        rw [hF, e.symm_apply_apply])
      right_inv := fun f => Subtype.ext (funext fun g => by
        show e (e.symm (f.1 (φ (φ.symm g)))) = f.1 g
        rw [e.apply_symm_apply, MulEquiv.apply_symm_apply]) }
  have hEsub : ∀ a b : ↥Z, ((E a - E b : ↥(ReciprocityTheory.Gal.Z1 rho)) : G → M) = F ((a - b : ↥Z) : G' → Q) :=
    fun a b => funext fun g => by
      show e (a.1 (φ.symm g)) - e (b.1 (φ.symm g)) = e (a.1 (φ.symm g) - b.1 (φ.symm g))
      rw [map_sub]
  refine Nat.card_congr (Quotient.congr E fun a b => ?_)
  rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap,
    Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_subtype, hEsub, hFB]

theorem card_H0_transport (φ : G' ≃* G) (act : G' → Q → Q)
    (e : Q ≃+ M) (rho : Representation (ZMod N) G M)
    (hr : ∀ g x, rho g (e x) = e (act (φ.symm g) x)) :
    Nat.card {x : Q // ∀ g, act g x = x} = Nat.card (ReciprocityTheory.Gal.H0 rho) := by
  have hr' : ∀ g x, rho (φ g) (e x) = e (act g x) := fun g x => by
    rw [hr, MulEquiv.symm_apply_apply]
  refine Nat.card_congr
    { toFun := fun x => ⟨e x.1, (ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere _ _).2 fun g => by rw [hr, x.2]⟩
      invFun := fun m => ⟨e.symm m.1, fun g => by
        apply e.injective
        rw [← hr', e.apply_symm_apply]
        exact (ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 m.2 (φ g)⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun m => Subtype.ext (e.apply_symm_apply m.1) }

end Generic

theorem card_H1_H0_transport : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (I : Submodule O ↥LA.T) (hI : StableSub LA I) (N : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod N) M] [TopologicalSpace M] [DiscreteTopology M] (e : (↥LA.T ⧸ I) ≃+ M) (rho : Representation (ZMod N) (Formalism.GaloisCohomology.GK l K.1) M), (∀ g x, rho g (e x) = e (actQ LA I hI ((IntermediateField.fixingSubgroupEquiv K.1).symm g) x)) → Nat.card (QuotientCohomology LA I hI) = Nat.card (ReciprocityTheory.Gal.H1 rho) ∧ Nat.card {x : ↥LA.T ⧸ I // ∀ g, actQ LA I hI g x = x} = Nat.card (ReciprocityTheory.Gal.H0 rho) := by
  intro l _ K LL _ _ _ O _ _ A LA I hI N M _ _ _ _ e rho hrho
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hφ := GlobalTheory.fixingSubgroupEquiv_bicontinuous _ _ K.1
  refine ⟨card_H1_transport _ hφ (fun g x => actQ LA I hI g x) (quotientCocycles LA I hI) (BQ LA I hI)
    (fun c => Iff.rfl) (fun c => ?_) e rho hrho,
    card_H0_transport _ (fun g x => actQ LA I hI g x) e rho hrho⟩
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, fun g => (congrFun ht g).symm⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, funext fun g => (ht g).symm⟩

end GlobalTheory.GaloisTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolySpanAndHomRelationsOfAdmissible
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory

theorem charpoly_span_and_hom_relations_of_admissible : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), TruncatedSeriesCountingIdentities.admG1 i r → LargeLevelLemmas.CharpolyCoeffsLemmaFamily i r ∧ LargeLevelLemmas.SpanQuotientLemma i r ρ π ∧ LargeLevelLemmas.HomRelationsLemmaAllChoices i r ρ π :=
  fun _ i r ρ π h => ⟨LargeLevelLemmas.span_lemma_clause i r h, LargeLevelLemmas.eigenspace_lemma_clause i r ρ π, LargeLevelLemmas.relation_lemma_clause i r ρ π⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientRingIntegersCompactAdicProperties
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.GoodCoeff

section Open

variable {l : ℕ} [Fact l.Prime] {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
  [IsModuleTopology ℚ_[l] LL]

theorem continuous_algebraMap_padic : Continuous (algebraMap ℚ_[l] LL) := by
  haveI := IsModuleTopology.toContinuousSMul ℚ_[l] LL
  have h : (algebraMap ℚ_[l] LL : ℚ_[l] → LL) = fun c => c • (1 : LL) :=
    funext Algebra.algebraMap_eq_smul_one
  rw [h]
  exact continuous_id.smul continuous_const

theorem padicInt_mem (A : Subring LL) (hA : IsOpen (A : Set LL)) (u : ℤ_[l]) :
    algebraMap ℚ_[l] LL (u : ℚ_[l]) ∈ A := by
  have hU : IsOpen ((algebraMap ℚ_[l] LL) ⁻¹' (A : Set LL)) :=
    hA.preimage continuous_algebraMap_padic
  have h0 : (0 : ℚ_[l]) ∈ (algebraMap ℚ_[l] LL) ⁻¹' (A : Set LL) := by
    simp [A.zero_mem]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 h0
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (Padic.norm_p_lt_one (p := l))
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n u)
  have hu : (u : ℚ_[l]) = ((u.appr n : ℕ) : ℚ_[l]) + (w : ℚ_[l]) * (l : ℚ_[l]) ^ n := by
    have := congrArg (fun z : ℤ_[l] => (z : ℚ_[l])) hw
    push_cast at this
    linear_combination -this
  have h1 : algebraMap ℚ_[l] LL ((w : ℚ_[l]) * (l : ℚ_[l]) ^ n) ∈ A := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_pow]
    calc ‖(w : ℚ_[l])‖ * ‖(l : ℚ_[l])‖ ^ n ≤ 1 * ‖(l : ℚ_[l])‖ ^ n :=
          mul_le_mul_of_nonneg_right (PadicInt.norm_le_one w) (by positivity)
      _ < ε := by rwa [one_mul]
  rw [hu, map_add, map_natCast]
  exact A.add_mem (natCast_mem A _) h1

end Open

theorem good_coeff_integers : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → (∀ x : LL, x ∈ Set.range (algebraMap O LL) ↔ RingHom.IsIntegralElem ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])) x) ∧ IsCompact (Set.range (algebraMap O LL)) ∧ (∀ n : ℕ, Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ n})) ∧ IsAdicComplete (Ideal.span {((l : ℕ) : O)}) O := by
  first
  | exact @_root_.GlobalTheory.PowerImageOpen.main
  | exact _root_.GlobalTheory.PowerImageOpen.main
  | (apply _root_.GlobalTheory.PowerImageOpen.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerImageOpen.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerImageOpen.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerImageOpen.main ..)

end GlobalTheory.GoodCoeff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelLatticeMapKilledByPrimePow
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow

theorem main : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Stmt := by
  intro O K _ _ _ _ _ l e a _ _ _ _ hT ι κ _ _ _ _ Sig U N η H hB D₁ D₂ hD₁ hD₂ F hF
  haveI : FiniteDimensional ℚ_[l] K := hT.finite
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  exact GlobalTheory.T.killsCoker_all_of_killsCoker_phiModuleLattice O K l e a ι κ η H D₁ D₂ F _
    (GlobalTheory.T.breuilKisin_pow_kills_lattice_cokernel O K l e a ι κ η H D₁ D₂ F Sig U N hB hD₁.chars_subset hD₂ hF)

end GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexFieldAutActsHarishChandraCharactersStatement
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexFieldAut_acts_harishChandra_characters : ∀ (g : ℕ) [Fact g.Prime] (σ : ℂ ≃+* ℂ), (∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ), (IsIrr χ → IsIrr (σ ∘ χ)) ∧ (zOf χ).coeff.mapRange σ (map_zero σ) = (zOf (σ ∘ χ)).coeff ∧ ∀ β, ip (σ ∘ χ) (σ ∘ β) = σ (ip χ β)) ∧ (∀ (L : List (Pc g)) (n : ℕ), hcL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) n = σ ∘ hcL L n) ∧ ∀ (d : ℕ) (χ : Gn g d → ℂ), IsCusp χ → IsCusp (σ ∘ χ) := by
  first | exact @GlobalTheory.Adopt.complexFieldAut_acts_harishChandra_characters | exact GlobalTheory.Adopt.complexFieldAut_acts_harishChandra_characters | (intros; apply GlobalTheory.Adopt.complexFieldAut_acts_harishChandra_characters <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContractEquivariant
section
noncomputable section

namespace GlobalTheory.PushCob

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage TensorProduct

theorem contract_equivariant {R Y Q : Type} [CommRing R] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Q] [Module R Q] (ψ : Y →ₗ[R] R) (A : Y →ₗ[R] Y) (B : Q →ₗ[R] Q) (u t : R)
    (h : ∀ y, ∃ z, ψ (A y) - u * ψ y = t * z) (x : Y ⊗[R] Q) :
    ∃ q : Q, TensorProduct.lid R Q (ψ.rTensor Q (TensorProduct.map A B x)) =
      u • B (TensorProduct.lid R Q (ψ.rTensor Q x)) + t • q := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul y q =>
    obtain ⟨z, hz⟩ := h y
    refine ⟨z • B q, ?_⟩
    simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul,
      smul_smul, ← add_smul]
    rw [← hz]; congr 1; ring
  | add x x' hx hx' =>
    obtain ⟨q, hq⟩ := hx
    obtain ⟨q', hq'⟩ := hx'
    refine ⟨q + q', ?_⟩
    simp only [map_add, hq, hq', smul_add]
    abel

theorem actQab_mk {O G WC : Type} [CommRing O] [Group G] [CommRing WC] [Algebra O WC]
    {AA : Subalgebra O WC} {act : G →* (WC ≃ₐ[O] WC)} {ξ : WCˣ} (h : XiOK AA act ξ) (a b : ℤ)
    (g : G) (m : ↥(Mxi AA ξ a)) :
    actQab h a b g (Submodule.Quotient.mk m) = Submodule.Quotient.mk (actM h a g m) := rfl

variable {l : ℕ} [Fact l.Prime]

theorem inclW_injective : Function.Injective (inclW l) :=
  WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))

theorem inclW_zl (z : ℤ_[l]) :
    inclW l (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℤ_[l] (WCb l) z := (inclWA l).commutes z

theorem mem_Mxi {P : LocPrime l} (AI : LocAinf l P) (k : ℕ) (w : WCb l)
    (hw : w ∈ Mxi (AinfSub l) (xiU AI) (k : ℤ)) : ∃ a : Ainf l, w = inclW l (AI.ξ ^ k * a) := by
  obtain ⟨y, ⟨a, rfl⟩, rfl⟩ := hw
  refine ⟨a, ?_⟩
  rw [LinearMap.mulLeft_apply, zpow_natCast, Units.val_pow_eq_pow_val, map_mul, map_pow]
  rfl

theorem mem_Mxi_zero {P : LocPrime l} (AI : LocAinf l P) (w : ↥(Mxi (AinfSub l) (xiU AI) 0)) :
    ∃ a : Ainf l, (w : WCb l) = inclW l a := by
  simpa using mem_Mxi AI 0 w w.2

def scaled {Y : Type} [AddCommGroup Y] [Module ℤ_[l] Y] (ψ : Y →ₗ[ℤ_[l]] ℚ_[l]) (r : ℕ)
    (h : ∀ y, ‖ψ y‖ ≤ (l : ℝ) ^ r) : Y →ₗ[ℤ_[l]] ℤ_[l] where
  toFun y := ⟨(l : ℚ_[l]) ^ r * ψ y, by
    have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
    exact h y⟩
  map_add' y y' := by
    apply Subtype.ext
    change _ = (l : ℚ_[l]) ^ r * ψ y + (l : ℚ_[l]) ^ r * ψ y'
    rw [← mul_add, ← map_add]
  map_smul' z y := by
    apply Subtype.ext
    change (l : ℚ_[l]) ^ r * ψ (z • y) = (z : ℚ_[l]) * ((l : ℚ_[l]) ^ r * ψ y)
    rw [map_smul, Algebra.smul_def, PadicInt.algebraMap_apply]
    ring

theorem scaled_coe {Y : Type} [AddCommGroup Y] [Module ℤ_[l] Y] (ψ : Y →ₗ[ℤ_[l]] ℚ_[l]) (r : ℕ)
    (h : ∀ y, ‖ψ y‖ ≤ (l : ℝ) ^ r) (y : Y) :
    ((scaled ψ r h y : ℤ_[l]) : ℚ_[l]) = (l : ℚ_[l]) ^ r * ψ y := rfl

theorem push_coboundary : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s e r N : ℕ) (Y : Type) [AddCommGroup Y] [Module ℤ_[l] Y] (ρ : ↥(Gj K s) →* (Y →ₗ[ℤ_[l]] Y)) (ψ : Y →ₗ[ℤ_[l]] ℚ_[l]), (∀ y, ‖ψ y‖ ≤ (l : ℝ) ^ r) → (∀ (σ : GQ l) (hσ : σ ∈ Gj K s) (y : Y), ‖ψ (ρ ⟨σ, hσ⟩ y) - (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * ψ y‖ ≤ 1) → ∀ (f : ↥(Gj K s) → Y) (c : GQ l → ℚ_[l]), (∀ (σ : GQ l) (hσ : σ ∈ Gj K s), c σ = ψ (f ⟨σ, hσ⟩)) → ∀ one : ↥(Mxi (AinfSub l) (xiU (D.locA l)) 0), (one : WCb l) = 1 → IsCob (repQ (D.locA l) (Gj K s) ρ 0 ((e : ℤ) + 1)) (fun g => (l : ℤ_[l]) ^ N • (f g ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU (D.locA l)) 0 ((e : ℤ) + 1)))) → ∃ b ∈ ((D.loc l).PD (botExt l)).Fil 0, ∀ σ ∈ Gj K s, ∃ a : Ainf l, algebraMap ℚ_[l] (D.loc l).R.BdR ((l : ℚ_[l]) ^ N * c σ) - (algebraMap ℚ_[l] (D.loc l).R.BdR (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (D.loc l).actQdR σ b - b) - (D.loc l).ιB ((D.locA l).ιA a) ∈ ((D.loc l).PD (botExt l)).Fil ((e : ℤ) + 1) := by
  intro D l _ K s e r N Y _ _ ρ ψ hψ hρ f c hc one hone hcob
  obtain ⟨x, hx⟩ := hcob
  have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hlr : (l : ℚ_[l]) ^ r ≠ 0 := pow_ne_zero _ hl
  obtain ⟨m0, hm0⟩ := Submodule.Quotient.mk_surjective _
    (TensorProduct.lid ℤ_[l] _ ((scaled ψ r hψ).rTensor _ x))
  obtain ⟨a0, ha0⟩ := mem_Mxi_zero _ m0
  refine ⟨qB (D.loc l) ((l : ℚ_[l]) ^ r)⁻¹ * io (D.locA l) a0, qB_mul_mem _ (io_mem _ _), ?_⟩
  intro σ hσ
  have hn : ‖(((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, (cyc_basic l _ (D.loc l).χQ_cyc).1, one_zpow]
  set u' : ℚ_[l] := (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) with hu'
  let u : ℤ_[l] := ⟨u', hn⟩
  have hu : (u : ℚ_[l]) = u' := rfl
  obtain ⟨q, hq⟩ := contract_equivariant (scaled ψ r hψ) (ρ ⟨σ, hσ⟩)
    (actQab (act := (D.locA l).actWCbHom.comp (Gj K s).subtype)
      ⟨fun g x hx => (xiOK (D.locA l)).1 (g : GQ l) x hx, (xiOK (D.locA l)).2.1,
        fun g => (xiOK (D.locA l)).2.2 (g : GQ l)⟩ 0 ((e : ℤ) + 1) ⟨σ, hσ⟩) u ((l : ℤ_[l]) ^ r)
    (fun y => ⟨⟨_, hρ σ hσ y⟩, by
      apply Subtype.ext
      change (l : ℚ_[l]) ^ r * ψ (ρ ⟨σ, hσ⟩ y) - u' * ((l : ℚ_[l]) ^ r * ψ y) =
        (((l : ℤ_[l]) ^ r : ℤ_[l]) : ℚ_[l]) * (ψ (ρ ⟨σ, hσ⟩ y) - u' * ψ y)
      push_cast
      ring⟩) x
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a, ha⟩ := mem_Mxi_zero _ m
  have h1 := congrArg (fun w => TensorProduct.lid ℤ_[l] _ ((scaled ψ r hψ).rTensor _ w))
    (hx ⟨σ, hσ⟩)
  simp only [map_smul, map_sub, LinearMap.rTensor_tmul, TensorProduct.lid_tmul] at h1
  rw [← hm0] at hq
  have h2 := h1.trans (congrArg₂ (· - ·) hq hm0.symm)
  beta_reduce at h2
  erw [actQab_mk] at h2
  simp only [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add,
    ← Submodule.Quotient.mk_sub] at h2
  rw [Submodule.Quotient.eq, Submodule.mem_comap] at h2
  obtain ⟨a', ha'⟩ := mem_Mxi (D.locA l) (e + 1) _ (by rw [Nat.cast_succ]; exact h2)
  have h3 : algebraMap ℤ_[l] (Ainf l) ((l : ℤ_[l]) ^ N * scaled ψ r hψ (f ⟨σ, hσ⟩)) -
      (algebraMap ℤ_[l] (Ainf l) u * (D.locA l).actW σ a0 +
        algebraMap ℤ_[l] (Ainf l) ((l : ℤ_[l]) ^ r) * a - a0) = (D.locA l).ξ ^ (e + 1) * a' := by
    apply inclW_injective
    rw [← ha']
    have h4 : inclW l ((D.locA l).actW σ a0) = (D.locA l).actWCbHom σ (m0 : WCb l) := by
      rw [ha0, inclW_act]; rfl
    rw [map_sub, map_sub, map_add, inclW_zl, map_mul (inclW l), map_mul (inclW l), inclW_zl,
      inclW_zl, h4, ← ha0, ← ha]
    change _ = (l : ℤ_[l]) ^ N • scaled ψ r hψ (f ⟨σ, hσ⟩) • (one : WCb l) -
      (u • (D.locA l).actWCbHom σ (m0 : WCb l) + (l : ℤ_[l]) ^ r • (m : WCb l) - (m0 : WCb l))
    rw [hone, smul_smul, ← Algebra.algebraMap_eq_smul_one, Algebra.smul_def, Algebra.smul_def]
  have h5 := congrArg (io (D.locA l)) h3
  rw [map_sub, map_sub, map_add, io_zl _ (D.locT l), map_mul (io _), map_mul (io _),
    map_mul (io _), map_pow (io _), io_zl _ (D.locT l), io_zl _ (D.locT l), io_act] at h5
  have h6 : io (D.locA l) (D.locA l).ξ ^ (e + 1) * io (D.locA l) a' ∈
      FilB (D.loc l) ((e : ℤ) + 1) := by
    have := FilB_mul (FilB_pow (io_ξ_mem (D.locA l)) (e + 1)) (io_mem (D.locA l) a')
    simpa using this
  refine ⟨a, ?_⟩
  have h7 := qB_mul_mem ((l : ℚ_[l]) ^ r)⁻¹ h6
  rw [← h5] at h7
  convert h7 using 1
  have h8 : qB (D.loc l) ((l : ℚ_[l]) ^ r)⁻¹ * qB (D.loc l) ((l : ℚ_[l]) ^ r) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hlr, map_one]
  rw [map_mul ((D.loc l).actQdR σ), AlgEquiv.commutes, hc σ hσ, ← io_apply, PadicInt.coe_mul,
    scaled_coe, PadicInt.coe_pow, PadicInt.coe_pow, PadicInt.coe_natCast, hu]
  simp only [map_mul]
  linear_combination (-(qB (D.loc l) ((l : ℚ_[l]) ^ N) * qB (D.loc l) (ψ (f ⟨σ, hσ⟩))) + io (D.locA l) a) * h8

end GlobalTheory.PushCob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalCharExistsOfGreen
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GreenExists

open Polynomial Formalism.D.Classical Formalism.CyclotomicNorms Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq

variable {g : ℕ} [hg : Fact g.Prime]

theorem mem_grUnipBlock_iff {d a : ℕ} (ha : a < d) (u : Gn g d) :
    u ∈ (grUnipBlock d a : Set (GL (Fin d) (ZMod g))) ↔
      InPar a (u : Mt g d) ∧ tl a (u : Mt g d) = ((1 : Gn g a) : Mt g a) ∧
        br a (d - a) (u : Mt g d) = ((1 : Gn g (d - a)) : Mt g (d - a)) := by
  constructor
  · intro h
    refine ⟨fun i j hj hi => ?_, ?_, ?_⟩
    · rcases h i j with h1 | h1
      · rw [h1, if_neg]; rintro rfl; omega
      · omega
    · ext i j
      have hi := i.2
      have hj := j.2
      have hij : (i : ℕ) < d ∧ (j : ℕ) < d := by omega
      rcases h ⟨i, hij.1⟩ ⟨j, hij.2⟩ with h1 | h1
      · simp only [tl, entN, dif_pos hij, h1, Units.val_one, Matrix.one_apply, Fin.ext_iff]
      · simp only at h1; omega
    · ext i j
      have hi := i.2
      have hj := j.2
      have hij : a + (i : ℕ) < d ∧ a + (j : ℕ) < d := by omega
      rcases h ⟨a + i, hij.1⟩ ⟨a + j, hij.2⟩ with h1 | h1
      · simp only [br, entN, dif_pos hij, h1, Units.val_one, Matrix.one_apply, Fin.ext_iff, add_right_inj]
      · simp only at h1; omega
  · rintro ⟨h1, h2, h3⟩ i j
    have hi := i.2
    have hj := j.2
    by_cases hia : (i : ℕ) < a
    · by_cases hja : (j : ℕ) < a
      · left
        have := congrFun (congrFun h2 ⟨i, hia⟩) ⟨j, hja⟩
        simpa only [tl, entN, dif_pos (And.intro hi hj), Units.val_one, Matrix.one_apply, Fin.ext_iff] using this
      · right; omega
    · left
      by_cases hja : (j : ℕ) < a
      · rw [h1 i j hja (by omega), if_neg]; rintro rfl; omega
      · have := congrFun (congrFun h3 ⟨i - a, by omega⟩) ⟨j - a, by omega⟩
        have e1 : a + (i - a) = (i : ℕ) := by omega
        have e2 : a + (j - a) = (j : ℕ) := by omega
        have e3 : ((i : ℕ) - a = j - a) ↔ (i : ℕ) = j := by omega
        simpa only [br, entN, e1, e2, e3, dif_pos (And.intro hi hj), Units.val_one, Matrix.one_apply,
          Fin.ext_iff] using this

theorem pow_eq_self_iff {f : (ZMod g)[X]} (hf : Irreducible f) {z : Fbar g} (hz : aeval z f = 0) (n : ℕ) :
    z ^ g ^ n = z ↔ f.natDegree ∣ n := by
  have hx : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
  have has : Associated (minpoly (ZMod g) z) f :=
    (minpoly.irreducible hx).associated_of_dvd hf (minpoly.dvd _ _ hz)
  rw [hf.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, ← has.dvd_iff_dvd_left, minpoly.dvd_iff]
  simp [sub_eq_zero]

theorem rootsBar_eq {f : (ZMod g)[X]} (hf : Irreducible f) {z : Fbar g} (hz : aeval z f = 0) :
    rootsBar f = (Finset.range f.natDegree).val.map fun i => z ^ g ^ i := by
  have hroot : ∀ i, aeval (z ^ g ^ i) f = 0 := fun i => by
    have := aeval_algHom_apply ((FiniteField.frobeniusAlgHom (ZMod g) (Fbar g)) ^ i) z f
    rw [hz, map_zero] at this
    rw [← this]
    congr 1
    rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]
  have hinj : ∀ i j, i < j → j < f.natDegree → z ^ g ^ i ≠ z ^ g ^ j := fun i j hij hj h => by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hij
    have h2 : (z ^ g ^ i) ^ g ^ (m + 1) = z ^ g ^ i := by
      rw [← pow_mul, ← pow_add, ← add_assoc, ← h]
    have := Nat.le_of_dvd (Nat.succ_pos m) ((pow_eq_self_iff hf (hroot i) _).1 h2)
    omega
  have hnd : ((Finset.range f.natDegree).val.map fun i => z ^ g ^ i).Nodup := by
    refine Multiset.Nodup.map_on (fun i hi j hj h => ?_) (Finset.range _).nodup
    rw [← Finset.mem_def, Finset.mem_range] at hi hj
    rcases lt_trichotomy i j with h1 | h1 | h1
    · exact absurd h (hinj i j h1 hj)
    · exact h1
    · exact absurd h.symm (hinj j i h1 hi)
  symm
  refine Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset hnd).2 fun w hw => ?_) ?_
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hw
    simpa [rootsBar, hf.ne_zero, aeval_def, eval_map] using hroot i
  · have := card_roots' (f.map (algebraMap (ZMod g) (Fbar g)))
    simpa [rootsBar] using this

end GlobalTheory.GreenExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharUnramifiedAwayFromEll
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.CycUnram

theorem main : ∀ (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)), v ∉ placesOver D.host.E (D.nd.l i) → ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), epsU D.nd i γ = 1 ∧ ∀ c, 1 ≤ c → c ≤ D.R.t → chiU D.nd i c γ = chiU D.nd i 1 γ := by
  intro D i v hv γ hγ
  have hl : ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by simpa [placesOver] using hv
  have h1 : cycZ D.host.E D.nd.Om (D.nd.l i) γ = 1 := by
    refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [cycZ_toZModPow_eq hl (D.nd.plOm.2 v) (q := 1) (fun x hx => by simpa using hγ.2 x hx) n]
    simp
  have h2 : epsU D.nd i γ = 1 := by
    unfold epsU Glob.epsO
    rw [MonoidHom.comp_apply, h1, map_one]
  refine ⟨h2, fun c hc1 hc2 => ?_⟩
  change D.nd.chi i c γ = D.nd.chi i 1 γ
  rw [D.nd.chi_def i c hc1 hc2, MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.comp_apply, h1, map_one,
    one_zpow, mul_one]

end GlobalTheory.CycUnram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTwistCocycleCoboundaryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomic_twist_cocycle_coboundary : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ s : ℕ, Lev l s → ∀ j : ℤ, j ≠ 0 → ∀ c : GQ l → PadicComplex l, CocOn (Gj K s) (fun g y => chiC χ j g * act g y) {y | ‖y‖ ≤ 1} c → CobOn (Gj K s) (fun g y => chiC χ j g * act g y) {y | ‖y‖ ≤ 1} (fun g => (l : PadicComplex l) ^ (1 + s + padicValInt l j) * c g) := by
  first | exact @GlobalTheory.Cyc.TwistKill.pow_kills_cyclotomic_H1 | exact GlobalTheory.Cyc.TwistKill.pow_kills_cyclotomic_H1 | (intros; apply GlobalTheory.Cyc.TwistKill.pow_kills_cyclotomic_H1 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilInvariantJumpDescendsFinExtStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamFil_invariant_jump_descends_finExt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K E : FinExt l), K.1 ≤ E.1 → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) ℚ_[l]), (∀ g ∈ GK K, ∀ h ∈ GK K, M (g * h) = M g * M h) → ∀ (a : ℤ) (y : Fin d → P.R.BdR), (∀ g ∈ GK E, ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun i => P.actQdR g (y i)) = y) → (∀ i, y i ∈ (P.PD K).Fil a) → ¬ (∀ i, y i ∈ (P.PD K).Fil (a + 1)) → ∃ z : Fin d → P.R.BdR, (∀ g ∈ GK K, ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun i => P.actQdR g (z i)) = z) ∧ (∀ i, z i ∈ (P.PD K).Fil a) ∧ ¬ (∀ i, z i ∈ (P.PD K).Fil (a + 1)) := by
  first | exact @GlobalTheory.InvDescent.jump_descends | exact GlobalTheory.InvDescent.jump_descends | (intros; apply GlobalTheory.InvDescent.jump_descends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodDataStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_thetaOnBdRPlus_periodData : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime], Nonempty (ThetaL (D.loc l) (D.locA l)) := by
  first | exact @GlobalTheory.ThetaTie.nonempty_thetaL | exact GlobalTheory.ThetaTie.nonempty_thetaL | (intros; apply GlobalTheory.ThetaTie.nonempty_thetaL <;> assumption)
end

