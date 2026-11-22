import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0284
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhIUnionTrans
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0130
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0148
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0242
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0267
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0258
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0237
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0280
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicProductExtendedByZeroAssoc
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0122
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0285
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientsExplicitSumsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodCoefficients_explicit_sums : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → (∀ x : ℕ → O, ∃ a : O, ∀ n : ℕ, ∃ b : O, a - ∑ j ∈ Finset.range n, ((l : ℕ) : O) ^ j * x j = ((l : ℕ) : O) ^ n * b) ∧ (∀ a : O, (∀ n : ℕ, ∃ b : O, a = ((l : ℕ) : O) ^ n * b) → a = 0) := by
  first | exact @GlobalTheory.goodO_coeff_explicit_sums | exact GlobalTheory.goodO_coeff_explicit_sums | (intros; apply GlobalTheory.goodO_coeff_explicit_sums <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodEigSumSupComplEigSumEqTopStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodEigSum_sup_compl_eigSum_eq_top : ∀ (D : D7) (i : D.nd.Loc), ZRat D (D.nd.mu i) (D.nd.j i) → SpecPr D i → D.nd.eigSum i ↑(D.nd.Zgood i) ⊔ D.nd.eigSum i (↑(D.nd.Zgood i))ᶜ = ⊤ := by
  first | exact @GlobalTheory.EtaJoin.eigSum_good_sup_compl_eq_top | exact GlobalTheory.EtaJoin.eigSum_good_sup_compl_eq_top | (intros; apply GlobalTheory.EtaJoin.eigSum_good_sup_compl_eq_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTracePatternIdempotentExchange
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq

theorem tr_eJ_eq_tr_eJ' : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 →
    ∀ (N k s : ℕ), N = k + 2 * s + 1 → ∀ χ : Gn g N → ℂ, IsClass χ →
      tr (eJ g N k s ψ) χ = tr (eJ' g N k ψ) χ := by
  intro g _ ψ hψ N k s hN χ hχ
  have key : ∀ i, i ≤ s →
      tr (GlobalTheory.GLm.ePat g N (GlobalTheory.GLm.phI k s i) (GlobalTheory.GLm.eeI k s) ψ) χ = tr (eJ' g N k ψ) χ := by
    intro i
    induction i with
    | zero => intro _; exact GlobalTheory.GLm.FirstPattern.tr_first_pattern g ψ N k s hN χ hχ
    | succ n ih =>
      intro hn
      rw [GlobalTheory.RootExch.step g ψ hψ N k s (n + 1) hN (by omega) hn χ hχ]
      exact ih (by omega)
  rw [← GlobalTheory.GLm.ePat_last_eq_eJ g ψ N k s hN]
  exact key s le_rfl

end GlobalTheory.GLq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H0TwDualEqZero
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.LocTwoOnto

theorem H0_twDual_eq_zero {R Γ M : Type} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M]
    (μ : Γ →* Rˣ) (ρ : Representation R Γ M)
    (hc : ∀ φ : M →+ R, (∀ g h m, φ (ρ g (ρ h m)) = φ (ρ h (ρ g m))) → φ = 0)
    (y : H0 (twDual μ ρ)) : y = 0 := by
  obtain ⟨φ, hφ⟩ := y
  have hfix : ∀ g, twDual μ ρ g φ = φ := hφ
  let f : M →ₗ[R] R := φ

  have hmul : ∀ g m, f (ρ g m) = ((μ g : Rˣ) : R) * f m := by
    intro g m
    have h := congrArg (fun ψ : TDual R M => ψ (ρ g m)) (hfix g)
    simp only [twDual_apply, Representation.inv_self_apply] at h
    exact h.symm

  have hzero : f.toAddMonoidHom = 0 :=
    hc _ fun g h m => by
      simp only [LinearMap.toAddMonoidHom_coe, hmul]
      ring
  apply Subtype.ext
  apply TDual.ext
  intro m
  have hm := congrArg (fun k : M →+ R => k m) hzero
  simp only [LinearMap.toAddMonoidHom_coe, AddMonoidHom.zero_apply] at hm
  exact hm

theorem loc2_surjective : PoitouTateTotallyComplex → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (Λ M : Type) [CommRing Λ] [AddCommGroup M] [Module Λ M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (ρ : Representation Λ (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), (∀ m : M, l • m = 0) → ContainsAbove S l → (∀ v, IsPlaceOver (Av v) v.1) → ContAction ρ → (∀ (C : Type) [AddCommGroup C] (φ : M →+ C), (∀ g h m, φ (ρ g (ρ h m)) = φ (ρ h (ρ g m))) → φ = 0) → ∀ x : ∀ v : S, H2 (ρ.comp (locFam S Av v)), ∃ y : H2 ρ, ∀ v, resH2 ρ (locFam S Av v) (continuous_locFam S Av v) y = x v := by
  intro hPT F Ω _ _ _ _ _ _ l _ Λ M _ _ _ _ _ _ S Av ρ hl hS hAv hρ hcomm x
  have hl0 : 0 < l ^ 1 := pow_pos (Fact.out : l.Prime).pos 1
  have : NeZero (l ^ (1 : ℕ)) := ⟨hl0.ne'⟩

  have hl1 : ∀ m : M, (l ^ (1 : ℕ)) • m = 0 := fun m => by rw [pow_one]; exact hl m
  have instZ : Module (ZMod (l ^ (1 : ℕ))) M := AddCommGroup.zmodModule hl1
  have : ContinuousConstSMul (ZMod (l ^ (1 : ℕ))) M := ⟨fun _ => continuous_of_discreteTopology⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective

  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (l ^ (1 : ℕ)) Ω)
    (Polynomial.degree_cyclotomic_pos _ _ hl0).ne'
  have hζ' : IsPrimitiveRoot ζ (l ^ (1 : ℕ)) := (Polynomial.isRoot_cyclotomic_iff_charZero hl0).1 hζ
  obtain ⟨inv, -, hall⟩ := hPT F Ω l 1 one_pos ζ hζ'
  obtain ⟨μ, hμ⟩ := PoitouTate.exists_lift_cycMod (Ω := Ω) (r := 1) hS

  let ρ' : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* Module.End (ZMod (l ^ (1 : ℕ))) M :=
    { toFun := fun g => (ρ g).toAddMonoidHom.toZModLinearMap (l ^ (1 : ℕ))
      map_one' := by ext m; simp
      map_mul' := fun g h => by ext m; simp }
  have hρ' : ContAction ρ' := hρ
  obtain ⟨hNT, -⟩ := hall S hS Av hAv μ hμ M ρ' hρ'
  have hc' : ∀ φ : M →+ ZMod (l ^ (1 : ℕ)), (∀ g h m, φ (ρ' g (ρ' h m)) = φ (ρ' h (ρ' g m))) → φ = 0 :=
    fun φ hφ => hcomm (ZMod (l ^ (1 : ℕ))) φ hφ

  choose z hz using fun v => Submodule.Quotient.mk_surjective _ (x v)
  let z' : ∀ v : S, Z2 (ρ'.comp (locFam S Av v)) := fun v => ⟨(z v).1, (z v).2⟩

  obtain ⟨y', hy'⟩ := LinearMap.mem_range.1
    ((hNT.mem_range_localization_H2_iff (fun v => Submodule.Quotient.mk (z' v))).2 fun y => by
      rw [H0_twDual_eq_zero μ ρ' hc' y]
      simp)
  obtain ⟨w', hw'⟩ := Submodule.Quotient.mk_surjective _ y'
  let w : Z2 ρ := ⟨w'.1, w'.2⟩
  refine ⟨Submodule.Quotient.mk w, fun v => ?_⟩
  have hv := congrFun hy' v
  rw [← hw'] at hv
  change resH2 ρ' (locFam S Av v) (continuous_locFam S Av v) (Submodule.Quotient.mk w') =
    Submodule.Quotient.mk (z' v) at hv
  rw [resH2, Submodule.mapQ_apply, Submodule.Quotient.eq] at hv
  rw [← hz v, resH2, Submodule.mapQ_apply, Submodule.Quotient.eq]
  simp only [Submodule.mem_comap, Submodule.coe_subtype] at hv ⊢

  obtain ⟨c, hc, hcd⟩ := (separated_dvr_second_cohomology_mem _ _).1 hv
  refine (separated_dvr_second_cohomology_mem _ _).2 ⟨c, hc, ?_⟩
  funext p
  have hp := congrFun hcd p
  exact hp

end GlobalTheory.LocTwoOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1LatticeIndexGrowth
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.EulerLevel

theorem card_H2_eq (N : ℕ) [NeZero N] (G : Type) [Group G] [TopologicalSpace G]
    (M : Type) [AddCommGroup M] [Module (ZMod N) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (χ : G →* (ZMod N)ˣ) (rho : Representation (ZMod N) G M)
    (e : ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep χ) ≃ₗ[ZMod N] ZMod N)
    (hb : Function.Bijective (ReciprocityTheory.Gal.cup20 χ rho (MonoidHom.id _))) :
    Nat.card (ReciprocityTheory.Gal.H2 rho) = Nat.card (ReciprocityTheory.Gal.H0 (ReciprocityTheory.Gal.twDual χ rho)) := by
  have hT := GlobalTheory.CocycleCount.card_linear_le N M
  have hTf : Finite (ReciprocityTheory.Gal.TDual (ZMod N) M) := hT.1
  let A : Type := ReciprocityTheory.Gal.H0 ((ReciprocityTheory.Gal.twDual χ rho).comp (MonoidHom.id G))
  let E : ReciprocityTheory.Gal.H2 rho ≃ (A →ₗ[ZMod N] ZMod N) :=
    (Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight e).toEquiv
  have hA : Finite A := Subtype.finite
  rw [Nat.card_congr E]
  exact GlobalTheory.ZModDual.card_dual_eq N A

set_option maxHeartbeats 1600000 in

theorem core_pos (hT : Formalism.GaloisCohomology.LocalTateDualityK) (hE : Formalism.GaloisCohomology.LocalEulerCharK) (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (hG : GoodO (Qp := ℚ_[l]) LL O) (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL) (hm : IsDualLat1 (P.PD K) LA LA' m) (r : ℕ) (hr : 0 < r) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T))
    (M : Type) [AddCommGroup M] (tM : TopologicalSpace M) (dM : @DiscreteTopology M tM) (e : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) ≃+ M) :
    Nat.card (QuotientCohomology LA _ hI) = Nat.card {x : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) // ∀ g, actQ LA _ hI g x = x} * Nat.card {x : (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) // ∀ g, actQ LA' _ hI' g x = x} * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * (finrank ℚ_[l] ↥K.1 * finrank LL A.V)) := by
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hp : l.Prime := Fact.out
  obtain ⟨-, -, hfinO, -⟩ := GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG
  have hcO : Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ≠ 0 := by
    have := hfinO 1
    rw [pow_one] at this
    exact Nat.card_pos.ne'
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcM : Nat.card M = Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL A.V) := by
    rw [← Nat.card_congr e.toEquiv]
    exact GlobalTheory.T.card_lattice_quot_prime_pow l _ LL O hG A LA r
  have hcM' : Nat.card (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) =
      Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL A.V) := by
    rw [GlobalTheory.T.card_lattice_quot_prime_pow l _ LL O hG A' LA' r, ← hm.1.2.2.2]
  haveI : Finite M := Nat.finite_of_card_ne_zero (by rw [hcM]; exact pow_ne_zero _ hcO)
  have htor : ∀ x : M, l ^ r • x = 0 := by
    intro x
    rw [← e.apply_symm_apply x, ← map_nsmul]
    generalize e.symm x = y
    induction y using Submodule.Quotient.induction_on with
    | H t =>
      rw [← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero _).2, map_zero]
      rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  haveI instM : Module (ZMod (l ^ r)) M := AddCommGroup.zmodModule htor
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  have hφ1 : φ.symm 1 = 1 := map_one _
  have hφm : ∀ g h, φ.symm (g * h) = φ.symm g * φ.symm h := map_mul _
  have hact1 : ∀ x : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), actQ LA _ hI 1 x = x := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H t =>
      exact congrArg Submodule.Quotient.mk (Subtype.ext (by
        show A.ρ 1 (t : A.V) = t
        rw [map_one]
        rfl))
  have hactm : ∀ (g h : ↥(GK K)) (x : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T))),
      actQ LA _ hI (g * h) x = actQ LA _ hI g (actQ LA _ hI h x) := by
    intro g h x
    induction x using Submodule.Quotient.induction_on with
    | H t =>
      exact congrArg Submodule.Quotient.mk (Subtype.ext (by
        show A.ρ (g * h) (t : A.V) = A.ρ g (A.ρ h t)
        rw [map_mul]
        rfl))
  have hex : ∃ rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K.1) M,
      ∀ (g : Formalism.GaloisCohomology.GK l K.1) (x : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T))), rho g (e x) = e (actQ LA _ hI (φ.symm g) x) :=
    ⟨GlobalTheory.CocycleCount.repOfAction _
      (fun g => e.toAddMonoidHom.comp ((actQ LA _ hI (φ.symm g)).toAddMonoidHom.comp e.symm.toAddMonoidHom))
      (fun x => by
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
          AddEquiv.coe_toAddMonoidHom, hφ1, hact1, AddEquiv.apply_symm_apply])
      (fun g h x => by
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
          AddEquiv.coe_toAddMonoidHom, hφm, hactm, AddEquiv.symm_apply_apply]),
      fun g x => congrArg (fun y => e (actQ LA _ hI (φ.symm g) y)) (e.symm_apply_apply x)⟩
  obtain ⟨rho, hcomp⟩ := hex
  have hrho : ReciprocityTheory.Gal.ContAction rho := by
    refine continuous_prod_of_discrete_right.2 fun x => ?_
    have hx : (fun g => rho g x) = fun g => e (actQ LA _ hI (φ.symm g) (e.symm x)) := by
      funext g
      rw [← hcomp, e.apply_symm_apply]
    rw [hx]
    exact ((GlobalTheory.T.lattice_modPow_action_isLocallyConstant l ↥(GK K) LL O hG A LA r hI (e.symm x)).comp e).continuous.comp hφ.2
  have hT1 := hT l K.1 hK r M rho hr hrho
  obtain ⟨⟨eH⟩, -, -, -, hb⟩ := hT1
  have hEu := hE l K.1 hK r M rho hr hrho
  have hTr := GlobalTheory.T.card_H1_H0_transport_lattice l K LL O A LA _ hI (l ^ r) M e rho hcomp
  obtain ⟨h1Q, h0Q⟩ := hTr
  have hTDfin : Finite (ReciprocityTheory.Gal.TDual (ZMod (l ^ r)) M) :=
    (GlobalTheory.CocycleCount.card_linear_le (l ^ r) M).1
  have hH2 := card_H2_eq (l ^ r) _ M _ rho eH hb
  have hD := GlobalTheory.T.exists_trace_form_integral_iff_goodCoeff l LL O hG
  obtain ⟨lam, hlam⟩ := hD
  have hMp := GlobalTheory.T.tracePairing_injective_equivariant_levelMap l P K LL O A A' LA LA' m hm lam hlam r hI hI' (GlobalTheory.T.periodCyclotomicChar_reduces_mod_prime_pow l P K r) M e rho hcomp
  obtain ⟨Ψ, hΨi, hΨe⟩ := hMp
  have hcD : Nat.card (ReciprocityTheory.Gal.TDual (ZMod (l ^ r)) M) = Nat.card M :=
    GlobalTheory.ZModDual.card_dual_eq (l ^ r) M
  have hΨb : Function.Bijective Ψ :=
    hΨi.bijective_of_nat_card_le (by rw [hcD, hcM, hcM'])
  have hfix' : Nat.card {y : (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) // ∀ g, actQ LA' _ hI' g y = y} =
      Nat.card (ReciprocityTheory.Gal.H0 (ReciprocityTheory.Gal.twDual (Formalism.GaloisCohomology.cycK l K.1 r) rho)) := by
    refine Nat.card_congr ((Equiv.ofBijective _ hΨb).subtypeEquiv fun y => ?_)
    rw [Equiv.ofBijective_apply, ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere]
    constructor
    · intro hy g
      exact (hΨe g y).symm.trans (congrArg Ψ (hy _))
    · intro hy g
      have h := hΨe (φ g) y
      have h2 : (IntermediateField.fixingSubgroupEquiv K.1).symm (φ g) = g := φ.symm_apply_apply g
      rw [h2, hy (φ g)] at h
      exact hΨb.1 h
  rw [h1Q, hEu, ← h0Q, hH2, ← hfix', hcM, ← pow_mul]
  rw [show r * finrank LL A.V * finrank ℚ_[l] ↥K.1 = r * (finrank ℚ_[l] ↥K.1 * finrank LL A.V) by ring]

theorem card_H1Q_eq : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), Nat.card (QuotientCohomology LA _ hI) = Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} * Nat.card {x : ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T) // ∀ g, actQ LA' _ hI' g x = x} * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * (finrank ℚ_[l] ↥K.1 * finrank LL A.V)) := by
  intro hT hE l _ P K LL _ _ _ O _ _ hG A A' LA LA' m hm r hI hI'
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hp : l.Prime := Fact.out
  obtain ⟨-, -, hfinO, -⟩ := GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG
  have hcO : Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ≠ 0 := by
    have := hfinO 1
    rw [pow_one] at this
    exact Nat.card_pos.ne'
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hs : ∀ (X : Type) [AddCommGroup X] [Module O X],
        Subsingleton (X ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O X)) := by
      intro X _ _
      rw [Submodule.Quotient.subsingleton_iff, pow_zero, Ideal.span_singleton_one, Submodule.top_smul]
    haveI := hs ↥LA.T
    haveI := hs ↥LA'.T
    have e1 : Nat.card (QuotientCohomology LA _ hI) = 1 := by
      haveI : Subsingleton (QuotientCohomology LA _ hI) := (Submodule.Quotient.mk_surjective _).subsingleton
      exact Nat.card_unique
    have e2 : Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} = 1 := by
      haveI : Unique {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} :=
        { default := ⟨0, fun g => map_zero _⟩, uniq := fun _ => Subsingleton.elim _ _ }
      exact Nat.card_unique
    have e3 : Nat.card {x : ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O ↥LA'.T) // ∀ g, actQ LA' _ hI' g x = x} = 1 := by
      haveI : Unique {x : ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O ↥LA'.T) // ∀ g, actQ LA' _ hI' g x = x} :=
        { default := ⟨0, fun g => map_zero _⟩, uniq := fun _ => Subsingleton.elim _ _ }
      exact Nat.card_unique
    simp only [e1, e2, e3]
    simp
  · exact core_pos hT hE l P K LL O hG A A' LA LA' m hm r hr hI hI' _ ⊥ (@DiscreteTopology.mk _ ⊥ rfl) (AddEquiv.refl _)

end GlobalTheory.EulerLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1LatticeRankGrowthStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H1_lattice_rank_growth_of_goodO : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), Module.Finite O (LatticeCohomology LA) → Module.Finite LL (H1V A.ρ) ∧ ∃ C : ℕ, 0 < C ∧ ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL (H1V A.ρ)) ≤ Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ∧ Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ≤ C * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL (H1V A.ρ)) := by
  first | exact @GlobalTheory.H1Rank.growth_H1T_dim_H1V | exact GlobalTheory.H1Rank.growth_H1T_dim_H1V | (intros; apply GlobalTheory.H1Rank.growth_H1T_dim_H1V <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionExteriorProductAssocComm
section
noncomputable section

namespace GlobalTheory.GLq.HcRing

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem toG_val {n : ℕ} (x : Gn g n) : toG (x : Mt g n) = x := by
  unfold toG
  rw [dif_pos x.isUnit]
  exact Units.ext rfl

theorem br_zero {a : ℕ} (M : Mt g a) : br 0 a M = M := by
  funext i j
  simp only [br, entN, zero_add, i.isLt, j.isLt, and_self, dif_pos]

theorem tl_self {a : ℕ} (M : Mt g a) : tl a M = M := by
  funext i j
  simp only [tl, entN, i.isLt, j.isLt, and_self, dif_pos]

theorem inPar_zero {n : ℕ} (M : Mt g n) : InPar 0 M := fun _ _ hj _ => absurd hj (Nat.not_lt_zero _)

theorem inPar_self {a : ℕ} (M : Mt g a) : InPar a M := fun i _ _ hi => absurd i.isLt (not_lt.2 hi)

theorem class_conj {G : Type} [Group G] {χ : G → ℂ} (h : IsClass χ) (x y : G) : χ (y⁻¹ * x * y) = χ x := by
  have := h x y⁻¹
  rwa [inv_inv] at this

theorem mean_class {G : Type} [Group G] [Fintype G] {χ : G → ℂ} (h : IsClass χ) (x : G) :
    (Fintype.card G : ℂ)⁻¹ * ∑ y : G, χ (y⁻¹ * x * y) = χ x := by
  simp only [class_conj h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

theorem hc_one_left (a : ℕ) (α : Gn g a → ℂ) (hα : IsClass α) : hc 0 a (fun _ => 1) α a = α := by
  funext x
  unfold hc hcT
  simp only [inPar_zero, if_true, one_mul,
    br_zero, toG_val]
  rw [Finset.filter_true_of_mem (fun _ _ => trivial), Finset.card_univ]
  exact mean_class hα x

theorem hc_one_right (a : ℕ) (α : Gn g a → ℂ) (hα : IsClass α) : hc a 0 α (fun _ => 1) a = α := by
  funext x
  unfold hc hcT
  simp only [inPar_self, if_true, mul_one,
    tl_self, toG_val]
  rw [Finset.filter_true_of_mem (fun _ _ => trivial), Finset.card_univ]
  exact mean_class hα x

theorem main : ∀ (g : ℕ) [Fact g.Prime] (a b c n : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) (γ : Gn g c → ℂ),
    IsClass α → IsClass β → IsClass γ →
      (n = a + b + c → hc (a + b) c (hc a b α β (a + b)) γ n = hc a (b + c) α (hc b c β γ (b + c)) n) ∧
      (n = a + b → hc a b α β n = hc b a β α n) ∧
      (hc 0 a (fun _ => 1) α a = α ∧ hc a 0 α (fun _ => 1) a = α) :=
  fun g _ a b c n α β γ hα hβ hγ =>
    ⟨GlobalTheory.GLm.HcAssoc.hc_assoc g a b c n α β γ hα hβ hγ, GlobalTheory.HCComm.main g a b n α β hα hβ,
      hc_one_left a α hα, hc_one_right a α hα⟩

end GlobalTheory.GLq.HcRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HighPowCoeffMemSpanPowStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_mul_coeff_mem_span_coeff_zero_pow : ∀ {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p] (x : WittVector p R) (N m : ℕ), ∃ k : ℕ, ∀ (z : WittVector p R) (n : ℕ), n < N → (x ^ k * z).coeff n ∈ Ideal.span {x.coeff 0 ^ m} := by
  first | exact @GlobalTheory.WittHighPow.high_pow_coeff_mem_span_pow | exact GlobalTheory.WittHighPow.high_pow_coeff_mem_span_pow | (intros; apply GlobalTheory.WittHighPow.high_pow_coeff_mem_span_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdeleLogAbsoluteValueEqLogIdeleModule
section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.IdeleLogNormCompare

open GroundTheory.Global GroundTheory.Global.IdeleGroup GlobalTheory.Mem.Chr.CharModel

variable (E : Type) [Field E] [NumberField E]

theorem ord_eq_ord_vw (d : (AdeleRing (𝓞 E) E)ˣ) (v : HeightOneSpectrum (𝓞 E)) :
    GroundTheory.Global.IdeleGroup.ord v d = GlobalTheory.Idele.ord_vw (finPart E d) v := rfl

theorem logInf_eq (d : (AdeleRing (𝓞 E) E)ˣ) :
    logInf E (infPart E d) = Real.log (infiniteModule d) := by
  rw [infiniteModule, Real.log_prod]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [Real.log_pow]
    rfl
  · intro w _
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (infinite_ne_zero d w))

theorem logFin_eq (d : (AdeleRing (𝓞 E) E)ˣ) :
    logFin E (finPart E d) = -Real.log (finiteModule d) := by
  classical
  have hfin := Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero (finPart E d))
  let S := hfin.toFinset
  have hS : ∀ v, v ∉ S → GlobalTheory.Idele.ord_vw (finPart E d) v = 0 := by
    intro v hv
    by_contra h
    exact hv (hfin.mem_toFinset.2 h)
  have hI : GlobalTheory.Idele.idealOf (finPart E d) =
      ∏ v ∈ S, (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ GlobalTheory.Idele.ord_vw (finPart E d) v := by
    unfold GlobalTheory.Idele.idealOf
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra h
    exact hv (by show (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ GlobalTheory.Idele.ord_vw (finPart E d) v = 1
                 rw [hS v h, zpow_zero])
  have hM : finiteModule d = ∏ v ∈ S, ‖(d : AdeleRing (𝓞 E) E).2 v‖ := by
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra h
    refine hv ?_
    change ‖(d : AdeleRing (𝓞 E) E).2 v‖ = 1
    rw [norm_finite_eq_rpow, ord_eq_ord_vw, hS v h, Int.cast_zero, neg_zero, Real.rpow_zero]
  have hN : ∀ v : HeightOneSpectrum (𝓞 E), (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
    fun v => (absNorm_asIdeal_pos v).ne'
  rw [logFin, hI, hM, map_prod, Rat.cast_prod, Real.log_prod, Real.log_prod, ← Finset.sum_neg_distrib]
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Rat.cast_natCast, Real.log_zpow,
      norm_finite_eq_rpow, Real.log_rpow (absNorm_asIdeal_pos v), ord_eq_ord_vw]
    ring
  · intro v _
    exact norm_ne_zero_iff.2 (finite_ne_zero d v)
  · intro v _
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Rat.cast_natCast]
    exact zpow_ne_zero _ (hN v)

theorem logNorm_eq_log_ideleModule (d : (AdeleRing (𝓞 E) E)ˣ) :
    logNorm E d = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E d : ℝ) := by
  rw [logNorm, logInf_eq, logFin_eq, ideleModule_apply,
    Real.log_mul (infiniteModule_pos d).ne' (finiteModule_pos d).ne']
  ring

end GlobalTheory.IdeleLogNormCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCocyclesCharBlockOtherTypePrimeStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaCocycles_charBlock_otherTypePrime : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ v ∈ D.nd.S i, PolyAt i r Xs π v → ∀ c : Fin D.R.t, resIne i (cocChi i r S Xs c) v = ⊥ := by
  first | exact @GlobalTheory.Cut.PolyInertia.main | exact GlobalTheory.Cut.PolyInertia.main | (intros; apply GlobalTheory.Cut.PolyInertia.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFormLatticeEqSumLocalisedLatticesStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFormLattice_eq_sum_localised_lattices : ∀ (D : D7) (M : MtFam D) (T : NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl), 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → HeckeStdTw T.B → LatStable T.B j w → ∀ y : T.B.V j w, y ∈ latLoc T.B j w ↔ ∃ z : ∀ i : D.nd.Loc, TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i), (∀ i, z i ∈ D.nd.MtIn i) ∧ y = ∑ i ∈ (D.nd.locs j w).attach, T.Psi j w i.1 i.2 (z i.1) := by
  first | exact @GlobalTheory.LatSplit.main | exact GlobalTheory.LatSplit.main | (intros; apply GlobalTheory.LatSplit.main <;> assumption)
end

