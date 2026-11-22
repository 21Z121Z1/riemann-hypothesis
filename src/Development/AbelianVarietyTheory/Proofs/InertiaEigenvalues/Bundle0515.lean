import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0033
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0025
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0476
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Formalism.AdmissibleDesigns.InvariantsEqBotIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
import Formalism.SharpRestriction.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import GroundTheory.LocalFields.ConductorTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowGaloisSubOneMemTensorAcrisImage
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0483
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0486

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowRamifiedUniformizerFieldZpow
section
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.ValGroupKprime

theorem norm_Kunr (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] {c : Om l} (hc : c ∈ Kunr l a) (h0 : c ≠ 0) :
    ∃ m : ℤ, ‖c‖ = (l : ℝ) ^ m := by
  have hK : MaximalUnramifiedExtension l ≤ ReciprocityTheory.ChartRestriction.L1.kurAlg l := by
    refine IntermediateField.adjoin_le_iff.2 fun x ⟨m, hm, hlm, hx⟩ => ?_
    refine ReciprocityTheory.ChartRestriction.L1.mem_kurAlg.2
      (Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨m, hm, hlm, ?_⟩))
    rw [← map_pow, hx, map_one]
  have h1 := ReciprocityTheory.ChartRestriction.L1.mem_kurAlg.1 (hK (Kunr_le_Kur l a hc))
  obtain ⟨m, hm⟩ := ReciprocityTheory.ChartRestriction.L1.kur_val l h1 ((map_ne_zero _).2 h0)
  exact ⟨m, by rw [← hm]; exact (PadicComplex.norm_extends l c).symm⟩

theorem norm_natCast_l (l : ℕ) [Fact l.Prime] : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  have := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [Padic.norm_p] at this
  simpa using this

theorem norm_pow_field (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e)
    (y : Om l) (hy : y ∈ (ϖ.field a).1) (h0 : y ≠ 0) : ∃ j : ℤ, ‖y‖ ^ e = (l : ℝ) ^ j := by
  set π := ϖ.seq 0 with hπdef
  set E := Kunr l a with hE
  have hπ0 : π ≠ 0 := ϖ.seq_ne_zero 0

  have hy' : y ∈ IntermediateField.adjoin E {π} := by
    have h1 : (ϖ.field a).1 = (IntermediateField.adjoin E {π}).restrictScalars ℚ_[l] := by
      rw [IntermediateField.restrictScalars_adjoin_eq_sup]; rfl
    rw [h1] at hy; exact hy
  have hint : IsAlgebraic E π :=
    (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) π).tower_top.isAlgebraic
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint] at hy'

  let M : Submodule E (Om l) := Submodule.span E (Set.range fun i : Fin e => π ^ (i : ℕ))
  have hlE : (-(l : Om l)) ∈ E := E.neg_mem (IntermediateField.natCast_mem E l)
  have hpow : ∀ n, π ^ n ∈ M := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < e
      · exact Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hn)
        have hk : k < e + k := by have := NeZero.pos e; omega
        have h2 : π ^ (e + k) = (⟨-(l : Om l), hlE⟩ : E) • π ^ k := by
          rw [pow_add, ϖ.seq_zero]; rfl
        rw [h2]; exact M.smul_mem _ (ih k hk)
  have hyM : y ∈ M := by
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy'
    obtain ⟨p, rfl⟩ := hy'
    show Polynomial.aeval π p ∈ M
    rw [Polynomial.aeval_eq_sum_range]
    exact Submodule.sum_mem _ fun i _ => M.smul_mem _ (hpow i)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hyM
  set t : Fin e → Om l := fun i => (c i : Om l) * π ^ (i : ℕ) with ht
  have hyt : y = ∑ i, t i := by rw [← hc]; rfl

  have hnπ : ‖π‖ ^ e = (l : ℝ)⁻¹ := by
    rw [← norm_pow, ϖ.seq_zero, norm_neg, norm_natCast_l]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith

  have hnt : ∀ i, t i ≠ 0 → ∃ m : ℤ, ‖t i‖ ^ e = (l : ℝ) ^ ((e : ℤ) * m - (i : ℕ)) := by
    intro i hi
    have hci : (c i : Om l) ≠ 0 := fun h => hi (by simp [ht, h])
    obtain ⟨m, hm⟩ := norm_Kunr l a (c i).2 hci
    refine ⟨m, ?_⟩
    rw [ht]; dsimp only
    rw [norm_mul, norm_pow, mul_pow, hm, ← pow_mul, mul_comm (i : ℕ) e, pow_mul, hnπ,
      zpow_sub₀ hl0.ne', inv_pow, ← zpow_natCast, ← _root_.zpow_mul, mul_comm m, zpow_natCast, div_eq_mul_inv]

  have hdist : ∀ i j, t i ≠ 0 → t j ≠ 0 → ‖t i‖ = ‖t j‖ → i = j := by
    intro i j hi hj hij
    obtain ⟨m1, h1⟩ := hnt i hi
    obtain ⟨m2, h2⟩ := hnt j hj
    have h3 : (e : ℤ) * m1 - (i : ℕ) = (e : ℤ) * m2 - (j : ℕ) :=
      zpow_right_injective₀ hl0 hl1.ne' (show (l : ℝ) ^ _ = (l : ℝ) ^ _ by rw [← h1, ← h2, hij])
    have h4 : ((i : ℕ) : ℤ) - (j : ℕ) = 0 := by
      have hi' := i.2
      have hj' := j.2
      refine Int.eq_zero_of_abs_lt_dvd (m := (e : ℤ)) ⟨m1 - m2, by linear_combination -h3⟩ ?_
      rw [abs_lt]; constructor <;> omega
    exact Fin.ext (by omega)

  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun i => ‖t i‖)
    (Finset.univ_nonempty_iff.2 ⟨⟨0, NeZero.pos e⟩⟩)
  have ht0 : t i0 ≠ 0 := by
    intro h
    apply h0
    rw [hyt]
    refine Finset.sum_eq_zero fun i _ => norm_eq_zero.1 (le_antisymm ?_ (norm_nonneg _))
    simpa [h] using hi0 i (Finset.mem_univ _)
  have hpos : 0 < ‖t i0‖ := norm_pos_iff.2 ht0
  have hrest : ‖∑ i ∈ Finset.univ.erase i0, t i‖ < ‖t i0‖ := by
    obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finset_sum_le (Finset.univ.erase i0) t
    rcases (Finset.univ.erase i0).eq_empty_or_nonempty with hs | hs
    · rw [hs, Finset.sum_empty, norm_zero]; exact hpos
    have him := hi hs
    refine lt_of_le_of_lt hle ?_
    by_cases hti : t i = 0
    · rw [hti, norm_zero]; exact hpos
    refine lt_of_le_of_ne (hi0 i (Finset.mem_univ _)) fun h => ?_
    exact (Finset.mem_erase.1 him).1 (hdist i i0 hti ht0 h)
  have hy2 : ‖y‖ = ‖t i0‖ := by
    rw [hyt, ← Finset.add_sum_erase _ _ (Finset.mem_univ i0),
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hrest.ne', max_eq_left hrest.le]
  obtain ⟨m, hm⟩ := hnt i0 ht0
  exact ⟨_, by rw [hy2, hm]⟩

end GlobalTheory.ValGroupKprime
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneTmulBcrisGaloisLatticeInjectiveStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_tmul_bcris_galoisLattice_injective : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL), Function.Injective (fun x : ↥T.L.T => (1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) := by
  first | exact @GlobalTheory.TContInj.main | exact GlobalTheory.TContInj.main | (intros; apply GlobalTheory.TContInj.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicHodgePropertiesConjInvariant
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
  GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf
open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module

namespace GlobalTheory.ConjLocal

section DdR

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} (e : V ≃ₗ[LL] V')
    (he : ∀ g x, e (ρ g x) = ρ' g (e x))
include he

theorem finrank_DdR_congr : finrank LL ↥(DdR PD ρ) = finrank LL ↥(DdR PD ρ') := by
  let E : V ⊗[Qp] BdR ≃ₗ[LL] V' ⊗[Qp] BdR := AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)
  have hE : ∀ g x, E (actVdR PD ρ g x) = actVdR PD ρ' g (E x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [E, actVdR, he]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  have hD : DdR PD ρ = (DdR PD ρ').comap (E : V ⊗[Qp] BdR →ₗ[LL] V' ⊗[Qp] BdR) := by
    ext x
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, Submodule.mem_comap, sub_eq_zero]
    constructor
    · intro hx g
      rw [LinearEquiv.coe_coe, ← hE, hx g]
    · intro hx g
      apply E.injective
      rw [hE]
      exact hx g
  rw [hD]
  exact (E.ofSubmodule' (DdR PD ρ')).finrank_eq

end DdR

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {a : ℕ}

theorem exists_ext_entries (L₁ : FinExt l) (A : GL (Fin a) (Om l)) :
    ∃ L₂ : FinExt l, L₁.1 ≤ L₂.1 ∧ (∀ i j, (A : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L₂.1) ∧
      ∀ i j, ((A⁻¹ : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L₂.1 := by
  let f : Bool × Fin a × Fin a → Om l := fun p => if p.1 then (A : Matrix (Fin a) (Fin a) (Om l)) p.2.1 p.2.2
    else ((A⁻¹ : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) p.2.1 p.2.2
  have hfin : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range f)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨supExt L₁ ⟨_, hfin⟩, le_sup_left, fun i j => ?_, fun i j => ?_⟩
  · exact (le_sup_right : IntermediateField.adjoin ℚ_[l] (Set.range f) ≤ L₁.1 ⊔ _)
      (IntermediateField.subset_adjoin _ _ ⟨(true, i, j), rfl⟩)
  · exact (le_sup_right : IntermediateField.adjoin ℚ_[l] (Set.range f) ≤ L₁.1 ⊔ _)
      (IntermediateField.subset_adjoin _ _ ⟨(false, i, j), rfl⟩)

theorem repE_apply (L : FinExt l) (r : ↥Gw →* GL (Fin a) ↥L.1) (g : ↥(GK Bw.Kw)) (x : Fin a → ↥L.1) :
    Bw.repE L r g x = ((r (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1).mulVec x := by
  simp [LocBridge.repE, Matrix.toLinAlgEquiv'_apply]

variable {Bw} in

theorem exists_conj_model {r r' : ↥Gw →* GL (Fin a) (Om l)} (A : GL (Fin a) (Om l))
    (hc : ∀ g, r' g = A * r g * A⁻¹) {L₁ : FinExt l} {r₁ : ↥Gw →* GL (Fin a) ↥L₁.1}
    (h₁ : IsModel Bw r L₁ r₁) :
    ∃ (L₂ : FinExt l) (hL : L₁.1 ≤ L₂.1) (r₂ : ↥Gw →* GL (Fin a) ↥L₂.1), IsModel Bw r' L₂ r₂ ∧
      ∃ e : (Fin a → ↥L₂.1) ≃ₗ[↥L₂.1] (Fin a → ↥L₂.1), ∀ g x,
        e (Bw.repE L₂ (Formalism.MainNotions.N.mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x) =
          Bw.repE L₂ r₂ g (e x) := by
  obtain ⟨L₂, hL, hA, hB⟩ := exists_ext_entries L₁ A
  let A₂ : Matrix (Fin a) (Fin a) ↥L₂.1 := fun i j => ⟨_, hA i j⟩
  let B₂ : Matrix (Fin a) (Fin a) ↥L₂.1 := fun i j => ⟨_, hB i j⟩
  let f : ↥L₂.1 →+* Om l := algebraMap ↥L₂.1 (Om l)
  have fA : f.mapMatrix A₂ = (A : Matrix (Fin a) (Fin a) (Om l)) := rfl
  have fB : f.mapMatrix B₂ = ((A⁻¹ : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) := rfl
  have inj : Function.Injective (f.mapMatrix : Matrix (Fin a) (Fin a) ↥L₂.1 → Matrix (Fin a) (Fin a) (Om l)) :=
    Matrix.map_injective Subtype.val_injective
  have h1 : A₂ * B₂ = 1 := inj (by rw [map_mul, map_one, fA, fB, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have h2 : B₂ * A₂ = 1 := inj (by rw [map_mul, map_one, fA, fB, ← Units.val_mul, inv_mul_cancel, Units.val_one])
  let U : GL (Fin a) ↥L₂.1 := ⟨A₂, B₂, h1, h2⟩
  refine ⟨L₂, hL, (MulAut.conj U).toMonoidHom.comp
    (Formalism.MainNotions.N.mapRep (IntermediateField.inclusion hL).toRingHom r₁), ?_, ?_⟩
  · refine ⟨h₁.1.trans hL, ?_⟩
    ext g i j
    rw [hc g, ← h₁.2]
    change (f.mapMatrix (A₂ * ((IntermediateField.inclusion hL).toRingHom.mapMatrix
        ((r₁ g : GL (Fin a) ↥L₁.1) : Matrix (Fin a) (Fin a) ↥L₁.1)) * B₂)) i j =
      ((A : Matrix (Fin a) (Fin a) (Om l)) * (algebraMap ↥L₁.1 (Om l)).mapMatrix
        ((r₁ g : GL (Fin a) ↥L₁.1) : Matrix (Fin a) (Fin a) ↥L₁.1) *
        ((A⁻¹ : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) i j
    rw [map_mul, map_mul, fA, fB]
    rfl
  · refine ⟨Formalism.MainNotions.N.K.Norm.matEquiv A₂ B₂ h1 h2, fun g x => ?_⟩
    rw [Formalism.MainNotions.N.K.Norm.matEquiv_apply, Formalism.MainNotions.N.K.Norm.matEquiv_apply, repE_apply, repE_apply]
    change A₂.mulVec (Matrix.mulVec _ x) = Matrix.mulVec (A₂ * _ * B₂) (A₂.mulVec x)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem local_conj : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Gw : Subgroup (Ω ≃ₐ[E] Ω))
    (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r r' : ↥Gw →* GL (Fin a) (Om l)) (A : GL (Fin a) (Om l)),
    (∀ g, r' g = A * r g * A⁻¹) → (IsdRAt P Bw r → IsdRAt P Bw r') ∧ (IsCrysAt P Bw r → IsCrysAt P Bw r') ∧
      (IsPotCrysAt P Bw r → IsPotCrysAt P Bw r') ∧
      ∀ (τ : E →+* Om l) (J : Multiset ℤ), IsJumpsAt P Bw r τ J → IsJumpsAt P Bw r' τ J := by
  intro l _ P E Ω _ _ _ _ O _ _ _ Gw Bw a r r' A hc
  have dR : ∀ {L₁ L₂ : FinExt l} {r₁ : ↥Gw →* GL (Fin a) ↥L₁.1} (hL : L₁.1 ≤ L₂.1)
      (r₂ : ↥Gw →* GL (Fin a) ↥L₂.1) (e : (Fin a → ↥L₂.1) ≃ₗ[↥L₂.1] (Fin a → ↥L₂.1)),
      (∀ g x, e (Bw.repE L₂ (Formalism.MainNotions.N.mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x) =
          Bw.repE L₂ r₂ g (e x)) → Bw.IsdRE P L₁ r₁ → Bw.IsdRE P L₂ r₂ := by
    intro L₁ L₂ r₁ hL r₂ e he hd
    have h := (local_ext P Bw hL r₁).2.1.2 hd
    unfold LocBridge.IsdRE at h ⊢
    rw [← finrank_DdR_congr (P.PD Bw.Kw) e he, h]
  refine ⟨fun ⟨L₁, r₁, h₁, hd⟩ => ?_, fun ⟨L₁, r₁, h₁, hd⟩ => ?_, fun ⟨L₁, r₁, h₁, hd⟩ => ?_,
    fun τ J ⟨L₁, r₁, h₁, hd, τ₁, hτ, hJ⟩ => ?_⟩
  · obtain ⟨L₂, hL, r₂, hm, e, he⟩ := exists_conj_model A hc h₁
    exact ⟨L₂, r₂, hm, dR hL r₂ e he hd⟩
  · obtain ⟨L₂, hL, r₂, hm, e, he⟩ := exists_conj_model A hc h₁
    exact ⟨L₂, r₂, hm, Formalism.MainNotions.N.K.Norm.isCrys_congr (P.PD Bw.Kw) e he ((local_ext P Bw hL r₁).1.2 hd)⟩
  · obtain ⟨L₂, hL, r₂, hm, e, he⟩ := exists_conj_model A hc h₁
    obtain ⟨K', hK, hcr⟩ := (local_ext P Bw hL r₁).2.2.1.2 hd
    exact ⟨L₂, r₂, hm, K', hK, Formalism.MainNotions.N.K.Norm.isCrys_congr (P.PD K') e (fun g x => he _ x) hcr⟩
  · obtain ⟨L₂, hL, r₂, hm, e, he⟩ := exists_conj_model A hc h₁
    refine ⟨L₂, r₂, hm, dR hL r₂ e he hd, (IntermediateField.inclusion hL).comp τ₁, fun x => hτ x, fun n => ?_⟩
    rw [hJ n, ← (local_ext P Bw hL r₁).2.2.2 τ₁ n]
    exact Formalism.MainNotions.N.K.Norm.multV_congr (P.PD Bw.Kw) e he _ n

end GlobalTheory.ConjLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiModuleHomShortExactSplitWittTiltStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phiModuleHom_shortExact_split_wittTilt_alt : ∀ {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {G : Type} [Group G] [TopologicalSpace G] {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] {P₀ : PhiMod O K l e a ι} {P₁ : PhiMod O K l e a κ} {P₂ : PhiMod O K l e a μ} {T₀ T₁ T₂ : LocLat G ℚ_[l] K O} {I₀ : Ident t ϖ P₀ T₀} {I₁ : Ident t ϖ P₁ T₁} {I₂ : Ident t ϖ P₂ T₂} {f : LatHom T₀.L T₁.L} {g : LatHom T₁.L T₂.L} {F : GlobalTheory.BK.Hom P₀ P₁} {H : GlobalTheory.BK.Hom P₁ P₂} (hS : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I₀ I₁ f F) (hH : IsMapOf I₁ I₂ g H), (∃ Z : Matrix κ μ (OW l O), (homMat t ϖ H).map (inclO l O) * Z = 1) ∧ (∃ Y : Matrix ι κ (OW l O), Y * (homMat t ϖ F).map (inclO l O) = 1) := by
  first | exact @GlobalTheory.phiModuleHom_shortExact_split_wittTilt | exact GlobalTheory.phiModuleHom_shortExact_split_wittTilt | (intros; apply GlobalTheory.phiModuleHom_shortExact_split_wittTilt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiWInclLEPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eis_pow_smul_phiW_inclL_eq_inclL_mulVec : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (α : ℕ) (Y : Matrix ι ι (OA l O)), (∀ i j, ∃ f : ZMod a → A O K, (∀ τ, (f τ : K⟦X⟧) = E K l e ^ α * P.mx τ i j) ∧ Y i j = ϖ.iTot t K f) → ∀ c : ι → OA l O, inclO l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e))) ^ α • phiW t ϖ P (inclL t ϖ P c) = inclL t ϖ P (Y.map (frobOA l O) *ᵥ fun i => frobOA l O (c i)) := by
  first | exact @GlobalTheory.BKReal.phiW_inclL_E_pow | exact GlobalTheory.BKReal.phiW_inclL_E_pow | (intros; apply GlobalTheory.BKReal.phiW_inclL_E_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolyValLeSumMulPow
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem polyVal_le_sum_mul_pow (Q : MvPolynomial (Fin 3) ℕ) (f r t : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    EmbeddingTypeJumps.polyVal Q f r t ≤ (∑ m ∈ Q.support, Q.coeff m) * (f * r * t) ^ Q.totalDegree := by
  unfold EmbeddingTypeJumps.polyVal
  rw [MvPolynomial.eval_eq', Finset.sum_mul]
  refine Finset.sum_le_sum fun m hm => ?_
  refine Nat.mul_le_mul_left _ ?_
  have hM : ∀ i : Fin 3, (![f, r, t] : Fin 3 → ℕ) i ≤ f * r * t := by
    intro i
    fin_cases i
    · show f ≤ f * r * t
      simpa using Nat.mul_le_mul (Nat.mul_le_mul (le_refl f) hr) ht
    · show r ≤ f * r * t
      simpa using Nat.mul_le_mul (Nat.mul_le_mul hf (le_refl r)) ht
    · show t ≤ f * r * t
      simpa using Nat.mul_le_mul (Nat.mul_le_mul hf hr) (le_refl t)
  have hpos : 0 < f * r * t := by positivity
  calc ∏ i, (![f, r, t] : Fin 3 → ℕ) i ^ m i ≤ ∏ i : Fin 3, (f * r * t) ^ m i :=
        Finset.prod_le_prod' fun i _ => Nat.pow_le_pow_left (hM i) _
    _ = (f * r * t) ^ (∑ i, m i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ (f * r * t) ^ Q.totalDegree := by
        apply Nat.pow_le_pow_right hpos
        have := MvPolynomial.le_totalDegree hm
        rwa [Finsupp.sum_fintype _ _ (by simp)] at this

theorem starG_of_thmB : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (ρ : FamilyRepresentationConstants.RhoFam D) (constantFirstHub C : ℝ)
    (Q : MvPolynomial (Fin 3) ℕ), FamilyRepresentationConstants.CG constantFirstHub Q ≤ C → EmbeddingTypeJumps.Conclusion2 ρ L constantFirstHub Q → KillingConditions.KillAt ρ →
    TwistedPlaces.ShaFinOdd D → StarG L ρ C := by
  intro D L P ρ constantFirstHub C Q hCG hB hK hSha
  unfold StarG
  intro i hi hl π hπ
  unfold Bd
  unfold FamilyRepresentationConstants.CG at hCG
  have hC67 : constantFirstHub ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCG
  have hS : ((∑ m ∈ Q.support, Q.coeff m : ℕ) : ℝ) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCG
  have hdeg : (Q.totalDegree : ℝ) ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCG
  have hC1 : (1 : ℝ) ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCG

  have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
  have hr1 : 1 ≤ D.R.r := by
    unfold Ranks.r
    have := D.R.m_add_three_le_k
    omega
  have hf1 : 1 ≤ D.R.f := by
    have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    omega
  have htr : 1 ≤ D.R.t * D.R.r := by simpa using Nat.mul_le_mul ht1 hr1

  have hlp : (D.nd.l i).Prime := by
    rcases hl with h | h <;> rw [h]
    exacts [D.host.hyp.1, D.host.hyp.2.1]
  have hl2 : 2 < D.nd.l i := by
    have hqd := D.host.qd_big
    rcases hl with h | h <;> rw [h] <;> nlinarith [hqd.1, hqd.2]
  have hodd : Odd (D.nd.l i) := hlp.odd_of_ne_two (by omega)
  have hlbig : L.sc.x ^ (2 * L.Ct + 5) < (D.nd.l i : ℝ) := by
    rcases hl with h | h <;> rw [h]
    exacts [P.qd_pow.1, P.qd_pow.2]
  have hsha : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤ := by
    intro e he
    rw [Finset.mem_Ioo] at he
    haveI : Fact (D.nd.l i).Prime := ⟨hlp⟩
    exact lt_top_iff_ne_top.2 (hSha (D.nd.l i) e he.1 he.2)
  have hK' := (hK i hi).1 π hπ
  have h := hB i hl hi hlbig π hπ hK'.1 hsha

  have hVV : TwistedPlaces.VVr D (D.nd.l i) =
      ((∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) := by
    show ((∑ e ∈ Finset.Ico 1 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) = _
    congr 2
  have hvh : TwistedPlaces.vhE D (D.nd.l i) = (padicValNat (D.nd.l i) (hE D.host) : ℝ) := rfl
  have heps : TwistedPlaces.epsL (D.nd.l i) = EmbeddingTypeJumps.epsL (D.nd.l i) := by
    unfold TwistedPlaces.epsL EmbeddingTypeJumps.epsL
    rw [one_div]

  have hLpos : 0 < TwistedPlaces.large₂ L := Real.rpow_pos_of_pos (by linarith [L.sc.one_lt_alt]) _
  have hlog : Real.log L.sc.b = TwistedPlaces.large₂ L := Real.log_exp _
  have hbpos : 0 < L.sc.b := Real.exp_pos _
  have hlpos : (0 : ℝ) < D.nd.l i := by exact_mod_cast hlp.pos
  have hbr : 0 ≤ (D.R.r : ℝ) * (L.sc.b / (D.nd.l i) + L.Sc + D.R.t + L.etaSz + TwistedPlaces.large₂ L) +
      D.R.m * L.sc.b := by
    have h1 := L.Sc_pos
    have h2 := L.etaSz_pos
    have h3 : 0 ≤ L.sc.b / (D.nd.l i) := div_nonneg hbpos.le hlpos.le
    have h4 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    have h5 : 0 ≤ L.sc.b / (D.nd.l i) + L.Sc + D.R.t + L.etaSz + TwistedPlaces.large₂ L := by linarith
    positivity
  have hM1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * D.R.t := by exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul hf1 hr1) ht1
  have hpoly : ((EmbeddingTypeJumps.polyVal Q D.R.f D.R.r D.R.t : ℕ) : ℝ) ≤ C * ((D.R.f : ℝ) * D.R.r * D.R.t) ^ C := by
    have h1 : ((EmbeddingTypeJumps.polyVal Q D.R.f D.R.r D.R.t : ℕ) : ℝ) ≤
        ((∑ m ∈ Q.support, Q.coeff m : ℕ) : ℝ) * ((D.R.f : ℝ) * D.R.r * D.R.t) ^ Q.totalDegree := by
      exact_mod_cast polyVal_le_sum_mul_pow Q _ _ _ hf1 hr1 ht1
    have hpow : ((D.R.f : ℝ) * D.R.r * D.R.t) ^ Q.totalDegree ≤ ((D.R.f : ℝ) * D.R.r * D.R.t) ^ C := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hM1 hdeg
    exact h1.trans (mul_le_mul hS hpow (by positivity) (by linarith))
  have hbnd : EmbeddingTypeJumps.bndB D L constantFirstHub Q (D.nd.l i) ≤ TwistedPlaces.midG L C (D.nd.l i) := by
    unfold EmbeddingTypeJumps.bndB TwistedPlaces.midG
    rw [hlog]
    have e1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC67 (Nat.cast_nonneg D.R.f)) hbr
    have e2 := mul_le_mul_of_nonneg_right hpoly hLpos.le
    linarith
  rw [hVV, hvh, heps]
  linarith

end GlobalTheory.NLink

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperRamificationGroupOfComm
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem pow_mem_upperRamificationGroup_of_comm : ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M] [FiniteDimensional F M] [IsGalois F M] (p e : ℕ) (v : ℝ), (∀ σ τ : M ≃ₐ[F] M, σ * τ = τ * σ) → 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F M v, σ ^ p ∈ upperRamificationGroup F M (min (2 * v) (v + e)) := by
  intro F M _ _ _ _ _ _ _ _ _ _ _ _ p e v hcomm hv hord σ hσ

  let f : M →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let φ : M ≃ₐ[F] f.fieldRange := f.equivFieldRange
  haveI : FiniteDimensional F f.fieldRange := LinearEquiv.finiteDimensional φ.toLinearEquiv
  haveI : IsMulCommutative (M ≃ₐ[F] M) := ⟨⟨hcomm⟩⟩
  haveI : IsAbelianGalois F M := IsAbelianGalois.mk
  haveI : IsAbelianGalois F f.fieldRange := IsAbelianGalois.of_algHom φ.symm.toAlgHom

  have h1 : φ.autCongr σ ∈ upperRamificationGroup F f.fieldRange v := by
    rw [← map_upperRamificationGroup_autCongr φ v]
    exact ⟨σ, hσ, rfl⟩
  have h2 := GlobalTheory.T.pow_mem_upperRamificationGroup_abelian_real F f.fieldRange p e v hv hord _ h1
  rw [← map_upperRamificationGroup_autCongr φ] at h2
  obtain ⟨τ, hτ, hτσ⟩ := h2
  have hτ' : τ = σ ^ p := φ.autCongr.injective (by simpa [map_pow] using hτσ)
  exact hτ' ▸ hτ

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowGaloisSubOneMemTensorAcrisImageStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_pow_galois_sub_one_mem_tensorAcris_image : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (σ : D.MMl) (c : ℕ), (l : K) ^ c • D.conn σ.1 ∈ D.MM → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ z : ι → OCr l O, (l : O) ^ c • (actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ)) - R.jB (toBcris t ϖ D.toPhiMod σ)) = R.jB fun i => toOB l O (z i) := by
  first | exact @GlobalTheory.GalTaylor.lpow_galDiff_eq_jB_toOB | exact GlobalTheory.GalTaylor.lpow_galDiff_eq_jB_toOB | (intros; apply GlobalTheory.GalTaylor.lpow_galDiff_eq_jB_toOB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiUnitOnRescaleUniformizerOfQValStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiUnitOn_rescale_uniformizer_of_qVal : ∀ (T : Formalism.L2.Pj.CDVR) (D : DegPre T.V) (ϖ : T.V), Irreducible ϖ → ∀ (y : D.X) (n : ℤ), QVal D ϖ y n → ∀ q : D.X → (FractionRing T.V)ˣ, (q y : FractionRing T.V) = algebraMap T.V (FractionRing T.V) ϖ ^ (-n) → PsiUnitOn (GlobalTheory.TauTwist.rescale D q) y Set.univ := by
  first | exact @GlobalTheory.TauTwist.psiUnitOn_rescale_of_qVal | exact GlobalTheory.TauTwist.psiUnitOn_rescale_of_qVal | (intros; apply GlobalTheory.TauTwist.psiUnitOn_rescale_of_qVal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QValPullbackMulRamificationCompleteDvrStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qVal_pullback_mul_ramification_complete_dvr : ∀ (T T' : Formalism.L2.Pj.CDVR) (g : T.V →+* T'.V) (D : DegPre T.V) (D' : DegPre T'.V) (hD : IsPullDeg g D D') (ϖ : T.V) (ϖ' : T'.V) (e : ℕ), Function.Injective g → Irreducible ϖ → Irreducible ϖ' → Associated (g ϖ) (ϖ' ^ e) → ∀ (y : D'.X) (n : ℤ), QVal D ϖ (hD.xe y) n → QVal D' ϖ' y (e * n) := by
  first | exact @GlobalTheory.QValPull.main | exact GlobalTheory.QValPull.main | (intros; apply GlobalTheory.QValPull.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentLeOfJumpsAtEmbeddingsUnramifiedStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionExponent_le_of_jumps_at_embeddings_unramified : ∀ (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hs : Good K 1 LL) (h r n : ℕ) (T : LocLat (LocalSituation.sit LT HW l (AI l) K 1 LL hs).G (LocalSituation.sit LT HW l (AI l) K 1 LL hs).Qp (LocalSituation.sit LT HW l (AI l) K 1 LL hs).LL (LocalSituation.sit LT HW l (AI l) K 1 LL hs).O), K.1 ≤ MaximalUnramifiedExtension l → finrank ℚ_[l] ↥K.1 ≤ n → 1 ≤ r → (∀ τ, ∃ U : Finset ℤ, U.card ≤ r ∧ (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) ∧ ∀ a, IsJumpV (LocalSituation.sit LT HW l (AI l) K 1 LL hs).PD T.ρ τ a → a ∈ U) → (∀ a ∈ LocalSituation.Jset (LocalSituation.sit LT HW l (AI l) K 1 LL hs) T, -(h : ℤ) ≤ a ∧ a ≤ h) ∧ GlobalTheory.HubX.invariantsCountConstant LT HW AI l K 1 LL hs h h T ≤ 5 + Nat.log l (2 * h) + n * r * (4 + 2 * Nat.log l (2 * h)) := by
  first | exact @GlobalTheory.HubX.cH0all_le_of_jumps_at_embeddings | exact GlobalTheory.HubX.cH0all_le_of_jumps_at_embeddings | (intros; apply GlobalTheory.HubX.cH0all_le_of_jumps_at_embeddings <;> assumption)
end

