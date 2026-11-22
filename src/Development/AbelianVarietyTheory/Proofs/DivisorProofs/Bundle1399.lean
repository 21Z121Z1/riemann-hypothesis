import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0008
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0584
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0583
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0817
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1372
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1386
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientSpaceEndomorphismScalarSchur
section
set_option autoImplicit false
noncomputable section
open NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MvPolynomial
open scoped Matrix

namespace GlobalTheory.CoefSchur

theorem polyAction_ten (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (h : ι → GL (Fin n) K) (f : ι → MvPolynomial (Fin n × Fin n) K) :
    actP lam h (ten f) = ten fun τ => sqAct K n (lam τ) (h τ) (f τ) := by
  have hb := (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n (fun τ => ((h τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ)).1
  simp only [actP, ten, detTwK, trAct, sqAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_prod, hb, map_smul]
  rw [Finset.prod_smul]

theorem natW_anti {n : ℕ} (lam : DomWeight n) : Antitone lam.natW := by
  intro i j hij
  have := lam.anti hij
  unfold DomWeight.natW
  omega

theorem ten_ext_mem (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    (ten fun τ => extremal K n (lam τ)) ∈ VV K lam :=
  Submodule.subset_span ⟨fun τ => extremal K n (lam τ),
    fun τ => Formalism.GradedWeylDivisibility.hwMem K n n le_rfl _ (natW_anti (lam τ)), rfl⟩

theorem endo_scalar : ∀ (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (g : Module.End K (VV K lam)),
    (∀ (h : ι → GL (Fin n) K) v, g (rhoK lam h v) = rhoK lam h (g v)) → ∃ a : K, ∀ v, g v = a • v := by
  intro K _ _ ι _ n lam g hg
  set v0 : VV K lam := ⟨_, ten_ext_mem K lam⟩ with hv0
  have hw0 := (GlobalTheory.T.weightSpace_coefficientSpace_eq_extremalTensorLine K lam).1
  have hgw := GlobalTheory.T.weylTensorCoefSpace_endomorphism_preserves_torus_weight K lam g hg v0 hw0
  obtain ⟨a, ha⟩ := (GlobalTheory.T.weightSpace_coefficientSpace_eq_extremalTensorLine K lam).2 _ (g v0).2 hgw
  have ha' : g v0 = a • v0 := Subtype.ext ha
  refine ⟨a, ?_⟩
  let W : Submodule K (Pol K ι n) := Submodule.map (VV K lam).subtype (LinearMap.ker (g - a • LinearMap.id))
  have hS : ∀ τ, nablaSq K n (lam τ) ≤ Submodule.span K (Set.range fun x : GL (Fin n) K => sqAct K n (lam τ) x (extremal K n (lam τ))) :=
    fun τ => GlobalTheory.T.dualWeylModule_le_span_extremalTranslates K n (lam τ)
  have hle := GlobalTheory.T.weylTensorCoefSpace_le_span_pure_tensors K lam _ hS
  have hW : VV K lam ≤ W := by
    refine hle.trans (Submodule.span_le.2 ?_)
    rintro P ⟨f, hf, rfl⟩
    choose h hh using hf
    have e : ten f = ten fun τ => sqAct K n (lam τ) (h τ) (extremal K n (lam τ)) := by
      congr 1; funext τ; exact (hh τ).symm
    refine ⟨rhoK lam h v0, ?_, ?_⟩
    · rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hg, ha', map_smul, sub_self]
    · rw [e, ← polyAction_ten]; rfl
  intro v
  obtain ⟨w, hw, hwv⟩ := hW v.2
  have : w = v := Subtype.ext hwv
  subst this
  simpa [sub_eq_zero] using hw

end GlobalTheory.CoefSchur
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactSetCharPolyCoeffBounded
section
noncomputable section

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

namespace GlobalTheory.LocBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_cj (w : Pl E) : Continuous (cj w) := by
  by_cases h : ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)
  · exact (GlobalTheory.ConjAtPlace.cj_spec w h).1
  · rw [GlobalTheory.ConjAtPlace.cj_of_not w h]; exact continuous_id

theorem continuous_nrmL (n : ℕ) (w : Pl E) : Continuous (nrmL n w) := by
  by_cases hs : IsSplitAt w
  · have e : nrmL n w = fun y => y := funext fun y => by simp [nrmL, hs]
    rw [e]; exact continuous_id
  · have e : nrmL n w = fun y => y * thetaGL n (cj w) y := funext fun y => by simp [nrmL, hs]
    rw [e]
    exact continuous_id.mul (GlobalTheory.ThetaPull.continuous_thetaGL (cj w) (continuous_cj w))

theorem continuous_coeff_charpoly {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem exists_bound_of_isCompact (w : Pl E) {K : Set (w.adicCompletion E)} (hK : IsCompact K) :
    ∃ m : ℕ, ∀ x ∈ K, Valued.v x ≤ WithZero.exp (m : ℤ) := by
  let U : ℕ → Set (w.adicCompletion E) := fun m => {y | Valued.v y ≤ WithZero.exp (m : ℤ)}
  have hcov : K ⊆ ⋃ m : ℕ, U m := by
    intro x _
    rcases eq_or_ne (Valued.v x) 0 with h0 | h0
    · exact Set.mem_iUnion.2 ⟨0, by simp only [U, Set.mem_setOf_eq, h0]; exact zero_le'⟩
    · refine Set.mem_iUnion.2 ⟨(WithZero.log (Valued.v x)).toNat, ?_⟩
      show Valued.v x ≤ _
      conv_lhs => rw [← WithZero.exp_log h0]
      rw [WithZero.exp_le_exp]
      omega
  have hdir : Directed (· ⊆ ·) U :=
    Monotone.directed_le fun a b hab y hy => le_trans hy (WithZero.exp_le_exp.2 (by exact_mod_cast hab))
  obtain ⟨m, hm⟩ := hK.elim_directed_cover U (fun m => GlobalTheory.PrincCong.isOpen_ball w (m : ℤ)) hcov hdir
  exact ⟨m, fun x hx => hm hx⟩

theorem bound_charpoly_nrmL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (C : Set (GLw n w)), IsCompact C →
    ∃ γ : WithZero (Multiplicative ℤ), γ ≠ 0 ∧ ∀ y ∈ C,
      (∀ i, Valued.v ((nrmL n w y).val.charpoly.coeff i) ≤ γ) ∧
        γ⁻¹ ≤ Valued.v ((nrmL n w y).val.charpoly.coeff 0) := by
  intro E _ _ _ n w C hC
  let F : Option (Fin (n + 1)) → GLw n w → w.adicCompletion E := fun o y =>
    match o with
    | none => ((nrmL n w y)⁻¹).val.det
    | some i => (nrmL n w y).val.charpoly.coeff i
  have hF : ∀ o, Continuous (F o) := by
    rintro (_ | i)
    · exact (Units.continuous_val.comp (continuous_nrmL n w).inv).matrix_det
    · exact (continuous_coeff_charpoly n i).comp (Units.continuous_val.comp (continuous_nrmL n w))
  have hK : IsCompact (⋃ o, F o '' C) := isCompact_iUnion fun o => hC.image (hF o)
  obtain ⟨m, hm⟩ := exists_bound_of_isCompact w hK
  have hb : ∀ o, ∀ y ∈ C, Valued.v (F o y) ≤ WithZero.exp (m : ℤ) := fun o y hy =>
    hm _ (Set.mem_iUnion.2 ⟨o, Set.mem_image_of_mem _ hy⟩)
  refine ⟨WithZero.exp (m : ℤ), WithZero.exp_ne_zero, fun y hy => ⟨fun i => ?_, ?_⟩⟩
  · by_cases hi : i ≤ n
    · exact hb (some ⟨i, Nat.lt_succ_of_le hi⟩) y hy
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; omega)]
      simp
  · have h1 : Valued.v (((nrmL n w y)⁻¹).val.det) ≤ WithZero.exp (m : ℤ) := hb none y hy
    have hdet : (nrmL n w y).val.det * ((nrmL n w y)⁻¹).val.det = 1 := by
      rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    have hc0 : (nrmL n w y).val.charpoly.coeff 0 = (-1) ^ n * (nrmL n w y).val.det := by
      rw [Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨n, rfl⟩,
        one_mul]
    have hv : Valued.v ((nrmL n w y).val.charpoly.coeff 0) * Valued.v (((nrmL n w y)⁻¹).val.det) = 1 := by
      rw [hc0, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul, ← map_mul, hdet, map_one]
    have hne : Valued.v (((nrmL n w y)⁻¹).val.det) ≠ 0 := fun h => by
      rw [h, mul_zero] at hv; exact zero_ne_one hv
    rw [eq_inv_of_mul_eq_one_left hv]
    exact inv_anti₀ (zero_lt_iff.2 hne) h1

end GlobalTheory.LocBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactUnipotentInCompactSubgroup
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.WhitHered Matrix GlobalTheory.InertSupp

namespace GlobalTheory.UnipCptSub

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem mem_grp_of_le {c : n → ℤ} {g : GL n k} (hg : g ∈ unipOf k c) {m M : ℕ} (hmM : m ≤ M)
    (h : g ∈ GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m)) :
    g ∈ GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c M) := by
  have key : ∀ x : GL n k, x ∈ unipOf k c → (∀ i j, GlobalTheory.IwahoriInj.Deep ((m : ℤ) * (c i - c j)) (x.val i j)) →
      ∀ i j, GlobalTheory.IwahoriInj.Deep ((M : ℤ) * (c i - c j)) (x.val i j) := by
    intro x hx hd i j
    by_cases hij : c i < c j
    · refine (hd i j).mono ?_
      have : (m : ℤ) ≤ M := by exact_mod_cast hmM
      nlinarith
    · rw [mem_unipOf.1 hx i j hij]
      by_cases e : i = j
      · subst e
        simp [GlobalTheory.IwahoriInj.deep_zero_iff]
      · simp [one_apply_ne e, GlobalTheory.IwahoriInj.deep_zero]
  exact ⟨key g hg h.1, key g⁻¹ (inv_mem hg) h.2⟩

theorem isOpen_grp (c : n → ℤ) (m : ℕ) :
    IsOpen (GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m) : Set (GL n k)) := by
  have e : (GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m) : Set (GL n k)) =
      (⋂ i, ⋂ j, {g : GL n k | GlobalTheory.IwahoriInj.Deep ((m : ℤ) * (c i - c j)) (g.val i j)}) ∩
      ⋂ i, ⋂ j, {g : GL n k | GlobalTheory.IwahoriInj.Deep ((m : ℤ) * (c i - c j)) ((g⁻¹).val i j)} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [e]
  refine IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  · exact (GlobalTheory.SBUniform.isOpen_deep _).preimage (Units.continuous_val.matrix_elem i j)
  · exact (GlobalTheory.SBUniform.isOpen_deep _).preimage (Units.continuous_coe_inv.matrix_elem i j)

theorem unipB_eq_unipOf (N : ℕ) :
    unipB k (Fin N) = unipOf k (fun i : Fin N => ((i : ℕ) : ℤ)) := by
  ext g
  rw [mem_unipB, mem_unipOf]
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    have hji : j ≤ i := by
      rw [not_lt] at hij
      exact Fin.le_def.2 (by exact_mod_cast hij)
    rcases hji.lt_or_eq with h | h
    · rw [h1 i j h, one_apply_ne (ne_of_gt h)]
    · subst h; rw [h2 j, one_apply_eq]
  · intro h
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · have : ¬ ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by
        have := Fin.lt_def.1 hji
        omega
      rw [h i j this, one_apply_ne (ne_of_gt hji)]
    · rw [h i i (lt_irrefl _), one_apply_eq]

theorem exists_compact_subgroup_of_isCompact :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
      (Q : Set (GL (Fin N) k)), IsCompact Q → Q ⊆ (unipB k (Fin N) : Set (GL (Fin N) k)) →
      ∃ U₀ : Subgroup (GL (Fin N) k), IsCompact (U₀ : Set (GL (Fin N) k)) ∧ Q ⊆ (U₀ : Set (GL (Fin N) k)) := by
  intro k _ _ _ _ N Q hQ hQU
  set c : Fin N → ℤ := fun i => ((i : ℕ) : ℤ)
  rw [unipB_eq_unipOf] at hQU
  let V : ℕ → Set (GL (Fin N) k) := fun m =>
    (GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m) : Set (GL (Fin N) k)) ∪ (unipOf k c : Set _)ᶜ
  have hVo : ∀ m, IsOpen (V m) := fun m =>
    (isOpen_grp c m).union (GlobalTheory.UnipCompact.isClosed_unipOf c).isOpen_compl
  have hVmono : Monotone V := by
    intro m M hmM g hg
    rcases hg with hg | hg
    · by_cases hu : g ∈ unipOf k c
      · exact Or.inl (mem_grp_of_le hu hmM hg)
      · exact Or.inr hu
    · exact Or.inr hg
  have hcov : Q ⊆ ⋃ m, V m := fun g hg =>
    Set.mem_iUnion.2 (((GlobalTheory.UnipCompact.eventually_mem_grp (hQU hg)).exists).imp fun _ h => Or.inl h)
  obtain ⟨M, hM⟩ := hQ.elim_directed_cover V hVo hcov hVmono.directed_le
  refine ⟨GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c M) ⊓ unipOf k c, ?_, fun g hg => ?_⟩
  · rw [Subgroup.coe_inf]
    exact (GlobalTheory.IwahoriInj.isCompact_grp _).inter_right (GlobalTheory.UnipCompact.isClosed_unipOf c)
  · rcases hM hg with h | h
    · exact ⟨h, hQU hg⟩
    · exact absurd (hQU hg) h

end GlobalTheory.UnipCptSub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTransposeMulPosDef
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitaryClasses

theorem posDef_cT_inv_mul_inv (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (h : GL (Fin n) E)
    (τ : E →+* ℂ) :
    ((cT (IsCMField.complexConj E).toRingEquiv.toRingHom (h⁻¹).val * (h⁻¹).val).map τ).PosDef := by
  set B : Matrix (Fin n) (Fin n) E := (h⁻¹).val with hB
  have hc : (cT (IsCMField.complexConj E).toRingEquiv.toRingHom B).map τ = (B.map τ)ᴴ := by
    ext i j
    simp [cT, Matrix.conjTranspose_apply, IsCMField.complexEmbedding_complexConj]
  rw [Matrix.map_mul, hc]
  refine Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit ?_)
  have hu : IsUnit B := (h⁻¹).isUnit
  exact hu.map (RingHom.mapMatrix τ)

end GlobalTheory.UnitaryClasses
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantOneMemCuspFormsOfWittIndexZero
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory

theorem constant_one_mem_cuspForms_of_wittIndex_zero : ∀ {D : D7} {θ : InfFam D} {A B : HSp D} {sA : RealMat A} {sB : RealMat B} {t : ℕ} {cA : CptF A}, HidaSetting θ A B sA sB t cA → wittIndex A = 0 → (fun _ : GA D A => (1 : ℂ)) ∈ A0 θ A cA := by
  intro D θ A B sA sB t cA _ h
  rw [wittIndex_eq_zero_iff_isAniso] at h
  exact (mem_cuspForms).2 ⟨⟨isAutFunSm_const θ A 1, fun r C hC => absurd hC (h r C)⟩, .of_invariant fun _ _ _ => rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousGLAdelicProjectionsInclusionsStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_GL_adelic_projections_inclusions : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), Continuous (fun g : GA E a => Matrix.GeneralLinearGroup.map (pInf E) g) ∧ Continuous (fun g : GA E a => Matrix.GeneralLinearGroup.map (pFin E) g) ∧ Continuous (infGL E a) ∧ Continuous (finGL E a) := by
  first | exact @GlobalTheory.GLProj.continuous_proj_incl | exact GlobalTheory.GLProj.continuous_proj_incl | (intros; apply GlobalTheory.GLProj.continuous_proj_incl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousInvolutiveLocalTransposeInverseStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_involutive_local_transpose_inverse : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), Continuous (thL n w) ∧ ∀ g : GLw n w, thL n w (thL n w g) = g := by
  first | exact @GlobalTheory.BCT.thL_continuous_involutive | exact GlobalTheory.BCT.thL_continuous_involutive | (intros; apply GlobalTheory.BCT.thL_continuous_involutive <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryLocalPointEqMapRationalStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryLocalPoint_eq_map_rational : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (γ : UE E n) (w : Pl E), ((locPt w γ : UL n w) : GLw n w) = Matrix.GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (γ : GL (Fin n) E) := by
  first | exact @GlobalTheory.BCT.LocVal.main | exact GlobalTheory.BCT.LocVal.main | (intros; apply GlobalTheory.BCT.LocVal.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSkewHermitianSelfDualLatticeSpaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_ne_zero_of_skewHermitianSelfDualLatticeSpace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (W : Spc F E n), W.IsSkew σ B r s → W.J.det ≠ 0 := by
  first | exact @GlobalTheory.SkewDet.det_ne_zero_of_isSkew | exact GlobalTheory.SkewDet.det_ne_zero_of_isSkew | (intros; apply GlobalTheory.SkewDet.det_ne_zero_of_isSkew <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalIntegralInvariantFormDiagonalLagrangian
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

noncomputable section
attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

namespace GlobalTheory.DiagLagrNorm
open MeasureTheory GlobalTheory.DiagForm IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem map_eI_eq : ∃ k : NNReal, k ≠ 0 ∧
    Measure.map (eI F κ) (volume : Measure (Vi F κ)) = k • (volume : Measure (κ → mixedEmbedding.mixedSpace F)) := by
  have : MeasurableAdd (mixedEmbedding.mixedSpace F) := inferInstance
  have : SigmaFinite (volume : Measure (mixedEmbedding.mixedSpace F)) := inferInstance
  have : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure :=
    Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  have : (Measure.map (eI F κ) (volume : Measure (Vi F κ))).IsAddHaarMeasure :=
    (eI F κ).isAddHaarMeasure_map volume
  exact ⟨_, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne',
    Measure.isAddLeftInvariant_eq_smul _ _⟩

theorem integral_compD {k : NNReal}
    (hk : Measure.map (eI F κ) (volume : Measure (Vi F κ)) = k • (volume : Measure (κ → mixedEmbedding.mixedSpace F)))
    (f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ) :
    SchwartzMap.integralCLM ℂ (volume : Measure (Vi F κ)) (compD F κ f) =
      (k : ℂ) * ∫ x : κ → mixedEmbedding.mixedSpace F, f (Sum.elim x x) := by
  rw [SchwartzMap.integralCLM_apply]
  have e : ∀ u, compD F κ f u = (fun x : κ → mixedEmbedding.mixedSpace F => f (Sum.elim x x)) (eI F κ u) :=
    fun u => rfl
  simp only [e]
  have h1 := integral_map_equiv (μ := (volume : Measure (Vi F κ))) (eI F κ).toHomeomorph.toMeasurableEquiv
    (fun x : κ → mixedEmbedding.mixedSpace F => f (Sum.elim x x))
  change ∫ y, f (Sum.elim y y) ∂(Measure.map (eI F κ) volume) = ∫ x, f (Sum.elim (eI F κ x) (eI F κ x)) at h1
  rw [hk, integral_smul_nnreal_measure] at h1
  rw [← h1, NNReal.smul_def, Complex.real_smul]

theorem exists_SB_ne : ∃ g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F),
    (∫ v : Vf F κ, g (Sum.elim v v) ∂Measure.addHaar) ≠ 0 := by
  obtain ⟨hO, hK⟩ := PI.IntAdCpctOpenWork.main F
  set O := {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}
  have h0 : (0 : FiniteAdeleRing (𝓞 F) F) ∈ O := fun v => (v.adicCompletionIntegers F).zero_mem
  set U : Set (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) := Set.univ.pi fun _ => O
  have hUo : IsOpen U := isOpen_set_pi Set.finite_univ fun _ _ => hO
  have hUc : IsCompact U := isCompact_univ_pi fun _ => hK
  set g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ := U.indicator fun _ => 1
  have hg : g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) :=
    ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨hUc.isClosed, hUo⟩).isLocallyConstant,
      HasCompactSupport.intro hUc fun z hz => Set.indicator_of_notMem hz _⟩
  set V : Set (Vf F κ) := Set.univ.pi fun _ => O
  have hVo : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => hO
  have hVc : IsCompact V := isCompact_univ_pi fun _ => hK
  have hgV : (fun v : Vf F κ => g (Sum.elim v v)) = V.indicator fun _ => (1 : ℂ) := by
    funext v
    simp only [g, U, V, Set.indicator_apply, Set.mem_univ_pi, Sum.forall, Sum.elim_inl, Sum.elim_inr, and_self]
  refine ⟨g, hg, ?_⟩
  rw [hgV, integral_indicator_const _ hVo.measurableSet]
  have hpos : 0 < (Measure.addHaar : Measure (Vf F κ)) V := hVo.measure_pos _ ⟨0, fun i _ => h0⟩
  have hfin : (Measure.addHaar : Measure (Vf F κ)) V < ⊤ := hVc.measure_lt_top
  have : 0 < (Measure.addHaar : Measure (Vf F κ)).real V := ENNReal.toReal_pos hpos.ne' hfin.ne
  simpa using this.ne'

end GlobalTheory.DiagLagrNorm

namespace GlobalTheory.RealLift

open MeasureTheory GlobalTheory.DiagForm GlobalTheory.DiagLagrNorm

theorem diagLagr_invForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type)
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ)),
    IsStd ψ → IsDblCoord (cA σ) (-1) JA JB d dd →
    ∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ z : Matrix α β (AE F E), ∀ φ ∈ (adeleClass F).sp (κ ⊕ κ),
      l (dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ) φ) = l φ) ∧
      ∃ g ∈ SB (κ ⊕ κ → Af F), ∀ f : SInf F (κ ⊕ κ),
        l (pureA F f g) = ∫ x : κ → mixedEmbedding.mixedSpace F, f (Sum.elim x x) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d dd _ hdd
  obtain ⟨k, hk0, hk⟩ := map_eI_eq (F := F) (κ := κ)
  obtain ⟨g, hg, hc⟩ := exists_SB_ne (F := F) (κ := κ)
  set c : ℂ := (∫ v : Vf F κ, g (Sum.elim v v) ∂Measure.addHaar) * (k : ℂ) with hcdef
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  have hc0 : c ≠ 0 := mul_ne_zero hc hk'
  refine ⟨c⁻¹ • lDiag F κ, ?_, ?_, g, hg, ?_⟩
  · intro g' hg'
    obtain ⟨T, hT⟩ := lDiag_adm (F := F) (κ := κ) g' hg'
    exact ⟨c⁻¹ • T, fun f => by simp [hT f]⟩
  · intro z φ hφ
    have hz : z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ = Matrix.fromCols z z := by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.mul_fromCols, Matrix.mul_one]
    have hr : dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (AE F E))ᵀ) φ =
        schr ψ (Sum.elim (d.e z).1 (d.e z).1, Sum.elim (d.e z).2 (-(d.e z).2)) φ := by
      rw [hz, Darboux.rho, hdd z z]
    simp only [LinearMap.smul_apply]
    rw [hr, lDiag_schr ψ _ _ hφ]
  · intro f
    simp only [LinearMap.smul_apply]
    rw [lDiag_pureA f hg, integral_compD hk, smul_eq_mul, hcdef]
    field_simp

end GlobalTheory.RealLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigensystemGoodFormsThetaTargetOccursOnRowsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigensystem_goodForms_thetaTarget_occurs_on_rows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → SchurAll R → GoodStable A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R → ∀ SF, IsSF R SF → ∀ i c, Wcc R SF i c ≠ ⊥ → EEc R SF c ≠ ⊥ := by
  first | exact @GlobalTheory.Hk3.eec_ne_bot_of_wcc_ne_bot | exact GlobalTheory.Hk3.eec_ne_bot_of_wcc_ne_bot | (intros; apply GlobalTheory.Hk3.eec_ne_bot_of_wcc_ne_bot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAddHaarMatrixSpaceStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_add_haar_matrix_space : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a d : ℕ},
    ∃ ν : @Measure (Matrix (Fin a) (Fin d) k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν := by
  first | exact @GlobalTheory.haar_exists_matrix_local_field | exact GlobalTheory.haar_exists_matrix_local_field | (intros; apply GlobalTheory.haar_exists_matrix_local_field <;> assumption)
end

