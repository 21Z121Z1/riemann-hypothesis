import Mathlib
import Formalism.LocalToGlobal.Columns.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleFinrankOne.IrrOfFinrankOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicHeckeCharValuesInNumberField
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0075
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0081
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwistBaseCoefficientRingResidueFieldFinite
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0088
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0115
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypesIdempotentCoefficients
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharCompMemComplexIrrCharSet
section
open Formalism.L2.DIV

noncomputable section

namespace GlobalTheory

theorem absIrrChar_comp_mem_gxIrrSet : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] {K : Type} [inst_2 : Field K]
    [inst_3 : CharZero K] (σ : K →+* ℂ) (χ : G → K), IsAbsIrrChar χ →
    (fun g => σ (χ g)) ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ := by
  intro G _ _ K _ _ σ χ h
  classical
  obtain ⟨⟨n, ρc, htr⟩, hip⟩ := PI.XgCTieBrWork.Chars.absIrr_isIrr σ h
  have htr' : ∀ x, σ (χ x) = Matrix.trace ((ρc x : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := htr
  have hchar : ∀ x, (PI.XgCTieBrWork.Chars.ofGL ρc).character x = σ (χ x) := fun x => by
    rw [PI.XgCTieBrWork.Chars.char_ofGL, htr']
  haveI : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (NeZero.ne _)
  have hfr := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    (PI.XgCTieBrWork.Chars.ofGL ρc) (PI.XgCTieBrWork.Chars.ofGL ρc)
  have hsum : ∑ g : G, (PI.XgCTieBrWork.Chars.ofGL ρc).character g *
      (PI.XgCTieBrWork.Chars.ofGL ρc).character g⁻¹ = (Nat.card G : ℂ) := by
    simp_rw [hchar]
    rw [Nat.card_eq_fintype_card, ← hip]
    unfold Formalism.L2.NT.ipG
    refine Finset.sum_congr rfl fun x _ => ?_
    show σ (χ x) * σ (χ x⁻¹) = σ (χ x) * star (σ (χ x))
    rw [htr' x, htr' x⁻¹, PI.XgCTieBrWork.Chars.star_trace_inv]
  rw [hsum, inv_mul_cancel₀ (NeZero.ne _)] at hfr
  have h1 : Module.finrank ℂ (Representation.IntertwiningMap (PI.XgCTieBrWork.Chars.ofGL ρc)
      (PI.XgCTieBrWork.Chars.ofGL ρc)) = 1 := by
    exact_mod_cast hfr.symm
  exact ⟨n, PI.XgCTieBrWork.Chars.ofGL ρc, PI.XgCTieBrWork.Chars.irr_of_finrank_one _ h1, funext hchar⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicHeckeCharValuesInNumberFieldStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicHeckeChar_values_in_numberField : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L) (I : Type) [Fintype I] (φ : I → L →+* ℂ), CMData F c φ → ∀ (χ : HChar L) (n : I → ℤ) (r : ℤ), χ.HasInf φ n → (∀ i, Even (n i - r)) → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ χ.ValuesIn ((r : ℝ) / 2) M.val.toRingHom := by
  first | exact @GlobalTheory.Mem.ValAlg.values_in_numberField | exact GlobalTheory.Mem.ValAlg.values_in_numberField | (intros; apply GlobalTheory.Mem.ValAlg.values_in_numberField <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisFrobeniusFixedFilZeroEqQp
section
namespace GlobalTheory.MemLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

theorem fund_phiB_alg (l : ℕ) [Fact l.Prime] (x : Per.Acris l) :
    Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) x) =
      algebraMap (Per.Acris l) (Per.Bcris l) (phiA l x) :=
  GlobalTheory.CrisMaps.φB_phiA l x

theorem fund_zB (l : ℕ) [Fact l.Prime] (z : ℤ_[l]) :
    Per.zB l z = algebraMap (Per.Acris l) (Per.Bcris l)
      (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l z)) :=
  (GlobalTheory.RingIface.zB_eq_aB_zA l z).trans (GlobalTheory.RingIface.aB_eq_alg l _)

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem fundamental_exact (l : ℕ) [Fact l.Prime] (C : Core l) (b : Per.Bcris l)
    (hφ : Per.φB l b = b) (hF : C.ι b ∈ Per.FilD l 0) :
    ∃ c : ℚ_[l], C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) = b := by
  obtain ⟨r, x, hx⟩ := GlobalTheory.T.bcris_eq_acris_localization_periodT l C b
  obtain ⟨-, hinj, -, -⟩ := GlobalTheory.T.bdRPlus_isDomain_bdR_isField l
  obtain ⟨-, h1, hmul, -, -, -, hP⟩ := GlobalTheory.T.bdR_filtration_laws l
  have hj := GlobalTheory.T.acrisToBdRPlus_injective l C.j C.j_cris
  obtain ⟨htu, ht1, -, hlu⟩ := GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C
  have htφ := GlobalTheory.T.acrisFrobenius_fontaine_t_eq_mul l C
  obtain ⟨-, -, huz, -, -, -⟩ := GlobalTheory.T.localPeriodRingsData_unramified_laws l C
  have hA : Function.Injective (algebraMap (Per.Acris l) (Per.Bcris l)) := by
    intro y y' h
    apply hj
    apply hinj
    rw [← C.ι_j, ← C.ι_j, h]
  have e1 : phiA l x = (l : Per.Acris l) ^ r * x := by
    apply hA
    rw [← fund_phiB_alg, map_mul, map_pow, map_natCast, ← hx, map_mul, map_pow, hφ,
      fund_phiB_alg, htφ, map_mul, map_natCast, mul_pow]
    ring
  have ht1' : algebraMap (Per.BdRp l) (Per.BdR l) (C.j C.t) ∈ Per.FilD l 1 :=
    (hP 1 _).2 ht1
  have htr : ∀ n : ℕ, algebraMap (Per.BdRp l) (Per.BdR l) (C.j C.t) ^ n ∈ Per.FilD l (n : ℤ) := by
    intro n
    induction n with
    | zero => rw [pow_zero]; exact h1
    | succ n ih =>
      rw [pow_succ, Nat.cast_succ]
      exact hmul _ _ _ _ ih ht1'
  have e2 : C.j x ∈ Per.FilP l r := by
    rw [← hP, ← C.ι_j, ← hx, map_mul, map_pow, C.ι_j]
    have := hmul _ _ _ _ hF (htr r)
    rwa [zero_add] at this
  obtain ⟨z, k, hz⟩ := GlobalTheory.T.acris_frobenius_eigen_fil_eq_qlMul_tPow l C r x e1 e2
  have e3 : (l : Per.Bcris l) ^ k * b = Per.zB l z := by
    apply (htu.pow r).mul_right_cancel
    have := congrArg (algebraMap (Per.Acris l) (Per.Bcris l)) hz
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast, ← hx, ← fund_zB, ← mul_assoc] at this
    exact this
  refine ⟨(z : ℚ_[l]) / (l : ℚ_[l]) ^ k, ?_⟩
  apply (hlu.pow k).mul_left_cancel
  rw [e3, ← huz]
  have hl : (l : ℚ_[l]) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have e4 : (z : ℚ_[l]) = (l : ℚ_[l]) ^ k * ((z : ℚ_[l]) / (l : ℚ_[l]) ^ k) := by
    field_simp
  conv_rhs => rw [e4]
  rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteBaseDataAdmissibleStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBaseData_admissible : ∀ (B : Base) (X : PreX B.toPre) (Ch : Chars B.fields (B.primes X) B.R.m), Ch.Ok → Ch.FromHecke B.wts B.embLL → (B.dat X Ch).Ok := by
  first | exact @GlobalTheory.Mem.DatLaws.dat_ok | exact GlobalTheory.Mem.DatLaws.dat_ok | (intros; apply GlobalTheory.Mem.DatLaws.dat_ok <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAutomorphicUnipotentLabelsStatement
section
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_automorphic_unipotent_labels : ∀ (B : Base) (C : Cols B) (W : RowsRest B C) (nd : NData B.R B.host W.what₂), IsEmpty nd.Loc → ∃ A : NAut nd, (∀ k w (p : A.LP w), A.items₂ k w p = (X - 1) ^ A.lpDim p) ∧ ∀ w (p : A.LP w) σ, A.inePol p σ = (X - 1) ^ A.lpDim p := by
  first | exact @GlobalTheory.MemN.exists_nAut_unramified | exact GlobalTheory.MemN.exists_nAut_unramified | (intros; apply GlobalTheory.MemN.exists_nAut_unramified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisCoordLattice
section
noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial

theorem exists_basis_coord_lattice {O V : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
    (B : Submodule O V) (hfg : B.FG)
    (hsp : Submodule.span (FractionRing O) (B : Set V) = ⊤) :
    ∃ (n : ℕ) (e : Module.Basis (Fin n) (FractionRing O) V),
      ∀ f : V, f ∈ B ↔ ∀ t, e.repr f t ∈ (algebraMap O (FractionRing O)).range := by
  classical
  have hfin : Module.Finite O B := Module.Finite.iff_fg.2 hfg
  have htf : Module.IsTorsionFree O V := Module.IsTorsionFree.trans_faithfulSMul O (FractionRing O) V
  have hfree : Module.Free O B := inferInstance
  let bO := Module.finBasis O B
  let v : Fin (Module.finrank O B) → V := fun t => (bO t : V)
  have hliO : LinearIndependent O v := bO.linearIndependent.map' B.subtype (Submodule.ker_subtype B)
  have hliK : LinearIndependent (FractionRing O) v :=
    (LinearIndependent.iff_fractionRing O (FractionRing O)).1 hliO
  have hBspan : B = Submodule.span O (Set.range v) := by
    have h1 : Submodule.map B.subtype (Submodule.span O (Set.range bO)) = B := by
      rw [bO.span_eq, Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_span, ← Set.range_comp] at h1
    exact h1.symm
  have hle : (⊤ : Submodule (FractionRing O) V) ≤ Submodule.span (FractionRing O) (Set.range v) := by
    rw [← hsp, Submodule.span_le]
    intro x hx
    have hx' : x ∈ Submodule.span O (Set.range v) := hBspan ▸ hx
    exact Submodule.span_subset_span O (FractionRing O) (Set.range v) hx'
  let e := Module.Basis.mk hliK hle
  have he : ∀ t, e t = v t := fun t => by simp [e]
  refine ⟨_, e, fun f => ⟨fun hf => ?_, fun hf => ?_⟩⟩
  · rw [hBspan] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      intro s
      rw [← he, e.repr_self]
      by_cases h : t = s
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [h]⟩
    | zero => intro s; exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro s
      rw [map_add, Finsupp.add_apply]
      exact add_mem (hx s) (hy s)
    | smul a x _ hx =>
      intro s
      rw [← algebraMap_smul (FractionRing O) a x, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact mul_mem ⟨a, rfl⟩ (hx s)
  · choose c hc using hf
    rw [← e.sum_repr f]
    refine sum_mem fun t _ => ?_
    rw [← hc t, algebraMap_smul, he]
    exact B.smul_mem _ (hBspan ▸ Submodule.subset_span ⟨t, rfl⟩)

section SideCoord

variable {K C : Type} [Field K] [Field C] (iC : K →+* C) {V : Bool → Type}
  [∀ b, AddCommGroup (V b)] [∀ b, Module K (V b)] {n : Bool → ℕ}
  (e : ∀ b, Module.Basis (Fin (n b)) K (V b))

def sideEv (b : Bool) : V b →+ ((Σ b', Fin (n b')) → C) where
  toFun f y := if h : y.1 = b then iC ((e b).repr f (h ▸ y.2)) else 0
  map_zero' := by
    funext y
    by_cases h : y.1 = b <;> simp [h]
  map_add' f g := by
    funext y
    by_cases h : y.1 = b <;> simp [h]

@[simp] theorem sideEv_same (b : Bool) (f : V b) (t : Fin (n b)) :
    sideEv iC e b f ⟨b, t⟩ = iC ((e b).repr f t) := by
  simp [sideEv]

theorem sideEv_other {b b' : Bool} (h : b' ≠ b) (f : V b) (t : Fin (n b')) :
    sideEv iC e b f ⟨b', t⟩ = 0 := by
  simp [sideEv, h]

theorem sideEv_smul (b : Bool) (a : K) (f : V b) (y : Σ b', Fin (n b')) :
    sideEv iC e b (a • f) y = iC a * sideEv iC e b f y := by
  obtain ⟨b', t⟩ := y
  by_cases h : b' = b
  · subst h; simp
  · simp [sideEv_other iC e h]

theorem sideEv_inj (b : Bool) : Function.Injective (sideEv iC e b) := by
  intro f g hfg
  apply (e b).repr.injective
  ext t
  have := congrFun hfg ⟨b, t⟩
  exact iC.injective (by simpa using this)

def sideU (b : Bool) (T : Module.End K (V b)) (c y : Σ b', Fin (n b')) : C :=
  if h : c.1 = b then sideEv iC e b (T (e b (h ▸ c.2))) y else 0

theorem sideEv_end (b : Bool) (T : Module.End K (V b)) (f : V b) (y : Σ b', Fin (n b')) :
    sideEv iC e b (T f) y = ∑ c, sideU iC e b T c y * sideEv iC e b f c := by
  classical
  have h0 : T f = ∑ t, (e b).repr f t • T (e b t) := by
    conv_lhs => rw [← (e b).sum_repr f]
    simp only [map_sum, map_smul]
  have h1 : sideEv iC e b (T f) y =
      ∑ t, iC ((e b).repr f t) * sideEv iC e b (T (e b t)) y := by
    rw [h0, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun t _ => sideEv_smul iC e b _ _ y
  rw [h1, Fintype.sum_sigma, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp [sideU, mul_comm]
  · intro b' _ hb
    refine Finset.sum_eq_zero fun t _ => ?_
    simp [sideEv_other iC e hb]
  · simp

end SideCoord

theorem exists_nth_of_fg_full : ∀ (D : D7) (tw : NTw D.R D.host D.what₂ D.LL0 D.nd)
    (ex : NExp D.R D.host D.what₂ D.LL0 D.nd tw),
    (∀ i : tw.Tw, ∃ iC : FractionRing (tw.O i) →+* ℂ_[tw.l i], ∀ x, ‖iC x‖ ≤ 1 ↔
      x ∈ (algebraMap (tw.O i) (FractionRing (tw.O i))).range) →
    (∀ i j b, (ex.Bsup i j b).FG ∧
      Submodule.span (FractionRing (tw.O i)) (ex.Bsup i j b : Set (ex.Fm i j b)) = ⊤) →
    Nonempty (NTh D.R D.host D.what₂ D.LL0 D.nd tw ex) := by
  classical
  intro D tw ex hi hB
  choose iC hiC using hi
  have hex := fun i j b =>
    exists_basis_coord_lattice (ex.Bsup i j b) (hB i j b).1 (hB i j b).2
  choose n e he using hex
  have hsup : ∀ i j b, {f : ex.Fm i j b | f ∈ (⊤ : AddSubgroup (ex.Fm i j b)) ∧
      ∀ y, ‖sideEv (iC i) (e i j) b f y‖ ≤ 1} = (ex.Bsup i j b : Set (ex.Fm i j b)) := by
    intro i j b
    ext f
    simp only [Set.mem_ofPred_eq, AddSubgroup.mem_top, true_and, SetLike.mem_coe]
    rw [he i j b f]
    constructor
    · intro h t
      have := h ⟨b, t⟩
      rw [sideEv_same] at this
      exact (hiC i _).1 this
    · intro h y
      obtain ⟨b', t⟩ := y
      by_cases hb : b' = b
      · subst hb
        rw [sideEv_same]
        exact (hiC i _).2 (h t)
      · rw [sideEv_other _ _ hb]
        simp
  exact ⟨{
    iC := iC
    iC_int := hiC
    aL := fun i => if ∃ k, tw.l i = D.host.g k then 1 else 0
    aL_g := fun i k h => if_pos ⟨k, h⟩
    aL_off := fun i h => if_neg (not_exists.2 h)
    Pt := fun i j => Σ b, Fin (n i j b)
    ev := fun i j b => sideEv (iC i) (e i j) b
    ev_smul := fun i j b a f y => sideEv_smul _ _ b a f y
    ev_inj := fun i j b => sideEv_inj _ _ b
    Lt := fun _ _ => PUnit
    acgLt := fun _ _ => inferInstance
    modLt := fun _ _ => inferInstance
    freeLt := fun _ _ => inferInstance
    finLt := fun _ _ => inferInstance
    Let := fun _ _ => PEmpty
    finLet := fun _ _ => inferInstance
    Harm := fun _ _ => Set.univ
    Ctr := fun _ _ => PEmpty
    ctrC := fun _ _ κ => κ.elim
    Harm_def := fun i j P => ⟨fun _ κ => κ.elim, fun _ => Set.mem_univ _⟩
    thV := fun _ _ _ _ _ => 0
    thV_add := fun _ _ _ _ _ _ => by simp
    thV_smul := fun _ _ _ _ _ _ => by simp
    thV_addP := fun _ _ _ _ _ _ => by simp
    thV_smulP := fun _ _ _ _ _ _ => by simp
    datPhi := fun _ _ _ _ => 0
    datP := fun _ _ _ _ => 0
    recDet := fun _ _ _ => 1
    Kq := fun _ _ _ => PUnit
    grpKq := fun _ _ _ => inferInstance
    actK := fun _ _ _ _ y => y
    actK_one := fun _ _ _ _ => rfl
    actK_mul := fun _ _ _ _ _ _ => rfl
    recDetq := fun _ _ _ _ => 1
    recDetq_mem := fun _ _ _ _ => one_mem _
    recDet_act := fun _ _ _ _ _ _ _ _ _ _ => rfl
    recDetq_act := fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    hkIdx := fun i j _ _ => Σ b, Fin (n i j b)
    finHk := fun _ _ _ _ => inferInstance
    hkMove := fun _ _ _ _ c _ => c
    hkU := fun i j b k P c y => sideU (iC i) (e i j) b (ex.hkF i j b k P) c y
    hk_ev := fun i j b k P _ _ _ _ f y => sideEv_end _ _ b _ f y
    MaximalUnramifiedExtension := fun _ => ⊤
    FmUr := fun _ _ _ => ⊤
    FmUr_smul := fun _ _ _ _ _ _ _ => AddSubgroup.mem_top _
    FmUr_span := fun i j b => by
      rw [AddSubgroup.coe_top, Submodule.span_univ]
    Bsup_def := fun i j b => by
      rw [hsup i j b, Submodule.span_eq] }⟩

end GlobalTheory.HeightCounting

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmConjugationOmegaStatement
section
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cm_conjugation_omega : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (nd : NData R H what₂), ∃ c : nd.Om ≃+* nd.Om, IsCMConjOm H.E nd.Om c := by
  first | exact @GlobalTheory.MemN.exists_isCMConjOm_nData | exact GlobalTheory.MemN.exists_isCMConjOm_nData | (intros; apply GlobalTheory.MemN.exists_isCMConjOm_nData <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiagSpacesOfCh
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.Mem

theorem exists_diagSpaces_ofCh : ∀ (P : PreCh) (L : LevCh P), ∃ (sp : @Spaces P.R L.host.F L.host.E _ _ _ _ L.host.cmStar _) (hT : letI := L.host.cmStar; sp.T = L.T P.u₀) (hY : letI := L.host.cmStar; ∀ j, j ≤ P.R.m → ∀ τ : L.host.E →+* ℂ, (sp.Y j).sig τ = sigYD P.R j) (hA : letI := L.host.cmStar; ∀ j, 0 < j → j < P.R.m → HasHyperbolicAuxiliaryFrame sp j) (hV : letI := L.host.cmStar; ∀ j, 1 ≤ j → j ≤ P.R.m → sp.Vneg j = false) (hz : letI := L.host.cmStar; (sp.X P.R.m).hT sp.z sp.z = (sp.T : L.host.E)), (letI := L.host.cmStar; DiagSpaces sp ∧ ∀ j, sp.Vneg j = false) ∧ (Pre.ofCh P L sp hT hY hA hV hz).R = P.R := by
  intro P L
  letI := L.host.cmStar
  have hs : ∀ x : L.host.E, star x = L.host.conj x := bridge_star_holds P.R L.host
  have hpz : star (L.piT P.u₀ : L.host.E) * (L.piT P.u₀ : L.host.E) = (L.T P.u₀ : L.host.E) := by
    rw [hs, mul_comm]
    exact L.piT_norm P.u₀
  obtain ⟨S, hT, hD, hV, hA, hz, hY⟩ := GlobalTheory.Mem.exists_diagSpaces_norm P.R L.host.F L.host.E (host_cmData P.R L.host)
    (L.T P.u₀) (L.T_prime P.u₀) (L.piT P.u₀ : L.host.E) hpz
  exact ⟨S, hT, hY, hA, fun j _ _ => hV j, hz, ⟨hD, hV⟩, rfl⟩

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarishChandraWeights
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem

theorem exists_preCh_of_prescribed : ∀ (R : Ranks) (H : Host R) (u0 : R.A), H.ccK = ⊤ → (∀ p ∈ H.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1) → Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)) → ∀ (M : ℕ), 0 < M → ∀ (c : Fin M → Fin (R.k - 2) → Bool) (Del hh : ℕ) (uF uL b1 : Tau R → ℤ), 1 ≤ Del → R.t + 3 ≤ 2 * hh → (∀ τ, ((R.k - 2 : ℕ) : ℤ) * (4 * Del) ≤ uF τ ∧ uL τ ≤ -1 ∧ -b1 τ ≤ uL τ) → ∃ hcW : Fin M → Tau R → HCParam R, (∀ u τ, (∀ i : Fin (R.k - 1), (hcW u τ).v i = ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * (Del : ℚ))) ∧ (∀ j : Fin R.m, (hcW u τ).b j = (b1 τ : ℚ) + (j.1 : ℚ) * (2 * hh : ℚ) ∧ (hcW u τ).e j = (hcW u τ).b j + hh) ∧ (∀ h : 0 < R.k, (hcW u τ).u ⟨0, h⟩ = (uF τ : ℚ) + 1 / 2 ∧ (hcW u τ).u ⟨R.k - 1, by omega⟩ = (uL τ : ℚ) + 1 / 2) ∧ ∀ (l : ℕ) (h : l < R.k - 2), (hcW u τ).u ⟨l + 1, by omega⟩ = (hcW u τ).v ⟨l, by omega⟩ - 1 / 2 - (if c u ⟨l, h⟩ then (Del : ℚ) else 0)) ∧ ∃ P : PreCh, P.R = R ∧ HEq P.H ({ H with u0 := u0 } : Host R) ∧ P.Word = Fin M ∧ HEq P.hcW hcW := by
  intro R H u0 hcc hlev hBB M hM c Del hh uF uL b1 hDel hhh hends
  choose hcW hW using fun (u : Fin M) (τ : Tau R) =>
    GlobalTheory.T.harish_chandra_parameter_formula R Del hh (uF τ) (uL τ) (b1 τ) hDel hhh (hends τ).1 (hends τ).2.1 (hends τ).2.2 (c u)
  refine ⟨hcW, hW, ?_⟩
  have hb : ∀ u u' τ, (hcW u τ).b = (hcW u' τ).b := fun u u' τ => funext fun j => by
    rw [((hW u τ).2.1 j).1, ((hW u' τ).2.1 j).1]
  refine ⟨{ R := R
            H := { H with u0 := u0 }
            ccK_top := hcc
            level_cond := hlev
            BB_disj := hBB
            Word := Fin M
            u₀ := ⟨0, hM⟩
            hcW := hcW
            hcW_v := fun u τ => funext fun i => by rw [(hW u τ).1 i, (hW _ τ).1 i]
            hcW_b := fun u τ => hb _ _ τ
            hcW_e := fun u τ => funext fun j => by
              rw [((hW u τ).2.1 j).2, ((hW _ τ).2.1 j).2, hb u ⟨0, hM⟩ τ]
            hcW_first := fun u τ h => by rw [((hW u τ).2.2.1 h).1, ((hW _ τ).2.2.1 h).1]
            hcW_last := fun u τ h => by rw [((hW u τ).2.2.1 h).2, ((hW _ τ).2.2.1 h).2] },
    rfl, HEq.rfl, rfl, HEq.rfl⟩

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityTypeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeChar_trivOn_realSubfield_infinityType : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L) (I : Type) [Fintype I] (φ : I → L →+* ℂ), CMData F c φ → ∀ (e : I → ℤ) (S : Finset (HeightOneSpectrum (𝓞 L))) (θ0 : ∀ v : HeightOneSpectrum (𝓞 L), (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ), (∀ w ∈ S, ∀ w', ConjPl c.toRingEquiv w w' → w' ∉ S) → (∀ ζ : (𝓞 L)ˣ, (∃ m : ℕ, 0 < m ∧ ((ζ : 𝓞 L) : L) ^ m = 1) → (∏ i, φ i ((ζ : 𝓞 L) : L) ^ (-e i)) * ∏ w ∈ S, ((θ0 w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) : ℂˣ) : ℂ) = 1) → ∃ χ : HChar L, χ.IsUnitary ∧ χ.TrivOn F ∧ χ.HasInf φ (fun i => -2 * e i) ∧ (∀ v, χ.TameAt v) ∧ (∀ v, v ∉ S → (∀ w ∈ S, ¬ ConjPl c.toRingEquiv w v) → χ.UnrAt v) ∧ (∀ w ∈ S, ∀ (k : Lˣ) (y : 𝓞 L) (b : (𝓞 L ⧸ w.asIdeal)ˣ), (k : L) = (y : L) → (b : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal y → χ.locK w k = θ0 w b) ∧ (∀ w ∈ S, ∀ n : ℕ, ((∀ x, IsUnitAt w x → χ.loc w x ^ n = 1) ↔ θ0 w ^ n = 1) ∧ ∀ w', ConjPl c.toRingEquiv w w' → ((∀ x, IsUnitAt w' x → χ.loc w' x ^ n = 1) ↔ θ0 w ^ n = 1)) := by
  first | exact @GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn | exact GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn | (intros; apply GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypesIdempotentCoefficientsStatement
section
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_types_idempotent_coefficients : ∀ (B : Base) (C : Cols B) (W : RowsRest B C) (χ : Chi B.toPre) (nd : NData B.R B.host W.what₂) (A : NAut nd), IsEmpty nd.Loc → HasChi nd χ → (∀ k w (p : A.LP w), A.items₂ k w p = (X - 1) ^ A.lpDim p) → (∀ w (p : A.LP w) σ, A.inePol p σ = (X - 1) ^ A.lpDim p) → (GoodChi B.toPre χ ∨ ((∀ μ, W.eOp μ = 0) ∧ ∀ μ j, W.eMt μ j = 0)) → ∃ T : NTypes A, T.IdempotentMatchesAction ∧ ∀ x, ∃ y : ↥B.LL0, B.embLL (y : B.LL) = T.e0.coeff x := by
  first | exact @GlobalTheory.MemN.TypesInhab.exists_nTypes | exact GlobalTheory.MemN.TypesInhab.exists_nTypes | (intros; apply GlobalTheory.MemN.TypesInhab.exists_nTypes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedCmTypeHeckeCharOnHost
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.ChiPsiExist

open Classical in

theorem exists_chiPsi : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ χ : HChar H.E, IsChiPsi H χ := by
  intro R H
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  obtain ⟨χ, hu, ht, hi, -, hunr, -⟩ :=
    GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn H.F H.E c (R.Psi) (embPsi H) hcm (fun _ => -1) ∅ (fun _ => 1)
      (fun w hw => absurd hw (Finset.notMem_empty w))
      (by
        intro ζ hζ
        rw [Finset.prod_empty, mul_one]
        exact UpperTheory.Mu.prod_emb_zpow H (Equiv.refl _) hζ _)
  exact ⟨χ, hu, fun v => hunr v (Finset.notMem_empty v) (fun w hw => absurd hw (Finset.notMem_empty w)), ht, hi⟩

end GlobalTheory.Mem.ChiPsiExist
end

