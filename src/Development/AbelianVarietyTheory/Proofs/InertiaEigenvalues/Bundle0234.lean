import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0227
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicBasisGaloisLatticeSameMatrices
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.Cyc.LatBasis

theorem exists_basis_of_full {R F N V ι : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup N] [Module R N] [AddCommGroup V] [Module F V]
    (f : N →+ V) (hf : Function.Injective f)
    (hs : ∀ (c : R) (x : N), f (c • x) = algebraMap R F c • f x)
    (hfull : ∀ v : V, ∃ c : R, c ≠ 0 ∧ ∃ x : N, algebraMap R F c • v = f x)
    (b : Module.Basis ι R N) :
    ∃ bV : Module.Basis ι F V, (∀ j, bV j = f (b j)) ∧
      ∀ x i, bV.repr (f x) i = algebraMap R F (b.repr x i) := by
  letI : Module R V := Module.compHom V (algebraMap R F)
  have hsm : ∀ (c : R) (v : V), c • v = algebraMap R F c • v := fun _ _ => rfl
  haveI : IsScalarTower R F V := ⟨fun c a v => by rw [hsm, Algebra.smul_def, mul_smul]⟩
  let f' : N →ₗ[R] V := { toFun := f, map_add' := map_add f, map_smul' := hs }
  haveI : IsLocalizedModule (nonZeroDivisors R) f' :=
    { map_units := fun s => by
        rw [Module.End.isUnit_iff]
        have h0 : algebraMap R F s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
        have : ⇑(algebraMap R (Module.End R V) s) = fun v => algebraMap R F s • v := by
          ext v; rfl
        rw [this]
        exact (MulAction.toPerm (Units.mk0 _ h0) : Equiv.Perm V).bijective
      surj := fun v => by
        obtain ⟨c, hc, x, hx⟩ := hfull v
        exact ⟨(x, ⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩), hx⟩
      exists_of_eq := fun h => ⟨1, by rw [hf h]⟩ }
  exact ⟨b.ofIsLocalizedModule F (nonZeroDivisors R) f',
    fun j => b.ofIsLocalizedModule_apply F _ f' j,
    fun x i => b.ofIsLocalizedModule_repr_apply F _ f' x i⟩

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {R Qp LL O : Type} [CommRing R] [IsDomain R]
  [Field Qp] [Algebra R Qp] [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]
  [TopologicalSpace LL] (T : LocLat G Qp LL O) (φ : R →+* O)
  (hφ : ∀ c, algebraMap O LL (φ c) = algebraMap Qp LL (algebraMap R Qp c))
  (hint : ∀ a : LL, ∃ c : R, c ≠ 0 ∧ ∃ o : O, algebraMap O LL o = algebraMap R Qp c • a)

include hφ in
omit [IsDomain R] in

theorem smul_eq (c : R) (v : T.V) : φ c • v = algebraMap R Qp c • v := by
  rw [← algebraMap_smul LL (φ c) v, ← algebraMap_smul LL (algebraMap R Qp c) v, hφ]

include hφ hint in

theorem exists_smul_mem (v : T.V) : ∃ c : R, c ≠ 0 ∧ algebraMap R Qp c • v ∈ T.L.T := by
  have kl : ∀ (c : R) (x : T.V), x ∈ T.L.T → algebraMap R Qp c • x ∈ T.L.T := by
    intro c x hx
    rw [← smul_eq T φ hφ]
    exact T.L.T.smul_mem _ hx
  have hv : v ∈ Submodule.span LL (T.L.T : Set T.V) := by rw [T.L.span]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, kl _ _ hx⟩
  | zero => exact ⟨1, one_ne_zero, kl _ _ T.L.T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn0, hn⟩ := hx
    obtain ⟨m, hm0, hm⟩ := hy
    refine ⟨n * m, mul_ne_zero hn0 hm0, ?_⟩
    rw [smul_add]
    refine T.L.T.add_mem ?_ ?_
    · rw [mul_comm, map_mul, mul_smul]; exact kl m _ hn
    · rw [map_mul, mul_smul]; exact kl n _ hm
  | smul a x _ hx =>
    obtain ⟨n, hn0, hn⟩ := hx
    obtain ⟨y, hy, o, ho⟩ := hint a
    refine ⟨y * n, mul_ne_zero hy hn0, ?_⟩
    have h3 := T.L.T.smul_mem o hn
    rw [← algebraMap_smul LL o, ho, smul_assoc, smul_comm a] at h3
    rw [map_mul, mul_smul]
    exact h3

include hφ hint in

theorem exists_basis_compHom [IsFractionRing R Qp] {ι : Type} :
    letI : Module R ↥T.L.T := Module.compHom ↥T.L.T φ
    ∀ b : Module.Basis ι R ↥T.L.T, ∃ bV : Module.Basis ι Qp T.V, ∀ g i j,
      algebraMap R Qp (b.repr (actT T.L g (b j)) i) = bV.repr (T.ρ g (bV j)) i := by
  letI : Module R ↥T.L.T := Module.compHom ↥T.L.T φ
  intro b
  obtain ⟨bV, h1, h2⟩ := exists_basis_of_full (F := Qp) (V := T.V) T.L.T.subtype.toAddMonoidHom
    Subtype.val_injective (fun c x => smul_eq T φ hφ c (x : T.V))
    (fun v => by
      obtain ⟨c, hc, h⟩ := exists_smul_mem T φ hφ hint v
      exact ⟨c, hc, ⟨_, h⟩, rfl⟩) b
  refine ⟨bV, fun g i j => ?_⟩
  rw [h1]
  exact (h2 (actT T.L g (b j)) i).symm

end Generic

theorem algebraMap_OL {l : ℕ} [Fact l.Prime] (LL : FinExt l) (c : ℤ_[l]) :
    algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) c) =
      algebraMap ℚ_[l] ↥LL.1 (algebraMap ℤ_[l] ℚ_[l] c) := by
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem exists_multiple_OL {l : ℕ} [Fact l.Prime] (LL : FinExt l) (a : ↥LL.1) :
    ∃ c : ℤ_[l], c ≠ 0 ∧ ∃ o : ↥(OL LL),
      algebraMap ↥(OL LL) ↥LL.1 o = algebraMap ℤ_[l] ℚ_[l] c • a := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h2 : IsAlgebraic ℤ_[l] a :=
    (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  exact ⟨y, hy, ⟨y • a, hi⟩, (algebraMap_smul ℚ_[l] y a).symm⟩

theorem exists_basis_of_isMat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ bV : Module.Basis (Fin d) ℚ_[l] T.V, ∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = algebraMap ℚ_[l] (PadicComplex l) (bV.repr (T.ρ g (bV j)) i) := by
  intro l _ K LL T d M A hM
  obtain ⟨b, hb, -⟩ := hM
  have H := exists_basis_compHom (ι := Fin d) T (algebraMap ℤ_[l] ↥(OL LL)) (algebraMap_OL LL)
    (exists_multiple_OL LL)
  obtain ⟨bV, h⟩ := H b
  refine ⟨bV, fun g i j => ?_⟩
  exact (hb g i j).trans (congrArg (algebraMap ℚ_[l] (PadicComplex l)) (h g i j))

end GlobalTheory.Cyc.LatBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowSmulMemOL
section
namespace GlobalTheory.IntegerRingPowers

open Formalism.BasicNotions

theorem exists_pow_smul_mem_OL {l : ℕ} [Fact (Nat.Prime l)] (LL : Loc.FinExt l) (a : ↥LL.1) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n * a ∈ Loc.OL LL := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hint : IsIntegral ℚ_[l] a := IsIntegral.of_finite ℚ_[l] a
  obtain ⟨⟨m, hm⟩, hmi⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ_[l]) a hint
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  refine ⟨m.valuation, ?_⟩
  rw [Loc.OL, mem_integralClosure_iff]
  have hmi' : IsIntegral ℤ_[l] (m • a) := hmi
  have e := PadicInt.unitCoeff_spec hm0
  set u := PadicInt.unitCoeff hm0
  have key : (l : ↥LL.1) ^ m.valuation * a = ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • (m • a) := by
    conv_rhs => rw [e]
    rw [smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Algebra.smul_def, map_pow, map_natCast]
  rw [key]
  exact IsIntegral.smul _ hmi'

theorem smul_mem_of_mem_OL {l : ℕ} [Fact (Nat.Prime l)] {K LL : Loc.FinExt l}
    (T : LocLat ↥(Loc.GK K) ℚ_[l] ↥LL.1 ↥(Loc.OL LL)) {c : ↥LL.1} (hc : c ∈ Loc.OL LL)
    {w : T.V} (hw : w ∈ T.L.T) : c • w ∈ T.L.T := by
  have h := T.L.T.smul_mem (⟨c, hc⟩ : ↥(Loc.OL LL)) hw
  have e := T.towO.smul_assoc (⟨c, hc⟩ : ↥(Loc.OL LL)) (1 : ↥LL.1) w
  have e2 : ((⟨c, hc⟩ : ↥(Loc.OL LL)) • (1 : ↥LL.1)) = c := by
    rw [Algebra.smul_def, mul_one]; rfl
  rw [e2, one_smul] at e
  rw [e]; exact h

theorem natCast_pow_mem_OL {l : ℕ} [Fact (Nat.Prime l)] (LL : Loc.FinExt l) (k : ℕ) :
    (l : ↥LL.1) ^ k ∈ Loc.OL LL :=
  (Loc.OL LL).pow_mem ((Loc.OL LL).natCast_mem l) k

theorem pow_smul_smul_eq {l : ℕ} [Fact (Nat.Prime l)] {K LL : Loc.FinExt l}
    (T : LocLat ↥(Loc.GK K) ℚ_[l] ↥LL.1 ↥(Loc.OL LL)) (a : ↥LL.1) (x : T.V) (k n : ℕ) :
    (l : ↥LL.1) ^ (k + n) • a • x = ((l : ↥LL.1) ^ k * a) • ((l : ↥LL.1) ^ n • x) := by
  rw [pow_add, mul_smul, mul_smul]
  congr 1
  rw [← mul_smul, ← mul_smul, mul_comm]

theorem main : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (K LL : Formalism.BasicNotions.Loc.FinExt l)
    (T : Formalism.BasicNotions.LocLat ↥(Formalism.BasicNotions.Loc.GK K) ℚ_[l]
      ↥(↑LL : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↥(Formalism.BasicNotions.Loc.OL LL))
    (v : Formalism.BasicNotions.LocLat.V T),
    ∃ (n : ℕ), (↑l : ↥(↑LL : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l))) ^ n • v ∈
      Formalism.WeaklyAdmissibleFiltrations.Lattice.T (Formalism.BasicNotions.LocLat.L T) := by
  intro l _ K LL T v
  have hv : v ∈ Submodule.span ↥LL.1 (T.L.T : Set T.V) := by
    rw [T.L.span]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by rw [pow_zero, one_smul]; exact hx⟩
  | zero => exact ⟨0, by rw [smul_zero]; exact T.L.T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨k, hk⟩ := hy
    refine ⟨n + k, ?_⟩
    rw [smul_add]
    refine T.L.T.add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact smul_mem_of_mem_OL T (natCast_pow_mem_OL LL k) hn
    · rw [pow_add, mul_smul]
      exact smul_mem_of_mem_OL T (natCast_pow_mem_OL LL n) hk
  | smul a x _ hx =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨k, hk⟩ := exists_pow_smul_mem_OL LL a
    refine ⟨k + n, ?_⟩
    rw [pow_smul_smul_eq T a x k n]
    exact smul_mem_of_mem_OL T hk hn

end GlobalTheory.IntegerRingPowers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubBasis
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open Matrix

noncomputable section

namespace GlobalTheory.TauFrame

theorem exists_sub_basis {C : Type} [Field C] {d r : ℕ} (f : Fin d → Fin r → C)
    (hf : Submodule.span C (Set.range f) = ⊤) :
    ∃ κ : Fin r → Fin d, LinearIndependent C (fun k => f (κ k)) := by
  obtain ⟨ι, a, ha, hsp, hli⟩ := exists_linearIndependent' C f
  haveI : Finite ι := Finite.of_injective a ha
  haveI := Fintype.ofFinite ι
  have hb := Module.finrank_eq_card_basis (Module.Basis.mk hli (by rw [hsp, hf]))
  rw [Module.finrank_fin_fun] at hb
  let e : Fin r ≃ ι := (Fintype.equivFinOfCardEq hb.symm).symm
  exact ⟨a ∘ e, hli.comp e e.injective⟩

section Norm

variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem norm_sum_le {n : ℕ} (f : Fin n → C) {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, ‖f i‖ ≤ c) :
    ‖∑ i, f i‖ ≤ c :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc (fun i _ => h i)

theorem norm_mul_le {a b c : ℕ} (A : Matrix (Fin a) (Fin b) C) (B : Matrix (Fin b) (Fin c) C)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hA : ∀ i j, ‖A i j‖ ≤ x) (hB : ∀ i j, ‖B i j‖ ≤ y) (i j) :
    ‖(A * B) i j‖ ≤ x * y := by
  rw [Matrix.mul_apply]
  refine norm_sum_le _ (mul_nonneg hx hy) fun k => ?_
  rw [norm_mul]
  exact mul_le_mul (hA _ _) (hB _ _) (norm_nonneg _) hx

theorem norm_mulVec_le {a b : ℕ} (A : Matrix (Fin a) (Fin b) C) (v : Fin b → C)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1) (i) : ‖A.mulVec v i‖ ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  refine norm_sum_le _ zero_le_one fun k => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA _ _) (norm_nonneg _) (hv _)

theorem exists_bound_lt {a : ℕ} (A : Matrix (Fin a) (Fin a) C) {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ i j, ‖A i j‖ < ρ) : ∃ x, 0 ≤ x ∧ x < ρ ∧ ∀ i j, ‖A i j‖ ≤ x := by
  refine ⟨‖fun p : Fin a × Fin a => A p.1 p.2‖, norm_nonneg _, ?_, fun i j => ?_⟩
  · exact (pi_norm_lt_iff hρ).2 fun p => h _ _
  · exact norm_le_pi_norm (fun p : Fin a × Fin a => A p.1 p.2) (i, j)

end Norm

theorem mem_mul {C : Type} [Field C] (F : Subfield C) {a b c : ℕ} (A : Matrix (Fin a) (Fin b) C)
    (B : Matrix (Fin b) (Fin c) C) (hA : ∀ i j, A i j ∈ F) (hB : ∀ i j, B i j ∈ F) (i j) :
    (A * B) i j ∈ F := by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hA _ _) (hB _ _)

variable {l : ℕ} [Fact l.Prime]

def subC (F : IntermediateField ℚ_[l] (Om l)) : Subfield (PadicComplex l) :=
  F.toSubfield.map (algebraMap (Om l) (PadicComplex l))

theorem mem_subC {F : IntermediateField ℚ_[l] (Om l)} {y : PadicComplex l} :
    y ∈ subC F ↔ y ∈ inC F := Iff.rfl

theorem act_fix {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {F : IntermediateField ℚ_[l] (Om l)} {σ : GQ l} (hσ : σ ∈ F.fixingSubgroup)
    {y : PadicComplex l} (hy : y ∈ subC F) : act σ y = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  have h1 := ha.1 σ x
  have h2 : σ x = x := hσ ⟨x, hx⟩
  rw [h2] at h1
  exact h1

theorem map_mul' {a b c : ℕ} (f : PadicComplex l ≃+* PadicComplex l)
    (A : Matrix (Fin a) (Fin b) (PadicComplex l)) (B : Matrix (Fin b) (Fin c) (PadicComplex l)) :
    (A * B).map f = A.map f * B.map f := by
  ext i j
  simp [Matrix.mul_apply]

theorem frame_of_idem (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (ha : IsActC act) (K : FinExt l) (m d r : ℕ)
    (M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (Dm E : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l) (hD : IsDec act χ K m M Dm U g)
    (hEM : ∀ σ ∈ Gj K m, E * M σ = M σ * E) (hEσ : ∀ σ ∈ Gj K m, E.map (act σ) = E)
    (hEF : ∀ i j, (Dm⁻¹ * E * Dm) i j ∈ subC (Ks K m))
    (R : Matrix (Fin r) (Fin d) (PadicComplex l)) (S : Matrix (Fin d) (Fin r) (PadicComplex l))
    (hR : ∀ i j, R i j ∈ subC (Ks K m) ∧ ‖R i j‖ ≤ 1)
    (hS : ∀ i j, S i j ∈ subC (Ks K m) ∧ ‖S i j‖ ≤ 1)
    (hRS : R * S = 1) (hRe : R * (Dm⁻¹ * E * Dm) = R) (heSR : (Dm⁻¹ * E * Dm) * S * R = Dm⁻¹ * E * Dm)
    (e : Fin d → Fin d → PadicComplex l) (u : Fin d → ℤ) (hli : LinearIndependent (PadicComplex l) e)
    (hfix : ∀ σ ∈ Gj K m, ∀ k, twAct act χ (u k) M σ (e k) = e k) (J : Set ℤ)
    (hJ : ∀ k, E.mulVec (e k) ≠ 0 → u k ∈ J) :
    Frame χ K m (fun σ => R * U σ * S) g ∧ HTBasis act χ (Gj K m) (fun σ => R * U σ * S) J ∧
    (∀ σ ∈ Gj K m, (R * Dm⁻¹) * M σ = (R * U σ * S) * (R * Dm⁻¹).map (act σ)) ∧
    ball l r ⊆ (R * Dm⁻¹).mulVec '' ball l d ∧
    (∀ x ∈ ball l d, (l : PadicComplex l) • (R * Dm⁻¹).mulVec x ∈ ball l r) ∧
    ∃ Q : Matrix (Fin d) (Fin r) (PadicComplex l), Q * (R * Dm⁻¹) = E := by
  obtain ⟨hdet, hDi, hDl, ⟨hgen, hcont, hint, hmul, hH, hg⟩, hrel⟩ := hD
  set e' := Dm⁻¹ * E * Dm with he'
  have h1 : Dm * Dm⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have h2 : Dm⁻¹ * Dm = 1 := Matrix.nonsing_inv_mul _ hdet
  have hDe : Dm * e' = E * Dm := by
    rw [he', ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hfixm : ∀ σ ∈ Gj K m, ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) (PadicComplex l)),
      (∀ i j, X i j ∈ subC (Ks K m)) → X.map (act σ) = X := by
    intro σ hσ a b X hX
    ext i j
    exact act_fix ha hσ (hX i j)
  have hcomm : ∀ σ ∈ Gj K m, e' * U σ = U σ * e' := by
    intro σ hσ
    have : Dm * (e' * U σ) = Dm * (U σ * e') := by
      rw [← Matrix.mul_assoc, hDe, Matrix.mul_assoc, hrel σ hσ, ← Matrix.mul_assoc, hEM σ hσ,
        Matrix.mul_assoc, ← Matrix.mul_assoc Dm, hrel σ hσ, Matrix.mul_assoc]
      congr 1
      conv_lhs => rw [← hEσ σ hσ]
      conv_rhs => rw [← hfixm σ hσ e' hEF]
      rw [← map_mul', ← map_mul', hDe]
    have h3 := congrArg (fun X => Dm⁻¹ * X) this
    simpa only [← Matrix.mul_assoc, h2, Matrix.one_mul] using h3
  have hkey : ∀ σ ∈ Gj K m, R * U σ * S * R = R * U σ := by
    intro σ hσ
    have h3 : R * U σ = R * U σ * e' := by
      rw [Matrix.mul_assoc, ← hcomm σ hσ, ← Matrix.mul_assoc, hRe]
    calc R * U σ * S * R = R * U σ * (e' * S * R) := by
          conv_lhs => rw [h3]
          simp only [Matrix.mul_assoc]
      _ = R * U σ := by rw [heSR, ← h3]
  have heq : ∀ σ ∈ Gj K m, (R * Dm⁻¹) * M σ = (R * U σ * S) * (R * Dm⁻¹).map (act σ) := by
    intro σ hσ
    have h3 : Dm.map (act σ) * Dm⁻¹.map (act σ) = 1 := by
      rw [← map_mul', h1]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have h4 : Dm⁻¹ * M σ = U σ * Dm⁻¹.map (act σ) := by
      calc Dm⁻¹ * M σ = Dm⁻¹ * (M σ * Dm.map (act σ)) * Dm⁻¹.map (act σ) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, h3, Matrix.mul_one]
        _ = _ := by rw [← hrel σ hσ, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [map_mul', hfixm σ hσ R (fun i j => (hR i j).1), ← Matrix.mul_assoc, hkey σ hσ,
      Matrix.mul_assoc, h4, Matrix.mul_assoc]
  have hsec : R * Dm⁻¹ * (Dm * S) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Dm⁻¹, h2, Matrix.one_mul, hRS]
  refine ⟨⟨hgen, ?_, ?_, ?_, ?_, ?_⟩, ?_, heq, ?_, ?_, ?_⟩
  · intro a b
    simp only [Matrix.mul_apply]
    refine continuousOn_finset_sum _ fun k _ => ContinuousOn.mul ?_ continuousOn_const
    exact continuousOn_finset_sum _ fun j _ => ContinuousOn.mul continuousOn_const (hcont _ _)
  · intro σ hσ a b
    refine ⟨mem_subC.1 (mem_mul _ _ _ (mem_mul _ _ _ (fun i j => (hR i j).1)
      (fun i j => mem_subC.2 (hint σ hσ i j).1)) (fun i j => (hS i j).1) a b), ?_⟩
    have := norm_mul_le (R * U σ) S (mul_nonneg zero_le_one zero_le_one) zero_le_one
      (norm_mul_le R (U σ) zero_le_one zero_le_one (fun i j => (hR i j).2)
        (fun i j => (hint σ hσ i j).2)) (fun i j => (hS i j).2) a b
    simpa using this
  · intro σ hσ τ hτ
    simp only
    rw [hmul σ hσ τ hτ, ← Matrix.mul_assoc (R * U σ * S), ← Matrix.mul_assoc (R * U σ * S),
      hkey σ hσ]
    simp only [Matrix.mul_assoc]
  · intro σ hσ
    simp only
    rw [hH σ hσ, Matrix.mul_one, hRS]
  · intro a b
    have hrho : 0 < rho1 l :=
      Real.rpow_pos_of_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
    obtain ⟨x, hx0, hx, hxb⟩ := exists_bound_lt (U g - 1) hrho hg
    have h3 : R * U g * S - 1 = R * (U g - 1) * S := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hRS]
    simp only
    rw [h3]
    have := norm_mul_le (R * (U g - 1)) S (mul_nonneg zero_le_one hx0) zero_le_one
      (norm_mul_le R (U g - 1) zero_le_one hx0 (fun i j => (hR i j).2) hxb)
      (fun i j => (hS i j).2) a b
    exact lt_of_le_of_lt (by simpa using this) hx
  · set Pm := R * Dm⁻¹ with hPm
    have hsp : Submodule.span (PadicComplex l) (Set.range fun k => Pm.mulVec (e k)) = ⊤ := by
      have h3 : Submodule.span (PadicComplex l) (Set.range e) = ⊤ :=
        hli.span_eq_top_of_card_eq_finrank' (by simp)
      have h4 : (Set.range fun k => Pm.mulVec (e k)) = Pm.mulVecLin '' Set.range e := by
        rw [← Set.range_comp]; rfl
      rw [h4, ← Submodule.map_span, h3, Submodule.map_top, LinearMap.range_eq_top]
      intro y
      refine ⟨(Dm * S).mulVec y, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hsec, Matrix.one_mulVec]
    obtain ⟨κ, hκ⟩ := exists_sub_basis _ hsp
    refine ⟨fun k => Pm.mulVec (e (κ k)), fun k => u (κ k), hκ, fun k => hJ _ fun h0 => ?_, ?_⟩
    · apply hκ.ne_zero k
      have h3 : Pm * E = Pm := by
        calc Pm * E = R * e' * Dm⁻¹ := by
              rw [hPm, he']; simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
          _ = Pm := by rw [hRe]
      show Pm.mulVec (e (κ k)) = 0
      rw [← h3, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
    · intro σ hσ k
      have h3 := hfix σ hσ (κ k)
      unfold twAct at h3 ⊢
      have hmap : (fun a => act σ (Pm.mulVec (e (κ k)) a)) =
          (Pm.map (act σ)).mulVec (fun a => act σ (e (κ k) a)) := by
        funext a
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
      simp only
      rw [hmap, Matrix.mulVec_mulVec, ← heq σ hσ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, h3]
  · intro y hy
    refine ⟨Dm.mulVec (S.mulVec y), norm_mulVec_le _ _ hDi
      (norm_mulVec_le _ _ (fun i j => (hS i j).2) hy), ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hsec, Matrix.one_mulVec]
  · intro x hx
    have h3 : (l : PadicComplex l) • (R * Dm⁻¹).mulVec x =
        R.mulVec (((l : PadicComplex l) • Dm⁻¹).mulVec x) := by
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
    rw [h3]
    exact norm_mulVec_le _ _ (fun i j => (hR i j).2) (norm_mulVec_le _ _ (fun i j => hDl i j) hx)
  · refine ⟨Dm * e' * S, ?_⟩
    calc Dm * e' * S * (R * Dm⁻¹) = Dm * (e' * S * R) * Dm⁻¹ := by simp only [Matrix.mul_assoc]
      _ = E := by rw [heSR, hDe, Matrix.mul_assoc, h1, Matrix.mul_one]

end GlobalTheory.TauFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTmulOneOfFrobFixedOfMemFilZero
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem equivFinsuppOfBasisLeft_lTensor_apply {F : Type} [Field F] {V M N : Type}
    [AddCommGroup V] [Module F V] [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    {ι : Type} [DecidableEq ι] (b : Module.Basis ι F V) (f : M →ₗ[F] N) (x : V ⊗[F] M) (i : ι) :
    equivFinsuppOfBasisLeft b (f.lTensor V x) i = f (equivFinsuppOfBasisLeft b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v m => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem algebraTensorModule_map_id_apply {F L : Type} [Field F] [Field L] [Algebra F L]
    {V M N : Type} [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    (f : M →ₗ[F] N) (x : V ⊗[F] M) :
    AlgebraTensorModule.map (LinearMap.id : V →ₗ[L] V) f x = f.lTensor V x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v m => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem exists_tmul_one_of_frob_fixed_of_mem_fil_zero :
    ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (x : V ⊗[Qp] B), φVB PD (LL := LL) (V := V) x = x → ιV PD (LL := LL) (V := V) x ∈ FilV PD (LL := LL) (V := V) 0 → ∃ v : V, x = v ⊗ₜ[Qp] (1 : B) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ x hφ hF
  classical
  let b := Module.Basis.ofVectorSpace Qp V
  have key : ∀ i, ∃ c : Qp, algebraMap Qp B c = equivFinsuppOfBasisLeft b x i := by
    intro i
    apply PD.fund
    · have h := equivFinsuppOfBasisLeft_lTensor_apply b PD.φ.toLinearMap x i
      rw [← algebraTensorModule_map_id_apply (L := LL)] at h
      have h2 : AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) PD.φ.toLinearMap x = x := hφ
      rw [h2] at h
      exact h.symm
    · obtain ⟨y, hy⟩ := hF
      have h := equivFinsuppOfBasisLeft_lTensor_apply b
        (PD.ι.toLinearMap.restrictScalars Qp) x i
      rw [← algebraTensorModule_map_id_apply (L := LL)] at h
      have h' := equivFinsuppOfBasisLeft_lTensor_apply b
        ((PD.Fil 0).restrictScalars Qp).subtype y i
      rw [← algebraTensorModule_map_id_apply (L := LL), hy] at h'
      have h3 : PD.ι (equivFinsuppOfBasisLeft b x i)
          = ((PD.Fil 0).restrictScalars Qp).subtype (equivFinsuppOfBasisLeft b y i) :=
        h.symm.trans h'
      rw [h3]
      exact (equivFinsuppOfBasisLeft b y i).2
  choose c hc using key
  refine ⟨∑ i ∈ (equivFinsuppOfBasisLeft b x).support, c i • b i, ?_⟩
  have hx : x = (equivFinsuppOfBasisLeft b).symm (equivFinsuppOfBasisLeft b x) := by simp
  rw [equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum] at hx
  rw [TensorProduct.sum_tmul]
  refine hx.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [← hc i, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotForallExistsTwoLiesOverAbsNormEqStatement
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_forall_exists_two_degree_one_primes_over : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ¬ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∃ P P' : HeightOneSpectrum (𝓞 M), P ≠ P' ∧ P.asIdeal.LiesOver v.asIdeal ∧ P'.asIdeal.LiesOver v.asIdeal ∧ Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm P'.asIdeal = Ideal.absNorm v.asIdeal := by
  first | exact @GlobalTheory.not_forall_exists_two_liesOver_absNorm_eq | exact GlobalTheory.not_forall_exists_two_liesOver_absNorm_eq | (intros; apply GlobalTheory.not_forall_exists_two_liesOver_absNorm_eq <;> assumption)
end

