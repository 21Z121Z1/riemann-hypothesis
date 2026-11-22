import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0107

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrystallineCocycles
section
noncomputable section

namespace GlobalTheory.HyodoDef

open Formalism.WeaklyAdmissibleFiltrations TensorProduct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)
    [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

def geometricCocycles : Submodule LL (G → V) where
  carrier := {c | c ∈ continuousCocycles ρ ∧ ∃ b : V ⊗[Qp] BdR, ∀ g, c g ⊗ₜ[Qp] (1 : BdR) = actVdR PD ρ g b - b}
  zero_mem' := ⟨(continuousCocycles ρ).zero_mem, 0, fun g => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, x, hx⟩ ⟨hb, y, hy⟩
    refine ⟨(continuousCocycles ρ).add_mem ha hb, x + y, fun g => ?_⟩
    simp only [Pi.add_apply, add_tmul, hx, hy, map_add]
    abel
  smul_mem' := by
    rintro c a ⟨ha, x, hx⟩
    refine ⟨(continuousCocycles ρ).smul_mem c ha, c • x, fun g => ?_⟩
    simp only [Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl

def crystallineCocycles : Submodule LL (G → V) where
  carrier := {c | c ∈ continuousCocycles ρ ∧ ∃ x : V ⊗[Qp] B, φVB PD (LL := LL) (V := V) x = x ∧
    ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x}
  zero_mem' := ⟨(continuousCocycles ρ).zero_mem, 0, map_zero _, fun g => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, x, hxφ, hx⟩ ⟨hb, y, hyφ, hy⟩
    refine ⟨(continuousCocycles ρ).add_mem ha hb, x + y, by rw [map_add, hxφ, hyφ], fun g => ?_⟩
    simp only [Pi.add_apply, add_tmul, hx, hy, map_add]
    abel
  smul_mem' := by
    rintro c a ⟨ha, x, hxφ, hx⟩
    refine ⟨(continuousCocycles ρ).smul_mem c ha, c • x, by rw [map_smul, hxφ], fun g => ?_⟩
    simp only [Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl

end GlobalTheory.HyodoDef

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
section
noncomputable section

namespace GlobalTheory.NL

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def conv {M : Type} [AddCommGroup M] [Module LL M] (e : PowerSeries LL) (f : ℤ → M) : ℤ → M :=
  fun k => ∑ᶠ j : ℕ, PowerSeries.coeff j e • f (k - j)

def latSpan {M ι : Type} [AddCommGroup M] [Module LL M] (ex : ι → ℤ → M) : Submodule LL (ℤ → M) :=
  Submodule.span LL {f | ∃ (e : PowerSeries LL) (x : ι), f = conv e (ex x)}

def Full {M : Type} [AddCommGroup M] [Module LL M] (D : Submodule LL M) (Λ : Submodule LL (ℤ → M)) : Prop :=
  ∃ m : ℕ, ∀ f : ℤ → M, (∀ k, f k ∈ D) → (∀ k < (m : ℤ), f k = 0) → f ∈ Λ

def Std {M : Type} [AddCommGroup M] [Module LL M] (D : Submodule LL M) (Λ : Submodule LL (ℤ → M)) : Prop :=
  ∀ f : ℤ → M, f ∈ Λ ↔ (∀ k, f k ∈ D) ∧ ∀ k < (0 : ℤ), f k = 0

def Graded {M : Type} [AddCommGroup M] [Module LL M] (Λ : Submodule LL (ℤ → M)) : Prop :=
  ∀ f : ℤ → M, f ∈ Λ ↔ (∃ m : ℤ, ∀ k < m, f k = 0) ∧ ∀ k, Pi.single k (f k) ∈ Λ

variable (PD) in

def FilAt (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) (a : ℤ) : Submodule LL (T.V ⊗[Qp] BdR) :=
  FildR PD T.ρ τ a ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ'

def van (W : LocWach PD LL O v n) (i : ZMod n) (ζ : LL) (k : ℕ) : Ideal (LetA O n) :=
  (Ideal.span {(PowerSeries.X : PowerSeries LL) ^ k}).comap (W.lev i ζ)

end Generic

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} {F : LocFon l P AI H}
  {K : FinExt l} {s : ℕ} {LL : FinExt l}

abbrev Lt (K LL : FinExt l) : Type 1 := LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)

abbrev Let (K : FinExt l) : Type := ZMod (Module.finrank ℚ_[l] ↥(K0 K))

abbrev AA (K LL : FinExt l) : Type := LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))

abbrev Di (H : LocHW l P) (h : Good K s LL) (T : Lt K LL) (i : Let K) : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.B) :=
  DcrisL (P.PD K) T.ρ ((H.W K s LL h).emb i)

def ex (C : LocCmpT l P AI H F) (h : Good K s LL) (T : Lt K LL) (i : Let K) (ζ : ↥LL.1)
    (x : ↥((H.W K s LL h).N T)) : ℤ → T.V ⊗[ℚ_[l]] P.R.B :=
  (C.C K s LL h).tie.levB T i ζ x

def Lat (C : LocCmpT l P AI H F) (h : Good K s LL) (T : Lt K LL) (i : Let K) (ζ : ↥LL.1) :
    Submodule ↥LL.1 (ℤ → T.V ⊗[ℚ_[l]] P.R.B) :=
  latSpan (ex C h T i ζ)

def Pt (H : LocHW l P) (h : Good K s LL) (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) : Prop :=
  ∃ τs : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1, H.IsPt h i ζ τs ∧
    ∀ (x : ↥K.1) (y : ↥(Ks K s)), (y : Om l) = (x : Om l) → τ x = τs y

def Comp (H : LocHW l P) (h : Good K s LL) (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) : Prop :=
  (∀ c : ↥(K0 K), ι ((H.W K s LL h).emb i c) = algebraMap ↥(K0 K) P.R.BdR c) ∧
    ι ζ = algebraMap (Om l) P.R.BdR (P.ζQ s) ∧ ∀ c : ↥K.1, ι (τ c) = algebraMap ↥K.1 P.R.BdR c

def tS (P : LocPrime l) (s : ℕ) : P.R.BdR := (((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB

end Concrete

end GlobalTheory.NL
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ValIrreducible
section
noncomputable section

namespace GlobalTheory.UnitLemma.Basic

variable {K : UQ} (B : InvAlg K)

variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
private theorem sigma_smul_eq_conj_smul (e : K.E) (v : B.A) : B.σ (e • v) = K.c e • B.σ v := by
  rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]

variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in

theorem _root_.GlobalTheory.UnitLemma.Basic.trace_sigma (u : B.A) :
    Algebra.trace K.E B.A (B.σ u) = K.c (Algebra.trace K.E B.A u) := by
  classical
  set b := Module.finBasis K.E B.A
  let φ : B.A ≃ₗ[K.E] (Fin (Module.finrank K.E B.A) → K.E) :=
    { toFun := fun v i => K.c (b.repr (B.σ v) i)
      map_add' := fun v w => by ext i; simp
      map_smul' := fun e v => by ext i; simp [sigma_smul_eq_conj_smul, K.c_c]
      invFun := fun f => B.σ (∑ i, K.c (f i) • b i)
      left_inv := fun v => by
        simp only [K.c_c, b.sum_repr, B.σ_σ]
      right_inv := fun f => by
        ext i
        simp [B.σ_σ, Finsupp.single_apply, K.c_c] }
  let b' := Module.Basis.ofEquivFun φ
  have hb' (j) : b' j = B.σ (b j) := by
    simp [b', Module.Basis.coe_ofEquivFun, φ, Pi.single_apply, apply_ite B.σ]
  have hrepr (w : B.A) (i) : b'.repr w i = K.c (b.repr (B.σ w) i) := by
    simp [b', φ]
  rw [Algebra.trace_eq_matrix_trace b' (B.σ u), Algebra.trace_eq_matrix_trace b u,
    Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
    Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', hb', hrepr, ← map_mul, B.σ_σ]

variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in

theorem _root_.GlobalTheory.UnitLemma.Basic.herm_smul_left (x y z : B.A) (e : K.E) :
    B.herm x (e • y) z = e * B.herm x y z := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]

variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in

theorem _root_.GlobalTheory.UnitLemma.Basic.herm_smul_right (x y z : B.A) (e : K.E) :
    B.herm x y (e • z) = K.c e * B.herm x y z := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [sigma_smul_eq_conj_smul, mul_smul_comm, map_smul, smul_eq_mul]

variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in

theorem _root_.GlobalTheory.UnitLemma.Basic.herm_symm (x : B.A) (hx : B.σ x = x) (y z : B.A) :
    B.herm x z y = K.c (B.herm x y z) := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [← _root_.GlobalTheory.UnitLemma.Basic.trace_sigma, map_mul B.σ, map_mul B.σ, hx, B.σ_σ]
  congr 1
  ring

variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in

theorem _root_.GlobalTheory.UnitLemma.Basic.herm_mul_left (x u y z : B.A) :
    B.herm x (u * y) z = B.herm x y (B.σ u * z) := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [map_mul B.σ, B.σ_σ]
  congr 1
  ring

variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in

theorem _root_.GlobalTheory.UnitLemma.Basic.herm_norm (x u y z : B.A) :
    B.herm (x * (u * B.σ u)) y z = B.herm x (u * y) (u * z) := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [map_mul B.σ]
  congr 1
  ring

end GlobalTheory.UnitLemma.Basic
end
end

