import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Formalism.LatticeTheta.Statement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0174
import GroundTheory.Brauer.TensorSimple
import Development.AbelianVarietyTheory.Definitions.Divisors.PlacesOverU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0155

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeImageEqLatticeImageTraceDual
section
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.LipschitzTR

section
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem inner_remb_eq_trace (a b : F) :
    ⟪remb F a, remb F b⟫ = ((Algebra.trace ℚ F (a * b) : ℚ) : ℝ) := by
  rw [GlobalTheory.trace_eq_sum_realEmbeddings, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [map_mul, mul_comm]

theorem remb_mem_dual_latOf_iff (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0) (ν : F) :
    remb F ν ∈ Formalism.H.dual (latOf N) ↔ ν ∈ FractionalIdeal.dual ℤ ℚ N := by
  rw [Formalism.H.dual, LinearMap.BilinForm.mem_dualSubmodule, FractionalIdeal.mem_dual hN]
  constructor
  · intro h a ha
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp (h (remb F a) ((mem_latOf N _).mpr ⟨a, ha, rfl⟩))
    refine ⟨z, ?_⟩
    rw [Algebra.traceForm_apply]
    have : ((z : ℚ) : ℝ) = ((Algebra.trace ℚ F (ν * a) : ℚ) : ℝ) := by
      have h2 : ((z : ℤ) : ℝ) = ⟪remb F ν, remb F a⟫ := by simpa using hz
      rw [inner_remb_eq_trace] at h2
      exact_mod_cast h2
    exact_mod_cast this
  · intro h y hy
    obtain ⟨a, ha, rfl⟩ := (mem_latOf N y).mp hy
    obtain ⟨z, hz⟩ := h a ha
    rw [Algebra.traceForm_apply] at hz
    refine Submodule.mem_one.mpr ⟨z, ?_⟩
    rw [show (innerₗ (RSp F)) (remb F ν) (remb F a) = ⟪remb F ν, remb F a⟫ from rfl,
      inner_remb_eq_trace, ← hz]
    simp

theorem exists_remb_eq_of_mem_dual {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ F)
    (N : FractionalIdeal (𝓞 F)⁰ F) (hbN : ∀ i, b i ∈ N) (μ : RSp F)
    (hμ : μ ∈ Formalism.H.dual (latOf N)) : ∃ ν : F, remb F ν = μ := by
  set B := Algebra.traceForm ℚ F
  have hB : B.Nondegenerate := traceForm_nondegenerate ℚ F
  set b' := B.dualBasis hB b
  have hdel : ∀ i j, Algebra.trace ℚ F (b' j * b i) = if i = j then 1 else 0 := fun i j => by
    have := LinearMap.BilinForm.apply_dualBasis_left hB b j i
    rwa [Algebra.traceForm_apply] at this
  have hc : ∀ i, ∃ z : ℤ, ⟪μ, remb F (b i)⟫ = z := fun i => by
    have := (LinearMap.BilinForm.mem_dualSubmodule _).mp hμ (remb F (b i))
      ((mem_latOf N _).mpr ⟨b i, hbN i, rfl⟩)
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp this
    exact ⟨z, by simpa using hz.symm⟩
  choose c hc using hc
  set ν : F := ∑ j, (c j : ℚ) • b' j
  have hνb : ∀ i, ⟪remb F ν, remb F (b i)⟫ = c i := fun i => by
    rw [inner_remb_eq_trace]
    have : Algebra.trace ℚ F (ν * b i) = c i := by
      simp only [ν, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, hdel, smul_eq_mul,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [this]; simp
  have hind : LinearIndependent ℝ (fun i => remb F (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := congrArg (fun w => ⟪w, remb F (b' j)⟫) hg
    simp only [sum_inner, real_inner_smul_left, inner_remb_eq_trace, inner_zero_left] at this
    simp only [mul_comm (b _) (b' j), hdel] at this
    rw [Finset.sum_eq_single j (fun i _ hi => by rw [if_neg hi]; simp) (by simp)] at this
    simpa using this
  have hcard : Fintype.card ι = Module.finrank ℝ (RSp F) := by
    rw [finrank_euclideanSpace, GlobalTheory.card_realEmbeddings, Module.finrank_eq_card_basis b]
  haveI : Nonempty ι := b.index_nonempty
  let E := basisOfLinearIndependentOfCardEqFinrank hind hcard
  have hz : innerₛₗ ℝ (μ - remb F ν) = 0 := E.ext fun i => by
    simp [E, inner_sub_left, hνb, hc]
  have h0 := LinearMap.congr_fun hz (μ - remb F ν)
  have h1 : ⟪μ - remb F ν, μ - remb F ν⟫ = 0 := by
    rw [LinearMap.zero_apply] at h0; exact h0
  rw [inner_self_eq_zero, sub_eq_zero] at h1
  exact ⟨ν, h1.symm⟩

end

theorem dual_latOf_eq_latOf_traceDual (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0) :
    Formalism.H.dual (latOf N) = latOf (FractionalIdeal.dual ℤ ℚ N) := by
  classical
  ext μ
  constructor
  · intro hμ
    rw [mem_latOf]
    let I : (FractionalIdeal (𝓞 F)⁰ F)ˣ := Units.mk0 N hN
    have hbN : ∀ i, basisOfFractionalIdeal F I i ∈ N := fun i => by
      have := (mem_span_basisOfFractionalIdeal F (I := I) (x := basisOfFractionalIdeal F I i)).mp
        (Submodule.subset_span ⟨i, rfl⟩)
      simpa [I] using this
    obtain ⟨ν, hν⟩ := exists_remb_eq_of_mem_dual (basisOfFractionalIdeal F I) N hbN μ hμ
    subst hν
    exact ⟨ν, (remb_mem_dual_latOf_iff N hN ν).mp hμ, rfl⟩
  · intro hμ
    obtain ⟨ν, hν, rfl⟩ := (mem_latOf _ μ).mp hμ
    exact (remb_mem_dual_latOf_iff N hN ν).mpr hν

end GlobalTheory.LipschitzTR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenProjectionQuotientLattice
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem eig_projection_quotLattice (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C]
    (Λ : Type) [CommRing Λ] (h : ℕ) (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O)
    (hind : iSupIndep (fun σ : Λ →+* O => eig C ρ σ))
    (hspan : (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤) :
    ∃ π : (Fin h → C) →ₗ[C] eig C ρ τ, (∀ x : eig C ρ τ, π x = x) ∧
      (∀ (z : Fin h → C) (x : eig C ρ τ),
        (z - (x : Fin h → C) ∈ ⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ σ.1) ↔ x = π z) ∧
      quotLattice C ρ τ = Set.range (fun t : Fin h → O => π (fun i => algebraMap O C (t i))) := by
  set W : Submodule C (Fin h → C) := ⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ σ.1 with hW
  have hW' : W = ⨆ σ, ⨆ (_ : σ ≠ τ), eig C ρ σ := by
    rw [hW, iSup_subtype]
  have hc : IsCompl (eig C ρ τ) W := by
    constructor
    · rw [hW']; exact hind τ
    · rw [codisjoint_iff, hW', ← iSup_split_single (fun σ => eig C ρ σ) τ, hspan]
  set π := Submodule.projectionOnto (eig C ρ τ) W hc with hπ
  have key : ∀ (z : Fin h → C) (x : eig C ρ τ), (z - (x : Fin h → C) ∈ W) ↔ x = π z := by
    intro z x
    rw [← Submodule.projectionOnto_apply_eq_zero_iff hc, map_sub,
      Submodule.projectionOnto_apply_left, sub_eq_zero, eq_comm]
  refine ⟨π, fun x => Submodule.projectionOnto_apply_left hc x, key, ?_⟩
  ext x
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, ((key _ x).1 ht).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, (key _ _).2 rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenSublatticeFreeLatticeIffEval
section
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.EigenSubEval

variable {C : Type} [Field C] {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)}
  {S : Type} [Fintype S] [DecidableEq S]

theorem evalVec_rsmul (b : S → Int0 v) (N : ℕ) (r : RS b) (z : Fin N → RS b) (s : S) (i : Fin N) :
    evalVec b N (r • z) s i = ((ev b s r : Int0 v) : C) * evalVec b N z s i := by
  simp only [evalVec, Pi.smul_apply, smul_eq_mul, map_mul, Subring.coe_mul]

theorem mem_eigSub_iff (b : S → Int0 v) (N : ℕ) (τ : S) (z : Fin N → RS b) :
    z ∈ eigSub b τ (Fin N → RS b) ↔ lin b τ • z = 0 := Iff.rfl

theorem eigenSub_iff_eval (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ) (τ : S) (ha : Function.Injective a)
    (hinj : Function.Injective (evalVec (liftA hv a) N))
    (hrange : ∀ y, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y)
    (y : Fin N → C) :
    y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin N → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) τ ↔
      ∃ z ∈ eigSub (liftA hv a) τ (Fin N → RS (liftA hv a)),
        (fun i => ((comp (liftA hv a) N τ z i : Int0 v) : C)) = y := by
  have hev : ∀ s t, ((ev (liftA hv a) s (lin (liftA hv a) t) : Int0 v) : C) = (a s : C) - a t := by
    intro s t
    rw [ev_lin]; rfl
  have hne : ∀ s, s ≠ τ → (a s : C) - a τ ≠ 0 := by
    intro s hs h
    exact hs (ha (Subtype.ext (sub_eq_zero.1 h)))
  have hmem : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin N → C)
      (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) τ ↔
      (Pi.single τ y : S → Fin N → C) ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N := Iff.rfl
  rw [hmem]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := (hrange _).1 h
    refine ⟨x, ?_, ?_⟩
    · rw [mem_eigSub_iff]
      apply hinj
      funext s i
      rw [evalVec_rsmul, hev, hx]
      have h0 : evalVec (liftA hv a) N (0 : Fin N → RS (liftA hv a)) s i = 0 := by
        simp [evalVec]
      rw [h0]
      by_cases e : s = τ
      · subst e; simp
      · simp [e]
    · rw [comp_coe, hx]; simp
  · rintro ⟨z, hz, rfl⟩
    rw [mem_eigSub_iff] at hz
    have key : evalVec (liftA hv a) N z = Pi.single τ (evalVec (liftA hv a) N z τ) := by
      funext s i
      by_cases e : s = τ
      · subst e; simp
      · have h1 := congrFun (congrFun (congrArg (evalVec (liftA hv a) N) hz) s) i
        rw [evalVec_rsmul, hev] at h1
        have h0 : evalVec (liftA hv a) N (0 : Fin N → RS (liftA hv a)) s i = 0 := by
          simp [evalVec]
        rw [h0] at h1
        rw [Pi.single_eq_of_ne e]
        exact (mul_eq_zero.1 h1).resolve_left (hne s e)
    rw [comp_coe, ← key]
    exact (hrange _).2 ⟨z, rfl⟩

end GlobalTheory.EigenSubEval
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbOverSumInjective
section
open NumberField Matrix GlobalTheory.UPel.HT
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.UPel.HT.RealRepBij

end GlobalTheory.UPel.HT.RealRepBij

namespace GlobalTheory.UPel.HT.RealRepBij

theorem span_range_eq_top {F B : Type} [Field F] [Ring B] [Algebra F B] [Algebra.IsCentral F B]
    [IsSimpleRing B] [FiniteDimensional F B] {n : ℕ} (σ : F →+* ℂ)
    (f : B →+* Matrix (Fin n) (Fin n) ℂ) (hdim : Module.finrank F B = n ^ 2)
    (hf : ∀ a, f (algebraMap F B a) = Matrix.scalar (Fin n) (σ a)) :
    Submodule.span ℂ (Set.range f) = ⊤ := by
  letI : Algebra F ℂ := σ.toAlgebra
  have hg : ∀ a, f (algebraMap F B a) = algebraMap F (Matrix (Fin n) (Fin n) ℂ) a := fun a => by
    rw [hf, Matrix.algebraMap_eq_diagonal]; rfl
  let g : B →ₐ[F] Matrix (Fin n) (Fin n) ℂ := { f with commutes' := hg }
  let L : ℂ ⊗[F] B →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) g (fun r y => Algebra.commute_algebraMap_left r _)
  have hn : 0 < n := by
    have := Module.finrank_pos (R := F) (M := B)
    rw [hdim] at this
    exact Nat.pos_of_ne_zero fun h => by simp [h] at this
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hinj : Function.Injective L :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right
      (not_subsingleton _)
  have hdim' : Module.finrank ℂ (ℂ ⊗[F] B) = Module.finrank ℂ (Matrix (Fin n) (Fin n) ℂ) := by
    rw [Module.finrank_baseChange, hdim, Module.finrank_matrix, Module.finrank_self]
    simp [sq]
  have hsurj : Function.Surjective L.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').1 hinj
  refine eq_top_iff.2 fun m _ => ?_
  clear ‹m ∈ ⊤›
  obtain ⟨x, rfl⟩ := hsurj m
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c b =>
    have : L.toLinearMap (c ⊗ₜ b) = c • f b := by
      dsimp only [L]
      rw [AlgHom.toLinearMap_apply]
      erw [Algebra.TensorProduct.lift_tmul]
      rw [Algebra.ofId_apply, Algebra.smul_def]; rfl
    rw [this]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨b, rfl⟩)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

end GlobalTheory.UPel.HT.RealRepBij

namespace GlobalTheory.UPel.HT.RealRepBij

variable {K F : Type} [Field K] [NumberField K] [IsCMField K] [Field F] [NumberField F] [IsCMField F]
  [Algebra K F] {p : ℕ} [Fact p.Prime]

end GlobalTheory.UPel.HT.RealRepBij
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSelfOfTrivial
section
noncomputable section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.LatticeRep

variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ]

def Transl (W : X → M →ₗ[ℂ] M) (A : Submodule R X) : Set M := {m | ∃ x v, Fixes W A v ∧ m = W x v}

def IsLatSystem (σ : R →+* R) (w : R) (γ : X → X → ℂ) (W : X → M →ₗ[ℂ] M) (lam : ℕ →* ℂ) (A : Submodule R X)
    (ρ : Γ →* Module.End R X) : Prop :=
  IsHeis σ w γ W ∧ GoodNorm σ lam ∧ SelfDual γ A ∧ Submodule.span ℂ (Transl W A) = ⊤ ∧
    (∀ g x y, γ (ρ g x) (ρ g y) = γ x y) ∧ ∀ g, idx A (A.map (ρ g)) ≠ 0

def IsLatRep (W : X → M →ₗ[ℂ] M) (lam : ℕ →* ℂ) (A : Submodule R X) (ρ : Γ →* Module.End R X)
    (Om : Γ →* Module.End ℂ M) : Prop :=
  (∀ g x v, Om g (W x v) = W (ρ g x) (Om g v)) ∧ ∀ g v, Fixes W A v → Om g v = normOp lam W A (A.map (ρ g)) v

variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M}

open Classical in
open scoped BigOperators in
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ] in
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M} in
theorem _root_.GlobalTheory.LatticeRep.transl_induction (hs : Submodule.span ℂ (_root_.GlobalTheory.LatticeRep.Transl W A) = ⊤) {p : M → Prop}
    (mem : ∀ x v, _root_.GlobalTheory.FinWeil.Fixes W A v → p (W x v)) (zero : p 0) (add : ∀ a b, p a → p b → p (a + b))
    (smul : ∀ (c : ℂ) a, p a → p (c • a)) (m : M) : p m := by
  have hm : m ∈ Submodule.span ℂ (_root_.GlobalTheory.LatticeRep.Transl W A) := by
    rw [hs]; exact Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, v, hv, rfl⟩ := hy
    exact mem x v hv
  | zero => exact zero
  | add a b _ _ ha hb => exact add a b ha hb
  | smul c a _ ha => exact smul c a ha

theorem mem_map_iff (ρ : Γ →* Module.End R X) (g : Γ) (A : Submodule R X) (x : X) :
    x ∈ A.map (ρ g) ↔ ρ g⁻¹ x ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]; exact ha
  · intro hx
    exact ⟨_, hx, by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩

theorem IsLatSystem.selfDual_map (h : IsLatSystem σ w γ W lam A ρ) (g : Γ) : SelfDual γ (A.map (ρ g)) := by
  obtain ⟨-, -, hA, -, hρ, -⟩ := h
  have e : ∀ x, ρ g (ρ g⁻¹ x) = x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  intro x
  rw [mem_map_iff, hA]
  constructor
  · rintro hx _ ⟨a, ha, rfl⟩
    rw [← hx a ha, ← hρ g (ρ g⁻¹ x), e]
  · intro hx a ha
    rw [← hρ g, e]
    exact hx _ ⟨a, ha, rfl⟩

open Classical in
open scoped BigOperators in
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ] in
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M} in
private theorem sumOp_eq_self_of_le {B : Submodule R X} (hBA : B ≤ A) {v : M}
    (hv : _root_.GlobalTheory.FinWeil.Fixes W A v) : _root_.GlobalTheory.FinWeil.sumOp W A B v = v := by
  unfold _root_.GlobalTheory.FinWeil.sumOp
  have hz : ∀ q : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup, q = 0 := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H b => exact (QuotientAddGroup.eq_zero_iff b).mpr (hBA b.2)
  rw [finsum_eq_single _ 0 (fun q hq => absurd (hz q) hq)]
  exact hv _ (hBA (Quotient.out (0 : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup)).2)

open Classical in
open scoped BigOperators in
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ] in
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M} in

theorem _root_.GlobalTheory.LatticeRep.IsLatRep.fix_of_map_le (h : _root_.GlobalTheory.LatticeRep.IsLatSystem σ w γ W lam A ρ) (hO : _root_.GlobalTheory.LatticeRep.IsLatRep W lam A ρ Om) {g : Γ}
    (hg : A.map (ρ g) ≤ A) {v : M} (hv : _root_.GlobalTheory.FinWeil.Fixes W A v) : Om g v = v := by
  rw [hO.2 g v hv]
  unfold _root_.GlobalTheory.FinWeil.normOp _root_.GlobalTheory.FinWeil.idx
  have hidx : A.toAddSubgroup.relIndex (A.map (ρ g)).toAddSubgroup = 1 :=
    AddSubgroup.relIndex_eq_one.mpr hg
  rw [hidx, map_one, inv_one, one_smul]
  exact sumOp_eq_self_of_le hg hv

theorem IsLatRep.eq_self_of_trivial (h : IsLatSystem σ w γ W lam A ρ) (hO : IsLatRep W lam A ρ Om) {g : Γ}
    (hg : ∀ x, ρ g x = x) (m : M) : Om g m = m := by
  refine transl_induction h.2.2.2.1 (p := fun m => Om g m = m) (fun x v hv => ?_) (map_zero _)
    (fun a b ha hb => by rw [map_add, ha, hb]) (fun c a ha => by rw [map_smul, ha]) m
  rw [hO.1, hg, hO.fix_of_map_le h _ hv]
  rintro _ ⟨a, ha, rfl⟩
  rw [hg]; exact ha

open Classical in
open scoped BigOperators in
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ] in
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M} in
private theorem map_sumOp_of_commute {B : Submodule R X} (φ : M →ₗ[ℂ] M)
    (h : _root_.GlobalTheory.FinWeil.idx A B ≠ 0) (hφ : ∀ x m, φ (W x m) = W x (φ m)) (v : M) :
    φ (_root_.GlobalTheory.FinWeil.sumOp W A B v) = _root_.GlobalTheory.FinWeil.sumOp W A B (φ v) := by
  unfold _root_.GlobalTheory.FinWeil.idx at h
  have : Finite (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) :=
    AddSubgroup.index_ne_zero_iff_finite.mp h
  unfold _root_.GlobalTheory.FinWeil.sumOp
  rw [map_finsum φ (Set.toFinite _)]
  simp only [hφ]

open Classical in
open scoped BigOperators in
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ] in
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M} in

theorem _root_.GlobalTheory.LatticeRep.IsLatRep.comm (h : _root_.GlobalTheory.LatticeRep.IsLatSystem σ w γ W lam A ρ) (hO : _root_.GlobalTheory.LatticeRep.IsLatRep W lam A ρ Om) (φ : M →ₗ[ℂ] M)
    (hφ : ∀ x m, φ (W x m) = W x (φ m)) (g : Γ) (m : M) : Om g (φ m) = φ (Om g m) := by
  refine _root_.GlobalTheory.LatticeRep.transl_induction (p := fun m => Om g (φ m) = φ (Om g m))
    h.2.2.2.1 (fun x v hv => ?_) ?_
    (fun a b ha hb => ?_) (fun c a ha => ?_) m
  · have hφv : _root_.GlobalTheory.FinWeil.Fixes W A (φ v) := fun a ha => by rw [← hφ, hv a ha]
    rw [hφ, hO.1, hO.1, hO.2 g _ hφv, hO.2 g _ hv, hφ]
    congr 1
    unfold _root_.GlobalTheory.FinWeil.normOp
    rw [map_smul, map_sumOp_of_commute φ (h.2.2.2.2.2 g) hφ]
  · simp
  · simp only [map_add, ha, hb]
  · simp only [map_smul, ha]

theorem IsLatRep.exists_stab (h : IsLatSystem σ w γ W lam A ρ) (hO : IsLatRep W lam A ρ Om) (m : M) :
    ∃ s : Set X, s.Finite ∧ ∀ g, A.map (ρ g) ≤ A → (∀ x ∈ s, ρ g x - x ∈ A ∧ γ (w • x) (ρ g x - x) = 1) → Om g m = m := by
  refine transl_induction h.2.2.2.1 (p := fun m => ∃ s : Set X, s.Finite ∧ ∀ g, A.map (ρ g) ≤ A →
    (∀ x ∈ s, ρ g x - x ∈ A ∧ γ (w • x) (ρ g x - x) = 1) → Om g m = m) (fun x v hv => ?_)
    ⟨∅, Set.finite_empty, fun g _ _ => map_zero _⟩ (fun a b ha hb => ?_) (fun c a ha => ?_) m
  · refine ⟨{x}, Set.finite_singleton x, fun g hg hx => ?_⟩
    obtain ⟨h1, h2⟩ := hx x rfl
    have h3 := h.1.comp x (ρ g x - x) v
    rw [hv _ h1, h2, one_smul, add_sub_cancel] at h3
    rw [hO.1, hO.fix_of_map_le h hg hv, h3]
  · obtain ⟨s, hs, h1⟩ := ha
    obtain ⟨t, ht, h2⟩ := hb
    exact ⟨s ∪ t, hs.union ht, fun g hg hx => by
      rw [map_add, h1 g hg fun x hx' => hx x (Or.inl hx'), h2 g hg fun x hx' => hx x (Or.inr hx')]⟩
  · obtain ⟨s, hs, h1⟩ := ha
    exact ⟨s, hs, fun g hg hx => by rw [map_smul, h1 g hg hx]⟩

theorem exists_extend {V : Type} [AddCommGroup V] [Module ℂ V] (N : Submodule ℂ V) (O : Γ →* Module.End ℂ N) :
    ∃ om : Γ →* Module.End ℂ V, ∀ g (m : N), om g m = O g m := by
  obtain ⟨C, hC⟩ := N.exists_isCompl
  let e := Submodule.prodEquivOfIsCompl N C hC
  let P : Γ →* Module.End ℂ (N × C) :=
    { toFun := fun g => (O g).prodMap LinearMap.id
      map_one' := by rw [map_one]; exact LinearMap.prodMap_one
      map_mul' := fun g k => by rw [map_mul, LinearMap.prodMap_mul]; rfl }
  refine ⟨(e.conjRingEquiv.toMonoidHom).comp P, fun g m => ?_⟩
  show e (P g (e.symm m)) = _
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
  simp [P, e]

end GlobalTheory.LatticeRep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleChartLocalizationFiniteTypeFormallyUnramifiStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleChart_localization_finiteType_formallyUnramified : ∀ (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (Ω : Type) [Field Ω] [Algebra R Ω] (I : Ideal (TensorProduct R Ω A)),
  letI : Algebra (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) :=
    (MvPolynomial.aeval (fun i => algebraMap (TensorProduct R Ω A ⧸ I) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (Ideal.Quotient.mk I (1 ⊗ₜ[R] t i)))).toRingHom.toAlgebra
  Algebra.FiniteType (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) ∧
    Algebra.FormallyUnramified (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) := by
  first | exact @GlobalTheory.DenseSec.locQuot_finiteType_formallyUnramified | exact GlobalTheory.DenseSec.locQuot_finiteType_formallyUnramified | (intros; apply GlobalTheory.DenseSec.locQuot_finiteType_formallyUnramified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeTensorOfLowHeight
section
open scoped TensorProduct

namespace GlobalTheory.GoodEtale

theorem etale_localization_of_etaleLow : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] (Q : Ideal O) [Q.IsPrime],
    GlobalTheory.GoodEtale.EtaleLow A R C → ((Q.comap (algebraMap R O)).comap (algebraMap A R)).height ≤ 1 →
    Algebra.Etale (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[R] C) := by
  intro A R C O _ _ _ _ _ _ _ Q _ hE hh
  have h := hE (Q.comap (algebraMap R O)) hh
  letI : Algebra (Localization.AtPrime (Q.comap (algebraMap R O))) (Localization.AtPrime Q) :=
    (Localization.localRingHom _ Q (algebraMap R O) rfl).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime (Q.comap (algebraMap R O))) (Localization.AtPrime Q) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    simp [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map,
      IsScalarTower.algebraMap_apply R O (Localization.AtPrime Q)]
  haveI := Algebra.Etale.baseChange (R := Localization.AtPrime (Q.comap (algebraMap R O)))
    (B := Localization.AtPrime Q) (A := Localization.AtPrime (Q.comap (algebraMap R O)) ⊗[R] C)
  exact Algebra.Etale.of_equiv (Algebra.TensorProduct.cancelBaseChange R
    (Localization.AtPrime (Q.comap (algebraMap R O))) (Localization.AtPrime Q) (Localization.AtPrime Q) C)

example : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] (Q : Ideal O) [Q.IsPrime],
    GlobalTheory.GoodEtale.EtaleLow A R C → ((Q.comap (algebraMap R O)).comap (algebraMap A R)).height ≤ 1 →
    Algebra.Etale (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[R] C) := etale_localization_of_etaleLow

end GlobalTheory.GoodEtale
end

