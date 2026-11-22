import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1353
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1305
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1366
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralShellsVanishBeyondPeriodRamified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemOfQdetMem
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

noncomputable section

namespace GlobalTheory.CapTrace

variable {A : Type} [Ring A] [Algebra ℂ A]

def dprod (L : List (ℂ × A)) : ℂ := (L.map Prod.fst).prod

def sub1 (L : List (ℂ × A)) : A := List.rec 0 (fun p L s => dprod L • p.2 + p.1 • s) L

theorem sub1_nil : sub1 ([] : List (ℂ × A)) = 0 := rfl

theorem sub1_cons (p : ℂ × A) (L : List (ℂ × A)) : sub1 (p :: L) = dprod L • p.2 + p.1 • sub1 L := rfl

theorem prod_affine (L : List (ℂ × A)) : ∃ c : ℕ → A, (∀ k, L.length < k → c k = 0) ∧
    (∀ u : ℂ, (L.map fun p => (u * p.1) • (1 : A) + p.2).prod =
      ∑ k ∈ Finset.range (L.length + 1), u ^ k • c k) ∧
    c L.length = dprod L • (1 : A) ∧ (∀ j, j + 1 = L.length → c j = sub1 L) := by
  induction L with
  | nil => exact ⟨fun k => if k = 0 then 1 else 0, fun k hk => by simp at hk; simp [Nat.pos_iff_ne_zero.1 hk],
      fun u => by simp, by simp [dprod], fun j hj => by simp at hj⟩
  | cons p L ih =>
    obtain ⟨c, hc0, hcu, hctop, hcsub⟩ := ih
    refine ⟨fun k => (if k = 0 then 0 else p.1 • c (k - 1)) + p.2 * c k, ?_, ?_, ?_, ?_⟩
    · intro k hk
      simp only [List.length_cons] at hk
      have h1 : k ≠ 0 := by omega
      simp only [h1, if_false, hc0 k (by omega), hc0 (k - 1) (by omega), smul_zero, mul_zero, add_zero]
    · intro u
      have hS1 : ∑ k ∈ Finset.range (L.length + 1 + 1), u ^ k • (if k = 0 then (0:A) else p.1 • c (k - 1)) =
          ∑ k ∈ Finset.range (L.length + 1), (u * p.1) • (u ^ k • c k) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, if_true, smul_zero, add_zero]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_smul, smul_smul, pow_succ]; ring_nf
      have hS2 : ∑ k ∈ Finset.range (L.length + 1 + 1), u ^ k • (p.2 * c k) =
          ∑ k ∈ Finset.range (L.length + 1), p.2 * (u ^ k • c k) := by
        rw [Finset.sum_range_succ, hc0 (L.length + 1) (by omega)]
        simp [mul_smul_comm]
      simp only [List.map_cons, List.prod_cons, hcu, List.length_cons, smul_add, Finset.sum_add_distrib, hS1, hS2,
        add_mul, Finset.mul_sum, smul_mul_assoc, one_mul]
    · simp only [List.length_cons, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, hctop,
        hc0 (L.length + 1) (by omega), mul_zero, add_zero, dprod, List.map_cons, List.prod_cons, smul_smul]
    · intro j hj
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hj
      subst hj
      beta_reduce
      rw [hctop, sub1_cons]
      rcases Nat.eq_zero_or_pos L.length with h | h
      · rw [if_pos h]
        have : L = [] := List.length_eq_zero_iff.1 h
        subst this
        simp [sub1_nil, dprod]
      · rw [if_neg (by omega), hcsub _ (by omega), mul_smul_comm, mul_one, add_comm]

end GlobalTheory.CapTrace

namespace GlobalTheory.CapTrace

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem coeff_mem (S : Submodule ℂ A) (n : ℕ) (c : ℕ → A)
    (h : ∀ u : ℂ, ∑ k ∈ Finset.range (n + 1), u ^ k • c k ∈ S) (m : ℕ) (hm : m ≤ n) : c m ∈ S := by
  let v : Fin (n + 1) → ℂ := fun j => ((j : ℕ) : ℂ)
  have hv : Function.Injective v := fun i j hij => Fin.ext (by simpa [v] using hij)
  have hdet : IsUnit (Matrix.vandermonde v).det :=
    isUnit_iff_ne_zero.2 (Matrix.det_vandermonde_ne_zero_iff.2 hv)
  have hW : (Matrix.vandermonde v)⁻¹ * Matrix.vandermonde v = 1 := Matrix.nonsing_inv_mul _ hdet
  set W := (Matrix.vandermonde v)⁻¹
  let m' : Fin (n + 1) := ⟨m, by omega⟩
  have key : c m = ∑ j, W m' j • ∑ k ∈ Finset.range (n + 1), v j ^ k • c k := by
    calc c m = ∑ k : Fin (n + 1), (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) m' k • c k := by
          rw [Finset.sum_eq_single m']
          · simp [m']
          · intro k _ hk; rw [Matrix.one_apply_ne (Ne.symm hk), zero_smul]
          · simp
      _ = ∑ k : Fin (n + 1), (W * Matrix.vandermonde v) m' k • c k := by rw [hW]
      _ = ∑ j, W m' j • ∑ k : Fin (n + 1), v j ^ (k : ℕ) • c k := by
          simp only [Matrix.mul_apply, Matrix.vandermonde_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
          exact Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_range (fun k => v j ^ k • c k)]
  rw [key]
  exact S.sum_mem fun j _ => S.smul_mem _ (h _)

theorem sub1_ones (L : List (ℂ × A)) (h : ∀ p ∈ L, p.1 = 1) : sub1 L = (L.map Prod.snd).sum ∧ dprod L = 1 := by
  induction L with
  | nil => simp [sub1_nil, dprod]
  | cons p L ih =>
    obtain ⟨h1, h2⟩ := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hp := h p List.mem_cons_self
    refine ⟨?_, ?_⟩
    · rw [sub1_cons, h1, h2, hp]; simp
    · simp only [dprod, List.map_cons, List.prod_cons, hp, one_mul]; exact h2

theorem dprod_eq_zero (L : List (ℂ × A)) (p : ℂ × A) (hp : p ∈ L) (h : p.1 = 0) : dprod L = 0 :=
  List.prod_eq_zero (List.mem_map.2 ⟨p, hp, h⟩)

theorem sub1_ofFn_eq_zero : ∀ (n : ℕ) (d : Fin n → ℂ) (B : Fin n → A) (k₀ k₁ : Fin n), k₀ ≠ k₁ → d k₀ = 0 →
    d k₁ = 0 → sub1 (List.ofFn fun k => (d k, B k)) = 0 := by
  intro n
  induction n with
  | zero => intro d B k₀; exact k₀.elim0
  | succ n ih =>
    intro d B k₀ k₁ hne h₀ h₁
    rw [List.ofFn_succ, sub1_cons]
    have hmem : ∀ j : Fin n, d j.succ = 0 → dprod (List.ofFn fun k : Fin n => (d k.succ, B k.succ)) = 0 :=
      fun j hj => dprod_eq_zero _ (d j.succ, B j.succ) (List.mem_ofFn.2 ⟨j, rfl⟩) hj
    induction k₀ using Fin.cases with
    | zero =>
      induction k₁ using Fin.cases with
      | zero => exact absurd rfl hne
      | succ j₁ => simp [h₀, hmem j₁ h₁]
    | succ j₀ =>
      induction k₁ using Fin.cases with
      | zero => simp [h₁, hmem j₀ h₀]
      | succ j₁ =>
        rw [ih (fun k => d k.succ) (fun k => B k.succ) j₀ j₁ (fun e => hne (by rw [e])) h₀ h₁, hmem j₀ h₀]
        simp

end GlobalTheory.CapTrace

namespace GlobalTheory.CapTrace

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem trace_mem_of_qdet_mem {n : ℕ} (X : Fin n → Fin n → A) (S : Subalgebra ℂ A)
    (h : ∀ u : ℂ, Formalism.REAL.qdet X u ∈ S) : ∑ i, X i i ∈ S := by
  classical
  let d : Equiv.Perm (Fin n) → Fin n → ℂ := fun σ k => if σ k = k then 1 else 0
  let B : Equiv.Perm (Fin n) → Fin n → A := fun σ k =>
    (if σ k = k then algebraMap ℂ A (-((k : ℕ) : ℂ)) else 0) + X (σ k) k
  let L : Equiv.Perm (Fin n) → List (ℂ × A) := fun σ => List.ofFn fun k => (d σ k, B σ k)
  have hlen : ∀ σ, (L σ).length = n := fun σ => List.length_ofFn
  choose c hc0 hcu hctop hcsub using fun σ => prod_affine (L σ)
  have hfac : ∀ σ (u : ℂ), (List.ofFn fun k : Fin n => Formalism.REAL.Tm X (u - ((k : ℕ) : ℂ)) (id (σ k)) (id k)).prod =
      ((L σ).map fun p => (u * p.1) • (1 : A) + p.2).prod := by
    intro σ u
    simp only [L, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.2 (funext fun k => ?_)
    simp only [Function.comp_apply, Formalism.REAL.Tm, id, d, B]
    split_ifs
    · rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, mul_one, sub_eq_add_neg, add_smul]; abel
    · simp
  let C : ℕ → A := fun k => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) * c σ k
  have hC : ∀ u : ℂ, Formalism.REAL.qdet X u = ∑ k ∈ Finset.range (n + 1), u ^ k • C k := by
    intro u
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, hfac, hcu, hlen, C, Finset.mul_sum, Finset.smul_sum, mul_smul_comm]
    exact Finset.sum_comm
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hmem : C (n - 1) ∈ S := coeff_mem (Subalgebra.toSubmodule S) n C (fun u => by
    rw [← hC]; exact h u) (n - 1) (by omega)
  have hsub : ∀ σ, c σ (n - 1) = sub1 (L σ) := fun σ => hcsub σ _ (by rw [hlen]; omega)
  have hCeq : C (n - 1) = ∑ k : Fin n, B 1 k := by
    simp only [C, hsub]
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · rw [(sub1_ones (L 1) ?_).1]
      · simp [L, List.map_ofFn, List.sum_ofFn]
      · intro p hp
        obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hp
        simp [d]
    · intro σ _ hσ
      obtain ⟨k₀, hk₀⟩ : ∃ k, σ k ≠ k := by
        by_contra hc; exact hσ (Equiv.ext fun k => not_not.1 fun hk => hc ⟨k, hk⟩)
      have hk₁ : σ (σ k₀) ≠ σ k₀ := fun e => hk₀ (σ.injective e)
      rw [sub1_ofFn_eq_zero n (d σ) (B σ) k₀ (σ k₀) (Ne.symm hk₀) (by simp [d, hk₀]) (by simp [d, hk₁]), mul_zero]
    · simp
  have hB : ∀ k : Fin n, B 1 k = algebraMap ℂ A (-((k : ℕ) : ℂ)) + X k k := fun k => by simp [B]
  simp only [hCeq, hB, Finset.sum_add_distrib] at hmem
  have hs : ∑ k : Fin n, algebraMap ℂ A (-((k : ℕ) : ℂ)) ∈ S := S.sum_mem fun k _ => S.algebraMap_mem _
  simpa using S.sub_mem hmem hs

end GlobalTheory.CapTrace

namespace GlobalTheory.CuspRep

theorem Eop_add_Eop_conj {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (τ : E →+* ℂ)
    (i : Fin a) : Eop τ i i + Eop (ComplexEmbedding.conjugate τ) i i = lieS E a i i (atEmb τ 1) := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  simp only [Eop, atEmb_conj, map_one, Complex.conj_I, e, map_neg, smul_neg, sub_neg_eq_add]
  rw [← smul_add]
  module

end GlobalTheory.CuspRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwSubISupInfLevel
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.DimPartsFull

theorem dualLab_dualLab' (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab, List.map_reverse, List.map_map]

section Tw
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool)

theorem twSub_map (V : Submodule ℂ E) : V.map (Tw.mkL s E) = Tw.sub s V := by
  ext x
  exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun hx => ⟨Tw.out x, hx, rfl⟩⟩

theorem twSub_iSup {C : Type} (S : C → Prop) (V : C → Submodule ℂ E) :
    Tw.sub s (⨆ (c : C) (_ : S c), V c) = ⨆ (c : C) (_ : S c), Tw.sub s (V c) := by
  rw [← twSub_map, Submodule.map_iSup]
  refine iSup_congr fun c => ?_
  rw [Submodule.map_iSup]
  refine iSup_congr fun _ => ?_
  exact twSub_map s (V c)

theorem twSub_finrank (V : Submodule ℂ E) : Module.finrank ℂ (Tw.sub s V) = Module.finrank ℂ V := by
  unfold Module.finrank
  congr 1
  symm
  exact rank_eq_of_equiv_equiv (cj s)
    (show V ≃+ Tw.sub s V from
      { toFun := fun x => ⟨Tw.mk s x.1, x.2⟩
        invFun := fun x => ⟨Tw.out x.1, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl })
    (Function.Involutive.bijective (cj_cj s))
    (fun r m => Subtype.ext ((Tw.mkL s E).map_smulₛₗ r m.1))

theorem twSub_le {V V' : Submodule ℂ E} (h : V ≤ V') : Tw.sub s V ≤ Tw.sub s V' := fun _ hx => h hx

theorem twSub_stable {G : Type} [Group G] (ρ : Representation ℂ G E) (V : Submodule ℂ E)
    (h : ∀ g, V.map (ρ g) ≤ V) (g : G) : (Tw.sub s V).map (Tw.rep s ρ g) ≤ Tw.sub s V := by
  rintro _ ⟨x, hx, rfl⟩
  exact h g ⟨Tw.out x, hx, rfl⟩

end Tw

theorem twSub_iSup_inf_level {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) {G : Type} [Group G] [Fintype G]
    (ρ : Representation ℂ G E) (P : Subgroup G) (ψ : P →* ℂˣ) {C : Type} (S : C → Prop) (U : C → Submodule ℂ E)
    (B Lev : Submodule ℂ E) (hUB : ∀ c, U c ≤ B) (hstab : ∀ c g, (U c).map (ρ g) ≤ U c)
    (hLev : Tw.sub s Lev = Tw.sub s B ⊓
      ⨅ h : P, LinearMap.ker (Tw.rep s ρ (h : G) - ((ψ h : ℂˣ) : ℂ) • LinearMap.id)) :
    Tw.sub s (⨆ (c : C) (_ : S c), U c) ⊓ Tw.sub s Lev = Tw.sub s (⨆ (c : C) (_ : S c), U c ⊓ Lev) := by
  rw [twSub_iSup, hLev, ← inf_assoc, inf_eq_left.2 (iSup₂_le fun c _ => twSub_le s (hUB c)),
    GlobalTheory.iSup_stable_inf_typeSpace (Tw.rep s ρ) P ψ _ S (fun c g => twSub_stable s ρ _ (hstab c) g), twSub_iSup]
  refine iSup_congr fun c => iSup_congr fun _ => ?_
  show _ = Tw.sub s (U c) ⊓ Tw.sub s Lev
  rw [hLev, ← inf_assoc, inf_eq_left.2 (twSub_le s (hUB c))]

open Classical in
theorem evC_single {D : D7} (V : HSp D) (P : Pl D.host.E) (a : List ℤ → ℂ) (d : List ℤ) :
    GlobalTheory.Hk3.evC V P a (Finsupp.single d 1) = if IsLab V P d then a d else 0 := by
  unfold GlobalTheory.Hk3.evC
  rw [Finsupp.sum_single_index]
  · split_ifs <;> simp
  · split_ifs <;> simp

theorem dimParts_of_schur {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} (hOk : A3.fam3.Ok3 s) (hW : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt)
    (hX : GoodStable A3.A.X) (hD : GlobalTheory.CuspMult.CuspDecomp D) (hM : GlobalTheory.CuspMult.MultEq R.toRealDat)
    (hU : R.toRealDat.LUnif) (hS : SchurAll R.toRealDat) : (R.toCx3 F).DimParts false := by
  obtain ⟨hC, hSF, hEE, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  have hIrr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨hE, -, -, -, hEev, hEchar⟩ := GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces R.toRealDat F.lv2 hC hS R.SF hSF
  intro j p
  obtain ⟨hWo, -, -, -, hWtop, hWstab, hWev, hWchar⟩ := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hC hS hIrr R.SF hSF j
  have hI := (GlobalTheory.Hk3.eH_laws R.toRealDat F.lv2 hC hIrr j).1
  have hlab : ∀ P d, Good R.toRealDat A3.A.μ0 P → (IsLab (Wc D j) P d ↔ IsLab (Yc D 0) P (dualLab d)) :=
    fun P d hP => (GlobalTheory.T.isLabel_thetaLiftSpace_iff_dual (s := 0) R.toRealDat F.lv2 hC j P d hP).1
  let LevW : Submodule ℂ (R.HW j (sg0 D A3.A)).H :=
    (R.toRealDat.Wat j (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A))).comap (R.HW j (sg0 D A3.A)).e
  let LevE : Submodule ℂ R.HE.H := (R.toRealDat.EEat (R.toRealDat.levR F.lv2 false)).comap R.HE.e
  have hWle : ∀ c, Wcc R.toRealDat R.SF j c ≤ LinearMap.range (eH R.toRealDat j) := fun c =>
    hWtop ▸ le_iSup (fun c => Wcc R.toRealDat R.SF j c) c
  have hr1 : LinearMap.range ((R.toCx3 F).w0C false j) = Tw.sub (twAt D.what₂.embLL A3.A.v0) LevW :=
    GlobalTheory.T.range_complex_points_level_forms_eq_good_forms R F hOk hW hU false j
  have hr2 := GlobalTheory.T.range_goodProjector_baseLevel_twistedModel R F hOk hW hEx hU j
  have hWside : (R.toCx3 F).Wp j p ⊓ LinearMap.range ((R.toCx3 F).w0C false j) =
      Tw.sub (twAt D.what₂.embLL A3.A.v0)
        (⨆ (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c), Wcc R.toRealDat R.SF j c ⊓ LevW) := by
    have e0 : (R.toCx3 F).Wp j p = Tw.sub (twAt D.what₂.embLL A3.A.v0)
        (⨆ (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c), Wcc R.toRealDat R.SF j c) := by
      show Tw.sub _ (R.Wp3 j p) = _
      unfold RealDat3.Wp3
      simp only [hWc]
    rw [e0, hr1]
    exact twSub_iSup_inf_level _ (R.gW j (sg0 D A3.A)) F.P0 ((Units.map A3.A.fam.v0.embedding.toMonoidHom).comp F.ψ0⁻¹)
      (R.Carries p) _ _ LevW hWle hWstab (hr1.symm.trans hr2)
  have hEside : (R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl false =
      Tw.sub (twAt D.what₂.embLL A3.A.v0)
        (⨆ (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c), EEc R.toRealDat R.SF c ⊓ LevE) := by
    have e0 : (R.toCx3 F).EEp p = Tw.sub (twAt D.what₂.embLL A3.A.v0)
        (⨆ (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c), EEc R.toRealDat R.SF c) := by
      show Tw.sub _ (R.EEp3 p) = _
      unfold RealDat3.EEp3
      simp only [hEE]
    have hl : Tw.sub (twAt D.what₂.embLL A3.A.v0) LevE = Tw.sub (twAt D.what₂.embLL A3.A.v0) ⊤ ⊓
        ⨅ h : F.P0, LinearMap.ker (Tw.rep (twAt D.what₂.embLL A3.A.v0) R.gE (h : G) -
          ((((Units.map A3.A.fam.v0.embedding.toMonoidHom).comp F.ψ0) h : ℂˣ) : ℂ) • LinearMap.id) := by
      have := (GlobalTheory.T.level_rows_eq_type_vectors_of_level R F hW).1
      refine this.trans ?_
      ext x
      exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
    rw [e0]
    exact twSub_iSup_inf_level _ R.gE F.P0 _ (R.Carries p) _ ⊤ LevE (fun _ => le_top)
      (fun c g => GlobalTheory.T.rowParts_full_spherical_algebra_stable_finiteGroup (s := 0) R.toRealDat F.lv2 hC R.SF hSF c g) hl
  rw [hWside, hEside]
  refine (twSub_finrank (E := (R.HW j (sg0 D A3.A)).H) _ _).trans (Eq.trans ?_ (twSub_finrank (E := R.HE.H) _ _).symm)
  have hWfix : ∀ c, ∀ x ∈ Wcc R.toRealDat R.SF j c, eH R.toRealDat j x = x := by
    intro c x hx
    obtain ⟨y, rfl⟩ := hWle c hx
    rw [← Module.End.mul_apply, hI]
  let I := {x : Pl D.host.E × List ℤ // Good R.toRealDat A3.A.μ0 x.1 ∧ IsLab (Wc D j) x.1 x.2}
  let lab : (Pl D.host.E → List ℤ → ℂ) → I → ℂ := fun c i => c i.1.1 i.1.2
  have hEle : ∀ c c', lab c = lab c' → EEc R.toRealDat R.SF c ≤ EEc R.toRealDat R.SF c' := by
    intro c c' hcc x hx
    refine hEchar c' x fun P d hP hd => ?_
    rw [hEev c P hP _ x hx, evC_single, if_pos hd]
    have hl : IsLab (Wc D j) P (dualLab d) := (hlab P (dualLab d) hP).2 (by rwa [dualLab_dualLab'])
    exact congrArg (· • x) (congrFun hcc ⟨(P, dualLab d), hP, hl⟩)
  have hWcle : ∀ c c', lab c = lab c' → Wcc R.toRealDat R.SF j c ≤ Wcc R.toRealDat R.SF j c' := by
    intro c c' hcc x hx
    refine hWchar c' x (hWfix c x hx) fun P d hP hd => ?_
    rw [hWev c P hP _ x hx, evC_single, if_pos hd]
    exact congrArg (· • x) (congrFun hcc ⟨(P, d), hP, hd⟩)
  symm
  refine GlobalTheory.finrank_iSup_joint_eigen_eq (I := I)
    (fun i => hE i.1.1 (Finsupp.single (dualLab i.1.2) 1)) (fun i => hWo i.1.1 (Finsupp.single i.1.2 1))
    (fun c => EEc R.toRealDat R.SF c ⊓ LevE) (fun c => Wcc R.toRealDat R.SF j c ⊓ LevW) lab ?_ ?_ ?_ ?_ (R.Carries p)
  · rintro c x hx ⟨⟨P, d⟩, hP, hd⟩
    rw [hEev c P hP _ x hx.1, evC_single, if_pos ((hlab P d hP).1 hd), dualLab_dualLab']
  · rintro c x hx ⟨⟨P, d⟩, hP, hd⟩
    rw [hWev c P hP _ x hx.1, evC_single, if_pos hd]
  · intro c c' hcc
    rw [le_antisymm (hEle c c' hcc) (hEle c' c hcc.symm), le_antisymm (hWcle c c' hcc) (hWcle c' c hcc.symm)]
    exact ⟨rfl, rfl⟩
  · intro c
    exact (GlobalTheory.T.finrank_W_eigenpart_eq_rows_full_hecke R.toRealDat F.lv2 hOk.ok2 hC hS hX hD hM R.SF hSF F.P0 F.ψ0 j c).symm

end GlobalTheory.DimPartsFull

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartLeEigensystemPartPrincipalLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePart_le_eigensystemPart_principalLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → ∀ SF, IsSF R SF → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → (∀ i, StdPsi hF (PW i)) → ∀ π i0 c, principalLevelFrame.IsEigOf (PW i0) (levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) (levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) SF π c → ∀ i, ∀ U ∈ principalLevelFrame.isotL R.θ (PW i) (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) (R.eWf i (sg0 D A)) π, ∃ x ∈ Wcc R SF i c, (R.HW i _).e x = U := by
  first | exact @GlobalTheory.PartTypeW.part_in_eigenpart | exact GlobalTheory.PartTypeW.part_in_eigenpart | (intros; apply GlobalTheory.PartTypeW.part_in_eigenpart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPlaceDecomposition
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.UnitaryPlaceSplit

theorem mix_mul {S A : Type} [CommRing S] [Ring A] [Algebra S A] {e : S} (he : e * e = e) (x y z w : A) :
    (e • x + (1 - e) • y) * (e • z + (1 - e) • w) = e • (x * z) + (1 - e) • (y * w) := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h0' : (1 - e) * e = 0 := by rw [mul_comm, h0]
  have h1 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h0, sub_zero]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, he, h0, h0', h1, zero_smul, add_zero,
    zero_add]

variable {F : Type} [Field F] [NumberField F]

def idemAt (v : Pl F) : AF F := LinearMap.inr F (Ainf F) (Af F) (singleFin v 1)

theorem evFin_idemAt (v : Pl F) : evFin F v (idemAt v) = 1 := evalV_singleFin_self v 1

theorem idemAt_mul_self (v : Pl F) : idemAt v * idemAt v = idemAt v := by
  refine Prod.ext (show (0 : Ainf F) * 0 = 0 from mul_zero 0) ?_
  change singleFin v 1 * singleFin v 1 = singleFin v 1
  rw [← singleFin_mul, one_mul]

theorem mul_idemAt_of_evFin (v : Pl F) {u : AF F} (hu : evFin F v u = 0) : u * idemAt v = 0 := by
  refine Prod.ext (show u.1 * (0 : Ainf F) = 0 from mul_zero _) ?_
  change u.2 * singleFin v 1 = 0
  refine af_ext fun w => ?_
  rw [map_mul, map_zero]
  by_cases h : w = v
  · subst h
    have : evalV F w u.2 = 0 := hu
    rw [this, zero_mul]
  · rw [evalV_singleFin_ne h, mul_zero]

end GlobalTheory.UnitaryPlaceSplit

end

namespace GlobalTheory.UnitaryPlaceSplit

open Matrix

theorem exists_split_at (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (g : UA σ J) :
    ∃ g₁ g₂ : UA σ J, g = g₁ * g₂ ∧ At (evFin F v) (mat g₁ - 1) ∧
      ∀ u : AF F, At (evFin F v) u → u • (mat g₂ - 1) = 0 := by
  have hee : idemAt v * idemAt v = idemAt v := idemAt_mul_self v
  set e : AF F := idemAt v with he_def
  set G : Matrix (Fin n) (Fin n) (AE F E) := ((g.1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))
    with hG
  set Gi : Matrix (Fin n) (Fin n) (AE F E) :=
    ((g.1⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) with hGi
  have hGGi : G * Gi = 1 := Units.mul_inv g.1
  have hGiG : Gi * G = 1 := Units.inv_mul g.1
  have split : ∀ X : Matrix (Fin n) (Fin n) (AE F E), X = e • X + (1 - e) • X := fun X => by
    rw [← add_smul, add_sub_cancel, one_smul]
  set M : Matrix (Fin n) (Fin n) (AE F E) := e • G + (1 - e) • 1 with hM
  set N : Matrix (Fin n) (Fin n) (AE F E) := e • Gi + (1 - e) • 1 with hN
  have hMN : M * N = 1 := by rw [hM, hN, mix_mul hee, hGGi, mul_one, ← split]
  have hNM : N * M = 1 := by rw [hM, hN, mix_mul hee, hGiG, mul_one, ← split]
  let g1gl : GL (Fin n) (AE F E) := ⟨M, N, hMN, hNM⟩
  have hmem : g1gl ∈ UG (cA σ) (incM F J) := by
    change Mᵀ * incM F J * M.map (cA σ) = incM F J
    have hg : Gᵀ * incM F J * G.map (cA σ) = incM F J := g.2
    have hT : Mᵀ = e • Gᵀ + (1 - e) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
      rw [hM, transpose_add, transpose_smul, transpose_smul, transpose_one]
    have hc : M.map (cA σ) = e • G.map (cA σ) + (1 - e) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
      rw [← AlgHom.mapMatrix_apply, hM, map_add, map_smul, map_smul, map_one, AlgHom.mapMatrix_apply]
    rw [hT, hc, split (incM F J), mix_mul hee, mix_mul hee, hg, one_mul, mul_one]
  let g₁ : UA σ J := ⟨g1gl, hmem⟩
  have hm1 : mat g₁ - 1 = e • (G - 1) := by
    change M - 1 = _
    rw [hM, smul_sub, sub_smul, one_smul]
    abel
  have hm2 : mat (g₁⁻¹ * g) - 1 = (1 - e) • (G - 1) := by
    change N * G - 1 = _
    conv_lhs => rw [split G]
    rw [hN, mix_mul hee, hGiG, one_mul, smul_sub, sub_smul (1 : AF F) e (1 : Matrix (Fin n) (Fin n) (AE F E)), one_smul]
    abel
  refine ⟨g₁, g₁⁻¹ * g, (mul_inv_cancel_left g₁ g).symm, fun u hu => ?_, fun u hu => ?_⟩
  · rw [hm1, smul_smul, mul_idemAt_of_evFin v hu, zero_smul]
  · have h1 : (1 - e) • u = 0 := hu (1 - e) (by rw [map_sub, map_one, he_def, evFin_idemAt, sub_self])
    rw [hm2, smul_smul, mul_comm, ← smul_eq_mul, h1, zero_smul]

end GlobalTheory.UnitaryPlaceSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralShellsVanishBeyondPeriodRamifiedStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zetaIntegralShells_vanish_beyondPeriod_ramified : GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.ShellLemma := by
  first | exact @GlobalTheory.ShellVan.shell_lemma | exact GlobalTheory.ShellVan.shell_lemma | (intros; apply GlobalTheory.ShellVan.shell_lemma <;> assumption)
end

