import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0740
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0257
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0056
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0735
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2157
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0674
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiStepCoreComponentMemCoreDepthLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CoreComp

variable {D : D7}

def finV {n : ℕ} (z : Fin n → D.host.E) : Fin n → AE D := fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i

theorem rat_entry {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) (i : Fin m) (j : Fin n) :
    (rat A : Mx D m n) i j = (1 : AF D.host.F) ⊗ₜ[D.host.F] A i j := rfl

theorem rat_mulVec_finV {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) (z : Fin n → D.host.E) :
    (rat A : Mx D m n) *ᵥ finV z = finV (A *ᵥ z) := by
  funext i
  simp only [finV, mulVec, dotProduct, TensorProduct.tmul_sum, rat_entry, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem finV_mem {S : HSp D} {L : Lat S} {z : Fin S.rank → D.host.E} (hz : z ∈ L) :
    finV z ∈ latV S L (fun _ => True) :=
  AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, fun v hv => absurd trivial hv, 1, rfl, z, hz,
    by funext i; simp [finV]⟩

theorem mem_of_finV (S : HSp D) (L : Lat S) (hL : Submodule.IsLattice D.host.E L) (z : Fin S.rank → D.host.E)
    (hz : finV z ∈ latV S L (fun _ => True)) : z ∈ L := GlobalTheory.T.mem_lattice_of_rational_mem_completion_all_places D S L hL z hz

theorem loc_iff {S : HSp D} {L : Lat S} (hL : Submodule.IsLattice D.host.E L) (y : Fin S.rank → AE D) :
    y ∈ latV S L (fun _ => True) ↔ (∀ i, y i ∈ idAt D (fun _ => True)) ∧
      ∀ v, ∀ e ∈ intAt D (· = v), e • y ∈ latV S L (· = v) := by
  have := ((GlobalTheory.FinPl.localComponents D (fun _ => True)).2 S).2.2.2 L y hL
  simpa using this

end GlobalTheory.CoreComp

namespace GlobalTheory.CoreComp

variable {D : D7}

theorem mulVec_mem_idAt {m n : ℕ} (M : Mx D m n) {y : Fin n → AE D} (hy : ∀ i, y i ∈ idAt D (fun _ => True)) (i : Fin m) :
    (M *ᵥ y) i ∈ idAt D (fun _ => True) := mulVec_idAt M hy i

theorem witt_core_inclusion_maps_split_lattices {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}
    (hL : Submodule.IsLattice D.host.E L) (hL₀ : Submodule.IsLattice D.host.E L₀) (hM : ∀ v, MonoAt d L L₀ v)
    {z : Fin S₀.rank → D.host.E} (hz : z ∈ L₀) : d.i₀ *ᵥ z ∈ L := by
  apply mem_of_finV S L hL
  rw [← rat_mulVec_finV]
  have hz' := (loc_iff hL₀ _).1 (finV_mem hz)
  refine (loc_iff hL _).2 ⟨mulVec_mem_idAt _ hz'.1, fun v e he => ?_⟩
  have h1 := hz'.2 v e he
  rw [← Matrix.mulVec_smul]
  refine (hM v _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩
  · have e0 : (d.pX *ᵥ ((rat d.i₀ : Mx D S.rank S₀.rank) *ᵥ e • finV z)) i = 0 := by
      rw [Matrix.mulVec_mulVec, show (rat d.i₀ : Mx D S.rank S₀.rank) = d.j0 from rfl, HypDec.pX_j0, Matrix.zero_mulVec]; rfl
    rw [e0]
    have : GlobalTheory.FinPl.colMul d.jX i 0 = 0 := by funext k; simp [GlobalTheory.FinPl.colMul]
    rw [this]; exact zero_mem _
  · have e0 : (d.pY *ᵥ ((rat d.i₀ : Mx D S.rank S₀.rank) *ᵥ e • finV z)) i = 0 := by
      rw [Matrix.mulVec_mulVec, show (rat d.i₀ : Mx D S.rank S₀.rank) = d.j0 from rfl, HypDec.pY_j0, Matrix.zero_mulVec]; rfl
    rw [e0]
    have : GlobalTheory.FinPl.colMul d.jY i 0 = 0 := by funext k; simp [GlobalTheory.FinPl.colMul]
    rw [this]; exact zero_mem _
  · rw [Matrix.mulVec_mulVec, show (rat d.i₀ : Mx D S.rank S₀.rank) = d.j0 from rfl, HypDec.p0_j0, Matrix.one_mulVec]
    exact h1

theorem witt_core_projection_maps_split_lattices {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}
    (hL : Submodule.IsLattice D.host.E L) (hL₀ : Submodule.IsLattice D.host.E L₀) (hM : ∀ v, MonoAt d L L₀ v)
    {y : Fin S.rank → D.host.E} (hy : y ∈ L) : d.q0 *ᵥ y ∈ L₀ := by
  apply mem_of_finV S₀ L₀ hL₀
  rw [← rat_mulVec_finV]
  have hy' := (loc_iff hL _).1 (finV_mem hy)
  refine (loc_iff hL₀ _).2 ⟨mulVec_mem_idAt _ hy'.1, fun v e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact ((hM v _).1 (hy'.2 v e he)).2.2

theorem qA_maps {S A B : HSp D} (o : OrthDec S A B) {L : Lat S} {LA : Lat A} {LB : Lat B}
    (hL : Submodule.IsLattice D.host.E L) (hLA : Submodule.IsLattice D.host.E LA) (hO : ∀ v, OrthAt o L LA LB v)
    {y : Fin S.rank → D.host.E} (hy : y ∈ L) : o.qA *ᵥ y ∈ LA := by
  apply mem_of_finV A LA hLA
  rw [← rat_mulVec_finV]
  have hy' := (loc_iff hL _).1 (finV_mem hy)
  refine (loc_iff hLA _).2 ⟨mulVec_mem_idAt _ hy'.1, fun v e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact ((hO v _).1 (hy'.2 v e he)).1

theorem rat_mulVec_mem_latA {S T : HSp D} (m : Matrix (Fin T.rank) (Fin S.rank) D.host.E) {L : Lat S} {L' : Lat T}
    (h : ∀ x ∈ L, m *ᵥ x ∈ L') {P : GlobalTheory.FinPl.Pl D → Prop} {y : Fin S.rank → AE D} (hy : y ∈ latA S L P) :
    (rat m : Mx D T.rank S.rank) *ᵥ y ∈ latA T L' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hα', a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨α, hα, hα', a, ha, m *ᵥ x, h x hx, ?_⟩
    funext i
    simp only [mulVec, dotProduct, Finset.mul_sum, TensorProduct.tmul_sum, rat_entry, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1; ring
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [mulVec_neg]; exact neg_mem hx

theorem latO_sandwich {S T S' T' : HSp D} {ΛS : Lat S} {ΛT : Lat T} {ΛS' : Lat S'} {ΛT' : Lat T'}
    (M : Matrix (Fin T'.rank) (Fin T.rank) D.host.E) (N : Matrix (Fin S.rank) (Fin S'.rank) D.host.E)
    (hS : IsSelfDualC S ΛS) (hS' : IsSelfDualC S' ΛS') (hT' : IsSelfDualC T' ΛT')
    (hN : ∀ y ∈ ΛS', N *ᵥ y ∈ ΛS) (hM : ∀ y ∈ ΛT, M *ᵥ y ∈ ΛT') {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) :
    ((rat M : Mx D T'.rank T.rank) * u * (rat N : Mx D S.rank S'.rank) : WO S' T') ∈
      latO S' T' (ΛS' : Set _) (ΛT' : Set _) fun _ => True := by
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S' T' ΛS' ΛT' hS' hT']
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · simp only [Matrix.mul_apply]
    exact sum_mem fun l _ => Ideal.mul_mem_right _ _
      (sum_mem fun k _ => Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu k l))
  · show ((rat M : Mx D T'.rank T.rank) * u * (rat N : Mx D S.rank S'.rank)) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact rat_mulVec_mem_latA M hM
      (GlobalTheory.FinPl.LatMem.latO_maps hS hu (GlobalTheory.OrthSumLat.rat_mulVec_mem_latV N hN hy))

theorem hatMx_sandwich {S T S' T' : HSp D} {ΛS : Lat S} {ΛT : Lat T} {ΛS' : Lat S'} {ΛT' : Lat T'}
    (M : Matrix (Fin T'.rank) (Fin T.rank) D.host.E) (N : Matrix (Fin S.rank) (Fin S'.rank) D.host.E)
    (hN : ∀ y ∈ ΛS', N *ᵥ y ∈ ΛS) (hM : ∀ y ∈ ΛT, M *ᵥ y ∈ ΛT') (I : Ideal (𝓞 D.host.E))
    {z : Mx D T.rank S.rank} (hz : z ∈ hatMx (I • homLat ΛS ΛT)) :
    (rat M : Mx D T'.rank T.rank) * z * (rat N : Mx D S.rank S'.rank) ∈ hatMx (I • homLat ΛS' ΛT') := by
  have key : ∀ X ∈ I • homLat ΛS ΛT, M * X * N ∈ I • homLat ΛS' ΛT' := by
    intro X hX
    refine Submodule.smul_induction_on hX (fun r hr Y hY => ?_) (fun a b ha hb => ?_)
    · have e : M * (r • Y) * N = r • (M * Y * N) := by rw [Matrix.mul_smul, Matrix.smul_mul]
      rw [e]
      refine Submodule.smul_mem_smul hr ?_
      intro y hy
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact hM _ (hY _ (hN y hy))
    · rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem ha hb
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, X, hX, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, M * X * N, key X hX, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul, TensorProduct.tmul_sum, rat_entry,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  | zero => rw [Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg, Matrix.neg_mul]; exact neg_mem hx

end GlobalTheory.CoreComp

namespace GlobalTheory.CoreComp

theorem core_mem_latCore : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    ∀ u ∈ (pcFB W F σ h h').Γ₀, ((F.oB σ h').resT _ u).1 ∈ latCore G (2 * σ + 2) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h' u hu
  have I := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF
  have sd : ∀ X : Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → IsSelfDualC (G.V X) (G.Λ X) :=
    fun X h1 h2 => (G.isV h1 h2).sd
  have sdG3 : IsSelfDualC (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0)) :=
    sd _ ⟨by omega, Nat.zero_le _⟩ (fun j e => by cases e)
  have sdG2 : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    sd _ ⟨h', Nat.zero_le _⟩ (fun j e => by cases e)
  have sdC3 : IsSelfDualC (G.V (.core (2 * σ + 2 + 1))) (G.Λ (.core (2 * σ + 2 + 1))) :=
    sd (.core (2 * σ + 2 + 1)) (show 2 * σ + 2 + 1 ≤ D.R.m by omega) (fun j e => by cases e)
  have sdC2 : IsSelfDualC (G.V (.core (2 * σ + 2))) (G.Λ (.core (2 * σ + 2))) :=
    sd (.core (2 * σ + 2)) (show 2 * σ + 2 ≤ D.R.m by omega) (fun j e => by cases e)
  have sd0 : IsSelfDualC (F.V₀ σ) (lat0 F σ h') := (I.2.1 σ h').1
  have hMJ : ∀ v, MonoAt (F.dJ (σ + 1) h) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.core (2 * (σ + 1) + 1))) v :=
    fun v => ((I.2.1 (σ + 1) h).2.1 v).2
  have hMB : ∀ v, MonoAt (F.dB σ h') (G.Λ (.grid (2 * σ + 2) 0)) (lat0 F σ h') v := fun v => ((I.2.1 σ h').2.1 v).1
  have hOB := (I.2.1 σ h').2.2.2

  have hN : ∀ y ∈ G.Λ (.core (2 * σ + 2 + 1)), (F.dJ (σ + 1) h).i₀ *ᵥ y ∈ G.Λ (.grid (2 * σ + 2 + 1) 0) :=
    fun y hy => witt_core_inclusion_maps_split_lattices (F.dJ (σ + 1) h) sdG3.1 sdC3.1 hMJ hy
  have hMm : ∀ y ∈ G.Λ (.grid (2 * σ + 2) 0),
      ((F.oB σ h').qA * (F.dB σ h').q0) *ᵥ y ∈ G.Λ (.core (2 * σ + 2)) := fun y hy => by
    rw [← Matrix.mulVec_mulVec]
    exact qA_maps (F.oB σ h') sd0.1 sdC2.1 hOB (witt_core_projection_maps_split_lattices (F.dB σ h') sdG2.1 sd0.1 hMB hy)
  have hx := AddSubgroup.mem_comap.1 hu
  set x := ((F.dJ (σ + 1) h).ext0 _).comp ((F.dB σ h').inc0 _) u with hxdef
  have hc : ((F.oB σ h').resT _ u).1 =
      (rat ((F.oB σ h').qA * (F.dB σ h').q0) : Mx D _ _) * x * (rat (F.dJ (σ + 1) h).i₀ : Mx D _ _) := by
    rw [OrthDec.resT_apply, rat_mul, hxdef]
    change (F.oB σ h').pA * u = (F.oB σ h').pA * (F.dB σ h').p0 * ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) *
      (F.dJ (σ + 1) h).j0
    have e1 : (F.dB σ h').p0 * (F.dB σ h').j0 = 1 := HypDec.p0_j0 _
    have e2 : (F.dJ (σ + 1) h).p0 * (F.dJ (σ + 1) h).j0 = 1 := HypDec.p0_j0 _
    calc (F.oB σ h').pA * u = (F.oB σ h').pA * (((F.dB σ h').p0 * (F.dB σ h').j0) * u *
          ((F.dJ (σ + 1) h).p0 * (F.dJ (σ + 1) h).j0)) := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [hc]
  refine ⟨?_, fun e he => ?_⟩
  · exact latO_sandwich _ _ (isSelfDualC_neg sdG3) (isSelfDualC_neg sdC3) sdC2 hN hMm hx.1
  · rw [← Matrix.smul_mul, ← Matrix.mul_smul]
    exact hatMx_sandwich _ _ hN hMm _ (hx.2 e he)

end GlobalTheory.CoreComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselPiecesFiniteAdelicLattices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin

section Transfer

variable {D : D7}

theorem mxAt_mul_right {m n k : ℕ} {x : Mx D m n} (hx : MxAt (fun _ => True) x) (M : Mx D n k) :
    MxAt (fun _ => True) (x ⬝ M) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

theorem mxAt_mul_left {m n k : ℕ} {x : Mx D m n} (hx : MxAt (fun _ => True) x) (M : Mx D k m) :
    MxAt (fun _ => True) (M ⬝ x) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)

theorem finLat_comap {m n m' n' : ℕ} {Γ : AddSubgroup (Mx D m' n')} (hΓ : FinLat Γ) (f : Mx D m n →+ Mx D m' n')
    (g : Mx D m' n' → Mx D m n) (hf : Continuous f) (hg : Continuous g) (hgf : ∀ a, g (f a) = a)
    (hfM : ∀ a, MxAt (fun _ => True) a → MxAt (fun _ => True) (f a))
    (hgM : ∀ b, MxAt (fun _ => True) b → MxAt (fun _ => True) (g b)) : FinLat (Γ.comap f) where
  fin a ha := hgf a ▸ hgM _ (hΓ.fin _ ha)
  cpt := by
    haveI : T2Space (Mx D m' n') := (GlobalTheory.MixModel.lattice_Mx D m' n').2.2.2.1
    have hc : IsClosed ((Γ.comap f : AddSubgroup _) : Set (Mx D m n)) := hΓ.cpt.isClosed.preimage hf
    refine (hΓ.cpt.image hg).of_isClosed_subset hc ?_
    intro a ha
    exact ⟨f a, ha, hgf a⟩
  opn := by
    obtain ⟨U, hU, h0, hUΓ⟩ := hΓ.opn
    exact ⟨f ⁻¹' U, hU.preimage hf, by simpa using h0, fun a ha hA => hUΓ _ ha (hfM a hA)⟩

end Transfer

theorem pcFB_fin : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    FinLat (pcFB W F σ h h').A₁ ∧ FinLat (pcFB W F σ h h').B₁ ∧ FinLat (pcFB W F σ h h').B₂ ∧
      ∀ u ∈ (pcFB W F σ h h').Γ₀, MxAt (fun _ => True) u := by
  intro D hOff T L μ0 hL sc G W M hM F hF σ h h'
  have hlat := (GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hOff T L μ0 hL sc G W M hM F hF).1 (2 * σ + 2) (by omega)
  have hRow : FinLat (latRow G (2 * σ + 2)) := hlat.1
  have hBig : FinLat (latBig G (2 * σ + 2)) := hlat.2.2.1
  set dV := F.dJ (σ + 1) h
  set dW := F.dB σ h'
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact finLat_comap hRow (dV.extX _) (fun w => w ⬝ dV.jX) (continuous_id.matrix_mul continuous_const)
      (continuous_id.matrix_mul continuous_const)
      (fun a => by simp only [HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one])
      (fun a ha => mxAt_mul_right ha _) (fun b hb => mxAt_mul_right hb _)
  · exact finLat_comap hBig ((dV.ext0 _).comp (dW.incX _)) (fun w => dW.pX ⬝ (w ⬝ dV.j0))
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
      (continuous_const.matrix_mul (continuous_id.matrix_mul continuous_const))
      (fun a => by simp only [AddMonoidHom.comp_apply, HypDec.matrixExtendByZero_apply, HypDec.incX_apply, Matrix.mul_assoc,
        HypDec.p0_j0, Matrix.mul_one, ← Matrix.mul_assoc dW.pX, HypDec.pX_jX, Matrix.one_mul])
      (fun a ha => mxAt_mul_right (mxAt_mul_left ha _) _) (fun b hb => mxAt_mul_left (mxAt_mul_right hb _) _)
  · exact finLat_comap hBig ((dV.ext0 _).comp (dW.incY _)) (fun w => dW.pY ⬝ (w ⬝ dV.j0))
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
      (continuous_const.matrix_mul (continuous_id.matrix_mul continuous_const))
      (fun a => by simp only [AddMonoidHom.comp_apply, HypDec.matrixExtendByZero_apply, HypDec.incY_apply, Matrix.mul_assoc,
        HypDec.p0_j0, Matrix.mul_one, ← Matrix.mul_assoc dW.pY, HypDec.pY_jY, Matrix.one_mul])
      (fun a ha => mxAt_mul_right (mxAt_mul_left ha _) _) (fun b hb => mxAt_mul_left (mxAt_mul_right hb _) _)
  · intro u hu
    have h1 := hRow.fin _ hu
    have h2 : dW.p0 ⬝ (((dV.ext0 _).comp (dW.inc0 _)) u ⬝ dV.j0) = u := by
      simp only [AddMonoidHom.comp_apply, HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_assoc,
        HypDec.p0_j0, Matrix.mul_one, ← Matrix.mul_assoc dW.p0, Matrix.one_mul]
    rw [← h2]
    exact mxAt_mul_left (mxAt_mul_right h1 _) _

end GlobalTheory.AscFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowColumnProductDataHaveVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.VecsLast

open ValuativeRel

theorem exists_nat_val_le {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (d : ℕ) :
    ∃ N : ℕ, 0 < N ∧ valuation k (N : k) ≤ valuation k ((ϖ ^ d : kˣ) : k) := by
  refine ⟨GlobalTheory.SplitWeil.resCard k ^ d, pow_pos ?_ d, ?_⟩
  · unfold GlobalTheory.SplitWeil.resCard
    exact Nat.card_pos
  · rw [Nat.cast_pow, map_pow, Units.val_pow_eq_pow_val, map_pow, hϖ]
    exact pow_le_pow_left₀ zero_le' (le_uniformizer_iff.2 GlobalTheory.RootEx.UnipPow.valuation_resCard_lt_one) d

end GlobalTheory.VecsLast

namespace GlobalTheory.VecsLast

open ValuativeRel

variable {D : D7}

theorem isSBHalf_prodCoord {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {P : Finset (Pl D.host.E)}
    {A B : P → Type} [∀ w, Fintype (A w)] [∀ w, Fintype (B w)]
    (c : ∀ w : P, Mx D m n →+ Matrix (A w) (B w) (Kw w.1))
    (hc : ∀ z, IsHalf e z → (z ∈ Λ ↔ ∀ w : P, GlobalTheory.StepData.IntM (c w z)))
    (d : P → ℕ) (ψ : ∀ w : P, Matrix (A w) (B w) (Kw w.1) → ℂ)
    (h1 : ∀ w M, ψ w M ≠ 0 → GlobalTheory.StepData.IntM M)
    (h2 : ∀ w M N, (∀ i j, valuation (Kw w.1) (N i j) ≤ valuation (Kw w.1) ((unifAt w.1 ^ d w : (Kw w.1)ˣ) : Kw w.1)) →
      ψ w (M + N) = ψ w M) :
    IsSBHalf e Λ (fun z => if IsHalf e z then ∏ w : P, ψ w (c w z) else 0) := by
  classical
  choose N hN0 hN using fun w : P => exists_nat_val_le (isUnif_unifAt (D := D) w.1) (d w)
  have hk0 : 0 < ∏ w : P, N w := Finset.prod_pos fun w _ => hN0 w
  have hhalf : ∀ (a : ℕ) (u : Mx D m n), IsHalf e u → IsHalf e (a • u) := fun a u hu i j => by
    show e * (a • u) i j = (a • u) i j
    rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hu i j]
  have hadd : ∀ {t u : Mx D m n}, IsHalf e u → (IsHalf e (t + u) ↔ IsHalf e t) := fun {t u} hu => by
    constructor
    · intro h i j
      have h1 := h i j
      have h2 := hu i j
      simp only [Matrix.add_apply, mul_add] at h1
      linear_combination h1 - h2
    · intro h i j
      simp only [Matrix.add_apply, mul_add, h i j, hu i j]
  refine ⟨fun t ht => ?_, ∏ w : P, N w, hk0, fun u hu hue t => ?_, fun t ht => ?_⟩
  · by_contra hc'
    exact ht (if_neg hc')
  · have hku := hhalf (∏ w : P, N w) u hue
    dsimp only
    by_cases ht : IsHalf e t
    · rw [if_pos ((hadd hku).2 ht), if_pos ht]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [map_add, map_nsmul]
      refine h2 w _ _ fun i j => ?_
      have hint := (hc u hue).1 hu w i j
      rw [Valuation.mem_integer_iff] at hint
      rw [Matrix.smul_apply, nsmul_eq_mul, map_mul]
      have hle : valuation (Kw w.1) (((∏ w : P, N w : ℕ) : Kw w.1)) ≤ valuation (Kw w.1) (N w : Kw w.1) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w), Nat.cast_mul, map_mul]
        exact mul_le_of_le_one_right' (GlobalTheory.RootEx.UnipPow.valuation_natCast_le_one _)
      calc valuation (Kw w.1) (((∏ w : P, N w : ℕ) : Kw w.1)) * valuation (Kw w.1) (c w u i j)
          ≤ valuation (Kw w.1) (((∏ w : P, N w : ℕ) : Kw w.1)) := mul_le_of_le_one_right' hint
        _ ≤ _ := hle.trans (hN w)
    · rw [if_neg (fun h => ht ((hadd hku).1 h)), if_neg ht]
  · dsimp only at ht
    have hE : IsHalf e t := by
      by_contra h
      exact ht (if_neg h)
    rw [if_pos hE] at ht
    have hmem : t ∈ Λ := (hc t hE).2 fun w => h1 w _ (Finset.prod_ne_zero_iff.1 ht w (Finset.mem_univ _))
    exact Λ.nsmul_mem hmem _

end GlobalTheory.VecsLast

namespace GlobalTheory.VecsLast

open ValuativeRel

variable {D : D7}

theorem isSBHalf_frames {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} (hβS : IsFrame βS ΛS) (hβT : IsFrame βT ΛT)
    {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (hAA : ∀ w ∈ P, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1))
    {A B : P → Type} [∀ w, Fintype (A w)] [∀ w, Fintype (B w)]
    (c : ∀ w : P, WO S T →+ Matrix (A w) (B w) (Kw w.1))
    (hc : ∀ (w : P) z, GlobalTheory.StepData.IntM (c w z) ↔
      GlobalTheory.StepData.IntM ((Comparison₂.fr βT βS (z.map (toEAf D))).map (cpt (D := D) w.1)))
    (d : P → ℕ) (ψ : ∀ w : P, Matrix (A w) (B w) (Kw w.1) → ℂ)
    (h1 : ∀ w M, ψ w M ≠ 0 → GlobalTheory.StepData.IntM M)
    (h2 : ∀ w M N, (∀ i j, valuation (Kw w.1) (N i j) ≤ valuation (Kw w.1) ((unifAt w.1 ^ d w : (Kw w.1)ˣ) : Kw w.1)) →
      ψ w (M + N) = ψ w M) :
    IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
      (fun z => if IsHalf e z then ∏ w : P, ψ w (c w z) else 0) := by
  refine isSBHalf_prodCoord c (fun z hz => ?_) d ψ h1 h2
  rw [GlobalTheory.ColLatDict.mem_latO_iff_intM hS hT hβS hβT he hAA z hz]
  exact ⟨fun h w => (hc w z).2 (h w.1 w.2), fun h w hw => (hc ⟨w, hw⟩ z).1 (h ⟨w, hw⟩)⟩

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem coord_add (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : ℕ × ℕ} (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m)
    (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m)
    (x y : Matrix (Fin (G.V (.grid X.1 X.2)).rank) (Fin (G.V (.grid Y.1 Y.2)).rank) (Kw w)) :
    B.coord t w hX hY (x + y) = B.coord t w hX hY x + B.coord t w hX hY y := by
  unfold Frames.coord
  rw [Matrix.mul_add, Matrix.add_mul]
  rfl

noncomputable def coordHom (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : ℕ × ℕ} (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m)
    (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m) :
    Matrix (Fin (G.V (.grid X.1 X.2)).rank) (Fin (G.V (.grid Y.1 Y.2)).rank) (AE D) →+
      Matrix (Fin ((locGrid G t w).rank Y)) (Fin ((locGrid G t w).rank X)) (Kw w) :=
  AddMonoidHom.mk' (fun z => B.coord t w hX hY (z.map fun a => cpt w (toEAf D a))) fun x y => by
    rw [Matrix.map_add _ (fun a b => by rw [RingHom.map_add, RingHom.map_add])]
    exact coord_add B t w hX hY _ _

theorem coordHom_int_iff (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : ℕ × ℕ} (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m)
    (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m) (z : Matrix (Fin (G.V (.grid X.1 X.2)).rank) (Fin (G.V (.grid Y.1 Y.2)).rank) (AE D)) :
    GlobalTheory.StepData.IntM (coordHom B t w hX hY z) ↔
      GlobalTheory.StepData.IntM ((Comparison₂.fr (B.β X.1 X.2) (B.β Y.1 Y.2) (z.map (toEAf D))).map (cpt (D := D) w)) :=
  GlobalTheory.MixVacBig.coord_int_iff B t w hX hY z

theorem natDatum_props {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} {ϖ : kˣ} {dp : ℕ} {φ : Matrix a b k → ℂ} (h : GlobalTheory.SplitFlip.IsNatDatum ϖ dp φ) :
    (∀ M, φ M ≠ 0 → GlobalTheory.StepData.IntM M) ∧
      ∀ M N, (∀ i j, valuation k (N i j) ≤ valuation k ((ϖ ^ dp : kˣ) : k)) → φ (M + N) = φ M := by
  obtain ⟨hs, hi⟩ := h
  refine ⟨fun M hM i j => ?_, fun M N hN => hi M N ?_⟩
  · by_contra hc
    refine hM (hs M fun hm => hc ?_)
    have := GlobalTheory.SplitFlip.FourierDepth.mem_matLat_diagLat.1 hm i j
    rw [Valuation.mem_integer_iff]
    simpa using this
  · exact GlobalTheory.SplitFlip.FourierDepth.mem_matLat_smul_stdLat.2 hN

end GlobalTheory.VecsLast

namespace GlobalTheory.VecsLast

theorem vecs_last : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → (∀ j : Fin D.R.m, ∃ f, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) f) ∧ ∀ i : Fin D.R.m, ∃ f, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) f := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t e he φ hφ
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hAA : ∀ w ∈ locPl ch.G t, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := by
    intro w hw
    have hb := GlobalTheory.FunObj.Good.badInt_notMem hL (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s) (hch.guard t) hw
    have h2q := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro _ rfl))
    have hN := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro_left _ rfl))
    refine ⟨fun a ha => ?_, ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩⟩
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_le_one_of_mem h2q (Or.inl ha)
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_nat hN
  refine ⟨fun j => ?_, fun i => ?_⟩
  · have hS : IsSelfDualC (ch.G.pS (.mu t D.R.m j)) (ch.G.latS (.mu t D.R.m j)) :=
      (node_isV ch.G hL (X := .grid D.R.m j) ⟨le_rfl, j.2.le⟩).sd
    have hT : IsSelfDualC (ch.G.pT (.mu t D.R.m j)) (ch.G.latT (.mu t D.R.m j)) :=
      (node_isV ch.G hL (X := .grid D.R.m ((j : ℕ) + 1)) ⟨le_rfl, j.2⟩).sd
    have hβS := ch.S.B.isFrame_β hL (i := D.R.m) (j := (j : ℕ)) le_rfl j.2.le
    have hβT := ch.S.B.isFrame_β hL (i := D.R.m) (j := (j : ℕ) + 1) le_rfl j.2
    have hmem : GlobalTheory.SplitFlip.Edge.theta D.R.m j ∈ GlobalTheory.SplitFlip.oppositePath D.R.m := by
      simp [GlobalTheory.SplitFlip.oppositePath]
    have hSB := isSBHalf_frames hS hT hβS hβT he hAA
      (fun w => coordHom ch.S.B t w.1 (X := (D.R.m, (j : ℕ) + 1)) (Y := (D.R.m, (j : ℕ))) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩)
      (fun w z => coordHom_int_iff ch.S.B t w.1 (X := (D.R.m, (j : ℕ) + 1)) (Y := (D.R.m, (j : ℕ))) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ z) (fun w => depthAt ch.G w.1) (fun w => φ w (.theta D.R.m j))
      (fun w => (natDatum_props (hφ w _ hmem)).1) (fun w => (natDatum_props (hφ w _ hmem)).2)
    obtain ⟨f, hf⟩ := GlobalTheory.FunObj.VecEx.exists_isThetaAt_of_vac hS.1 hT.1 hS hT he (ch.rm.vT_is t D.R.m j le_rfl j.2) hSB
    exact ⟨f, hSB, hf⟩
  · have hS : IsSelfDualC (ch.G.pS (.chi i D.R.m)) (ch.G.latS (.chi i D.R.m)) :=
      isSelfDualC_neg (node_isV ch.G hL (X := .grid ((i : ℕ) + 1) D.R.m) ⟨i.2, le_rfl⟩).sd
    have hT : IsSelfDualC (ch.G.pT (.chi i D.R.m)) (ch.G.latT (.chi i D.R.m)) :=
      (node_isV ch.G hL (X := .grid (i : ℕ) D.R.m) ⟨i.2.le, le_rfl⟩).sd
    have hβS := ch.S.B.isFrame_β hL (i := (i : ℕ) + 1) (j := D.R.m) i.2 le_rfl
    have hβT := ch.S.B.isFrame_β hL (i := (i : ℕ)) (j := D.R.m) i.2.le le_rfl
    have hmem : GlobalTheory.SplitFlip.Edge.ex i D.R.m ∈ GlobalTheory.SplitFlip.oppositePath D.R.m := by
      simp [GlobalTheory.SplitFlip.oppositePath]
    have hSB := isSBHalf_frames hS hT hβS hβT he hAA
      (fun w => coordHom ch.S.B t w.1 (X := ((i : ℕ), D.R.m)) (Y := ((i : ℕ) + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩)
      (fun w z => coordHom_int_iff ch.S.B t w.1 (X := ((i : ℕ), D.R.m)) (Y := ((i : ℕ) + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ z) (fun w => depthAt ch.G w.1) (fun w => φ w (.ex i D.R.m))
      (fun w => (natDatum_props (hφ w _ hmem)).1) (fun w => (natDatum_props (hφ w _ hmem)).2)
    obtain ⟨f, hf⟩ := GlobalTheory.FunObj.VecEx.exists_isThetaAt_of_vac hS.1 hT.1 hS hT he (ch.rm.vX_is i D.R.m i.2 le_rfl) hSB
    exact ⟨f, hSB, hf⟩

end GlobalTheory.VecsLast
end

