import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0003
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0001
import Formalism.FlagUnipotentLattices.FlagUnipotentLatticeOfRel
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0004
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLevelGen
section
noncomputable section

namespace Formalism.MainNotions.BridgeLevelGen

open MeasureTheory NumberField Formalism.MainNotions.S Formalism.MainNotions.BridgeLevelIdx
open scoped ENNReal TensorProduct

theorem finrank_E (I : AutInst) : Module.finrank ℚ I.E = 2 * I.f := by
  rw [← Module.finrank_mul_finrank ℚ I.F I.E, I.cm.deg2]
  show _ = 2 * Module.finrank ℚ I.F
  ring

theorem incl_mem (I : AutInst) (b : 𝓞 I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E b) ∈ IntAf I.F I.E :=
  Subring.subset_closure (Or.inl ⟨⟨_, ⟨b, rfl⟩⟩, rfl⟩)

theorem levelGen_holds (I : AutInst) (g : ℕ) (hg : 1 ≤ g) : LevelGen I g := by
  classical
  have hg0 : ((g : 𝓞 I.E)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨m, ℓ, hm, hℓ, hgen⟩ :=
    Formalism.MainNotions.BridgeLevelGenA.gen_mod (R := 𝓞 I.E) (K := I.E) (g : 𝓞 I.E) hg0 I.L I.L_fg
  set ι : (Fin I.n → I.E) → (Fin I.n → I.E ⊗[I.F] Af I.F) :=
    fun x i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i) with hι
  have hιL : ∀ x ∈ I.L, ι x ∈ I.Lf := fun x hx => Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩

  have hgenA : ∀ y ∈ I.Lf, ∃ (a : Fin m → IntAf I.F I.E) (z : Fin I.n → I.E ⊗[I.F] Af I.F), z ∈ I.Lf ∧
      y = ∑ j, (a j : I.E ⊗[I.F] Af I.F) • ι (ℓ j) + (g : I.E ⊗[I.F] Af I.F) • z := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨x, hx⟩, rfl⟩ := hy
      obtain ⟨a, w, hw, hxw⟩ := hgen x hx
      refine ⟨fun j => ⟨_, incl_mem I (a j)⟩, ι w, hιL w hw, ?_⟩
      show ι x = _
      rw [hxw]
      funext i
      simp only [hι, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def, map_add, map_sum, map_mul, map_natCast]
    | zero => exact ⟨0, 0, I.Lf.zero_mem, by simp⟩
    | add y y' _ _ hy hy' =>
      obtain ⟨a, z, hz, rfl⟩ := hy
      obtain ⟨a', z', hz', rfl⟩ := hy'
      refine ⟨a + a', z + z', I.Lf.add_mem hz hz', ?_⟩
      simp only [Pi.add_apply, Subring.coe_add, add_smul, Finset.sum_add_distrib, smul_add]
      abel
    | smul c y _ hy =>
      obtain ⟨a, z, hz, rfl⟩ := hy
      refine ⟨fun j => c * a j, (c : I.E ⊗[I.F] Af I.F) • z, lf_csmul c hz, ?_⟩
      rw [Subring.smul_def]
      simp only [smul_add, Finset.smul_sum, smul_smul, Subring.coe_mul]
      rw [mul_comm (c : I.E ⊗[I.F] Af I.F) (g : I.E ⊗[I.F] Af I.F)]

  let Q := 𝓞 I.E ⧸ Ideal.span {(g : 𝓞 I.E)}
  have hQ : Nat.card Q = g ^ (2 * I.f) := by
    rw [← finrank_E]; exact Formalism.HermitianLatticeCounting.Final.FlagKernelVanishing.residueRingCard I.E g
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; positivity)
  letI : Fintype Q := Fintype.ofFinite Q
  let R' : Finset (𝓞 I.E) := Finset.univ.image (fun q : Q => q.out)
  have hR' : R'.card ≤ g ^ (2 * I.f) := by
    calc R'.card ≤ (Finset.univ : Finset Q).card := Finset.card_image_le
      _ = g ^ (2 * I.f) := by rw [Finset.card_univ, Fintype.card_eq_nat_card, hQ]
  let S : Finset (Fin I.n → I.E ⊗[I.F] Af I.F) := Finset.univ.image (fun b : Fin m → R' =>
    ∑ j, Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E (b j : 𝓞 I.E)) • ι (ℓ j))
  have hS : S.card ≤ g ^ (2 * I.f * I.n) := by
    calc S.card ≤ (Finset.univ : Finset (Fin m → R')).card := Finset.card_image_le
      _ = R'.card ^ m := by simp
      _ ≤ (g ^ (2 * I.f)) ^ m := Nat.pow_le_pow_left hR' m
      _ ≤ (g ^ (2 * I.f)) ^ I.n := Nat.pow_le_pow_right (pow_pos (by omega) _) hm
      _ = g ^ (2 * I.f * I.n) := by rw [← pow_mul]
  refine ⟨m, fun j => ι (ℓ j), S, hm, hS, fun j => hιL _ (hℓ j), hgenA, fun y hy => ?_⟩
  obtain ⟨a, z, hz, rfl⟩ := hgenA y hy
  have hloc : ∀ j, ∃ β : 𝓞 I.E, β ∈ R' ∧ ∃ c ∈ IntAf I.F I.E, (a j : I.E ⊗[I.F] Af I.F) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E β) + (g : I.E ⊗[I.F] Af I.F) * c := by
    intro j
    obtain ⟨b, ⟨β, rfl⟩, c, hc, e⟩ := Formalism.MainNotions.BridgeLevelGenB.dense_modE g hg (a j : I.E ⊗[I.F] Af I.F) (a j).2
    set β' : 𝓞 I.E := (Ideal.Quotient.mk (Ideal.span {(g : 𝓞 I.E)}) β).out with hβ'
    have hmem : β' - β ∈ Ideal.span {(g : 𝓞 I.E)} :=
      Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out _)
    obtain ⟨δ, hδ⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨β', Finset.mem_image_of_mem _ (Finset.mem_univ _),
      c - Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E δ),
      sub_mem hc (incl_mem I δ), ?_⟩
    have hβ : β = β' - δ * (g : 𝓞 I.E) := by rw [hδ]; ring
    rw [e, hβ]
    simp only [map_sub, map_mul, map_natCast, Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply]
    rw [TensorProduct.sub_tmul, show (algebraMap (𝓞 I.E) I.E δ * (g : I.E)) ⊗ₜ[I.F] (1 : Af I.F) =
      (algebraMap (𝓞 I.E) I.E δ) ⊗ₜ[I.F] (1 : Af I.F) * (g : I.E ⊗[I.F] Af I.F) by
        rw [← map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := I.F) (B := Af I.F)) g,
          Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]]
    ring
  choose β hβR c hc hac using hloc
  refine ⟨∑ j, Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E (β j)) • ι (ℓ j),
    Finset.mem_image.2 ⟨fun j => ⟨β j, hβR j⟩, Finset.mem_univ _, rfl⟩,
    ∑ j, (c j : I.E ⊗[I.F] Af I.F) • ι (ℓ j) + z, ?_, ?_⟩
  · refine I.Lf.add_mem (Submodule.sum_mem _ fun j _ => ?_) hz
    exact lf_csmul ⟨c j, hc j⟩ (hιL _ (hℓ j))
  · simp only [hac, add_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum, smul_smul]
    abel

theorem levelIdx (I : AutInst) (μf : Measure I.Gf) [μf.IsMulLeftInvariant] {g : ℕ} (hg : 1 ≤ g) :
    μf I.Kset ≤ ((g ^ (2 * I.n ^ 2 * I.f) : ℕ) : ℝ≥0∞) * μf (I.Kg g) :=
  levelIdx_holds μf hg (levelGen_holds I g hg)

end Formalism.MainNotions.BridgeLevelGen

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.PSDKOnOfPSDK
section
open Matrix MeasureTheory NumberField Filter Topology

noncomputable section

namespace Formalism.MainNotions.S.LocalFrameAxioms

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

def LocMatch (D : D7) (T T' : ℝ) (x : LocalDataRealPlace D) (B : LocBessel D.R.k D.R.rS) : Prop :=
  B.lam = x.lam ∧ B.u = x.u ∧ B.u' = x.u' ∧ Tz D.R.k D.R.rS B.z = T ∧ Tz D.R.k D.R.rS B.z' = T' ∧
    B.ε = epsSH D.R

def FrameAx (D : D7) (δ : D.host.E) (L : LatticeDataWithDual D) (B : D.what₂.Tau → LocBessel D.R.k D.R.rS) : Prop :=
  ∃ ϱ : ℝ, IsFrameScale D L ϱ ∧ ∀ v, (B v).c = cPsi D δ v / (ϱ : ℂ)

def PsiAx (D : D7) (δ : D.host.E) : Prop :=
  δ ≠ 0 ∧ ((∀ v, (plEmb D v δ).re = 0) ∨ ∀ v, (plEmb D v δ).im = 0)

theorem k_le_nS (D : D7) : D.R.k ≤ 2 * D.R.rS + D.R.k + 1 := by omega

def Nlet (D : D7) (Kst : ℕ) : ℝ := 4 * (Kst : ℝ) * ((D.R.rS : ℝ) + 1)

section Arith

open scoped ComplexOrder

variable (D : D7)

def InProd (Sg : ℕ → ℕ → Finset D.host.E) : ℕ → List (D.host.E × ℕ) → Prop
  | _, [] => True
  | a, (t, s) :: bs => t ∈ Sg (a + 1) s ∧ InProd Sg (a + s) bs

def headsOf (Sg : ℕ → ℕ → Finset D.host.E) (j : ℕ) : Set (Point D.host.E j) := {h | InProd D Sg 0 h.1}

def PSDKOn {α : Type*} (S : Set α) (K : α → α → ℂ) : Prop :=
  ∀ (X : Finset α) (a : α → ℂ), (∀ p ∈ X, p ∈ S) → 0 ≤ ∑ p ∈ X, ∑ q ∈ X, star (a p) * K p q * a q

def KLEOn {α : Type*} (S : Set α) (K L : α → α → ℂ) : Prop := PSDKOn S (fun p q => L p q - K p q)

theorem PSDKOn_of_PSDK {α : Type*} {K : α → α → ℂ} (h : PSDK K) (S : Set α) : PSDKOn S K := fun X a _ => h X a

def ArithAxF (L : LatticeDataWithDual D) (Kd : KernelData D) : Prop :=
  (∀ p q, Kd.K 0 p q = 1) ∧
  (∀ i, i ≤ D.R.rS + 1 → PSDK (Kd.K i)) ∧
  (∀ i, 1 ≤ i → i ≤ D.R.rS + 1 → 0 ≤ Kd.e i ∧ Kd.e i ≤ 1) ∧

  (∀ (j s : ℕ) (hs : 1 ≤ s), j + s ≤ D.R.rS + 1 → ∀ (h h' : Point D.host.E j) (t t' : D.host.E)
      (ht : t ≠ 0) (ht' : t' ≠ 0),
      Kd.K (j + s) (ptSnoc D h t ht s hs) (ptSnoc D h' t' ht' s hs) ≠ 0 →
        (if j + s = D.R.rS + 1 ∧ s = 1 then t = t' else t⁻¹ - t'⁻¹ ∈ L.La' (j + 1) s)) ∧

  ∀ Sg : ℕ → ℕ → Finset D.host.E,
    ∃ Th : (j s : ℕ) → D.host.E → Point D.host.E j → Point D.host.E j → ℂ,
    ∀ (j s : ℕ) (hs : 1 ≤ s), j + s ≤ D.R.rS + 1 →
      (∀ (t : D.host.E) (ht : t ≠ 0), t ∈ Sg (j + 1) s →
        KLEOn (headsOf D Sg j)
          (fun h h' : Point D.host.E j => Kd.K (j + s) (ptSnoc D h t ht s hs) (ptSnoc D h' t ht s hs)) (Th j s t)) ∧
      (∀ t, ∀ l ∈ L.La (j + 1) s, ∀ h ∈ headsOf D Sg j, ∀ h' ∈ headsOf D Sg j, Th j s (t + l) h h' = Th j s t h h') ∧
      (∀ t, PSDKOn (headsOf D Sg j) (Th j s t)) ∧
      (∀ X : Finset D.host.E, (∀ t ∈ X, ∀ t' ∈ X, t - t' ∈ L.La (j + 1) s → t = t') →
        KLEOn (headsOf D Sg j) (fun h h' => ∑ t ∈ X, Th j s t h h')
          (fun h h' => (1 + (Kd.e (j + s) : ℂ)) * Kd.K j h h'))

variable {D}

theorem _root_.Formalism.MainNotions.S.ArithAx.toF {L : LatticeDataWithDual D} {Kd : KernelData D} (h : ArithAx D L Kd) : ArithAxF D L Kd := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  refine ⟨h0, h1, h2, h3, fun Sg => ⟨Kd.Th, fun j s hs hjs => ?_⟩⟩
  obtain ⟨a, b, c, d⟩ := h4 j s hs hjs
  exact ⟨fun t ht _ => PSDKOn_of_PSDK (a t ht) _, fun t l hl _ _ _ _ => by rw [b t l hl],
    fun t => PSDKOn_of_PSDK (c t) _, fun X hX => PSDKOn_of_PSDK (d X hX) _⟩

end Arith

def stThmA (D : D7) (C C' : ℝ) (Kst : ℕ) (Vm : ValMap D.R.k D.R.rS) : Prop :=
  ∀ (δ : D.host.E) (T T' : ℝ) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) (Kd : KernelData D)
    (B : D.what₂.Tau → LocBessel D.R.k D.R.rS)
    (f : ∀ v, Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → ((B v).Wq →L[ℂ] (B v).Wp))
    (μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ)
    (ι : Type) [Countable ι] (c : ι → Point D.host.E (D.R.rS + 1) → ℂ),
    4 ≤ Kst → 1 ≤ D.host.v →
    PsiAx D δ → LatAx D δ L → FrameAx D δ L B → ArithAxF D L Kd →
    (∀ v, LocMatch D T T' (x v) (B v) ∧ IsKFinCoefH (B v).σ (f v) ∧
      IsSection D.R.k D.R.rS (B v).z (B v).z' (μsec v)) →
    (∀ v, InterlaceS (k_le_nS D) (x v).u (x v).lam ∧ InterlaceS (k_le_nS D) (x v).u' (x v).lam) →
    (∀ v, (x v).u ≠ (x v).u') →
    (∀ v, GapAtLeast (epsSH D.R) (x v).lam
      (C * (D.R.m : ℝ) ^ ((9 : ℝ) / 2) * (Nlet D Kst * (D.R.r : ℝ) ^ 2 + (D.R.r : ℝ) ^ 3))) →
    (∀ v, IsCutS (x v).u (x v).u' (Set.Icc (x v).a (x v).b)) →
    (∀ v, (x v).a ≤ (x v).a1 ∧ (x v).a1 ≤ (x v).b1 ∧ (x v).b1 ≤ (x v).b ∧
      Nlet D Kst ^ 3 / 2 ≤ (x v).b1 - (x v).a1) →
    (∀ v, C * ((D.R.k : ℝ) * Nlet D Kst * ((D.R.rS : ℝ) + 1) ^ 2 +
        Nlet D Kst ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2 + Nlet D Kst ^ 3) ≤ (x v).b - (x v).a) →
    ((D.R.rS : ℝ) + 1) * (C / ThS D C C (Nlet D Kst) T T' δ x L) ^ D.R.f ≤ 1 →
    C' ≤ ThS D C C (Nlet D Kst) T T' δ x L →
    RowsAx (fun v => (B v).Wq →L[ℂ] (B v).Wp) (fun _ => hsInner) (Kd.K (D.R.rS + 1))
      (fun h => ptWeightG D L.ρ T T' h.1) c (fun v h => Vm.V (B v) (f v) (locBlocks D L.ρ v h.1)) →
    SRowForm (fun v => (B v).Wq →L[ℂ] (B v).Wp) (fun _ => hsInner) (fun h => ptWeightG D L.ρ T T' h.1) c
        (fun v h => Vm.V (B v) (f v) (locBlocks D L.ρ v h.1)) ≤
      ENNReal.ofReal ((1 + C * ((D.R.rS : ℝ) + 1) *
          (C / ThS D C C (Nlet D Kst) T T' δ x L) ^ D.R.f) *
          ∏ i ∈ Finset.Icc 1 (D.R.rS + 1), (1 + Kd.e i)) *
        jNorm2One (fun v => (B v).Wq →L[ℂ] (B v).Wp) (fun _ => hsNormSq) D.R.k D.R.rS T T' L.κ
          (fun v p => (B v).J (f v) (bigCell D.R.k D.R.rS p.1 (μsec v p.2)))

end Formalism.MainNotions.S.LocalFrameAxioms

end
end

