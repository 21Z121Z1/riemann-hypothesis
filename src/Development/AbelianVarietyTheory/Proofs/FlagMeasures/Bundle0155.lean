import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0137
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTotalMassLeGenericMass
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0140
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0139
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0141
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0142

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsProjector
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.WittInt

theorem exists_projector {O K V : Type} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (Λ : Submodule O V) (hfg : Λ.FG) (hspan : Submodule.span K (Λ : Set V) = ⊤) (W : Submodule K V) :
    ∃ P : V →ₗ[K] V, (∀ z ∈ Λ, P z ∈ Λ) ∧ (∀ z, P z ∈ W) ∧ ∀ z ∈ W, P z = z := by
  have hmul : ∀ y : V, ∃ s : nonZeroDivisors O, s • y ∈ Λ := fun y => by
    have hy : y ∈ Submodule.span K (Λ : Set V) := by rw [hspan]; trivial
    obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) K (Λ : Set V) y hy
    rw [Submodule.span_eq] at hs
    exact ⟨s, hs⟩
  have hunit : ∀ s : nonZeroDivisors O, IsUnit (algebraMap O (Module.End O V) s) := fun s => by
    have := isLocalizedModule_id (nonZeroDivisors O) V K
    exact IsLocalizedModule.map_units (S := nonZeroDivisors O) (LinearMap.id : V →ₗ[O] V) s
  have hloc : IsLocalizedModule (nonZeroDivisors O) Λ.subtype :=
    { map_units := hunit
      surj := fun y => by
        obtain ⟨s, hs⟩ := hmul y
        exact ⟨(⟨_, hs⟩, s), rfl⟩
      exists_of_eq := fun h => ⟨1, by rw [Subtype.ext h]⟩ }
  have hne : ∀ s : nonZeroDivisors O, algebraMap O K s ≠ 0 := fun s =>
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hsat : ∀ (s : nonZeroDivisors O) (v : V), (s : O) • v ∈ W → v ∈ W := fun s v h => by
    rw [← algebraMap_smul K] at h
    exact (W.smul_mem_iff (hne s)).1 h
  have : Module.Finite O Λ := Module.Finite.iff_fg.2 hfg
  let Q : Submodule O Λ := (W.restrictScalars O).comap Λ.subtype
  have : Module.Flat O (Λ ⧸ Q) := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨v, rfl⟩ := Q.mkQ_surjective q
    obtain ⟨c, hc⟩ := hq
    have h1 : Q.mkQ ((c : O) • v) = 0 := by rw [map_smul]; exact hc
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hsat c v h1
  have : Module.FinitePresentation O (Λ ⧸ Q) := Module.finitePresentation_of_finite _ _
  have : Module.Projective O (Λ ⧸ Q) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property Q.mkQ LinearMap.id Q.mkQ_surjective
  let π : Λ →ₗ[O] Λ := LinearMap.id - s ∘ₗ Q.mkQ
  have hπ : ∀ v, π v ∈ Q := by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have h1 : Q.mkQ (s (Q.mkQ v)) = Q.mkQ v := LinearMap.congr_fun hs _
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]
  have hπ' : ∀ v ∈ Q, π v = v := by
    intro v hv
    have h1 : Q.mkQ v = 0 := by rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h1, map_zero, sub_zero]
  let g : V →ₗ[K] V := LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) K
      (IsLocalizedModule.lift (nonZeroDivisors O) Λ.subtype (Λ.subtype ∘ₗ π) hunit)
  have hg : ∀ y : Λ, g y = π y := fun y =>
    IsLocalizedModule.lift_apply (nonZeroDivisors O) Λ.subtype _ hunit y
  refine ⟨g, fun z hz => ?_, fun z => ?_, fun z hz => ?_⟩
  · rw [hg ⟨z, hz⟩]
    exact (π _).2
  · obtain ⟨c, hc⟩ := hmul z
    refine hsat c _ ?_
    rw [← LinearMap.map_smul_of_tower]
    have := hg ⟨_, hc⟩
    rw [show g ((c : O) • z) = _ from this]
    exact hπ _
  · obtain ⟨c, hc⟩ := hmul z
    have h1 := hg ⟨_, hc⟩
    rw [hπ' ⟨_, hc⟩ ((W.restrictScalars O).smul_mem (c : O) hz)] at h1
    have h2 : g (algebraMap O K c • z) = algebraMap O K c • z := by
      rw [algebraMap_smul]; exact h1
    rw [map_smul] at h2
    exact smul_right_injective V (hne c) h2

section Form

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

theorem form_star {J : Matrix (Fin n) (Fin n) E} (hJ : Jᴴ = J) (x y : Fin n → E) :
    star (star x ⬝ᵥ (J *ᵥ y)) = star y ⬝ᵥ (J *ᵥ x) := by
  rw [← star_dotProduct_star, star_star, star_mulVec, hJ, dotProduct_mulVec, dotProduct_comm]

theorem form_adj {J : Matrix (Fin n) (Fin n) E} (hd : J.det ≠ 0) (M : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) :
    star (M *ᵥ x) ⬝ᵥ (J *ᵥ y) = star x ⬝ᵥ (J *ᵥ ((J⁻¹ * Mᴴ * J) *ᵥ y)) := by
  rw [mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (Ne.isUnit hd),
    Matrix.one_mul, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

theorem form_nondeg {J : Matrix (Fin n) (Fin n) E} (hd : J.det ≠ 0) (y : Fin n → E)
    (h : ∀ x : Fin n → E, star x ⬝ᵥ (J *ᵥ y) = 0) : y = 0 := by
  apply eq_zero_of_mulVec_eq_zero hd
  funext i
  have := h (Pi.single i 1)
  simpa [← Pi.single_star] using this

theorem exists_adjoint {J : Matrix (Fin n) (Fin n) E} (hd : J.det ≠ 0)
    (P : (Fin n → E) →ₗ[E] (Fin n → E)) :
    ∃ Q : (Fin n → E) →ₗ[E] (Fin n → E),
      (∀ x y, star (P x) ⬝ᵥ (J *ᵥ y) = star x ⬝ᵥ (J *ᵥ Q y)) ∧
      LinearMap.trace E _ Q = star (LinearMap.trace E _ P) := by
  obtain ⟨M, rfl⟩ := Matrix.toLin'.surjective P
  refine ⟨Matrix.toLin' (J⁻¹ * Mᴴ * J), fun x y => form_adj hd M x y, ?_⟩
  rw [Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, Matrix.trace_mul_cycle,
    mul_nonsing_inv _ (Ne.isUnit hd), Matrix.one_mul, trace_conjTranspose]

end Form

theorem split_of_trace (E : Type) [Field E] [NumberField E] [StarRing E] (w : 𝓞 E)
    (hw : (w : E) + star (w : E) = 1) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (hd : J.det ≠ 0)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsLattice E Λ)
    (hself : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range)
    (W : Submodule E (Fin n → E)) (hW : ∀ x ∈ W, ∀ y ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) :
    ∃ W' : Submodule E (Fin n → E), (∀ x ∈ W', ∀ y ∈ W', star x ⬝ᵥ (J *ᵥ y) = 0) ∧
      Module.finrank E W' = Module.finrank E W ∧
      (∀ y ∈ W', (∀ x ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → y = 0) ∧
      ∀ z ∈ Λ, ∃ x ∈ Λ, ∃ y ∈ Λ, x ∈ W ∧ y ∈ W' ∧
        ∀ t ∈ W ⊔ W', star t ⬝ᵥ (J *ᵥ (z - x - y)) = 0 := by
  obtain ⟨P, hPΛ, hPW, hPid⟩ := exists_projector Λ hΛ.fg hΛ.span_eq_top W
  obtain ⟨Q, hPQ, htr⟩ := exists_adjoint hd P
  have hQP : ∀ x y, star (Q x) ⬝ᵥ (J *ᵥ y) = star x ⬝ᵥ (J *ᵥ P y) := fun x y => by
    rw [← form_star hJ, ← hPQ, form_star hJ]
  have hQΛ : ∀ z ∈ Λ, Q z ∈ Λ := fun z hz => (hself _).2 fun y hy => by
    rw [← hPQ]; exact (hself z).1 hz _ (hPΛ y hy)
  have hQ0 : ∀ y, (∀ x ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → Q y = 0 := fun y hy =>
    form_nondeg hd _ fun x => by rw [← hPQ]; exact hy _ (hPW x)
  have hQW : ∀ y ∈ W, Q y = 0 := fun y hy => hQ0 y fun x hx => hW x hx y hy
  have hPP : ∀ y, P (P y) = P y := fun y => hPid _ (hPW y)
  have hQQ : ∀ y, Q (Q y) = Q y := fun y => by
    rw [← sub_eq_zero]
    refine form_nondeg hd _ fun x => ?_
    rw [mulVec_sub, dotProduct_sub, ← hPQ, ← hPQ, hPP, hPQ, sub_self]
  have hQPz : ∀ y, Q (P y) = 0 := fun y => hQW _ (hPW y)
  let T : (Fin n → E) →ₗ[E] (Fin n → E) := Q - (w : E) • (P ∘ₗ Q)
  have hT : ∀ y, T y = Q y - (w : E) • P (Q y) := fun y => rfl
  have hQT : ∀ y, Q (T y) = Q y := fun y => by
    rw [hT, map_sub, map_smul, hQPz, hQQ, smul_zero, sub_zero]
  have hTT : ∀ y, T (T y) = T y := fun y => by rw [hT (T y), hQT, hT]
  have hWT : ∀ x ∈ W, ∀ y, star x ⬝ᵥ (J *ᵥ T y) = star x ⬝ᵥ (J *ᵥ y) := fun x hx y => by
    rw [hT, mulVec_sub, dotProduct_sub, hW x hx _ (W.smul_mem _ (hPW _)), sub_zero, ← hPQ, hPid x hx]
  have hTl : ∀ x y, star (T x) ⬝ᵥ (J *ᵥ y) =
      star x ⬝ᵥ (J *ᵥ (P y - star (w : E) • P (Q y))) := fun x y => by
    rw [hT, star_sub, star_smul, sub_dotProduct, smul_dotProduct, hPQ, hQP, hQP, mulVec_sub,
      dotProduct_sub, mulVec_smul, dotProduct_smul]
  refine ⟨LinearMap.range T, ?_, ?_, ?_, fun z hz => ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [hTl, hQT, hT, map_sub, map_smul, hPP, sub_sub, ← add_smul, hw, one_smul, sub_self, mulVec_zero,
      dotProduct_zero]
  · have h1 : LinearMap.IsProj W P := ⟨hPW, hPid⟩
    have h2 : LinearMap.IsProj (LinearMap.range T) T :=
      ⟨fun x => ⟨x, rfl⟩, by rintro _ ⟨x, rfl⟩; exact hTT x⟩
    have h3 : Q ∘ₗ P = 0 := LinearMap.ext hQPz
    have h4 : LinearMap.trace E _ T = LinearMap.trace E _ Q := by
      simp only [T]
      rw [map_sub, map_smul, LinearMap.trace_comp_comm', h3, map_zero, smul_zero, sub_zero]
    rw [h2.trace, htr, h1.trace, star_natCast] at h4
    exact_mod_cast h4
  · rintro _ ⟨y, rfl⟩ hy
    have h0 : Q y = 0 := hQ0 y fun x hx => by rw [← hWT x hx]; exact hy x hx
    rw [hT, h0, map_zero, smul_zero, sub_zero]
  · have hTz : T z ∈ Λ := Λ.sub_mem (hQΛ z hz) (Λ.smul_mem w (hPΛ _ (hQΛ z hz)))
    have hu : z - T z ∈ Λ := Λ.sub_mem hz hTz
    have hxW : P (z - T z) ∈ W := hPW _
    have hQu : Q (z - T z) = 0 := by rw [map_sub, hQT, sub_self]
    refine ⟨P (z - T z), hPΛ _ hu, T z, hTz, hxW, ⟨z, rfl⟩, fun t ht => ?_⟩
    obtain ⟨a, ha, _, ⟨b, rfl⟩, rfl⟩ := Submodule.mem_sup.1 ht
    rw [star_add, add_dotProduct, hTl, sub_right_comm, map_sub P (z - T z), map_sub Q (z - T z), hQu, hQPz, hPP, sub_self,
      sub_self, map_zero, smul_zero, sub_self, mulVec_zero, dotProduct_zero, add_zero, mulVec_sub,
      mulVec_sub, dotProduct_sub, dotProduct_sub, hWT a ha, hW a ha _ hxW, sub_self, sub_self]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Jᴴ = J → J.det ≠ 0 → ∀ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Λ → (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) → ∀ W : Submodule E (Fin n → E), (∀ x ∈ W, ∀ y ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → ∃ W' : Submodule E (Fin n → E), (∀ x ∈ W', ∀ y ∈ W', star x ⬝ᵥ (J *ᵥ y) = 0) ∧ Module.finrank E W' = Module.finrank E W ∧ (∀ y ∈ W', (∀ x ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → y = 0) ∧ ∀ z ∈ Λ, ∃ x ∈ Λ, ∃ y ∈ Λ, x ∈ W ∧ y ∈ W' ∧ ∀ t ∈ W ⊔ W', star t ⬝ᵥ (J *ᵥ (z - x - y)) = 0 := by
  intro E _ _ _ hE n J hJ hd Λ hΛ hs W hW
  obtain ⟨w, hw⟩ := GlobalTheory.TraceOnto.exists_trace_one E hE
  exact split_of_trace E w hw n J hJ hd Λ hΛ hs W hW

end GlobalTheory.WittInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsShuffle
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.ParCoset

open GlobalTheory.FinGL Formalism.L2.DIV Finset

variable {g : ℕ} [Fact g.Prime] {n : ℕ}

theorem inPar_iff (a : ℕ) (M : Mt g n) :
    InPar a M ↔ M.BlockTriangular (fun i : Fin n => if (i : ℕ) < a then 0 else 1) := by
  constructor
  · intro h i j hij
    apply h <;> (dsimp only at hij; split_ifs at hij <;> omega)
  · intro h i j hj hi
    apply h
    dsimp only
    rw [if_pos hj, if_neg (by omega)]
    exact Nat.zero_lt_one

theorem inPar_mul {a : ℕ} {x y : Gn g n} (hx : InPar a (x : Mt g n)) (hy : InPar a (y : Mt g n)) :
    InPar a ((x * y : Gn g n) : Mt g n) := by
  rw [inPar_iff] at *
  exact hx.mul hy

theorem inPar_inv {a : ℕ} {x : Gn g n} (hx : InPar a (x : Mt g n)) : InPar a ((x⁻¹ : Gn g n) : Mt g n) := by
  rw [inPar_iff] at *
  rw [Matrix.coe_units_inv]
  haveI := x.invertible
  exact Matrix.blockTriangular_inv_of_blockTriangular hx

def pMat (g : ℕ) [Fact g.Prime] (σ : Equiv.Perm (Fin n)) : Mt g n := fun r j => if r = σ j then 1 else 0

theorem pMat_mul (σ τ : Equiv.Perm (Fin n)) : pMat g σ * pMat g τ = pMat g (σ * τ) := by
  ext r j
  simp [pMat, Matrix.mul_apply]
  congr

theorem pMat_one : pMat g (1 : Equiv.Perm (Fin n)) = 1 := by
  ext r j
  simp [pMat, Matrix.one_apply]
  congr

def pU (g : ℕ) [Fact g.Prime] (σ : Equiv.Perm (Fin n)) : Gn g n :=
  ⟨pMat g σ, pMat g σ⁻¹, by rw [pMat_mul, mul_inv_cancel, pMat_one], by rw [pMat_mul, inv_mul_cancel, pMat_one]⟩

theorem pU_mul (σ τ : Equiv.Perm (Fin n)) : pU g (σ * τ) = pU g σ * pU g τ :=
  Units.ext (pMat_mul σ τ).symm

theorem inPar_pU {a : ℕ} {τ : Equiv.Perm (Fin n)} (h : ∀ j, (τ j : ℕ) < a ↔ (j : ℕ) < a) :
    InPar a ((pU g τ : Gn g n) : Mt g n) := by
  intro i j hj hi
  have : i ≠ τ j := by
    rintro rfl
    have := (h j).2 hj
    omega
  exact if_neg this

noncomputable def rk (a c : ℕ) (M : Mt g n) : ℕ :=
  (Matrix.diagonal (fun i : Fin n => if c ≤ (i : ℕ) then (1 : ZMod g) else 0) * M *
    Matrix.diagonal (fun j : Fin n => if (j : ℕ) < a then (1 : ZMod g) else 0)).rank

theorem rk_le {a c : ℕ} {p q : Mt g n} (hp : InPar c p) (hq : InPar a q) (M : Mt g n) :
    rk a c (p * M * q) ≤ rk a c M := by
  unfold rk
  set F : Mt g n := Matrix.diagonal (fun i : Fin n => if c ≤ (i : ℕ) then (1 : ZMod g) else 0) with hF
  set E : Mt g n := Matrix.diagonal (fun j : Fin n => if (j : ℕ) < a then (1 : ZMod g) else 0) with hE
  have h1 : F * p = F * p * F := by
    ext i j
    simp only [hF, Matrix.mul_diagonal, Matrix.diagonal_mul]
    split_ifs with h h'
    · simp
    · rw [hp i j (by omega) h]; simp
    · simp
    · simp
  have h2 : q * E = E * (q * E) := by
    ext i j
    simp only [hE, Matrix.mul_diagonal, Matrix.diagonal_mul]
    split_ifs with h h'
    · simp
    · rw [hq i j h (by omega)]; simp
    · simp
    · simp
  have h3 : F * (p * M * q) * E = (F * p) * ((F * M * E) * (q * E)) := by
    calc F * (p * M * q) * E = (F * p) * M * (q * E) := by simp only [Matrix.mul_assoc]
      _ = (F * p * F) * M * (E * (q * E)) := by rw [← h1, ← h2]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [h3]
  exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_mul_le_left _ _)

theorem rk_eq {a c : ℕ} {p q : Gn g n} (hp : InPar c (p : Mt g n)) (hq : InPar a (q : Mt g n)) (x : Gn g n) :
    rk a c ((p * x * q : Gn g n) : Mt g n) = rk a c (x : Mt g n) := by
  refine le_antisymm (rk_le hp hq _) ?_
  have h := rk_le (inPar_inv hp) (inPar_inv hq) ((p * x * q : Gn g n) : Mt g n)
  rw [← Units.val_mul, ← Units.val_mul] at h
  have e : p⁻¹ * (p * x * q) * q⁻¹ = x := by group
  rwa [e] at h

theorem rk_pU (a c : ℕ) (σ : Equiv.Perm (Fin n)) :
    rk a c ((pU g σ : Gn g n) : Mt g n) = #{j : Fin n | (j : ℕ) < a ∧ ¬ (σ j : ℕ) < c} := by
  unfold rk
  have h : Matrix.diagonal (fun i : Fin n => if c ≤ (i : ℕ) then (1 : ZMod g) else 0) *
      ((pU g σ : Gn g n) : Mt g n) *
      Matrix.diagonal (fun j : Fin n => if (j : ℕ) < a then (1 : ZMod g) else 0) =
      ((pU g σ : Gn g n) : Mt g n) *
      Matrix.diagonal (fun j : Fin n => if (j : ℕ) < a ∧ ¬ (σ j : ℕ) < c then (1 : ZMod g) else 0) := by
    ext r j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, pU, pMat]
    by_cases hr : r = σ j
    · subst hr
      by_cases h1 : (j : ℕ) < a <;> by_cases h2 : c ≤ (σ j : ℕ) <;> simp [h1, h2]
    · simp [hr]
  rw [h, Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnits_det_units _), Matrix.rank_diagonal,
    Fintype.card_subtype]
  congr 1
  ext j
  simp

theorem card_lt {a : ℕ} (ha : a ≤ n) (σ : Equiv.Perm (Fin n)) : #{j : Fin n | (σ j : ℕ) < a} = a := by
  have h : #{j : Fin n | (σ j : ℕ) < a} = #{j : Fin n | (j : ℕ) < a} :=
    Finset.card_equiv σ (by simp)
  rw [h, Fin.card_filter_val_lt]
  omega

theorem card_lt' {a : ℕ} (ha : a ≤ n) : #{j : Fin n | (j : ℕ) < a} = a := by
  rw [Fin.card_filter_val_lt]
  omega

theorem card_split (P Q : Fin n → Prop) [DecidablePred P] [DecidablePred Q] :
    #{j : Fin n | P j ∧ Q j} + #{j : Fin n | P j ∧ ¬ Q j} = #{j : Fin n | P j} := by
  rw [← Finset.filter_filter, ← Finset.filter_filter, Finset.card_filter_add_card_filter_not]

theorem card_split' (P Q : Fin n → Prop) [DecidablePred P] [DecidablePred Q] :
    #{j : Fin n | P j ∧ Q j} + #{j : Fin n | ¬ P j ∧ Q j} = #{j : Fin n | Q j} := by
  rw [← card_split Q P]
  simp only [and_comm]

theorem card_not (P : Fin n → Prop) [DecidablePred P] :
    #{j : Fin n | P j} + #{j : Fin n | ¬ P j} = n := by
  rw [Finset.card_filter_add_card_filter_not]
  simp

theorem exists_young {a c : ℕ} (ha : a ≤ n) (hc : c ≤ n) (σ s : Equiv.Perm (Fin n))
    (h : #{j : Fin n | (j : ℕ) < a ∧ ¬ (σ j : ℕ) < c} = #{j : Fin n | (j : ℕ) < a ∧ ¬ (s j : ℕ) < c}) :
    ∃ t₁ t₂ : Equiv.Perm (Fin n), (∀ j, (t₁ j : ℕ) < c ↔ (j : ℕ) < c) ∧ (∀ j, (t₂ j : ℕ) < a ↔ (j : ℕ) < a) ∧
      σ = t₁ * s * t₂ := by
  let f : Equiv.Perm (Fin n) → Fin n → Bool × Bool := fun τ j => (decide ((j : ℕ) < a), decide ((τ j : ℕ) < c))
  have hcard : ∀ y, Fintype.card {j // f σ j = y} = Fintype.card {j // f s j = y} := by
    have e1 := card_split (fun j : Fin n => (j : ℕ) < a) (fun j => (σ j : ℕ) < c)
    have e2 := card_split (fun j : Fin n => (j : ℕ) < a) (fun j => (s j : ℕ) < c)
    have e3 := card_split' (fun j : Fin n => (j : ℕ) < a) (fun j => (σ j : ℕ) < c)
    have e4 := card_split' (fun j : Fin n => (j : ℕ) < a) (fun j => (s j : ℕ) < c)
    have e5 := card_split (fun j : Fin n => ¬ (j : ℕ) < a) (fun j => (σ j : ℕ) < c)
    have e6 := card_split (fun j : Fin n => ¬ (j : ℕ) < a) (fun j => (s j : ℕ) < c)
    rw [card_lt hc] at e3 e4
    rintro ⟨y₁, y₂⟩
    rw [Fintype.card_subtype, Fintype.card_subtype]
    cases y₁ <;> cases y₂ <;>
      simp only [f, Prod.mk.injEq, decide_eq_true_eq, decide_eq_false_iff_not] <;> omega
  let t₂ : Equiv.Perm (Fin n) := Equiv.ofFiberEquiv fun y => Fintype.equivOfCardEq (hcard y)
  have ht : ∀ j, f s (t₂ j) = f σ j := fun j => Equiv.ofFiberEquiv_map _ j
  refine ⟨σ * t₂⁻¹ * s⁻¹, t₂, fun j => ?_, fun j => ?_, by group⟩
  · have := congrArg Prod.snd (ht (t₂⁻¹ (s⁻¹ j)))
    simpa [f] using this.symm
  · have := congrArg Prod.fst (ht j)
    simpa [f] using this

theorem exists_shuffle {a b c i : ℕ} (hn : n = a + b) (hia : i ≤ a) (hic : i ≤ c) (hb : c - i ≤ b) :
    ∃ s : Equiv.Perm (Fin n), wI g a c i n = pU g s ∧
      #{j : Fin n | (j : ℕ) < a ∧ ¬ (s j : ℕ) < c} = a - i := by
  let f : Fin n → Fin n := fun j => ⟨sigI a c i j, by
    have := j.2
    unfold sigI
    split_ifs <;> omega⟩
  have hf : Function.Injective f := by
    intro j k h
    have h' : sigI a c i j = sigI a c i k := congrArg Fin.val h
    apply Fin.ext
    unfold sigI at h'
    split_ifs at h' <;> omega
  let s : Equiv.Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
  have hs : ∀ j, (s j : ℕ) = sigI a c i j := fun _ => rfl
  refine ⟨s, ?_, ?_⟩
  · have e : (fun r j : Fin n => if (r : ℕ) = sigI a c i j then (1 : ZMod g) else 0) =
        ((pU g s : Gn g n) : Mt g n) := by
      funext r j
      simp only [pU, pMat, ← hs, Fin.val_inj]
    unfold wI toG
    rw [e, dif_pos (Units.isUnit _), IsUnit.unit_of_val_units]
  · have e1 := card_split (fun j : Fin n => (j : ℕ) < a) (fun j => (s j : ℕ) < c)
    have e2 : #{j : Fin n | (j : ℕ) < a ∧ (s j : ℕ) < c} = #{j : Fin n | (j : ℕ) < i} := by
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs, sigI]
      split_ifs <;> omega
    have e3 := card_lt' (a := a) (n := n) (by omega)
    have e4 := card_lt' (a := i) (n := n) (by omega)
    omega

theorem exists_perm (a c : ℕ) (x : Gn g n) : ∃ σ : Equiv.Perm (Fin n), ∃ p q : Gn g n,
    InPar c (p : Mt g n) ∧ InPar a (q : Mt g n) ∧ x = p * pU g σ * q := by
  obtain ⟨m, u, hu, u', hu', h⟩ := Bruhat.exists_decomp x
  have hup : ∀ (e : ℕ) (v : Gn g n), v ∈ unip (ZMod g) n → InPar e (v : Mt g n) := fun e v hv i j hj hi =>
    unip_lower hv (show j < i from Fin.lt_def.2 (by omega))
  let D : Gn g n := ⟨Matrix.diagonal fun j => (m.2 j : ZMod g), Matrix.diagonal fun j => ((m.2 j)⁻¹ : (ZMod g)ˣ),
    by simp only [Matrix.diagonal_mul_diagonal, Units.mul_inv, Matrix.diagonal_one],
    by simp only [Matrix.diagonal_mul_diagonal, Units.inv_mul, Matrix.diagonal_one]⟩
  have hD : InPar a (D : Mt g n) := fun i j hj hi =>
    Matrix.diagonal_apply_ne _ (by rintro rfl; omega)
  refine ⟨m.1, u, D * u', hup c u hu, inPar_mul hD (hup a u' hu'), Units.ext ?_⟩
  have e : Bruhat.mono m = ((pU g m.1 : Gn g n) : Mt g n) * (D : Mt g n) := by
    ext r j
    simp [Bruhat.mono, pU, pMat, D, Matrix.mul_diagonal]
  rw [h, e]
  simp only [Units.val_mul, Matrix.mul_assoc]

theorem doubleCoset : ∀ (g : ℕ) [Fact g.Prime] (a b c d n : ℕ), n = a + b → n = c + d → ∀ x : Gn g n, ∃! i : ℕ, i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b) ∧ ∃ p q : Gn g n, InPar c (p : Mt g n) ∧ InPar a (q : Mt g n) ∧ x = p * wI g a c i n * q := by
  intro g _ a b c d n hab hcd x
  have key : ∀ i : ℕ, (i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b) ∧ ∃ p q : Gn g n,
      InPar c (p : Mt g n) ∧ InPar a (q : Mt g n) ∧ x = p * wI g a c i n * q) →
      i = a - rk a c (x : Mt g n) := by
    rintro i ⟨hi, p, q, hp, hq, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨s, hs, hc⟩ := exists_shuffle (g := g) hab (by omega : i ≤ a) hi.2.1 hi.2.2
    rw [rk_eq hp hq, hs, rk_pU, hc]
    omega
  refine existsUnique_of_exists_of_unique ?_ fun i j hi hj => (key i hi).trans (key j hj).symm
  obtain ⟨σ, p, q, hp, hq, rfl⟩ := exists_perm a c x
  have e1 := card_split (fun j : Fin n => (j : ℕ) < a) (fun j => (σ j : ℕ) < c)
  have e3 := card_split' (fun j : Fin n => (j : ℕ) < a) (fun j => (σ j : ℕ) < c)
  have e5 := card_split (fun j : Fin n => ¬ (j : ℕ) < a) (fun j => (σ j : ℕ) < c)
  have e6 := card_not (fun j : Fin n => (j : ℕ) < a)
  have e7 := card_lt' (a := a) (n := n) (by omega)
  rw [card_lt (by omega)] at e3
  obtain ⟨i, hi⟩ : ∃ i, i = #{j : Fin n | (j : ℕ) < a ∧ (σ j : ℕ) < c} := ⟨_, rfl⟩
  obtain ⟨s, hs, hc⟩ := exists_shuffle (g := g) (i := i) (c := c) hab (by omega) (by omega) (by omega)
  obtain ⟨t₁, t₂, h₁, h₂, ht⟩ := exists_young (a := a) (c := c) (by omega) (by omega) σ s (by omega)
  refine ⟨i, ?_, p * pU g t₁, pU g t₂ * q, inPar_mul hp (inPar_pU h₁), inPar_mul (inPar_pU h₂) hq, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · rw [hs, ht, pU_mul, pU_mul]
    group

end GlobalTheory.GLm.ParCoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTotalMassLeGenericMassStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_total_mass_le_generic_mass : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (R : LocNG.Reps P) (d0 d₁ : LocNG.Datum P) (t₁ : Term V M r), LocNG.IsTermOver P d₁ t₁ → ∀ Cl : Term V M r → Prop, (∀ t, Cl t ↔ ∃ s ∈ P.St, ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ i j, A i j ∈ M.L.O ∧ A' i j ∈ M.L.O ∧ ∃ c ∈ M.L.O, A' i j - A i j = algebraMap F E (LocNG.theta M) * c) ∧ (∀ i j, j < i → A i j = 0 ∧ A' i j = 0) ∧ (∀ i, A i i = 1 ∧ A' i i = 1) ∧ (∀ j, t.f j = ∑ i, A i j • s (t₁.f i)) ∧ ∀ j, t.f' j = ∑ i, A' i j • s (t₁.f' i)) → ∀ g : ℝ≥0∞, g = ∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * ∑' t : {t // t ∈ R.RT d.1 ∧ ¬ LocNG.BBne (H := H) t ∧ Cl t}, ENNReal.ofReal (LocNG.mu P t.1) → g ≠ ⊤ ∧ LocNG.nn R d0 ≤ ENNReal.ofReal (8 * P.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2))) * g ∧ (P.PrimeTo → LocNG.nn R d0 = g) ∧ ((∃ t', LocNG.IsTermOver P d0 t') → g ≠ 0) := by
  first | exact @GlobalTheory.HL.AbsGenMass.total_le_generic | exact GlobalTheory.HL.AbsGenMass.total_le_generic | (intros; apply GlobalTheory.HL.AbsGenMass.total_le_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HolomorphicExtensionCompactRepStatement
section
open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_extension_compact_rep : ∀ (n : ℕ) (ε : Fin n → Bool) (B : Type) [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] (π : Matrix (Fin n) (Fin n) ℂ → B), π 1 = 1 → (∀ a ∈ Formalism.REAL.Kset ε, ∀ b ∈ Formalism.REAL.Kset ε, π (a * b) = π a * π b) → ContinuousOn π (Formalism.REAL.Kset ε) → ∃ τ : Matrix (Fin n) (Fin n) ℂ → B, DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y)) {y | IsUnit (Matrix.of y)} ∧ ∀ k ∈ Formalism.REAL.Kset ε, τ k = π k := by
  first | exact @GlobalTheory.HolExt.exists_holomorphic_extension | exact GlobalTheory.HolExt.exists_holomorphic_extension | (intros; apply GlobalTheory.HolExt.exists_holomorphic_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InitialLengthsProductMomentLeStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.initial_lengths_product_moment_le : ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r l : ℕ) (hl : l ≤ r + 1) (len : Fin (r + 1) → Ω → ℝ) (Ph : Ω → ℝ) (A Rr : ℝ), (∀ a, AEMeasurable (len a) ν) → (∀ a, ∀ᵐ x ∂ν, 0 < len a x) → AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) → ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν = 1 → 0 ≤ A → 1 ≤ Rr → (∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal (len 0 x ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (A ^ q)) → (∀ a : Fin r, ∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal ((len a.succ x / len a.castSucc x) ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * q))) → ∫⁻ x, ENNReal.ofReal ((∏ a : Fin l, len (Fin.castLE hl a) x ^ 2) * Ph x) ∂ν ≤ ENNReal.ofReal ((A * Rr ^ (2 * r)) ^ l) := by
  first | exact @GlobalTheory.MomentHolder.initial_product_moment_le | exact GlobalTheory.MomentHolder.initial_product_moment_le | (intros; apply GlobalTheory.MomentHolder.initial_product_moment_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableAndNormAmplitudeLeOfPairingsStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_and_norm_amplitude_le_of_pairings : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (ν : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (γ : Mat k r) (c K : ℝ), γ ∈ GG k r → ν {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → 0 < c → 0 ≤ K → (∀ (v : Wp) (w : Wq), ‖v‖ = 1 → ‖w‖ = 1 → ∫⁻ x, ENNReal.ofReal (‖⟪v, Φ (γ * Matrix.of x)⟫_ℂ‖ * ‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖) ∂ν ≤ ENNReal.ofReal K) → Integrable (fun x => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) ν ∧ ‖(haveI := FiniteDimensional.complete ℂ Wp; ampJ ν c Φ Φ' γ)‖ ≤ K / c := by
  first | exact @GlobalTheory.Amp.OpNorm.integrable_and_norm_ampJ_le | exact GlobalTheory.Amp.OpNorm.integrable_and_norm_ampJ_le | (intros; apply GlobalTheory.Amp.OpNorm.integrable_and_norm_ampJ_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHaarOnBesselSubgroupProdMap
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.ProdHaarS

theorem isHaarOn_prod_map : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Mt k r)),
    inWb k r z → 0 < Tz k r z → IsHaarOn (UWset k r z) μW → IsHaarOn (Nset k r) μN →
    IsHaarOn (Sset k r z) ((μW.prod μN).map fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2) := by
  intro k r z μW μN hz hT hW hN
  obtain ⟨-, -, h, -⟩ := GlobalTheory.muSof_isHaar k r z μW μN hz hT hW hN
  exact h

end GlobalTheory.SgInf.ProdHaarS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRiemannianHaarOnSubgroupMapMulRightUnitaryStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRiemannianHaarOnSubgroup_map_mul_right_unitary : ∀ (n : ℕ) (ε : Fin n → Bool) (M : Subgroup (Formalism.REAL.UJ ε)) (d : ℕ) (μ : Measure (Formalism.REAL.UJ ε)), IsClosed (M : Set (Formalism.REAL.UJ ε)) → IsGaugeSub (M : Set (Formalism.REAL.UJ ε)) d μ → ∀ l ∈ M, l ∈ maxK ε → μ.map (fun g => g * l) = μ := by
  first | exact @GlobalTheory.GaugeRightInv.isGaugeSub_map_mul_right | exact GlobalTheory.GaugeRightInv.isGaugeSub_map_mul_right | (intros; apply GlobalTheory.GaugeRightInv.isGaugeSub_map_mul_right <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroupsStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlagLevi_maxCompact_closed_subgroups : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∃ M : Subgroup (Formalism.REAL.UJ ε), (M : Set (Formalism.REAL.UJ ε)) = flagM ε W) ∧ IsClosed (flagM ε W) ∧ (∃ K : Subgroup (Formalism.REAL.UJ ε), (K : Set (Formalism.REAL.UJ ε)) = maxK ε) ∧ IsClosed (maxK ε) ∧ ∀ m ∈ flagM ε W, ∀ u ∈ flagN ε W, m * u * m⁻¹ ∈ flagN ε W := by
  first | exact @GlobalTheory.FlagLeviGroup.levi_compact_subgroups | exact GlobalTheory.FlagLeviGroup.levi_compact_subgroups | (intros; apply GlobalTheory.FlagLeviGroup.levi_compact_subgroups <;> assumption)
end

