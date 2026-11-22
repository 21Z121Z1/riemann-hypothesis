import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0107
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0059
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0106
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0108
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisHankelDetNeZeroOfLiftStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallisHankelDet_ne_zero_of_lift : ∀ (k : Type) [Field k] (r : ℕ) (Z : Gl r k) (μ l : k), Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → Delta (inv Z) ≠ 0 := by
  first | exact @GlobalTheory.JR.Step.delta_lift_ne | exact GlobalTheory.JR.Step.delta_lift_ne | (intros; apply GlobalTheory.JR.Step.delta_lift_ne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisInvKRegularIffIsUnit
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.EtInv

section Gen
variable {F K : Type} [Field F] [CommRing K] [Algebra F K] [Module.Finite F K]

theorem eq_zero_of_trace_mul [CharZero F] [IsReduced K] (a : K)
    (h : ∀ x : K, Algebra.trace F K (x * a) = 0) : a = 0 := by
  classical
  let b := Module.finBasis F K
  have hn : IsNilpotent (Algebra.leftMulMatrix b a) := by
    apply ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow
    intro k hk _
    rw [← map_pow, ← Algebra.trace_eq_matrix_trace]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ]
    exact h _
  obtain ⟨m, hm⟩ := hn
  rw [← map_pow, ← map_zero (Algebra.leftMulMatrix b)] at hm
  exact (IsNilpotent.eq_zero ⟨m, Algebra.leftMulMatrix_injective b hm⟩)

variable {r : ℕ} {τ : K}

theorem trace_mul_eq_sum (bb : Module.Basis (Fin r) F K) (hb : ∀ i, bb i = τ ^ (i : ℕ)) (x a : K) :
    Algebra.trace F K (x * a) = ∑ j, bb.repr x j * Algebra.trace F K (τ ^ (j : ℕ) * a) := by
  conv_lhs => rw [← bb.sum_repr x]
  simp [Finset.sum_mul, smul_mul_assoc, map_sum, hb]

end Gen

section Comp
variable {F K : Type} [Field F] [CommRing K] [Algebra F K] {r : ℕ} {τ : K} {p : Fin r → F}

theorem leftMulMatrix_eq_companion (bb : Module.Basis (Fin r) F K) (hb : ∀ i, bb i = τ ^ (i : ℕ))
    (hr : τ ^ r + ∑ i, p i • τ ^ (i : ℕ) = 0) : Algebra.leftMulMatrix bb τ = companion p := by
  classical
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, hb, ← pow_succ']
  simp only [companion, Matrix.of_apply]
  by_cases hj : (j : ℕ) + 1 = r
  · rw [if_pos hj, hj, eq_neg_of_add_eq_zero_left hr]
    have : ∑ k, p k • τ ^ (k : ℕ) = ∑ k, p k • bb k := by simp [hb]
    rw [this, map_neg, Finsupp.neg_apply, bb.repr_sum_self]
  · rw [if_neg hj]
    have hlt : (j : ℕ) + 1 < r := by omega
    have : τ ^ ((j : ℕ) + 1) = bb ⟨(j : ℕ) + 1, hlt⟩ := by rw [hb]
    rw [this, bb.repr_self, Finsupp.single_apply]
    by_cases hi : (i : ℕ) = (j : ℕ) + 1
    · rw [if_pos (Fin.ext hi.symm), if_pos hi]
    · rw [if_neg (fun h => hi (by rw [← h])), if_neg hi]

theorem companion_pow_mulVec (bb : Module.Basis (Fin r) F K) (hb : ∀ i, bb i = τ ^ (i : ℕ))
    (hr : τ ^ r + ∑ i, p i • τ ^ (i : ℕ) = 0) (n : ℕ) :
    (companion p ^ n) *ᵥ (fun i : Fin r => if (i : ℕ) = 0 then (1 : F) else 0) = ⇑(bb.repr (τ ^ n)) := by
  classical
  induction n with
  | zero =>
    rw [pow_zero, Matrix.one_mulVec, pow_zero]
    funext i
    have hr0 : 0 < r := lt_of_le_of_lt (Nat.zero_le _) i.2
    have h1 : (1 : K) = bb ⟨0, hr0⟩ := by rw [hb]; simp
    rw [h1, bb.repr_self, Finsupp.single_apply]
    by_cases hi : (i : ℕ) = 0
    · rw [if_pos hi, if_pos (Fin.ext hi.symm)]
    · rw [if_neg hi, if_neg (fun h => hi (by rw [← h]))]
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, ← leftMulMatrix_eq_companion bb hb hr,
      Algebra.leftMulMatrix_apply, LinearMap.toMatrix_mulVec_repr, pow_succ']
    rfl

end Comp

theorem invK_regular_iff_isUnit :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p →
      Function.Bijective (fun (a : A.K) (i : Fin r) => Algebra.trace F A.K (τ ^ (i : ℕ) * a)) ∧
      ∀ a : A.K, (∀ i : ℕ, mom (sec (A.invK τ p lam a)) i = Algebra.trace F A.K (τ ^ i * a)) ∧
        (Delta (A.invK τ p lam a) ≠ 0 ↔ IsUnit a) := by
  intro F E _ _ _ _ hU A r τ p lam hg
  classical
  haveI : CharZero F := hU.charZero
  obtain ⟨hli, hfr, hr⟩ := hg
  let bb : Module.Basis (Fin r) F A.K :=
    basisOfLinearIndependentOfCardEqFinrank' _ hli (by rw [hfr, Fintype.card_fin])
  have hb : ∀ i, bb i = τ ^ (i : ℕ) := fun i => by
    simp [bb]
  let Ψ : A.K →ₗ[F] (Fin r → F) :=
    { toFun := fun a i => Algebra.trace F A.K (τ ^ (i : ℕ) * a)
      map_add' := fun a a' => by funext i; simp [mul_add]
      map_smul' := fun c a => by funext i; simp [mul_smul_comm] }
  have hΨ : ∀ a, Ψ a = fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * a) := fun _ => rfl
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    apply eq_zero_of_trace_mul (F := F) a
    intro x
    rw [trace_mul_eq_sum bb hb x a]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := congrFun ha j
    simp only [hΨ, Pi.zero_apply] at this
    rw [this, mul_zero]
  have hbij : Function.Bijective Ψ := by
    refine ⟨hinj, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hfr])).1 hinj
  have hmom : ∀ a : A.K, ∀ i : ℕ, mom (sec (A.invK τ p lam a)) i = Algebra.trace F A.K (τ ^ i * a) := by
    intro a i
    simp only [mom, sec, Et.invK]
    rw [companion_pow_mulVec bb hb hr i, trace_mul_eq_sum bb hb (τ ^ i) a, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine ⟨hbij, fun a => ⟨hmom a, ?_⟩⟩

  have hH : ∀ v : Fin r → F, hankel (A.invK τ p lam a) *ᵥ v = Ψ (a * bb.equivFun.symm v) := by
    intro v
    funext i
    simp only [hankel, Matrix.mulVec, dotProduct, Matrix.of_apply, hmom, hΨ,
      Module.Basis.equivFun_symm_apply, hb, Finset.mul_sum, map_sum, mul_smul_comm, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]; ring_nf
  have hcomp : Function.Injective (hankel (A.invK τ p lam a)).mulVec ↔ Function.Injective (fun y : A.K => a * y) := by
    constructor
    · intro h y y' hyy
      have := h (a₁ := bb.equivFun y) (a₂ := bb.equivFun y') (by rw [hH, hH]; simp [hyy])
      exact bb.equivFun.injective this
    · intro h v v' hvv
      rw [hH, hH] at hvv
      exact bb.equivFun.symm.injective (h (hinj hvv))
  rw [Delta, ← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit, hcomp]
  constructor
  · intro h
    have hs : Function.Surjective (Algebra.lmul F A.K a) :=
      LinearMap.injective_iff_surjective.1 h
    obtain ⟨y, hy⟩ := hs 1
    exact ⟨⟨a, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩
  · intro h
    exact h.mul_right_injective

end GlobalTheory.JR.EtInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorGlBorderedConjugationStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallisTransferFactor_glBorderedConjugationAction_integral : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] (n : ℕ) (k : GL (Fin n) F), k ∈ glO n F → ∀ Y : Gl n F, omega (act k Y) = omega Y := by
  first | exact @GlobalTheory.JR.omega_act_glO | exact GlobalTheory.JR.omega_act_glO | (intros; apply GlobalTheory.JR.omega_act_glO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KrasnerLemmaDecompositionGroupStabilizerVersion
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory

theorem krasner_val_lt_apply_iff {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) (a b : Ω) :
    A.valuation (σ a) < A.valuation (σ b) ↔ A.valuation a < A.valuation b := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  · have hb' : A.valuation b ≠ 0 := by simpa using hb
    have hsb : σ b ≠ 0 := (map_ne_zero_iff _ σ.injective).mpr hb
    have hsb' : A.valuation (σ b) ≠ 0 := by simpa using hsb
    rw [← div_lt_one₀ (zero_lt_iff.mpr hb'), ← div_lt_one₀ (zero_lt_iff.mpr hsb'),
      ← map_div₀, ← map_div₀, ← map_div₀, valuation_apply_lt_one_iff hσ]

theorem krasner_stabiliser (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (β β' : Ω)
    (h : ∀ d ∈ Dec (F := E) A, d β ≠ β → A.valuation (β' - β) < A.valuation (d β - β)) :
    ∀ σ ∈ Dec (F := E) A, σ β' = β' → σ β = β := by
  intro σ hσ hfix
  by_contra hne
  have hσi : σ⁻¹ ∈ Dec (F := E) A := (Dec (F := E) A).inv_mem hσ
  have hne' : (σ⁻¹ : G E Ω) β ≠ β := by
    intro he
    apply hne
    conv_lhs => rw [← he]
    exact mul_inv_apply β
  have h1 := h σ hσ hne
  have h2 := h σ⁻¹ hσi hne'
  rw [← krasner_val_lt_apply_iff hσ, map_sub σ, map_sub σ, mul_inv_apply, hfix] at h2
  have e : β - σ β = (β - β') + (β' - σ β) := by ring
  have h3 : A.valuation (β - σ β) = A.valuation (σ β - β) := Valuation.map_sub_swap _ _ _
  have h4 : A.valuation (β - β') = A.valuation (β' - β) := Valuation.map_sub_swap _ _ _
  have key : A.valuation (β - σ β) < A.valuation (β - σ β) := by
    conv_lhs => rw [e]
    refine Valuation.map_add_lt _ ?_ h2
    rw [h4, h3]; exact h1
  exact lt_irrefl _ key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCountAndGramDetSignNormClass
section
noncomputable section

namespace GlobalTheory.UnitLemma.NormClass

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial

section Orb

variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A]

def mulLatEquiv (u : Aˣ) : Submodule O A ≃ Submodule O A where
  toFun := mulLat O (u : A)
  invFun := mulLat O ((u⁻¹ : Aˣ) : A)
  left_inv L := by
    ext y
    simp only [mem_mulLat, inv_inv, Units.inv_mul_cancel_left]
  right_inv L := by
    ext y
    simp only [mem_mulLat, inv_inv, Units.mul_inv_cancel_left]

end Orb

variable {K : UQ}

open Polynomial in
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A] in
private theorem isLat_mulLat_unit {E : Type} [Field E] [Algebra E A] (u : Aˣ) (L : Submodule O A)
    (hL : _root_.GlobalTheory.UnitLemma.IsLat O E L) : _root_.GlobalTheory.UnitLemma.IsLat O E (_root_.GlobalTheory.UnitLemma.mulLat O (u : A) L) := by
  unfold _root_.GlobalTheory.UnitLemma.IsLat at hL ⊢
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.UnitLemma.mulLat
    exact hL.1.map _
  · unfold _root_.GlobalTheory.UnitLemma.mulLat
    rw [Submodule.map_coe]
    have e : (⇑(LinearMap.mulLeft O (u : A))) = ⇑(LinearMap.mulLeft E (u : A)) := rfl
    rw [e, Submodule.span_image, hL.2, Submodule.map_top, LinearMap.range_eq_top]
    intro z
    exact ⟨((u⁻¹ : Aˣ) : A) * z, by simp⟩

open Polynomial in
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A] in
private theorem forall_mem_mulLat_unit_iff (u : Aˣ) (L : Submodule O A) (P : A → Prop) :
    (∀ z ∈ _root_.GlobalTheory.UnitLemma.mulLat O (u : A) L, P z) ↔ ∀ z ∈ L, P (u * z) := by
  constructor
  · intro h z hz
    exact h _ ((_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat u L _).mpr (by rwa [Units.inv_mul_cancel_left]))
  · intro h z hz
    have := h _ ((_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat u L z).mp hz)
    rwa [Units.mul_inv_cancel_left] at this

open Polynomial in
variable {K : _root_.GlobalTheory.UnitLemma.UQ} in
private theorem herm_mul_unit_sigma (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (u : B.Aˣ) (a b : B.A) :
    B.herm (x * (u * B.σ (u : B.A))) a b = B.herm x (u * a) (u * b) := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  simp only [map_mul]
  congr 1
  ring

open Polynomial in
variable {K : _root_.GlobalTheory.UnitLemma.UQ} in
private theorem mem_X_mul_unit_sigma_iff (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (u : B.Aˣ)
    (L : Submodule K.O B.A) :
    L ∈ B.X (x * (u * B.σ (u : B.A))) ↔ _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) L ∈ B.X x := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.X
  simp only [Set.mem_setOf_eq]
  refine and_congr ?_ (and_congr ?_ ?_)
  · refine ⟨isLat_mulLat_unit u L, fun h => ?_⟩
    have := isLat_mulLat_unit (u⁻¹) _ h
    have hL : _root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) (_root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) L) = L :=
      (_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).left_inv L
    rwa [hL] at this
  · rw [forall_mem_mulLat_unit_iff]
    constructor
    · intro h z hz
      rw [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, mul_left_comm, Units.inv_mul_cancel_left]
      exact h z hz
    · intro h z hz
      have := h z hz
      rwa [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, mul_left_comm, Units.inv_mul_cancel_left] at this
  · constructor
    · intro h w
      rw [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, h, forall_mem_mulLat_unit_iff]
      simp only [herm_mul_unit_sigma, Units.mul_inv_cancel_left]
    · intro h w
      have := h (u * w)
      rw [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, Units.inv_mul_cancel_left, forall_mem_mulLat_unit_iff] at this
      rw [this]
      simp only [herm_mul_unit_sigma]

open Polynomial in
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A] in
private theorem mulLat_unit_comm (u t : Aˣ) (L : Submodule O A) :
    _root_.GlobalTheory.UnitLemma.mulLat O (u : A) (_root_.GlobalTheory.UnitLemma.mulLat O (t : A) L) =
      _root_.GlobalTheory.UnitLemma.mulLat O (t : A) (_root_.GlobalTheory.UnitLemma.mulLat O (u : A) L) := by
  ext y
  simp only [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat]
  rw [mul_left_comm]

open Polynomial in
variable {K : _root_.GlobalTheory.UnitLemma.UQ} in

theorem _root_.GlobalTheory.UnitLemma.NormClass.N_norm_class : ∀ (K : _root_.GlobalTheory.UnitLemma.UQ) (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (u : B.Aˣ),
    B.N (x * (u * B.σ (u : B.A))) = B.N x ∧
      K.eta (B.gramDet (x * (u * B.σ (u : B.A)))) = K.eta (B.gramDet x) := by
  intro K B x u
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.UnitLemma.InvAlg.N _root_.GlobalTheory.UnitLemma.orbSum
    simp only [one_mul]
    let wt : Submodule K.O B.A → ℚ := fun L =>
      ((_root_.GlobalTheory.UnitLemma.stabLat K.O L ⊓ B.T).relIndex (_root_.GlobalTheory.UnitLemma.intUnits K.O B.A ⊓ B.T) : ℚ)
    have hwt : ∀ (t : B.Aˣ) (L : Submodule K.O B.A), wt (_root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L) = wt L := by
      intro t L
      simp only [wt, _root_.GlobalTheory.UnitLemma.Orbit.stabLat_mulLat]
    have hrel : ∀ (X : Set (Submodule K.O B.A)) (a b : X),
        (∃ t ∈ B.T, (b : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) a) → wt a = wt b := by
      rintro X a b ⟨t, -, h⟩
      rw [h, hwt]
    have hout : ∀ (X : Set (Submodule K.O B.A)) (o : Quot (fun L M : X => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L)),
        wt ((Quot.out o : X) : Submodule K.O B.A) = Quot.lift (fun a : X => wt a) (hrel X) o := by
      intro X o
      conv_rhs => rw [← Quot.out_eq o]
    show (∑ᶠ o : Quot (fun L M : B.X (x * (u * B.σ (u : B.A))) => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L), wt ((Quot.out o : B.X (x * (u * B.σ (u : B.A)))) : Submodule K.O B.A)) =
      ∑ᶠ o : Quot (fun L M : B.X x => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L), wt ((Quot.out o : B.X x) : Submodule K.O B.A)
    simp only [hout]
    have hφ : ∀ L : B.X (x * (u * B.σ (u : B.A))), _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) L ∈ B.X x :=
      fun L => (mem_X_mul_unit_sigma_iff B x u L).mp L.2
    have hψ : ∀ M : B.X x, _root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) M ∈ B.X (x * (u * B.σ (u : B.A))) := by
      intro M
      refine (mem_X_mul_unit_sigma_iff B x u _).mpr ?_
      have hM : _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) (_root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) M) = M :=
        (_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).right_inv (M : Submodule K.O B.A)
      rw [hM]
      exact M.2
    let e : Quot (fun L M : B.X (x * (u * B.σ (u : B.A))) => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L) ≃
        Quot (fun L M : B.X x => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L) :=
      { toFun := Quot.map (fun L => ⟨_, hφ L⟩) (by
          rintro a b ⟨t, ht, h⟩
          refine ⟨t, ht, ?_⟩
          show _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) b = _
          rw [h]
          exact mulLat_unit_comm u t (a : Submodule K.O B.A))
        invFun := Quot.map (fun M => ⟨_, hψ M⟩) (by
          rintro a b ⟨t, ht, h⟩
          refine ⟨t, ht, ?_⟩
          show _root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) b = _
          rw [h]
          exact mulLat_unit_comm u⁻¹ t (a : Submodule K.O B.A))
        left_inv := by
          intro o
          induction o using Quot.ind with
          | mk L => exact congrArg (Quot.mk _) (Subtype.ext ((_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).left_inv (L : Submodule K.O B.A)))
        right_inv := by
          intro o
          induction o using Quot.ind with
          | mk M => exact congrArg (Quot.mk _) (Subtype.ext ((_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).right_inv (M : Submodule K.O B.A))) }
    rw [← finsum_comp_equiv e]
    refine finsum_congr fun o => ?_
    induction o using Quot.ind with
    | mk L => exact (hwt u (L : Submodule K.O B.A)).symm
  · let φ : B.A ≃ₗ[K.E] B.A :=
      { LinearMap.mulLeft K.E (u : B.A) with
        invFun := fun z => ((u⁻¹ : B.Aˣ) : B.A) * z
        left_inv := fun z => Units.inv_mul_cancel_left u z
        right_inv := fun z => Units.mul_inv_cancel_left u z }
    have e : B.gramDet (x * (u * B.σ (u : B.A))) =
        (Matrix.of fun i j => B.herm x (((Module.finBasis K.E B.A).map φ) i)
          (((Module.finBasis K.E B.A).map φ) j)).det := by
      unfold _root_.GlobalTheory.UnitLemma.InvAlg.gramDet
      simp only [herm_mul_unit_sigma, Module.Basis.map_apply]
      rfl
    rw [e, _root_.GlobalTheory.UnitLemma.Orbit.eta_gram]

end GlobalTheory.UnitLemma.NormClass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieLatticeProdComapInlAndMapSndStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieLattice_prod_comap_inl_and_map_snd : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A)), M ∈ (B₁.prod B₂).Lin → M.comap (LinearMap.inl K.O B₁.A B₂.A) ∈ B₁.Lin ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) ∈ B₂.Lin := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.lin_fst_snd | exact GlobalTheory.UnitLemma.InvAlg.lin_fst_snd | (intros; apply GlobalTheory.UnitLemma.InvAlg.lin_fst_snd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentOfInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.Per

theorem linearIndependent_of_invariant (G E M ι : Type) [Field E] [AddCommGroup M] [Module E M]
    [Fintype ι] (σ : G → (E →+* E)) (ρ : G → (M →+ M))
    (hρ : ∀ g (e : E) (m : M), ρ g (e • m) = σ g e • ρ g m) (v : ι → M)
    (hv : ∀ g i, ρ g (v i) = v i)
    (hind : ∀ c : ι → E, (∀ g i, σ g (c i) = c i) → ∑ i, c i • v i = 0 → ∀ i, c i = 0) :
    LinearIndependent E v := by
  classical
  rw [Fintype.linearIndependent_iff]

  suffices H : ∀ n : ℕ, ∀ c : ι → E,
      (Finset.univ.filter (fun i => c i ≠ 0)).card ≤ n → ∑ i, c i • v i = 0 → ∀ i, c i = 0 by
    exact fun c hc => H _ c le_rfl hc
  intro n
  induction n with
  | zero =>
    intro c hcard _ i
    by_contra h
    have hpos : 0 < (Finset.univ.filter (fun i => c i ≠ 0)).card :=
      Finset.card_pos.mpr ⟨i, by simp [h]⟩
    omega
  | succ n ih =>
    intro c hcard hsum
    by_contra hne
    obtain ⟨i0, hi0⟩ := not_forall.mp hne

    obtain ⟨c', hc'⟩ : ∃ c' : ι → E, c' = fun i => (c i0)⁻¹ * c i := ⟨_, rfl⟩
    have hc'sum : ∑ i, c' i • v i = 0 := by
      simp only [hc', mul_smul, ← Finset.smul_sum, hsum, smul_zero]
    have hc'i0 : c' i0 = 1 := by
      rw [hc']
      exact inv_mul_cancel₀ hi0
    have hsupp : Finset.univ.filter (fun i => c' i ≠ 0) = Finset.univ.filter (fun i => c i ≠ 0) := by
      ext i
      simp [hc', hi0]

    have hfix : ∀ g i, σ g (c' i) = c' i := by
      intro g
      obtain ⟨d, hd⟩ : ∃ d : ι → E, d = fun i => σ g (c' i) - c' i := ⟨_, rfl⟩
      have h1 : ∑ i, σ g (c' i) • v i = 0 := by
        have h2 := congrArg (ρ g) hc'sum
        rw [map_sum, map_zero] at h2
        simpa [hρ, hv] using h2
      have hdsum : ∑ i, d i • v i = 0 := by
        simp only [hd, sub_smul, Finset.sum_sub_distrib, h1, hc'sum, sub_zero]
      have hsub : Finset.univ.filter (fun i => d i ≠ 0) ⊆
          (Finset.univ.filter (fun i => c' i ≠ 0)).erase i0 := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hi ⊢
        refine ⟨?_, ?_⟩
        · rintro rfl
          apply hi
          simp [hd, hc'i0]
        · intro h0
          apply hi
          simp [hd, h0]
      have hmem : i0 ∈ Finset.univ.filter (fun i => c' i ≠ 0) := by simp [hc'i0]
      have hdcard : (Finset.univ.filter (fun i => d i ≠ 0)).card ≤ n := by
        have h3 := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hmem, hsupp] at h3
        omega
      intro i
      have h5 := ih d hdcard hdsum i
      rw [hd] at h5
      exact sub_eq_zero.mp h5
    have h4 := hind c' hfix hc'sum i0
    rw [hc'i0] at h4
    exact one_ne_zero h4

end GlobalTheory.Per
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCommuteOfCommuteSeparableCharpolyStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_commute_of_commute_separable_charpoly : ∀ (E : Type) [Field E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E), A₀.charpoly.Separable → ∀ m n : Matrix (Fin r) (Fin r) E, m * A₀ = A₀ * m → n * A₀ = A₀ * n → m * n = n * m := by
  first | exact @GlobalTheory.CommSep.commute_of_commute_separable | exact GlobalTheory.CommSep.commute_of_commute_separable | (intros; apply GlobalTheory.CommSep.commute_of_commute_separable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeAlgebraMapOfStarEqStatement
section
open GlobalTheory.UnitLemma Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_range_algebraMap_of_star_eq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [GlobalTheory.JR.Unram F E] (y : E), star y = y → ∃ x : F, algebraMap F E x = y := by
  first | exact @GlobalTheory.JR.Unram.mem_range_of_star_eq | exact GlobalTheory.JR.Unram.mem_range_of_star_eq | (intros; apply GlobalTheory.JR.Unram.mem_range_of_star_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCharacterOnIdempotentPartFramePropertiesStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normCharacterOnIdempotentPart_frame_properties : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A) (S : Finset ι), IsFrame B e π S → (∀ (I : Finset ι) (x y : B.A), IsUnit x → IsUnit y → chi B e I (x * y) = chi B e I x * chi B e I y) ∧ (∀ (I : Finset ι) (w : B.A), IsUnit w → chi B e I (w * B.σ w) = 1) ∧ (∀ I J : Finset ι, I ⊆ S → J ⊆ S → chi B e I (∏ j ∈ J, π j) = (-1) ^ (J ∩ I).card) ∧ (∀ y, B.Plus y → chi B e S y = K.eta (Algebra.norm K.E y)) := by
  first | exact @GlobalTheory.UnitLemma.Desc.chi_frame_props | exact GlobalTheory.UnitLemma.Desc.chi_frame_props | (intros; apply GlobalTheory.UnitLemma.Desc.chi_frame_props <;> assumption)
end

