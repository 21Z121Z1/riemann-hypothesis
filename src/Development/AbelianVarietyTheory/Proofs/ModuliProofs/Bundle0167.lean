import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0012
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0162
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0163
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0164
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0062

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoLinCombLamOfAppellHumbert
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory

namespace SharpBundle

def IsFrameAlong {g : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (L : LB X)
    (fr : L.ι → (Fin g → ℂ) → ℂ) : Prop :=
  (∀ i, DifferentiableOn ℂ (fr i) {z | ⊤ ≤ e z ⁻¹ᵁ L.U i}) ∧ (∀ i z, ⊤ ≤ e z ⁻¹ᵁ L.U i → fr i z ≠ 0) ∧
    ∀ i j z, ⊤ ≤ e z ⁻¹ᵁ (L.U i ⊓ L.U j) → fr i z = valAt' (e z) (L.U i ⊓ L.U j) (L.g i j).val * fr j z

theorem differentiableOn_finset_prod {E κ : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E}
    (s : Finset κ) (φ : κ → E → ℂ) (h : ∀ k, DifferentiableOn ℂ (φ k) S) :
    DifferentiableOn ℂ (fun z => ∏ k ∈ s, φ k z) S := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using differentiableOn_const (1 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

theorem IsFrameAlong.linComb {g : ℕ} {X Y : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (L : LB Y) {K : Type}
    [Fintype K] (φ : K → (X ⟶ Y)) (ε : K → ℤ) (fr : K → L.ι → (Fin g → ℂ) → ℂ)
    (h : ∀ k, IsFrameAlong (fun z => e z ≫ φ k) L (fr k)) :
    IsFrameAlong e (LB.LinComb L φ ε) (fun (j : K → L.ι) z => ∏ k, fr k (j k) z ^ ε k) := by
  have hc : ∀ (j : K → L.ι) z, ⊤ ≤ e z ⁻¹ᵁ LB.wchart L φ j → ∀ k, ⊤ ≤ (e z ≫ φ k) ⁻¹ᵁ L.U (j k) :=
    fun j z hz => (CubeValues.le_preimage_wchart (e z) L φ j).1 hz
  refine ⟨fun j => ?_, fun j z hz => ?_, fun j j' z hz => ?_⟩
  · refine differentiableOn_finset_prod Finset.univ (fun k (z : Fin g → ℂ) => fr k (j k) z ^ ε k) fun k => ?_
    refine DifferentiableOn.zpow ?_ (Or.inl fun z hz => (h k).2.1 _ _ (hc j z hz k))
    exact ((h k).1 (j k)).mono fun z hz => hc j z hz k
  · exact Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ ((h k).2.1 _ _ (hc j z hz k))
  · obtain ⟨h1, h2⟩ := (top_le_preimage_inf (e z) _ _).1 hz
    have e1 := CubeValues.val_linComb (e z) valAt'_rules L φ ε j j' h1 h2
    refine Eq.trans ?_ (congrArg (· * ∏ k, fr k (j' k) z ^ ε k) e1.symm)
    show _ = (∏ k, _) * _
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← mul_zpow]
    exact congrArg (· ^ ε k) ((h k).2.2 (j k) (j' k) z
      ((top_le_preimage_inf _ _ _).2 ⟨hc j z h1 k, hc j' z h2 k⟩))

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem isFrameAlong_comp {n : ℕ} (F : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)) :
    IsFrameAlong (fun z => (u.ex (F z)).left) L (fun i z => u.fr i (F z)) :=
  ⟨fun i => (u.fr_hol i).comp (LinearMap.toContinuousLinearMap F).differentiable.differentiableOn fun _ hz => hz,
    fun i z hz => u.fr_ne i (F z) hz, fun i j z hz => u.fr_compat i j (F z) hz⟩

def withFrame {M : LB A.left} (fr : M.ι → (Fin g → ℂ) → ℂ) (h : IsFrameAlong (fun z => (u.ex z).left) M fr) :
    HolUnif A M g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := fr
  fr_hol := h.1
  fr_ne := h.2.1
  fr_compat := h.2.2

theorem hermForm_add_left (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp [hermForm, add_dotProduct]

theorem hermForm_add_right (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp [hermForm, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_swap {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = hermForm Hm z w - 2 * Complex.I * ((hermForm Hm z w).im : ℂ) := by
  have h : hermForm Hm w z = starRingEnd ℂ (hermForm Hm z w) := by
    change _ = star (hermForm Hm z w)
    unfold hermForm
    rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, hH.eq, Matrix.dotProduct_mulVec]
  rw [h]
  apply Complex.ext <;> simp
  ring

variable {u} {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}

theorem ah_step (h : u.IsAH Hm χ) (l : u.Λ) (i : L.ι) (z : Fin g → ℂ) (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i) :
    u.fr i z = χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * u.fr i (z + l) :=
  h.2.2.2 l i z hz

theorem ah_step_add (h : u.IsAH Hm χ) (l m : u.Λ) (i : L.ι) (z : Fin g → ℂ) (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i) :
    u.fr i z = χ l * χ m * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l +
      (Real.pi * hermForm Hm (z + l) m + Real.pi / 2 * hermForm Hm m m)) * u.fr i (z + l + m) := by
  have h2 := ah_step h m i (z + l) (by rw [CubeValues.ex_add_period u z l l.2]; exact hz)
  rw [ah_step h l i z hz, h2, Complex.exp_add _ (_ + _)]
  ring

theorem prod_finset_fin_two' (f : Finset (Fin 2) → ℂ) :
    ∏ I : ULift.{0} (Finset (Fin 2)), f I.down = f ∅ * f {0} * f {1} * f {0, 1} := by
  rw [Fintype.prod_equiv Equiv.ulift (fun I : ULift.{0} (Finset (Fin 2)) => f I.down) f fun I => rfl]
  have : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [this, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  ring

theorem lam_step (h : u.IsAH Hm χ) (j : ULift.{0} (Finset (Fin 2)) → L.ι) (x x' : Fin 2 → Fin g → ℂ) (l : Fin 2 → u.Λ)
    (hx' : ∀ a, x' a = x a + l a)
    (hx : ∀ I, ⊤ ≤ (u.ex (∑ a ∈ I.down, x a)).left ⁻¹ᵁ L.U (j I)) :
    ∏ I : ULift.{0} (Finset (Fin 2)), u.fr (j I) (∑ a ∈ I.down, x a) ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      Complex.exp (Real.pi * Complex.I * ((hermForm Hm (l 0) (l 1)).im : ℂ) +
        (Real.pi * (hermForm Hm (x 0) (l 1) + hermForm Hm (x 1) (l 0)) +
          Real.pi / 2 * (hermForm Hm (l 0) (l 1) + hermForm Hm (l 1) (l 0)))) *
      ∏ I : ULift.{0} (Finset (Fin 2)), u.fr (j I) (∑ a ∈ I.down, x' a) ^ ((-1 : ℤ) ^ (2 - I.down.card)) := by
  rw [prod_finset_fin_two' fun I => u.fr (j ⟨I⟩) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (2 - I.card)),
    prod_finset_fin_two' fun I => u.fr (j ⟨I⟩) (∑ a ∈ I, x' a) ^ ((-1 : ℤ) ^ (2 - I.card))]
  have c01 : ({0, 1} : Finset (Fin 2)).card = 2 := rfl
  have s01 : ∀ y : Fin 2 → Fin g → ℂ, ∑ a ∈ ({0, 1} : Finset (Fin 2)), y a = y 0 + y 1 := fun y =>
    Finset.sum_pair (by decide)
  have h0 := hx ⟨{0}⟩
  have h1 := hx ⟨{1}⟩
  have h01 := hx ⟨{0, 1}⟩
  simp only [Finset.sum_singleton, s01] at h0 h1 h01
  have e0 := ah_step h (l 0) _ _ h0
  have e1 := ah_step h (l 1) _ _ h1
  have e01 := ah_step_add h (l 0) (l 1) _ _ h01
  have n0 : χ (l 0) ≠ 0 := fun e => by simpa [e] using h.2.2.1 (l 0)
  have n1 : χ (l 1) ≠ 0 := fun e => by simpa [e] using h.2.2.1 (l 1)
  have hs : x 0 + l 0 + (x 1 + l 1) = x 0 + x 1 + l 0 + l 1 := by abel
  simp only [Finset.sum_singleton, s01, Finset.sum_empty, Finset.card_empty, Finset.card_singleton, c01, hx', hs]
  norm_num
  rw [e0, e1, e01]
  have key : Complex.exp (Real.pi * hermForm Hm (x 0 + x 1) (l 0) + Real.pi / 2 * hermForm Hm (l 0) (l 0) +
      (Real.pi * hermForm Hm (x 0 + x 1 + l 0) (l 1) + Real.pi / 2 * hermForm Hm (l 1) (l 1))) =
      Complex.exp (Real.pi * Complex.I * ((hermForm Hm (l 0) (l 1)).im : ℂ) +
        (Real.pi * (hermForm Hm (x 0) (l 1) + hermForm Hm (x 1) (l 0)) +
          Real.pi / 2 * (hermForm Hm (l 0) (l 1) + hermForm Hm (l 1) (l 0)))) *
      Complex.exp (Real.pi * hermForm Hm (x 0) (l 0) + Real.pi / 2 * hermForm Hm (l 0) (l 0)) *
      Complex.exp (Real.pi * hermForm Hm (x 1) (l 1) + Real.pi / 2 * hermForm Hm (l 1) (l 1)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [hermForm_add_left]
    rw [hermForm_swap h.1 (l 0) (l 1)]
    ring
  rw [key]
  have := Complex.exp_ne_zero (Real.pi * hermForm Hm (x 0) (l 0) + Real.pi / 2 * hermForm Hm (l 0) (l 0))
  have := Complex.exp_ne_zero (Real.pi * hermForm Hm (x 1) (l 1) + Real.pi / 2 * hermForm Hm (l 1) (l 1))
  simp only [mul_inv]
  field_simp

theorem sum_symmetrise {n : ℕ} (W : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → Fin n → ℂ) :
    ∑ uv : Fin n × Fin n, (W uv.1 uv.2 : ℂ) * (b uv.1 uv.2 + b uv.2 uv.1) =
      ∑ i, ∑ j, ((W + W.transpose) i j : ℂ) * b i j := by
  simp only [Fintype.sum_prod_type, Matrix.add_apply, Matrix.transpose_apply, Int.cast_add, mul_add, add_mul,
    Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

end SharpBundle

open SharpBundle in

theorem lbIso_linComb_lam_of_appellHumbert : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (P₀ : Out.PolAV (Sp ℂ)) (u₀ : HolUnif P₀.A P₀.L P₀.g) (H₀ : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ₀ : u₀.Λ → ℂ) (pr : Fin 8 → (P.A ⟶ P₀.A)) (R : Fin 8 → ((Fin P.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ))), u.IsAH Hm χ → u₀.IsAH H₀ χ₀ → (∀ i z, u₀.ex (R i z) = u.ex z ≫ pr i) → (∀ z w, hermForm Hm z w = ∑ i, ∑ j, ((W + W.transpose) i j : ℂ) * hermForm H₀ (R i z) (R j w)) → (∀ l : u.Λ, χ l = Complex.exp (Real.pi * Complex.I * ∑ i, ∑ j, (W i j : ℂ) * ((hermForm H₀ (R i l) (R j l)).im : ℂ))) → LBIso P.L (LB.LinComb (abelian₂ P₀.A P₀.L) (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) := by
  intro h1 h2 h3 h4 W P u Hm χ P₀ u₀ H₀ χ₀ pr R hu hu₀ hR hH hχ
  let r : Fin 8 × Fin 8 → Fin 2 → Fin 8 := fun uv => ![uv.1, uv.2]
  have hpt : ∀ (uv : Fin 8 × Fin 8) (I : Finset (Fin 2)) z,
      ((u.ex z).left ≫ (lift (pr uv.1) (pr uv.2)).left) ≫ (psum P₀.A (x2 P₀.A) I).left =
        (u₀.ex (∑ a ∈ I, R (r uv a) z)).left := fun uv I z => by
    rw [← Over.comp_left, ← Over.comp_left,
      CubeValues.comp_psum u₀ (u.ex z ≫ lift (pr uv.1) (pr uv.2)) (x2 P₀.A) fun a => R (r uv a) z]
    intro k
    fin_cases k <;> simp [x2, r, hR]
  have hin : ∀ uv : Fin 8 × Fin 8, IsFrameAlong (fun z => (u.ex z).left ≫ (lift (pr uv.1) (pr uv.2)).left)
      (abelian₂ P₀.A P₀.L) (fun (j : ULift.{0} (Finset (Fin 2)) → P₀.L.ι) z =>
        ∏ I : ULift.{0} (Finset (Fin 2)), u₀.fr (j I) (∑ a ∈ I.down, R (r uv a) z) ^ ((-1 : ℤ) ^ (2 - I.down.card))) :=
    fun uv => IsFrameAlong.linComb _ P₀.L (K := ULift.{0} (Finset (Fin 2))) _ _
      (fun I i z => u₀.fr i (∑ a ∈ I.down, R (r uv a) z)) fun I => by
        simp only [hpt]
        simpa only [LinearMap.sum_apply] using isFrameAlong_comp u₀ (∑ a ∈ I.down, R (r uv a))
  have hout := IsFrameAlong.linComb (fun z => (u.ex z).left) (abelian₂ P₀.A P₀.L) (K := Fin 8 × Fin 8)
    (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2) _ hin
  have hΛ : ∀ i (l : u.Λ), R i l ∈ u₀.Λ := fun i l => by
    rw [← u₀.ker, hR, (u.ker _).2 l.2, ← CubeValues.ex_zero u, ← hR, map_zero, CubeValues.ex_zero]
  refine GlobalTheory.lbIso_of_same_factor h1 h2 h3 h4 P _ _ u (withFrame u _ hout) P.isLB
    (LB.isLB_linComb (LB.isLB_linComb P₀.isLB _ _) _ _) rfl fun l i j z hi hj => ?_
  have hj' := (CubeValues.le_preimage_wchart (u.ex z).left (abelian₂ P₀.A P₀.L) _ j).1 hj
  have hst := fun uv : Fin 8 × Fin 8 => lam_step hu₀ (j uv) (fun a => R (r uv a) z) (fun a => R (r uv a) (z + l))
    (fun a => ⟨R (r uv a) l, hΛ _ l⟩) (fun a => map_add _ _ _) fun I => by
      rw [← hpt]
      exact (CubeValues.le_preimage_wchart _ P₀.L _ (j uv)).1 (hj' uv) I
  change u.fr i z * ∏ uv : Fin 8 × Fin 8, _ = u.fr i (z + l) * ∏ uv : Fin 8 × Fin 8, _
  simp only [hst, mul_zpow, Finset.prod_mul_distrib, ← Complex.exp_int_mul, ← Complex.exp_sum]
  rw [ah_step hu l i z hi, hχ, ← Complex.exp_add, hH, hH, ← sum_symmetrise W fun a b => hermForm H₀ (R a z) (R b l),
    ← sum_symmetrise W fun a b => hermForm H₀ (R a l) (R b l), ← Fintype.sum_prod_type' fun a b =>
      (W a b : ℂ) * ((hermForm H₀ (R a l) (R b l)).im : ℂ), Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, mul_comm _ (u.fr i (z + l)), _root_.mul_assoc]
  congr 3
  refine Finset.sum_congr rfl fun uv _ => ?_
  simp only [r, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisedIsoCommutesFieldAutomorphismOfTorsionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedIso_commutes_fieldAutomorphism_of_torsion : Laws → ∀ (S : Scheme.{0}) (P P' : PolAV S) (C : Type) [Field C] [IsAlgClosed C] (t : Sp C ⟶ S) (φ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P'.A), φ.hom ≫ fst _ _ = fst _ _ → lift (𝟙 (Over.mk t)) (1 : Over.mk t ⟶ P.A) ≫ φ.hom ≫ snd _ _ = 1 → LBIso (P.L.pull (snd (Over.mk t) P.A).left) (P'.L.pull (φ.hom ≫ snd (Over.mk t) P'.A).left) → ∀ k : ℕ, 3 ≤ k → (k : C) ≠ 0 → ∀ s : Over.mk t ≅ Over.mk t, (∀ x : Over.mk t ⟶ P.A, x ^ k = 1 → lift (𝟙 (Over.mk t)) (s.hom ≫ x) ≫ φ.hom ≫ snd _ _ = s.hom ≫ lift (𝟙 (Over.mk t)) x ≫ φ.hom ≫ snd _ _) → s.hom ▷ P.A ≫ φ.hom ≫ snd _ _ = φ.hom ≫ snd _ _ := by
  first | exact @GlobalTheory.SerreTwist.whisker_comp_eq | exact GlobalTheory.SerreTwist.whisker_comp_eq | (intros; apply GlobalTheory.SerreTwist.whisker_comp_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RaisedModelFiniteCoverAmpleFramesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raised_model_finite_cover_ample_frames : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N k : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), n.Prime → Odd n → (∃ e, N = n ^ e) → IsUnit (n : O) → l₀.Dvd l → IsDedFrac β → Raises B Y → Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L ((n ^ k) ^ 2)) → GlobalTheory.LN.Amp Y := by
  first | exact @GlobalTheory.RaisedAmple.amp_of_raises | exact GlobalTheory.RaisedAmple.amp_of_raises | (intros; apply GlobalTheory.RaisedAmple.amp_of_raises <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RaisedModelLevelOneDescendsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raised_model_level_one_descends : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ : Level H) (B : BaseModel T l₀) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), 0 < n → l₀.Dvd l → l.A = 1 → IsDedFrac β → Raises B Y → Y.Descends := by
  first | exact @GlobalTheory.RaisedDescends.descends_of_raises | exact GlobalTheory.RaisedDescends.descends_of_raises | (intros; apply GlobalTheory.RaisedDescends.descends_of_raises <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_principal_object_descends_large_subfield : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (K : Type) [Field K] (K₀ : Subfield K) (s₀ : Sp K₀ ⟶ Sp o) (s : Sp K ⟶ Sp o) (c : SiegPre h M ζ s), s = spMap K₀.subtype ≫ s₀ → c.Principal → ∃ F : Finset K, ∀ (K₁ : Subfield K) (hK : K₀ ≤ K₁), (F : Set K) ⊆ K₁ → ∃ c₁ : SiegPre h M ζ (spMap (Subfield.inclusion hK) ≫ s₀), c₁.Principal ∧ SiegPB c c₁ (spMap K₁.subtype) := by
  first | exact @GlobalTheory.SiegDesc.siegPre_descends | exact GlobalTheory.SiegDesc.siegPre_descends | (intros; apply GlobalTheory.SiegDesc.siegPre_descends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TangentLeDim
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PelTangent

open GlobalTheory.ShapePull

def chartPullSection {X Y : Scheme.{0}} (L : LB X) (F : Y ⟶ X) (r : X ⟶ Y) (e : r ≫ F = 𝟙 X) :
    ChartPull L (L.pull F) r :=
  have m : ∀ i y, y ∈ L.U i → r y ∈ (L.pull F).U (fun _ => i) := fun i y hy => mem_pull.2 (by
    have : F (r y) = y := congrArg (fun g : X ⟶ X => g y) e
    rw [this]; exact hy)
  { idx := fun i _ => i
    le := fun i y hy => m i y hy
    g := fun y i j hi hj =>
      ((gm_pull_g L F r y (fun _ => i) (fun _ => j) (m i y hi) (m j y hj)).trans (by rw [e])).symm }

section Group

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem exists_oAct (h : IsGrpPullback G' G f φ) {O : Type} [CommRing O] (a : OAct O G) :
    ∃ a' : OAct O G', ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left := by
  choose w hw pa using fun c => (haveI := a.hom c; GlobalTheory.SymBaseChange.exists_endo h (a.act c))
  have hl : ∀ c, (w c).left ≫ φ = φ ≫ (a.act c).left := fun c => by
    have := congrArg (fun z => z.left) (pa c (𝟙 G'))
    simpa [pushPt] using this
  refine ⟨⟨w, hw, ?_, fun c d => ?_, fun c d => ?_⟩, hl⟩
  · exact eq_up h _ (push_end h (hl 1)) (push_id h) a.one
  · exact eq_up h _ (push_end h (hl _)) (push_comp h _ (push_end h (hl c)) (hl d)) (a.mul c d)
  · exact eq_up h _ (push_end h (hl _)) (push_mul h _ (push_end h (hl c)) (push_end h (hl d))) (a.add c d)

theorem adj_up [IsCommMonObj G] [IsCommMonObj G'] (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left}
    (hL : L.IsLB) (hL' : L'.IsLB) (H : LBIso L' (L.pull φ)) {w v : G ⟶ G} {w' v' : G' ⟶ G'}
    (hw : w'.left ≫ φ = φ ≫ w.left) (hv : v'.left ≫ φ = φ ≫ v.left)
    (A : LBIso (cubeLB G ![fst G G ≫ w, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ v] L)) :
    LBIso (cubeLB G' ![fst G' G' ≫ w', snd G' G'] L') (cubeLB G' ![fst G' G', snd G' G' ≫ v'] L') :=
  iso_up (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _)
    (DVR.linComb_isLB _ hL' _ _) (iso_cubeLB_pull h _ H (push_comp h _ (push_fst h) hw) (push_snd h))
    (iso_cubeLB_pull h _ H (push_fst h) (push_comp h _ (push_snd h) hv)) A

theorem prim_up [IsCommMonObj G] [IsCommMonObj G'] (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left}
    (hL : L.IsLB) (hL' : L'.IsLB) (H : LBIso L' (L.pull φ)) {w : G ⟶ G} {w' : G' ⟶ G'}
    (hw : w'.left ≫ φ = φ ≫ w.left) (A : LBIso L (cubeLB G ![𝟙 G, w] L)) :
    LBIso L' (cubeLB G' ![𝟙 G', w'] L') := by
  have i : LBIso (cubeLB G' ![𝟙 G', w'] L') ((cubeLB G ![𝟙 G, w] L).pull φ) :=
    iso_cubeLB_pull h (selfMap h) H (push_id h) (push_end h hw)
  have a : (cubeLB G ![𝟙 G, w] L).IsLB := DVR.linComb_isLB _ hL _ _
  have a' : (cubeLB G' ![𝟙 G', w'] L').IsLB := DVR.linComb_isLB _ hL' _ _
  exact iso_up hL a hL' a' H i A

end Group

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cmHostUnit_add_conj_eq_one (H : Host E) : H.w0 + H.bar H.w0 = 1 := by
  have h1 : H.bar H.rt ^ 2 = H.rt ^ 2 := by
    rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  have h2 : 2 * H.bar H.w0 = 1 + H.bar H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    simpa [map_ofNat] using this
  have h3 : H.bar H.rt = -H.rt := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with e | e
    · exfalso
      have e' : IsCMField.complexConj E (H.rt : E) = H.rt := by rw [← H.bar_eq, e]
      obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have c := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
      rw [e'] at c
      have r : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
        have := congrArg (fun z : 𝓞 E => φ (z : E)) H.rt_sq
        simpa using this
      obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 c.symm
      rw [hx] at r
      have r' : x ^ 2 = -(H.d : ℝ) := by exact_mod_cast r
      have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      nlinarith [sq_nonneg x]
    · exact e
  have : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    rw [mul_add, h2, H.two_weight_eq_one_add_root, h3]; ring
  exact mul_left_cancel₀ two_ne_zero this

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'')
    (h : R →+* R'') (e : g.comp f = h) : spMap g ≫ spMap f = spMap h := by
  subst e
  exact (Spec.map_comp _ _).symm

theorem tangent_le_dim : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (r : ℕ) (β : o →+* K) (t : TObj g k J b (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))) (τ : SAB H (Sp (TrivSqZeroExt K (Fin r → K)))), a w = H.w0 → a w' = H.bar H.w0 → ρ ^ 2 = -(H.d : o) → IsPEL D a bas ρ t τ → (∀ (lam : (Fin r → K) →ₗ[K] K) (t' : TObj g k J b (spMap ((algebraMap K (DualNumber K)).comp β))), TMap t' t (spMap (dirMap lam)) → TMap t' t (constPt (spMap (dirMap lam))) → lam = 0) → r ≤ D.dim := by
  intro L1 L2 L3 E _ _ _ H D g J a w w' bas k o _ b ρ K _ _ _ r β t τ hw hw' hρ ⟨e, he, hL, hact, hdet⟩ hlam
  letI := t.ab.comm
  let p : Sp K ⟶ Sp (TrivSqZeroExt K (Fin r → K)) := spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom
  let q : Sp K ⟶ Sp (DualNumber K) := spMap (TrivSqZeroExt.fstHom K K K).toRingHom
  have hp : p ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) = spMap β :=
    spMap_comp _ _ _ (by ext x; simp [TrivSqZeroExt.algebraMap_eq_inl])
  obtain ⟨t₀, T₀⟩ := GlobalTheory.tObj_pull o g k J b _ _ _ _ p t hp
  obtain ⟨φ₀, h₀, hL₀, hpt₀, hact₀⟩ := id T₀
  letI := t₀.ab.comm

  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have h₁ : IsGrpPullback t.A τ.G (𝟙 _) e.inv.left := isGrpPullback_of_iso e.symm
  have ih : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
  have hL₁ : LBIso t.L (τ.PP.L.pull e.inv.left) :=
    LBIso.chartPull (chartPullSection t.L _ _ ih) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull τ.PP.L _ _ rfl) hL.symm
  obtain ⟨A, hA⟩ := exists_oAct h₁ τ.act
  obtain ⟨A₀, hA₀⟩ := exists_oAct h₀ A
  have hj : ∀ j, (t.act j).left ≫ e.inv.left = e.inv.left ≫ (τ.act.act (a j)).left := fun j => by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [Iso.comp_inv_eq, Category.assoc, hact, e.inv_hom_id_assoc]
  have adj := fun c => adj_up h₁ τ.PP.isLB t.isLB hL₁ (hA c) (hA (H.bar c)) (τ.adj c)
  have prim : t.Prim w w' := by
    refine ⟨eq_up h₁ _ (push_mul h₁ _ (push_end h₁ (hj w)) (push_end h₁ (hj w'))) (push_id h₁) ?_,
      adj_up h₁ τ.PP.isLB t.isLB hL₁ (hj w) (hj w') ?_, prim_up h₁ τ.PP.isLB t.isLB hL₁ (hj w) ?_⟩
    · rw [hw, hw', ← τ.act.add, cmHostUnit_add_conj_eq_one, τ.act.one]
    · rw [hw, hw']; exact τ.adj _
    · rw [hw]; exact τ.prim
  have det : DetCond D A₀ (𝟙 (Sp K)) (β ρ) := fun σ => by
    have key : ∀ n, LieMult τ.act p σ n → LieMult A₀ (𝟙 (Sp K)) σ n := fun n hn =>
      (GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ A A₀ h₀ hA₀ K _ σ n).2
        ((GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ τ.act A h₁ hA K _ σ n).2 (by
          rw [Category.comp_id, Category.id_comp]; exact hn))
    have := (hdet K p β hp).1 σ
    exact ⟨fun x => key _ (this.1 x), fun x => key _ (this.2 x)⟩
  obtain ⟨n, v, ty, hv, hty, hdiag⟩ := GlobalTheory.exists_adapted_lieBasis E H D K t₀.A A₀ (β ρ) t₀.ab.smooth det
  obtain ⟨Θ, hsym, hcomm, hker⟩ := GlobalTheory.T.exists_ksMatrix_alt L1 L2 L3 K r t.pol t₀.pol φ₀ n v h₀ hL₀ hv
  have inj : Function.Injective Θ := by
    rw [injective_iff_map_eq_zero]
    intro lam h0
    let d : Sp (DualNumber K) ⟶ Sp (TrivSqZeroExt K (Fin r → K)) := spMap (dirMap lam)
    have hd : d ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) =
        spMap ((algebraMap K (DualNumber K)).comp β) :=
      spMap_comp _ _ _ (by ext x <;> simp [dirMap, TrivSqZeroExt.algebraMap_eq_inl])
    have hq : q ≫ d = p := spMap_comp _ _ _ (by ext x; simp [dirMap])
    obtain ⟨t', T'⟩ := GlobalTheory.tObj_pull o g k J b _ _ _ _ d t hd
    obtain ⟨ψ, h', hL', hpt', hact'⟩ := id T'
    letI := t'.ab.comm
    obtain ⟨ψ₀, k₀, k₁⟩ := hker lam h0 t'.A ψ h'
    let io : t₀.A.left ⟶ t'.A.left := h'.1.lift φ₀ (t₀.A.hom ≫ q) (by rw [h₀.1.w, Category.assoc, hq])
    have i₁ : io ≫ ψ = φ₀ := h'.1.lift_fst _ _ _
    have i₂ : io ≫ t'.A.hom = t₀.A.hom ≫ q := h'.1.lift_snd _ _ _
    have prim' : t'.Prim w w' :=
      ⟨eq_up h' _ (push_mul h' _ (push_end h' (hact' w)) (push_end h' (hact' w'))) (push_id h') prim.1,
        adj_up h' t.isLB t'.isLB hL' (hact' w) (hact' w') prim.2.1, prim_up h' t.isLB t'.isLB hL' (hact' w) prim.2.2⟩
    have c₁ : IsGrpPullback t₀.A t'.A q io := h'.cancel (h₀.congr hq.symm i₁.symm) i₂
    have c₂ : LBIso t₀.L (t'.L.pull io) :=
      LBIso.trans t₀.isLB (pull_isLB t.isLB φ₀) (pull_isLB t'.isLB io) hL₀
        (LBIso.chartPull (chartPullSame t.L _ _ _ io fun _ => i₁.symm) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t'.L io io rfl) hL'.symm)
    have c₃ : ∀ i, (t₀.pt i).left ≫ io = q ≫ (t'.pt i).left := fun i => by
      apply h'.1.hom_ext
      · rw [Category.assoc, i₁, hpt₀, Category.assoc, hpt', ← Category.assoc, hq]
      · rw [Category.assoc, i₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
    have c₄ : ∀ j, (t₀.act j).left ≫ io = io ≫ (t'.act j).left := fun j => by
      apply h'.1.hom_ext
      · rw [Category.assoc, i₁, hact₀, Category.assoc, hact', ← Category.assoc, i₁]
      · rw [Category.assoc, i₂, ← Category.assoc, Over.w, Category.assoc, Over.w, i₂]
    have T₁ := GlobalTheory.ConstTheta.tMap_of_const L1 L2 L3 o g k J b w w' K _ _ t' t₀ io ψ₀ prim' c₁ c₂ c₃ c₄ k₀ (k₁ io i₁ i₂)
    have T₂ := ((GlobalTheory.ZM.tmap_id_comp_cancel o g k J b _ _ _ _ _ _ t t₀ t').2 _ _ T₀).1 T₁
    refine hlam lam t' T' ?_
    show TMap t' t (_ ≫ q ≫ d)
    rw [hq]
    exact T₂
  have hρ' : β ρ ^ 2 = -(H.d : K) := by rw [← map_pow, hρ, map_neg, map_natCast]
  have B := GlobalTheory.SymSignature.finrank_le E H D.p D.q n K (β ρ) ty (LinearMap.range Θ) hρ' hty (by
    rintro _ ⟨lam, rfl⟩
    exact ⟨hsym lam, fun c => hcomm (A.act c) (A.act (H.bar c)) (A₀.act c) (A₀.act (H.bar c)) _ _ (A.hom _) (A.hom _)
      (hA₀ _) (hA₀ _) (adj c) (hdiag c) (hdiag (H.bar c)) lam⟩)
  rw [LinearMap.finrank_range_of_inj inj] at B
  simpa [Datum.dim, Module.finrank_linearMap] using B

end GlobalTheory.PelTangent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelObjectDescendsFgSubfieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLevel_object_descends_fg_subfield : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) [Finite J] (K : Type) [Field K] (β : o →+* K) (t : TObj g k J b (spMap β)), ∃ (K₀ : Subfield K) (β₀ : o →+* K₀) (t₀ : TObj g k J b (spMap β₀)), K₀.subtype.comp β₀ = β ∧ (Countable o → Countable K₀) ∧ (∃ s : Finset K, K₀ = Subfield.closure (Set.range β ∪ s)) ∧ TMap t t₀ (spMap K₀.subtype) := by
  first | exact @GlobalTheory.ThetaDescent.descends_to_fg_subfield | exact GlobalTheory.ThetaDescent.descends_to_fg_subfield | (intros; apply GlobalTheory.ThetaDescent.descends_to_fg_subfield <;> assumption)
end

