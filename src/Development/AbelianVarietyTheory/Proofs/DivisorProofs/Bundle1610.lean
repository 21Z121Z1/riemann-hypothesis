import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1434
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorMixedLaplacianKilledLoweringKilled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0288
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1579
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowRankBoxFunctionStable
section
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.RankCoinv.Nbhd

section
variable {k : Type} [Field k] {Γ : Type*} [LinearOrderedCommMonoidWithZero Γ] (v : Valuation k Γ)
variable {X Y W : Type} [Fintype Y]

theorem val_mul_le {P : Matrix X Y k} {Z : Matrix Y W k} {s t : Γ} (hP : ∀ i a, v (P i a) ≤ s)
    (hZ : ∀ a j, v (Z a j) ≤ t) (i : X) (j : W) : v ((P * Z) i j) ≤ s * t := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun a _ => ?_
  rw [map_mul]; exact mul_le_mul' (hP i a) (hZ a j)
end

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_inv_pow (ϖ : kˣ) (c : ℕ) :
    valuation k (((ϖ ^ c)⁻¹ : kˣ) : k) = (valuation k (ϖ : k))⁻¹ ^ c := by
  simp [Units.val_inv_eq_inv_val, map_inv₀, map_pow, inv_pow]

theorem exists_le_inv_pow {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (x : k) :
    ∃ c : ℕ, valuation k x ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k) := by
  by_cases h : valuation k x ≤ 1
  · exact ⟨0, by simpa using h⟩
  · have hx : x ≠ 0 := by rintro rfl; simp at h
    have h0 : 0 < valuation k x := zero_lt_iff.2 (by simpa using hx)
    have hy : valuation k x⁻¹ ≤ 1 := by
      rw [map_inv₀]
      calc (valuation k x)⁻¹ = (valuation k x)⁻¹ * 1 := (mul_one _).symm
        _ ≤ (valuation k x)⁻¹ * valuation k x := mul_le_mul' le_rfl (le_of_not_ge h)
        _ = 1 := inv_mul_cancel₀ h0.ne'
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (R := 𝒪[k])
      (x := ⟨x⁻¹, hy⟩) (fun h' => hx (inv_eq_zero.1 (congrArg Subtype.val h'))) hϖ.irreducible
    refine ⟨n, ?_⟩
    have h1 : valuation k (algebraMap 𝒪[k] k u) = 1 :=
      (Valuation.integer.integers (valuation k)).one_of_isUnit u.isUnit
    have h2 : valuation k x⁻¹ = valuation k (ϖ : k) ^ n := by
      have := congrArg (fun y : 𝒪[k] => valuation k (y : k)) hu
      simp only [Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow] at this
      rw [this]
      have h1' : valuation k ((u : 𝒪[k]) : k) = 1 := h1
      rw [h1', one_mul]
    rw [valuation_inv_pow, inv_pow, ← h2, map_inv₀, inv_inv]

theorem exists_bound {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) {R S : Type} [Fintype R] [Fintype S]
    (H : Matrix R S k) : ∃ c : ℕ, ∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k) := by
  choose f hf using fun p : R × S => exists_le_inv_pow hϖ (H p.1 p.2)
  refine ⟨Finset.univ.sup f, fun l i => (hf (l, i)).trans ?_⟩
  rw [valuation_inv_pow, valuation_inv_pow]
  have hle : valuation k (ϖ : k) ≤ 1 := hϖ.mem
  have h0 : valuation k (ϖ : k) ≠ 0 := by simp
  have h1 : 1 ≤ (valuation k (ϖ : k))⁻¹ :=
    calc (1 : _) = valuation k (ϖ : k) * (valuation k (ϖ : k))⁻¹ := (mul_inv_cancel₀ h0).symm
      _ ≤ 1 * (valuation k (ϖ : k))⁻¹ := mul_le_mul' hle le_rfl
      _ = _ := one_mul _
  exact pow_le_pow_right₀ h1 (Finset.le_sup (f := f) (Finset.mem_univ (l, i)))

theorem exists_int_inv_one_add {n : Type} [Fintype n] [DecidableEq n] (E : Matrix n n k)
    (hE : ∀ i j, valuation k (E i j) < 1) :
    ∃ N : Matrix n n k, (∀ i j, N i j ∈ 𝒪[k]) ∧ (1 + E) * N = 1 := by
  have hI : ∀ i j, (1 + E) i j ∈ 𝒪[k] := fun i j => by
    rw [Valuation.mem_integer_iff, Matrix.add_apply]
    refine Valuation.map_add_le _ ?_ (hE i j).le
    rw [one_apply]; split_ifs <;> simp
  have hEI : ∀ i j, E i j ∈ 𝒪[k] := fun i j => (Valuation.mem_integer_iff _ _).2 (hE i j).le
  let M : Matrix n n 𝒪[k] := fun i j => ⟨(1 + E) i j, hI i j⟩
  have hres : (IsLocalRing.residue 𝒪[k]).mapMatrix M = 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, map_apply]
    have : M i j - (1 : Matrix n n 𝒪[k]) i j = ⟨E i j, hEI i j⟩ := by
      apply Subtype.ext
      by_cases h : i = j <;> simp [M, one_apply, h]
    have hm : M i j - (1 : Matrix n n 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      rw [this, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
      exact hE i j
    have e2 : (IsLocalRing.residue 𝒪[k]) (M i j) = (IsLocalRing.residue 𝒪[k]) ((1 : Matrix n n 𝒪[k]) i j) := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hm
    rw [e2]; by_cases h : i = j <;> simp [one_apply, h]
  have hdet : IsUnit M.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, hres, det_one]
    exact one_ne_zero
  refine ⟨(algebraMap 𝒪[k] k).mapMatrix M⁻¹, fun i j => (M⁻¹ i j).2, ?_⟩
  have hM : (algebraMap 𝒪[k] k).mapMatrix M = 1 + E := rfl
  rw [← hM, ← map_mul, Matrix.mul_nonsing_inv M hdet, map_one]

end GlobalTheory.RankCoinv.Nbhd

namespace GlobalTheory.RankCoinv.Nbhd
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

theorem inv_mul_mem_box_iff {g : GL A k} (hg : g ∈ KO k A) (ϖ : kˣ) (C X : Matrix A D k) (m : ℕ) :
    (g⁻¹).val * X ∈ box ϖ C (fun _ => m) ↔ X ∈ box ϖ (g.val * C) (fun _ => m) := by
  obtain ⟨h1, h2⟩ := (mem_KO_iff g).1 hg
  have h1' : ∀ i a, valuation k (g.val i a) ≤ 1 := fun i a => (Valuation.mem_integer_iff _ _).1 (h1 i a)
  have h2' : ∀ i a, valuation k ((g⁻¹).val i a) ≤ 1 := fun i a => (Valuation.mem_integer_iff _ _).1 (h2 i a)
  simp only [box, Set.mem_setOf_eq]
  constructor
  · intro hZ i j
    have e : X i j - (g.val * C) i j = (g.val * ((g⁻¹).val * X - C)) i j := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.sub_apply]
    rw [e]
    exact (val_mul_le (valuation k) h1' (fun a j => by rw [Matrix.sub_apply]; exact hZ a j) i j).trans_eq (one_mul _)
  · intro hZ i j
    have e : ((g⁻¹).val * X) i j - C i j = ((g⁻¹).val * (X - g.val * C)) i j := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.sub_apply]
    rw [e]
    exact (val_mul_le (valuation k) h2' (fun a j => by rw [Matrix.sub_apply]; exact hZ a j) i j).trans_eq (one_mul _)

theorem omA_boxFn {g : GL A k} (hg : g ∈ KO k A) (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (C : Matrix A D k) (m : ℕ) :
    ∃ s : ℂ, omA ν β g 1 (boxFn ϖ C (fun _ => m)) = s • boxFn ϖ (g.val * C) (fun _ => m) := by
  refine ⟨(((ν (gdet g))⁻¹ : ℂˣ) : ℂ) * apow (gdet g) (-(Fintype.card D : ℂ) / 2), funext fun X => ?_⟩
  rw [omA_one_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  by_cases h : X ∈ box ϖ (g.val * C) (fun _ => m)
  · simp only [boxFn]
    rw [Set.indicator_of_mem h, Set.indicator_of_mem ((inv_mul_mem_box_iff hg ϖ C X m).2 h)]
    rfl
  · simp only [boxFn]
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((inv_mul_mem_box_iff hg ϖ C X m).1 h'))]

end GlobalTheory.RankCoinv.Nbhd

open GlobalTheory.RankCoinv.Nbhd GlobalTheory.SplitFlip GlobalTheory.SplitWeil in

theorem GlobalTheory.RankCoinv.exists_boxFn_mem_lowRank_sup_twistSpan : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (r : ℕ) (X₀ : Matrix A D k), X₀.rank = r → r < Fintype.card A → ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ C ∈ GlobalTheory.RankCoinv.box ϖ X₀ (fun _ => m₀), GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ν β hν hνϖ r X₀ hrank hr
  obtain ⟨g, hg, i₀, hi₀⟩ := GlobalTheory.T.rank_deficient_integral_row_reduction k A D X₀ (hrank ▸ hr)
  have hgint := (GlobalTheory.SplitFlip.mem_KO_iff g).1 hg
  have hg1 : ∀ i a, valuation k (g.val i a) ≤ 1 := fun i a => (Valuation.mem_integer_iff _ _).1 (hgint.1 i a)
  have hYr : (g.val * X₀).rank = r := by
    rw [← hrank]
    exact Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
  obtain ⟨H₁, Q₁, hHQ⟩ : ∃ (H₁ : Matrix (Fin r) A k) (Q₁ : Matrix D (Fin r) k), H₁ * (g.val * X₀) * Q₁ = 1 := by
    rw [← hYr]; exact GlobalTheory.T.matrix_rank_normal_form k A D _
  let H₂ : Matrix (Fin r) A k := Matrix.of fun l i => if i = i₀ then 0 else H₁ l i
  have hH₂Y : H₂ * (g.val * X₀) = H₁ * (g.val * X₀) := by
    ext l j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [H₂, Matrix.of_apply]
    split_ifs with h
    · rw [h, hi₀ j, zero_mul, mul_zero]
    · rfl
  obtain ⟨h, Q₀, hhY, hQ₀, hhYQ⟩ := GlobalTheory.T.integral_right_inverse_normalization k D r (H₂ * (g.val * X₀)) Q₁ (by rw [hH₂Y, hHQ])
  let H := h * H₂
  have hHi₀ : ∀ l, H l i₀ = 0 := fun l => by simp [H, H₂, Matrix.mul_apply]
  obtain ⟨c, hc⟩ := exists_bound hϖ H
  refine ⟨c + 1, fun m hm C hC => ?_⟩
  have hϖ0 : valuation k (ϖ : k) ≠ 0 := by simp
  have hϖlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hCX : ∀ a j, valuation k ((C - X₀) a j) ≤ valuation k (ϖ : k) ^ (c + 1) := fun a j => by
    rw [Matrix.sub_apply]; simpa using hC a j
  have hgCX : ∀ i j, valuation k ((g.val * (C - X₀)) i j) ≤ valuation k (ϖ : k) ^ (c + 1) := fun i j => by
    simpa using val_mul_le (valuation k) hg1 hCX i j
  have hc' : ∀ l i, valuation k (H l i) ≤ (valuation k (ϖ : k))⁻¹ ^ c := fun l i => by
    rw [← valuation_inv_pow]; exact hc l i
  have hprod : (valuation k (ϖ : k))⁻¹ ^ c * valuation k (ϖ : k) ^ (c + 1) = valuation k (ϖ : k) := by
    rw [inv_pow, pow_succ, inv_mul_cancel_left₀ (pow_ne_zero _ hϖ0)]
  have hEb : ∀ l j, valuation k ((H * (g.val * (C - X₀))) l j) ≤ valuation k (ϖ : k) := fun l j => by
    rw [← hprod]; exact val_mul_le (valuation k) hc' hgCX l j
  have hsplit : g.val * C = g.val * X₀ + g.val * (C - X₀) := by rw [Matrix.mul_sub]; abel
  have hHY : H * (g.val * X₀) = h * (H₂ * (g.val * X₀)) := Matrix.mul_assoc _ _ _
  have hHC : H * (g.val * C) = H * (g.val * X₀) + H * (g.val * (C - X₀)) := by rw [hsplit, Matrix.mul_add]
  have hHCint : ∀ l j, (H * (g.val * C)) l j ∈ 𝒪[k] := fun l j => by
    rw [hHC, Valuation.mem_integer_iff, Matrix.add_apply]
    refine Valuation.map_add_le _ ?_ ((hEb l j).trans hϖlt.le)
    rw [hHY]; exact hhY l j
  have hQ₀' : ∀ j l, valuation k (Q₀ j l) ≤ 1 := fun j l => (Valuation.mem_integer_iff _ _).1 (hQ₀ j l)
  set E := H * (g.val * (C - X₀)) * Q₀ with hE
  have hEv : ∀ i j, valuation k (E i j) < 1 := fun i j =>
    lt_of_le_of_lt (by simpa using val_mul_le (valuation k) hEb hQ₀' i j) hϖlt
  have hHCQ : H * (g.val * C) * Q₀ = 1 + E := by
    rw [hHC, Matrix.add_mul, hHY, hhYQ]
  obtain ⟨N, hN, hN1⟩ := exists_int_inv_one_add E hEv
  have hN' : ∀ i j, valuation k (N i j) ≤ 1 := fun i j => (Valuation.mem_integer_iff _ _).1 (hN i j)
  have hQint : ∀ j l, (Q₀ * N) j l ∈ 𝒪[k] := fun j l => by
    rw [Valuation.mem_integer_iff]; simpa using val_mul_le (valuation k) hQ₀' hN' j l
  have hHCQ' : H * (g.val * C) * (Q₀ * N) = 1 := by rw [← Matrix.mul_assoc, hHCQ, hN1]
  have hrow : ∀ j, valuation k ((g.val * C) i₀ j) ≤ valuation k ((ϖ ^ (c + 1) : kˣ) : k) := fun j => by
    rw [hsplit, Matrix.add_apply, hi₀ j, zero_add]; simpa using hgCX i₀ j
  have hmem := GlobalTheory.T.box_function_twisted_coinvariant_rank k A D ϖ hϖ ν β hν hνϖ i₀ r c m (g.val * C) H (Q₀ * N) hHi₀ hc (by omega)
    hHCint hQint hHCQ' hrow
  obtain ⟨s, hs⟩ := omA_boxFn hg ν β ϖ C m
  have hΦ := boxFn_mem_SB ϖ C (fun _ => m)
  have h1 : omA ν β g 1 (boxFn ϖ C (fun _ => m)) ∈ lowRank (r + 1) ⊔ twistSpan ν β := by
    rw [hs]; exact Submodule.smul_mem _ _ hmem
  have h2 : omA ν β g 1 (boxFn ϖ C (fun _ => m)) - boxFn ϖ C (fun _ => m) ∈ lowRank (r + 1) ⊔ twistSpan ν β :=
    Submodule.mem_sup_right (sub_mem_twistSpan ν β g hΦ)
  simpa using sub_mem h1 h2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LoweringPartKillsFockProductMinors
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowKillDelta

open GlobalTheory.FockIndep GlobalTheory.OrientedHeis GlobalTheory.FockKill
open scoped Real Classical

section Model

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {θ : InfFam D} {τ : D.what₂.Tau}
  {Sp : D.what₂.Tau → SPar} {M : DSModel T Sp}

theorem exists_coef_any {BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    (hB : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) {p : ℕ} {BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hBT : IsONBasis (gramAt D T τ) (cart M τ) (BT τ) p)
    {X : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (lX : X ∈ lieAt T τ) (lY : Complex.I • (cart M τ * X) ∈ lieAt T τ) (ha : cart M τ * X = -(X * cart M τ)) :
    ∃ ν : Fin T.rank → Fin T.rank → ℂ, (∀ a b : Fin T.rank, ¬ (p ≤ (a : ℕ) ∧ (b : ℕ) < p) → ν a b = 0) ∧
      ∀ a c b d, ∀ u, u = unitMap (BS τ) (BT τ) a c → ∀ u', u' = unitMap (BS τ) (BT τ) b d →
        ((omDir S T τ (X * u) τ u' : ℝ) + Complex.I * (omDir S T τ (cplxO 1 (cart M τ) (X * u)) τ u' : ℝ)) +
          (-Complex.I) * ((omDir S T τ (X * cplxO 1 (cart M τ) u) τ u' : ℝ) +
            Complex.I * (omDir S T τ (cplxO 1 (cart M τ) (X * cplxO 1 (cart M τ) u)) τ u' : ℝ)) =
        (if c = d then ν a b else 0) + (if d = c then ν b a else 0) := by
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  obtain ⟨ε, hε, -, ht⟩ := hBT
  let o : Matrix (Fin T.rank) (Fin T.rank) ℂ → Fin T.rank → Fin T.rank → ℝ := fun W a b =>
    2 * (tauE D τ D.host.xi0 * ((BT τ)ᴴ * gramAt D T τ * W * BT τ) a b).re
  have hre := GlobalTheory.RealSymplForm.realPlace_imaginaryGenerator_re_eq_zero D τ
  have osym : ∀ W ∈ lieAt T τ, ∀ a b, o W a b = o W b a := fun W hW a b =>
    congrArg (2 * ·) (skew_entry (GlobalTheory.SmoothAutCheck.gramAt_herm T τ) hW hre a b)
  have ozero : ∀ W, cart M τ * W = -(W * cart M τ) → ∀ a b : Fin T.rank, ((a : ℕ) < p ↔ (b : ℕ) < p) →
      o W a b = 0 := fun W hW a b hab => by
    simp only [o]
    rw [zero_entry (hT τ) ht hW, mul_zero, Complex.zero_re, mul_zero]
    rcases hε a with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hε b with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> simp only [h1, h3]
    · norm_num
    · exact absurd (hab.1 h2) (by omega)
    · exact absurd (hab.2 h4) (by omega)
    · norm_num
  have hom1 : ∀ W a c b d, omDir S T τ (W * unitMap (BS τ) (BT τ) a c) τ (unitMap (BS τ) (BT τ) b d) =
      if c = d then o W b a else 0 := fun W a c b d => by
    rw [omDir, if_pos rfl, trace_unitMap (hB τ)]
    split_ifs <;> simp [o]
  have hJ : ∀ (W : Matrix (Fin T.rank) (Fin T.rank) ℂ) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ),
      cplxO 1 (cart M τ) (W * u) = Complex.I • (cart M τ * W) * u := fun W u => by
    rw [cplxO, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc]
  have hJ' : ∀ u : Matrix (Fin T.rank) (Fin S.rank) ℂ,
      X * cplxO 1 (cart M τ) u = (-(Complex.I • (cart M τ * X))) * u := fun u => by
    rw [cplxO, Matrix.mul_one, ha, smul_neg, neg_neg, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have hJ'' : Complex.I • (cart M τ * -(Complex.I • (cart M τ * X))) = X := by
    rw [Matrix.mul_neg, Matrix.mul_smul, ← Matrix.mul_assoc, (hT τ).1, Matrix.one_mul, smul_neg, smul_smul,
      Complex.I_mul_I, neg_smul, neg_neg, one_smul]
  have oneg : ∀ W a b, o (-W) a b = -o W a b := fun W a b => by
    simp only [o, Matrix.neg_mul, Matrix.neg_apply, mul_neg, Complex.neg_re]
  clear_value o
  refine ⟨fun a b => if p ≤ (a : ℕ) ∧ (b : ℕ) < p then
    2 * (o X a b + Complex.I * o (Complex.I • (cart M τ * X)) a b) else 0, fun a b h => if_neg h, ?_⟩
  rintro a c b d _ rfl _ rfl
  rw [hJ', hJ, hJ, hJ'', hom1, hom1, hom1, oneg]
  by_cases e3 : c = d
  swap
  · simp [e3, Ne.symm e3]
  subst e3
  simp only [if_true]
  have z1 := ozero _ ha
  have z2 := ozero _ (anti_I ha)
  have s1 := osym _ lX a b
  have s2 := osym _ lY a b
  generalize Complex.I • (cart M τ * X) = Y at z2 s2
  rw [s1, s2]
  have e : (o X b a : ℂ) + Complex.I * o Y b a + -Complex.I * ((-o Y b a : ℝ) + Complex.I * o X b a) =
      2 * (o X b a + Complex.I * o Y b a) := by
    push_cast
    linear_combination (-o X b a : ℂ) * Complex.I_mul_I

  rw [e]
  by_cases ha' : (a : ℕ) < p <;> by_cases hb' : (b : ℕ) < p
  · simp [z1 b a (by simp [ha', hb']), z2 b a (by simp [ha', hb'])]
  · rw [if_neg (by omega), if_pos (by omega), zero_add]
  · rw [if_pos (by omega), if_neg (by omega), add_zero]
  · simp [z1 b a (by simp [ha', hb']), z2 b a (by simp [ha', hb'])]

theorem gen_kill_any (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    (hB : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) {p : ℕ} {BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hBT : IsONBasis (gramAt D T τ) (cart M τ) (BT τ) p)
    {X : Matrix (Fin T.rank) (Fin T.rank) ℂ} {GX GY : Module.End ℂ (WO S T → ℂ)}
    (hX : IsGen ψ om θ τ X GX) (hY : IsGen ψ om θ τ (Complex.I • (cart M τ * X)) GY)
    (lX : X ∈ lieAt T τ) (lY : Complex.I • (cart M τ * X) ∈ lieAt T τ) (ha : cart M τ * X = -(X * cart M τ))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f)
    (h0 : (GX + Complex.I • GY) f = 0) {P : MvPolynomial (FVar D T.rank S.rank) ℂ}
    (hP : ∀ a b : Fin T.rank, p ≤ (a : ℕ) → (b : ℕ) < p →
      ∑ c : Fin S.rank, MvPolynomial.pderiv (τ, a, c) (MvPolynomial.pderiv (τ, b, c) P) = 0) :
    (GX + Complex.I • GY) (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (BT) f P) = 0 := by
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hS := fun τ => isCartanInv_one (hB τ)
  obtain ⟨ν, n0, hν⟩ := exists_coef_any hB hBT lX lY ha
  unfold pureTensorO aPlusAll
  refine (quad_pure (P := IsThetaFunO ψ S T) (G := GX + Complex.I • GY)
    (B := fun k g => ((fockScale D k.1 : ℂ)⁻¹ * (if k.1 = τ then (1 : ℂ) else 0)) •
      (annih (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) (X * unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g +
        (-Complex.I) • annih (heisO ψ S T) θ τ (cplxO 1 (cart M τ))
          (X * cplxO 1 (cart M k.1) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2)) g))
    (μ := fun i j => if i.1 = τ then if j.1 = τ then if i.2.2 = j.2.2 then
      ((fockScale D τ : ℂ)⁻¹ * (fockScale D τ : ℂ)⁻¹ * (-(4 * π * Complex.I))) * ν i.2.1 j.2.1 else 0 else 0 else 0)
    (fun _ _ => theta_add) (fun a _ => theta_smul a) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf ?_ h0 P).trans ?_
  · exact fun _ _ h => aPlus_theta hψ hθ _ _ _ h
  · exact fun i j _ h => aPlus_comm' (sS := fun _ => 1) hψ hθ i.1 _ hS hT j.1 _ h
  · exact fun _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h'
  · exact fun _ a _ h => aPlus_smul hψ hθ _ _ _ a h
  · intro i g g' hg hg'
    rw [annih_add hψ hθ _ _ _ hg hg', annih_add hψ hθ _ _ _ hg hg']
    simp only [smul_add]
    abel
  · intro i a g hg
    rw [annih_smul hψ hθ _ _ _ _ hg, annih_smul hψ hθ _ _ _ _ hg, smul_comm _ a, ← smul_add, smul_comm _ a]
  · rintro ⟨τ₁, a, c⟩ ⟨τ₂, b, d⟩ g hg
    have ta := fun z => annih_theta hψ hθ τ (cplxO 1 (cart M τ)) z hg
    have aa := fun z => annih_aPlus (sS := fun _ => 1) hψ hθ τ z hS hT τ₂ (unitMap (BS τ₂) (BT τ₂) b d) hg
    dsimp only at aa ⊢
    rw [aa, aa, aPlus_smul hψ hθ _ _ _ _ (theta_add (ta _) (theta_smul _ (ta _))),
      aPlus_add hψ hθ _ _ _ (ta _) (theta_smul _ (ta _)), aPlus_smul hψ hθ _ _ _ _ (ta _), smul_add (-Complex.I),
      add_add_add_comm, smul_add, smul_smul, ← add_smul, smul_smul]
    refine congrArg₂ (· + ·) rfl (congrArg (· • g) ?_)
    by_cases e1 : τ₁ = τ
    swap
    · simp only [if_neg e1, ite_self, mul_zero, zero_mul, add_zero]
    by_cases e2 : τ₂ = τ
    swap
    · simp [e2, omDir, Ne.symm e2]
    subst e1
    subst e2
    have := hν a c b d _ rfl _ rfl
    simp only [if_true]
    by_cases e3 : c = d
    · simp only [if_pos e3, if_pos e3.symm] at this ⊢
      linear_combination ((fockScale D τ₂ : ℂ)⁻¹ * (fockScale D τ₂ : ℂ)⁻¹ * (-(4 * π * Complex.I))) * this
    · simp only [if_neg e3, if_neg (Ne.symm e3)] at this ⊢
      linear_combination ((fockScale D τ₂ : ℂ)⁻¹ * (fockScale D τ₂ : ℂ)⁻¹ * (-(4 * π * Complex.I))) * this
  · exact fun i _ h => gen_aPlus hψ hθ hX hY _ _ _ h
  · intro i
    rw [hv, hv, smul_zero, add_zero, smul_zero]
  · refine (congrArg _ ?_).trans (map_zero _)
    simp only [Fintype.sum_prod_type, ite_smul, zero_smul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.smul_sum]
    by_cases hab : p ≤ (a : ℕ) ∧ (b : ℕ) < p
    · rw [hP a b hab.1 hab.2, smul_zero]
    · rw [n0 a b hab, mul_zero, zero_smul]

end Model

theorem rderC_theta_eq_zero_any : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → S.SigOK → T.SigOK → ∀ (BS : D.what₂.Tau → Mt S.rank), (∀ τ, IsONBasis (gramAt D S τ) 1 (BS τ) S.rank) → ∀ (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp) (p : D.what₂.Tau → ℕ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsONBasis (gramAt D T τ) (cart M τ) (BT τ) (p τ)) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f) → ∀ (P : PolF D T.rank S.rank) τ, (∀ a b : Fin T.rank, p τ ≤ (a : ℕ) → (b : ℕ) < p τ → ∑ c : Fin S.rank, MvPolynomial.pderiv (τ, a, c) (MvPolynomial.pderiv (τ, b, c) P) = 0) → ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ h, RderC θ T τ Z (fun g => thetaKO om h g (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS BT f P)) = 0 := by
  intro D ψ S T χS χT om hom θ hθ kS kT BS hBS Sp M p BT hBT f hf hv P τ hP Z hZ h
  have hψ := hom.std
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hB : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1 := fun τ => by
    obtain ⟨ε, h1, h2, -⟩ := hBS τ
    rw [h2, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases h1 a with h | h
    · rw [h.1, Complex.ofReal_one]
    · exact absurd a.2 (not_lt.2 h.2)
  have hS := fun τ => isCartanInv_one (hB τ)
  obtain ⟨h1, h2⟩ := pMinus_laws hZ
  obtain ⟨ha, eY⟩ := parts (GlobalTheory.SmoothAutCheck.gramAt_unit T τ) (hT τ) h1 h2
  obtain ⟨lX, lY⟩ := GlobalTheory.SmoothAutCheck.parts_mem T τ Z
  unfold RderC
  unfold conjAt at lX lY ⊢
  rw [eY] at lY ⊢
  generalize (1 / 2 : ℂ) • (Z + -((gramAt D T τ)⁻¹ * Zᴴ * gramAt D T τ)) = X at ha lX lY
  obtain ⟨GX, hX⟩ : ∃ G, IsGen ψ om θ τ X G := GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ S T χS χT om hom θ hθ τ _ lX
  obtain ⟨GY, hY⟩ : ∃ G, IsGen ψ om θ τ (Complex.I • (cart M τ * X)) G :=
    GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ S T χS χT om hom θ hθ τ _ lY
  have hφ : IsThetaFunO ψ S T (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS BT f P) :=
    pure_mem (P := IsThetaFunO ψ S T) (fun _ _ => theta_add) (fun a _ => theta_smul a)
      (fun _ _ h => aPlus_theta hψ hθ _ _ _ h) hf _
  have key := gen_kill_any hψ hθ hB (hBT τ) hX hY lX lY ha hf (hv τ)
    (gen_kill_vac hom hθ kS kT hS hT hX hY lX lY ha hf hv) hP
  generalize pureTensorO ψ θ S T (fun _ => 1) (cart M) BS BT f P = φ at key hφ
  funext g
  have a1 := ((hX φ hφ).2.2.2 (h, g) 0).deriv
  have a2 := ((hY φ hφ).2.2.2 (h, g) 0).deriv
  simp only [Prod.mk_mul_mk, mul_one] at a1 a2
  have a3 := congrFun (congrArg (om (h, g)) key) 0
  rw [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, map_zero] at a3
  simp only [Pi.add_apply, Pi.smul_apply, Rder, thetaKO]
  rw [a1, a2]
  exact a3

theorem rderC_ptAt_delta_eq_zero : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m om BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m om BW f₀ f c io → ∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus (R.MW i σ) τ, ∀ h, RderC R.θ (Wc D i) τ Z (fun g => thetaKO om h g (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ BW f (deltaAtEmb D i σ))) = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m om BW f₀ f c io hL τ Z hZ h
  obtain ⟨hCore, -, -, -, -, hW, hBW, hLV, -⟩ := id hL
  have hf := (GlobalTheory.FinZeta.levVec_vacFin R F i t σ s P cμ cη m om BW f₀ f c io hL).1
  obtain ⟨⟨hψ, hv⟩, e, he, hth⟩ := hLV
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hvac : ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i σ) τ)) f := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hv.inf ho.conj.infPart_eq ho.conj.conj.infPart_eq hth hv.theta hf (hv.fock τ)
  have hpq : ∀ ρ, pW D i ρ + qW D i ρ ≤ (Vc D i).rank := fun ρ =>
    (sig_sum _ (D.sp.W_sig _) (tauE D ρ)).trans_le ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i))
  have hP := GlobalTheory.MinorHarmonic.laplacian_delta D (Wc D i).rank (Vc D i).rank (pW D i) (qW D i) (aPlAt D i σ) (aMiAt D i σ) hpq τ
  exact rderC_theta_eq_zero_any D R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) om hW R.θ hv.inf (D.sp.V_sig _) (D.sp.W_sig _)
    (R.BV i) (hCore.models.BV i) _ (R.MW i σ) (pW D i) BW hBW f hf hvac (deltaAtEmb D i σ) τ hP Z hZ h

end GlobalTheory.LowKillDelta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatVecIff
section
noncomputable section

open NumberField

namespace GlobalTheory.ThetaParseval

def ratVec (F : Type) [Field F] [NumberField F] (κ : Type) : AddSubgroup (κ → AdeleRing (𝓞 F) F) :=
  (AddMonoidHom.compLeft (algebraMap F (AdeleRing (𝓞 F) F)).toAddMonoidHom κ).range

theorem mem_ratVec_iff {F : Type} [Field F] [NumberField F] {κ : Type} (x : κ → AdeleRing (𝓞 F) F) :
    x ∈ ratVec F κ ↔ ∃ ξ : κ → F, x = fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i) := by
  constructor
  · rintro ⟨ξ, rfl⟩
    exact ⟨ξ, rfl⟩
  · rintro ⟨ξ, rfl⟩
    exact ⟨ξ, rfl⟩

end GlobalTheory.ThetaParseval

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsCoefficientFieldChangeStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduliLaws_coefficientFieldChange : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j Xo c' (unfBC hle U) (fun σ => dict (σ.comp (incF c c' hle))) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f : cuspW Xo c U (wtZ a n), ∃ h : rulBC hle (f : Rul Xo c) ∈ cuspW Xo c' (unfBC hle U) (wtZ a n), ∀ σ : c'.F →+* ℂ, normW (unfBC hle U) (xiR D) (fun _ => D.sp.W j) (fun σ => dict (σ.comp (incF c c' hle))) (wtZ a n) σ ⟨_, h⟩ = normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ.comp (incF c c' hle)) f := by
  first | exact @GlobalTheory.LawsFieldChange.laws_fieldChange | exact GlobalTheory.LawsFieldChange.laws_fieldChange | (intros; apply GlobalTheory.LawsFieldChange.laws_fieldChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicFactorFiniteStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monicFactorFinite' : MonicFactorFinite := by
  first | exact @GlobalTheory.LeviHC.monicFactorFinite | exact GlobalTheory.LeviHC.monicFactorFinite | (intros; apply GlobalTheory.LeviHC.monicFactorFinite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonSplitPlaceStabilizerFixesLatticeVacuumStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonSplitPlace_stabilizer_fixes_latticeVacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (H : Geo.Tor.Host D.host.E) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSelfDualC V ΛV → IsSelfDualC W ΛW → ∀ f, IsThetaFunO ψ V W f → IsLatVac (heisO ψ V W) (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) f → ∀ v ε (k : GA D W), GlobalTheory.WeilParts.NonSplitAt D v ε → GlobalTheory.WeilParts.SuppPl ε W k → (∀ u, u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) ↔ actO V W 1 k u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True)) → om (1, k) f = f ∧ (V.rank ≠ 0 → mu k = 1) := by
  first | exact @GlobalTheory.AdTh.nonSplit_fixes_latVac | exact GlobalTheory.AdTh.nonSplit_fixes_latVac | (intros; apply GlobalTheory.AdTh.nonSplit_fixes_latVac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdEndomorphismPowLevelComponentEqOneOfRelationStatement
section
open GlobalTheory.HTLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_endomorphism_pow_levelComponent_eq_one_of_relation : ∀ (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (n : ℕ) (φ : Fin n → (M →* M)) (c : Fin n → ℤ_[l]), ∑ i, c i • Tate.map l (φ i) = 0 → ∀ (N : ℕ) (m : Fin n → ℤ), (∀ i, PadicInt.toZModPow N (c i) = (m i : ZMod (l ^ N))) → ∀ t : Tate l M, ∏ i, φ i (t.lev N) ^ m i = 1 := by
  first | exact @GlobalTheory.TateRel.prod_pow_eq_one | exact GlobalTheory.TateRel.prod_pow_eq_one | (intros; apply GlobalTheory.TateRel.prod_pow_eq_one <;> assumption)
end

