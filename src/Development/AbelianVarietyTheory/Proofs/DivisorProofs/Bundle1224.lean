import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1107
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermPairSectionsChangeOfIsometricCombinati
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSNef.ChangePair
open GlobalTheory.VolBr.NuEq
variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem exists_chart (M : HermLB p) (x : X) : ∃ c, x ∈ M.B.U c := by
  have h : x ∈ (⨆ c, M.B.U c) := by rw [M.isLB.cover]; trivial
  exact TopologicalSpace.Opens.mem_iSup.1 h

theorem loc_eq (P : Pair p) (a b a' b' i j : ℤ) (f : X.functionField) (ρ ρ' : X.functionFieldˣ) (e g) :
    f * (ρ : X.functionField) ^ i * (ρ' : X.functionField) ^ j =
      P.loc (i * a + j * a') (i * b + j * b') f e g *
        (((ρ : X.functionField) / P.loc a b 1 e g) ^ i * ((ρ' : X.functionField) / P.loc a' b' 1 e g) ^ j) := by
  have hs : (P.r e : X.functionField) ≠ 0 := (P.r e).ne_zero
  have ht : (P.r' g : X.functionField) ≠ 0 := (P.r' g).ne_zero
  simp only [Pair.loc, one_mul]
  rw [div_zpow, div_zpow, mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul,
    zpow_add₀ hs, zpow_add₀ ht, mul_comm a i, mul_comm b i, mul_comm a' j, mul_comm b' j]
  have h1 := zpow_ne_zero (i * a) hs
  have h2 := zpow_ne_zero (i * b) ht
  have h3 := zpow_ne_zero (j * a') hs
  have h4 := zpow_ne_zero (j * b') ht
  field_simp

end GlobalTheory.HSNef.ChangePair

namespace GlobalTheory.HSNef

open GlobalTheory.VolBr.NuEq ChangePair in

theorem change_pair : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (a b a' b' : ℤ) (M N : HermLB p), P.Rep a b M → P.Rep a' b' N → ∃ Q : Pair p, Q.L = M ∧ Q.A = N ∧ ∀ (i j : ℤ) (R : ℝ), Q.Bl i j R = P.Bl (i * a + j * a') (i * b + j * b') R := by
  intro k _ X _ p P a b a' b' M N ⟨ρ, hρ, hu, hn⟩ ⟨ρ', hρ', hu', hn'⟩
  let Q : Pair p := ⟨M, N, ρ, ρ', hρ, hρ'⟩
  have hw : ∀ (i j : ℤ) (x : X) c d e g, x ∈ M.B.U c → x ∈ N.B.U d → x ∈ P.L.B.U e → x ∈ P.A.B.U g →
      UnitAt x (((ρ c : X.functionField) / P.loc a b 1 e g) ^ i *
        ((ρ' d : X.functionField) / P.loc a' b' 1 e g) ^ j) :=
    fun i j x c d e g hc hd he hg =>
      (NuEq.unitAt_zpow (hu x c e g hc he hg) i).mul (NuEq.unitAt_zpow (hu' x d e g hd he hg) j)
  have hH : ∀ i j : ℤ, Q.H i j = P.H (i * a + j * a') (i * b + j * b') := by
    intro i j
    ext f
    constructor
    · intro hf x e g he hg
      obtain ⟨c, hc⟩ := exists_chart M x
      obtain ⟨d, hd⟩ := exists_chart N x
      have hW := hw i j x c d e g hc hd he hg
      have h := hf x c d hc hd
      change RegAt x (f * _ ^ i * _ ^ j) at h
      rw [loc_eq P a b a' b' i j f (ρ c) (ρ' d) e g] at h
      have h' := h.mul hW.inv.regAt
      rwa [mul_assoc, mul_inv_cancel₀ hW.ne_zero, mul_one] at h'
    · intro hf x c d hc hd
      obtain ⟨e, he⟩ := exists_chart P.L x
      obtain ⟨g, hg⟩ := exists_chart P.A x
      change RegAt x (f * _ ^ i * _ ^ j)
      rw [loc_eq P a b a' b' i j f (ρ c) (ρ' d) e g]
      exact (hf x e g he hg).mul (hw i j x c d e g hc hd he hg).regAt
  have hnu : ∀ (i j : ℤ) (f : X.functionField), f ∈ P.H (i * a + j * a') (i * b + j * b') →
      ∀ (σ : k →+* ℂ) (y : CxPts p σ), Q.nu i j σ y f = P.nu (i * a + j * a') (i * b + j * b') σ y f := by
    intro i j f hf σ y
    have hc := mem_pick (M.φ σ).isLB y
    have hd := mem_pick (N.φ σ).isLB y
    have he := mem_pick (P.L.φ σ).isLB y
    have hg := mem_pick (P.A.φ σ).isLB y
    set c := pick (M.φ σ).isLB y
    set d := pick (N.φ σ).isLB y
    set e := pick (P.L.φ σ).isLB y
    set g := pick (P.A.φ σ).isLB y
    have hfQ : f ∈ Q.H i j := (hH i j).symm ▸ hf
    rw [nu_eq k X p Q i j f hfQ σ y c d hc hd, nu_eq k X p P _ _ f hf σ y e g he hg]
    have hU := hu _ c e g (mem_ptsIn.1 hc) (mem_ptsIn.1 he) (mem_ptsIn.1 hg)
    have hU' := hu' _ d e g (mem_ptsIn.1 hd) (mem_ptsIn.1 he) (mem_ptsIn.1 hg)
    have hreg : RegAt (under y) (P.loc (i * a + j * a') (i * b + j * b') f e g) :=
      hf _ e g (mem_ptsIn.1 he) (mem_ptsIn.1 hg)
    have eU : ‖ratVal ((ρ c : X.functionField) / P.loc a b 1 e g) y‖ =
        Real.exp ((M.φ σ).φ c y / 2 - (a * (P.L.φ σ).φ e y + b * (P.A.φ σ).φ g y) / 2) := by
      rw [← Real.exp_log (norm_pos_iff.2 (ratVal_ne_zero hU))]
      congr 1
      linarith [hn σ y c e g hc he hg]
    have eU' : ‖ratVal ((ρ' d : X.functionField) / P.loc a' b' 1 e g) y‖ =
        Real.exp ((N.φ σ).φ d y / 2 - (a' * (P.L.φ σ).φ e y + b' * (P.A.φ σ).φ g y) / 2) := by
      rw [← Real.exp_log (norm_pos_iff.2 (ratVal_ne_zero hU'))]
      congr 1
      linarith [hn' σ y d e g hd he hg]
    change ‖ratVal (f * _ ^ i * _ ^ j) y‖ * _ = _
    rw [loc_eq P a b a' b' i j f (ρ c) (ρ' d) e g,
      ratVal_mul hreg ((NuEq.unitAt_zpow hU i).mul (NuEq.unitAt_zpow hU' j)).regAt,
      ratVal_mul (NuEq.unitAt_zpow hU i).regAt (NuEq.unitAt_zpow hU' j).regAt,
      ratVal_zpow' hU, ratVal_zpow' hU', norm_mul, norm_mul, norm_zpow, norm_zpow, eU, eU',
      ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.exp_mul, ← Real.exp_mul, mul_assoc,
      ← Real.exp_add, ← Real.exp_add]
    congr 2
    push_cast
    ring
  refine ⟨Q, rfl, rfl, fun i j R => ?_⟩
  ext f
  constructor
  · rintro ⟨hf, hR⟩
    have hf' : f ∈ P.H (i * a + j * a') (i * b + j * b') := hH i j ▸ hf
    exact ⟨hf', fun σ y => hnu i j f hf' σ y ▸ hR σ y⟩
  · rintro ⟨hf, hR⟩
    exact ⟨(hH i j).symm ▸ hf, fun σ y => (hnu i j f hf σ y).symm ▸ hR σ y⟩

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntOfDenLe
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.FinFix

variable {p : ℕ} [Fact p.Prime]

theorem exists_int_of_den_le (D k : ℕ) (hD : 0 < D) (q : ℚ)
    (h1 : ∀ ℓ : ℕ, ℓ ≠ p → q.den.factorization ℓ ≤ D.factorization ℓ) (h2 : q.den.factorization p ≤ k) :
    ∃ m : ℤ, ((D * p ^ k : ℕ) : ℚ) * q = m := by
  have hp : p.Prime := Fact.out
  have hN : 0 < D * p ^ k := Nat.mul_pos hD (pow_pos hp.pos k)
  have hdvd : q.den ∣ D * p ^ k := by
    rw [← Nat.factorization_le_iff_dvd q.den_nz hN.ne']
    intro ℓ
    rw [Nat.factorization_mul hD.ne' (pow_ne_zero _ hp.ne_zero), Nat.factorization_pow, hp.factorization]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.smul_apply, smul_eq_mul]
    by_cases hl : ℓ = p
    · subst hl; simp only [Finsupp.single_eq_same, mul_one]; have := h2; omega
    · have := h1 ℓ hl; omega
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨c * q.num, ?_⟩
  rw [hc]
  calc ((q.den * c : ℕ) : ℚ) * q = (c : ℚ) * (q * q.den) := by push_cast; ring
    _ = _ := by rw [Rat.mul_den_eq_num]; push_cast; ring

theorem grp_val_injective (G : HTGroup p) (β : G.Cˣ) :
    Function.Injective (fun y : grp G β => (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) := by
  intro y y' hyy
  have hu : (y : G.Cˣ × ℚˣ).1 = (y' : G.Cˣ × ℚˣ).1 := Units.ext hyy
  have h1 : (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G ((y : G.Cˣ × ℚˣ).1 : G.Cˣ) =
      algebraMap ℚ G.C (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) * β := y.2.1
  have h2 : (((y' : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G ((y' : G.Cˣ × ℚˣ).1 : G.Cˣ) =
      algebraMap ℚ G.C (((y' : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) * β := y'.2.1
  rw [hu] at h1
  have h3 : algebraMap ℚ G.C (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) = algebraMap ℚ G.C (((y' : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := by
    have := h1.symm.trans h2
    simpa using congrArg (· * ((β⁻¹ : G.Cˣ) : G.C)) this
  have h4 : (y : G.Cˣ × ℚˣ).2 = (y' : G.Cˣ × ℚˣ).2 := Units.ext ((algebraMap ℚ G.C).injective h3)
  exact Subtype.ext (Prod.ext hu h4)

theorem finite_fix_core (G : HTGroup p) (hG : G.a = 1) (v : InfinitePlace G.F)
    (hv : sigPosH (G.gram_herm v) = 1) (L : G.Level) (f : G.GAf → ℂ)
    (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f)
    (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) (hf' : IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f')
    (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (hsym : sh G β = β)
    (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) (h : G.GAf × Gr G 1) (z : Fin G.n → ℂ)
    (hz : 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re) :
    Set.Finite {y : grp G β | FixL G v β y z ∧
      f (h.1⁻¹ * toAfF G β x t hx y * h.1) * f' (h.2⁻¹ * toP1 G β y * h.2) ≠ 0} := by
  obtain ⟨D, hD, hAf⟩ := GlobalTheory.T.formGroup_testFunction_support_bounded_denominators p G β x t hx L f hf h.1
  obtain ⟨k, hP⟩ := GlobalTheory.T.p_adic_denominator_bound p G β K' f' hf' h.2
  obtain ⟨K, hK⟩ := GlobalTheory.T.fixed_vector_squared_bound p G hG v hv β hsym hR z hz
  set N : ℕ := D * p ^ k with hN
  have hNpos : (0 : ℝ) < N := by
    rw [hN]; exact_mod_cast Nat.mul_pos hD (pow_pos (Fact.out : p.Prime).pos k)
  set b := Module.finBasis ℚ G.C with hb
  set S : Finset G.C := Finset.univ.image (fun i => ((N : ℚ)⁻¹) • b i) with hS
  let Φ : G.C →+ (InfinitePlace G.F → Fin G.n → Fin G.n → ℂ) :=
    AddMonoidHom.mk' (fun c w i l => G.psi w c i l) (by intro a c; funext w i l; simp [map_add])
  refine Set.Finite.of_finite_image ?_ ((grp_val_injective G β).injOn)
  refine GlobalTheory.T.finite_of_bounded_image_in_finitely_generated_subgroup Φ (fun k e he => GlobalTheory.T.embeddings_real_independent p G k e he) S _ ?_ (Real.sqrt (max K 0 * N)) ?_
  · rintro _ ⟨y, ⟨-, hne⟩, rfl⟩
    have hf1 := left_ne_zero_of_mul hne
    have hf2 := right_ne_zero_of_mul hne
    show (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∈ AddSubgroup.closure (S : Set G.C)
    rw [← b.sum_repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    obtain ⟨m, hm⟩ := exists_int_of_den_le D k hD (b.repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i)
      (fun ℓ hℓ => (hAf y hf1 ℓ hℓ).1 i) ((hP y hf2).1 i)
    have hN0 : (N : ℚ) ≠ 0 := by
      rw [hN]; exact_mod_cast (Nat.mul_pos hD (pow_pos (Fact.out : p.Prime).pos k)).ne'
    have e : b.repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i • b i = m • ((N : ℚ)⁻¹ • b i) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, ← hm, mul_comm, ← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
    rw [e]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by
      simp only [hS, Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact ⟨i, rfl⟩)) m
  · rintro _ ⟨y, ⟨hfix, hne⟩, rfl⟩
    have hf1 := left_ne_zero_of_mul hne
    have hf2 := right_ne_zero_of_mul hne
    have hs : (0 : ℚ) < (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := y.2.2
    obtain ⟨m, hm⟩ := exists_int_of_den_le D k hD ((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)
      (fun ℓ hℓ => (hAf y hf1 ℓ hℓ).2) (hP y hf2).2
    have hsN : ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) ≤ N := by
      have hm' : ((N : ℚ)) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹ = m := by
        rw [← hm, Units.val_inv_eq_inv_val]
      have hmpos : (0 : ℚ) < m := by
        rw [← hm']; exact mul_pos (by exact_mod_cast hNpos) (inv_pos.2 hs)
      have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast (show (0 : ℤ) < m by exact_mod_cast hmpos)
      have : (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) ≤ N := by
        have h2 : (1 : ℚ) ≤ (N : ℚ) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹ := hm' ▸ hm1
        calc (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) = 1 * (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := (one_mul _).symm
          _ ≤ ((N : ℚ) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹) * (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) :=
            mul_le_mul_of_nonneg_right h2 hs.le
          _ = N := by field_simp
      exact_mod_cast this
    have hsR : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by exact_mod_cast hs
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun w => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
    have h1 := hK y hfix w i j
    have h2 : ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i j‖ ^ 2 ≤ max K 0 * N :=
      h1.trans ((mul_le_mul_of_nonneg_right (le_max_left K 0) hsR.le).trans
        (mul_le_mul_of_nonneg_left hsN (le_max_right K 0)))
    have h3 := Real.abs_le_sqrt h2
    rwa [abs_of_nonneg (norm_nonneg _)] at h3

end GlobalTheory.FinFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitMulZpowUniformiserTmulStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isUnit_mul_zpow_uniformiser_tmul : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra (K ⊗[ℂ] κ') L]
    (E : Place (algebraMap ℂ K)) (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring),
  Function.Injective (algebraMap (K ⊗[ℂ] κ') L) → Irreducible t →
  ∀ g : K, g ≠ 0 → ∃ q : locAt (L := L) 𝔭, IsUnit q ∧
    algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1) = q * (algebraMap (K ⊗[ℂ] κ') L ((t : K) ⊗ₜ 1)) ^ E.ord g := by
  first | exact @GlobalTheory.GraphLocal.exists_isUnit_mul_zpow_tmul | exact GlobalTheory.GraphLocal.exists_isUnit_mul_zpow_tmul | (intros; apply GlobalTheory.GraphLocal.exists_isUnit_mul_zpow_tmul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalEquationEffectiveQCartierDivisorStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localEquation_effectiveQCartierDivisor : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), ∀ (D : X → ℚ), IsQCart D → ∀ x : X, ∃ (m : ℕ) (f : X.functionFieldˣ), 0 < m ∧ RegAt x (f : X.functionField) ∧ ∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord f : ℚ) / m := by
  first | exact @GlobalTheory.PairStep.exists_localEqn_of_isQCart | exact GlobalTheory.PairStep.exists_localEqn_of_isQCart | (intros; apply GlobalTheory.PairStep.exists_localEqn_of_isQCart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalModelAtComplexPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localModel_at_complexPoint : ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.EssFiniteType ℂ A] (ε : A →ₐ[ℂ] ℂ),
  ∃ T : Subring (FractionRing A), IsLocModel (algebraMap ℂ (FractionRing A)) T ∧
    RatRes (algebraMap ℂ (FractionRing A)) T ∧
    ∀ a : A, algebraMap A (FractionRing A) a ∈ T ∧ (ε a = 0 → NonUnit T (algebraMap A (FractionRing A) a)) := by
  first | exact @GlobalTheory.FieldPair.exists_locModel_at_point | exact GlobalTheory.FieldPair.exists_locModel_at_point | (intros; apply GlobalTheory.FieldPair.exists_locModel_at_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogNcardSeminormBallExpSmallLeStatement
section
open Filter Topology GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_log_ncard_seminormBall_exp_small_le : ∀ (G : Type) [AddCommGroup G] (Λ : ℕ → AddSubgroup G) (B : ℕ → ℝ → Set G) (d : ℕ), 0 < d → (∀ m, IsBallFam (Λ m) (B m)) → (∀ m R, (B m R).Finite) → ∀ C : ℝ, (∀ᶠ m : ℕ in atTop, Real.log ((B m (Real.exp (3 * m))).ncard : ℝ) ≤ C * (m : ℝ) ^ d) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ m : ℕ in atTop, Real.log ((B m (Real.exp (δ * m))).ncard : ℝ) ≤ Real.log ((B m 1).ncard : ℝ) + ε * (m : ℝ) ^ d := by
  first | exact @GlobalTheory.VolBr.log_ncard_ball_exp_le | exact GlobalTheory.VolBr.log_ncard_ball_exp_le | (intros; apply GlobalTheory.VolBr.log_ncard_ball_exp_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixCharpolyPreservingHermitianFormCM
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.GlobHerm

theorem vandermonde_diag_herm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ) (hl : Function.Injective l)
    (h1 : ∀ k, ‖l k‖ = 1) (hVA : vandermonde l * A = diagonal l * vandermonde l) :
    A.det ≠ 0 ∧ (Matrix.of fun i j : Fin n => trace (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ))) = (vandermonde l)ᴴ * vandermonde l ∧
      ((vandermonde l)ᴴ * vandermonde l).det ≠ 0 ∧
      Aᴴ * ((vandermonde l)ᴴ * vandermonde l) * A = (vandermonde l)ᴴ * vandermonde l := by
  set V := vandermonde l with hV
  have hl0 : ∀ k, l k ≠ 0 := fun k h => by simpa [h] using h1 k
  have hVd : V.det ≠ 0 := det_vandermonde_ne_zero_iff.2 hl
  have hconj : ∀ k, starRingEnd ℂ (l k) = (l k)⁻¹ := by
    intro k
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h1 k]; simp
  have hAd : A.det ≠ 0 := by
    have := congrArg Matrix.det hVA
    rw [det_mul, det_mul, det_diagonal, mul_comm] at this
    have h2 : A.det = ∏ k, l k := mul_right_cancel₀ hVd this
    rw [h2]; exact Finset.prod_ne_zero_iff.2 fun k _ => hl0 k
  set D' := diagonal fun k => (l k)⁻¹
  have hDD : D' * diagonal l = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext k; exact inv_mul_cancel₀ (hl0 k)
  have hAinv : A * A⁻¹ = 1 := mul_nonsing_inv A (isUnit_iff_ne_zero.2 hAd)
  have hVAi : V * A⁻¹ = D' * V := by
    calc V * A⁻¹ = D' * diagonal l * V * A⁻¹ := by rw [hDD, one_mul]
      _ = D' * (V * A) * A⁻¹ := by rw [hVA, mul_assoc D']
      _ = D' * V := by rw [mul_assoc, mul_assoc, hAinv, mul_one]
  have hpow : ∀ j : ℕ, V * A ^ j = diagonal l ^ j * V := by
    intro j; induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hVA, ← mul_assoc, ← pow_succ]
  have hpowi : ∀ j : ℕ, V * A⁻¹ ^ j = D' ^ j * V := by
    intro j; induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hVAi, ← mul_assoc, ← pow_succ]
  have hVinv : V⁻¹ * V = 1 := nonsing_inv_mul V (isUnit_iff_ne_zero.2 hVd)
  have hVinv' : V * V⁻¹ = 1 := mul_nonsing_inv V (isUnit_iff_ne_zero.2 hVd)
  refine ⟨hAd, ?_, ?_, ?_⟩
  · ext i j
    have hM : V * (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ)) = (D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) * V := by
      rw [← mul_assoc, hpowi, mul_assoc, hpow, ← mul_assoc]
    have htr : trace (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ)) = trace (D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) := by
      calc trace (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ)) = trace (V⁻¹ * (V * (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ)))) := by
            rw [← mul_assoc, hVinv, one_mul]
        _ = trace (V⁻¹ * ((D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) * V)) := by rw [hM]
        _ = trace (D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) := by
            rw [trace_mul_comm, mul_assoc, hVinv', mul_one]
    rw [of_apply, htr, diagonal_pow, diagonal_pow, diagonal_mul_diagonal, trace_diagonal, mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [V, D', vandermonde_apply, conjTranspose_apply, hconj, inv_pow]
  · rw [det_mul, det_conjTranspose]
    exact mul_ne_zero (by simpa using hVd) hVd
  · calc Aᴴ * (Vᴴ * V) * A = (V * A)ᴴ * (V * A) := by
          rw [conjTranspose_mul]; simp only [mul_assoc]
      _ = Vᴴ * ((diagonal l)ᴴ * diagonal l) * V := by
          rw [hVA, conjTranspose_mul]; simp only [mul_assoc]
      _ = Vᴴ * V := by
          rw [diagonal_conjTranspose, diagonal_mul_diagonal]
          have : (diagonal fun k => star (l k) * l k) = 1 := by
            rw [← diagonal_one]; congr 1; funext k
            show starRingEnd ℂ (l k) * l k = 1
            rw [hconj, inv_mul_cancel₀ (hl0 k)]
          simp only [Pi.star_apply] at this ⊢
          rw [this, mul_one]

end GlobalTheory.GlobHerm

namespace GlobalTheory.GlobHerm

theorem exists_mat_herm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    ∃ C H : Matrix (Fin n) (Fin n) E, C.charpoly = P ∧ C.det ≠ 0 ∧ H.det ≠ 0 ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom H = H ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom C * H * C = H := by
  intro E _ _ _ n P hP
  obtain ⟨hmon, hdeg, hsep, hroot⟩ := hP
  subst hdeg
  have hP0 : P ≠ 0 := hmon.ne_zero
  let pb := AdjoinRoot.powerBasis hP0
  let Cm : Matrix (Fin P.natDegree) (Fin P.natDegree) E := Algebra.leftMulMatrix pb.basis pb.gen
  let H : Matrix (Fin P.natDegree) (Fin P.natDegree) E :=
    Matrix.of fun i j => trace (Cm⁻¹ ^ (i : ℕ) * Cm ^ (j : ℕ))
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hτc : ∀ x, τ ((IsCMField.complexConj E).toRingEquiv.toRingHom x) = starRingEnd ℂ (τ x) :=
    fun x => IsCMField.complexEmbedding_complexConj E τ x
  have hQsep : (P.map τ).Separable := hsep.map
  have hQcard : (P.map τ).roots.card = P.natDegree := by
    rw [splits_iff_card_roots.1 (IsAlgClosed.splits _), natDegree_map]
  have hs : (P.map τ).roots.toFinset.card = P.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hQsep), hQcard]
  let e : (P.map τ).roots.toFinset ≃ Fin P.natDegree := Fintype.equivFinOfCardEq (by simp [hs])
  let l : Fin P.natDegree → ℂ := fun k => (e.symm k : ℂ)
  have hl : Function.Injective l := Subtype.val_injective.comp e.symm.injective
  have hlr : ∀ k, eval₂ τ (l k) P = 0 := by
    intro k
    have := (e.symm k).2
    rw [Multiset.mem_toFinset, mem_roots hQsep.ne_zero, IsRoot, eval_map] at this
    exact this
  have h1 : ∀ k, ‖l k‖ = 1 := fun k => hroot τ _ (Multiset.mem_toFinset.1 (e.symm k).2)
  have hrep : ∀ k (x : AdjoinRoot P),
      ∑ i : Fin pb.dim, l k ^ (i : ℕ) * τ (pb.basis.repr x i) = AdjoinRoot.lift τ (l k) (hlr k) x := by
    intro k x
    conv_rhs => rw [← pb.basis.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, PowerBasis.coe_basis]
    simp only [pb, AdjoinRoot.powerBasis_gen, map_pow, AdjoinRoot.lift_root, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.lift_of]
    ring
  have hVA : vandermonde l * Cm.map τ = diagonal l * vandermonde l := by
    ext k j
    rw [mul_apply, diagonal_mul, vandermonde_apply]
    show ∑ i : Fin pb.dim, l k ^ (i : ℕ) * τ (Algebra.leftMulMatrix pb.basis pb.gen i j) = l k * l k ^ (j : ℕ)
    have hC : ∀ i : Fin pb.dim, Algebra.leftMulMatrix pb.basis pb.gen i j = pb.basis.repr (pb.gen * pb.basis j) i :=
      fun i => Algebra.leftMulMatrix_eq_repr_mul _ _ _ _
    rw [Finset.sum_congr rfl fun i _ => by rw [hC i], hrep k]
    simp only [pb, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen]
    rw [← pow_succ', map_pow, AdjoinRoot.lift_root, pow_succ']
  obtain ⟨hAd, hH, hHd, hpres⟩ := GlobalTheory.GlobHerm.vandermonde_diag_herm (Cm.map τ) l hl h1 hVA
  have hinv : (Cm.map τ)⁻¹ = Cm⁻¹.map τ := by
    apply inv_eq_left_inv
    have hCd : Cm.det ≠ 0 := by
      intro h; apply hAd
      have := RingHom.map_det τ Cm
      rw [h, map_zero] at this
      exact this.symm
    rw [← Matrix.map_mul, nonsing_inv_mul Cm (isUnit_iff_ne_zero.2 hCd), Matrix.map_one _ (map_zero τ) (map_one τ)]
  have hHm : H.map τ = (vandermonde l)ᴴ * vandermonde l := by
    rw [← hH]
    ext i j
    simp only [map_apply, of_apply, H]
    rw [AddMonoidHom.map_trace τ, hinv]
    congr 1
    change τ.mapMatrix _ = _
    rw [map_mul, map_pow, map_pow]
    rfl
  have hinj : Function.Injective (fun M : Matrix (Fin P.natDegree) (Fin P.natDegree) E => M.map τ) :=
    Matrix.map_injective τ.injective
  have hcT : ∀ M : Matrix (Fin P.natDegree) (Fin P.natDegree) E,
      (cT (IsCMField.complexConj E).toRingEquiv.toRingHom M).map τ = (M.map τ)ᴴ := by
    intro M; ext i j
    simp only [cT, map_apply, transpose_apply, conjTranspose_apply, hτc]
    rfl
  refine ⟨Cm, H, ?_, ?_, ?_, ?_, ?_⟩
  · refine (charpoly_leftMulMatrix pb).trans ?_
    rw [AdjoinRoot.powerBasis_gen, AdjoinRoot.minpoly_root hP0, hmon.leadingCoeff, inv_one,
      Polynomial.C_1, mul_one]
  · intro h; apply hAd
    have := RingHom.map_det τ Cm
    rw [h, map_zero] at this
    exact this.symm
  · intro h; apply hHd
    have := RingHom.map_det τ H
    rw [h, map_zero] at this
    rw [← hHm]; exact this.symm
  · apply hinj
    simp only
    rw [hcT, hHm, conjTranspose_mul, conjTranspose_conjTranspose]
  · apply hinj
    simp only
    rw [Matrix.map_mul, Matrix.map_mul, hcT, hHm, hpres]
end GlobalTheory.GlobHerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOfClassOfFixedUnitsEq
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.UnitLemma.InvAlg.ClRel

theorem eq_of_mk_eq : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (x y : {x : B.Aˣ // B.σ (x : B.A) = x}), (Quot.mk _ x : B.Cl) = Quot.mk _ y → ∃ a : B.Aˣ, (y.1 : B.A) = x.1 * (a * B.σ a) := by
  intro K B x y h
  have hsu : ∀ u : B.Aˣ, B.σ (u : B.A) * B.σ ((u⁻¹ : B.Aˣ) : B.A) = 1 := fun u => by
    rw [← map_mul, Units.mul_inv, map_one]
  have heq : Equivalence (fun x y : {x : B.Aˣ // B.σ (x : B.A) = x} =>
      ∃ u : B.Aˣ, (y.1 : B.A) = x.1 * (u * B.σ (u : B.A))) := by
    refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨u, hu⟩
      refine ⟨u⁻¹, ?_⟩
      rw [hu]
      calc (x.1 : B.A) = (x.1 : B.A) * (((u : B.A) * ((u⁻¹ : B.Aˣ) : B.A)) *
            (B.σ (u : B.A) * B.σ ((u⁻¹ : B.Aˣ) : B.A))) := by rw [hsu, Units.mul_inv, one_mul, mul_one]
        _ = _ := by ring
    · rintro x y z ⟨u, hu⟩ ⟨v, hv⟩
      refine ⟨u * v, ?_⟩
      rw [hv, hu, Units.val_mul, map_mul]
      ring
  exact (heq.eqvGen_iff).mp (Quot.eqvGen_exact h)

end GlobalTheory.UnitLemma.InvAlg.ClRel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareMatrixImageSubmoduleContainsUniformiStatement
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_square_matrix_image_submodule_contains_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (ϖ : O) (N : Submodule O (Fin n → O)), ϖ ≠ 0 → (∀ y : Fin n → O, (fun a => ϖ * y a) ∈ N) → ∃ A : Matrix (Fin n) (Fin n) O, (∀ x, x ∈ N ↔ ∃ u, A *ᵥ u = x) ∧ A.det ≠ 0 := by
  first | exact @GlobalTheory.exists_square_matrix_of_submodule_between | exact GlobalTheory.exists_square_matrix_of_submodule_between | (intros; apply GlobalTheory.exists_square_matrix_of_submodule_between <;> assumption)
end

