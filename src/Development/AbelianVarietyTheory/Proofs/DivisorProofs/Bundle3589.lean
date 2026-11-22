import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3582
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3584
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefLineBundleNumericalTheoremsProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2106
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3583
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3412
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3585
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3571
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDualRepresentableAffineBaseStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_dual_representable_affine_base : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → HasRep A g (𝟙_ _) := by
  first | exact @GlobalTheory.DualCon.hasRep_affine | exact GlobalTheory.DualCon.hasRep_affine | (intros; apply GlobalTheory.DualCon.hasRep_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDieudonneIntegralityFactorisationStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_dieudonne_integrality_factorisation : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), (∀ n : ℕ, (∀ m, ∃ m', T.map (t.map t' f.hom) m = p ^ n • m') → ∃ f' : A ⟶ B, f = p ^ n • f') ∧ (IsIsogeny f → IsIsog (t.map t' f.hom) ∧ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map (t.map t' f.hom))) = padicValNat p (deg f)) ∧ ∀ (C : AbVar k) (K : PDivGroup p k) (t'' : K.TorsionTower C.X) (g : A ⟶ C) (e : ℕ), IsIsogeny f → deg f = p ^ e → LinearMap.range (T.map (t.map t'' g.hom)) ≤ LinearMap.range (T.map (t.map t' f.hom)) → ∃ u : B ⟶ C, f ≫ u = g := by
  first | (exact @GlobalTheory.Dieu.AbVarDieu.abVar_dieudonne_integral_length_factor) | (exact GlobalTheory.Dieu.AbVarDieu.abVar_dieudonne_integral_length_factor) | (intros; apply GlobalTheory.Dieu.AbVarDieu.abVar_dieudonne_integral_length_factor  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AngehrnSiuCutLowerCentreDimension
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem exists_nat_div_of_nonneg (q : ℚ) (hq : 0 ≤ q) : ∃ a b : ℕ, 0 < b ∧ q = a / b := by
  refine ⟨q.num.toNat, q.den, q.den_pos, ?_⟩
  have h1 : ((q.num.toNat : ℕ) : ℚ) = q.num := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hq)
  rw [h1]
  exact (Rat.num_div_den q).symm

theorem exists_qWeil_eq_comb (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Sp ℂ) (hp : IsProjOver p) (D E : CartierDiv X) (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hD : D.Eff) (hE : E.Eff) (s t : ℚ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    letI := algebraΓOfHom p
    ∃ (F : CartierDiv X) (M : ℕ), 0 < M ∧ F.Eff ∧ s • qWeil D m + t • qWeil E k = qWeil F M ∧
      ∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB F] : ℚ) / M =
        s * ((interNumRed ℂ C ![toLB D] : ℚ) / m) + t * ((interNumRed ℂ C ![toLB E] : ℚ) / k) := by
  letI := algebraΓOfHom p
  obtain ⟨a, b, hb, rfl⟩ := exists_nat_div_of_nonneg s hs
  obtain ⟨a', b', hb', rfl⟩ := exists_nat_div_of_nonneg t ht
  have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
  have hb0' : (b' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hb'.ne'
  refine ⟨(a * b' * k) • D + (a' * b * m) • E, b * b' * m * k,
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hb hb') hm) hk,
    (eff_nsmul_of_qadd hD _).add (eff_nsmul_of_qadd hE _), ?_, ?_⟩
  · funext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, qWeil, CartierDiv.mult_add,
      mult_nsmul_of_qadd]
    push_cast
    field_simp
  · intro C hC
    have e := interNumRed_of_cls_eq_nsmul_add ℂ X p hp (toLB ((a * b' * k) • D + (a' * b * m) • E))
      (toLB D) (toLB E) (isLB_toLB _) (isLB_toLB D) (isLB_toLB E) (a * b' * k) (a' * b * m) C hC
      (by rw [← toPic_apply, ← toPic_apply, ← toPic_apply, map_add, map_nsmul, map_nsmul])
    rw [e]
    push_cast
    field_simp

theorem logCanonicalCut_lowers_centre_dimension : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (r : ℕ) (N₀ : LB X) (hN₀ : N₀.IsLB) (A F : CartierDiv X) (a : ℕ)
      (x z : X) (e : ℕ) (c' : ℝ) (lam μ : ℚ) (m' : ℕ) (D₀ : CartierDiv X),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → 0 < r → IsNef ℂ N₀ →
      IsAmpleLB (toLB A) → 0 < a → toPic F = a • cls N₀ hN₀ →
      IsClosed ({x} : Set X) → z ⤳ x → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e →
      (z = genericPoint X ∨ IsNkltCentre p n (Δ + qWeil D₀ m') z) → 0 < c' →
      c' ^ e < (interNumRed ℂ (Closeds.closure ({z} : Set X)) (fun _ : Fin e => N₀) : ℝ) / (r : ℝ) ^ e →
      0 < m' → D₀.Eff → 0 < μ → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' = lam * interNumRed ℂ C ![N₀] / r - μ * interNumRed ℂ C ![toLB A]) → LcAt p n (Δ + qWeil D₀ m') x →
      ∃ (lam' μ' : ℚ) (m'' : ℕ) (D₁ : CartierDiv X), 0 < m'' ∧ D₁.Eff ∧ 0 < μ' ∧ (lam' : ℝ) < lam + e / c' ∧
        (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₁] : ℚ) / m'' = lam' * interNumRed ℂ C ![N₀] / r - μ' * interNumRed ℂ C ![toLB A]) ∧ LcCut p n (Δ + qWeil D₁ m'') x (e - 1) := by
  intro hPr X _ _ _ p n hp hn
  intro Δ m G r N₀ hN₀ A F a x z e c' lam μ m' D₀ hΔ hklt hm hG hr hNnef hA ha hF hx hzx he hdim
    hcen hc' hv hm' hD₀ hμ hcurve hlc
  letI := algebraΓOfHom p

  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hre : (0 : ℝ) < (r : ℝ) ^ e := pow_pos hr0 e
  have hc'e : (0 : ℝ) < c' ^ e := pow_pos hc' e
  have hIr : c' ^ e * (r : ℝ) ^ e <
      ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℝ) := by
    rwa [lt_div_iff₀ hre] at hv
  have hIpos : (0 : ℝ) <
      ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℝ) :=
    lt_trans (mul_pos hc'e hre) hIr
  have he0 : e ≠ 0 := by omega
  have hee : (0 : ℝ) < (e : ℝ) ^ e := pow_pos (by exact_mod_cast (show 0 < e by omega)) e

  obtain ⟨κ, hκ0, hκc, hκI⟩ : ∃ κ : ℚ, (0 : ℝ) < κ ∧ (κ : ℝ) < e / c' ∧
      (e : ℝ) ^ e * (r : ℝ) ^ e < (κ : ℝ) ^ e *
        ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℝ) := by
    set I : ℝ := ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℝ)
      with hIdef
    have hx0 : 0 ≤ (e : ℝ) ^ e * (r : ℝ) ^ e / I := by positivity
    have hy0 : 0 ≤ ((e : ℝ) ^ e * (r : ℝ) ^ e / I) ^ ((e : ℝ)⁻¹) := Real.rpow_nonneg hx0 _
    have hye : (((e : ℝ) ^ e * (r : ℝ) ^ e / I) ^ ((e : ℝ)⁻¹)) ^ e = (e : ℝ) ^ e * (r : ℝ) ^ e / I :=
      Real.rpow_inv_natCast_pow hx0 he0
    have hyc : ((e : ℝ) ^ e * (r : ℝ) ^ e / I) ^ ((e : ℝ)⁻¹) < e / c' := by
      by_contra hcon
      push_neg at hcon
      have h1 := pow_le_pow_left₀ (by positivity) hcon e
      rw [hye, div_pow, div_le_div_iff₀ hc'e hIpos] at h1
      nlinarith [mul_lt_mul_of_pos_left hIr hee]
    obtain ⟨κ, hyκ, hκc⟩ := exists_rat_btwn hyc
    refine ⟨κ, lt_of_le_of_lt hy0 hyκ, hκc, ?_⟩
    have h2 := pow_lt_pow_left₀ hyκ hy0 he0
    rw [hye, div_lt_iff₀ hIpos] at h2
    exact h2
  have hκq : (0 : ℚ) < κ := by exact_mod_cast hκ0
  have hκIq : (e : ℚ) ^ e * (r : ℚ) ^ e < κ ^ e *
      ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℚ) := by
    exact_mod_cast hκI

  have hrq : (0 : ℚ) < r := by exact_mod_cast hr
  have haq : (0 : ℚ) < a := by exact_mod_cast ha
  obtain ⟨s, hs⟩ := exists_nat_gt (2 * κ / (μ * a * r))
  have hsq : (0 : ℚ) < s := lt_trans (by positivity) hs
  have hs0 : 0 < s := by exact_mod_cast hsq
  set h : ℚ := κ / ((s : ℚ) * a * r) with hhdef
  have hh : 0 < h := by positivity
  have hhμ : h < μ / 2 := by
    rw [hhdef, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hs
    nlinarith

  set A' : CartierDiv X := s • F + A with hA'def
  have hclsA' : cls (toLB A') (isLB_toLB A') = (s * a) • cls N₀ hN₀ + 1 • cls (toLB A) (isLB_toLB A) := by
    rw [← toPic_apply, ← toPic_apply, hA'def, map_add, map_nsmul, hF, one_nsmul, smul_smul]
  have hA'amp : IsAmpleLB (toLB A') := by
    refine isAmpleLB_of_cls_eq_ample_add_nef ℂ X p hp (toLB A) (lbPow N₀ (s * a)) (toLB A') hA
      (hNnef.pow hA (s * a)) (isLB_toLB A') ?_
    rw [cls_lbPow hN₀, hclsA', one_nsmul, add_comm]

  have hmix := mixExp_interNumRed nefNumerics_outright ℂ X p hp N₀ (toLB A) (toLB A') hN₀
    (isLB_toLB A) (isLB_toLB A') (s * a) 1 (Closeds.closure {z}) e hNnef (IsAmpleLB.isNef (k := ℂ) hA)
    hclsA' (by rw [Closeds.coe_closure]; exact hdim)
  have hmixQ : ((s : ℚ) * a) ^ e *
      ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℚ) ≤
      ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => toLB A' : ℤ) : ℚ) := by
    exact_mod_cast hmix
  have hcard : (({x} : Finset X).card : ℚ) * (e : ℚ) ^ e < h ^ e *
      ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => toLB A' : ℤ) : ℚ) := by
    rw [Finset.card_singleton, Nat.cast_one, one_mul]
    have hhs : h * ((s : ℚ) * a) = κ / r := by
      rw [hhdef]; field_simp
    calc (e : ℚ) ^ e < (κ / r) ^ e *
          ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℚ) := by
          rw [div_pow, div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
          exact hκIq
      _ = h ^ e * (((s : ℚ) * a) ^ e *
          ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N₀ : ℤ) : ℚ)) := by
          rw [← mul_assoc, ← mul_pow, hhs]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmixQ (by positivity)

  have hDq : IsQCart (qWeil D₀ m') := ⟨m', D₀, hm', hD₀, rfl⟩
  obtain ⟨B, δ₀, hδ₀, -, hBnum, hOff, hnk, hsep⟩ := GlobalTheory.T.exists_divisor_nonKlt_points_numerically_multiple hPr X p n hp hn Δ m G A'
    (qWeil D₀ m') {x} z e h hΔ hklt hm hG hA'amp hDq
    (fun y hy => by rw [Finset.mem_singleton] at hy; subst hy; exact ⟨hx, hzx⟩) he hdim hcen hh hcard

  obtain ⟨ε, hε0, hεb⟩ := exists_rat_btwn (show (0 : ℝ) < ((e : ℝ) / c' - κ) / (|(lam : ℝ)| + 1) from
    div_pos (by linarith) (by positivity))
  set δ : ℚ := min (min δ₀ (1 / 2)) ε with hδdef
  have hδ0 : 0 < δ := lt_min (lt_min hδ₀ (by norm_num)) (by exact_mod_cast hε0)
  have hδε : δ ≤ ε := min_le_right _ _
  have hδh : δ ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδδ₀ : δ ≤ δ₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := by linarith
  have hδlam : (δ : ℝ) * |(lam : ℝ)| < e / c' - κ := by
    have h1 : (δ : ℝ) ≤ ε := by exact_mod_cast hδε
    have h2 := (lt_div_iff₀ (by positivity : (0 : ℝ) < |(lam : ℝ)| + 1)).1 hεb
    nlinarith [abs_nonneg (lam : ℝ)]

  have hxk : KltAt p n Δ x := hklt x
  have hk1 : KltAt p n (Δ + (1 - δ) • qWeil D₀ m') x :=
    kltAt_add_smul_of_lcAt X p n hp hn Δ (qWeil D₀ m') δ x hDq hxk hlc hδ0 hδ1
  have hnk1 := hnk δ hδ0.le hδδ₀ x (Finset.mem_singleton_self x)
  have hsDq : IsQCart ((1 - δ) • qWeil D₀ m') := by
    obtain ⟨F₁, M₁, hM₁, hF₁, heq, -⟩ := exists_qWeil_eq_comb X p hp D₀ D₀ m' m' hm' hm' hD₀ hD₀
      (1 - δ) 0 (by linarith) le_rfl
    exact ⟨M₁, F₁, hM₁, hF₁, by rw [← heq, zero_smul, add_zero]⟩
  have hBq : IsQCart B := hBnum.isQCart
  obtain ⟨c, hc0, hc1, hlcc, hnkc⟩ := GlobalTheory.T.exists_rational_logCanonicalThreshold_at_point hPr X p n hp hn Δ m G ((1 - δ) • qWeil D₀ m') B x
    hm hG hsDq hBq hk1 hnk1
  have hcut := logCanonicalCut_of_step X p n hp hn Δ (qWeil D₀ m') B δ c x z (e - 1) hxk hDq hBq hlc hδ0 hδ1
    hc1 hOff hsep (by rw [Nat.sub_add_cancel he]; exact hdim) hlcc hnkc

  obtain ⟨m₁, B₀, hm₁, hB₀, rfl, hBn⟩ := hBnum
  obtain ⟨D₂, m'', hm'', hD₂, heq, hnum⟩ := exists_qWeil_eq_comb X p hp D₀ B₀ m' m₁ hm' hm₁ hD₀ hB₀
    (1 - δ) c (by linarith) hc0.le
  refine ⟨(1 - δ) * lam + c * κ, (1 - δ) * μ - c * h, m'', D₂, hm'', hD₂, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · have t1 : -((δ : ℝ) * lam) ≤ δ * |(lam : ℝ)| := by
      rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs _) (by exact_mod_cast hδ0.le)
    have t2 : (c : ℝ) * κ ≤ κ := by
      have : (c : ℝ) ≤ 1 := by exact_mod_cast hc1
      nlinarith
    push_cast
    nlinarith
  · intro C hC
    have eA' := interNumRed_of_cls_eq_nsmul_add ℂ X p hp (toLB A') N₀ (toLB A) (isLB_toLB A') hN₀
      (isLB_toLB A) (s * a) 1 C hC hclsA'
    rw [hnum C hC, hcurve C hC, hBn C hC, eA']
    have hr0' : (r : ℚ) ≠ 0 := hrq.ne'
    have hs0' : (s : ℚ) ≠ 0 := hsq.ne'
    have ha0' : (a : ℚ) ≠ 0 := haq.ne'
    rw [hhdef]
    push_cast
    field_simp
    ring
  · rw [← heq, ← add_assoc]
    exact hcut

end GlobalTheory.PairStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusCycleHeightsOfAnalytic
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem arCalc_cycleHeights_of_analytic :
    ArchInteg → ArchRecip → GlobalTheory.Published.ArCalc ∧ GlobalTheory.Published.CycleHeights := fun hI hR =>
  have h := GlobalTheory.T.arithIntersection_forms_of_archimedean_statements hI hR
  have hC : GlobalTheory.Published.ArCalc := GlobalTheory.Published.arCalc_of_form_mix_projection h.1 h.2.1 h.2.2
  ⟨hC, GlobalTheory.Published.cycleHeights_of_arCalc hC⟩

end GlobalTheory.MixHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseRigidityTangentVectorConstantStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_rigidity_tangent_vector_constant : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k) (a : Fin C.m → k), GlobalTheory.RigChart.IsConstAlong C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ρ a → ρ.comp (Cn.ψ.comp MvPolynomial.C) = GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C)) := by
  first | exact @GlobalTheory.RigBase.const_on_base | exact GlobalTheory.RigBase.const_on_base | (intros; apply GlobalTheory.RigBase.const_on_base <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirationalOnWeightParameters
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp

theorem gap_add_vec {N : ℕ} (v w : Fin N → ℤ) (k : ℕ) : gap (v + w) k = gap v k + gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.add_apply]; ring
  · simp

theorem gaps_u₁_u₂_of_wtBig {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    (P : WtPar Dw) (hB : WtBig P) (τ : Psi H) (a b : Fin (Dw.p + Dw.q)) (hab : (b : ℕ) = a + 1) :
    (((CompHt.dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) : ℕ) : ℤ) ≤ P.u₁ τ a - P.u₁ τ b ∧
    (((CompHt.dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) : ℕ) : ℤ) ≤ P.u₂ τ a - P.u₂ τ b := by
  have hk : (a : ℕ) + 1 < Dw.p + Dw.q := by have := b.2; omega
  have g1 := hB.gaps τ a hk
  have g2 := (P.gap_rem τ a).1
  have e1 : P.u₁ τ a - P.u₁ τ b = gap (P.u₁ τ) a := (gap_eq _ hab).symm
  have e2 : P.u₂ τ a - P.u₂ τ b = gap (P.u₁ τ) a + gap (P.rem τ) a := by
    rw [← gap_eq _ hab]
    exact gap_add_vec (P.u₁ τ) (P.rem τ) a
  have hn : (CompHt.dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) ≤
      (FlagTan.dimFlag Dw + 3) * ((FlagTan.dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + FlagTan.dimFlag Dw + 3) := by
    rw [dimFlag_eq]
    generalize FlagTan.dimFlag Dw = D
    generalize Dw.p + Dw.q = N
    generalize (D + 1).choose 2 = C
    nlinarith [Nat.zero_le (D * C), Nat.zero_le (D * N), Nat.zero_le C]
  have hn' : (((CompHt.dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) : ℕ) : ℤ) ≤
      (((FlagTan.dimFlag Dw + 3) * ((FlagTan.dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + FlagTan.dimFlag Dw + 3) : ℕ) : ℤ) :=
    by exact_mod_cast hn
  rw [e1, e2]
  exact ⟨hn'.trans g1, by linarith⟩

theorem birOn_u₁_u₂ : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → Hypotheses2 → Size → Covers fun Fm x _ ι p i Y PP _ => ∀ Z, BirOn Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ 0) ∧ BirOn Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂ 0) := by
  intro hX hG hQ hSi hP2 hS
  have hP := GlobalTheory.T.stronger_published_hypotheses_imply hP2
  have hBir : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q →
      ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)),
      (∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 →
        (((CompHt.dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b) →
      ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) :=
    GlobalTheory.T.weight_principalisation_bound hX hG hQ hSi hP hP2.q15 hP2.q16
  refine Closed.imp (((GlobalTheory.T.size_bounds_for_family hS).and (GlobalTheory.T.weight_parameter_strict_antitone hS)).and wtBig_run) ?_
  rintro eps Fm CH - ⟨⟨⟨C1, -, H1⟩, ⟨C2, -, H2⟩⟩, ⟨C3, -, H3⟩⟩
  refine ⟨0, le_rfl, ?_⟩
  obtain ⟨x0, H⟩ := (H1.and H2).and H3
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨a1, a2⟩, a3⟩ := H x hx hle ι p hp
  have s1 := a1 i hi Y hY
  have s2 := a2 i hi
  have hB := a3 i hi
  intro Z
  have G := gaps_u₁_u₂_of_wtBig _ hB
  exact ⟨hBir (Fm.D x ι) p.T s1.1 ((i : ℕ) + 1) s2.1 s2.2.1 Y _ _ hY.1 _ (fun τ a b h => (G τ a b h).1) Z,
    hBir (Fm.D x ι) p.T s1.1 ((i : ℕ) + 1) s2.1 s2.2.1 Y _ _ hY.1 _ (fun τ a b h => (G τ a b h).2) Z⟩

end GlobalTheory.HSApp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyHasPointRigidCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalFamily_has_pointRigid_coordinates : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), HasRigidCoords C := by
  first | exact @GlobalTheory.UCanon.canon_hasRigidCoords | exact GlobalTheory.UCanon.canon_hasRigidCoords | (intros; apply GlobalTheory.UCanon.canon_hasRigidCoords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreLiftCommTranslationSectionRatiosStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedFibreLift_comm_translation_section_ratios : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r)))  → ∀ (A₀ : Over (Sp k)) (_ : GrpObj A₀) (m₀ : A₀.left ⟶ P.D.toPre.P.A.left), IsGrpPullback A₀ P.D.toPre.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ dl : ∀ W : P.D.toPre.P.A.left.Opens, Γ(P.D.toPre.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.D.toPre.P.A.hom m₀ (fun r => (ρ r).snd) ⊤ dl → (∀ (Z' : Scheme.{0}) (a : Z' ⟶ Y.H.left) (b : Z' ⟶ A₀.left), a ≫ Y.q.left = b ≫ m₀ → ∀ (i : h.J) (W : P.D.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ W ≤ h.W i → ∀ f, pbT b (dl W f) (b ⁻¹ᵁ (m₀ ⁻¹ᵁ W)) = pbT a (h.d i _ ((Y.q.left.app W).hom f)) (b ⁻¹ᵁ (m₀ ⁻¹ᵁ W))) → ∀ (y : P.D.toPre.X) (T₀ : A₀.left ⟶ A₀.left), T₀ ≫ m₀ = m₀ ≫ (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left → T₀ ≫ A₀.hom = A₀.hom → ∀ (N : ℕ), 1 ≤ N → ∀ (σ σ' : P.D.toPre.SecB N 0) (U : P.D.toPre.P.A.left.Opens) (f : Γ(P.D.toPre.P.A.left, U)), (∀ z ∈ U, ∀ J, Good P.D.toPre.P.L z J → IsUnit (sval σ' (𝟙 _) z J) ∧ sval σ (𝟙 _) z J = gs (𝟙 _) z U f * sval σ' (𝟙 _) z J) → dl ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ U) (((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left.app U).hom f) = pbT T₀ (dl U f) (m₀ ⁻¹ᵁ ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ U)) := by
  first | exact @GlobalTheory.HeatRatioW.dl_comm_transl_ratio | exact GlobalTheory.HeatRatioW.dl_comm_transl_ratio | (intros; apply GlobalTheory.HeatRatioW.dl_comm_transl_ratio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombinedMetrizedBundleNefAntitoneStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.combined_metrized_bundle_nef_antitone : Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∀ (c : O.s.Comp) (Q : Finset ℕ) (l : ℕ), l ∈ Q → l.Prime → ∃ (V : Cover (O.var c)) (M : DV.Rt D.what₂.Tau O.N → HermLB V.p), (∀ x, Norms V (M x) (fun z => genAt (O.root0 c Q x).D z) (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y)) ∧ ∀ n : D.what₂.Tau → Fin O.N → ℤ, (∀ τ, Antitone (n τ)) → NefOver (ArInt.comb M fun x => -n x.1 x.2) l := by
  first | exact @GlobalTheory.HtNefCore.exists_cover_nefOver | exact GlobalTheory.HtNefCore.exists_cover_nefOver | (intros; apply GlobalTheory.HtNefCore.exists_cover_nefOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPolarizationPerfectPairing
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FieldPerf

theorem finrank_of_rankAtStalk {k : Type} [Field k] {M : Type*} [AddCommGroup M] [Module k M]
    [Module.Finite k M] {n : ℕ} (h : ∀ p : PrimeSpectrum k, Module.rankAtStalk M p = n) :
    Module.finrank k M = n := by
  have e := h ⟨⊥, Ideal.isPrime_bot⟩
  rwa [Module.rankAtStalk_eq_finrank_of_free] at e

theorem isPerfPair : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[k] HdR B →ₗ[k] k, AbDual.IsCorrForm (dp0 k) (𝟙 _) A B P φ → φ.IsPerfPair := by
  intro H k _ A B _ _ g hA hB gA gB P hP φ hφ
  obtain ⟨HF, HH, -⟩ := GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange H
  obtain ⟨fA, -, rA⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim HF hA gA
  obtain ⟨fB, -, rB⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim HF hB gB
  obtain ⟨-, -, fFA, -, rFA⟩ := HH k A g hA gA
  obtain ⟨-, -, fFB, -, rFB⟩ := HH k B g hB gB
  exact GlobalTheory.T.isPerfPair_dual_of_half_dim_kernel_conditions k (primDR A) (primDR B) (PrimitiveSubmodule A) (PrimitiveSubmodule B) g
    (finrank_of_rankAtStalk rA) (finrank_of_rankAtStalk rB)
    (finrank_of_rankAtStalk rFA) (finrank_of_rankAtStalk rFB) φ
    (GlobalTheory.T.hodge_filtration_orthogonal_perfect H k A B g hA hB gA gB P hP φ hφ)
    (GlobalTheory.T.mem_hodgeFiltration_of_orthogonal_perfectPairing H k A B g hA hB gA gB P hP φ hφ)

end GlobalTheory.FieldPerf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorStalkEvaluationLinearMapFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_stalk_evaluation_linear_map_family : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → Y1) → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C) (r : X₁.M.Z.presheaf.stalk z₁), X₁.M.stalkHom z₁ r = X₁.S.th (lab c) / X₁.S.th x₀ → ev1 r - T 0 c ∈ maximalIdeal V1 := by
  first | exact @GlobalTheory.Poinc.Sep.UMem.const_term_sub_mem | exact GlobalTheory.Poinc.Sep.UMem.const_term_sub_mem | (intros; apply GlobalTheory.Poinc.Sep.UMem.const_term_sub_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineScalarTorusInvariantHeatOperatorsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_scalar_torusInvariant_heatOperators : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h h' : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → IsBasic Y h' → h.Θ = h'.Θ → h.u = h'.u → ∃ (ℓ : Q.X →+ R) (π π' : R), ∀ (k : ℕ) (α : Q.X) (σ σ' σ'' : Q.SecB k α), TActs Y h k α σ σ' → TActs Y h' k α σ σ'' → ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J → sval σ'' x.left z J = sval σ' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom (2 * (k : R) * ℓ α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π')) * sval σ x.left z J := by
  first | exact @GlobalTheory.HeatUniq.exists_affine_scalar | exact GlobalTheory.HeatUniq.exists_affine_scalar | (intros; apply GlobalTheory.HeatUniq.exists_affine_scalar <;> assumption)
end

