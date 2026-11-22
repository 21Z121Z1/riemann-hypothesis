import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ClassSumNb
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DecayOfVanishingAtCusps
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeckeRelationAdmissibleFamilyPointwise
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHEqThSDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0019
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0016
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableEisMajorant
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHSiegelOperator

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ClassSumNbStatement
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSum_sum_nb_eq_of_moves_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n M q : ℕ) (P : Ideal (𝓞 E)), 0 < M → GoodPrime M q P → ∀ f : Lt E n → ℂ, (∀ h ∈ DH E n M, ∀ Λ ∈ Vset E n M, ∀ Λ' ∈ Vset E n M, Moves h Λ Λ' → f Λ' = f Λ) → ((q : ℂ) - 1) * classSum M (fun Λ => ∑ᶠ Λ' ∈ Nb M P Λ, f Λ') = ((q : ℂ) ^ n - 1) * classSum M f := by
  first | exact @GlobalTheory.SW.classSum_nb | exact GlobalTheory.SW.classSum_nb | (intros; apply GlobalTheory.SW.classSum_nb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DecayOfVanishingAtCuspsStatement
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decay_of_vanishing_at_cusps' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (N R : ℕ) (δ s : ℝ), 0 < N → 0 < R → 0 < δ → 0 ≤ s → ∃ C : ℝ, ∀ (f : CM Ψ N N → ℂ) (B : ℝ), DifferentiableOn ℂ (fun Z : CF Ψ N N => f Z) {Z | (Z : CM Ψ N N) ∈ Hn Ψ N} → (∀ y : Matrix (Fin N) (Fin N) E, IntM y → ccT y = y → ∀ Z ∈ Hn Ψ N, f (fun τ => Z τ + ((R : E) • y).map τ.1) = f Z) → (∀ Z ∈ HnGe Ψ N (δ / 4), ‖f Z‖ ≤ B) → (∀ v : Fin N → E, v ≠ 0 → ∀ Z ∈ Hn Ψ N, Tendsto (fun t : ℝ => f (pushZ Ψ Z v t)) atTop (𝓝 0)) → ∀ Z ∈ HnGe Ψ N δ, ‖f Z‖ * detIm Z ^ s ≤ C * B := by
  first | exact @GlobalTheory.SW.decay_of_vanishing_at_cusps | exact GlobalTheory.SW.decay_of_vanishing_at_cusps | (intros; apply GlobalTheory.SW.decay_of_vanishing_at_cusps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeckeRelationAdmissibleFamilyPointwiseStatement
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_relation_admissibleFamily_pointwise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (M R q : ℕ) (P : Ideal (𝓞 E)) (φ : Fam E n N) (𝔛 : Lt E N), admitted M R φ → 𝔛.FG → Agree (R * M) 𝔛 (stdL E N) → GoodPrime (R * M) q P → ∃ (A : ℕ) (XA XB : Fin A → Lt E N) (β : Fin A → Fin (q ^ N) → Matrix (Fin N) (Fin N) E), A * (q - 1) = q ^ N - 1 ∧ (∀ i, (XA i).FG ∧ Agree (R * M) (XA i) (stdL E N) ∧ gidx (XA i) = q * gidx 𝔛 ∧ (XB i).FG ∧ Agree (R * M) (XB i) (stdL E N) ∧ q * gidx (XB i) = gidx 𝔛 ∧ ∀ j, ccT (β i j) = β i j) ∧ ∀ Λ ∈ Vset E n M, ∀ x, ((q : ℂ) - 1) * ((q : ℂ) ^ n * ∑ i, twist R (XA i) φ Λ x + ∑ i, ∑ j, chiH Ψ (β i j) x * twist R (XB i) φ Λ x) = ((q : ℂ) - 1) * (q : ℂ) ^ N * (∑ᶠ Λ' ∈ Nb M P Λ, twist R 𝔛 φ Λ' x) + ((q : ℂ) ^ (2 * N) - (q : ℂ) ^ n) * twist R 𝔛 φ Λ x := by
  first | exact @GlobalTheory.SW.hecke_relation_pointwise | exact GlobalTheory.SW.hecke_relation_pointwise | (intros; apply GlobalTheory.SW.hecke_relation_pointwise <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionUnitaryGroupTestFunctions
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW

namespace WeilAct

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}

omit [IsCMField E] in

theorem thH_smul (c : ℂ) (φ : Matrix (Fin n) (Fin N) E → ℂ) (Z : CM Ψ N N) (z z' : CM Ψ n N) :
    thH Ψ (c • φ) Z z z' = c * thH Ψ φ Z z z' := by
  unfold thH
  rw [← tsum_mul_left]
  refine tsum_congr fun x => ?_
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem thH_add (hΨ : IsType Ψ) {φ ψ : Matrix (Fin n) (Fin N) E → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ)
    {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (z z' : CM Ψ n N) :
    thH Ψ (φ + ψ) Z z z' = thH Ψ φ Z z z' + thH Ψ ψ Z z z' := by
  have h1 := ((GlobalTheory.T.hermitianTheta_summable_and_determines_testFn E Ψ hΨ n N φ hφ Z hZ).1 z z').of_norm
  have h2 := ((GlobalTheory.T.hermitianTheta_summable_and_determines_testFn E Ψ hΨ n N ψ hψ Z hZ).1 z z').of_norm
  unfold thH
  rw [← h1.tsum_add h2]
  refine tsum_congr fun x => ?_
  simp only [Pi.add_apply, add_mul]

theorem unique (hΨ : IsType Ψ) {γ : M2 E N} (hγ : γ ∈ UU E N)
    {φ ψ ψ' : Matrix (Fin n) (Fin N) E → ℂ} (hψ : IsSB ψ) (hψ' : IsSB ψ')
    (t : TransH Ψ γ φ ψ) (t' : TransH Ψ γ φ ψ') : ψ = ψ' := by
  have hZ := Base.I_mem_Hn (N := N) Ψ
  set Z : CM Ψ N N := fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ) with hZdef
  obtain ⟨hd, hA, -⟩ := (unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ
  refine (GlobalTheory.T.hermitianTheta_summable_and_determines_testFn E Ψ hΨ n N ψ hψ _ hA).2 ψ' hψ' fun w w' => ?_
  have u1 : ∀ τ, IsUnit (hDen Ψ γ Z τ).det := fun τ => (hd τ).1.isUnit
  have u2 : ∀ τ, IsUnit (hDen' Ψ γ Z τ).det := fun τ => by
    refine Ne.isUnit fun h => (hd τ).1 ?_
    rw [← (hd τ).2.1, h, zero_mul]
  have e1 := t Z hZ (fun τ => Matrix.of fun k => hDen' Ψ γ Z τ *ᵥ w τ k)
    (fun τ => Matrix.of fun k => w' τ k ᵥ* hDen Ψ γ Z τ)
  have e2 := t' Z hZ (fun τ => Matrix.of fun k => hDen' Ψ γ Z τ *ᵥ w τ k)
    (fun τ => Matrix.of fun k => w' τ k ᵥ* hDen Ψ γ Z τ)
  have a1 : (fun τ => Matrix.of fun k => (hDen' Ψ γ Z τ)⁻¹ *ᵥ
      (Matrix.of fun k => hDen' Ψ γ Z τ *ᵥ w τ k) k : CM Ψ n N) = w := by
    funext τ
    ext k i
    change ((hDen' Ψ γ Z τ)⁻¹ *ᵥ (hDen' Ψ γ Z τ *ᵥ w τ k)) i = _
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (u2 τ), Matrix.one_mulVec]
  have a2 : (fun τ => Matrix.of fun k =>
      (Matrix.of fun k => w' τ k ᵥ* hDen Ψ γ Z τ) k ᵥ* (hDen Ψ γ Z τ)⁻¹ : CM Ψ n N) = w' := by
    funext τ
    ext k i
    change ((w' τ k ᵥ* hDen Ψ γ Z τ) ᵥ* (hDen Ψ γ Z τ)⁻¹) i = _
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (u1 τ), Matrix.vecMul_one]
  have e := e1.trans e2.symm
  beta_reduce at e
  rw [a1, a2] at e
  exact e

theorem ip_ofQ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N : ℕ) :
    ∃ d : ℂ, d ≠ 0 ∧ ∀ φ ψ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → IsSB ψ →
      ip (fun m : Matrix (Fin n) (QI E N) ℚ => φ (ofQ m)) (fun m => ψ (ofQ m)) = d * ip φ ψ := by
  obtain ⟨d, hd, h⟩ := GlobalTheory.T.schwartzBruhat_rationalCoords_integral_proportional E n N
  refine ⟨d, by exact_mod_cast hd.ne', fun φ ψ hφ hψ => ?_⟩
  have h1 : IsSB fun x => conj (ψ x) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ ψ ψ hψ hψ).2.2.2.1
  exact h (fun x => φ x * conj (ψ x)) (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ φ _ hφ h1).2.2.1

theorem ip_smul {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] {c : ℂ}
    (hc : ‖c‖ = 1) (φ ψ : Matrix κ ι K → ℂ) : ip (c • φ) (c • ψ) = ip φ ψ := by
  unfold ip
  congr 1
  funext x
  have : c * conj c = 1 := by rw [Complex.mul_conj', hc]; simp
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  linear_combination (φ x * conj (ψ x)) * this

theorem exists_op (hΨ : IsType Ψ) (hn : Even n) {γ : M2 E N} (hγ : γ ∈ UU E N) :
    ∃ W : (Matrix (Fin n) (Fin N) E → ℂ) → Matrix (Fin n) (Fin N) E → ℂ, ∀ φ, IsSB φ →
      IsSB (W φ) ∧ TransH Ψ γ φ (W φ) ∧ ∀ φ', IsSB φ' → ip (W φ) (W φ') = ip φ φ' := by
  obtain ⟨hb, hS, -, hth, hsb⟩ := thH_eq_thS_dictionary E Ψ hΨ n N
  obtain ⟨σ, hσ, c, hc, hdict⟩ := GlobalTheory.T.exists_rational_symplectic_of_unitary_cmField E Ψ hΨ n N γ hγ
  obtain ⟨ω, hω⟩ := GlobalTheory.T.exists_weil_of_symplectic' (Fin n) (QI E N) σ (by simpa using hn) hσ
  obtain ⟨d, hd, hip⟩ := ip_ofQ E n N
  let e := Equiv.ofBijective _ hb
  let V : (Matrix (Fin n) (Fin N) E → ℂ) → Matrix (Fin n) (Fin N) E → ℂ := fun φ x =>
    ω (fun m => φ (ofQ m)) (e.symm x)
  have hV : ∀ φ, (fun m => V φ (ofQ m)) = ω fun m => φ (ofQ m) := fun φ => by
    funext m
    exact congrArg _ (e.symm_apply_apply m)
  have hVsb : ∀ φ, IsSB φ → IsSB (V φ) := fun φ hφ => by
    rw [hsb, hV]
    exact (hω _ ((hsb φ).1 hφ)).1
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  refine ⟨fun φ => (c ^ (n / 2))⁻¹ • V φ, fun φ hφ => ⟨?_, ?_, fun φ' hφ' => ?_⟩⟩
  · exact (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ (hVsb φ hφ) (hVsb φ hφ)).2.1 _
  · intro Z hZ z z'
    obtain ⟨h1, h2, h3⟩ := hdict Z hZ
    obtain ⟨h3, h4⟩ := h3 z z'
    have key := (hω _ ((hsb φ).1 hφ)).2.1 _ (hS Z hZ) (zetaOf Ψ z z')
    rw [thH_smul, hth, hth, hV, ← h1, h3, key, h2, Finset.sum_congr rfl fun k _ => h4 k,
      Fintype.card_fin, mul_pow, ← Finset.prod_pow, hFac, Finset.prod_mul_distrib,
      ← Complex.exp_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
    have hp : ∀ τ : Ψ, ((hDen Ψ γ Z τ).det ^ 2) ^ (n / 2) = (hDen Ψ γ Z τ).det ^ n := fun τ => by
      rw [← pow_mul, Nat.mul_div_cancel' hn.two_dvd]
    simp only [hp]
    have := pow_ne_zero (n / 2) hc0
    rw [← mul_assoc (π * I : ℂ) 2, show (π * I * 2 : ℂ) = 2 * π * I by ring]
    field_simp
  · rw [ip_smul (by simp [hc])]
    refine mul_left_cancel₀ hd ?_
    rw [← hip _ _ (hVsb φ hφ) (hVsb φ' hφ'), ← hip _ _ hφ hφ', hV, hV]
    exact (hω _ ((hsb φ).1 hφ)).2.2 _ ((hsb φ').1 hφ')

theorem weil_spec (hΨ : IsType Ψ) (hn : Even n) {γ : M2 E N} (hγ : γ ∈ UU E N)
    {φ : Matrix (Fin n) (Fin N) E → ℂ} (hφ : IsSB φ) :
    IsSB (weil Ψ γ φ) ∧ TransH Ψ γ φ (weil Ψ γ φ) := by
  obtain ⟨W, hW⟩ := exists_op hΨ hn hγ
  have h : ∃ ψ, IsSB ψ ∧ TransH Ψ γ φ ψ := ⟨W φ, (hW φ hφ).1, (hW φ hφ).2.1⟩
  rw [weil, dif_pos h]
  exact h.choose_spec

end WeilAct

open WeilAct in

theorem weil_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ γ ∈ UU E N, ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → IsSB (weil Ψ γ φ) ∧ TransH Ψ γ φ (weil Ψ γ φ) ∧ (∀ ψ, IsSB ψ → TransH Ψ γ φ ψ → ψ = weil Ψ γ φ) ∧ (∀ ψ, IsSB ψ → ip (weil Ψ γ φ) (weil Ψ γ ψ) = ip φ ψ ∧ weil Ψ γ (φ + ψ) = weil Ψ γ φ + weil Ψ γ ψ) ∧ (∀ c : ℂ, weil Ψ γ (c • φ) = c • weil Ψ γ φ) ∧ (∀ γ' ∈ UU E N, weil Ψ (γ' * γ) φ = weil Ψ γ' (weil Ψ γ φ)) ∧ weil Ψ 1 φ = φ := by
  intro E _ _ _ Ψ hΨ n N hn γ hγ φ hφ
  obtain ⟨s1, t1⟩ := weil_spec hΨ hn hγ hφ
  refine ⟨s1, t1, fun ψ hψ t => unique hΨ hγ hψ s1 t t1, fun ψ hψ => ⟨?_, ?_⟩, fun c => ?_,
    fun γ' hγ' => ?_, ?_⟩
  · obtain ⟨s2, t2⟩ := weil_spec hΨ hn hγ hψ
    obtain ⟨W, hW⟩ := exists_op (n := n) hΨ hn hγ
    rw [unique hΨ hγ s1 (hW φ hφ).1 t1 (hW φ hφ).2.1,
      unique hΨ hγ s2 (hW ψ hψ).1 t2 (hW ψ hψ).2.1]
    exact (hW φ hφ).2.2 ψ hψ
  · obtain ⟨s2, t2⟩ := weil_spec hΨ hn hγ hψ
    obtain ⟨s3, t3⟩ := weil_spec hΨ hn hγ (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ φ ψ hφ hψ).1
    refine unique hΨ hγ s3 (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ s1 s2).1 t3 fun Z hZ z z' => ?_
    rw [thH_add hΨ s1 s2 ((unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ).2.1, thH_add hΨ hφ hψ hZ,
      t1 Z hZ, t2 Z hZ, mul_add]
  · obtain ⟨s3, t3⟩ := weil_spec hΨ hn hγ ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ φ φ hφ hφ).2.1 c)
    refine unique hΨ hγ s3 ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ s1 s1).2.1 c) t3 fun Z hZ z z' => ?_
    rw [thH_smul, thH_smul, t1 Z hZ, mul_left_comm]
  · have hm := (unitary_act_halfSpace E Ψ N γ hγ).1.2.2.2.2 γ' hγ'
    obtain ⟨s2, t2⟩ := weil_spec hΨ hn hγ' s1
    obtain ⟨s3, t3⟩ := weil_spec hΨ hn hm hφ
    exact unique hΨ hm s3 s2 t3 ((transH_comp E Ψ n N γ γ' hγ hγ').2 _ _ _ t1 t2)
  · obtain ⟨s3, t3⟩ := weil_spec hΨ hn Base.one_mem_UU hφ
    exact unique hΨ Base.one_mem_UU s3 hφ t3 (Base.transH_one Ψ φ)

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsHeatThHStatement
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHeat_thH_of_isSB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (φ : Matrix (Fin n) (Fin N) E → ℂ), IsSB φ → IsHeat Ψ (thH Ψ φ) := by
  first | exact @GlobalTheory.SW.isHeat_thH | exact GlobalTheory.SW.isHeat_thH | (intros; apply GlobalTheory.SW.isHeat_thH <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableEisMajorantStatement
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_prod_inv_norm_det_hDen_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), 4 * N < n → ∀ (c : ℕ) (rep : Lag E N → M2 E N), 0 < c → (∀ U, rep U ∈ UU E N ∧ Den c (rep U) ∧ botSpan (rep U) = U.1) → Summable fun U : Lag E N => ∏ τ : Ψ, (‖(hDen Ψ (rep U) (fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ)) τ).det‖ ^ n)⁻¹ := by
  first | exact @GlobalTheory.SW.summable_eis_majorant | exact GlobalTheory.SW.summable_eis_majorant | (intros; apply GlobalTheory.SW.summable_eis_majorant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHSiegelOperatorStatement
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ), IsSB φ → IsSB (dropF φ) ∧ ∀ Z ∈ Hn Ψ (N + 1), dropZ Ψ Z ∈ Hn Ψ N ∧ (∀ t : ℝ, 0 ≤ t → pushZ Ψ Z (Pi.single 0 1) t ∈ Hn Ψ (N + 1)) ∧ ∀ z z' : CM Ψ n (N + 1), Tendsto (fun t : ℝ => thH Ψ φ (pushZ Ψ Z (Pi.single 0 1) t) z z') atTop (𝓝 (thH Ψ (dropF φ) (dropZ Ψ Z) (fun τ => (z τ).submatrix id Fin.succ) (fun τ => (z' τ).submatrix id Fin.succ))) := by
  first | exact @GlobalTheory.SW.thH_siegel_operator | exact GlobalTheory.SW.thH_siegel_operator | (intros; apply GlobalTheory.SW.thH_siegel_operator <;> assumption)
end

