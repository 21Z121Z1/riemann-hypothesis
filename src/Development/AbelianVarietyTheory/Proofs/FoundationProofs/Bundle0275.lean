import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0238
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0221
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0200
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0202
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0268
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0217
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0252
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0265
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryClassRepTrivialAtCm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0266
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwinerSelfDualVacuumIsVacuum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0267

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHeckeEigenfunctionalDepletedEisensteinNeZe
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem zv_unit_of_isCoprime {L : ℕ} {d : ℤ} (h : IsCoprime d (L : ℤ)) : IsUnit (d : ZMod L) := by
  obtain ⟨u, v, huv⟩ := h
  have h1 := congrArg (Int.cast : ℤ → ZMod L) huv
  push_cast at h1
  rw [ZMod.natCast_self, mul_zero, add_zero] at h1
  exact isUnit_iff_exists_inv.mpr ⟨_, (mul_comm _ _).trans h1⟩

theorem zv_apply_ne_zero {L : ℕ} (χ : DirichletCharacter ℂ L) {x : ZMod L} (hx : IsUnit x) : χ x ≠ 0 := by
  obtain ⟨u, rfl⟩ := hx
  intro h
  have h1 : χ ((u : ZMod L) * ((u⁻¹ : (ZMod L)ˣ) : ZMod L)) = 1 := by rw [Units.mul_inv, map_one]
  rw [map_mul, h, zero_mul] at h1
  exact zero_ne_one h1

theorem zv_inv_mul {L : ℕ} (χ : DirichletCharacter ℂ L) {x : ZMod L} (hx : IsUnit x) : χ⁻¹ x * χ x = 1 := by
  rw [MulChar.inv_apply_eq_inv']
  exact inv_mul_cancel₀ (zv_apply_ne_zero χ hx)

theorem zv_ch_changeLevel_mul {N l : ℕ} (cop : N.Coprime l) (A : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l)
    (d : ℤ) : ch (A.changeLevel (dvd_mul_right N l) * ψ.changeLevel (dvd_mul_left l N)) d = ch A d * ch ψ d := by
  unfold ch
  rw [MulChar.mul_apply]
  by_cases hu : IsUnit ((d : ZMod (N * l)))
  · obtain ⟨u, hu⟩ := hu
    rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu,
      ZMod.cast_intCast (dvd_mul_right N l), ZMod.cast_intCast (dvd_mul_left l N)]
  · rw [MulChar.map_nonunit _ hu, zero_mul]
    have hn : ¬ (IsUnit (d : ZMod N) ∧ IsUnit (d : ZMod l)) := by
      rintro ⟨h1, h2⟩
      apply hu
      have : IsUnit (ZMod.chineseRemainder cop (d : ZMod (N * l))) := by
        rw [map_intCast]
        exact Prod.isUnit_iff.mpr ⟨by simpa using h1, by simpa using h2⟩
      exact (isUnit_map_iff (ZMod.chineseRemainder cop) _).mp this
    rcases not_and_or.mp hn with h | h
    · rw [MulChar.map_nonunit _ h, zero_mul]
    · rw [MulChar.map_nonunit _ h, mul_zero]

theorem zv_root {N l : ℕ} (hN : 0 < N) (cop : l.Coprime N) (θ : DirichletCharacter ℂ N) :
    ∃ n : ℕ, 0 < n ∧ (θ (l : ZMod N)) ^ n = 1 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  refine ⟨Fintype.card (ZMod N)ˣ, Fintype.card_pos, ?_⟩
  rw [← ZMod.coe_unitOfCoprime l cop, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]

end GlobalTheory.EisM

namespace GlobalTheory.EisM

theorem eigF_value_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e N : ℕ) (χ θ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ l) (g : ℕ → ℂ) (α β : ℂ), 1 ≤ e → 0 < N → ¬ l ∣ N → Prim (2 * e + 1) N χ g →
    α + β = χ⁻¹ l * g l → α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e) → ‖ι.symm α‖ = 1 → θ (-1) = (-1) ^ e * ψ (-1) →
    θ * χ ≠ 1 → ∃ (B : ℕ) (c : ℕ → ℂ), EigF (2 * e + 1) N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c ∧
      val B c l α 1 (Zs (2 * e + 1) l (ch θ) (hat ⇑(θ * χ)) (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)) ≠ 0 := by
  intro l _ ι e N χ θ ψ g α β he hN hlN hg hsum hprod hα hpar hθχ
  have hp : l.Prime := Fact.out
  have hl0 : 0 < l := hp.pos
  have hNl : 0 < N * l := Nat.mul_pos hN hl0
  have cop : N.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hlN).symm
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_gammaZeroPartitionWeight (N * l) hNl
  have hprod' : α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e + 1 - 1) := by rw [Nat.add_sub_cancel]; exact hprod
  obtain ⟨B, c, hEig, hlam⟩ := GlobalTheory.T.exists_heckeEigenfunctional_of_depletedEigenform (2 * e + 1) N l χ g ρ α β (by omega) hN hp hlN hg hρ hsum hprod'
  refine ⟨B, c, hEig, ?_⟩
  have hχm : χ (-1) = -1 :=
    (GlobalTheory.T.odd_chi_and_tendsto_twisted_LSeries_ne_zero_of_prim (2 * e + 1) N 1 χ 1 g ((((2 * e + 1 : ℕ) : ℝ) + 1) / 2) ⟨e, rfl⟩ hN one_pos hg le_rfl).1

  obtain ⟨φ, hφ⟩ : ∃ φ : DirichletCharacter ℂ (N * l), ∀ d : ℤ, ch φ d = ch (θ * χ) d * ch ψ d :=
    ⟨_, zv_ch_changeLevel_mul cop _ _⟩
  have hφ1 : φ ≠ 1 := by
    intro h1
    apply hθχ
    ext a
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder cop (a : ZMod N).val 1
    haveI : NeZero N := ⟨hN.ne'⟩
    have hkN : ((k : ℕ) : ZMod N) = a := by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hk1, ZMod.natCast_zmod_val]
    have hkl : ((k : ℕ) : ZMod l) = 1 := by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hk2, Nat.cast_one]
    have hk : ch φ ((k : ℕ) : ℤ) = (θ * χ) a := by
      rw [hφ]; unfold ch; push_cast; rw [hkN, hkl, map_one, mul_one]
    rw [h1] at hk
    unfold ch at hk
    rw [MulChar.one_apply_coe]
    by_cases hu : IsUnit ((((k : ℕ) : ℤ)) : ZMod (N * l))
    · rw [MulChar.one_apply hu] at hk; exact hk.symm
    · rw [MulChar.map_nonunit _ hu] at hk; exact absurd hk.symm (zv_apply_ne_zero (θ * χ) a.isUnit)

  have hψ2 : ψ (-1) * ψ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have hφm : ch φ (-1) = (-1) ^ e * ψ (-1) * (-1) * ψ (-1) := by
    rw [hφ]; unfold ch; push_cast; rw [MulChar.mul_apply, hpar, hχm]

  obtain ⟨c₀, hFF⟩ := GlobalTheory.T.eisenstein_periodic_weights_isModularForm e l N (ch ψ) (ch θ) (ch ψ) (ch θ) he hl0 hN
    (by unfold ch; push_cast; exact MulChar.map_zero ψ)
    (fun x => by unfold ch; push_cast; rw [ZMod.natCast_self, add_zero])
    (fun x => by unfold ch; push_cast; rw [ZMod.natCast_self, add_zero])
    (fun d _ => ⟨fun x => by unfold ch; push_cast; rw [map_mul, mul_comm],
      fun x => by unfold ch; push_cast; rw [map_mul, mul_comm]⟩)
    (by unfold ch; push_cast; rw [hpar]; linear_combination (-1 : ℂ) ^ e * hψ2)
  rw [mul_comm l N] at hFF

  have hat0 : hat φ 0 = 0 := ((GlobalTheory.T.dirichletCharFiniteFourierTransform_properties).1 (N * l) φ hNl).2.2 hφ1
  obtain ⟨c₁, hE, hlat⟩ := GlobalTheory.T.eisenstein_latticeFunction_isModularFormCoeffSeq (e + 1) (N * l) 1 (fun _ => 1) (ch φ⁻¹) (fun _ => 1) φ (by omega) hNl one_pos
    hat0 (fun _ => rfl)
    (fun d hd => by
      have hu : IsUnit (d : ZMod (N * l)) := zv_unit_of_isCoprime (by simpa using hd)
      refine ⟨fun y => ?_, fun x => by ring⟩
      unfold ch
      rw [map_mul, ← mul_assoc, mul_comm (φ⁻¹ _), mul_assoc, zv_inv_mul φ hu, mul_one])
    (by
      rw [mul_one]
      unfold ch
      rw [MulChar.inv_apply_eq_inv']
      have := hφm; unfold ch at this; rw [this]
      apply inv_eq_of_mul_eq_one_left
      have hm : ((-1 : ℂ) ^ e) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      linear_combination ((-1 : ℂ) ^ e) ^ 2 * hψ2 + hm)
  rw [mul_one] at hE
  have hE' : MF (e + 1) (N * l) (ch φ⁻¹) (eis (e + 1) c₁ (hat ⇑φ) fun _ => 1) := by
    simpa only [mul_one] using hE

  set FF := eis e c₀ (ch ψ) (ch θ) with hFFdef
  set E := eis (e + 1) c₁ (hat ⇑φ) fun _ => 1 with hEdef
  have hX : MF (2 * e + 1) (N * l) (ch χ⁻¹) (mul FF E) := by
    have h1 := (GlobalTheory.T.modularFormCoeffSeq_mul_and_qExpansion).2 e (e + 1) (N * l) _ _ FF E hFF hE'
    rw [show e + (e + 1) = 2 * e + 1 by ring] at h1
    refine (GlobalTheory.T.modularFormCoeffSeq_linear_structure (2 * e + 1) (N * l) _).2.2.2.1 _ _ (fun d hd => ?_) h1
    have hu : IsUnit (d : ZMod (N * l)) := zv_unit_of_isCoprime hd
    have hd' : IsCoprime d (N : ℤ) := by
      have : IsCoprime d ((N : ℤ) * (l : ℤ)) := by simpa using hd
      exact this.of_mul_right_left
    have hd'' : IsCoprime d (l : ℤ) := by
      have : IsCoprime d ((N : ℤ) * (l : ℤ)) := by simpa using hd
      exact this.of_mul_right_right
    have uN := zv_unit_of_isCoprime hd'
    have ul := zv_unit_of_isCoprime hd''
    have e1 := hφ d
    unfold ch at e1 ⊢
    rw [MulChar.mul_apply] at e1
    rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv', e1]
    have := zv_apply_ne_zero θ uN
    have := zv_apply_ne_zero χ uN
    have := zv_apply_ne_zero ψ ul
    field_simp
  have hqs : qs (mul FF E) = fun τ => qs FF τ * qs E τ := ((GlobalTheory.T.modularFormCoeffSeq_mul_and_qExpansion).1 FF E hFF.1 hE'.1).2
  obtain ⟨κ, hκ, hlat'⟩ : ∃ κ : ℂ, κ ≠ 0 ∧ ∀ τ : ℍ,
      lat (e + 1) 0 (N * l) (0, 1) (latF (N * l) (fun _ => 1) φ) τ = κ * qs E τ :=
    ⟨_, by
      have : ((N * l : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hNl.ne'
      have h2 : (-2 * (π : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h3 : (((e + 1 - 1).factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
      exact div_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (div_ne_zero h2 this))) h3, hlat⟩
  have hpet : ∀ h : ℍ → ℂ, pet (2 * e + 1) ρ h (qs (mul FF E)) =
      κ⁻¹ * pet (2 * e + 1) ρ h (fun τ => qs FF τ * lat (e + 1) 0 (N * l) (0, 1) (latF (N * l) (fun _ => 1) φ) τ) := by
    intro h
    unfold pet
    rw [← integral_const_mul]
    congr 1
    funext τ
    rw [hqs]
    beta_reduce
    rw [hlat' τ]
    field_simp
  obtain ⟨P, hP0, hP1, hP2⟩ := GlobalTheory.T.pet_eis_lat_eq_and_vo_eq_mul e N l χ θ ψ φ g ρ c₀ he hN hp hlN hg hρ hφ hφ1 hFF

  have copl : l.Coprime N := cop.symm
  have hα0 : α ≠ 0 := by
    intro h; rw [h, map_zero, norm_zero] at hα; exact zero_ne_one hα
  have fθ := GlobalTheory.T.heckeRoots_ne_prime_pow_mul_rootOfUnity l ι e N χ g α β (θ l) he hN hlN hg hsum hprod hα (zv_root hN copl θ)
  have fχ := GlobalTheory.T.heckeRoots_ne_prime_pow_mul_rootOfUnity l ι e N χ g α β (χ⁻¹ l) he hN hlN hg hsum hprod hα (zv_root hN copl χ⁻¹)
  have hlamX : lam B c (mul FF E) ≠ 0 := by
    rw [hlam _ hX, hpet, hpet, hP1, hP2]
    intro h0
    have hl : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
    have hκi : κ⁻¹ ≠ 0 := inv_ne_zero hκ
    have h3 : κ⁻¹ * P / (l : ℂ) ^ (2 * e + 1) * ((l : ℂ) * θ l - β) = 0 := by
      rw [← h0]; field_simp; ring
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact div_ne_zero (mul_ne_zero hκi hP0) (pow_ne_zero _ hl) h4
    · exact fθ.2.1 (by linear_combination -h4)
  exact GlobalTheory.T.depletedEisensteinProduct_value_ne_zero_of_rankin e N l χ θ ψ φ (fun q => χ⁻¹ q * g q) α c₀ c₁ B c he hN hp hlN hα0 hEig hpar hχm hθχ hφ hFF hE'
    hlamX fθ.1 (fχ.2.2 e he)

end GlobalTheory.EisM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalComponentUnitaryMatrix
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.LocalComponent

theorem exists_idem_away (D : D7) {q : ℕ} (hq : q.Prime) :
    ∃ f ∈ OhE D, f * f = f ∧ sgA D f = f ∧ (∀ k : ℕ, ∃ w ∈ OhE D, f = (q : AE D) ^ k * w) ∧
      ∀ n : ℕ, n.Coprime q → ∃ w ∈ OhE D, 1 - f = (n : AE D) * w := by
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.IntAdeleComplete.integral_separated_complete D
  obtain ⟨f, hf, hff, ⟨w, hw, hfw⟩, h3⟩ := GlobalTheory.IdealIdele.exists_idem (OhE D) hsep hcpl q hq.pos
  have h2 : ∀ k : ℕ, ∃ w ∈ OhE D, f = (q : AE D) ^ k * w := by
    intro k
    induction k with
    | zero => exact ⟨f, hf, by simp⟩
    | succ k ih =>
      obtain ⟨v, hv, h⟩ := ih
      refine ⟨v * w, mul_mem hv hw, ?_⟩
      calc f = f * f := hff.symm
        _ = ((q : AE D) ^ k * v) * ((q : AE D) * w) := by rw [← h, ← hfw]
        _ = _ := by ring
  have h4 : ∀ n : ℕ, n.Coprime q → ∃ w ∈ OhE D, 1 - f = (n : AE D) * w := fun n hn =>
    h3 n (Nat.pos_of_ne_zero (by rintro rfl; exact hq.ne_one (by simpa using hn))) hn.symm
  refine ⟨f, hf, hff, ?_, h2, h4⟩
  have key : f * (1 - sgA D f) = 0 := by
    refine hsep _ fun N hN => ?_
    obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' q hq.ne_one
    obtain ⟨u, hu, e1⟩ := h2 a
    obtain ⟨v, hv, e2⟩ := h4 n' ((Nat.Prime.coprime_iff_not_dvd hq).2 hn').symm
    have e3 := congrArg (sgA D) e2
    rw [map_sub, map_one, map_mul, map_natCast] at e3
    refine ⟨u * sgA D v, mul_mem hu (VacMove.sgA_mem D hv), ?_⟩
    rw [e3]
    push_cast
    linear_combination ((n' : AE D) * sgA D v) * e1
  have key' := congrArg (sgA D) key
  rw [map_mul, map_sub, map_one, VacMove.sgA_sgA, map_zero] at key'
  linear_combination key' - key

theorem exists_common_denom (D : D7) {q : ℕ} (hq : q.Prime) {n : ℕ} (y : Fin n → AE D) :
    ∃ a m : ℕ, m.Coprime q ∧ ∀ i, (q : AE D) ^ a * (m : AE D) * y i ∈ OhE D := by
  choose N hN hy using fun i => VacMove.exists_nat_denom D (y i)
  have hP : (∏ i, N i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (hN i).ne'
  obtain ⟨a, m, hm, e⟩ := Nat.exists_eq_pow_mul_and_not_dvd hP q hq.ne_one
  refine ⟨a, m, ((Nat.Prime.coprime_iff_not_dvd hq).2 hm).symm, fun i => ?_⟩
  obtain ⟨c, hc⟩ : N i ∣ ∏ i, N i := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have e' : (q : AE D) ^ a * (m : AE D) = (c : AE D) * (N i : AE D) := by
    have := congrArg (Nat.cast : ℕ → AE D) (e.symm.trans hc)
    push_cast at this
    rw [this, mul_comm]
  rw [e', mul_assoc]
  exact mul_mem (natCast_mem _ c) (hy i)

theorem glue_mul {A : Type} [CommRing A] {n : ℕ} {f : A} (hf : f * f = f) {σ τ : Matrix (Fin n) (Fin n) A}
    (h : σ * τ = 1) : ((1 - f) • σ + f • (1 : Matrix (Fin n) (Fin n) A)) * ((1 - f) • τ + f • 1) = 1 := by
  have h1 : (1 - f) * (1 - f) = 1 - f := by linear_combination hf
  have h2 : (1 - f) * f = 0 := by linear_combination -hf
  have h3 : f * (1 - f) = 0 := by linear_combination -hf
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, h, h1, h2, h3, hf, zero_smul,
    Matrix.mul_one, add_zero, zero_add]
  rw [← add_smul, sub_add_cancel, one_smul]

theorem mulVec_inc_smul (D : D7) {n : ℕ} (H : Matrix (Fin n) (Fin n) (AE D)) (c : ℕ) (x : Fin n → D.host.E)
    (i : Fin n) : H.mulVec (fun j => inc D (((c : D.host.E) • x) j)) i =
      (c : AE D) * H.mulVec (fun j => inc D (x j)) i := by
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

set_option maxHeartbeats 1000000 in

theorem exists_local_component : ∀ (D : D7) (n q : ℕ), q.Prime → ∀ s : Matrix (Fin n) (Fin n) D.host.E, s * cT D s = 1 → ∃ g : GA D n, (∀ p : ℕ, p.Prime → p ≠ q → TrivAt D p (g : GL (Fin n) (AE D))) ∧ ∀ (h : GA D n) (B C : Lat D n), Moves D (h : GL (Fin n) (AE D)) B → EqAway D q B C → SAt D q s B C → Moves D ((g * h : GA D n) : GL (Fin n) (AE D)) C := by
  intro D n q hq s hs
  obtain ⟨f, hf, hff, hsg, h2, h3⟩ := exists_idem_away D hq
  have hs' : cT D s * s = 1 := mul_eq_one_comm.1 hs
  have a : s.map (inc D) * (cT D s).map (inc D) = 1 := by
    rw [← Matrix.map_mul, hs, Matrix.map_one _ (map_zero _) (map_one _)]
  have b : (cT D s).map (inc D) * s.map (inc D) = 1 := by
    rw [← Matrix.map_mul, hs', Matrix.map_one _ (map_zero _) (map_one _)]
  let g : GL (Fin n) (AE D) := ⟨_, _, glue_mul hff a, glue_mul hff b⟩
  have hg : g ∈ GA D n := by
    rw [PtsMem.mem_GA]
    have e : ((g : Matrix (Fin n) (Fin n) (AE D)).map (sgA D)).transpose =
        (1 - f) • (cT D s).map (inc D) + f • (1 : Matrix (Fin n) (Fin n) (AE D)) := by
      ext i j
      change sgA D ((1 - f) * inc D (s j i) + f * (1 : Matrix (Fin n) (Fin n) (AE D)) j i) =
        (1 - f) * inc D (D.host.conj (s j i)) + f * (1 : Matrix (Fin n) (Fin n) (AE D)) i j
      rw [map_add, map_mul, map_mul, map_sub, map_one, hsg, PtsMem.sgA_inc]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
    rw [e]
    exact glue_mul hff b
  refine ⟨⟨g, hg⟩, fun p hp hpq i j => ?_, ?_⟩
  · have hz : ZeroAt D p (1 - f) := fun k => by
      obtain ⟨w, hw, e⟩ := h3 (p ^ k) (Nat.Coprime.pow_left k ((Nat.coprime_primes hp hq).2 hpq))
      exact ⟨1, one_pos, by simp, w, hw, by rw [e]; push_cast; ring⟩
    have := VacMove.zeroAt_mul D hp hz (inc D (s i j) - (1 : Matrix (Fin n) (Fin n) (AE D)) i j)
    convert this using 1
    change (1 - f) * inc D (s i j) + f * (1 : Matrix (Fin n) (Fin n) (AE D)) i j - _ = _
    ring
  · rintro h B C hB ⟨k, hBC, hCB⟩ ⟨m, hm, hsB, hsC⟩ x
    set H : Matrix (Fin n) (Fin n) (AE D) :=
      (((h : GL (Fin n) (AE D))⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D)) with hH
    have hB' : ∀ (c : ℕ) (y : Fin n → D.host.E), (c : D.host.E) • y ∈ B ↔
        ∀ i, (c : AE D) * H.mulVec (fun j => inc D (y j)) i ∈ OhE D := fun c y => by
      rw [hB]
      exact forall_congr' fun i => by rw [mulVec_inc_smul]
    have e : ∀ i, ((((((⟨g, hg⟩ : GA D n) * h : GA D n) : GL (Fin n) (AE D))⁻¹ : GL (Fin n) (AE D)) :
        Matrix (Fin n) (Fin n) (AE D)).mulVec (fun j => inc D (x j))) i =
        (1 - f) * H.mulVec (fun j => inc D ((cT D s).mulVec x j)) i + f * H.mulVec (fun j => inc D (x j)) i := by
      intro i
      rw [Subgroup.coe_mul, mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
      change H.mulVec (((1 - f) • (cT D s).map (inc D) + f • (1 : Matrix (Fin n) (Fin n) (AE D))).mulVec _) i = _
      have e1 : ((cT D s).map (inc D)).mulVec (fun j => inc D (x j)) = fun j => inc D ((cT D s).mulVec x j) :=
        funext fun j => (RingHom.map_mulVec (inc D) (cT D s) x j).symm
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, e1, Matrix.mulVec_add,
        Matrix.mulVec_smul, Matrix.mulVec_smul]
      rfl
    simp only [e]
    constructor
    · intro hx i
      obtain ⟨w, hw, e1⟩ := h3 m hm
      obtain ⟨v, hv, e2⟩ := h2 k
      have m1 := (hB' m _).1 (hsC x hx) i
      have m2 := (hB' (q ^ k) x).1 (by simpa using hCB x hx) i
      have := add_mem (mul_mem hw m1) (mul_mem hv m2)
      convert this using 1
      push_cast
      rw [e1]
      linear_combination H.mulVec (fun j => inc D (x j)) i * e2
    · intro hx
      obtain ⟨a1, n1, hn1, d1⟩ := exists_common_denom D hq (H.mulVec (fun j => inc D ((cT D s).mulVec x j)))
      obtain ⟨a2, n2, hn2, d2⟩ := exists_common_denom D hq (H.mulVec (fun j => inc D (x j)))
      have m1 : (n1 : D.host.E) • (cT D s).mulVec x ∈ B := (hB' n1 _).2 fun i => by
        obtain ⟨v, hv, e2⟩ := h2 a1
        have := add_mem (mul_mem (mul_mem (natCast_mem _ n1) (sub_mem (one_mem _) hf)) (hx i)) (mul_mem hv (d1 i))
        convert this using 1
        linear_combination ((n1 : AE D) * H.mulVec (fun j => inc D ((cT D s).mulVec x j)) i) * e2 -
          (n1 : AE D) * (H.mulVec (fun j => inc D ((cT D s).mulVec x j)) i - H.mulVec (fun j => inc D (x j)) i) * hff
      have m2 : ((q ^ a2 : ℕ) : D.host.E) • x ∈ B := (hB' (q ^ a2) _).2 fun i => by
        obtain ⟨w, hw, e1⟩ := h3 n2 hn2
        have := add_mem (mul_mem (mul_mem (pow_mem (natCast_mem _ q) a2) hf) (hx i)) (mul_mem hw (d2 i))
        convert this using 1
        push_cast
        linear_combination ((q : AE D) ^ a2 * H.mulVec (fun j => inc D (x j)) i) * e1 +
          (q : AE D) ^ a2 * (H.mulVec (fun j => inc D ((cT D s).mulVec x j)) i - H.mulVec (fun j => inc D (x j)) i) * hff
      have c1 := hsB _ m1
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hs, Matrix.one_mulVec, smul_smul] at c1
      have c2 := hBC _ m2
      rw [smul_smul] at c2
      have hcop : IsCoprime ((m * n1 : ℕ) : ℤ) ((q ^ (k + a2) : ℕ) : ℤ) :=
        Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right _ (Nat.Coprime.mul_left hm hn1))
      obtain ⟨u, v, huv⟩ := hcop
      have huv' := congrArg (Int.cast : ℤ → D.host.E) huv
      push_cast at huv' c2
      have := add_mem (zsmul_mem c1 u) (zsmul_mem c2 v)
      convert this using 1
      funext j
      simp only [Pi.add_apply, Pi.smul_apply]
      simp only [zsmul_eq_mul, smul_eq_mul]
      linear_combination (-x j) * huv'

end GlobalTheory.LocalComponent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubmoduleStatement
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gkMod_injective_range_eq_of_act_stable : ∀ (p q : ℕ) (M : GKMod p q) (N : Submodule ℂ M.V), (∀ Z, ∀ x ∈ N, M.act Z x ∈ N) → ∃ (M' : GKMod p q) (i : M'.V →ₗ[ℂ] M.V), Function.Injective i ∧ LinearMap.range i = N ∧ ∀ Z x, i (M'.act Z x) = M.act Z (i x) := by
  first | exact @GlobalTheory.GKSubmodule.exists_submodule | exact GlobalTheory.GKSubmodule.exists_submodule | (intros; apply GlobalTheory.GKSubmodule.exists_submodule <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceOneEvenNormUnitAtTwoStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_traceOne_evenNorm_unit_at_two : ∀ (D : D7) (lam : Qbar →+* ℂ_[2]), ∃ (a : 𝓞 D.host.K) (β : ℂ) (k : ℕ), D.host.φ₀ (((a : D.host.K) : D.host.E)) = β ∧ β ∈ Qbar ∧ ‖lamC lam β‖ = 1 ∧ β + starRingEnd ℂ β = 1 ∧ β * starRingEnd ℂ β = ((2 * k : ℕ) : ℂ) ∧ ∀ (Λ : AddSubgroup ℂ) (t₀ : ℂ), GL3Theta.IsTwoTorsionPointUnkilled D Λ t₀ → β * t₀ ∉ Λ ∧ (1 - β) * t₀ ∉ Λ := by
  first | exact @GlobalTheory.EvenTheta.exists_int_trace_one_unit_at_two | exact GlobalTheory.EvenTheta.exists_int_trace_one_unit_at_two | (intros; apply GlobalTheory.EvenTheta.exists_int_trace_one_unit_at_two <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceOneIntegerConjDiffPrimeToStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_traceOne_integer_conj_diff_prime_to : ∀ (D : D7) (q : ℕ), q.Prime → ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧ ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → (q : 𝓞 D.host.E) ∈ P → w - sgO D w ∉ P := by
  first | exact @GlobalTheory.TraceOne.exists_trace_one | exact GlobalTheory.TraceOne.exists_trace_one | (intros; apply GlobalTheory.TraceOne.exists_trace_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsWeierstrassPSeriesStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_isWeierstrassPSeries : ∀ (K : Type) [Field K] [CharZero K] (a b : K), ∃! P : PowerSeries K, IsWpSer a b P := by
  first | exact @GlobalTheory.WpSeries.existsUnique_isWpSer | exact GlobalTheory.WpSeries.existsUnique_isWpSer | (intros; apply GlobalTheory.WpSeries.existsUnique_isWpSer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryClassRepTrivialAtCmStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryClass_rep_trivial_at_cm : ∀ D : D7, oddRep D := by
  first | exact @GlobalTheory.NormSum.exists_rep_trivial_at | exact GlobalTheory.NormSum.exists_rep_trivial_at | (intros; apply GlobalTheory.NormSum.exists_rep_trivial_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeierstrassPSeriesAndSigmaStarQuotientSeriStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weierstrassPSeries_and_sigmaStarQuotientSeries : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∃ P : PowerSeries ℂ, IsWpSer (g2 Λ) (g3 Λ) P ∧ ∀ v, v ∉ Λ → PowerSeries.X ^ 2 * PowerSeries.mk (coef1 (sqTh Λ v)) = PowerSeries.mk (coef1 (sgStar Λ)) ^ 2 * lineSer P (wpF Λ v) := by
  first | exact @GlobalTheory.WpSeries.exists_wpSer | exact GlobalTheory.WpSeries.exists_wpSer | (intros; apply GlobalTheory.WpSeries.exists_wpSer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisSlTwoActionModularFunctionRingOfCongrStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_slTwo_action_modularFunctionRing_of_congr : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : GlobalTheory.FN.ring ε.range) (N w : ℕ), 0 < N → Lv ε.range N w a → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∀ γ γ' : SL(2, ℤ), Cong N d γ γ' → T.gal s (T.sl (ofSL γ) (T.io a)) = T.sl (ofSL γ') (T.gal s (T.io a)) := by
  first | exact @GlobalTheory.FN.gal_sl_io_of_cong | exact GlobalTheory.FN.gal_sl_io_of_cong | (intros; apply GlobalTheory.FN.gal_sl_io_of_cong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumTaylorCoordinateSpaceEntireStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_taylor_coordinateSpace_entire : ∀ (D : D7) (N N' : ℕ) (F : VC D N N' → ℂ), Differentiable ℂ F → ∀ z : VC D N N', HasSum (fun α : Mono D N N' => taylor D F α * mono D α z) (F z) := by
  first | exact @GlobalTheory.EntireTaylor.hasSum_taylor_mono | exact GlobalTheory.EntireTaylor.hasSum_taylor_mono | (intros; apply GlobalTheory.EntireTaylor.hasSum_taylor_mono <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwinerSelfDualVacuumIsVacuumStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwiner_selfDual_vacuum_isVacuum : ∀ (D : D7), Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a d : ℕ) L L' L₁ L₁', SD D L → SD D L' → SD D L₁ → SD D L₁' → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G → ThetaVectorUpToUnits D (tor0 D cc δ) t0 L₁ L₁' (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) L₁ L₁') (G : VC D a d → ℂ)) := by
  first | exact @GlobalTheory.VacuumMove.isVacuum_thetaIntertwiner_selfDual | exact GlobalTheory.VacuumMove.isVacuum_thetaIntertwiner_selfDual | (intros; apply GlobalTheory.VacuumMove.isVacuum_thetaIntertwiner_selfDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IrreducibleOfWeightLineStatement
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_bot_or_eq_of_weight_line_generates : ∀ (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H), Function.Injective E → (∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) → ∀ (S : Ix p q → Ix p q → Prop), Equivalence S → ∀ (μ : Ix p q → ℚ) (v : M.V) (U : Submodule ℂ M.V), v ∈ wtSub M.act μ → (∀ U' : Submodule ℂ M.V, v ∈ U' → (∀ a b, S a b → ∀ x ∈ U', M.act (Eab a b) x ∈ U') → U ≤ U') → (∀ x ∈ U, x ∈ wtSub M.act μ → ∃ c : ℂ, x = c • v) → ∀ N : Submodule ℂ M.V, N ≤ U → (∀ a b, S a b → ∀ x ∈ N, M.act (Eab a b) x ∈ N) → N = ⊥ ∨ N = U := by
  first | exact @GlobalTheory.FockIrr.irreducible_of_weight_line | exact GlobalTheory.FockIrr.irreducible_of_weight_line | (intros; apply GlobalTheory.FockIrr.irreducible_of_weight_line <;> assumption)
end

