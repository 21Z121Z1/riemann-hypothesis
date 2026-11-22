import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0408
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0397
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0404
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinarySelmerDualVanishesOfStrict
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0017
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaTW
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0022
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedAwayFromLOfTwistedShapiroLimit
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UntwistedRepresentationOrdinaryTriangularShape
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormGaussSumModPrimePowerLeHalfPowerStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_gaussSumModPrimePower_le_half_power : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)), z ^ (l ^ m) = 1 → ‖gSum m z ψ‖ ≤ ‖(l : Qbar l) ^ (m / 2)‖ := by
  first | (exact @GlobalTheory.KZ.Cmp.norm_gSum_le) | (exact GlobalTheory.KZ.Cmp.norm_gSum_le) | (intros; apply GlobalTheory.KZ.Cmp.norm_gSum_le  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormPowSubPowLtOneOfUltra
section
namespace GlobalTheory.PowerDifferenceNorm

theorem norm_pow_sub_pow_lt_one_of_ultra {K : Type*} [NormedCommRing K] [IsUltrametricDist K]
    {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (h : ‖x - y‖ < 1) (n : ℕ) :
    ‖x ^ n - y ^ n‖ < 1 := by
  rcases n with _ | n
  · simp
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have e : x ^ (n + 1 + 1) - y ^ (n + 1 + 1)
        = x * (x ^ (n + 1) - y ^ (n + 1)) + (x - y) * y ^ (n + 1) := by ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt ((norm_mul_le _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _) hx)) ih
    · have hp : ‖y ^ (n + 1)‖ ≤ 1 :=
        (norm_pow_le' y n.succ_pos).trans (pow_le_one₀ (norm_nonneg _) hy)
      exact lt_of_le_of_lt ((norm_mul_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) hp)) h

theorem norm_pow_sub_pow_lt_one :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {x y : Formalism.ConjugateSelfDual.Qbar l}, ‖x‖ ≤ (1 : ℝ) → ‖y‖ ≤ (1 : ℝ) →
      ‖x - y‖ < (1 : ℝ) → ∀ (n : ℕ), ‖x ^ n - y ^ n‖ < (1 : ℝ) := by
  intro l _ x y hx hy h n
  exact norm_pow_sub_pow_lt_one_of_ultra hx hy h n

end GlobalTheory.PowerDifferenceNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinarySelmerDualVanishesOfStrictStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinarySelmer_dual_vanishes_of_strict : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ES W A → StrZero (dual1 W) A → GrZero (dual1 W) A := by
  first | exact @GlobalTheory.Ord2.Upgrade.upgrade | exact GlobalTheory.Ord2.Upgrade.upgrade | (intros; apply GlobalTheory.Ord2.Upgrade.upgrade <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShCocWsumProps
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA
open scoped Matrix MatrixGroups

namespace GlobalTheory.K4

theorem shCoc_wsum_props : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
  (ρ : (Ω ≃ₐ[ℚ] Ω) → Matrix (Fin 2) (Fin 2) (Qbar l)) (cf : Coef l) (ι : Type) [Fintype ι] (cw : ι → Qbar l)
  (Yx : ι → ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
  (∀ i r, ShCoc ρ (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Yx i r)) →
  (∀ i r, Yx i r = push (redL l r) (Yx i (r + 1))) →
  (∀ i r y j, Continuous fun s => Yx i r s y j) →
  (∀ i r s u j, Yx i r s u j ∈ cf.O) → (∀ i, cw i ∈ cf.O) →
  (∀ r, ShCoc ρ (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (fun s y => ∑ i, cw i • Yx i r s y)) ∧
  (∀ r, (fun s y => ∑ i, cw i • Yx i r s y) = push (redL l r) (fun s y => ∑ i, cw i • Yx i (r + 1) s y)) ∧
  (∀ r y j, Continuous fun s => (∑ i, cw i • Yx i r s y) j) ∧
  (∀ r s u j, (∑ i, cw i • Yx i r s u) j ∈ cf.O) := by
  intro l _ Ω _ _ ρ cf ι _ cw Yx hC hP hCont hO hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r s t x
    have := fun i => hC i r s t x
    simp only [this, Finset.sum_add_distrib, smul_add, Matrix.mulVec_sum, Matrix.mulVec_smul]
  · intro r
    funext s y
    simp only [push]
    conv_lhs => rw [show (∑ i, cw i • Yx i r s y) = ∑ i, cw i • push (redL l r) (Yx i (r + 1)) s y from by
      simp only [← hP]]
    simp only [push, Finset.smul_sum]
    exact Finset.sum_comm
  · intro r y j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact continuous_finset_sum _ fun i _ => continuous_const.mul (hCont i r y j)
  · intro r s u j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hw i) (hO i r s u j)

end GlobalTheory.K4
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TeichmullerDecompositionDirichletTwistedPowerStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_decomposition_dirichlet_twisted_power : ∀ (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (e R j : ℕ), l ≠ 2 → ∃ (ε : Qbar l) (t : ℕ), (ε = 0 ∨ ε ^ (l - 1) = 1) ∧ Cg R (φ (j : ZMod l) * (j : Qbar l) ^ e) (ε * ((1 + (l : Qbar l)) ^ e) ^ t) ∧ ∀ m, 1 ≤ m → m ≤ R → ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), InComp φ e ψ → ψ⁻¹ (j : ZMod (l ^ m)) = ε * (ψ⁻¹ (1 + (l : ZMod (l ^ m)))) ^ t := by
  first | exact @GlobalTheory.TeichDec.teich | exact GlobalTheory.TeichDec.teich | (intros; apply GlobalTheory.TeichDec.teich; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TruncatedShiftedSeriesEqIntegralPolyCombinationStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncated_shifted_series_eq_integral_poly_combination : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (F : PowerSeries (Qbar l)) (N : ℕ), (∀ n, F.coeff n ∈ c.O) → ∃ a : ℕ → Qbar l, (∀ j, a j ∈ c.O) ∧ ∀ z : Qbar l, tval F N z = ∑ j ∈ Finset.range N, a j * z ^ j := by
  first | exact @GlobalTheory.KZ.Cmp.tval_eq_sum_pow_of_integral | exact GlobalTheory.KZ.Cmp.tval_eq_sum_pow_of_integral | (intros; apply GlobalTheory.KZ.Cmp.tval_eq_sum_pow_of_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedAwayFromLOfTwistedShapiroLimitStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_away_from_l_of_twisted_shapiro_limit : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l)) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (η : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l), Continuous W → Continuous θ → (∀ s i j, mat W s i j ∈ c.O) → (∀ s, mat W s = (θ s : Qbar l) • ρ s) → (∀ s i j, ρ s i j ∈ c.O) → (∀ r x i, Continuous fun s => Y r s x i) → (∀ r s x i, Y r s x i ∈ c.O) → (∀ r, ShCoc ρ (cycMod ℚ Ω l r)⁻¹ (Y r)) → (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) → (∀ r x, η r x ∈ c.O) → (∀ r s x, ‖η r (x * cycMod ℚ Ω l r s) - η r x * (θ s : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → y ∈ Z1 (Loc.colRep W) → (∀ r s i, ‖y s i - spec (η r) (Y r) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → Unr W y := by
  first | exact @GlobalTheory.KA.unr_of_twisted_limit | exact GlobalTheory.KA.unr_of_twisted_limit | (intros; apply GlobalTheory.KA.unr_of_twisted_limit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UntwistedRepresentationOrdinaryTriangularShapeStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.CyclotomicQExpansion
open scoped Matrix MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.untwisted_representation_ordinary_triangular_shape : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)) (ψ : ZMod l → Qbar l),
  Nf e S A W → SrcUr ι e A W g →
  (∃ χ : G ℚ Ω →* (Qbar l)ˣ, KillsMu l χ ∧
    (∀ s ∈ Ine (F := ℚ) A, mat W s 1 1 * (cycBar ℚ Ω l s : Qbar l) ^ (e : ℤ) * ((dt W s : Qbar l)⁻¹ * (χ s : Qbar l)) = 1) ∧
    ∀ s : G ℚ Ω, (χ s : Qbar l) = ψ ((((cycMod (F := ℚ) (Ω := Ω) l 1 s : ZMod (l ^ 1))).val : ℕ) : ZMod l)) →
  ∃ ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) (Qbar l),
    (∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = rhoK W e ψ s) ∧ Continuous ρ ∧
    (∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0) ∧
    (∀ s ∈ Ine (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = 1) ∧
    ∃ F : Finset Ω, ∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) →
      (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((cycZ ℚ Ω l s : ℤ_[l]) : Qbar l) ^ (2 * e) := by
  first | (exact @GlobalTheory.RhoAdm.rho_ordinary_shape) | (exact GlobalTheory.RhoAdm.rho_ordinary_shape) | (intros; apply GlobalTheory.RhoAdm.rho_ordinary_shape  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZetaSystemExponentRaiseOfPrimePowSmul
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA
open scoped Matrix MatrixGroups

namespace GlobalTheory.K4

theorem zetaSystem_exponent_raise_of_prime_pow_smul : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
  (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N)
  (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (cf : Coef l) (c₀ m : ℕ)
  (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
  (∀ b b', pr (b + b') = pr b + pr b') →
  (∀ (a : ℤ_[l]) b, pr (a • b) = algebraMap ℚ_[l] (Qbar l) (a : ℚ_[l]) • pr b) →
  IsZetaSystemFixedExponent X l pr W e ψ N x c d k g cf c₀ Y →
  IsZetaSystemFixedExponent X l pr W e ψ N x c d k g cf (c₀ + m) (fun r s y => ((l : Qbar l) ^ m) • Y r s y) := by
  intro l _ Ω _ _ ε X pr W e ψ N _ x c d k g cf c₀ m Y hadd hsmul hZ r n
  obtain ⟨bB, hB, b, hb, hY⟩ := hZ r n
  have hl : ‖((l : ℕ) : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ l
  have hlm : ‖((l : ℕ) : Qbar l) ^ m‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hl
  have hpr : ∀ v : X.Fn l, pr (((l : ℤ_[l]) ^ m) • v) = ((l : ℕ) : Qbar l) ^ m • pr v := by
    intro v
    rw [hsmul]
    congr 1
    simp
  refine ⟨fun σ => ((l : ℤ_[l]) ^ m) • bB σ, ?_, fun y => ((l : ℕ) : Qbar l) ^ m • b y, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨h1, h2⟩ := hB σ hσ
    refine ⟨Submodule.smul_mem _ _ h1, fun u => ?_⟩
    have : (((l : ℤ_[l]) ^ m) • bB σ) u - ((l : ℤ_[l]) ^ (c₀ + m)) • clsBmu X l n r N x c d k g σ u
        = ((l : ℤ_[l]) ^ m) • (bB σ u - ((l : ℤ_[l]) ^ c₀) • clsBmu X l n r N x c d k g σ u) := by
      rw [smul_sub, smul_smul, ← pow_add, add_comm m c₀]
      rfl
    rw [this, LinearMap.map_smul, h2 u, smul_zero]
  · intro y i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact cf.O.mul_mem (cf.O.pow_mem (cf.O.natCast_mem l) m) (hb y i)
  · intro s y
    have hYf : YfB X l pr W e ψ n r N (fun σ => ((l : ℤ_[l]) ^ m) • bB σ) s y
        = ((l : ℕ) : Qbar l) ^ m • YfB X l pr W e ψ n r N bB s y := by
      unfold YfB GlobalTheory.KA.push
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [hpr, Matrix.mulVec_smul]
    rw [hYf]
    intro i
    have h := hY s y i
    unfold Cg at h ⊢
    have hrw : ((l : ℕ) : Qbar l) ^ m • Y r s y i -
        (((l : ℕ) : Qbar l) ^ m • YfB X l pr W e ψ n r N bB s y +
          (rhoK W e ψ s *ᵥ (((l : ℕ) : Qbar l) ^ m • b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)) -
            ((l : ℕ) : Qbar l) ^ m • b y)) i
        = ((l : ℕ) : Qbar l) ^ m * (Y r s y i - (YfB X l pr W e ψ n r N bB s y +
          (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y)) i) := by
      simp only [Matrix.mulVec_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    show ‖_‖ ≤ _
    simp only [Pi.smul_apply, smul_eq_mul] at hrw ⊢
    rw [hrw, norm_mul]
    calc _ ≤ 1 * ‖Y r s y i - (YfB X l pr W e ψ n r N bB s y +
          (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y)) i‖ :=
          mul_le_mul_of_nonneg_right hlm (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h

end GlobalTheory.K4
end

