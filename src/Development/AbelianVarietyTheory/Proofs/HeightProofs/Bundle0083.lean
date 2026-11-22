import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0079
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntUnit
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRightKFourierSeriesUnitaryModerateGrowth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier
open MeasureTheory Matrix Formalism.REAL GlobalTheory.TypeSum

variable {n : ℕ}

theorem rder_mem (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ) (hφ : φ ∈ polyV ε d) (l : List (Mx n))
    (hl : ∀ X ∈ l, inK ε X) : rder ε l φ ∈ polyV ε d := by
  induction l with
  | nil => exact hφ
  | cons X l ih =>
    have h := (GlobalTheory.T.contDiff_matrixRightInvariantDerivative ε d _ (ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) X (hl X List.mem_cons_self)).1
    exact h

theorem hs_mul_toMK (ε : Fin n → Bool) (y : Mx n) (k : KG ε) : hs (y * toMK k) = hs y :=
  ((hermitian_small_ball n ε).2 y _ k.2).1

theorem toMK_expK_mul (ε : Fin n → Bool) (X : Mx n) (hK : inK ε X) (t : ℝ) (x : KG ε) :
    toMK (expK ε X t * x) = NormedSpace.exp (t • X) * toMK x := by
  rw [toMK_mul, toMK_expK hK, Complex.coe_smul]

theorem summable_listSum {ι : Type} (U : List ι) (b : ι → ℕ → ℝ) (hb : ∀ u ∈ U, Summable (b u)) :
    Summable fun i => (U.map fun u => b u i).sum := by
  induction U with
  | nil => simpa using (summable_zero : Summable fun _ : ℕ => (0 : ℝ))
  | cons u U ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hb u List.mem_cons_self).add (ih fun v hv => hb v (List.mem_cons_of_mem _ hv))

theorem exists_rightKFourier : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ e : ℕ → (Formalism.REAL.KG ε → ℂ), (∀ i, Continuous (e i)) ∧
    (∀ i, KFinFun ε (e i)) ∧ ∀ f : Mx n → ℂ, ContinuousOn f (UJset ε) → UMG ε f →
    ∃ (N : ℕ) (Φ : ℕ → List (Mx n) → Mx n → ℂ) (B : ℕ → ℕ → ℝ),
      (∀ i, ∀ y ∈ UJset ε, Φ i [] y = ∫ k, e i k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) ∧
      (∀ i (l : List (Mx n)), (∀ Y ∈ l, Y ∈ lieSet ε ∧ Yᴴ = -Y) → ∀ X : Mx n, X ∈ lieSet ε → Xᴴ = -X →
        ∀ y ∈ UJset ε, HasDerivAt (fun t : ℝ => Φ i l (y * NormedSpace.exp (t • X))) (Φ i (X :: l) y) 0) ∧
      (∀ i k (w : List (Mx n)), w.length ≤ k → (∀ X ∈ w, X ∈ lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
        ∀ y ∈ UJset ε, ‖Φ i w y‖ ≤ B i k * (1 + hs y) ^ N) ∧
      (∀ k, Summable fun i => B i k) ∧
      ∀ y ∈ UJset ε, HasSum (fun i => ∫ k, e i k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (f y) := by
  intro n ε
  have hker : ∀ i, IsKer ε i (kerE ε i) := fun i => isKer_kerE (GlobalTheory.T.exists_compactUnitary_fourierKernel ε i)
  refine ⟨kerE ε, fun i => continuous_of_mem (hker i).1, fun i => kFinFun_of_mem (hker i).1, ?_⟩
  intro f hf hU
  obtain ⟨N, F, hF0, hFd, hFg⟩ := hU
  have hcF : ContinuousOn (F []) (UJset ε) := hf.congr fun g hg => hF0 g hg
  have hdec : ∀ u : List (Mx n), ∃ b : ℕ → ℝ, Summable b ∧ ((∀ X ∈ u, inK ε X) → ∀ i, ∀ y ∈ UJset ε,
      ‖∫ k, kerE ε i k * F u (y * toMK k) ∂(muK ε)‖ ≤ b i * (1 + hs y) ^ N) := by
    intro u
    by_cases hu : ∀ X ∈ u, inK ε X
    · obtain ⟨b, hb, hb'⟩ := GlobalTheory.T.kFourier_coefficient_rapid_decay ε N F hFd hFg hcF (kerE ε) hker u hu
      exact ⟨b, hb, fun _ => hb'⟩
    · exact ⟨0, summable_zero, fun h => absurd h hu⟩
  choose b hbs hbb using hdec
  choose U C hC0 hUK hC using GlobalTheory.T.rightDeriv_norm_le_finite_words_bound ε
  have hQ : ∀ i, ∀ y ∈ UJset ε, avgK ε (kerE ε i) f y ∈ polyV ε i := fun i y hy =>
    GlobalTheory.T.compactUnitaryAverage_mem_polyV ε i _ (hker i).1 f hf y hy
  have hbound : ∀ i m (w : List (Mx n)), w.length ≤ m → (∀ X ∈ w, X ∈ GlobalTheory.SmoothGlob.lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
      ∀ y ∈ UJset ε, ‖rder ε w (avgK ε (kerE ε i) f y) 1‖ ≤ C m * ((U m).map fun u => b u i).sum * (1 + hs y) ^ N := by
    intro i m w hw hwX y hy
    have hwK : ∀ X ∈ w, inK ε X ∧ hs X ≤ 1 := fun X hX =>
      ⟨inK_of_skew (hwX X hX).1 (hwX X hX).2.1, (hwX X hX).2.2⟩
    have h1 := hC m i _ (hQ i y hy) w hw hwK
    have h2 : ((U m).map fun u => ‖rder ε u (avgK ε (kerE ε i) f y) 1‖).sum ≤
        ((U m).map fun u => b u i * (1 + hs y) ^ N).sum := by
      refine List.sum_le_sum fun u hu => ?_
      rw [GlobalTheory.T.compactUnitaryRightDeriv_conjInvariantAverage_eq ε N F hFd hFg f hf hF0 _ (continuous_of_mem (hker i).1) (GlobalTheory.T.compactUnitary_fourierKernel_conj_invariant ε i _ (hker i)) u (hUK m u hu) y hy]
      exact hbb u (hUK m u hu) i y hy
    rw [List.sum_map_mul_right] at h2
    calc _ ≤ _ := h1
      _ ≤ C m * (((U m).map fun u => b u i).sum * (1 + hs y) ^ N) := mul_le_mul_of_nonneg_left h2 (hC0 m)
      _ = _ := by ring
  refine ⟨N, fun i l y => rder ε l (avgK ε (kerE ε i) f y) 1,
    fun i m => C m * ((U m).map fun u => b u i).sum, ?_, ?_, hbound, ?_, ?_⟩
  · intro i y hy
    simp [avgK, toMK_one]
  · intro i l hl X hX hXs y hy
    have hK := inK_of_skew hX hXs
    have hlK : ∀ Y ∈ l, inK ε Y := fun Y hY => inK_of_skew (hl Y hY).1 (hl Y hY).2
    have hR := rder_mem ε i _ (hQ i y hy) l hlK
    have e1 : (fun t : ℝ => rder ε l (avgK ε (kerE ε i) f (y * NormedSpace.exp (t • X))) 1) =
        fun t : ℝ => rder ε l (avgK ε (kerE ε i) f y) (1 * expK ε X t) := by
      funext t
      rw [one_mul, ← mul_one (expK ε X t), ← rder_left ε l _ (expK ε X t) 1]
      congr 1
      funext x
      simp only [avgK]
      rw [toMK_expK_mul ε X hK t x]
      simp only [Matrix.mul_assoc]
    show HasDerivAt (fun t : ℝ => rder ε l (avgK ε (kerE ε i) f (y * NormedSpace.exp (t • X))) 1)
      (rder ε [X] (rder ε l (avgK ε (kerE ε i) f y)) 1) 0
    rw [e1]
    exact (GlobalTheory.T.contDiff_matrixRightInvariantDerivative ε i _ hR X hK).2 1
  · intro m
    exact (summable_listSum (U m) b fun u _ => hbs u).mul_left (C m)
  · intro y hy
    have key := GlobalTheory.T.hasSum_compactUnitaryFourier_value_one ε (kerE ε) hker (fun k => f (y * toMK k)) ?_ (fun i => C 0 * ((U 0).map fun u => b u i).sum * (1 + hs y) ^ N)
      (((summable_listSum (U 0) b fun u _ => hbs u).mul_left (C 0)).mul_right _) ?_
    · simpa [toMK_one] using key
    · exact hf.comp_continuous ((continuous_const.mul (continuous_toMK ε))) fun k => mul_mem_UJ hy (K_le_UJ k.2)
    · intro i k'
      have hyk : y * toMK k' ∈ UJset ε := mul_mem_UJ hy (K_le_UJ k'.2)
      have := hbound i 0 [] le_rfl (by simp) _ hyk
      rw [hs_mul_toMK] at this
      simpa [avgK, toMK_one, toMK_mul, Matrix.mul_assoc] using this

end GlobalTheory.KFourier

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.TotientDvdCardUnitsQuot
section
noncomputable section

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize

theorem totient_dvd_card_units_quot (E : Type) [Field E] [NumberField E] (N : ℕ) (hN : 0 < N) :
    N.totient ∣ Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ := by
  have : NeZero N := ⟨hN.ne'⟩
  have hc : CharP (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) N := by
    refine ⟨fun m => ?_⟩
    have h1 : Ideal.comap (algebraMap ℤ (𝓞 E)) (Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(N : ℤ)})) =
        Ideal.span {(N : ℤ)} := Ideal.comap_map_eq_self_of_faithfullyFlat _
    rw [Ideal.map_span, Set.image_singleton, map_natCast] at h1
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 E)})), Ideal.Quotient.eq_zero_iff_mem,
      ← Int.natCast_dvd_natCast, ← Ideal.mem_span_singleton (x := (m : ℤ)), ← h1, Ideal.mem_comap, map_natCast]
  have hi : Function.Injective (ZMod.castHom (dvd_refl N) (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})) :=
    ZMod.castHom_injective _
  have := Subgroup.card_dvd_of_injective _ (Units.map_injective
    (f := (ZMod.castHom (dvd_refl N) (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})).toMonoidHom) hi)
  rwa [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at this

set_option maxHeartbeats 4000000 in

theorem fieldOK0_and_zeta_mem : ∀ (X : Stages) (F : IntermediateField ℚ ℂ), Rich X.B.toPre F → (∀ z, z ∈ F ↔ ∃ x ∈ X.B.Ks, X.B.embLL x = z) → ∀ p : ℕ, (p = X.toD7.host.pde ∨ p = X.toD7.host.pde') → FieldOK0 X.toD7 p ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (15 * classNumber X.toD7.host.E) ∈ FO X.toD7 := by
  intro X F hR hF p hp'
  obtain rfl : F = FO X.toD7 := SetLike.ext fun z => (hF z).trans (mem_FO_assembled_iff X z).symm
  have hp : p = X.B.host.pde ∨ p = X.B.host.pde' := hp'
  have hp0 : p.Prime := by
    rcases hp with rfl | rfl
    exacts [X.B.host.pde_prime, X.B.host.pde'_prime]
  have key : FieldOK0 X.toD7 p := by
    refine ⟨hp, hermitianCodeWordStages_ringOfIntegers_full _, hermitianCodeWordStages_has_rootOfUnity _, ?_, ?_, TypeNormPin.hermitianCodeWordStages_typeNorms_principal _,
      fun h => Nat.not_prime_zero (X.B.toPre.level_cond 0 h).1, ?_⟩
    · rcases hp with rfl | rfl
      exacts [hR.roots _ (by simp), hR.roots _ (by simp)]
    · exact curveOver_of_weberSet X.toD7 _
        (Nat.mul_pos (Nat.mul_pos (X.B.host.g_prime 0).pos (X.B.host.g_prime 1).pos) hp0.pos) (hR.host _)
        fun L hL => hR.weber L hL p (by simpa using hp)
    · rcases hp with rfl | rfl
      exacts [X.B.toPre.level_split _ X.B.host.pde_level.1, X.B.toPre.level_split _ X.B.host.pde_level.2]
  refine ⟨key, ?_⟩
  have hN : 0 < X.B.host.g 0 * X.B.host.g 1 * p :=
    Nat.mul_pos (Nat.mul_pos (X.B.host.g_prime 0).pos (X.B.host.g_prime 1).pos) hp0.pos
  have hroot : Complex.exp (2 * Real.pi * Complex.I /
      (xiOrd X.B.host (X.B.host.g 0 * X.B.host.g 1 * p) : ℕ)) ∈ FO X.toD7 := by
    rcases hp with rfl | rfl
    · exact hR.roots (xiOrd X.B.host (X.B.host.g 0 * X.B.host.g 1 * X.B.host.pde)) (by simp)
    · exact hR.roots (xiOrd X.B.host (X.B.host.g 0 * X.B.host.g 1 * X.B.host.pde')) (by simp)
  have hI : Ideal.span {((X.B.host.g 0 * X.B.host.g 1 * p : ℕ) : 𝓞 X.B.host.E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hN.ne'
  have : Finite (𝓞 X.B.host.E ⧸ Ideal.span {((X.B.host.g 0 * X.B.host.g 1 * p : ℕ) : 𝓞 X.B.host.E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ hI
  have ho : 0 < xiOrd X.B.host (X.B.host.g 0 * X.B.host.g 1 * p) :=
    Nat.mul_pos (Nat.mul_pos two_pos (classNumber_pos _)) Nat.card_pos
  have h15 : 15 ∣ p - 1 := by
    have := X.B.host.pde_mod
    rcases hp with rfl | rfl <;> omega
  have hd : 15 * classNumber X.B.host.E ∣ xiOrd X.B.host (X.B.host.g 0 * X.B.host.g 1 * p) := by
    have h1 := (h15.trans ((Nat.totient_prime hp0).symm.dvd.trans
      (Nat.totient_dvd_of_dvd (Dvd.intro_left _ rfl)))).trans (totient_dvd_card_units_quot X.B.host.E _ hN)
    rw [mul_comm]
    exact Nat.mul_dvd_mul (Dvd.intro_left _ rfl) h1
  refine GlobalTheory.NormOneChar.mem_of_pow_eq_one ho hroot ?_
  obtain ⟨c, hc⟩ := hd
  have hh : 15 * classNumber X.B.host.E ≠ 0 := mul_ne_zero (by norm_num) (classNumber_ne_zero _)
  rw [hc, pow_mul]
  have := (Complex.isPrimitiveRoot_exp _ hh).pow_eq_one
  change (Complex.exp (2 * Real.pi * Complex.I / (15 * classNumber X.B.host.E : ℕ)) ^ _) ^ c = 1
  rw [this, one_pow]

end GlobalTheory.FieldSize
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesFiniteAlgebraicPermutedStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weberValues_finite_algebraic_permuted : ∀ (L : PeriodPair) (n : ℕ), 0 < n → L.g₂ ≠ 0 → L.g₃ ≠ 0 → (weberSet L n).Finite ∧ (IsAlgebraic ℚ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) → ∀ w ∈ weberSet L n, IsAlgebraic ℚ w) ∧ ∀ τ : ℂ ≃+* ℂ, τ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) = (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) → ∀ t, (n : ℂ) * t ∈ L.lattice → t ∉ L.lattice → ∃ t', (n : ℂ) * t' ∈ L.lattice ∧ t' ∉ L.lattice ∧ τ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) = (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t') := by
  first | exact @GlobalTheory.FieldSize.weberSet_finite_algebraic_permuted | exact GlobalTheory.FieldSize.weberSet_finite_algebraic_permuted | (intros; apply GlobalTheory.FieldSize.weberSet_finite_algebraic_permuted <;> assumption)
end

