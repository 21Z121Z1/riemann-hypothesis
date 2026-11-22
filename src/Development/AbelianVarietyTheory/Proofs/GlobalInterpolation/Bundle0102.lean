import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0014
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NarrowJetMoments
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0087
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Formalism.LocalToGlobal.Divisibility.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0096
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0089
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0092
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0090
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0093
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickExists
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0005
import Development.AutomorphicArithmetic.ThickFrames.ThickFrame2Large

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.BadPrimes

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_cofactor {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v) {P : HeightOneSpectrum (𝓞 E)}
    (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    ∃ P' : HeightOneSpectrum (𝓞 E), P ≠ P' ∧ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal := by
  obtain ⟨Q, Q', hQ, hm⟩ := hs
  have hle : Q.asIdeal * Q'.asIdeal ≤ P.asIdeal := by
    rw [← hm, Ideal.map_le_iff_le_comap, ← hP]
  rcases P.isPrime.mul_le.1 hle with h | h
  · have : Q = P := HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h)
    subst this
    exact ⟨Q', hQ, hm⟩
  · have : Q' = P := HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le P.isPrime.ne_top h)
    subst this
    exact ⟨Q, hQ.symm, hm.trans (mul_comm _ _)⟩

theorem absNorm_eq_of_split (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v)
    (hq : (Ideal.absNorm v.asIdeal).Prime) {P : HeightOneSpectrum (𝓞 E)} (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal := by
  obtain ⟨P', -, hm⟩ := exists_cofactor hs hP
  have h1 : Ideal.absNorm P.asIdeal * Ideal.absNorm P'.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
    rw [← map_mul, ← hm, Ideal.absNorm_algebraMap (𝓞 F) (𝓞 E), ← h2,
      Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E]
  have hP1 : Ideal.absNorm P.asIdeal ≠ 1 := fun h => P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have hP2 : Ideal.absNorm P'.asIdeal ≠ 1 := fun h => P'.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  exact (((Nat.Prime.mul_eq_prime_sq_iff hq hP1 hP2).1 h1)).1

theorem notMem_sq_of_split {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v) {a : 𝓞 F} (ha : a ∉ v.asIdeal ^ 2)
    {P : HeightOneSpectrum (𝓞 E)} (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    algebraMap (𝓞 F) (𝓞 E) a ∉ P.asIdeal ^ 2 := by
  intro hm2
  obtain ⟨P', hne, hm⟩ := exists_cofactor hs hP
  have hav : a ∈ v.asIdeal := by
    rw [← hP, Ideal.under_def, Ideal.mem_comap]
    exact Ideal.pow_le_self two_ne_zero hm2
  obtain ⟨J, hJ⟩ := Ideal.dvd_span_singleton.2 hav
  have h1 : P.asIdeal * P.asIdeal ∣ P.asIdeal * (P'.asIdeal * Ideal.map (algebraMap (𝓞 F) (𝓞 E)) J) := by
    rw [← mul_assoc, ← hm, ← Ideal.map_mul, ← hJ, Ideal.map_span, Set.image_singleton, Ideal.dvd_span_singleton, ← sq]
    exact hm2
  have h3 := (mul_dvd_mul_iff_left P.ne_bot).1 h1
  rcases P.prime.dvd_or_dvd h3 with h | h
  · exact hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top (Ideal.le_of_dvd h))).symm
  · have h4 : J ≤ v.asIdeal := by
      rw [← hP, Ideal.under_def, ← Ideal.map_le_iff_le_comap]
      exact Ideal.le_of_dvd h
    apply ha
    rw [← Ideal.span_singleton_le_iff_mem, hJ, sq]
    exact Ideal.mul_mono_right h4

end Split

open GlobalTheory.Proof.NarrowJetMoments in

theorem bad_primes : ∀ (X : Fields) (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (u : Pr.Word), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u ∧ (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 ∧ (((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.asIdeal ↔ P ∈ Pr.vT u) := by
  classical
  intro X Pr sel S mu u hX hPr hsel hT hg P hP
  have hoff : ∀ Q ∈ rowSG Pr sel mu, ((Pr.T u : ℕ) : 𝓞 X.E) ∉ Q.asIdeal := fun Q hQ =>
    notMem_rowSG hPr hsel (hPr.T_prime u) hT (hPr.T_ne_g u) hQ
  have hmem : ∀ Q, Q ∈ Sall sel mu u ↔ Q ∈ Pr.vT u ∨ Q ∈ rowSG Pr sel mu := fun Q => by
    unfold Sall
    exact Finset.mem_union
  rcases (hmem P).1 hP with h | h
  · have hTP := T_mem hPr u ⟨P, h⟩
    refine ⟨fun hc => ?_, ?_, ?_, fun _ => h, fun _ => hTP⟩
    · rcases (hmem _).1 hc with h' | h'
      · apply conj_piT_notMem hPr u ⟨P, h⟩
        exact (mem_conjP P _).1 (decoFin_mem_of_mem_divs h')
      · exact hoff _ h' (natCast_mem_conjP.2 hTP)
    · rw [hPr.vT_norm u P h]
      exact hPr.T_prime u
    · rw [hPr.vT_norm u P h]
      exact (T_unif hX hPr u ⟨P, h⟩).2
  · have hn := hoff P h
    refine ⟨fun hc => ?_, ?_⟩
    · rcases (hmem _).1 hc with h' | h'
      · exact hn (natCast_mem_conjP.1 (T_mem hPr u ⟨_, h'⟩))
      · exact conjP_notMem_rowSG hX hPr hsel hg h h'
    have hlast : ((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.asIdeal ↔ P ∈ Pr.vT u :=
      ⟨fun h' => absurd h' hn, fun h' => T_mem hPr u ⟨P, h'⟩⟩
    rcases Finset.mem_union.1 h with h1 | h1
    · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h1
      rw [hPr.vG_norm i P hi]
      refine ⟨hPr.g_prime i, ?_, hlast⟩
      have hrk : 2 * X.f = Module.finrank ℚ X.E := by
        rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, ← hX.card_Tau, mul_comm]
        rfl
      have hcc : cO X.E (X.conjO (Pr.piG i)) = Pr.piG i := cO_cO _
      refine GlobalTheory.SplitUnram.natCast_notMem_sq X.E (cO X.E) (X.conjO (Pr.piG i)) (Pr.g i) cO_cO (hPr.g_prime i) ?_ ?_ ?_
        (hPr.vG_norm i) P hi
      · rw [hcc, mul_comm, hPr.piG_norm i]
      · rw [hcc]
        exact (hPr.piG_cop i).symm
      · rw [← hrk, ← hPr.vG_card i]
        rfl
    · obtain ⟨v, ⟨hs, ⟨hq, hq2⟩, -⟩, rfl⟩ := good_of_mem_QE h1
      rw [absNorm_eq_of_split hX.rankE hs hq (hsel v)]
      refine ⟨hq, ?_, hlast⟩
      have := notMem_sq_of_split hs hq2 (hsel v)
      rwa [map_natCast] at this

end GlobalTheory.ThetaMove.BadPrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AddSubgroupRepsExistenceCardSumStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addSubgroup_reps_existence_card_sum : ∀ (H : Type) [AddCommGroup H], (∀ Λ B : AddSubgroup H, Λ.relIndex B ≠ 0 → ∃ R : Finset H, IsReps Λ B R) ∧ (∀ (Λ B : AddSubgroup H) (R : Finset H), IsReps Λ B R → R.card = Λ.relIndex B) ∧ (∀ (M : Type) [AddCommMonoid M] (Λ B B₁ B₂ : AddSubgroup H) (R R₁ R₂ : Finset H) (F : H → M), B₁ ≤ B → B₂ ≤ B → (∀ y ∈ B, ∃ y₁ ∈ B₁, ∃ y₂ ∈ B₂, y - (y₁ + y₂) ∈ Λ) → (∀ y₁ ∈ B₁, ∀ y₂ ∈ B₂, y₁ + y₂ ∈ Λ → y₁ ∈ Λ) → IsReps Λ B R → IsReps Λ B₁ R₁ → IsReps Λ B₂ R₂ → (∀ y ∈ B, ∀ l ∈ Λ, l ∈ B → F (y + l) = F y) → ∑ y ∈ R, F y = ∑ y₂ ∈ R₂, ∑ y₁ ∈ R₁, F (y₁ + y₂)) ∧ (∀ (K : Type) [Field K] (Λ B : AddSubgroup H) (R : Finset H) (φ : H → K), IsReps Λ B R → (∀ x ∈ B, ∀ y ∈ B, φ (x + y) = φ x * φ y) → (∀ x ∈ B, x ∈ Λ → φ x = 1) → ((∀ y ∈ B, φ y = 1) → ∑ y ∈ R, φ y = (R.card : K)) ∧ ((¬ ∀ y ∈ B, φ y = 1) → ∑ y ∈ R, φ y = 0)) ∧ ∀ (Λ B : AddSubgroup H) (g p : ℕ), p.Prime → Nat.Coprime g p → Λ.relIndex B ≠ 0 → (∀ x ∈ B, g • x ∈ Λ) → ¬ p ∣ Λ.relIndex B := by
  first | exact @GlobalTheory.RepsMod.reps_facts | exact GlobalTheory.RepsMod.reps_facts | (intros; apply GlobalTheory.RepsMod.reps_facts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicNumbersPadicPlacesFactsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicNumbers_padicPlaces_facts : ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (σ : K →+* ℂ) (ι : K →+* ℂ_[p]), (∃ lam : TaylorLogMetric.Qbar →+* ℂ_[p], ∀ k, σ k ∈ TaylorLogMetric.Qbar ∧ TaylorLogMetric.lamC lam (σ k) = ι k) ∧ (∀ w : HeightOneSpectrum (𝓞 K), (∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1) → ∀ x : K, w.valuation K x ≤ 1 → ‖ι x‖ ≤ 1) ∧ ∀ (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (r : ℚ), Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ((r : ℝ) : ℂ)) ∈ TaylorLogMetric.Qbar ∧ ‖TaylorLogMetric.lamC lam (Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ((r : ℝ) : ℂ)))‖ = 1 := by
  first | exact @GlobalTheory.MomPlace.places | exact GlobalTheory.MomPlace.places | (intros; apply GlobalTheory.MomPlace.places <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BadCharacterBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bad_character_bound : ∀ (C : FC) (p : Pt C) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ) (Cb : ℝ), p.From H a b c u0 → CanonInst p.ta.Gx → BadOK p.L.sc Cb H → ChBad_at p.ta.Gx Cb := by
  first | exact @GlobalTheory.EX.chBad_of_from | exact GlobalTheory.EX.chBad_of_from | (intros; apply GlobalTheory.EX.chBad_of_from <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BranchingOk
section
namespace GlobalTheory.LvT.BuiltChain

theorem branching_ok : Formalism.MainNotions.PrimeDegreeVariant.Conclusion6 := Formalism.L2.DIV.BrJ.branching_interlacing_pairs

end GlobalTheory.LvT.BuiltChain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CrdSurjective
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.IdxHom

open GlobalTheory.CharValCompare Matrix Kronecker

variable {E : Type} [Field E] {a b : ℕ}

def crd (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) : HomE E a b →+ (Fin a × Fin b → E) where
  toFun x := (LinearMap.toMatrix' ((g'.symm : Sp E b →ₗ[E] Sp E b) ∘ₗ x ∘ₗ (g : Sp E a →ₗ[E] Sp E a))).vec
  map_zero' := by simp
  map_add' x y := by
    rw [LinearMap.add_comp, LinearMap.comp_add, map_add, Matrix.vec_add]

theorem crd_apply (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) (x : HomE E a b) :
    crd g g' x = (LinearMap.toMatrix' ((g'.symm : Sp E b →ₗ[E] Sp E b) ∘ₗ x ∘ₗ (g : Sp E a →ₗ[E] Sp E a))).vec := rfl

theorem crd_injective (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) : Function.Injective (crd g g') := by
  intro x y h
  rw [crd_apply, crd_apply, Matrix.vec_inj] at h
  have h1 := LinearMap.toMatrix'.injective h
  refine LinearMap.ext fun v => ?_
  have := LinearMap.congr_fun h1 (g.symm v)
  simpa using this

theorem crd_surjective (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) : Function.Surjective (crd g g') := by
  intro v
  obtain ⟨A, rfl⟩ := Matrix.vec_bijective.2 v
  refine ⟨(g' : Sp E b →ₗ[E] Sp E b) ∘ₗ Matrix.toLin' A ∘ₗ (g.symm : Sp E a →ₗ[E] Sp E a), ?_⟩
  rw [crd_apply]
  congr 1
  rw [← LinearMap.toMatrix'_toLin' A]
  congr 1
  refine LinearMap.ext fun v => ?_
  simp

def chg (g₁ g₂ : Sp E a ≃ₗ[E] Sp E a) (g₁' g₂' : Sp E b ≃ₗ[E] Sp E b) : Matrix (Fin a × Fin b) (Fin a × Fin b) E :=
  (LinearMap.toMatrix' ((g₂.symm : Sp E a →ₗ[E] Sp E a) ∘ₗ (g₁ : Sp E a →ₗ[E] Sp E a)))ᵀ ⊗ₖ
    LinearMap.toMatrix' ((g₁'.symm : Sp E b →ₗ[E] Sp E b) ∘ₗ (g₂' : Sp E b →ₗ[E] Sp E b))

theorem chg_mulVec (g₁ g₂ : Sp E a ≃ₗ[E] Sp E a) (g₁' g₂' : Sp E b ≃ₗ[E] Sp E b) (x : HomE E a b) :
    chg g₁ g₂ g₁' g₂' *ᵥ crd g₂ g₂' x = crd g₁ g₁' x := by
  rw [chg, crd_apply, crd_apply, Matrix.kronecker_mulVec_vec, Matrix.transpose_transpose,
    ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
  congr 2
  refine LinearMap.ext fun v => ?_
  simp

theorem det_chg (g₁ g₂ : Sp E a ≃ₗ[E] Sp E a) (g₁' g₂' : Sp E b ≃ₗ[E] Sp E b) :
    (chg g₁ g₂ g₁' g₂').det = ((dt g₂)⁻¹ * dt g₁) ^ b * ((dt g₁')⁻¹ * dt g₂') ^ a := by
  rw [chg, Matrix.det_kronecker, Matrix.det_transpose, LinearMap.det_toMatrix', LinearMap.det_toMatrix',
    LinearMap.det_comp, LinearMap.det_comp, LinearEquiv.det_coe_symm, LinearEquiv.det_coe_symm, Fintype.card_fin,
    Fintype.card_fin, dt_eq, dt_eq, dt_eq, dt_eq]

variable [NumberField E]

theorem ordE_chg (P : HeightOneSpectrum (𝓞 E)) (g₁ g₂ : Sp E a ≃ₗ[E] Sp E a) (g₁' g₂' : Sp E b ≃ₗ[E] Sp E b) :
    ordE P (chg g₁ g₂ g₁' g₂').det =
      (b * ordE P (dt g₁) - a * ordE P (dt g₁')) - (b * ordE P (dt g₂) - a * ordE P (dt g₂')) := by
  have h : ∀ {n : ℕ} (f : Sp E n ≃ₗ[E] Sp E n), P.valuation E (dt f) = WithZero.exp (-ordE P (dt f)) := by
    intro n f
    rw [ordE, neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).2 (dt_ne f))]
  rw [det_chg, ordE, map_mul, map_pow, map_pow, map_mul, map_mul, map_inv₀, map_inv₀, h g₁, h g₂, h g₁', h g₂',
    ← WithZero.exp_neg, ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_add, ← WithZero.exp_nsmul,
    ← WithZero.exp_nsmul, ← WithZero.exp_add, WithZero.log_exp, nsmul_eq_mul, nsmul_eq_mul]
  ring

variable [StarRing E]

theorem mem_homAt_iff {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {g : Sp E a ≃ₗ[E] Sp E a} {g' : Sp E b ≃ₗ[E] Sp E b} (hg : IsFr P N g) (hg' : IsFr P N' g') (x : HomE E a b) :
    x ∈ homAt {P} N N' ↔ ∀ i, IntAt P (crd g g' x i) := by
  change (∀ Q ∈ ({P} : Finset _), ∀ y ∈ localization₂ Q.asIdeal N, x y ∈ localization₂ Q.asIdeal N') ↔ _
  simp only [Finset.mem_singleton, forall_eq]
  constructor
  · rintro h ⟨j, i⟩
    have h1 := h _ ((hg _).2 (single_mem_stdAt P j))
    rw [← g'.apply_symm_apply (x _), hg', stdAt, mem_localization_standardLattice] at h1
    have h2 := h1 i
    simpa [crd_apply, LinearMap.toMatrix'_apply] using h2
  · intro h y hy
    obtain ⟨z, rfl⟩ := g.surjective y
    rw [hg, stdAt, mem_localization_standardLattice] at hy
    rw [← g'.apply_symm_apply (x _), hg', stdAt, mem_localization_standardLattice]
    intro i
    have : g'.symm (x (g z)) =
        LinearMap.toMatrix' ((g'.symm : Sp E b →ₗ[E] Sp E b) ∘ₗ x ∘ₗ (g : Sp E a →ₗ[E] Sp E a)) *ᵥ z := by
      rw [LinearMap.toMatrix'_mulVec]
      rfl
    rw [this, Matrix.mulVec, dotProduct]
    exact intAt_sum _ _ fun j _ => (h (j, i)).mul (hy j)

theorem relIndex_homAt : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (P : HeightOneSpectrum (𝓞 E)) (N₁ N₂ : Submodule (𝓞 E) (Sp E a)) (N₁' N₂' : Submodule (𝓞 E) (Sp E b)), Submodule.IsLattice E N₁ → Submodule.IsLattice E N₂ → Submodule.IsLattice E N₁' → Submodule.IsLattice E N₂' → homAt {P} N₂ N₂' ≤ homAt {P} N₁ N₁' → (((homAt {P} N₂ N₂').toAddSubgroup.relIndex (homAt {P} N₁ N₁').toAddSubgroup : ℕ) : ℚ) = ((Ideal.absNorm P.asIdeal : ℕ) : ℚ) ^ (volExp P N₁ N₁' - volExp P N₂ N₂') := by
  intro E _ _ _ a b P N₁ N₂ N₁' N₂' h₁ h₂ h₁' h₂' hle
  obtain ⟨g₁, hg₁⟩ := exists_isFr P h₁
  obtain ⟨g₂, hg₂⟩ := exists_isFr P h₂
  obtain ⟨g₁', hg₁'⟩ := exists_isFr P h₁'
  obtain ⟨g₂', hg₂'⟩ := exists_isFr P h₂'
  have h0 : ∀ x, x ∈ (homAt {P} N₁ N₁').toAddSubgroup.map (crd g₁ g₁') ↔ ∀ i, IntAt P (x i) := by
    intro x
    obtain ⟨y, rfl⟩ := crd_surjective g₁ g₁' x
    rw [AddSubgroup.mem_map_iff_mem (crd_injective _ _), Submodule.mem_toAddSubgroup, mem_homAt_iff hg₁ hg₁']
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ (crd_injective g₁ g₁'),
    GlobalTheory.IdxDet.relIndex_mulVec E (Fin a × Fin b) P (chg g₁ g₂ g₁' g₂') _ _ ?_ h0 ?_ (AddSubgroup.map_mono hle),
    ordE_chg, volExp, volExp, ordDet_eq hg₁, ordDet_eq hg₂, ordDet_eq hg₁', ordDet_eq hg₂']
  · rw [det_chg]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero (inv_ne_zero (dt_ne _)) (dt_ne _)))
      (pow_ne_zero _ (mul_ne_zero (inv_ne_zero (dt_ne _)) (dt_ne _)))
  · intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, (h0 _).2 ((mem_homAt_iff hg₂ hg₂' y).1 hy), (chg_mulVec _ _ _ _ y).symm⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨y, rfl⟩ := crd_surjective g₂ g₂' v
      exact ⟨y, (mem_homAt_iff hg₂ hg₂' y).2 ((h0 _).1 hv), (chg_mulVec _ _ _ _ y).symm⟩

end GlobalTheory.IdxHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DiscOneScaleRatioIdealRingAlgebraicUnitStatement
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discOneScale_ratio_ideal_ring_algebraic_unit : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ₀ ^ 12 = GlobalTheory.MomOne.discr D.host.d → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → Nat.Coprime (Ideal.absNorm cc) q → δ / δ₀ ∈ Qbar ∧ ∀ ι : ℂ ≃+* ℂ_[q], ‖ι (δ / δ₀)‖ = 1 := by
  first | exact @GlobalTheory.MomDelta.delta_ratio | exact GlobalTheory.MomDelta.delta_ratio | (intros; apply GlobalTheory.MomDelta.delta_ratio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsHermitianFormDescentCoefficientField
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

noncomputable section

namespace GlobalTheory.Glob.FormDescent

theorem desc : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ} (S : GStep E K n) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok) (z : S.Cl → GlobalTheory.Mem.Col2.Fr emb σ n → ℂ), z ∈ S.Fi emb σ lam → ∀ v : S.Cl → Formalism.L2.DIV.VV K lam, (∀ c, z c = evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (v c)) → ∃ y : S.FormsK emb lam h, (∀ c, y.1 c = v c) ∧ S.embF emb σ lam h y = z := by
  intro E K ι _ _ _ _ _ _ _ emb σ n S lam h z hz v hv
  have hinj : Function.Injective (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ) := by
    intro a b hab
    have h1 := congrArg (polOf (Gr emb σ n) (shiftOf lam) (fr0 emb σ n)) hab
    rw [GlobalTheory.LvT.BuiltChain.polOf_evV, GlobalTheory.LvT.BuiltChain.polOf_evV] at h1
    exact Subtype.ext (MvPolynomial.map_injective σ σ.injective h1)
  refine ⟨⟨v, fun c g => ?_⟩, fun c => rfl, ?_⟩
  · apply hinj
    show evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (S.rho emb lam c.1 g.1 (v c)) = _
    rw [GlobalTheory.LvT.BuiltChain.evV_rho, ← hv c]
    exact (hz c).2 ⟨g.1, g.2⟩
  · funext c
    exact (hv c).symm

end GlobalTheory.Glob.FormDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLocalBasisSnocOfLocalBasisStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localBasis_snoc_of_localBasis : ∀ {E : Type} [Field E] [NumberField E] {N n : ℕ} (hN : N = n + 1) (t : E), t ≠ 0 → ∀ (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin n → E)), (∀ x, x ∈ L ↔ iniH hN x ∈ L' ∧ t * x (Br.iL hN) ∈ (1 : Submodule (𝓞 E) E)) → ∀ (p : ℕ) (B' : GL (Fin n) E), p.Prime → IsLocBasis p (L' : Set (Fin n → E)) B' → ∃ B : GL (Fin N) E, (∀ x, iniH hN ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) = (B' : Matrix (Fin n) (Fin n) E) *ᵥ iniH hN x) ∧ (∀ x, t * ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) (Br.iL hN) = x (Br.iL hN)) ∧ IsLocBasis p (L : Set (Fin N → E)) B := by
  first | exact @GlobalTheory.isLocBasis_snoc | exact GlobalTheory.isLocBasis_snoc | (intros; apply GlobalTheory.isLocBasis_snoc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsNatSmulMemOfFg
section
namespace GlobalTheory.FinitelyGeneratedNatMultiple

theorem exists_nat_smul_mem_of_fg {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W]
    [Module (NumberField.RingOfIntegers E) W]
    {M N : Submodule (NumberField.RingOfIntegers E) W}
    (hM : GlobalTheory.ThetaMove.Full M) (hN : Submodule.FG N) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ N, (m : NumberField.RingOfIntegers E) • x ∈ M := by
  classical
  obtain ⟨s, rfl⟩ := hN
  have hM' : ∀ x : W, ∃ n : ℕ, 0 < n ∧ (n : NumberField.RingOfIntegers E) • x ∈ M := hM
  choose n hn0 hn using hM'
  refine ⟨∏ y ∈ s, n y, Finset.prod_pos fun y _ => hn0 y, fun x hx => ?_⟩
  have hle : Submodule.span (NumberField.RingOfIntegers E) (s : Set W) ≤
      M.comap (LinearMap.lsmul (NumberField.RingOfIntegers E) W
        ((∏ y ∈ s, n y : ℕ) : NumberField.RingOfIntegers E)) := by
    rw [Submodule.span_le]
    intro y hy
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (Finset.mem_coe.mp hy)
    show ((∏ y ∈ s, n y : ℕ) : NumberField.RingOfIntegers E) • y ∈ M
    rw [hk, mul_comm, Nat.cast_mul, mul_smul]
    exact M.smul_mem _ (hn y)
  exact hle hx

end GlobalTheory.FinitelyGeneratedNatMultiple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPrimesInProgressionBounded
section
namespace GlobalTheory.EX

theorem lt_of_prime_mod_eq_one {p M : ℕ} (hp : p.Prime) (h : p % M = 1) (hM : 0 < M) : M < p := by
  by_contra hc
  rcases (not_lt.mp hc).lt_or_eq with hlt | heq
  · rw [Nat.mod_eq_of_lt hlt] at h
    exact hp.one_lt.ne' h
  · subst heq
    simp at h

theorem mod_eq_one_of_mod_mul {p M K : ℕ} (h : p % (M * K) = 1) (hM : 1 < M) : p % M = 1 := by
  rw [← Nat.mod_mul_right_mod p M K, h, Nat.mod_eq_of_lt hM]

theorem auxiliary_primes : SmallPrimeOne → ∃ C8 : ℝ, 1 ≤ C8 ∧ ∀ N : ℕ, 30 ≤ N → ∃ p p' q0 : ℕ, p.Prime ∧ p'.Prime ∧ q0.Prime ∧ p ≠ p' ∧ q0 ≠ p ∧ q0 ≠ p' ∧ p % (15 * N) = 1 ∧ p' % (15 * N) = 1 ∧ q0 % N = 1 ∧ (p : ℝ) ≤ (N : ℝ) ^ C8 ∧ (p' : ℝ) ≤ (N : ℝ) ^ C8 ∧ (q0 : ℝ) ≤ (N : ℝ) ^ C8 := by
  rintro ⟨A, hA, hS⟩
  have hA0 : 0 ≤ A := by linarith
  refine ⟨(2 + 2 * A + (2 + 2 * A) * A) * A, by nlinarith [mul_nonneg hA0 hA0, mul_nonneg hA0 (mul_nonneg hA0 hA0)], ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  have key : ∀ (M : ℕ) (e : ℝ), 2 ≤ M → (M : ℝ) ≤ (N : ℝ) ^ e →
      ∃ p : ℕ, p.Prime ∧ p % M = 1 ∧ (p : ℝ) ≤ (N : ℝ) ^ (e * A) := by
    intro M e hM hMe
    obtain ⟨p, hp, hpm, hple⟩ := hS M hM
    refine ⟨p, hp, hpm, hple.trans ?_⟩
    rw [Real.rpow_mul hN0.le]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hMe hA0
  have h15 : ((15 * N : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
    have : (30 : ℝ) ≤ N := by exact_mod_cast hN
    rw [Real.rpow_two]; push_cast; nlinarith
  have hM1 : 2 ≤ 15 * N := by omega
  obtain ⟨p, hp, hpm, hple⟩ := key (15 * N) 2 hM1 h15
  have hM2 : 2 ≤ 15 * N * p := hM1.trans (Nat.le_mul_of_pos_right _ hp.pos)
  have hb2 : ((15 * N * p : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 + 2 * A) := by
    rw [Real.rpow_add hN0, Nat.cast_mul (15 * N) p]
    exact mul_le_mul h15 hple (Nat.cast_nonneg _) (Real.rpow_nonneg hN0.le _)
  obtain ⟨p', hp', hpm', hple'⟩ := key (15 * N * p) _ hM2 hb2
  have hM3 : 2 ≤ 15 * N * p * p' := hM2.trans (Nat.le_mul_of_pos_right _ hp'.pos)
  have hb3 : ((15 * N * p * p' : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 + 2 * A + (2 + 2 * A) * A) := by
    rw [Real.rpow_add hN0, Nat.cast_mul (15 * N * p) p']
    exact mul_le_mul hb2 hple' (Nat.cast_nonneg _) (Real.rpow_nonneg hN0.le _)
  obtain ⟨q, hq, hqm, hqle⟩ := key (15 * N * p * p') _ hM3 hb3
  have l1 : 15 * N * p < p' := lt_of_prime_mod_eq_one hp' hpm' (by omega)
  have l2 : 15 * N * p * p' < q := lt_of_prime_mod_eq_one hq hqm (by omega)
  have l3 : p ≤ 15 * N * p := Nat.le_mul_of_pos_left _ (by omega)
  have l4 : p' ≤ 15 * N * p * p' := Nat.le_mul_of_pos_left _ (by omega)
  have hAA := mul_nonneg hA0 hA0
  have hAAA := mul_nonneg hA0 hAA
  refine ⟨p, p', q, hp, hp', hq, by omega, by omega, by omega, hpm,
    mod_eq_one_of_mod_mul hpm' (by omega), ?_, ?_, ?_, hqle⟩
  · have : 15 * N * p * p' = N * (15 * p * p') := by ring
    rw [this] at hqm
    exact mod_eq_one_of_mod_mul hqm (by omega)
  · exact hple.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith))
  · exact hple'.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith))

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsThinPrimeSet
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem Lwv_le_mul_log (s : Scale) (hy : 1 ≤ Real.log s.x) :
    (Lwv s : ℝ) ≤ (4084 + 60 / s.eps) * Real.log s.x := by
  have he := s.eps_pos
  have h1 : (⌈(405 : ℝ) * Real.log s.x⌉₊ : ℝ) < 405 * Real.log s.x + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  have h2 : (⌈30 / s.eps⌉₊ : ℝ) < 30 / s.eps + 1 := Nat.ceil_lt_add_one (by positivity)
  have h3 : 60 / s.eps = 2 * (30 / s.eps) := by ring
  have h4 : 0 < 30 / s.eps := by positivity
  unfold Lwv
  push_cast
  rw [h3]
  nlinarith [mul_nonneg h4.le (sub_nonneg.mpr hy)]

theorem exists_thick_set_sizes :
    ∃ CT2 : ℝ, ∀ eps Co : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R → (R.o : ℝ) ≤ Co → ∃ T : Finset ℕ, (∀ a ∈ T, 4 * Lwv s * a < R.n0) ∧ Formalism.FrobeniusOrbits.NoRel T (Lwv s) ∧ (R.n0 : ℝ) * Real.exp (-(CT2 * Real.sqrt (Real.log (R.n0 : ℝ) * Real.log (Lwv s)))) / (Lwv s) ≤ T.card ∧ s.x ^ (-s.eps) * R.n ≤ (T.card : ℝ) ∧ 4 * Lwv s * T.card ≤ R.n0 ∧ 2 ≤ Lwv s := by
  obtain ⟨C, -, hT⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.thickFrame2
  refine ⟨C, fun eps Co he he' => ?_⟩
  obtain ⟨x0, hT⟩ := hT eps (max Co 2) (4084 + 60 / eps) he he'
  refine ⟨max x0 (Real.exp 1), fun s R hs hx hR ho => ?_⟩
  have hx0 : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have hy1 : 1 ≤ Real.log s.x := (Real.le_log_iff_exp_le hx0).mpr ((le_max_right _ _).trans hx)
  have hL : 2 ≤ Lwv s := by unfold Lwv; omega
  have hLK := Lwv_le_mul_log s hy1
  have hn1 := hR.n_lo
  have hn2 := hR.n_up
  rw [hs] at hLK hn1 hn2
  have hp0 : 0 < s.x ^ (2 + 8 * eps) := Real.rpow_pos_of_pos hx0 _
  have hlo : s.x ^ UpperTheory.BernoulliSumsFrobeniusOrbits.hE eps / 2 ≤ (R.n : ℝ) := by
    unfold UpperTheory.BernoulliSumsFrobeniusOrbits.hE
    linarith
  have hup : (R.n : ℝ) ≤ max Co 2 * s.x ^ UpperTheory.BernoulliSumsFrobeniusOrbits.hE eps :=
    hn2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp0.le)
  obtain ⟨T, t1, t2, t3, t4, t5⟩ := hT s.x ((le_max_left _ _).trans hx) R.toFrame (Lwv s) hL hLK
    (ho.trans (le_max_left _ _)) hlo hup
  exact ⟨T, t1, t2, t3, hs ▸ t4, t5, hL⟩

end GlobalTheory.EX
end

