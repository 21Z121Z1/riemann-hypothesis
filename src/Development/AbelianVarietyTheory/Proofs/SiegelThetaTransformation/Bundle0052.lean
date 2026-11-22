import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionZeroAndNorm
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0010
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicCuspFormAutomorphicBoundedSquareIntegrableStatement
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_cuspForm_automorphic_bounded_square_integrable : ∀ (D : D7) (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hD : Dom a n), ∀ f ∈ T.cuspA j a n, (∀ γ ∈ GQ (T.V j σ), ∀ g, T.phiJ j σ a f (γ * g) = T.phiJ j σ a f g) ∧ (∀ k ∈ T.Kf j σ, ∀ g, T.phiJ j σ a f (g * k) = T.mu j σ k * T.phiJ j σ a f g) ∧ Continuous (T.phiJ j σ a f) ∧ (∃ C : ℝ, ∀ g, ‖T.phiJ j σ a f g‖ ≤ C) ∧ MemLp (onQ (T.V j σ) (T.phiJ j σ a f)) 2 (muQ1 (T.V j σ)) := by
  first | exact @GlobalTheory.AdelicCusp.phiJ_automorphic | exact GlobalTheory.AdelicCusp.phiJ_automorphic | (intros; apply GlobalTheory.AdelicCusp.phiJ_automorphic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionZeroAndNormStatement
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledHermitianTestFunction_zero_and_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∃ a : ℂ, a ≠ 0 ∧ ∃ b : ℝ, 0 < b ∧ ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → dbl X bas idx φ₁ φ₂ 0 = a * ip φ₁ φ₂ ∧ ip (dbl X bas idx φ₁ φ₂) (dbl X bas idx φ₁ φ₂) = b * (ip φ₁ φ₁ * ip φ₂ φ₂) := by
  first | exact @GlobalTheory.SW.dbl_zero_and_norm | exact GlobalTheory.SW.dbl_zero_and_norm | (intros; apply GlobalTheory.SW.dbl_zero_and_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedRealStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_lattice_stabilizer_bounded_real : ∀ (D : D7) (V : HSp D) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ R : ℝ, ∃ K : Set (GA D V), IsCompact K ∧ ∀ h : GA D V, (∀ y, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ (finMat D.sp.cm.sig V.gram h).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V)) → (∀ ρ i j, ‖infMat D.sp.cm.sig V.gram (θ ρ) h i j‖ ≤ R) → h ∈ K := by
  first | exact @GlobalTheory.StabCompact.exists_compact_stab | exact GlobalTheory.StabCompact.exists_compact_stab | (intros; apply GlobalTheory.StabCompact.exists_compact_stab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker

theorem exists_infFam_and_stdChar : ∀ D : D7, (∃ θ : InfFam D, IsInfFam θ) ∧ ∃ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) :=
  fun D => ⟨GlobalTheory.DualPairCompare.exists_infFam D, GlobalTheory.StdAdelicChar.exists_isStdChar D⟩

end GlobalTheory.Ker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsProperProjection
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StabProper

private lemma sum_mul_conj_eq_conj_dotProduct {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    ∑ a, ∑ b, x a * conj (G b a) * conj (y b) = conj (y ⬝ᵥ (G *ᵥ star x)) := by
  simp only [dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_conj]
  ring

theorem unitary_iff_form {n : ℕ} (G g : Matrix (Fin n) (Fin n) ℂ) :
    gᴴ * G * g = G ↔ ∀ v w : Fin n → ℂ,
      ∑ a, ∑ b, (g.map conj *ᵥ v) a * conj (G b a) * conj ((g.map conj *ᵥ w) b) =
        ∑ a, ∑ b, v a * conj (G b a) * conj (w b) := by
  have h1 : ∀ v : Fin n → ℂ, star (g.map conj *ᵥ v) = g *ᵥ star v := by
    intro v; ext i
    simp [mulVec, dotProduct]
  have key : ∀ v w : Fin n → ℂ, ∑ a, ∑ b, (g.map conj *ᵥ v) a * conj (G b a) * conj ((g.map conj *ᵥ w) b) =
      conj (w ⬝ᵥ ((gᴴ * G * g) *ᵥ star v)) := by
    intro v w
    rw [sum_mul_conj_eq_conj_dotProduct, h1]
    congr 1
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec w gᴴ]
    congr 1
    ext j
    simp [vecMul, mulVec, dotProduct, conjTranspose_apply, mul_comm]
  constructor
  · intro h v w
    rw [key, h, sum_mul_conj_eq_conj_dotProduct]
  · intro h
    ext i j
    have hs : ∀ k : Fin n, star (Pi.single k 1 : Fin n → ℂ) = Pi.single k 1 := by
      intro k; ext l; by_cases hl : l = k <;> simp [hl]
    have := h (Pi.single j 1) (Pi.single i 1)
    rw [key, sum_mul_conj_eq_conj_dotProduct, hs] at this
    have := (starRingEnd ℂ).injective this
    simpa [mulVec, dotProduct, Pi.single_apply] using this

variable {D : D7}

theorem compAt_eq (θ : InfFam D) (τ : D.what₂.Tau) {m n : ℕ} (w : Mx D m n) :
    compAt θ τ w = w.map ((θ τ).comp (infPart D)) := rfl

theorem hermC_eq {S T : HSp D} (C : Ctx S T) (σ : C.X.Ψ) (v w : Fin T.rank → ℂ) :
    hermC σ.1 C.X.Gm v w = ∑ a, ∑ b, v a * conj (gramAt D T (C.m.e.symm σ) b a) * conj (w b) := by
  unfold hermC gramAt
  have he := C.m.e_emb (C.m.e.symm σ)
  rw [Equiv.apply_symm_apply] at he
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [C.m.gT, he]
  simp [NumberField.ComplexEmbedding.conjugate_coe_eq]

end GlobalTheory.StabProper

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwoStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitIdempotents_of_relTraceOneModTwo : ∀ (D : D7) (w : D.host.E), IsIntegral ℤ w → w + cc w = 1 → IdemTwo w → ∃ s : Finset (Formalism.L2.Theta.AE D), (∀ e ∈ s, IsSplitIdem D e ∧ ∀ e' ∈ s, e ≠ e' → e * e' = 0 ∧ e * cA D e' = 0) ∧ (∃ a ∈ AddSubgroup.closure {z : Formalism.L2.Theta.AE D | ∃ α ∈ intAf D.host.F, ∃ o : 𝓞 D.host.E, z = pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E)}, pairA D.host.F 0 1 ⊗ₜ[D.host.F] w - ∑ e ∈ s, e = 2 * a) ∧ (∃ a ∈ AddSubgroup.closure {z : Formalism.L2.Theta.AE D | ∃ α ∈ intAf D.host.F, ∃ o : 𝓞 D.host.E, z = pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E)}, pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) - ∑ e ∈ s, (e + cA D e) = 2 * a) ∧ ∀ e, IsSplitIdem D e → e ∈ AddSubgroup.closure {z : Formalism.L2.Theta.AE D | ∃ α ∈ intAf D.host.F, ∃ o : 𝓞 D.host.E, z = pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E)} ∧ (e ∈ s ∨ cA D e ∈ s ∨ ∃ a ∈ AddSubgroup.closure {z : Formalism.L2.Theta.AE D | ∃ α ∈ intAf D.host.F, ∃ o : 𝓞 D.host.E, z = pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E)}, e = 2 * a) := by
  first | exact @GlobalTheory.IdemModTwo.exists_split_idempotents | exact GlobalTheory.IdemModTwo.exists_split_idempotents | (intros; apply GlobalTheory.IdemModTwo.exists_split_idempotents <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchurHeisG
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker

open GlobalTheory.SW.DblZero in

theorem schur_heisG : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ A : TF n g → TF n g, (∀ φ, IsSB φ → IsSB (A φ)) → (∀ φ ψ, IsSB φ → IsSB ψ → A (φ + ψ) = A φ + A ψ) → (∀ (a : ℂ) φ, IsSB φ → A (a • φ) = a • A φ) → (∀ (y : Matrix (Fin n) (Fin r) E) φ, IsSB φ → A (heisG X bas y φ) = heisG X bas y (A φ)) → ∃ c : ℂ, ∀ φ, IsSB φ → A φ = c • φ := by
  intro E _ _ _ r X g q0 hr bas idx n hs _ A hA hadd hsmul hcomm

  obtain ⟨c, hc⟩ := exists_eq_mul_ip (κ := Fin n) (ι := Fin g) (fun φ ψ => ip (A φ) ψ)
    (fun φ φ' ψ hφ hφ' hψ => by
      rw [hadd φ φ' hφ hφ', ip_add_left (hA φ hφ) (hA φ' hφ') hψ])
    (fun φ ψ ψ' hφ hψ hψ' => by
      exact ip_add_right (hA φ hφ) hψ hψ')
    (fun a b φ ψ hφ hψ => by
      rw [hsmul a φ hφ, ip_smul (hA φ hφ) hψ])
    (fun a b φ ψ hφ hψ => by
      obtain ⟨y, hy⟩ := exists_heisG (n := n) hs a b
      rw [← hy φ, hcomm y φ hφ, hy (A φ)]
      exact ((heisS_laws _ _ a b (A φ) (hA φ hφ)).2.2.2.2) ψ hψ)
  refine ⟨c, fun φ hφ => ?_⟩

  have hAφ := hA φ hφ
  have hcφ : IsSB (-c • φ) := ((isSB_algebra_haar_linear _ _ _ φ φ hφ hφ).2.1) (-c)
  have hd : IsSB (A φ + -c • φ) := (isSB_algebra_haar_linear _ _ _ (A φ) (-c • φ) hAφ hcφ).1
  have hzero : ip (A φ + -c • φ) (A φ + -c • φ) = 0 := by
    rw [ip_add_left hAφ hcφ hd, hc φ _ hφ hd]
    have h1 : ip (-c • φ) (A φ + -c • φ) = -c * ip φ (A φ + -c • φ) := by
      have := ip_smul hφ hd (-c) 1
      rw [one_smul, map_one, mul_one] at this
      exact this
    rw [h1]
    ring
  by_contra hne
  have hne' : A φ + -c • φ ≠ 0 := by
    intro h0
    apply hne
    have : A φ = -(-c • φ) := eq_neg_of_add_eq_zero_left h0
    rw [this, neg_smul, neg_neg]
  exact ip_self_ne_zero hd hne' hzero

end GlobalTheory.Ker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumMultiplierTrivialPrincipalCongruenceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuumMultiplier_trivial_principalCongruence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (H : Host E) (Dw : Datum H) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), r = Dw.p + Dw.q → Function.Injective φ → Submodule.span E (Set.range φ) = ⊤ → (∀ a b, ((Dw.EF a b : ℤ) : ℚ) = EF X (φ a) (φ b)) → ∀ L : Lt E r, SelfD X L → ∀ (M : ℕ), 3 ≤ M → ∀ ga : GL (Fin r) E, IsUn X ga → mapL ga L = L → (∀ u ∈ L, ∃ u' ∈ L, (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u') → ∀ v : TF n g, IsVac X bas (H.w0 : E) (tens (stdL E n) L) v → wG X bas idx ga v = v := by
  first | exact @GlobalTheory.VacMult.wG_vac_eq | exact GlobalTheory.VacMult.wG_vac_eq | (intros; apply GlobalTheory.VacMult.wG_vac_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilDoubledTestFunctionZeroEqZeroStatement
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_doubledTestFunction_zero_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → ∀ ξ : Fin r → E, (∃ (s : Finset (Fin n → E)) (a : (Fin n → E) → ℂ), ∑ v ∈ s, a v ≠ 0 ∧ ∑ v ∈ s, a v • heisG X bas (vecMulVec v ξ) φ₁ = 0) → ∀ γ ∈ UU E r, Sum.elim ξ 0 ᵥ* dblT X ∈ botSpan γ → weil X.Ψ γ (dbl X bas idx φ₁ φ₂) 0 = 0 := by
  first | exact @GlobalTheory.SW.weil_dbl_zero_eq_zero | exact GlobalTheory.SW.weil_dbl_zero_eq_zero | (intros; apply GlobalTheory.SW.weil_dbl_zero_eq_zero <;> assumption)
end

