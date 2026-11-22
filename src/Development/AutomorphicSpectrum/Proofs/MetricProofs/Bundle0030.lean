import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0028
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0005
import Development.WeilBound.CoreStatements.AmpleLineBundles.SpanLeOfMem
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0007
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0003
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0011
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizationGlueC2Explicit
import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0039
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0006

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeLeRankMulSlopeStatement
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalized_degree_le_rank_mul_slope : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (μ : ℝ), E.slopeMax ≤ (μ : EReal) → ∀ F : Submodule (𝓞 K) E.carrier, E.normDegree F ≤ E.rank F * μ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DegSlope.normDegree_le_rank_mul_of_slopeMax_le | exact GlobalTheory.CompanionTheory.Ar.DegSlope.normDegree_le_rank_mul_of_slopeMax_le | (intros; apply GlobalTheory.CompanionTheory.Ar.DegSlope.normDegree_le_rank_mul_of_slopeMax_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeOrthogonalSum
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.OrthSum

variable {K : Type} [Field K] [NumberField K]

theorem disjoint_of_orth (E : HermitianBundle.{0} K) {F G : Submodule (𝓞 K) E.carrier}
    (h : OrthAt E F G) : Disjoint F G := by
  rw [Submodule.disjoint_def]
  intro x hxF hxG
  by_contra hx
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hli : LinearIndependent (𝓞 K) (fun _ : Unit => x) := linearIndependent_unique_iff.mpr hx
  have hpos := gramDet_pos E.metric σ hli
  have h0 := h σ x hxF x hxG
  rw [← FibreSpace.inner_equiv E.metric σ] at h0
  have h0' : inner ℂ (fibreVec E.metric σ x) (fibreVec E.metric σ x) = 0 := h0
  have hz : GroundTheory.Heights₂.Heights.gramDet E.metric σ (fun _ : Unit => x) = 0 := by
    unfold GroundTheory.Heights₂.Heights.gramDet
    rw [Matrix.det_unique, Matrix.gram_apply, h0', Complex.zero_re]
  linarith

theorem gramDet_sumElim (E : HermitianBundle.{0} K) (σ : K →+* ℂ) {a b : ℕ}
    {s : Fin a → E.carrier} {t : Fin b → E.carrier} (hs : LinearIndependent (𝓞 K) s)
    (ht : LinearIndependent (𝓞 K) t)
    (h : ∀ i j, inner ℂ (fibreVec E.metric σ (s i)) (fibreVec E.metric σ (t j)) = 0) :
    gramDet E.metric σ (Sum.elim s t) = gramDet E.metric σ s * gramDet E.metric σ t := by
  have hconj : ∀ i j, inner ℂ (fibreVec E.metric σ (t j)) (fibreVec E.metric σ (s i)) = 0 := by
    intro i j
    rw [← inner_conj_symm, h i j, map_zero]
  have hM : (Matrix.gram ℂ fun k => fibreVec E.metric σ (Sum.elim s t k)) =
      Matrix.fromBlocks (Matrix.gram ℂ fun i => fibreVec E.metric σ (s i)) 0 0
        (Matrix.gram ℂ fun j => fibreVec E.metric σ (t j)) := by
    ext (i | i) (j | j) <;>
      simp only [Matrix.gram_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, h, hconj]
  have him : ∀ {n : ℕ} (v : Fin n → FibreSpace E.metric σ), (Matrix.gram ℂ v).det.im = 0 := by
    intro n v
    have hA : (Matrix.gram ℂ v).conjTranspose = Matrix.gram ℂ v := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.gram_apply]
      exact inner_conj_symm _ _
    have hdet := Matrix.det_conjTranspose (Matrix.gram ℂ v)
    rw [hA] at hdet
    exact Complex.conj_eq_iff_im.mp hdet.symm
  unfold GroundTheory.Heights₂.Heights.gramDet
  rw [hM, Matrix.det_fromBlocks_zero₂₁, Complex.mul_re, him, him, mul_zero, sub_zero]

theorem degree_sup (E : HermitianBundle.{0} K) {F G : Submodule (𝓞 K) E.carrier}
    (h : OrthAt E F G) : E.degree (F ⊔ G) = E.degree F + E.degree G := by
  have hd : Disjoint F G := disjoint_of_orth E h
  obtain ⟨s, hs, hsF⟩ := CoverDenseAlt.exists_fam E F
  obtain ⟨t, ht, htG⟩ := CoverDenseAlt.exists_fam E G
  have hNs : Submodule.span (𝓞 K) (Set.range s) ≤ F := CoverDenseAlt.span_le_of_mem hsF
  have hNt : Submodule.span (𝓞 K) (Set.range t) ≤ G := CoverDenseAlt.span_le_of_mem htG
  have hst : LinearIndependent (𝓞 K) (Sum.elim s t) := hs.sum_type ht (hd.mono hNs hNt)
  have hmem : ∀ i, Sum.elim s t i ∈ F ⊔ G := by
    rintro (i | i)
    · exact Submodule.mem_sup_left (hsF i)
    · exact Submodule.mem_sup_right (htG i)
  have hcard : Fintype.card (Fin (E.rank F) ⊕ Fin (E.rank G)) = E.rank (F ⊔ G) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, CoverDenseAlt.rank_sup E hd]
  obtain ⟨hiF, hF⟩ := CoverDenseAlt.deg_eq E F hs hsF (Fintype.card_fin _)
  obtain ⟨hiG, hG⟩ := CoverDenseAlt.deg_eq E G ht htG (Fintype.card_fin _)
  obtain ⟨-, hFG⟩ := CoverDenseAlt.deg_eq E (F ⊔ G) hst hmem hcard
  have hidx : CoverDenseAlt.idx (Submodule.span (𝓞 K) (Set.range (Sum.elim s t))) (F ⊔ G) =
      CoverDenseAlt.idx (Submodule.span (𝓞 K) (Set.range s)) F * CoverDenseAlt.idx (Submodule.span (𝓞 K) (Set.range t)) G := by
    rw [Set.Sum.elim_range, Submodule.span_union,
      ← CoverDenseAlt.idx_mul (sup_le_sup_right hNs _) (sup_le_sup_left hNt F)]
    congr 1
    · exact CoverDenseAlt.idx_sup hNs (hd.mono_right hNt)
    · rw [sup_comm F, sup_comm F G]
      exact CoverDenseAlt.idx_sup hNt hd.symm
  have hlog : ∀ σ : K →+* ℂ, Real.log (GroundTheory.Heights₂.Heights.gramDet E.metric σ (Sum.elim s t)) =
      Real.log (GroundTheory.Heights₂.Heights.gramDet E.metric σ s) + Real.log (GroundTheory.Heights₂.Heights.gramDet E.metric σ t) := by
    intro σ
    have hgram := gramDet_sumElim E σ hs ht (fun i j => by
      have h1 := h σ _ (hsF i) _ (htG j)
      rw [← FibreSpace.inner_equiv E.metric σ] at h1
      exact h1)
    rw [hgram, Real.log_mul (gramDet_pos E.metric σ hs).ne' (gramDet_pos E.metric σ ht).ne']
  rw [hFG, hF, hG, hidx, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hiF) (Nat.cast_ne_zero.mpr hiG)]
  simp only [hlog, Finset.sum_add_distrib]
  ring

theorem degree_bot (E : HermitianBundle.{0} K) : E.degree ⊥ = 0 := by
  have hrk : Fintype.card (Fin 0) = E.rank ⊥ := by
    unfold GroundTheory.Heights₂.Heights.HermitianBundle.rank
    simp
  obtain ⟨-, hdeg⟩ := CoverDenseAlt.deg_eq E ⊥ (s := (Fin.elim0 : Fin 0 → E.carrier)) linearIndependent_empty_type
    (fun i => i.elim0) hrk
  have h1 : CoverDenseAlt.idx (Submodule.span (𝓞 K) (Set.range (Fin.elim0 : Fin 0 → E.carrier))) ⊥ = 1 := by
    rw [CoverDenseAlt.idx_eq_card]
    refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => ?_⟩, ⟨0⟩⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Subsingleton.elim a b]
  have hg : ∀ σ : K →+* ℂ, GroundTheory.Heights₂.Heights.gramDet E.metric σ (Fin.elim0 : Fin 0 → E.carrier) = 1 := by
    intro σ
    unfold GroundTheory.Heights₂.Heights.gramDet
    rw [Matrix.det_isEmpty, Complex.one_re]
  rw [hdeg, h1]
  simp only [hg, Real.log_one, Nat.cast_one, Finset.sum_const_zero, mul_zero, sub_zero]

theorem orth_biSup (E : HermitianBundle.{0} K) {F : Submodule (𝓞 K) E.carrier} {I : Type}
    (G : I → Submodule (𝓞 K) E.carrier) (S : Finset I) (h : ∀ b ∈ S, OrthAt E F (G b)) :
    OrthAt E F (⨆ b ∈ S, G b) := by
  classical
  intro σ x hx y hy
  obtain ⟨μ, rfl⟩ := (Submodule.mem_iSup_finset_iff_exists_sum G y).mp hy
  rw [← FibreSpace.inner_equiv E.metric σ]
  have hfv : fibreVec E.metric σ (∑ b ∈ S, (μ b : E.carrier)) = ∑ b ∈ S, fibreVec E.metric σ (μ b) := by
    simpa using fibreVec_sum E.metric σ S (fun _ => 1) (fun b => (μ b : E.carrier))
  change inner ℂ (fibreVec E.metric σ x) (fibreVec E.metric σ (∑ b ∈ S, (μ b : E.carrier))) = 0
  rw [hfv, inner_sum]
  refine Finset.sum_eq_zero fun b hb => ?_
  have h1 := h b hb σ x hx _ (μ b).2
  rw [← FibreSpace.inner_equiv E.metric σ] at h1
  exact h1

theorem degree_rank_biSup (E : HermitianBundle.{0} K) {I : Type}
    (F : I → Submodule (𝓞 K) E.carrier) (h : ∀ a b, a ≠ b → OrthAt E (F a) (F b)) (S : Finset I) :
    E.degree (⨆ a ∈ S, F a) = ∑ a ∈ S, E.degree (F a) ∧
      E.rank (⨆ a ∈ S, F a) = ∑ a ∈ S, E.rank (F a) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · have hb : (⨆ a ∈ (∅ : Finset I), F a) = ⊥ := by simp
    rw [hb, Finset.sum_empty, Finset.sum_empty]
    refine ⟨degree_bot E, ?_⟩
    unfold GroundTheory.Heights₂.Heights.HermitianBundle.rank
    simp
  · intro a S ha ih
    rw [Finset.iSup_insert, Finset.sum_insert ha, Finset.sum_insert ha]
    have horth : OrthAt E (F a) (⨆ b ∈ S, F b) :=
      orth_biSup E F S fun b hb => h a b fun hab => ha (hab ▸ hb)
    refine ⟨?_, ?_⟩
    · rw [degree_sup E horth, ih.1]
    · rw [CoverDenseAlt.rank_sup E (disjoint_of_orth E horth), ih.2]

theorem normDegree_rank_iSup : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (I : Type) [Fintype I] (F : I → Submodule (𝓞 K) E.carrier), (∀ a b, a ≠ b → OrthAt E (F a) (F b)) → E.normDegree (⨆ a, F a) = ∑ a, E.normDegree (F a) ∧ E.rank (⨆ a, F a) = ∑ a, E.rank (F a) := by
  intro K _ _ E I _ F h
  have hU : (⨆ a, F a) = ⨆ a ∈ (Finset.univ : Finset I), F a := by simp
  obtain ⟨hd, hr⟩ := degree_rank_biSup E F h Finset.univ
  rw [hU]
  refine ⟨?_, hr⟩
  unfold GroundTheory.Heights₂.Heights.HermitianBundle.normDegree
  rw [hd, Finset.sum_div]

end GlobalTheory.CompanionTheory.Ar.OrthSum
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodMatrixLocalTrivializationStatement
section
open Matrix Metric GroundTheory.Heights₂.Heights.Regular GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_matrix_local_trivialization : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : LogPeriods n a g Λ), ∃ (Q : PeriodPolydisc n a g) (A : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ i j, DifferentiableOn ℂ (fun z => A z i j) (ball 0 1)) ∧ (A 0).det ≠ 0 ∧ ∀ w ∈ logCover L.a_le, A (expCover a w) * L.H (expCover a w) * (A (expCover a w))ᴴ = (((Q.τ w).map Complex.im)⁻¹).map Complex.ofReal := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_periodPolydisc_frame | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_periodPolydisc_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_periodPolydisc_frame <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PolarIdentityFromSymmetricForms
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem coefficient_identities_give_operator_identity : ∀ (σ : Type) [Fintype σ] (D : ℕ) (a : (Fin (D + 1) → σ) → ℝ) (b : (Fin D → σ) → ℝ) (κ : ℕ → ℝ) (ε : σ → ℤ) (a₀ : σ), (∀ (π : Equiv.Perm (Fin (D + 1))) w, a (w ∘ π) = a w) → (∀ (π : Equiv.Perm (Fin D)) w, b (w ∘ π) = b w) → (∀ n : σ → ℤ, n a₀ = 0 → polar (D + 1) a (fun _ x => (n x : ℝ)) = 0 ∧ ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D + 1 → polar (D + 1) a (mix (2 * k) (fun x => (ε x : ℝ)) fun x => (n x : ℝ)) = -(2 * κ k) * polar D b (mix (2 * k - 1) (fun x => (ε x : ℝ)) fun x => (n x : ℝ))) → ∀ (c : σ → ℝ), c a₀ = 0 → ∀ u : ℝ, eval (fun x => c x - u / 2 * ε x) (formPoly (D + 1) a) + eval (fun x => c x + u / 2 * ε x) (formPoly (D + 1) a) = (tsgPoly D κ (linePoly c ε (formPoly D b))).eval u :=
  @PositivityTheory.Xgp.t_thma_alg

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PtsIntegralConjLineEq
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

namespace GlobalTheory.CompanionTheory.Ar.Tw

theorem ptsIntegral_conjLine : PtsIndepStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι), IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn Q A s → ptsIntegral Q (pot fun j => conjLine (L j)) (logNorm (conjLine A) s) = ptsIntegral Q (pot L) (logNorm A s) := by
  intro hI K _ ι _ Q e L A s hQ hL hA hs
  exact GlobalTheory.CompanionTheory.Ar.Cmp.arInt_conj
    (fun K _ ι _ P e Ψ L A s hP hΨ hL hA hs => sheetIndep K ι P e Ψ L A s hP hΨ hL hA hs) hI
    (fun K _ ι _ P e hP => goodProjExists K ι P e hP) K ι Q e L A s hQ hL hA hs

end GlobalTheory.CompanionTheory.Ar.Tw
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.QuotientLatticeByIsotropicSubmodule
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.quotient_lattice_by_isotropic_submodule : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (I : Submodule (𝓞 E) Λ), IsSaturated I → IsIsoSub R.form I → ∃ (g' : ℕ) (Λ' : Type) (_ : AddCommGroup Λ') (_ : Module (𝓞 E) Λ') (R' : RiemLat E g' Λ') (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), Function.Surjective q ∧ LinearMap.ker q = Submodule.span ℂ (R.P '' I) ∧ (∀ a x, q (R.B a x) = R'.B a (q x)) ∧ Set.range R'.P = q '' (R.P '' {x | ∀ y ∈ I, R.form x y = 0}) ∧ ∀ x y, (∀ v ∈ I, R.ip (R.P v) x = 0) → R'.ip (q x) (q y) = R.ip x y := by
  first | exact @LevelTowerAlt.isotropic_quotient_lattice | exact LevelTowerAlt.isotropic_quotient_lattice
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationFibreProductCompatible
section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem sameSing_of_isoLine : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k) (P : Ideal (MRing ι)) (P₁ : Ideal (MRing ι₁)) (P₂ : Ideal (MRing ι₂)) (D : ℕ) (σ₁ σ₂ : Type) (S₁ : PB.AnSys D σ₁) (S₂ : PB.AnSys D σ₂) (Re₁ : PB.Realis S₁ P₁) (Re₂ : PB.Realis S₂ P₂) (β : MRing ι) (a₁ : σ₁) (a₂ : σ₂) (A₁ : HermLine ι₁) (A₂ : HermLine ι₂) (A₁' A₂' : HermLine ι), IsBlockMap κ₁ v₁ → IsBlockMap κ₂ v₂ → IsPullHerm κ₁ v₁ A₁ A₁' → IsPullHerm κ₂ v₂ A₂ A₂' → (Re₁.ref a₁).a = A₁.a → (Re₂.ref a₂).a = A₂.a → (∀ x, Re₁.π x ∉ ReciprocityTheory.AnForm.P.bdry S₁.s → Real.log (A₁.h (Re₁.R.lift x x)) = Real.log ((Re₁.ref a₁).h (Re₁.R.lift x x)) + S₁.ph a₁ (Re₁.π x)) → (∀ x, Re₂.π x ∉ ReciprocityTheory.AnForm.P.bdry S₂.s → Real.log (A₂.h (Re₂.R.lift x x)) = Real.log ((Re₂.ref a₂).h (Re₂.R.lift x x)) + S₂.ph a₂ (Re₂.π x)) → IsMultiProjPrime P → IsoLineOn P {z | z ∈ mcPts P ∧ evC z β ≠ 0} A₁' A₂' → SameSing Re₁ Re₂ P κ₁ v₁ κ₂ v₂ β a₁ a₂ :=
  @PositivityTheory.UnitarySelfGeneration.h_samesing

end GlobalTheory.CompanionTheory.Ar.Cmp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationPullbackCompatibleStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisation_pullback_compatible : ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k', ι' k') → Ω) (S' : AnSys D σ) (Re' : Realis S' (mCoordIdeal y)) (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')), IsBlockMap κ v → imageZ v (mCoordIdeal y) = P → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ a, IsPullHerm κ v (Re.line a t) (Re'.line a t)) → Re'.deg = IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) * Re.deg → Re'.PB II = Re.PB II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.pb_indep_cover | exact GlobalTheory.CompanionTheory.Ar.PB.pb_indep_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.pb_indep_cover <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizationGlueC2ExplicitStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularization_glue_C2_explicit : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A B : FinHolAtlas e X) (Θ th : LocPot X) (s : X → X → ℂ) (ph : X → ℝ), A.Compatible B → (∀ x, ∃ j, x ∈ chartBall B j 1) → (∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target) → IsPotential A Θ → IsPosPot A Θ → IsPotential A th → IsClosed (bdry s) → A.SmoothOn (bdry s)ᶜ ph → ∃ K : ℝ, 0 < K ∧ ∀ (t₀ : ℝ) (δ : ℝ → ℝ) (f : ℝ → Fin B.n → X → ℝ), 0 < t₀ → Tendsto δ (𝓝[>] 0) (𝓝 0) → (∀ t, 0 < t → t ≤ t₀ → t ≤ δ t ∧ δ t ≤ 1 ∧ (∀ j, A.SmoothOn (chartBall B j (5 / 4)) (f t j)) ∧ (∃ Mb : ℝ, ∀ j, ∀ y ∈ chartBall B j (5 / 4), |f t j y| ≤ Mb) ∧ (∀ j, IsPshOn A (chartBall B j (5 / 4)) (th + LocPot.ofFun (f t j))) ∧ ∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4), |f t j y - f t k y| ≤ δ t) → (∀ j, ∀ K' ⊆ ball (0 : Fin e → ℂ) (5 / 4) ∩ (B.chart j).symm ⁻¹' (bdry s)ᶜ, IsCompact K' → TendstoUniformlyOn (fun t => f t j ∘ (B.chart j).symm) (ph ∘ (B.chart j).symm) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (f t j ∘ (B.chart j).symm)) (fderiv ℝ (ph ∘ (B.chart j).symm)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (f t j ∘ (B.chart j).symm))) (fderiv ℝ (fderiv ℝ (ph ∘ (B.chart j).symm))) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ (f t j ∘ (B.chart j).symm) z - fderiv ℝ (ph ∘ (B.chart j).symm) z‖ ≤ M * t) → ∃ F : ℝ → X → ℝ, (∀ t, 0 < t → t ≤ t₀ → A.Smooth (F t) ∧ IsPsh A (th + LocPot.ofFun (F t) + Θ.rsmul (K * δ t)) ∧ ∀ j, ∀ y ∈ chartBall B j (5 / 4), f t j y ≤ F t y ∧ F t y ≤ f t j y + K * δ t) ∧ IsRegFamilyC2 A s ph F := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.regularization_glue_C2 | exact GlobalTheory.CompanionTheory.Ar.Giv.regularization_glue_C2 | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.regularization_glue_C2 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjection
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.riemann_lattice_eigen_projection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ), Function.Injective R.P ∧ Submodule.span ℝ (Set.range R.P) = ⊤ ∧ (∀ s : 𝓞 E →+* ℂ, (∀ x, eigComp R.B s x ∈ eigSp R.B s) ∧ (∀ x ∈ eigSp R.B s, eigComp R.B s x = x) ∧ (∀ (c : ℂ) x y, eigComp R.B s (c • x + y) = c • eigComp R.B s x + eigComp R.B s y) ∧ ∀ a x, eigComp R.B s (R.B a x) = s a • eigComp R.B s x) ∧ (∀ x, ∑ s : E →+* ℂ, eigComp R.B (s.comp (algebraMap (𝓞 E) E)) x = x) ∧ ∀ s s' : 𝓞 E →+* ℂ, s ≠ s' → ∀ x ∈ eigSp R.B s, ∀ y ∈ eigSp R.B s', R.ip x y = 0 := by
  first | exact @LevelTowerAlt.riemann_lattice_eigen_projections | exact LevelTowerAlt.riemann_lattice_eigen_projections
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ShiftHEqTensorConstLine
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem shiftH_eq_tensor_constLine {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (A : HermLine ι) (t : ℝ) :
    shiftH A t = A.tensor (ReciprocityTheory.ChartRestriction.G.AI.I2.constLine (-t)) := by
  unfold shiftH ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor ReciprocityTheory.ChartRestriction.G.AI.I2.constLine
    ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight
  congr 1
  · exact (add_zero _).symm
  · funext z
    show Real.exp t * A.h z = A.h z * Real.exp (-(-t))
    rw [neg_neg, mul_comm]

theorem selfInt_shiftH : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ)
    (A : HermLine ι) (t : ℝ) (II : IntersectionSystem), IsIntersectionSystem II → IsArithVar P (D + 1) →
    IsSmoothHerm A →
    II K ι P (D + 1) (fun _ => shiftH A t) =
      II K ι P (D + 1) (fun _ => A) + ((D : ℝ) + 1) * t * geomDeg P A D := by
  intro K _ ι _ P D A t II hII hP hA
  have h := GroundTheory.Heights₂.Heights.HilbertSamuel.TopConstantTwist.proof K ι P D A (-t) II hII hP hA
  rw [shiftH_eq_tensor_constLine, h]
  push_cast
  ring

end GlobalTheory.CompanionTheory.Ar.Small
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SphereMeasureStereographicIntegral
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.sphere_measure_stereographic_integral : let n : ℂ → Fin 3 → ℝ := (fun (a : ℂ) (i : Fin 3) => (![2 * a.re, 2 * a.im, 1 - ‖a‖ ^ 2] : Fin 3 → ℝ) i / (1 + ‖a‖ ^ 2)); (∀ f : (Fin 3 → ℝ) → ℝ, Measurable f → (Integrable (fun a : ℂ => f (n a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) ↔ Integrable (fun m : ReciprocityTheory.ChartRestriction.G.AI.S2 => f fun i => (m : ReciprocityTheory.ChartRestriction.G.AI.E3) i) ReciprocityTheory.ChartRestriction.G.AI.sphereMeasure) ∧ ∫ a : ℂ, f (n a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2) = ∫ m : ReciprocityTheory.ChartRestriction.G.AI.S2, f (fun i => (m : ReciprocityTheory.ChartRestriction.G.AI.E3) i) ∂ ReciprocityTheory.ChartRestriction.G.AI.sphereMeasure) ∧ ∀ a₀ a₁ : ℂ, logSin 1 a₀ a₁ = (1 / 2) * Real.log ((1 - ∑ i, n a₀ i * n a₁ i) / 2) := by
  intro n
  exact ⟨PositivityTheory.Xgp.fib_stereo.measure_part, PositivityTheory.Xgp.fib_stereo.logSin_part⟩
end

