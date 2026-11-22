import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0259
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0007
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0131
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0156
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0139
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0260

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnisotropicUnitaryGroupCompact
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.CompactField

section Shell

variable {K W : Type} [NontriviallyNormedField K] [NormedAddCommGroup W] [NormedSpace K W] [ProperSpace W]

theorem exists_lower_bound (P : W → ℝ) (hc : Continuous P) (hpos : ∀ w, w ≠ 0 → 0 < P w)
    (hom : ∀ (t : K) w, P (t • w) = ‖t‖ ^ 2 * P w) : ∃ m : ℝ, 0 < m ∧ ∀ w, m * ‖w‖ ^ 2 ≤ P w := by
  obtain ⟨k, hk⟩ := NormedField.exists_one_lt_norm K
  have hk0 : 0 < ‖k‖ := by linarith
  set S : Set W := Metric.closedBall 0 1 \ Metric.ball 0 (1 / ‖k‖) with hS
  have hSc : IsCompact S := (isCompact_closedBall (0 : W) 1).diff Metric.isOpen_ball
  have hP0 : P 0 = 0 := by
    have := hom 0 0
    simpa using this
  have key : ∃ m : ℝ, 0 < m ∧ ∀ w ∈ S, m ≤ P w := by
    rcases S.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨x, hx, hmin⟩ := hSc.exists_isMinOn h hc.continuousOn
      have hx0 : x ≠ 0 := by
        rintro rfl
        apply hx.2
        simp only [Metric.mem_ball, dist_self]
        positivity
      exact ⟨P x, hpos x hx0, fun w hw => hmin hw⟩
  obtain ⟨m, hm, hmS⟩ := key
  refine ⟨m, hm, fun w => ?_⟩
  by_cases hw : w = 0
  · simp [hw, hP0]
  obtain ⟨d, hd0, hd1, hd2, -⟩ := rescale_to_shell hk one_pos hw
  have hmem : d • w ∈ S := ⟨by simpa using hd1.le, by simpa using hd2⟩
  have h1 := hmS _ hmem
  rw [hom] at h1
  have hd' : 0 < ‖d‖ := norm_pos_iff.2 hd0
  have hnorm : ‖d‖ * ‖w‖ < 1 := by simpa [norm_smul] using hd1
  have hPw := hpos w hw
  have hnn : 0 ≤ ‖d‖ * ‖w‖ := mul_nonneg hd'.le (norm_nonneg w)
  have h2 : (‖d‖ * ‖w‖) ^ 2 ≤ 1 := by nlinarith
  have h3 : ‖d‖ ^ 2 * (m * ‖w‖ ^ 2) ≤ ‖d‖ ^ 2 * P w := by nlinarith
  exact le_of_mul_le_mul_left h3 (by positivity)

end Shell

section Bound

variable {K R : Type} [NontriviallyNormedField K] [ProperSpace K] [CommRing R] [Algebra K R] [Module.Finite K R]
  [TopologicalSpace R] [IsModuleTopology K R]

theorem continuous_of_fix (c : R →+* R) (hc : ∀ t : K, c (algebraMap K R t) = algebraMap K R t) : Continuous c := by
  haveI : IsTopologicalRing R := IsModuleTopology.isTopologicalRing K R
  let cl : R →ₗ[K] R :=
    { toFun := c
      map_add' := map_add c
      map_smul' := fun t x => by simp [Algebra.smul_def, hc] }
  exact IsModuleTopology.continuous_of_linearMap cl

theorem hform_smul {M : ℕ} (c : R →+* R) (hc : ∀ t : K, c (algebraMap K R t) = algebraMap K R t)
    (J : Matrix (Fin M) (Fin M) R) (t : K) (u : Fin M → R) :
    Formalism.UG.hform c J (t • u) (t • u) = (t ^ 2) • Formalism.UG.hform c J u u := by
  unfold Formalism.UG.hform
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, Algebra.smul_def, map_mul, hc, map_pow]
  ring

theorem hform_col {M : ℕ} (c : R →+* R) (J g : Matrix (Fin M) (Fin M) R) (j : Fin M) :
    Formalism.UG.hform c J (fun i => g i j) (fun i => g i j) = (Formalism.UG.cT c g * J * g) j j := by
  unfold Formalism.UG.hform Formalism.UG.cT
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem exists_compact_entries {M : ℕ} (c : R →+* R) (hc : ∀ t : K, c (algebraMap K R t) = algebraMap K R t)
    (J : Matrix (Fin M) (Fin M) R) (hne : ∀ u : Fin M → R, u ≠ 0 → Formalism.UG.hform c J u u ≠ 0) :
    ∃ C : Set R, IsCompact C ∧
      ∀ g : Matrix (Fin M) (Fin M) R, Formalism.UG.cT c g * J * g = J → ∀ i j, g i j ∈ C := by
  haveI : IsTopologicalRing R := IsModuleTopology.isTopologicalRing K R
  let e : R ≃ₗ[K] (Fin (Module.finrank K R) → K) := (Module.finBasis K R).equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hes : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  have hcc : Continuous c := continuous_of_fix c hc
  let U : (Fin M → Fin (Module.finrank K R) → K) → (Fin M → R) := fun w i => e.symm (w i)
  have hU : Continuous U := continuous_pi fun i => hes.comp (continuous_apply i)
  let Q : (Fin M → R) → R := fun u => Formalism.UG.hform c J u u
  have hQ : Continuous Q := by
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact ((hcc.comp (continuous_apply i)).mul continuous_const).mul (continuous_apply j)
  let P : (Fin M → Fin (Module.finrank K R) → K) → ℝ := fun w => ‖e (Q (U w))‖
  have hP : Continuous P := (he.comp (hQ.comp hU)).norm
  have hUinj : ∀ w, w ≠ 0 → U w ≠ 0 := by
    intro w hw h
    apply hw
    funext i
    have := congrFun h i
    simpa [U] using this
  have hpos : ∀ w, w ≠ 0 → 0 < P w := by
    intro w hw
    refine norm_pos_iff.2 fun h => ?_
    exact hne _ (hUinj w hw) (e.map_eq_zero_iff.1 h)
  have hom : ∀ (t : K) w, P (t • w) = ‖t‖ ^ 2 * P w := by
    intro t w
    have h1 : U (t • w) = t • U w := by
      funext i
      simp [U]
    simp only [P, Q]
    rw [h1, hform_smul c hc, map_smul, norm_smul, norm_pow]
  obtain ⟨m, hm, hmP⟩ := exists_lower_bound (K := K) P hP hpos hom
  let A : ℝ := ∑ j, ‖e (J j j)‖
  have hA : ∀ j, ‖e (J j j)‖ ≤ A := fun j =>
    Finset.single_le_sum (f := fun j => ‖e (J j j)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  refine ⟨e.symm '' Metric.closedBall 0 (Real.sqrt (A / m)),
    (isCompact_closedBall _ _).image hes, fun g hg i j => ?_⟩
  refine ⟨e (g i j), ?_, e.symm_apply_apply _⟩
  let w : Fin M → Fin (Module.finrank K R) → K := fun i => e (g i j)
  have hw : P w = ‖e (J j j)‖ := by
    have h1 : U w = fun i => g i j := by
      funext i
      simp [U, w]
    simp only [P, Q]
    rw [h1, hform_col, hg]
  have h2 := hmP w
  rw [hw] at h2
  have h3 : ‖w‖ ^ 2 ≤ A / m := by
    rw [le_div_iff₀ hm]
    linarith [hA j]
  have h4 : ‖w‖ ≤ Real.sqrt (A / m) := Real.le_sqrt_of_sq_le h3
  have h5 : ‖e (g i j)‖ ≤ ‖w‖ := norm_le_pi_norm w i
  simpa using h5.trans h4

end Bound

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

section Main

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_algebraMap_left (K : Type) [CommRing K] [Algebra F K] (σ : E →ₐ[F] E) (t : K) :
    sigR K σ (algebraMap K (K ⊗[F] E) t) = algebraMap K (K ⊗[F] E) t := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem sigR_sigR (K : Type) [CommRing K] [Algebra F K] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (z : K ⊗[F] E) :
    sigR K σ (sigR K σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR, hσ]
  | add y z hy hz => rw [map_add, map_add, hy, hz]

theorem hform_ne_zero (K : Type) [CommRing K] [Algebra F K] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) (hf : IsField (K ⊗[F] E)) (hiso : ¬ IsoAt K σ J)
    (u : Fin M → K ⊗[F] E) (hu : u ≠ 0) : Formalism.UG.hform (sigR K σ) (JR (F := F) K J) u u ≠ 0 := by
  intro h0
  have hdet : IsUnit (JR (F := F) K J).det := by
    unfold JR
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hJ).map _
  set c := sigR K σ with hc
  let y : Fin M → K ⊗[F] E := Matrix.vecMul (fun i => c (u i)) (JR (F := F) K J)
  have hy : y ≠ 0 := by
    intro hy0
    have h1 : (fun i => c (u i)) = 0 := by
      have h2 := congrArg (fun v => Matrix.vecMul v (JR (F := F) K J)⁻¹) hy0
      simp only [y, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one, Matrix.zero_vecMul] at h2
      exact h2
    apply hu
    funext i
    have h3 := congrArg c (congrFun h1 i)
    simpa [hc, sigR_sigR K σ hσ] using h3
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  obtain ⟨b, hb⟩ := hf.mul_inv_cancel hj
  refine hiso ⟨u, Pi.single j b, h0, ?_⟩
  have h4 : Formalism.UG.hform c (JR (F := F) K J) u (Pi.single j b) = y j * b := by
    unfold Formalism.UG.hform
    simp only [y, Matrix.vecMul, dotProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · simp
  exact h4.trans hb

end Main

theorem isCompact_univ_HA : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ {K : Type} [NontriviallyNormedField K] [ProperSpace K] [Algebra F K], IsField (K ⊗[F] E) → ¬ IsoAt K σ J →
      IsCompact (Set.univ : Set (HA K σ J)) := by
  intro F E _ _ _ _ _ σ hσ M J hJ K _ _ _ hfield hiso
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology K (K ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (K ⊗[F] E) := IsModuleTopology.isTopologicalRing K _
  let e : (K ⊗[F] E) ≃ₗ[K] (Fin (Module.finrank K (K ⊗[F] E)) → K) := (Module.finBasis K (K ⊗[F] E)).equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  haveI : T2Space (K ⊗[F] E) := T2Space.of_injective_continuous e.injective he
  have hc := sigR_algebraMap_left (F := F) (E := E) K σ
  obtain ⟨C, hC, hCg⟩ := exists_compact_entries (K := K) (sigR K σ) hc (JR (F := F) K J)
    (hform_ne_zero K σ (GlobalTheory.CompanionTheory.SaGen.CompactField.sigma_sigma hσ) J hJ.2 hfield hiso)
  have hcs : Continuous (sigR (F := F) (E := E) K σ) := continuous_of_fix (K := K) _ hc
  have hcl : IsClosed (HR K σ J : Set (GL (Fin M) (K ⊗[F] E))) := by
    have hv : Continuous fun g : GL (Fin M) (K ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (K ⊗[F] E)) :=
      Units.continuous_val
    exact isClosed_eq (((hv.matrix_map hcs).matrix_transpose.matrix_mul continuous_const).matrix_mul hv)
      continuous_const
  have hemb : Topology.IsClosedEmbedding fun g : HR K σ J => Units.embedProduct _ g.1 :=
    Units.isClosedEmbedding_embedProduct.comp hcl.isClosedEmbedding_subtypeVal
  let S : Set (Matrix (Fin M) (Fin M) (K ⊗[F] E)) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  have hK := hemb.isCompact_preimage (hS.prod (hS.image MulOpposite.continuous_op))
  have huniv : (fun g : HR K σ J => Units.embedProduct _ g.1) ⁻¹'
      (S ×ˢ (MulOpposite.op '' S)) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    exact ⟨fun i _ j _ => hCg _ g.2 i j, (g⁻¹).1.1, fun i _ j _ => hCg _ (g⁻¹).2 i j, rfl⟩
  rw [huniv] at hK
  exact hK

end GlobalTheory.CompanionTheory.SaGen.CompactField
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterValuesIntegralStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_values_integral : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ),
    Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)) →
    ∀ g, ∃ a : ↥(OL K), (a : ↥K.1) = ((χ g : (↥K.1)ˣ) : ↥K.1) := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.IntVal.integral_values | exact GlobalTheory.CompanionTheory.LTPer.IntVal.integral_values | (intros; apply GlobalTheory.CompanionTheory.LTPer.IntVal.integral_values <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartRestrictPullBijective
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeZarCap

attribute [local instance] MvPolynomial.gradedAlgebra

theorem inU_inf {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (V W : X.Opens) (T : Thick (nlFun γ p X q κ)) :
    InU (V ⊓ W) T ↔ InU V T ∧ InU W T := by
  unfold InU
  rw [← le_inf_iff]
  exact Iff.rfl

theorem irrelevant_le_span (K : Type) [Field K] (N : ℕ) :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K)) := by
  intro x hx
  rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hx
  have h0 : MvPolynomial.coeff 0 x = 0 := by
    erw [MvPolynomial.decomposition.decompose'_apply, MvPolynomial.homogeneousComponent_zero] at hx
    exact MvPolynomial.C_eq_zero.1 hx
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  by_contra hne
  have hm0 : m = 0 := Finsupp.ext fun i => by
    by_contra hi
    exact hne ⟨i, Set.mem_univ i, hi⟩
  subst hm0
  exact (MvPolynomial.mem_support_iff.1 hm) h0

theorem iSup_wch {K : Type} [Field K] {X : Scheme.{0}} (N : ℕ) (i : X ⟶ PSpace K N) : (⨆ j, wch i j) = ⊤ := by
  have h := AlgebraicGeometry.Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
    (fun j => MvPolynomial.X j) (irrelevant_le_span K N)
  simp only [wch]
  rw [← Scheme.Hom.preimage_iSup, h, Scheme.Hom.preimage_top]

theorem resU_eq {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r r' : ℤ) :
    resU (sq (thFil L r) (thFil L r')) h = (incl h).sq (incl_fil h r) (incl_fil h r') := by
  unfold resU CrystallineSemistableComparison.Pb.SMor.sq
  congr 1
  funext T
  refine LinearMap.ext fun x => Subtype.ext ?_
  obtain ⟨z, hz⟩ := x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

private theorem isHecke_div_and_resEtaPow_div {X : Scheme.{0}} {m N : ℕ} (u : Fin m → X.Opens) (w : Fin (N + 1) → X.Opens)
    (hw : (⨆ j, w j) = ⊤) (S : Finset (Fin m)) :
    (⨅ k ∈ S, u k) ≤ ⨆ c : Fin m → Fin (N + 1), ⨅ k ∈ S, (u k ⊓ w (c k)) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · exact le_iSup_of_le (fun _ => 0) (by simp)
  · intro a S ha ih
    rw [Finset.iInf_insert]
    calc u a ⊓ ⨅ k ∈ S, u k ≤ (⨆ j, u a ⊓ w j) ⊓ ⨆ c : Fin m → Fin (N + 1), ⨅ k ∈ S, (u k ⊓ w (c k)) :=
          inf_le_inf (by rw [← inf_iSup_eq, hw, inf_top_eq]) ih
      _ = ⨆ j, ⨆ c : Fin m → Fin (N + 1), (u a ⊓ w j) ⊓ ⨅ k ∈ S, (u k ⊓ w (c k)) := by
          rw [iSup_inf_eq]
          simp_rw [inf_iSup_eq]
      _ ≤ ⨆ c : Fin m → Fin (N + 1), ⨅ k ∈ insert a S, (u k ⊓ w (c k)) := by
          refine iSup_le fun j => iSup_le fun c => le_iSup_of_le (Function.update c a j) ?_
          rw [Finset.iInf_insert]
          refine inf_le_inf (by simp) (le_iInf₂ fun k hk => (iInf₂_le k hk).trans ?_)
          have hka : k ≠ a := fun h => ha (h ▸ hk)
          simp [hka]

theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ) (S : Finset (Fin m)) (hS : S.Nonempty)
    (r r' : ℤ) (j : ℕ),
    ∃ h : capS (wK q i y s) S ≤ KS q s {⨅ k ∈ S, uy i y k},
      Function.Bijective ((resU (sq (thFil (smFun X q) r) (thFil (smFun X q) r')) h).pull j) := by
  intro K _ X q N m i y s S hS r r' j
  classical
  have e : capS (wK q i y s) S = KS q s (Set.range fun c : Fin m → Fin (N + 1) => ⨅ k ∈ S, (uy i y k ⊓ wch i (c k))) := by
    funext T
    apply propext
    constructor
    · intro hT
      obtain ⟨k0, hk0⟩ := hS
      refine ⟨(hT k0 hk0).1, ?_⟩
      have hc : ∀ k, ∃ c : Fin (N + 1), k ∈ S → InU (uy i y k ⊓ wch i c) T := by
        intro k
        by_cases hk : k ∈ S
        · obtain ⟨_, V, ⟨c, rfl⟩, hV⟩ := hT k hk
          exact ⟨c, fun _ => hV⟩
        · exact ⟨0, fun h => absurd h hk⟩
      choose c hc using hc
      exact ⟨_, ⟨c, rfl⟩, (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (fun k => uy i y k ⊓ wch i (c k)) S _).2 hc⟩
    · rintro ⟨hT, V, ⟨c, rfl⟩, hV⟩ k hk
      exact ⟨hT, _, ⟨c k, rfl⟩, (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (fun k => uy i y k ⊓ wch i (c k)) S _).1 hV k hk⟩
  rw [e]
  have hle : KS q s (Set.range fun c : Fin m → Fin (N + 1) => ⨅ k ∈ S, (uy i y k ⊓ wch i (c k))) ≤
      KS q s {⨅ k ∈ S, uy i y k} := by
    rintro T ⟨hT, V, ⟨c, rfl⟩, hV⟩
    refine ⟨hT, _, Set.mem_singleton _, (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (uy i y) S _).2 fun k hk => ?_⟩
    exact ((inU_inf _ _ _).1 ((GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (fun k => uy i y k ⊓ wch i (c k)) S _).1 hV k hk)).1
  have hc : ∀ W ∈ ({⨅ k ∈ S, uy i y k} : Set X.Opens),
      W ≤ sSup (Set.range fun c : Fin m → Fin (N + 1) => ⨅ k ∈ S, (uy i y k ⊓ wch i (c k))) := by
    intro W hW
    rw [Set.mem_singleton_iff] at hW
    subst hW
    rw [sSup_range]
    exact isHecke_div_and_resEtaPow_div (uy i y) (wch i) (iSup_wch N i) S
  refine ⟨hle, ?_⟩
  rw [resU_eq]
  exact (GlobalTheory.CompanionTheory.NlZar.zariski_descent (CrystallineSemistableComparison.Pb.TF 1 s) (Or.inl ⟨rfl, 1, s, rfl⟩) _ _ hle hc j).1 r r'

end GlobalTheory.CompanionTheory.ConeZarCap
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartTensorBaseCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.BcMor

theorem chart_mor : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {V : X.Opens} {d : ℕ} (cV : Coord q V d),
    letI := (strV q V).toAlgebra
    ∀ (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) V d) (cA : Chart γ 0 q (κA O I) V d)
      (eO : O ⊗[O] Γ(X, V) ≃+* cO.D.B) (eA : A ⊗[O] Γ(X, V) ≃+* cA.D.B),
      (∀ r, eO (r ⊗ₜ 1) = cO.D.i r) → (∀ r, eA (r ⊗ₜ 1) = cA.D.i r) →
      (∀ f, ev cO.D cO.inV f = Ideal.Quotient.mk _ (eO (1 ⊗ₜ f))) →
      (∀ f, ev cA.D cA.inV f = Ideal.Quotient.mk _ (eA (1 ⊗ₜ f))) →
      ∃ e₀ : cO.D ⟶ ((nmO γ q).mor 0).obj cA.D, ∀ f, e₀.φ (eO (1 ⊗ₜ f)) = eA (1 ⊗ₜ f) := by
  intro O A _ _ _ I γ X q V d cV
  letI a0 : Algebra O Γ(X, V) := (strV q V).toAlgebra
  intro cO cA eO eA hO hA hvO hvA
  have hptT : pt (((nmO γ q).mor 0).obj cA.D) = pt cA.D := Category.comp_id _
  have hT : InU V (((nmO γ q).mor 0).obj cA.D) := by
    unfold InU
    rw [hptT]
    exact cA.inV
  obtain ⟨g, hg, -⟩ := cO.rep (CommRingCat.of ((((nmO γ q).mor 0).obj cA.D).B ⧸ (((nmO γ q).mor 0).obj cA.D).J))
    (((nmO γ q).mor 0).obj cA.D).y hT
  have hg' : (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)).Pt.map (CommRingCat.ofHom g) cO.D.y =
      (((nmO γ q).mor 0).obj cA.D).y := hg
  let ι : O ⊗[O] Γ(X, V) →+* A ⊗[O] Γ(X, V) :=
    (Algebra.TensorProduct.map (Algebra.ofId O A) (AlgHom.id O Γ(X, V))).toRingHom
  let φ : cO.D.B →+* cA.D.B := (eA.toRingHom.comp ι).comp eO.symm.toRingHom
  have hφ : ∀ f, φ (eO (1 ⊗ₜ f)) = eA (1 ⊗ₜ f) := fun f => by
    change eA (ι (eO.symm (eO (1 ⊗ₜ f)))) = _
    rw [RingEquiv.symm_apply_apply]
    change eA (Algebra.TensorProduct.map (Algebra.ofId O A) (AlgHom.id O Γ(X, V)) (1 ⊗ₜ f)) = _
    simp
  have hf : ∀ r, φ (cO.D.i r) = (((nmO γ q).mor 0).obj cA.D).i r := fun r => by
    change eA (ι (eO.symm (cO.D.i r))) = cA.D.i (algebraMap O A r)
    rw [← hO r, RingEquiv.symm_apply_apply, ← hA]
    change eA (Algebra.TensorProduct.map (Algebra.ofId O A) (AlgHom.id O Γ(X, V)) (r ⊗ₜ 1)) = _
    simp [Algebra.ofId_apply]
  have hptg : pt (((nmO γ q).mor 0).obj cA.D) = Spec.map (CommRingCat.ofHom g) ≫ pt cO.D := by
    unfold pt
    rw [← hg']
    rfl
  have hev : ∀ f, ev cA.D cA.inV f = g (ev cO.D cO.inV f) := fun f => by
    have key : ∀ (y : Spec (CommRingCat.of (cA.D.B ⧸ cA.D.J)) ⟶ X) (_ : y = Spec.map (CommRingCat.ofHom g) ≫ pt cO.D)
        (h'' : ⊤ ≤ y ⁻¹ᵁ V), GlobalTheory.Cris.evalAt y V h'' f = g (ev cO.D cO.inV f) := by
      intro y hy h''
      subst hy
      exact GlobalTheory.LogCris.evalAt_map _ (pt cO.D) cO.inV h'' f
    exact key _ (hptT.symm.trans hptg) cA.inV
  have hq : (Ideal.Quotient.mk (((nmO γ q).mor 0).obj cA.D).J).comp φ = g.comp (Ideal.Quotient.mk cO.D.J) := by
    refine RingHom.ext fun x => ?_
    obtain ⟨f, rfl⟩ : ∃ f, x = eO (1 ⊗ₜ f) := by
      refine ⟨TensorProduct.lid O Γ(X, V) (eO.symm x), ?_⟩
      have e : (1 : O) ⊗ₜ[O] (TensorProduct.lid O Γ(X, V) (eO.symm x)) = eO.symm x :=
        (TensorProduct.lid O Γ(X, V)).symm_apply_apply (eO.symm x)
      rw [e, RingEquiv.apply_symm_apply]
    change Ideal.Quotient.mk cA.D.J (φ (eO (1 ⊗ₜ f))) = g (Ideal.Quotient.mk cO.D.J (eO (1 ⊗ₜ f)))
    rw [hφ, ← hvA, ← hvO, hev]
  exact ⟨GlobalTheory.CompanionTheory.ChartMaps.homOf cO (((nmO γ q).mor 0).obj cA.D) φ hf g hq hg', hφ⟩

end GlobalTheory.CompanionTheory.BcMor
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentSubobjectCoherentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coherent_subobject_coherent : ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] {E : X.Modules}, IsCoherent E → ∀ D : Subobject E, (D : X.Modules).IsQuasicoherent → IsCoherent (D : X.Modules) := by
  first | exact @GlobalTheory.CompanionTheory.GE.isCoherent_subobject | exact GlobalTheory.CompanionTheory.GE.isCoherent_subobject | (intros; apply GlobalTheory.CompanionTheory.GE.isCoherent_subobject <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordNear
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeLocal

theorem coord_near : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] {V' : X.Opens}, IsAffineOpen V' → ∀ x : X, x ∈ V' →
    ∃ (f : Γ(X, V')) (e : ℕ) (c : Coord q (X.basicOpen f) e), x ∈ X.basicOpen f := by
  intro K _ X q _ V' hV x hx
  have h : RingHom.Locally RingHom.IsStandardSmooth (q.appLE ⊤ V' le_top).hom :=
    RingHom.smooth_iff_locally_isStandardSmooth.1 (q.smooth_appLE (isAffineOpen_top _) hV le_top)
  obtain ⟨f, hf, hst⟩ := GlobalTheory.CompanionTheory.CovEx.exists_basicOpen RingHom.IsStandardSmooth
    RingHom.isStandardSmooth_respectsIso q hV h hx
  obtain ⟨n, g, hg, he⟩ := hst.exists_etale_mvPolynomial
  exact ⟨f, n, (GlobalTheory.CompanionTheory.CovEx.coord_basicOpen q hV f g hg he).some, hf⟩

end GlobalTheory.CompanionTheory.ConeLocal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetOneUnitaryClosed
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen

theorem isClosed_det_eq_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {K : Type} [NontriviallyNormedField K] [Algebra F K], IsClosed {x : HA K σ J | ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1} := by
  intro F E _ _ _ _ _ σ _ M J K _ _
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (K ⊗[F] E) := GlobalTheory.CompanionTheory.SW.TopK.isTopRing K
  haveI : T2Space (K ⊗[F] E) :=
    (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo K (Module.finBasis F E)).isEmbedding.t2Space
  have hc : Continuous fun x : HA K σ J =>
      ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  exact isClosed_eq hc.matrix_det continuous_const

end GlobalTheory.CompanionTheory.SaGen

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChowCoverIntegralStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chow_cover_integral : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] [IsIntegral X], ∃ (N : ℕ) (Y : Scheme.{0}) (i : Y ⟶ projectiveSpace A N) (O : Y.Opens) (ψ : (O : Scheme.{0}) ⟶ X) (W : X.Opens), IsClosedImmersion i ∧ IsProper ψ ∧ O.ι ≫ i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A)) ∧ (W : Set X).Nonempty ∧ IsIso (ψ ∣_ W) := by
  first | exact @GlobalTheory.CompanionTheory.GE.ChowOpen.exists_chow_open | exact GlobalTheory.CompanionTheory.GE.ChowOpen.exists_chow_open | (intros; apply GlobalTheory.CompanionTheory.GE.ChowOpen.exists_chow_open <;> assumption)
end

