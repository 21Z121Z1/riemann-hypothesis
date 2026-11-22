import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1015
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0953
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0556
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0582
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0075
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFinitenessGl1Unramified
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.TwFinGL1

theorem twisted_finiteness_gl1 : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ δ N : GL (Fin 1) (Qr p r),
    GlobalTheory.TwFin.TwFin (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) (GlobalTheory.LKLoc.Kint p (Q0 p) 1 r) δ N := by
  intro p _ r hr δ N E
  refine ⟨{1}, fun t _ _ => ?_⟩
  obtain ⟨u, hu, k, hk, htk⟩ :=
    GlobalTheory.LKLoc.GLOneUnit.exists_decomp p (Q0 p) r inferInstance hr δ t
  exact ⟨u, hu, 1, Finset.mem_singleton_self _, k, hk, by rw [htk, mul_one]⟩

end GlobalTheory.TwFinGL1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHeckeTestFunctionSupportCompactStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedHeckeTestFunction_support_compact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∃ Ω : Set G.GAf, IsCompact Ω ∧ ∀ g, f g ≠ 0 → g ∈ Ω := by
  first | (exact @GlobalTheory.isTest_support_compact) | (exact GlobalTheory.isTest_support_compact) | (intros; apply GlobalTheory.isTest_support_compact  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormProductIterateTwistedConjStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedNormProductIterate_twistedConj : ∀ {H : Type} [Group H] (θ : H →* H) (r : ℕ) (δ g : H), nrmG θ r (g⁻¹ * δ * θ g) = g⁻¹ * nrmG θ r δ * (⇑θ)^[r] g ∧ δ * θ (nrmG θ r δ) = nrmG θ r δ * (⇑θ)^[r] δ := by
  first | (exact @GlobalTheory.LKMid.nrmG_twConj) | (exact GlobalTheory.LKMid.nrmG_twConj) | (intros; apply GlobalTheory.LKMid.nrmG_twConj  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.UnitaryAdelicTop

theorem isClosed_UG {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [TopologicalSpace B] [IsTopologicalRing B]
    [T2Space B] (c : B →ₐ[A] B) (hc : Continuous c) {n : ℕ} (J : Matrix (Fin n) (Fin n) B) :
    IsClosed (UG c J : Set (GL (Fin n) B)) := by
  have hv : Continuous fun g : GL (Fin n) B => (g : Matrix (Fin n) (Fin n) B) := Units.continuous_val
  exact isClosed_eq (((hv.matrix_transpose).matrix_mul continuous_const).matrix_mul (hv.matrix_map hc)) continuous_const

theorem lcsc_UA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E), IsTopologicalGroup (UA σ J) ∧ LocallyCompactSpace (UA σ J) ∧
      SecondCountableTopology (UA σ J) ∧ T2Space (UA σ J) := by
  intro F E _ _ _ _ _ σ n J
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin n) (AE F E)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) (AE F E)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : T2Space (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.t2Space
  have hσ : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hc := isClosed_UG (cA σ) hσ (incM F J)
  exact ⟨inferInstance, hc.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology, inferInstance⟩

end GlobalTheory.UnitaryAdelicTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPointExtOfComponents
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem finiteAdeleRingAway_eq_of_forall_eval_eq {p : ℕ} {x y : AfP p} (h : ∀ v : AwayP p, AfP.eval v x = AfP.eval v y) : x = y :=
  RestrictedProduct.ext (R := fun v : AwayP p => v.1.adicCompletion ℚ) _ h

theorem basV_repr_map {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (x : AfP p ⊗[ℚ] G.C)
    (i : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C) x) i =
      AfP.eval v ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    simp only [basV, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem ext_of_piV : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (g g' : G.GAf),
    (∀ v : AwayP p, piV G v g = piV G v g') → g = g' := by
  intro p _ G g g' h
  have h1 : ∀ v : AwayP p, Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)
      (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) =
      Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)
      (((g' : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) := fun v =>
    congrArg (fun z : Gv G v => (((z : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : Qv v ⊗[ℚ] G.C))) (h v)
  have h2 : ∀ v : AwayP p, AfP.eval v (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p)) =
      AfP.eval v (((g' : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p)) := fun v =>
    congrArg (fun z : Gv G v => (((z : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : Qv v))) (h v)
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    apply (Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).ext_elem
    intro i
    apply finiteAdeleRingAway_eq_of_forall_eval_eq
    intro v
    rw [← basV_repr_map, ← basV_repr_map, h1 v]
  · apply Units.ext
    exact finiteAdeleRingAway_eq_of_forall_eval_eq h2

end GlobalTheory.OrbFinAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFramesStrongApproximation
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem GlobalTheory.ClassSum.sum_covolume_le : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M m : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (X : Fin m → Data E r) (g : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (x0 : ∀ i, Frame (X i).Ψ r) (S : Finset (Fin m)) (g0 : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), 2 ≤ r → 3 ≤ M → Unr E → SelfDualLat G Λ → IsUA (IsCMField.complexConj E) G g0 → (∀ i, IsUA (IsCMField.complexConj E) G (g i)) → (∀ i ∈ S, TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M g0.det (g i).det) → (∀ i ∈ S, ∀ j ∈ S, UEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M (g i) (g j) → i = j) → (∀ i ∈ S, (X i).Gm = G ∧ (X i).Ψ = Ψ ∧ ((X i).Λ : Set (Fin r → E)) = latOf (maximalRealSubfield E) (g i) (Λ : Set (Fin r → E)) ∧ (∀ γ, γ ∈ (X i).Γ ↔ IsUStab G (X i).Λ γ ∧ ∀ x ∈ (X i).Λ, ∃ y ∈ (X i).Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) ∧ IsOrth (X i) (x0 i)) → ∑ i ∈ S, covolume (inReal (X i).Ψ (X i).Gm (X i).Γ) (realSU (X i).Ψ (X i).Gm) (riemHaar (X i).Ψ (X i).Gm (x0 i)) ≤ ENNReal.ofReal ((M : ℝ) ^ (2 * fdeg E * r ^ 2) * rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E) := by
  intro hP E _ _ _ r M m G Λ Ψ X g x0 S g0 hr hM hU hΛ hg0 hg hT hUE hX
  classical
  rcases S.eq_empty_or_nonempty with hS | ⟨i0, hi0⟩
  · subst hS; simp
  obtain ⟨hG0, hΨ0, -, -, hO0⟩ := hX i0 hi0
  subst hG0
  subst hΨ0
  obtain ⟨L, hLset, hLhat, hL⟩ := GlobalTheory.T.self_dual_lattice_real_completion E r (X i0).Gm Λ g0 hΛ hg0
  obtain ⟨γ, s, hγs, hpair⟩ := GlobalTheory.T.self_dual_lattice_congruence_subgroups E r M m (X i0).Gm Λ L g g0 S (fun i => (X i).Γ) (fun i => (X i).Λ)
    (by omega) hΛ hg0 hLset hLhat hg hT (fun i hi => ⟨(hX i hi).2.2.1, (hX i hi).2.2.2.1⟩)
  have hherm : ∀ a b, cc ((X i0).Gm a b) = (X i0).Gm b a := (X i0).Gm_herm
  have tr : ∀ (Ψ1 : Finset (E →+* ℂ)) (G1 : Matrix (Fin r) (Fin r) E) (x1 : Frame Ψ1 r) (p1 : ℕ)
      (H : Subgroup (GL (Fin r) E)), Ψ1 = (X i0).Ψ → G1 = (X i0).Gm →
      (∀ τ : Ψ1, gram τ.1 G1 (mat x1 τ) = Matrix.diagonal fun a : Fin r => ((sgn p1 (a : ℕ) : ℝ) : ℂ)) →
      covolume (inReal Ψ1 G1 H) (realSU Ψ1 G1) (riemHaar Ψ1 G1 x1) =
        covolume (inReal (X i0).Ψ (X i0).Gm H) (realSU (X i0).Ψ (X i0).Gm) (riemHaar (X i0).Ψ (X i0).Gm (x0 i0)) := by
    intro Ψ1 G1 x1 p1 H h1 h2 h3
    subst h1 h2
    rw [GlobalTheory.T.riemannianHaar_independent_of_orthonormal_frame E r p1 (X i0).p0 _ _ x1 (x0 i0) hherm h3 hO0]
  set Δ : Fin m → Subgroup (GL (Fin r) E) := fun i => ((X i).Γ).map (MulAut.conj (γ i)⁻¹).toMonoidHom with hΔ
  have hback : ∀ i, (Δ i).map (MulAut.conj (γ i)).toMonoidHom = (X i).Γ := by
    intro i
    rw [hΔ, Subgroup.map_map]
    have : (MulAut.conj (γ i)).toMonoidHom.comp (MulAut.conj (γ i)⁻¹).toMonoidHom = MonoidHom.id _ := by
      ext δ : 1
      simp [mul_assoc]
    rw [this, Subgroup.map_id]
  have hterm : ∀ i ∈ S, covolume (inReal (X i).Ψ (X i).Gm (X i).Γ) (realSU (X i).Ψ (X i).Gm)
      (riemHaar (X i).Ψ (X i).Gm (x0 i)) =
      covolume (inReal (X i0).Ψ (X i0).Gm (Δ i)) (realSU (X i0).Ψ (X i0).Gm) (riemHaar (X i0).Ψ (X i0).Gm (x0 i0)) := by
    intro i hi
    obtain ⟨hGi, hΨi, -, -, hOi⟩ := hX i hi
    rw [tr (X i).Ψ (X i).Gm (x0 i) (X i).p0 (X i).Γ hΨi hGi hOi, ← hback i]
    exact GlobalTheory.T.hermitian_gram_diagonal_signature_unitary E r (X i0).p0 (X i0).Ψ (X i0).Gm (x0 i0) (γ i) (Δ i) hherm hO0 (hγs i hi).1
  obtain ⟨J, t, ht, hcount⟩ := GlobalTheory.T.signature_unitary_lattice_family E r M (X i0).p0 (X i0).Gm L (X i0).Ψ (x0 i0) (Fin m) S s Δ hr
    (by omega) hL (X i0).cmType hO0 (fun i hi => (hγs i hi).2.1)
    (fun i hi j hj h => hUE i hi j hj (hpair i hi j hj h)) (fun i hi => (hγs i hi).2.2)
  have hV := GlobalTheory.T.real_unitary_covolume_sum hP E r (X i0) L (x0 i0) J t hr hU hL hO0 ht
  rw [Finset.sum_congr rfl hterm]
  refine hcount.trans ?_
  calc (M : ℝ≥0∞) ^ (2 * fdeg E * r ^ 2) * ∑' j, covolume (inReal (X i0).Ψ (X i0).Gm (ratStab (X i0).Gm (L : Set (Fin r → E)) (t j))) (realSU (X i0).Ψ (X i0).Gm) (riemHaar (X i0).Ψ (X i0).Gm (x0 i0))
      ≤ (M : ℝ≥0∞) ^ (2 * fdeg E * r ^ 2) * ENNReal.ofReal (rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E) := by
        gcongr
    _ = _ := by
        rw [mul_assoc ((M : ℝ) ^ (2 * fdeg E * r ^ 2)), ENNReal.ofReal_mul (p := (M : ℝ) ^ (2 * fdeg E * r ^ 2)) (by positivity),
          ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedConjugatePlaceUniformiser
section
open IsDedekindDomain NumberField

namespace GlobalTheory.FixedPrime

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem le_of_under_le (P : Ideal (𝓞 E)) [hP : P.IsPrime]
    (h : ∀ x : 𝓞 E, IsCMField.ringOfIntegersComplexConj E x ∈ P → x ∈ P) (Q : Ideal (𝓞 E))
    (hQ : Q.under (𝓞 (maximalRealSubfield E)) ≤ P.under (𝓞 (maximalRealSubfield E))) : Q ≤ P := by
  intro y hy
  obtain ⟨s, hs⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E
    (y * IsCMField.ringOfIntegersComplexConj E y)).1 (by
      rw [map_mul, mul_comm]
      congr 1
      ext; simp)
  have h1 : s ∈ Q.under (𝓞 (maximalRealSubfield E)) := by
    rw [Ideal.under_def, Ideal.mem_comap, hs]
    exact Q.mul_mem_right _ hy
  have h2 := hQ h1
  rw [Ideal.under_def, Ideal.mem_comap, hs] at h2
  exact (hP.mem_or_mem h2).elim id (h y)

theorem isInertAt_under [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (P : HeightOneSpectrum (𝓞 E))
    (h : ∀ x : 𝓞 E, IsCMField.ringOfIntegersComplexConj E x ∈ P.asIdeal → x ∈ P.asIdeal) :
    Formalism.UG.IsInertAt (maximalRealSubfield E) E (P.under (𝓞 (maximalRealSubfield E))) P := by
  classical
  haveI := P.isPrime
  haveI : Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) P.asIdeal :=
    Algebra.unramified_iff_forall.1 inferInstance ⟨P.asIdeal, P.isPrime⟩
  set v := P.under (𝓞 (maximalRealSubfield E)) with hv
  have hva : v.asIdeal = P.asIdeal.under (𝓞 (maximalRealSubfield E)) := rfl
  have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective _ _
  unfold Formalism.UG.IsInertAt
  rw [hva]
  have hle : (P.asIdeal.under (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ P.asIdeal := Ideal.map_comap_le
  have h1 : Ideal.ramificationIdx' (P.asIdeal.under (𝓞 (maximalRealSubfield E))) P.asIdeal = 1 := by
    letI := Localization.AtPrime.algebraOfLiesOver (P.asIdeal.under (𝓞 (maximalRealSubfield E))) P.asIdeal
    exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff P.ne_bot hle).2
      ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 (maximalRealSubfield E))
        (P.asIdeal.under (𝓞 (maximalRealSubfield E))) P.asIdeal).1 ‹_›).2
  have h2 : ¬ (P.asIdeal.under (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ P.asIdeal ^ 2 :=
    fun h => (Ideal.ramificationIdx'_ne_one_iff hle).2 h h1
  set I := Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))
    (P.asIdeal.under (𝓞 (maximalRealSubfield E))) with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    exact v.ne_bot
  have hfac : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors I, p = P.asIdeal := by
    intro p hp
    obtain ⟨hpp, hpl⟩ := (Ideal.mem_normalizedFactors_iff hI0).1 hp
    have hp0 : p ≠ ⊥ := fun h0 => hI0 (le_bot_iff.1 (h0 ▸ hpl))
    refine (hpp.isMaximal hp0).eq_of_le P.isPrime.ne_top (le_of_under_le P.asIdeal h p ?_)
    exact (v.isMaximal.eq_of_le (Ideal.comap_ne_top _ hpp.ne_top)
      (Ideal.map_le_iff_le_comap.1 hpl)).ge
  obtain ⟨n, hn⟩ : ∃ n, I = P.asIdeal ^ n := by
    refine ⟨Multiset.card (UniqueFactorizationMonoid.normalizedFactors I), ?_⟩
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI0]
    rw [Multiset.eq_replicate_card.2 hfac, Multiset.prod_replicate, Multiset.card_replicate]
  rcases n with _ | _ | n
  · exfalso
    rw [hn, pow_zero, Ideal.one_eq_top, top_le_iff] at hle
    exact P.isPrime.ne_top hle
  · simpa using hn
  · exact absurd (hn ▸ Ideal.pow_le_pow_right (by omega)) h2

theorem exists_isUnramInv [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E))
    (h : Formalism.UG.IsInertAt (maximalRealSubfield E) E v P) :
    ∃ (σ : P.adicCompletion E →+* P.adicCompletion E) (ϖ : P.adicCompletion E),
      (∀ x : E, σ (algebraMap E (P.adicCompletion E) x) =
        algebraMap E (P.adicCompletion E) (IsCMField.complexConj E x)) ∧
      Formalism.UG.IsUnramInv ϖ σ (Ideal.absNorm v.asIdeal) := by
  obtain ⟨σ, ϖ, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.InertConj.exists_conj_completion E v P h
  refine ⟨σ, ϖ, h1, h2, h3, h5, h6, h4, ?_, ?_⟩
  · have a : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have b : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    omega
  · have hN : Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
      rw [← show Ideal.map _ v.asIdeal = P.asIdeal from h, Ideal.absNorm_algebraMap,
        ← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E]
      congr 1
      exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)
        (𝓞 E) E).symm
    rw [← hN]
    exact Formalism.UG.P.tjcosets_card_residue P

end CM

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isConjAt_isUnramInv : ∀ {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal → ∃ (σ : P.adicCompletion D.host.E →+* P.adicCompletion D.host.E) (ϖ : P.adicCompletion D.host.E) (q : ℕ), IsConjAt P σ ∧ Formalism.UG.IsUnramInv ϖ σ q := by
  intro D P hP
  haveI := D.host.isCMField_hostE
  haveI := GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm
  have h := isInertAt_under P fun x hx => by
    rw [← hP, Formalism.L2.Col.mem_conjIdeal]
    exact hx
  obtain ⟨σ, ϖ, h1, h2⟩ := exists_isUnramInv _ P h
  exact ⟨σ, ϖ, _, h1, h2⟩

end GlobalTheory.FixedPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedExtensionBasisStatement
section
open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes GlobalTheory.LKRes.ResSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_extension_basis : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), 0 < r → ∀ (ζ : Qr p r), IsPrimitiveRoot (ζ : PadicAlgCl p) (p ^ r - 1) → ∀ x : KQ p K r, ∃ c : Fin r → K, x = ∑ j : Fin r, inclK p K r (c j) * inclQ p K r ζ ^ (j : ℕ) := by
  first | exact @GlobalTheory.LKRes.ResSplit.KQ_eq_sum_pow | exact GlobalTheory.LKRes.ResSplit.KQ_eq_sum_pow | (intros; apply GlobalTheory.LKRes.ResSplit.KQ_eq_sum_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationAlgHomEqOfInertPrime
section
open NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace GlobalTheory.InertConjVal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def phiO (φ : E →ₐ[F] E) : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (φ : E →+* E)

theorem coe_phiO (φ : E →ₐ[F] E) (y : 𝓞 E) : ((phiO φ y : 𝓞 E) : E) = φ (y : E) := rfl

theorem phiO_comp (φ : E →ₐ[F] E) :
    (phiO φ).comp (algebraMap (𝓞 F) (𝓞 E)) = algebraMap (𝓞 F) (𝓞 E) := by
  refine RingHom.ext fun f => RingOfIntegers.ext ?_
  rw [RingHom.comp_apply, coe_phiO]
  have h : ((algebraMap (𝓞 F) (𝓞 E) f : 𝓞 E) : E) = algebraMap F E (f : F) := rfl
  rw [h]
  exact φ.commutes _

theorem map_phiO_pow (φ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) (n : ℕ) :
    Ideal.map (phiO φ) (w.asIdeal ^ n) = w.asIdeal ^ n := by
  unfold Formalism.UG.IsInertAt at hin
  rw [← hin, ← Ideal.map_pow, Ideal.map_map, phiO_comp]

theorem intVal_phi_le (φ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) (y : 𝓞 E) :
    w.intValuation (phiO φ y) ≤ w.intValuation y := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [map_zero]
  have h0 : w.intValuation y ≠ 0 := w.intValuation_ne_zero y hy
  have h1 : w.intValuation y ≤ 1 := w.intValuation_le_one y
  set k := WithZero.log (w.intValuation y) with hk
  have hek : w.intValuation y = WithZero.exp k := (WithZero.exp_log h0).symm
  have hk0 : k ≤ 0 := by
    rw [hek, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    exact h1
  have hn : w.intValuation y = WithZero.exp (-(((-k).toNat : ℕ) : ℤ)) := by
    rw [hek, Int.toNat_of_nonneg (by omega), neg_neg]
  have hm : y ∈ w.asIdeal ^ (-k).toNat := (w.intValuation_le_pow_iff_mem y _).1 hn.le
  rw [hn]
  refine (w.intValuation_le_pow_iff_mem _ _).2 ?_
  rw [← map_phiO_pow φ v w hin]
  exact Ideal.mem_map_of_mem _ hm

theorem bij (σ : E →ₐ[F] E) : Function.Bijective σ := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact σ.bijective

theorem intVal_phi (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) (y : 𝓞 E) :
    w.intValuation (phiO σ y) = w.intValuation y := by
  refine le_antisymm (intVal_phi_le σ v w hin y) ?_
  let τ : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (bij σ)
  have h := intVal_phi_le (τ.symm : E →ₐ[F] E) v w hin (phiO σ y)
  have e : phiO (τ.symm : E →ₐ[F] E) (phiO σ y) = y := by
    apply RingOfIntegers.ext
    rw [coe_phiO, coe_phiO]
    show τ.symm (τ (y : E)) = (y : E)
    exact τ.symm_apply_apply _
  rwa [e] at h

theorem val_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w → ∀ x : E, w.valuation E (σ x) = w.valuation E x := by
  intro F E _ _ _ _ _ σ v w hin x
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  rw [map_div₀, map_div₀, map_div₀]
  have e : ∀ y : 𝓞 E, σ (algebraMap (𝓞 E) E y) = algebraMap (𝓞 E) E (phiO σ y) := fun y => rfl
  rw [e, e, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    intVal_phi σ v w hin, intVal_phi σ v w hin]

end GlobalTheory.InertConjVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationAlgebraMapEqOfInertPlace
section
open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory.InertValRestr

theorem liesOver_of_isInertAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) : w.asIdeal.LiesOver v.asIdeal := by
  refine ⟨?_⟩
  have hP : w.asIdeal.IsPrime := w.isPrime
  have hc : (w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).IsPrime := inferInstance
  refine v.isMaximal.eq_of_le hc.ne_top ?_
  show v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
  rw [← hin]
  exact Ideal.le_comap_map

theorem ramificationIdx'_eq_one_of_isInertAt {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) : v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
  have hP : w.asIdeal.IsPrime := w.isPrime
  apply Ideal.ramificationIdx'_spec
  · rw [hin, pow_one]
  · rw [hin]
    exact not_le_of_gt (Ideal.pow_succ_lt_pow w.ne_bot 1 |>.trans_eq (pow_one _))

theorem valuation_algebraMap_of_isInertAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w → ∀ x : F, w.valuation E (algebraMap F E x) = v.valuation F x := by
  intro F E _ _ _ _ _ v w hin x
  have := liesOver_of_isInertAt v w hin
  rw [← HeightOneSpectrum.valuation_liesOver (K := F) E v w x,
    ramificationIdx'_eq_one_of_isInertAt v w hin, pow_one]

end GlobalTheory.InertValRestr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VoganNormSqHolomorphicLowestKTypeSubRootLtStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.voganNormSq_holomorphicLowestKType_sub_root_lt : ∀ (n p : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → (∀ a, ε a = decide ((a : ℕ) < p)) → ∀ a c : Fin n, ε a = true → ε c = false → vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam - Formalism.REAL.root a c) < vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) := by
  first | exact @GlobalTheory.HolDict.vNormSq_lowK_sub_noncompact_root_lt | exact GlobalTheory.HolDict.vNormSq_lowK_sub_noncompact_root_lt | (intros; apply GlobalTheory.HolDict.vNormSq_lowK_sub_noncompact_root_lt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VoganNormSqLtOfRemoveNoncompactRootStatement
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.voganNormSq_lt_of_remove_noncompactRoot : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), StrictAnti lam → IsHolChamber ε lam → ∀ a b : Fin n, ε a = true → ε b = false → vNormSq ε (lowK ε lam - root a b) < vNormSq ε (lowK ε lam) := by
  first | exact @GlobalTheory.HolomorphicRootNormBound.vNormSq_lt_of_root | exact GlobalTheory.HolomorphicRootNormBound.vNormSq_lt_of_root | (intros; apply GlobalTheory.HolomorphicRootNormBound.vNormSq_lt_of_root <;> assumption)
end

