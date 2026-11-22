import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0339
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0379
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0381
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0380
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0382
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1259
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0350
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOrbitCoefficientSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0378
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0266

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTypeIwahoriMaximalCompactIdempotentFamily
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

noncomputable section

namespace GlobalTheory.TrIdem

theorem isIntegralOp_smoothOp {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G W} (hρ : GlobalTheory.PRep.IsSmooth ρ) {f : G → ℂ} (hf : IsLocallyConstant f ∧ HasCompactSupport f) :
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ ρ f (smoothOp ρ μ f) := by
  intro v l
  have hi := hρ.smoothOp_integrand hf.1 hf.2 v
  refine ⟨?_, ?_⟩
  · simpa [smul_eq_mul] using integrable_map (μ := μ) hi.1 hi.2 l l.map_zero
  · rw [hρ.map_smoothOp (μ := μ) hf.1 hf.2 l v]
    simp [smul_eq_mul]

theorem isSmooth_comp_locFin {D : D7} {V : HSp D} {W : Type} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GfC V) W} (hσ : GlobalTheory.PRep.IsSmooth σ) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.PRep.IsSmooth (σ.comp (locFin V v)) := fun x =>
  (hσ x).preimage ((continuous_emb D.sp.cm.sig V.gram v).subtype_mk _)

set_option maxHeartbeats 2000000 in

theorem exists_idemFam : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), U.u ∉ T.S → ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∃ e, IsFinFamily D.sp.cm.sig V.gram (frameLat V) e ∧ (∀ v : T.S, e v = T.idem μf v) ∧ (∀ v, conv (μf v) (e v) (e v) = e v) ∧ (∀ k ∈ U.frame.iwahori, ∀ g, e U.u (k * g) = e U.u g) ∧ SphRest T U e ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → HasTypeVec T σ → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V e) P → P ≠ 0 := by
  intro D V T U hu μf hH h1 ν hν
  refine ⟨fam T U μf T.S, GlobalTheory.T.isRestrictedFiniteTensorFamily_typeIdempotents D V T U μf hH h1 hu T.S, fun v => fam_of_mem T U μf T.S v.2 v.2, ?_, ?_, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ T.S
    · rw [fam_of_mem T U μf T.S hv hv]
      let s := T.frame ⟨v, hv⟩
      have hk : IsOpen (s.red.ker : Set (stabLoc D.sp.cm.sig V.gram (frameLat V) v)) := by
        rw [show (s.red.ker : Set (stabLoc D.sp.cm.sig V.gram (frameLat V) v)) = (↑) ⁻¹' (stabLocOne D.sp.cm.sig V.gram s.emb (frameLat V) : Set (GLoc D.sp.cm.sig V.gram v)) from
          Set.ext s.red_eq_one_iff]
        exact (isOpen_stabLocOne V.gram s.emb (frameLat V) s.cm).preimage continuous_subtype_val
      exact conv_typeIdem (μf v) (isOpen_stabLoc _ _ _ v) (isCompact_stabLoc _ _ _ v) s.red_surjective hk _ (T.irred _)
    · rw [fam_of_not T U μf T.S (fun h => hv h.1)]
      obtain ⟨ho, hle⟩ := GlobalTheory.T.unitaryTypeLevelFamily_isOpen_le_latticeStabilizer D V T U hu v
      exact GlobalTheory.T.groupConvolution_normalizedIndicator_self _ (μf v) _ ho ((isCompact_stabLoc _ _ _ v).of_isClosed_subset
        (Subgroup.isClosed_of_isOpen _ ho) hle)
  · intro k hk g
    rw [fam_of_not T U μf T.S (fun h => hu h.1), levelFam_u]
    simp only [normInd, Pi.smul_apply]
    congr 1
    by_cases hg : g ∈ U.frame.iwahori
    · rw [indicator_of_mem (show k * g ∈ (U.frame.iwahori : Set _) from mul_mem hk hg), indicator_of_mem (show g ∈ (U.frame.iwahori : Set _) from hg)]; rfl
    · rw [indicator_of_notMem (show k * g ∉ (U.frame.iwahori : Set _) from fun h => hg ((Subgroup.mul_mem_cancel_left _ hk).1 h)),
        indicator_of_notMem (show g ∉ (U.frame.iwahori : Set _) from hg)]
  · intro v hv hvu k hk k' hk' g
    rw [fam_of_not T U μf T.S (fun h => hv h.1), levelFam_of_notMem T U hv hvu]
    simp only [normInd, Pi.smul_apply]
    congr 1
    have : k * g * k' ∈ Kv V v ↔ g ∈ Kv V v := by
      rw [Subgroup.mul_mem_cancel_right _ hk', Subgroup.mul_mem_cancel_left _ hk]
    by_cases hg : g ∈ Kv V v
    · rw [indicator_of_mem (show k * g * k' ∈ (Kv V v : Set _) from this.2 hg), indicator_of_mem (show g ∈ (Kv V v : Set _) from hg)]; rfl
    · rw [indicator_of_notMem (show k * g * k' ∉ (Kv V v : Set _) from fun h => hg (this.1 h)),
        indicator_of_notMem (show g ∉ (Kv V v : Set _) from hg)]
  · intro W _ _ σ hσ hT P hP
    rw [HasTypeVec] at hT
    obtain ⟨x, hx0, hxK, hxS⟩ := hT

    have hxker : ∀ v : T.S, ∀ k ∈ kerSub T v, σ (locFin V v k) x = x := by
      intro v
      have hle : Submodule.span ℂ {y | ∃ φ : T.W v →ₗ[ℂ] W, (∀ (k : Kv V v) z, φ (T.τ v ((T.frame v).red k) z) = σ (locFin V v k) (φ z)) ∧ y ∈ LinearMap.range φ} ≤
          GlobalTheory.PRep.fixed (σ.comp (locFin V v)) (kerSub T v) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨φ, hφ, z, rfl⟩ ⟨_, ⟨k, hk1, rfl⟩⟩
        have := hφ k z
        rw [MonoidHom.mem_ker.1 hk1, map_one] at this
        simpa using this.symm
      intro k hk
      simpa using hle (hxS v) ⟨k, hk⟩
    have hxlev : ∀ v, ∀ k ∈ levelFam T U v, σ (locFin V v k) x = x := by
      intro v k hk
      by_cases hvu : v = U.u
      · subst hvu
        rw [levelFam_u] at hk
        exact hxK _ hu k (U.frame.iwahori_le hk)
      · by_cases hv : v ∈ T.S
        · rw [levelFam_of_mem T U hu ⟨v, hv⟩] at hk
          exact hxker ⟨v, hv⟩ k hk
        · rw [levelFam_of_notMem T U hv hvu] at hk
          exact hxK v hv k hk
    have hlev := GlobalTheory.T.unitaryTypeLevelFamily_isOpen_le_latticeStabilizer D V T U hu
    have key : ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.F)), A ⊆ T.S → ∀ P,
        GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (fam T U μf A)) P → P x = x := by
      intro A
      induction A using Finset.induction_on with
      | empty =>
        intro _ P hP
        have e : fam T U μf ∅ = fun v => normInd (μf v) (levelFam T U v : Set _) :=
          funext fun v => fam_of_not T U μf ∅ (fun h => Finset.notMem_empty v h.2)
        rw [e] at hP
        refine GlobalTheory.T.integratedOperator_normalizedIndicatorProd_fixed D V μf hH h1 ν hν (levelFam T U) (fun v => (hlev v).1) (fun v => (hlev v).2) ?_ W σ x
          (GlobalTheory.T.fixed_of_forall_localSubgroup_fixed_finiteAdelic D V W σ hσ (levelFam T U) (fun v => (hlev v).2) x hxlev) P hP
        filter_upwards [T.S.eventually_cofinite_notMem, eventually_cofinite_ne U.u] with v hv hvu
        exact levelFam_of_notMem T U hv hvu
      | insert a A ha ih =>
        intro hsub P hP
        have haS : a ∈ T.S := hsub (Finset.mem_insert_self a A)
        obtain ⟨H, K, -, -, -, hHB⟩ := GlobalTheory.T.pureTensorOperator_eq_offPlace_mul_atPlace D V a μf hH h1 ν hν W σ hσ (fam T U μf A)
          (GlobalTheory.T.isRestrictedFiniteTensorFamily_typeIdempotents D V T U μf hH h1 hu A)
        have hloc := isSmooth_comp_locFin hσ a
        have hfin := (GlobalTheory.T.isRestrictedFiniteTensorFamily_typeIdempotents D V T U μf hH h1 hu A).1
        have hfin' := (GlobalTheory.T.isRestrictedFiniteTensorFamily_typeIdempotents D V T U μf hH h1 hu (insert a A)).1
        have hg : fam T U μf (insert a A) a = T.idem μf ⟨a, haS⟩ := fam_of_mem T U μf _ haS (Finset.mem_insert_self _ _)
        have e1 : Function.update (fam T U μf A) a (fam T U μf (insert a A) a) = fam T U μf (insert a A) := by
          funext v
          by_cases hva : v = a
          · subst hva
            rw [Function.update_self]
          · rw [Function.update_of_ne hva]
            by_cases hv : v ∈ T.S ∧ v ∈ A
            · rw [fam_of_mem T U μf _ hv.1 hv.2, fam_of_mem T U μf _ hv.1 (Finset.mem_insert_of_mem hv.2)]
            · rw [fam_of_not T U μf _ hv, fam_of_not T U μf _ (fun h => hv ⟨h.1, (Finset.mem_insert.1 h.2).resolve_left hva⟩)]
        have h2 : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (fam T U μf (insert a A)))
            (H ∘ₗ smoothOp (σ.comp (locFin V a)) (μf a) (fam T U μf (insert a A) a)) := by
          have := hHB _ (hfin' a) _ (isIntegralOp_smoothOp (μf a) hloc ⟨(hfin' a).1, (hfin' a).2⟩)
          rwa [e1] at this
        have hPB := hP.unique h2
        have h3 : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (fam T U μf A))
            (H ∘ₗ smoothOp (σ.comp (locFin V a)) (μf a) (fam T U μf A a)) := by
          have := hHB _ (hfin a) _ (isIntegralOp_smoothOp (μf a) hloc ⟨(hfin a).1, (hfin a).2⟩)
          rwa [Function.update_eq_self] at this
        have hB' := ih (fun v hv => hsub (Finset.mem_insert_of_mem hv)) _ h3
        have hBx : smoothOp (σ.comp (locFin V a)) (μf a) (fam T U μf (insert a A) a) x = x :=
          hg ▸ GlobalTheory.T.typeIdempotentOperator_fix_span_images D V T μf hH W σ hσ ⟨a, haS⟩ x (hxS ⟨a, haS⟩)
        have hB'x : smoothOp (σ.comp (locFin V a)) (μf a) (fam T U μf A a) x = x := by
          rw [fam_of_not T U μf A (fun h => ha h.2)]
          obtain ⟨ho, hle⟩ := hlev a
          exact GlobalTheory.T.smoothRepIntegratedOperator_normalizedIndicator_fixed _ (μf a) _ ho ((isCompact_stabLoc _ _ _ a).of_isClosed_subset
            (Subgroup.isClosed_of_isOpen _ ho) hle) W _ hloc x (hxlev a)
        rw [hPB, LinearMap.comp_apply, hBx]
        rw [LinearMap.comp_apply, hB'x] at hB'
        exact hB'
    intro h0
    have hx := key T.S (Finset.Subset.refl _) P hP
    subst h0
    exact hx0 hx.symm

end GlobalTheory.TrIdem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniquePureTensorRestrictedFamily
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PureTensorExists

theorem existsUnique_isPure : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ), IsRestricted ψ θ S T sS sT ΛS ΛT f₀ x → ∃! f, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC x hx
  classical
  have hstd : IsStdChar D ψ (-1) := GlobalTheory.PlaceTensor.base_std hB
  have hf0 : IsThetaFunO ψ S T f₀ := GlobalTheory.PlaceTensor.base_theta hB

  have build : ∀ (s : Finset (Place D)) (y : Place D → WO S T → ℂ),
      IsRestricted ψ θ S T sS sT ΛS ΛT f₀ y → (∀ p, y p ≠ f₀ → p ∈ s) →
        ∃ f, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y f := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro y _ hy
      have hconst : y = fun _ => f₀ := by
        funext p
        by_contra hne
        exact absurd (hy p hne) (by simp)
      subst hconst
      exact ⟨f₀, (GlobalTheory.T.isPureTensor_base_vector_and_local_factor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC).1⟩
    · intro q s _ ih y hyR hy

      have hres : IsRestricted ψ θ S T sS sT ΛS ΛT f₀ (Function.update y q f₀) := by
        refine ⟨fun p => ?_, ?_⟩
        · by_cases hpq : p = q
          · subst hpq
            simpa using GlobalTheory.PlaceTensor.base_isLocal hB p
          · simpa [Function.update_apply, hpq] using hyR.1 p
        · refine hyR.2.subset fun p hp => ?_
          by_cases hpq : p = q
          · subst hpq
            simp at hp
          · simpa [Function.update_apply, hpq] using hp
      have hsub : ∀ p, Function.update y q f₀ p ≠ f₀ → p ∈ s := by
        intro p hp
        by_cases hpq : p = q
        · subst hpq
          simp at hp
        · have hp' : y p ≠ f₀ := by simpa [Function.update_apply, hpq] using hp
          rcases Finset.mem_insert.1 (hy p hp') with h | h
          · exact absurd h hpq
          · exact h
      obtain ⟨f, hf⟩ := ih (Function.update y q f₀) hres hsub
      obtain ⟨f', hf', -⟩ := GlobalTheory.T.pureTensor_update_factor_from_base_vector D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC
        (Function.update y q f₀) y f q hf (by simp)
        (fun p hp => (Function.update_of_ne hp f₀ y).symm) (hyR.1 q)
      exact ⟨f', hf'⟩
  obtain ⟨f, hf⟩ := build hx.2.toFinset x hx (fun p hp => by simpa using hp)
  refine ⟨f, hf, fun g hg => ?_⟩

  obtain ⟨hHaar, hFD, -⟩ := id hC
  have hfT : IsThetaFunO ψ S T f := hf.2.1
  have hgT : IsThetaFunO ψ S T g := hg.2.1
  have hIP := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hstd hC
  have hd : IsThetaFunO ψ S T (g - f) := GlobalTheory.WeilVacMove.isTheta_sub hgT hfT
  have hz : g - f = 0 := by
    refine GlobalTheory.HeisTotal.eq_zero_of_orthogonal_translates D ψ hstd S T f₀ (g - f) hf0
      (GlobalTheory.PlaceTensor.base_ne_zero hB) hd μ 𝓕 hHaar hFD fun w => ?_
    have hw : IsThetaFunO ψ S T (heisO ψ S T w f₀) :=
      (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hstd S T).1 w f₀ hf0
    have e1 : ipO μ 𝓕 g (heisO ψ S T w f₀) = ipO μ 𝓕 f (heisO ψ S T w f₀) := by
      rw [(hg.2.2 w).2, (hf.2.2 w).2]
    have e2 : ipO μ 𝓕 (heisO ψ S T w f₀) g = ipO μ 𝓕 (heisO ψ S T w f₀) f := by
      rw [(hIP g _ hgT hw).2.1, (hIP f _ hfT hw).2.1, e1]
    have e3 := ((hIP (g - f) _ hd hw).2.2.2.1 f hfT).2
    rw [sub_add_cancel] at e3
    have e4 : ipO μ 𝓕 (heisO ψ S T w f₀) (g - f) = 0 := by
      linear_combination e2 - e3
    exact e4
  exact sub_eq_zero.1 hz

end GlobalTheory.PureTensorExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockAlgebraicThetaVectorsStableLineDerivative
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SquareComm.LineDeriv

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

private theorem hD_eq_mul_add_fderiv {G R : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]
    (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (f : G → ℂ) (w : G)
    (hf : DifferentiableAt ℝ (fun x : R => f (w + ι x)) 0) (u : R) :
    hD ι π om u f w =
      (-(Real.pi * Complex.I) * ((om (π w) u : ℝ) : ℂ)) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u := by
  have hlin : HasDerivAt (fun t : ℝ => t • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
  have hF : HasDerivAt (fun t : ℝ => f (w + ι (t • u))) (fderiv ℝ (fun x : R => f (w + ι x)) 0 u) 0 := by
    have h0 : ((0 : ℝ) • u) = 0 := zero_smul ℝ u
    have hf' : DifferentiableAt ℝ (fun x : R => f (w + ι x)) ((0 : ℝ) • u) := by rwa [h0]
    have := hf'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hlin
    rw [h0] at this
    exact this
  have hP : HasDerivAt (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * ((om (π w) (t • u) : ℝ) : ℂ)))
      (-(Real.pi * Complex.I) * ((om (π w) u : ℝ) : ℂ)) 0 := by
    have e : (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * ((om (π w) (t • u) : ℝ) : ℂ))) =
        fun t : ℝ => Complex.exp ((t : ℂ) * (-(Real.pi * Complex.I) * ((om (π w) u : ℝ) : ℂ))) := by
      funext t
      rw [map_smul, smul_eq_mul]
      push_cast
      ring_nf
    rw [e]
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * (-(Real.pi * Complex.I) * ((om (π w) u : ℝ) : ℂ)))
        (1 * (-(Real.pi * Complex.I) * ((om (π w) u : ℝ) : ℂ))) 0 :=
      (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const _
    simpa using h1.cexp
  have hPF := hP.mul hF
  unfold hD
  exact hPF.deriv.trans (by simp)

theorem dLine_eq_sum_dRho {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {L : ℝ →+ WO S T} (hL : IsRealDir T S L) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    dLine ψ S T L f = ∑ τ, Datum.dRho (heisO ψ S T) θ τ (compAt θ τ (L 1)) f := by
  classical
  obtain ⟨σ, hσ⟩ := exists_chart hθ
  funext w
  have hd : DifferentiableAt ℝ (fun x => f (w + iotaW σ T S x)) 0 :=
    ((theta_sm hσ hf w).differentiable (by simp)).differentiableAt
  rw [Finset.sum_apply, dLine_eq_hD hσ hψ hL f, hD_eq_mul_add_fderiv _ _ _ _ _ hd]
  have hτ : ∀ τ, Datum.dRho (heisO ψ S T) θ τ (compAt θ τ (L 1)) f w =
      (-(Real.pi * Complex.I) * ((omO S T (piW θ T S w) (Pi.single τ (compAt θ τ (L 1))) : ℝ) : ℂ)) * f w +
        fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0 (Pi.single τ (compAt θ τ (L 1))) := by
    intro τ
    rw [dRho_eq_dLine, dLine_eq_hD hσ hψ (isRealDir_lineAt hθ τ _) f, GlobalTheory.FockIndep.piW_lineAt hθ τ]
    exact hD_eq_mul_add_fderiv _ _ _ _ _ hd _
  rw [Finset.sum_congr rfl fun τ _ => hτ τ, Finset.sum_add_distrib]
  have hp : piW θ T S (L 1) = ∑ τ, (Pi.single τ (compAt θ τ (L 1)) : RW T S) := by
    exact (Finset.univ_sum_single (piW θ T S (L 1))).symm
  rw [hp, map_sum, map_sum]
  simp only [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]

theorem deriv_line_mem_algF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X), ∀ Φ ∈ algF ψ θ ε A B,
      ∀ L : ℝ →+ WO (sgn ε M) X, Continuous L → (∀ t, (L t).map (finPart D) = 0) →
        (fun x => deriv (fun t : ℝ => heisO ψ (sgn ε M) X (L t) Φ x) 0) ∈ algF ψ θ ε A B := by
  intro D ψ θ hψ hθ ε M X A B Φ hΦ L hLc hLf
  have hsub : algF ψ θ ε A B ≤ GlobalTheory.RealWeil.thetaSub ψ (sgn ε M) X := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, P, hg, rfl⟩
    have hg' : IsThetaFunO ψ (sgn ε M) X g := hg.1
    show IsThetaFunO ψ (sgn ε M) X (fockF ψ θ ε A B g P)
    unfold fockF pureTensorO aPlusAll
    exact GlobalTheory.FockIndep.pure_mem (fun _ _ h h' => GlobalTheory.OrientedHeis.theta_add h h')
      (fun a _ h => GlobalTheory.OrientedHeis.theta_smul a h)
      (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) hg' P
  have hth : IsThetaFunO ψ (sgn ε M) X Φ := hsub hΦ
  have hL : IsRealDir X (sgn ε M) L := ⟨hLc, hLf⟩
  show dLine ψ (sgn ε M) X L Φ ∈ algF ψ θ ε A B
  rw [dLine_eq_sum_dRho hψ hθ hL hth]
  exact Submodule.sum_mem _ fun τ _ => GlobalTheory.SquareComm.dRho_mem_algF D ψ θ hψ hθ ε M X A B Φ hΦ τ _

end GlobalTheory.SquareComm.LineDeriv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisAvgInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField GlobalTheory.FinDecomp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinDecomp

theorem heisAvg_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (m : ℕ)
    (lam : WO S T → ℂ), (∀ x ∈ Λ, ∀ y ∈ Λ, lam (x + y) = lam x * lam y * ψ (symplOH S T x y)) →
    ∀ [Fintype (Qm m Λ)] (g : WO S T → ℂ), (∀ l ∈ Λ, lam (m • l) • heisO ψ S T (m • l) g = g) →
    ∀ b ∈ Λ, lam b • heisO ψ S T b (∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) g) =
      ∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) g := by
  intro D ψ S T Λ m lam hlam _ g hg b hb
  have hsm : ∀ (x : WO S T) (c : ℂ) (f : WO S T → ℂ), heisO ψ S T x (c • f) = c • heisO ψ S T x f := by
    intro x c f; funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
  have hsumlin : ∀ (x : WO S T) (F : Qm m Λ → WO S T → ℂ),
      heisO ψ S T x (∑ q, F q) = ∑ q, heisO ψ S T x (F q) := by
    intro x F; funext w; simp only [heisO, Finset.sum_apply, Finset.mul_sum]
  have hmul : ∀ x ∈ Λ, ∀ y ∈ Λ, lam x • heisO ψ S T x (lam y • heisO ψ S T y g) =
      lam (x + y) • heisO ψ S T (x + y) g := by
    intro x hx y hy
    rw [hsm, GlobalTheory.FinTranslate.heisO_heisO, smul_smul, smul_smul, hlam x hx y hy]
  have key : ∀ q : Qm m Λ, lam b • heisO ψ S T b (lam (repm q) • heisO ψ S T (repm q) g) =
      lam (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) •
        heisO ψ S T (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) g := by
    intro q
    have hbq : b + repm q ∈ Λ := Λ.add_mem hb (repm_mem q)
    rw [hmul b hb _ (repm_mem q)]
    have hmk : (QuotientAddGroup.mk (⟨b + repm q, hbq⟩ : Λ) : Qm m Λ) =
        (QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q := by
      conv_rhs => rw [← mk_repm q]
      rfl
    have h1 := repm_mk_sub (m := m) hbq
    rw [hmk] at h1
    obtain ⟨l, hl, hl'⟩ := mem_mLat.1 h1
    have he : repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q) = (b + repm q) + m • l := by
      rw [hl']; abel
    rw [he, ← hmul _ hbq _ (Λ.nsmul_mem hl m), hg l hl]
  calc lam b • heisO ψ S T b (∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) g)
      = ∑ q : Qm m Λ, lam (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) •
          heisO ψ S T (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) g := by
        rw [hsumlin, Finset.smul_sum]
        exact Finset.sum_congr rfl fun q _ => key q
    _ = _ := Equiv.sum_comp (Equiv.addLeft (QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ))
          (fun q => lam (repm q) • heisO ψ S T (repm q) g)

end GlobalTheory.FinDecomp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergArchimedeanDiffOperatorHasDerivAtFamilStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergArchimedeanDiffOperator_hasDerivAt_family : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (G : ℝ → SInf F κ) (P Q : ℝ → (κ → mixedEmbedding.mixedSpace F))
    (g' : SInf F κ) (P' Q' : κ → mixedEmbedding.mixedSpace F),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => G p.1 p.2) →
    (∀ y, HasDerivAt (fun t => G t y) (g' y) 0) → HasDerivAt P P' 0 → HasDerivAt Q Q' 0 → ∀ y,
    HasDerivAt (fun t => GlobalTheory.HeisOrbit.dOp (P t) (Q t) (G t) y) (GlobalTheory.HeisOrbit.dOp (P 0) (Q 0) g' y + GlobalTheory.HeisOrbit.dOp P' Q' (G 0) y) 0 := by
  first | exact @GlobalTheory.HeisOrbit.DOpDeriv.dOp_hasDerivAt | exact GlobalTheory.HeisOrbit.DOpDeriv.dOp_hasDerivAt | (intros; apply GlobalTheory.HeisOrbit.DOpDeriv.dOp_hasDerivAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivativeMemFockAlgebraicThetaVectorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_derivative_mem_fockAlgebraicThetaVectors : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X), ∀ f ∈ algF ψ θ ε A B, ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ),
      dRho (heisO ψ (sgn ε S) X) θ τ z f ∈ algF ψ θ ε A B := by
  first | exact @GlobalTheory.SquareComm.dRho_mem_algF | exact GlobalTheory.SquareComm.dRho_mem_algF | (intros; apply GlobalTheory.SquareComm.dRho_mem_algF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOrbitCoefficientSmoothStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_orbit_coefficient_smooth : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W), ∀ γ ∈ Lines σ W, ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)) ∧
    ∃ u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u' ∧
      HasDerivAt (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)) (GlobalTheory.HeisOrbit.archCo M.co u') 0 := by
  first | exact @GlobalTheory.HeisOrbitSmooth.archCo_orbit_smooth | exact GlobalTheory.HeisOrbitSmooth.archCo_orbit_smooth | (intros; apply GlobalTheory.HeisOrbitSmooth.archCo_orbit_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleAdmissibleFiniteLengthStatement
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_admissible_finite_length : GlobalTheory.Published.KFiniteCoefficientsAnalytic → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsIrrAdm ε π → (∀ Y : Submodule ℂ H, IsGKSub ε π Y → Y = ⊥ ∨ Y = kFinVec ε π) ∧ HasFiniteLength ε π := by
  first | exact @GlobalTheory.HCChar.simple_of_isIrrAdm | exact GlobalTheory.HCChar.simple_of_isIrrAdm | (intros; apply GlobalTheory.HCChar.simple_of_isIrrAdm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermBoundedDenominatorsMovedLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelTerm_bounded_denominators_moved_level : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ e : ℕ, ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ M : ℕ, 0 < M ∧ ∀ (g : GA D V) (h : GA D W), ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ M * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ e ∧ ∀ F : WO V W → ℂ, IsThetaFunO ψ V W F → (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ V W (actO V W g h u) F = F) → ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, term ψ V V' W C C' B μ 𝓨 F y ≠ 0 → ∀ x : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ a b, IsIntegral ℤ (x a b)) → ∃ c : ℤ, (N : ℝ) * ratPair W y x = c := by
  first | exact @GlobalTheory.MixedTermIntegral.integral | exact GlobalTheory.MixedTermIntegral.integral | (intros; apply GlobalTheory.MixedTermIntegral.integral <;> assumption)
end

