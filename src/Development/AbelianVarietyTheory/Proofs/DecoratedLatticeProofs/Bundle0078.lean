import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0109
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0078
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0077
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.WordData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FirstPacketUnfoldedOfNongenericUnit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0001
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Formalism.FormalDegreeBessel.StatementIO
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HermCoord
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity
import ReciprocityTheory.NeutralLocalFields.Bundle0001
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinalAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardResidueFieldOfRingEquivAdicCompletion
section
open ValuativeRel NumberField IsDedekindDomain

namespace GlobalTheory.LocalResidue

theorem card_residue_of_ringEquiv : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : k ≃+* v.adicCompletion F), (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) → Nat.card 𝓀[k] = Ideal.absNorm v.asIdeal := by
  intro F _ _ v k _ _ _ _ φ hφ
  let ψ : 𝒪[k] ≃+* v.adicCompletionIntegers F :=
    { toFun := fun a => ⟨φ a, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ((hφ a).2 a.2)⟩
      invFun := fun b => ⟨φ.symm b, (hφ _).1 (by
        rw [RingEquiv.apply_symm_apply]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 b.2)⟩
      left_inv := fun a => Subtype.ext (φ.symm_apply_apply a)
      right_inv := fun b => Subtype.ext (φ.apply_symm_apply b)
      map_mul' := fun a b => Subtype.ext (map_mul φ (a : k) (b : k))
      map_add' := fun a b => Subtype.ext (map_add φ (a : k) (b : k)) }
  have e := IsLocalRing.ResidueField.mapEquiv ψ
  have hF : ∀ s : 𝓞 F, Valued.v (algebraMap F (v.adicCompletion F) s) = v.intValuation s := fun s =>
    (v.valuedAdicCompletion_eq_valuation' _).trans (HeightOneSpectrum.valuation_of_algebraMap v s)
  have hc := GlobalTheory.SplitUnif.card_residueField v (algebraMap F (v.adicCompletion F)) v (fun _ => rfl) fun s => by
    rw [hF, HeightOneSpectrum.intValuation_lt_one_iff_mem]
  rw [Nat.card_congr e.toEquiv, hc]

end GlobalTheory.LocalResidue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmGoodModelOfGlobalArtinReciprocity
section
namespace GlobalTheory.Corev.CmTwoClosing

theorem cmGoodModel_of_globalArtinReciprocity (hA : GlobalTheory.Published.GlobalArtinReciprocity) : Formalism.L2.Th1.CM.CM2 :=
  GlobalTheory.T.cmLattice_good_model_unramified (GlobalTheory.T.exists_idealClass_artinSymbol_of_globalArtin hA) GlobalTheory.T.chebotarev_degreeOne_valuationSubrings

end GlobalTheory.Corev.CmTwoClosing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmMultiplierIntegralSeriesAtInertPrimeProofStatement
section
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmMultiplierIntegralSeriesAtInertPrime_proof : EndOmega := by
  first | exact @GlobalTheory.Honda.endOmega_holds | exact GlobalTheory.Honda.endOmega_holds | (intros; apply GlobalTheory.Honda.endOmega_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollisionTypingsCompare
section
noncomputable section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2

namespace GlobalTheory.CollCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Core.Deg GlobalTheory.IndefiniteRowSideFullHecke.WordCollisionBound

theorem uOne_last (D : D7) (u w : D.what₂.Word) (τ : D.what₂.Tau) : uOne D w τ D.R.k = uOne D u τ D.R.k := by
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  have h : 1 ≤ D.R.k ∧ D.R.k ≤ D.R.k := ⟨hk, le_rfl⟩
  simp only [uOne, dif_pos h, uS]
  have a := D.hcW_last w τ hk
  have b := D.hcW_last u τ hk
  exact congrArg (fun q : ℚ => (q : ℝ)) (a.trans b.symm)

theorem splits_level (D : D7) (w : D.what₂.Word) : SplitsE D (D.mem w).A.T :=
  S.splitsCompl_of_ncard _ _ (D.mem w).A.T_prime
    (Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion.split_clause _ Formalism.L2.SG.ResidEvFree.cycSplit_holds _ (D.mem w).A.T_prime (S.level_norm_one_mod_conductor _ w)).2

def CappedBound : Prop :=
  ∀ Cg cb Cu cT CT CW : ℝ, 0 < cb → 0 < cT →
    ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      ∀ (D : D7) (L : ℝ) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (u : D.what₂.Word),
        (∀ w, Tr D w ≤ Real.exp L ^ (CW * D.R.m)) →
        1 < L → WordData D u → Sizes D L u C' Cl Cg cb Cu cT CT →
        Formalism.BasicNotions.Ties D → Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D → Nonempty (SIso D.s (sOf hF)) →
        ConcTie X Y → (Y.tO u u).AbsConv →
        (Y.tO u u).pairAbs ((Y.tO u u).big (Y.tO u u).nzSet) ≤
          Real.exp (-((1 / 3 : ℝ) * D.R.k * D.R.f * Real.log D.R.k)) *
            (duC X Y u ^ 2 / DstC X + duC X Y u)

end GlobalTheory.CollCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactUnitaryFiniteInvariantSubspaceStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_unitary_finite_invariant_subspace : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [SecondCountableTopology K] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (π : K →* (H →L[ℂ] H)), (∀ k x, ‖π k x‖ = ‖x‖) → (∀ x, Continuous fun k => π k x) → ∃ S : Submodule ℂ H, S ≠ ⊥ ∧ FiniteDimensional ℂ S ∧ ∀ k, ∀ x ∈ S, π k x ∈ S := by
  first | exact @GlobalTheory.CompactRep.exists_finiteDimensional_invariant | exact GlobalTheory.CompactRep.exists_finiteDimensional_invariant | (intros; apply GlobalTheory.CompactRep.exists_finiteDimensional_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateIdealLatticeDiscrOneHomotheticIdealStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateIdealLattice_discr_one_homothetic_ideal : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∀ ρ : M →ₐ[ℚ] ℂ, Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧ ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ, x ≠ 0 ∧ lamConj M ρ (lamOf D cc δ) = lamOf D c x := by
  first | exact @GlobalTheory.ConjLatticeCore.conj_lattice_core | exact GlobalTheory.ConjLatticeCore.conj_lattice_core | (intros; apply GlobalTheory.ConjLatticeCore.conj_lattice_core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoordPair
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
open GlobalTheory.SWC

noncomputable section

namespace GlobalTheory.HermSD

def coordPair {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (n : ℕ) (x y : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E)) : R :=
  ∑ a, x.1 a * y.1 a + ∑ p, Algebra.trace R (R ⊗[F] E) (sigR R σ (x.2 p) * y.2 p)

end GlobalTheory.HermSD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DenseKFiniteVectorsUnitaryGroupRep
section
open scoped InnerProductSpace

namespace GlobalTheory.CompactRep

theorem dense_finite_vectors (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [SecondCountableTopology K] (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : K →* H →L[ℂ] H)
    (hiso : ∀ k x, ‖π k x‖ = ‖x‖) (hcont : ∀ x, Continuous fun k => π k x) :
    Dense {v : H | ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧
      ∀ k, ∀ x ∈ S, π k x ∈ S} := by
  let N : Submodule ℂ H :=
    { carrier := {v : H | ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧
        ∀ k, ∀ x ∈ S, π k x ∈ S}
      add_mem' := by
        rintro a b ⟨S, hS, ha, hSs⟩ ⟨T, hT, hb, hTs⟩
        refine ⟨S ⊔ T, inferInstance, Submodule.add_mem_sup ha hb, ?_⟩
        intro k x hx
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
        rw [map_add]
        exact Submodule.add_mem_sup (hSs k y hy) (hTs k z hz)
      zero_mem' := ⟨⊥, inferInstance, Submodule.zero_mem _, by
        intro k x hx
        rw [Submodule.mem_bot] at hx ⊢
        rw [hx, map_zero]⟩
      smul_mem' := by
        rintro c a ⟨S, hS, ha, hSs⟩
        exact ⟨S, hS, S.smul_mem c ha, hSs⟩ }
  have hNst : ∀ k, ∀ a ∈ N, π k a ∈ N := by
    rintro k a ⟨S, hS, ha, hSs⟩
    exact ⟨S, hS, hSs k a ha, hSs⟩
  have hinner : ∀ k a b, ⟪π k a, π k b⟫_ℂ = ⟪a, b⟫_ℂ := fun k a b =>
    (LinearIsometry.mk (π k).toLinearMap (hiso k)).inner_map_map a b
  have hinv : ∀ k a, π k (π k⁻¹ a) = a := by
    intro k a
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  have hOst : ∀ k, ∀ w ∈ Nᗮ, π k w ∈ Nᗮ := by
    intro k w hw
    rw [Submodule.mem_orthogonal] at hw ⊢
    intro a ha
    rw [← hinv k a, hinner]
    exact hw _ (hNst _ a ha)
  have hbot : Nᗮ = ⊥ := by
    by_contra hne
    haveI : Nontrivial Nᗮ := Submodule.nontrivial_iff_ne_bot.2 hne
    let ρ : K →* (Nᗮ →L[ℂ] Nᗮ) :=
      { toFun := fun k => ((π k).comp Nᗮ.subtypeL).codRestrict Nᗮ (fun w => hOst k w w.2)
        map_one' := by
          ext w
          simp
        map_mul' := by
          intro k l
          ext w
          show π (k * l) w = π k (π l w)
          rw [map_mul, ContinuousLinearMap.mul_apply] }
    have hρ : ∀ k (w : Nᗮ), ((ρ k w : Nᗮ) : H) = π k w := fun k w => rfl
    obtain ⟨S, hS0, hSf, hSs⟩ := exists_finiteDimensional_invariant K Nᗮ ρ
      (fun k w => hiso k w) (fun w => (hcont w).subtype_mk _)
    apply hS0
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hwN : (w : H) ∈ N := by
      refine ⟨S.map Nᗮ.subtype, inferInstance, ⟨w, hw, rfl⟩, ?_⟩
      rintro k x ⟨y, hy, rfl⟩
      exact ⟨ρ k y, hSs k y hy, rfl⟩
    have h0 : ⟪(w : H), (w : H)⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 w.2 _ hwN
    exact Subtype.ext (inner_self_eq_zero.1 h0)
  exact Submodule.dense_iff_topologicalClosure_eq_top.2
    (Submodule.topologicalClosure_eq_top_iff.2 hbot)

theorem dense_isKFin (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) : Dense {v : H | Formalism.MainNotions.S.IsKFin ε σ v} := by
  obtain ⟨⟨h1, hmul⟩, hiso, hcont⟩ := hσ
  have hemb : Topology.IsEmbedding (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Formalism.REAL.KG ε) := hemb.secondCountableTopology
  have hU : ∀ k : Formalism.REAL.KG ε, Formalism.REAL.toMK k ∈ Formalism.MainNotions.S.UJset ε := fun k => k.1.2
  let π : Formalism.REAL.KG ε →* (H →L[ℂ] H) :=
    { toFun := fun k => σ (Formalism.REAL.toMK k)
      map_one' := h1
      map_mul' := fun k l => hmul _ (hU k) _ (hU l) }
  have hd := dense_finite_vectors (Formalism.REAL.KG ε) H π (fun k x => hiso _ (hU k) x)
    (fun x => (hcont x).comp_continuous hemb.continuous hU)
  refine hd.mono ?_
  rintro v ⟨S, hS, hv, hSs⟩
  refine ⟨S, hS, hv, ?_⟩
  intro g hg x hx
  rw [← Formalism.REAL.range_toMK] at hg
  obtain ⟨k, rfl⟩ := hg
  exact hSs k x hx

end GlobalTheory.CompactRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstCoupledKernelFiniteDatumLevelSize
section
noncomputable section

namespace GlobalTheory.Core.Ht2.DatOneS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

theorem smallDatum_xiCpl1_sharp : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (al : I.β (N.R.m - 2)) (p₀ : ChPt (R := N.R) sel mu u (N.R.m - 2)) (p : ChPt (R := N.R) sel mu u (N.R.m - 2 + 1)) (Y : Set (Sp X.E (N.R.N (N.R.m - 2 + 1)))), SmallDatum (Sall sel mu u) p₀.deco.1.N p.deco.1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiCpl1 Ch sel mu cst I (N.R.m - 2) al p₀ p Y) 1 := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hH al p₀ p Y
  obtain ⟨hrow, hG, hT, -⟩ := GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hH
  have hI : I.Ok Ch sel mu cst G (N.R.m - 2) := hH.2.2.2.2.2.2.1
  have hfr : ∀ {j : ℕ} (r : ChPt (R := N.R) sel mu u j) (P : rowSG Pr sel mu) x,
      frsF sel mu r P x ∈ r.deco.1.at P.1 ↔ x ∈ stdAt X.E (N.R.N j) P.1 := by
    intro j r P x
    have hP := hrow P.1 P.2
    simp only [frsF, hP, dif_pos]
    exact (GlobalTheory.ColNorms.liftFr_lifts X.E _ _ _ r.deco ⟨P.1, hP⟩).1 x
  have key := @GlobalTheory.ColNorms.DatOne.smallDatum_of_frames X.E X.K _ _ _ _ _ _ (Pr.vT u) _ _ (rowSG Pr sel mu) (fun a b => Classical.propDecidable (a = b))
    p₀.deco.1 p.deco (frsF sel mu p₀) (frsF sel mu p) (hfr p₀) (hfr p) (Pr.T u * (Pr.g 0 * Pr.g 1))
    (fun P => Formalism.L2.Col.qOf P.1) ?_ ?_
    (fun P x => PsiAt Ch sel mu cst (N.R.m - 2) P (I.h (N.R.m - 2) al P) x ((frsF sel mu p P).symm (repY Y))) (fun _ => 1) ?_
  · rw [Finset.prod_const_one] at key
    exact key
  · intro P
    obtain ⟨i, -, hq, -⟩ := hG P.1 (hrow P.1 P.2)
    show Formalism.L2.Col.qOf P.1 ∣ _
    rw [hq]
    refine Dvd.dvd.mul_left ?_ _
    fin_cases i
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  · intro P hP
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hT P hP)
  · intro P
    have hm := hI.hm
    have h := GlobalTheory.T.movedDatum_small_typePrime_any_level CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hH (N.R.m - 2) (by omega) P
      (I.h (N.R.m - 2) al P) 1 (hI.stabG _ al P (hrow P.1 P.2)) (one_mem _)
    exact GlobalTheory.ColNorms.DatOne.locSmall_joinCol h _

end GlobalTheory.Core.Ht2.DatOneS

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocityStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertClassField_of_globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity → Neutral.HilbertClassField.Statement := by
  first | exact @GlobalTheory.Published.GlobalArtinReciprocity.hilbertClassField | exact GlobalTheory.Published.GlobalArtinReciprocity.hilbertClassField | (intros; apply GlobalTheory.Published.GlobalArtinReciprocity.hilbertClassField <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IrreducibleKStableFiniteSubspace
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
open scoped InnerProductSpace

namespace GlobalTheory.AdmUnitary

theorem admissible_and_kFin_smooth : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → (∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε σ S → ∀ v ∈ S, ∃ Y : Submodule ℂ H, FiniteDimensional ℂ Y ∧ v ∈ Y ∧ ∀ B : H →L[ℂ] H, (∀ k ∈ Formalism.REAL.Kset ε, ∀ u, B (σ k u) = σ k (B u)) → ∀ y ∈ Y, B y ∈ Y) ∧ ∀ v, IsKFin ε σ v → Formalism.QuantumDeterminants.SmoothOnH (Formalism.REAL.Jm ε) (fun g => σ g v) := by
  intro n ε H _ _ _ σ hσ hirr
  refine ⟨fun S hS hst v hv => ?_, fun v hv => CompanionTheory.D.gk.admitted.kFin_smooth n ε H σ hσ hirr v hv⟩
  obtain ⟨Y, hY, -, hvY, hT⟩ := CompanionTheory.D.gk.admitted.unitary_group_admissible n ε H σ hσ hirr S hst v hv
  exact ⟨Y, hY, hvY, hT⟩

end GlobalTheory.AdmUnitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KStableSubmoduleEqTopOfHighestWeightLe
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
open scoped InnerProductSpace

namespace GlobalTheory.HwSpan

theorem eq_top_of_hwSub_le : ∀ (p q : ℕ) (M : GKMod p q) (N : Submodule ℂ M.V), KStable M.act N →
    (∀ μ, hwSub M.act μ ≤ N) → N = ⊤ := by
  intro p q M N hN hhw
  have hL : Formalism.MainNotions.SchurIrreducible.IsKLieAct M.act := fun X Y _ _ => M.lie X Y
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨W, hfd, hvW, hW⟩ := M.kfin v
  have hle : W ≤ N := GlobalTheory.BlockReps.le_of_hw hL hW (fun x _ => M.wts x) hN
    (fun μ x _ hx => hhw μ hx.2)
  exact hle hvW

end GlobalTheory.HwSpan
end

