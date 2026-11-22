import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0774
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0349
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ObjOnNarrowOfObjectsExist
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0350
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0348
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TestDataHaarFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidTranslateLineBundleRationalPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0166
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1555
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeToLevelOfDvdTrueDGam
section
noncomputable section

namespace GlobalTheory.DGamOnRecord

open Formalism.BasicNotions Formalism.MainNotions NumberField GlobalTheory.IndefiniteRowSideFullHecke.LatticeAutomorphismLcm GlobalTheory.DGamPrimeToLevel
open Formalism.L2.Col (Sp hStd autLat PosStar)
open Formalism.HermitianLatticesTheory (isom IsUnimodular)
open GlobalTheory.Mem.Col2 (DGam autOrd autO gamOrd gamRanks)

section Transport

variable {E : Type} [Field E] [NumberField E] [StarRing E]
  {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
  {V' : Type} [AddCommGroup V'] [Module E V'] [Module (𝓞 E) V'] [IsScalarTower (𝓞 E) E V']

omit [StarRing E] in

theorem card_dvd_of_minkMult {n N M : ℕ} (hM : MinkMult N M) (hN : Module.finrank ℚ E * n ≤ N)
    (G : Subgroup (Sp E n ≃ₗ[E] Sp E n)) [Finite G] : Nat.card G ∣ M := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have hr : Module.finrank ℚ (Sp E n × (Fin k → ℚ)) = Module.finrank ℚ E * n + k := by
    rw [Module.finrank_prod, ← Module.finrank_mul_finrank ℚ E (Sp E n)]
    simp
  let b := Module.finBasisOfFinrankEq ℚ _ hr
  let r : G →* Module.End ℚ (Sp E n × (Fin k → ℚ)) :=
    { toFun := fun g => ((g.1 : Sp E n →ₗ[E] Sp E n).restrictScalars ℚ).prodMap LinearMap.id
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }
  have hr : Function.Injective r := fun g h hgh =>
    Subtype.ext (LinearEquiv.ext fun x => congrArg Prod.fst (LinearMap.congr_fun hgh (x, 0)))
  let φ : G →* Matrix.GeneralLinearGroup (Fin (Module.finrank ℚ E * n + k)) ℚ :=
    ((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom.comp r).toHomUnits
  have hφ : Function.Injective φ := fun g h hgh =>
    hr ((LinearMap.toMatrixAlgEquiv b).injective (congrArg Units.val hgh))
  have e := MonoidHom.ofInjective hφ
  rw [Nat.card_congr e.toEquiv]
  exact hM φ.range (Finite.of_equiv _ e.toEquiv)

end Transport

def trueDGam (D : D7) : ℕ := letI := D.host.cmStar; DGam D.host.E D.R

def ChainsCarryLcm (D : D7) : Prop := ∀ u μ, IsAutLcm D (D.chTw u μ).DGam

end GlobalTheory.DGamOnRecord

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdEndomorphismPowLevelComponentEqOneOfRelation
section
open GlobalTheory.HTLat

namespace GlobalTheory.TateRel

theorem lev_sum {M : Type} [CommGroup M] {l : ℕ} {ι : Type} (s : Finset ι) (f : ι → Tate l M) (N : ℕ) :
    (∑ i ∈ s, f i).lev N = ∏ i ∈ s, (f i).lev N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, Tate.lev_add, ih]

theorem prod_pow_eq_one (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (φ : Fin n → (M →* M)) (c : Fin n → ℤ_[l]) (h : ∑ i, c i • Tate.map l (φ i) = 0) (N : ℕ)
    (m : Fin n → ℤ) (hm : ∀ i, PadicInt.toZModPow N (c i) = (m i : ZMod (l ^ N)))
    (t : Tate l M) : ∏ i, φ i (t.lev N) ^ m i = 1 := by
  have h0 : ((∑ i, c i • Tate.map l (φ i)) t).lev N = 1 := by rw [h]; rfl
  rw [LinearMap.sum_apply, lev_sum] at h0
  rw [← h0]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, Tate.lev_smul, Tate.lev_map]
  set y := φ i (t.lev N)
  have hy : y ^ ((l ^ N : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, ← map_pow, Tate.lev_pow, map_one]
  have hc : ((GlobalTheory.PDiv.digit N (c i) : ℕ) : ZMod (l ^ N)) = ((m i : ℤ) : ZMod (l ^ N)) := by
    rw [GlobalTheory.PDiv.cast_digit, hm i]
  have hc' : (((GlobalTheory.PDiv.digit N (c i) : ℕ) : ℤ) : ZMod (l ^ N)) = ((m i : ℤ) : ZMod (l ^ N)) := by
    rw [Int.cast_natCast]; exact hc
  rw [ZMod.intCast_eq_intCast_iff'] at hc'
  rw [zpow_eq_zpow_emod (m i) hy, ← hc', ← zpow_eq_zpow_emod _ hy, zpow_natCast]

end GlobalTheory.TateRel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoefficientSeparation
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SpecTraceProof

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

open Classical in

theorem isCopyFinDS_of_equiv {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ρ : GA D V →* (H →L[ℂ] H)} {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {σ : Representation ℂ (GfC V) W} {σ' : Representation ℂ (GfC V) W'} (f : σ.Equiv σ')
    (h : IsCopyFinDS σ M ρ ⊤) : IsCopyFinDS σ' M ρ ⊤ := by
  obtain ⟨T, hT, hinj, hspan⟩ := h
  refine ⟨T ∘ₗ f.symm.toLinearEquiv.toLinearMap, ?_, hinj.comp f.symm.toLinearEquiv.injective, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := mem_homTensorPi.1 hT
    refine mem_homTensorPi.2 ⟨fun _ _ => Submodule.mem_top, fun g w y => ?_, fun i g w y => h3 i g _ y⟩
    have e : f.symm.toLinearEquiv (σ' g w) = σ g (f.symm.toLinearEquiv w) :=
      LinearMap.congr_fun (f.symm.isIntertwining' g) w
    have h2' := h2 g (f.symm.toLinearEquiv w) y
    rw [← e] at h2'
    exact h2'
  · rw [← hspan]
    congr 2
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Set.mem_setOf_eq]
    exact ⟨fun ⟨w, y, hv⟩ => ⟨_, y, hv⟩, fun ⟨w, y, hv⟩ => ⟨f.toLinearEquiv w, y, by simpa using hv⟩⟩

open Classical in

theorem isCopyFinDS_of_uEquiv {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    {ρ : GA D V →* (H →L[ℂ] H)} {ρ' : GA D V →* (H' →L[ℂ] H')} {W : Type} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GfC V) W} (hρ : UEquiv ρ ρ')
    (h : IsCopyFinDS σ M ρ ⊤) : IsCopyFinDS σ M ρ' ⊤ := by
  obtain ⟨A, hA⟩ := hρ
  obtain ⟨T, hT, hinj, hspan⟩ := h
  let C := (ContinuousLinearMap.compContinuousMultilinearMapL ℂ M.H H H'
    (A.toContinuousLinearEquiv : H →L[ℂ] H')).toLinearMap
  have hC : ∀ w y, (C ∘ₗ T) w y = A (T w y) := fun _ _ => rfl
  refine ⟨C ∘ₗ T, ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := mem_homTensorPi.1 hT
    refine mem_homTensorPi.2 ⟨fun _ _ => Submodule.mem_top, fun g w y => ?_, fun i g w y => ?_⟩
    · rw [hC, hC, h2, hA]
    · rw [hC, hC, h3, hA]
  · intro w w' e
    refine hinj (ContinuousMultilinearMap.ext fun y => A.injective ?_)
    rw [← hC, ← hC, e]
  · have hS : {v | ∃ w y, v = (C ∘ₗ T) w y} = A '' {v | ∃ w y, v = T w y} := by
      ext v
      simp only [hC, Set.mem_setOf_eq, Set.mem_image]
      exact ⟨fun ⟨w, y, hv⟩ => ⟨_, ⟨w, y, rfl⟩, hv.symm⟩, fun ⟨_, ⟨w, y, rfl⟩, hv⟩ => ⟨w, y, hv.symm⟩⟩
    rw [hS]
    have hd : Dense ((Submodule.span ℂ {v | ∃ w y, v = T w y} : Submodule ℂ H) : Set H) :=
      Submodule.dense_iff_topologicalClosure_eq_top.2 hspan
    refine Submodule.dense_iff_topologicalClosure_eq_top.1 ?_
    have e2 : (Submodule.span ℂ ((A.toLinearEquiv : H →ₗ[ℂ] H') '' {v | ∃ w y, v = T w y}) : Set H') =
        (A.toLinearEquiv : H →ₗ[ℂ] H') '' (Submodule.span ℂ {v | ∃ w y, v = T w y} : Set H) := by
      rw [Submodule.span_image, Submodule.map_coe]
    have e3 : (A.toLinearEquiv : H →ₗ[ℂ] H') '' {v | ∃ w y, v = T w y} = A '' {v | ∃ w y, v = T w y} := rfl
    rw [← e3, e2]
    exact A.surjective.denseRange.dense_image A.continuous hd

theorem not_isIntegralOp_zero {G W : Type} [Group G] [MeasurableSpace G] [AddCommGroup W] [Module ℂ W]
    {ν : Measure G} {σ : Representation ℂ G W} {F : G → ℂ} {c : ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ F c) (hc : c ≠ 0) : ¬ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ F 0 := by
  intro h0
  obtain ⟨A, hA, -, rfl⟩ := h
  obtain rfl := hA.unique h0
  refine hc ?_
  have e : (LinearMap.restrict (0 : W →ₗ[ℂ] W) (p := LinearMap.range (0 : W →ₗ[ℂ] W))
      (q := LinearMap.range (0 : W →ₗ[ℂ] W)) fun v _ => LinearMap.mem_range_self _ v) = 0 :=
    LinearMap.ext fun x => Subtype.ext rfl
  rw [e, map_zero]

theorem specTrace : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.HarishChandraCharacters → (∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.CuspidalOperators V μ) → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → SpecTrace := by
  intro hDSC _ _ _ hFlath hChar hCO hPCT hPCS
  intro D V lam S M T U μa μf μ _ _ fa ff hTD ν hν n Ws _ _ σs hIrr hcover c hc
  have hcusp := GlobalTheory.T.discrete_series_multiplicity hCO hPCT D V lam S M T U μa μf μ fa ff hTD
  have hpone := GlobalTheory.T.discrete_series_model_trace_terms hDSC hFlath hChar hPCS D V lam S M T U μa μf μ fa ff hTD ν hν
  refine ⟨hcusp.traceClass, ?_⟩
  refine GlobalTheory.T.eq_sum_of_hasSum_of_bijective_matching (UDual (GA D V)) n (fun x => (mCusp V μ x.rep.π).toNat)
    (fun x => repTrace x.rep.π μ (tensor D.sp.cm.sig V.gram fa ff)) (fun i => (mCuspDS μ (σs i) M).toNat) c
    (fun x i => IsCopyFinDS (σs i) M x.rep.π ⊤) _ hcusp.hasSum_trace ?_ ?_ ?_ ?_ ?_
  ·
    intro x hm ht
    have hm' : mCusp V μ x.rep.π ≠ 0 := fun h => hm (by rw [h]; simp)
    have htr : HasTrace (repOp x.rep.π μ (tensor D.sp.cm.sig V.gram fa ff))
        (repTrace x.rep.π μ (tensor D.sp.cm.sig V.gram fa ff)) := ⟨hcusp.traceClass_rep x hm', rfl⟩
    obtain ⟨W, _, _, σ, hσi, hσa, hcopy, hσt⟩ := hpone x.rep.H x.rep.π x.rep.isIrr _ htr ht
    have hmσ : mCuspDS μ σ M ≠ 0 := by
      rwa [← GlobalTheory.T.cuspMultiplicity_completion_eq_discreteSeriesModel D V S M μ x.rep.H x.rep.π x.rep.isIrr W σ hσi hσa hcopy]
    obtain ⟨i, ⟨f⟩⟩ := hcover W σ hσi hσa hmσ (not_isIntegralOp_zero hσt ht)
    exact ⟨i, isCopyFinDS_of_equiv f hcopy⟩
  ·
    intro i hi
    have hi' : mCuspDS μ (σs i) M ≠ 0 := fun h => hi (by rw [h]; simp)
    obtain ⟨H, _, _, π, hπ, hcopy⟩ := GlobalTheory.T.exists_irreducibleUnitary_completion_finiteTimesDS D V S M μ (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hi'
    let R : IrrU (GA D V) := ⟨H, π, hπ⟩
    refine ⟨R.cl, isCopyFinDS_of_uEquiv ?_ hcopy⟩
    exact (IrrU.cl_eq_iff.1 (UDual.cl_rep R.cl)).symm
  ·
    intro x i hR
    refine ⟨?_, ?_⟩
    · rw [GlobalTheory.T.cuspMultiplicity_completion_eq_discreteSeriesModel D V S M μ x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hR]
    · exact (GlobalTheory.T.test_data_haar_factorization D V lam S M T U μa μf μ fa ff hTD ν hν x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i)
        (hIrr.1 i) (hIrr.2.1 i) hR (c i) (hc i)).2
  ·
    intro x i j hi hj
    by_contra hne
    have e := (GlobalTheory.T.unitaryEquiv_iff_finitePart_equiv_discreteSeries D V S M x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hi
      x.rep.H x.rep.π x.rep.isIrr (Ws j) (σs j) (hIrr.1 j) (hIrr.2.1 j) hj).1 (UEquiv.refl _)
    exact (hIrr.2.2 i j hne).false e.some
  ·
    intro x y i hx hy
    have e := (GlobalTheory.T.unitaryEquiv_iff_finitePart_equiv_discreteSeries D V S M x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hx
      y.rep.H y.rep.π y.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hy).2 ⟨Representation.Equiv.refl _⟩
    rw [← UDual.cl_rep x, ← UDual.cl_rep y]
    exact IrrU.cl_eq_iff.2 e

end GlobalTheory.SpecTraceProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneSubbundleSplitAtPoints
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.QCoh

namespace GlobalTheory.VB

theorem exists_forall_isUnit_sum_mul {κ : Type} [Field κ] [Infinite κ] {T : Type} [Finite T]
    (R : T → Type) [∀ t, CommRing (R t)] [∀ t, IsLocalRing (R t)] (σ : ∀ t, κ →+* R t) {k : ℕ}
    (u : ∀ t, Fin k → R t) (hu : ∀ t, ∃ i, IsUnit (u t i)) :
    ∃ c : Fin k → κ, ∀ t, IsUnit (∑ i, σ t (c i) * u t i) := by
  let p : T → Submodule κ (Fin k → κ) := fun t =>
    { carrier := {c | ∑ i, σ t (c i) * u t i ∈ IsLocalRing.maximalIdeal (R t)}
      add_mem' := fun {a b} ha hb => by
        simpa [add_mul, Finset.sum_add_distrib] using Ideal.add_mem _ (Set.mem_setOf.1 ha) (Set.mem_setOf.1 hb)
      zero_mem' := by simp
      smul_mem' := fun a c hc => by
        simpa [Finset.mul_sum, mul_assoc] using Ideal.mul_mem_left _ (σ t a) (Set.mem_setOf.1 hc) }
  obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p fun t ht => by
    obtain ⟨i, hi⟩ := hu t
    have h : ∑ j, σ t ((Pi.single i 1 : Fin k → κ) j) * u t j ∈ IsLocalRing.maximalIdeal (R t) :=
      ht.ge (Submodule.mem_top (x := Pi.single i 1))
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, map_one,
      one_mul] at h
    exact h hi
  exact ⟨c, fun t => not_not.1 (hc t)⟩

theorem exists_retraction_of_isUnit {R P M : Type} [CommRing R] [AddCommGroup P] [Module R P]
    [AddCommGroup M] [Module R M] (g : Module.Basis (Fin 1) R P) (f : P →ₗ[R] M) (l : M →ₗ[R] R)
    (h : IsUnit (l (f (g 0)))) : ∃ ρ : M →ₗ[R] P, ρ ∘ₗ f = LinearMap.id := by
  obtain ⟨v, hv⟩ := h.exists_left_inv
  refine ⟨(v • l).smulRight (g 0), g.ext fun i => ?_⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [hv]

variable {X : Scheme.{0}} {F G : X.Modules}

theorem stalkLinear_finset_sum {ι : Type} (s : Finset ι) (φ : ι → (G ⟶ F)) (x : X) :
    stalkLinear (∑ i ∈ s, φ i) x = ∑ i ∈ s, stalkLinear (φ i) x :=
  map_sum (AddMonoidHom.mk' (fun ψ : G ⟶ F => stalkLinear ψ x) fun a b => stalkLinear_add a b x) φ s

theorem stalkLinear_smulHom_apply (a : Γ(X, ⊤)) (x : X) (t : (F.presheaf.stalk x :)) :
    stalkLinear (smulHom F a) x t = X.presheaf.germ ⊤ x trivial a • t := by
  obtain ⟨V, hV, s, rfl⟩ := F.presheaf.exists_germ_eq t
  rw [stalkLinear_germ, smulHom_app_apply, germ_smul]
  exact congrArg (· • _) (X.presheaf.germ_res_apply _ x hV a)

theorem eq_top_of_epi_sigma {k : ℕ} (φ : (∐ fun _ : Fin k => G) ⟶ F) [Epi φ] (x : X)
    (N : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :))
    (h : ∀ i t, stalkLinear (Sigma.ι (fun _ : Fin k => G) i ≫ φ) x t ∈ N) : N = ⊤ := by
  have := Abelian.hasFiniteBiproducts (C := X.Modules)
  let e := biproduct.isoCoproduct fun _ : Fin k => G
  have he : e.hom ≫ φ = ∑ i, biproduct.π (fun _ : Fin k => G) i ≫
      Sigma.ι (fun _ : Fin k => G) i ≫ φ := by
    rw [biproduct.isoCoproduct_hom, biproduct.desc_eq, Preadditive.sum_comp]
    simp only [Category.assoc]
  refine top_le_iff.1 fun t _ => ?_
  obtain ⟨t, rfl⟩ := stalkLinear_surjective (e.hom ≫ φ) x t
  rw [he, stalkLinear_finset_sum, LinearMap.sum_apply]
  refine sum_mem fun i _ => ?_
  rw [stalkLinear_comp]
  exact h i _

theorem IsTorsionFree.mono_of_injective_generic [IsIntegral X] (h : IsTorsionFree G) (φ : G ⟶ F)
    (hφ : Function.Injective (stalkLinear φ (genericPoint X))) : Mono φ := by
  refine mono_of_locally_app_injective _ fun W x hx => ⟨W, hx, le_rfl, fun a b e => ?_⟩
  have hη := genericPoint_mem hx
  refine sub_eq_zero.1 (h W hη _ (hφ ?_))
  rw [map_sub, map_sub, stalkLinear_germ, stalkLinear_germ, map_zero, sub_eq_zero]
  exact congrArg _ e

theorem exists_line_subsheaf_split_at_finite : ∀ (κ : Type) [Field κ] [Infinite κ] (C : Scheme.{0})
    [Algebra κ Γ(C, ⊤)] [IsIntegral C], IsProjOver (strHom κ C) → ∀ (F : C.Modules) (r : ℕ),
    IsVB F (r + 1) → ∀ S : Set C, S.Finite → ∃ (G : C.Modules) (φ : G ⟶ F), IsVB G 1 ∧ Mono φ ∧
      ∀ x ∈ S, ∃ ρ : (F.presheaf.stalk x :) →ₗ[C.presheaf.stalk x] (G.presheaf.stalk x :),
        ρ ∘ₗ GlobalTheory.QCoh.stalkLinear φ x = LinearMap.id := by
  intro κ _ _ C _ _ hp F r hF S hS
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  have := hF.isFiniteQC
  obtain ⟨n, k, φ, hφ⟩ := (hA.eventually_exists_epi_sigma F).exists
  have hG := isVB_toMod (Twist.isLB_lbZPow hA.isLB (-n))
  generalize GlobalTheory.LB.toMod (lbZPow A (-n)) = G at φ hφ hG
  let ψ : Fin k → (G ⟶ F) := fun i => Sigma.ι (fun _ : Fin k => G) i ≫ φ
  have b := fun x => (hF.nonempty_basis_stalk x).some
  have g := fun x => (hG.nonempty_basis_stalk x).some
  let T : Set C := insert (genericPoint C) S
  have : Finite T := (hS.insert _).to_subtype
  obtain ⟨c, hc⟩ := exists_forall_isUnit_sum_mul (fun x : T => C.presheaf.stalk x.1)
    (fun x => (C.presheaf.germ ⊤ x.1 trivial).hom.comp (algebraMap κ Γ(C, ⊤)))
    (fun x i => (b x.1).coord 0 (stalkLinear (ψ i) x.1 (g x.1 0))) fun x => by
      by_contra! H
      have h := eq_top_of_epi_sigma φ x.1
        (Submodule.comap ((b x.1).coord 0) (IsLocalRing.maximalIdeal (C.presheaf.stalk x.1)))
        fun i t => by
          rw [Submodule.mem_comap, ← (g x.1).sum_repr t, Fin.sum_univ_one, map_smul, map_smul]
          exact Ideal.mul_mem_left _ _ (H i)
      have h1 := h.ge (Submodule.mem_top (x := b x.1 0))
      rw [Submodule.mem_comap, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_eq_same] at h1
      exact h1 isUnit_one
  let α : G ⟶ F := ∑ i, ψ i ≫ smulHom F (algebraMap κ Γ(C, ⊤) (c i))
  have key : ∀ x ∈ T, ∃ ρ : (F.presheaf.stalk x :) →ₗ[C.presheaf.stalk x] (G.presheaf.stalk x :),
      ρ ∘ₗ stalkLinear α x = LinearMap.id := fun x hx => by
    refine exists_retraction_of_isUnit (g x) _ ((b x).coord 0) ?_
    convert hc ⟨x, hx⟩ using 1
    rw [stalkLinear_finset_sum, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [stalkLinear_comp, LinearMap.comp_apply, stalkLinear_smulHom_apply, map_smul]
    rfl
  refine ⟨G, α, hG, hG.isTorsionFree.mono_of_injective_generic α ?_,
    fun x hx => key x (Set.mem_insert_of_mem _ hx)⟩
  obtain ⟨ρ, hρ⟩ := key _ (Set.mem_insert _ _)
  exact LinearMap.injective_of_comp_eq_id _ _ hρ

end GlobalTheory.VB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFibreProjectiveCurve
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.ratFibre

theorem isIntegral_of_flat_preimmersion {X Y : Scheme.{0}} [IsIntegral X] [Nonempty Y] (j : Y ⟶ X)
    [Flat j] [IsPreimmersion j] : IsIntegral Y := by
  have hred (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
    have h1 := Flat.stalkMap j y
    have h2 := j.stalkMap_surjective y
    algebraize [(j.stalkMap y).hom]
    have : IsLocalHom (algebraMap (X.presheaf.stalk (j y)) (Y.presheaf.stalk y)) :=
      inferInstanceAs (IsLocalHom (j.stalkMap y).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (j y))
      (B := Y.presheaf.stalk y)
    exact isReduced_of_injective (RingEquiv.ofBijective (j.stalkMap y).hom
      ⟨FaithfulSMul.algebraMap_injective (X.presheaf.stalk (j y)) (Y.presheaf.stalk y), h2⟩).symm
      (RingEquiv.injective _)
  have : IsReduced Y := isReduced_of_isReduced_stalk Y
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  obtain ⟨η, -, hη⟩ := Flat.generalizingMap j (genericPoint_specializes (j y₀))
  have hg : IsGenericPoint η (Set.univ : Set Y) := by
    refine Set.eq_univ_of_forall fun y => specializes_iff_mem_closure.1 ?_
    rw [← j.isEmbedding.isInducing.specializes_iff, hη]
    exact genericPoint_specializes _
  have : IrreducibleSpace Y := (irreducibleSpace_def Y).2 hg.isIrreducible
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

theorem dim_eq_of_isPullback {X Y : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp ℤ) [IsProper f] [Flat f]
    {j : Y ⟶ X} {q : Y ⟶ Sp ℚ} (H : IsPullback j q f (spMap (algebraMap ℤ ℚ))) {D : ℕ}
    (hD : topologicalKrullDim X = (D + 1 : ℕ)) : topologicalKrullDim Y = D := by
  obtain ⟨A, _, _, _, _, _, i, _, -, -, hA⟩ := exists_affine_chart_trdeg_eq f (genericPoint X)
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast ℤ (A := A)
  rw [hA] at hd
  have h₁ := topologicalKrullDim_preimage_genericPoint_eq f hd
  have := IsPreimmersion.of_isLocalization (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)
  obtain ⟨e₁, r₁⟩ := isEmbedding_and_range_eq_of_isPullback f H
  have hr₁ : Set.range (spMap (algebraMap ℤ ℚ)) = {genericPoint (Spec (.of ℤ))} := by
    refine Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨Set.range_nonempty _, ?_⟩
    rintro _ ⟨x, rfl⟩
    rw [genericPoint_eq_bot_of_affine]
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (algebraMap ℤ ℚ) x.asIdeal = ⊥
    have := x.isPrime
    rw [Ideal.eq_bot_of_prime x.asIdeal]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective ℤ ℚ)
  rw [hr₁] at r₁
  have h₂ := (topologicalKrullDim_eq_of_isEmbedding e₁ r₁).symm.trans h₁
  have h₃ := IntModel.topologicalKrullDim_eq_succ Int.not_isField H h₂
  have h₄ : D + 1 = d + 1 := by exact_mod_cast hD.symm.trans h₃
  obtain rfl : D = d := by omega
  exact h₂

theorem isProjCurve (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (h : IsArithVar p 1) :
    IsProjCurve ℚ (ratFibre p) := by
  have := h.finite
  have := h.isIntegral
  have := h.flat
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 h.finite
  obtain ⟨_, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 h.isProjOver
  have hP : IsProjOver (p ≫ spMap (Int.castRingHom k)) := hL.isProjOver _
  have H : IsPullback (fst p) (snd p) (p ≫ spMap (Int.castRingHom k)) (spMap (algebraMap ℤ ℚ)) :=
    isPullback p
  have hd : topologicalKrullDim (ratFibre p) = (1 : ℕ) := dim_eq_of_isPullback _ H h.dim_eq
  have : Nonempty (ratFibre p) := by
    by_contra hn
    have : IsEmpty (ratFibre p) := not_nonempty_iff.1 hn
    have : IsEmpty (IrreducibleCloseds (ratFibre p)) :=
      ⟨fun Z => Z.isIrreducible.nonempty.elim fun x _ => isEmptyElim x⟩
    rw [topologicalKrullDim, Order.krullDim_eq_bot] at hd
    exact absurd hd (by decide)
  have h₁ : IsPreimmersion (spMap (algebraMap ℤ ℚ)) :=
    IsPreimmersion.of_isLocalization (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)
  have h₂ : Flat (spMap (algebraMap ℤ ℚ)) :=
    (flat_int_iff_charZero _).2 (((Scheme.ΓSpecIso (.of ℚ)).commRingCatIsoToRingEquiv.toRingHom.charZero_iff
      (Scheme.ΓSpecIso (.of ℚ)).commRingCatIsoToRingEquiv.injective).2 (inferInstanceAs (CharZero ℚ)))
  have : IsPreimmersion (fst p) := MorphismProperty.of_isPullback H.flip h₁
  have : Flat (fst p) := MorphismProperty.of_isPullback H.flip h₂
  refine ⟨isIntegral_of_flat_preimmersion (fst p), hd.trans Nat.cast_one, ?_⟩
  rw [strHom_eq]
  exact ProjSpace.isProjOver_of_isPullback_spMap _ H hP

end GlobalTheory.ratFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidTranslateLineBundleRationalPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_rigidTranslateLineBundle_rationalPoint : ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), L.IsLB → ∀ a : 𝟙_ (Over (Sp K)) ⟶ B, Out.RelAmple B L → Out.RelAmple B (GlobalTheory.RigidTranslate.rigTransl L a) := by
  first | exact @GlobalTheory.RigidTranslate.relAmple_rigTransl_point | exact GlobalTheory.RigidTranslate.relAmple_rigTransl_point | (intros; apply GlobalTheory.RigidTranslate.relAmple_rigTransl_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfArtinianSquareZeroLiftingNoetherianBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_of_artinian_squareZero_lifting_noetherian_base : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (X : Scheme.{0}) (s : X ⟶ Sp B), LocallyOfFiniteType s → (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp B) (x₀ : Sp C₀ ⟶ X), x₀ ≫ s = spMap π ≫ t → ∃ x : Sp C ⟶ X, spMap π ≫ x = x₀ ∧ x ≫ s = t) → Smooth s := by
  first | exact @GlobalTheory.SmoothCrit.smooth_of_artinian_lift | exact GlobalTheory.SmoothCrit.smooth_of_artinian_lift | (intros; apply GlobalTheory.SmoothCrit.smooth_of_artinian_lift <;> assumption)
end

