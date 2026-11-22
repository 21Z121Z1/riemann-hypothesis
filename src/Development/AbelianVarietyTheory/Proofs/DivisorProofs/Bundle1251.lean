import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1190
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRealPointsFixFiniteAdelicHomsStatement
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRealPoints_fix_finiteAdelicHoms : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (g : GAF σ JS) (h : GAF σ JT),
      g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS → h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT → ∀ u : WOF F E nS nT, u.map (infPartF F E) = 0 →
        actOF σ JS JT g h u = u := by
  first | exact @GlobalTheory.RealWeilFinFix.actOF_fin | exact GlobalTheory.RealWeilFinFix.actOF_fin | (intros; apply GlobalTheory.RealWeilFinFix.actOF_fin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRepUpqMatrixFunction
section
section

noncomputable section

namespace GlobalTheory.PsCo.PcEF.MatrixRepresentation

variable {n : ℕ} (ε : Fin n → Bool) {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

abbrev mat (g : Formalism.REAL.UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

theorem mat_injective : Function.Injective (mat ε) := fun _ _ h => Subtype.ext (Units.ext h)

def rep (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (x : Matrix (Fin n) (Fin n) ℂ) : X →L[ℂ] X := by
  classical exact if h : ∃ g, mat ε g = x then π h.choose else 1

theorem rep_mat (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (g : Formalism.REAL.UJ ε) : rep ε π (mat ε g) = π g := by
  have h : ∃ g', mat ε g' = mat ε g := ⟨g, rfl⟩
  rw [rep, dif_pos h, mat_injective ε h.choose_spec]

theorem range_mat : Set.range (mat ε) = Formalism.MainNotions.S.UJset ε := (Formalism.REAL.isClosedEmbeddingMatrix n ε).2

theorem mat_mem (g : Formalism.REAL.UJ ε) : mat ε g ∈ Formalism.MainNotions.S.UJset ε := range_mat ε ▸ ⟨g, rfl⟩

theorem exists_mat {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ Formalism.MainNotions.S.UJset ε) : ∃ g, mat ε g = x := by
  rw [← range_mat ε] at hx; exact hx

theorem isEmbedding_mat : Topology.IsEmbedding (mat ε) := (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding

end GlobalTheory.PsCo.PcEF.MatrixRepresentation

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEF.MatrixRepresentation

theorem unitaryRep_upq_matrixFunction : MatRep := by
  intro n ε U _ _ π hπ hi
  refine ⟨rep ε π, ⟨⟨?_, fun a ha b hb => ?_⟩, fun a ha v => ?_, fun v => ?_⟩, fun S hS hinv => ?_, fun g => rep_mat ε π g⟩
  · have h1 : mat ε 1 = 1 := rfl
    rw [← h1, rep_mat, map_one]
  · obtain ⟨g, rfl⟩ := exists_mat ε ha
    obtain ⟨h, rfl⟩ := exists_mat ε hb
    have hm : mat ε g * mat ε h = mat ε (g * h) := rfl
    rw [hm, rep_mat, rep_mat, rep_mat, map_mul]
    rfl
  · obtain ⟨g, rfl⟩ := exists_mat ε ha
    rw [rep_mat]
    exact hπ.norm_apply g v
  · have hr : Formalism.MainNotions.S.UJset ε = Set.range (mat ε) := (range_mat ε).symm
    show ContinuousOn (fun g => rep ε π g v) (Formalism.MainNotions.S.UJset ε)
    rw [hr, continuousOn_iff_continuous_domRestrict]
    let E := (isEmbedding_mat ε).toHomeomorph
    have hE : ∀ y, (fun g => π g v) (E.symm y) = rep ε π (y : Matrix (Fin n) (Fin n) ℂ) v := by
      intro y
      obtain ⟨g, rfl⟩ := E.surjective y
      show π (E.symm (E g)) v = rep ε π (mat ε g) v
      rw [E.symm_apply_apply, rep_mat]
    exact ((hπ.continuous_apply v).comp E.symm.continuous).congr hE
  · exact hi.2 S ⟨hS, fun g v hv => by simpa [rep_mat] using hinv _ (mat_mem ε g) v hv⟩

end GlobalTheory.PsCo.PcEF

end
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumRealRestrictionSatisfiesStandardThetaLaw
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacRealForm

theorem vacuum_real_law : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (σ : (D.what₂.Tau → ℂ) →+ AE D) (δ : ℂ), GlobalTheory.FockCompare.Chart W.θ σ → Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D (G.pS (.top t j)).rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D (G.pT (.top t j)).rank), ∀ Y, Formalism.MainNotions.TaylorLogMetric.al D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) x * Formalism.MainNotions.TaylorLogMetric.U D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) x (GlobalTheory.VacRealForm.thY σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f δ) Y = GlobalTheory.VacRealForm.thY σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f δ Y := by
  intro D T L sc G W U N σ δ hσ hcrv hδ t j hj f hf x hx Y
  obtain ⟨M, hM, rfl⟩ := GlobalTheory.T.torusLattice_standard_points_scaled_embedding δ x hx
  have hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (N.fr (.top j)).1 * (G.V (.top j)).gram * (N.fr (.top j)).1 = 1 :=
    N.fr_on (.top j) (show j ≤ D.R.m by omega)
  have hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (N.fr (.top (j + 1))).1 * (G.V (.top (j + 1))).gram *
      (N.fr (.top (j + 1))).1 = 1 := N.fr_on (.top (j + 1)) (show j + 1 ≤ D.R.m from hj)
  have hlat := GlobalTheory.T.orthonormalFrame_finitePart_mem_completedLattice (G.V (.top j)) (G.V (.top (j + 1))) (N.fr (.top j)) (N.fr (.top (j + 1))) hS M hM
  obtain ⟨k, hk, heig⟩ := GlobalTheory.T.heisenbergOperator_finitePart_latticeVacuum_sign W.ψ (G.V (.top j)) (G.V (.top (j + 1))) (colLat (N.fr (.top j))) (colLat (N.fr (.top (j + 1))))
    hf.1 (GlobalTheory.T.isSelfDualC_columnLattice_of_orthonormalFrame _ _ hS) (GlobalTheory.T.isSelfDualC_columnLattice_of_orthonormalFrame _ _ hT) f hf.2.lat _ hlat
  have hlaw := GlobalTheory.VacUnique.apply_add_infRat hσ hf.1 hf.2.theta _ heig
  rw [GlobalTheory.T.rationalPoint_finitePart_isotropic_pairing, neg_zero, AddChar.map_zero_eq_one, one_mul] at hlaw
  have hU := GlobalTheory.T.torusTranslate_thetaCoordinate_of_realPart_law σ (G.V (.top j)) (G.V (.top (j + 1))) (N.fr (.top j)) (N.fr (.top (j + 1))) hS hT δ hδ M f _ hlaw Y
  have hal := GlobalTheory.T.torusSemicharacter_eq_neg_one_pow_traceExponent (G.V (.top j)) (G.V (.top (j + 1))) (N.fr (.top j)) (N.fr (.top (j + 1))) hS hT δ hδ M k hk
  show Formalism.MainNotions.TaylorLogMetric.al D _ _ * Formalism.MainNotions.TaylorLogMetric.U D _ _ (thY σ (G.V (.top j)) (G.V (.top (j + 1))) (fun τ => (N.fr (.top j)).1.map (tauE D τ))
    (fun τ => (N.fr (.top (j + 1))).1.map (tauE D τ)) f δ) Y = _
  rw [hU, ← mul_assoc, hal, one_mul]
  rfl

end GlobalTheory.VacRealForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValResultantCharpolyShiftedUnitAdjoinRootStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.val_resultant_charpoly_shifted_unit_adjoinRoot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (k : ℕ) (t : K.O), t ≠ 0 → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (a b : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K), Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → Algebra.adjoin K.E {(1 + algebraMap K.O B₁.A t * B₁.g)} = ⊤ → aeval (1 + algebraMap K.O B₁.A t * B₁.g) (Q₁.map e.symm.toRingHom) = 0 → Module.finrank K.E B₁.A = Q₁.natDegree → Algebra.adjoin K.E {(1 + algebraMap K.O B₂.A t * B₂.g)} = ⊤ → aeval (1 + algebraMap K.O B₂.A t * B₂.g) (Q₂.map e.symm.toRingHom) = 0 → Module.finrank K.E B₂.A = Q₂.natDegree → (B₁.P * B₂.P).Separable ∧ GlobalTheory.UnitLemma.val K.O (resultant B₁.P B₂.P) = ordL (resultant Q₁ Q₂) - ((k * a * b : ℕ) : ℤ) := by
  first | exact @GlobalTheory.UnitLemma.ShiftRes.val_resultant_shift | exact GlobalTheory.UnitLemma.ShiftRes.val_resultant_shift | (intros; apply GlobalTheory.UnitLemma.ShiftRes.val_resultant_shift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationEqOrConjOfUnderMaximalRealSubfieldEq
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.BCT

theorem valuation_eq_or_eq_conj_of_under_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w u : Pl E), u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → (∀ y : E, w.valuation E y = u.valuation E y) ∨ (∀ y : E, w.valuation E y = u.valuation E (IsCMField.complexConj E y)) := by
  intro E _ _ _ w u h
  set σ : E ≃+* E := (IsCMField.complexConj E).toRingEquiv with hσ
  set e : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv σ with he
  have hc : ∀ x : 𝓞 E, ((e x : 𝓞 E) : E) = IsCMField.complexConj E (x : E) := fun x => rfl
  have hmem : ∀ x ∈ w.asIdeal, x ∈ u.asIdeal ∨ e x ∈ u.asIdeal := by
    intro x hx
    have hfix : IsCMField.complexConj E (((x * e x : 𝓞 E)) : E) = ((x * e x : 𝓞 E) : E) := by
      have h1 : ((x * e x : 𝓞 E) : E) = (x : E) * IsCMField.complexConj E (x : E) := by
        rw [← hc]; rfl
      rw [h1, map_mul, IsCMField.complexConj_apply_apply, mul_comm]
    have hF : ((x * e x : 𝓞 E) : E) ∈ maximalRealSubfield E :=
      (IsCMField.complexConj_eq_self_iff E _).1 hfix
    have hint : IsIntegral ℤ (⟨_, hF⟩ : maximalRealSubfield E) := by
      have := (x * e x).isIntegral_coe
      exact (isIntegral_algebraMap_iff (algebraMap (maximalRealSubfield E) E).injective).1 this
    have hz : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) ⟨_, hint⟩ = x * e x :=
      RingOfIntegers.ext rfl
    have h1 : (⟨_, hint⟩ : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      change algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) _ ∈ w.asIdeal
      rw [hz]
      exact Ideal.mul_mem_right _ _ hx
    rw [← h] at h1
    change algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) _ ∈ u.asIdeal at h1
    rw [hz] at h1
    exact u.isPrime.mem_or_mem h1
  have hsub : (w.asIdeal : Set (𝓞 E)) ⊆ (u.asIdeal : Set (𝓞 E)) ∪
      (u.comap (e : 𝓞 E →+* 𝓞 E) e.surjective).asIdeal := fun x hx => hmem x hx
  rcases Ideal.subset_union.1 hsub with h2 | h2
  · left
    have : w = u := HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top h2)
    subst this
    intro y; rfl
  · right
    intro y
    exact GlobalTheory.QNorm.valuation_of_eq_comap σ u w
      (w.isMaximal.eq_of_le (u.comap (e : 𝓞 E →+* 𝓞 E) e.surjective).isPrime.ne_top h2) y

end GlobalTheory.BCT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachModuleMapMatrixCompMulStatement
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachModuleMapMatrix_comp_mul : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (T T' T'' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (n n' n'' : ℕ) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T)) (b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T')) (b'' : Module.Basis (Fin n'') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T'')) (g : LatHom T.L T'.L) (g' : LatHom T'.L T''.L) (g'' : LatHom T.L T''.L) (A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n' n) (A' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n'' n') (A'' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n'' n), IsMapMat (H.W K 1 LL hA.2.2) g b b' A → IsMapMat (H.W K 1 LL hA.2.2) g' b' b'' A' → IsMapMat (H.W K 1 LL hA.2.2) g'' b b'' A'' → (∀ x, g''.f x = g'.f (g.f x)) → ∀ i, A'' i = A' i * A i := by
  first | exact @GlobalTheory.WachPlace.isMapMat_comp_mul | exact GlobalTheory.WachPlace.isMapMat_comp_mul | (intros; apply GlobalTheory.WachPlace.isMapMat_comp_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachRingFactsUnramifiedLevelOneStatement
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachRingFacts_unramified_levelOne : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL), RingFacts (H.W K 1 LL hA.2.2) := by
  first | exact @GlobalTheory.WachPlace.ringFacts_of_caseA | exact GlobalTheory.WachPlace.ringFacts_of_caseA | (intros; apply GlobalTheory.WachPlace.ringFacts_of_caseA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilQDivisorAvoidsPointCartierIffNotMemSuppStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilQDivisorAvoidsPoint_cartier_iff_notMem_supp : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (D₀ : CartierDiv X) (m : ℕ) (z : X), D₀.Eff → 0 < m → (Off (qWeil D₀ m) z ↔ z ∉ D₀.supp) := by
  first | exact @GlobalTheory.PairStep.off_qWeil_iff_notMem_supp | exact GlobalTheory.PairStep.off_qWeil_iff_notMem_supp | (intros; apply GlobalTheory.PairStep.off_qWeil_iff_notMem_supp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerBumpFiniteFactorProperties
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

namespace GlobalTheory.WhitBump.FinBump

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

theorem psiFin_add (a b : Af E) : psiFin (a + b) = psiFin a * psiFin b := by
  simp only [psiFin, map_add, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem bumpFin_eq (hK : ∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n),
      u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n → psiFin (GlobalTheory.Whittaker.superDiag u) = 1)
    {g u : GL (Fin n) (Af E)} (hu : u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n))
    (hg : u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n) :
    bumpFin g = psiFin (GlobalTheory.Whittaker.superDiag u) := by
  have h : ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n :=
    ⟨u, hu, hg⟩
  unfold bumpFin
  rw [dif_pos h]
  obtain ⟨hu', hg'⟩ := h.choose_spec
  set u' := h.choose
  have hw : u⁻¹ * u' ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n) := mul_mem (inv_mem hu) hu'
  have hwK : u⁻¹ * u' ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n := by
    have : u⁻¹ * u' = (u⁻¹ * g) * (u'⁻¹ * g)⁻¹ := by group
    rw [this]; exact mul_mem hg (inv_mem hg')
  have hsplit : u' = u * (u⁻¹ * u') := by group
  rw [hsplit, GlobalTheory.GamMul.UnipPlaced.superDiag_mul_unip hu hw, psiFin_add, hK _ hw hwK, mul_one]

end GlobalTheory.WhitBump.FinBump

namespace GlobalTheory.WhitBump.FinBump

theorem bumpFin_zero_of_not {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}
    {g : GL (Fin n) (Af E)}
    (h : ¬ ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n) :
    bumpFin g = 0 := by
  unfold bumpFin; rw [dif_neg h]

theorem bumpFin_props : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ),
    (∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n →
      psiFin (GlobalTheory.Whittaker.superDiag u) = 1) →
    bumpFin (E := E) (n := n) 1 = 1 ∧
    (∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), ∀ g, bumpFin (u * g) = psiFin (GlobalTheory.Whittaker.superDiag u) * bumpFin g) ∧
    (∀ k ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n, ∀ g, bumpFin (g * k) = bumpFin g) ∧
    ∀ g, bumpFin g ≠ 0 → ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n),
      u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n := by
  intro E _ _ _ n hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bumpFin_eq hK (one_mem _) (by simpa using one_mem _), hK 1 (one_mem _) (one_mem _)]
  · intro u hu g
    by_cases h : ∃ v ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), v⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n
    · obtain ⟨v, hv, hvg⟩ := h
      have e : (u * v)⁻¹ * (u * g) = v⁻¹ * g := by group
      rw [bumpFin_eq hK (mul_mem hu hv) (by rw [e]; exact hvg), bumpFin_eq hK hv hvg,
        GlobalTheory.GamMul.UnipPlaced.superDiag_mul_unip hu hv, psiFin_add]
    · rw [bumpFin_zero_of_not h, mul_zero]
      refine bumpFin_zero_of_not fun ⟨v, hv, hvg⟩ => h ⟨u⁻¹ * v, mul_mem (inv_mem hu) hv, ?_⟩
      have e : (u⁻¹ * v)⁻¹ * g = v⁻¹ * (u * g) := by group
      rw [e]; exact hvg
  · intro k hk g
    by_cases h : ∃ v ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), v⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n
    · obtain ⟨v, hv, hvg⟩ := h
      have e : v⁻¹ * (g * k) = (v⁻¹ * g) * k := by group
      rw [bumpFin_eq hK hv (by rw [e]; exact mul_mem hvg hk), bumpFin_eq hK hv hvg]
    · rw [bumpFin_zero_of_not h]
      refine bumpFin_zero_of_not fun ⟨v, hv, hvg⟩ => h ⟨v, hv, ?_⟩
      have e : v⁻¹ * g = (v⁻¹ * (g * k)) * k⁻¹ := by group
      rw [e]; exact mul_mem hvg (inv_mem hk)
  · intro g hg
    by_contra h
    exact hg (bumpFin_zero_of_not h)

end GlobalTheory.WhitBump.FinBump
end

