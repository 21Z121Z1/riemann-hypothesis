import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0337
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0332
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import GroundTheory.AutomorphicForms.Bundle0020
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemRestrictionOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0320
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.BijectiveToPushforwardComp
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0324
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.RedMk
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0322
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0344
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisIsAdicCompleteStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_isAdicComplete_span_prime : ∀ {l : ℕ} [Fact l.Prime], IsAdicComplete (Ideal.span {(l : Acris l)}) (Acris l) := by
  first | exact @GlobalTheory.CompanionTheory.ACrisAdic.acris_isAdicComplete | exact GlobalTheory.CompanionTheory.ACrisAdic.acris_isAdicComplete | (intros; apply GlobalTheory.CompanionTheory.ACrisAdic.acris_isAdicComplete <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicDegreeFormulaStatement
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_degree_formula : MulF → MulI → LogAbsBasic → FinSupp → DegAdelic := by
  first | exact @GlobalTheory.CompanionTheory.DegAdelicProof.degAdelic_of | exact GlobalTheory.CompanionTheory.DegAdelicProof.degAdelic_of | (intros; apply GlobalTheory.CompanionTheory.DegAdelicProof.degAdelic_of <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AmpleTwistSectionsGenerateSubsheaf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem le_of_epi_sectionsHom {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB)
    {P : X.Modules} (S B : Subobject P) (n : ℤ) {k : ℕ}
    (s : Fin k → Γ(GlobalTheory.twistZ (S : X.Modules) H n, ⊤)) (hs : Epi (GlobalTheory.QCoh.sectionsHom s))
    (hB : ∀ i, genSub hH n ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) S.arrow).app ⊤ (s i)) ≤ B) : S ≤ B := by
  have hL' := GlobalTheory.Twist.isLB_lbZPow hH (-n)
  have h₁ := (GlobalTheory.Twist.epi_map_iff hL' (GlobalTheory.QCoh.sectionsHom s)).2 hs
  have := GlobalTheory.Twist.preservesColimits_twistFunctor hL'
  let T := GlobalTheory.twistFunctor (GlobalTheory.lbZPow H (-n))
  let E : T.obj (∐ fun _ : Fin k => GlobalTheory.QCoh.structureModule X) ⟶ (S : X.Modules) :=
    GlobalTheory.Twist.map _ (GlobalTheory.QCoh.sectionsHom s) ≫
      (GlobalTheory.Twist.twistZAddIso (S : X.Modules) hH (add_neg_cancel n)).hom ≫
      (GlobalTheory.Twist.twistZZeroIso (S : X.Modules) hH).inv
  haveI hE : Epi E := epi_comp' h₁ inferInstance
  have key : ∀ i, T.map (Sigma.ι (fun _ : Fin k => GlobalTheory.QCoh.structureModule X) i) ≫ E =
      genHom hH n (s i) := fun i => by
    have e : Sigma.ι (fun _ : Fin k => GlobalTheory.QCoh.structureModule X) i ≫ GlobalTheory.QCoh.sectionsHom s =
        GlobalTheory.QCoh.sectionHom (s i) := Sigma.ι_desc _ _
    rw [genHom, ← e]
    change T.map _ ≫ T.map _ ≫ _ = T.map (_ ≫ _) ≫ _
    exact (Category.assoc (T.map _) (T.map _) _).symm
  let g : ∀ i : Fin k, T.obj (GlobalTheory.QCoh.structureModule X) ⟶ (B : X.Modules) := fun i =>
    factorThruImageSubobject (genHom hH n ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) S.arrow).app ⊤ (s i))) ≫
      Subobject.ofLE _ _ (hB i)
  have hg : ∀ i, g i ≫ B.arrow = genHom hH n (s i) ≫ S.arrow := fun i => by
    rw [← genHom_map_app hH S.arrow n (s i)]
    exact (Category.assoc _ _ _).trans ((congrArg _ (Subobject.ofLE_arrow _)).trans
      (imageSubobject_arrow_comp
        (genHom hH n ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) S.arrow).app ⊤ (s i)))))
  let c := PreservesCoproduct.iso T (fun _ : Fin k => GlobalTheory.QCoh.structureModule X)
  let t : T.obj (∐ fun _ : Fin k => GlobalTheory.QCoh.structureModule X) ⟶ (B : X.Modules) :=
    c.hom ≫ Sigma.desc g
  have ht : t ≫ B.arrow = E ≫ S.arrow := by
    have hι : ∀ i, Sigma.ι (fun _ : Fin k => T.obj (GlobalTheory.QCoh.structureModule X)) i ≫ c.inv =
        T.map (Sigma.ι (fun _ : Fin k => GlobalTheory.QCoh.structureModule X) i) :=
      fun i => ι_comp_sigmaComparison T _ i
    have h₂ : c.inv ≫ t = Sigma.desc g := Iso.inv_hom_id_assoc c _
    have h₃ : c.inv ≫ t ≫ B.arrow = c.inv ≫ E ≫ S.arrow := by
      rw [← Category.assoc, h₂]
      refine Sigma.hom_ext _ _ fun i => ?_
      rw [← Category.assoc, Sigma.ι_desc, hg i, ← key i, ← Category.assoc, ← Category.assoc,
        hι i]
      rfl
    exact (cancel_epi c.inv).1 h₃
  haveI : StrongEpi E := strongEpi_of_epi E
  have sq : CommSq t E B.arrow S.arrow := ⟨ht⟩
  exact Subobject.le_of_comm sq.lift sq.fac_right

theorem le_of_genSub_le : ∀ {X : Scheme.{0}} [IsNoetherian X] {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X}
    (hA : GlobalTheory.IsAmpleLB H) {P : X.Modules} (S : Subobject P), IsCoherent (S : X.Modules) →
    ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ B : Subobject P,
      (∀ b ∈ twSecs H n S, genSub hA.isLB n b ≤ B) → S ≤ B := by
  intro X _ H hA P S hS
  haveI : GlobalTheory.QCoh.IsFiniteQC (S : X.Modules) := ⟨hS.1, hS.2⟩
  obtain ⟨n₀, h₀⟩ := Filter.eventually_atTop.1
    (hA.eventually_isGloballyGenerated_twistZ (S : X.Modules))
  refine ⟨n₀, fun n hn B hB => ?_⟩
  obtain ⟨k, s, hs⟩ := GlobalTheory.QCoh.isGloballyGenerated_iff_spanStalks.1 (h₀ n hn)
  exact le_of_epi_sectionsHom hA.isLB S B n s ((GlobalTheory.QCoh.epi_sectionsHom_iff s).2 hs)
    fun i => hB _ ⟨s i, rfl⟩

end GlobalTheory.CompanionTheory.GE.TwGen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BernsteinZelevinskyGeometricLemmaStatement
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bernstein_zelevinsky_geometric_lemma : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (β γ : Fin n → ℕ), ∃ (K : ℕ) (w : Fin K → Equiv.Perm (Fin n)), (∀ g : GL (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j)) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W), GroundTheory.Automorphic.IsSmooth σ → ∃ V : ℕ → Submodule ℂ (JacquetModule F n γ (parabolicInd F n β σ)), V 0 = ⊥ ∧ V K = ⊤ ∧ Monotone V ∧ ∃ hV : ∀ i (m : levi F n γ), V i ≤ (V i).comap (jacquetRep F n γ (parabolicInd F n β σ) m), ∀ j : Fin K, ∃ Ψ : Representation.IntertwiningMap ((jacquetRep F n γ (parabolicInd F n β σ)).subrepresentation (V (j + 1)) (hV (j + 1))) (indRep (cellLeviSub F β γ (w j)) (normInducing σ γ (w j))), Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ V j := by
  first | exact @GlobalTheory.CompanionTheory.GeomLemmaUniform.geometricLemma_uniform | exact GlobalTheory.CompanionTheory.GeomLemmaUniform.geometricLemma_uniform | (intros; apply GlobalTheory.CompanionTheory.GeomLemmaUniform.geometricLemma_uniform <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockCountReindexEquivsStatement
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_count_reindex_equivs : ∀ {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ} {m : α → Type} {m' : β' → Type} (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (w : Equiv.Perm (Fin N)), ∃ (f : ∀ i, (Σ j, Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)) ≃ m i) (g : ∀ j, (Σ i, Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)) ≃ m' j), ∀ i j (t : Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)), w (e' ⟨j, g j ⟨i, t⟩⟩) = e ⟨i, f i ⟨j, t⟩⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Cell.cell_row_column_partitions | exact GlobalTheory.CompanionTheory.Cell.cell_row_column_partitions | (intros; apply GlobalTheory.CompanionTheory.Cell.cell_row_column_partitions <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemRestrictionOpenStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_system_restriction_open : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩; ∀ {P : X.Modules} {E : (O : Scheme.{0}).Modules}, IsCoherent P → IsCoherent E → ∀ f : P.restrict O.ι ⟶ E, Epi f → ∀ S : ℕ → Subobject E, ClosedSys I E S → ∀ T : (O : Scheme.{0}).IdealSheafData, IsProper (T.subschemeι ≫ ((O : Scheme.{0}) ↘ Spec (.of A))) → Scheme.Modules.SupportedIn (cokernel (S 0).arrow) (T.support : Set (O : Scheme.{0})) → IsClosed (O.ι '' (T.support : Set (O : Scheme.{0}))) ∧ ∃ Sb : ℕ → Subobject P, ClosedSys I P Sb ∧ (∀ e (W : (O : Scheme.{0}).Opens), IsAffineOpen W → ∀ x : Γ(P, O.ι ''ᵁ W), x ∈ secs (Sb e) (O.ι ''ᵁ W) ↔ f.app W ((P.restrictAppIso O.ι W).inv x) ∈ secs (S e) W) ∧ ∀ e (V : X.Opens), Disjoint (V : Set X) (O.ι '' (T.support : Set (O : Scheme.{0}))) → secs (Sb e) V = Set.univ := by
  first | exact @GlobalTheory.CompanionTheory.GE.Extend.extend | exact GlobalTheory.CompanionTheory.GE.Extend.extend | (intros; apply GlobalTheory.CompanionTheory.GE.Extend.extend <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentExtensionSurjectionOpen
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.Present

def toModPullZPowIso {X Y : Scheme.{0}} {L : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hL : L.IsLB) (f : Y ⟶ X) (m : ℤ) :
    GlobalTheory.LB.toMod ((GlobalTheory.lbZPow L m).pull f) ≅ GlobalTheory.LB.toMod (GlobalTheory.lbZPow (L.pull f) m) :=
  (GlobalTheory.Twist.unitTwistIso _).symm ≪≫ (GlobalTheory.Twist.twistZPullIso f hL _ m).symm ≪≫ GlobalTheory.Twist.unitTwistIso _

theorem exists_coherent_epi_restrict {X : Scheme.{0}} [IsNoetherian X] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X)
    (hH : GlobalTheory.IsAmpleLB H) (O : X.Opens) (E : (O : Scheme.{0}).Modules) (hE : IsCoherent E) :
    ∃ P : X.Modules, IsCoherent P ∧ ∃ f : P.restrict O.ι ⟶ E, Epi f := by
  haveI : CompactSpace (O : Scheme.{0}) :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (O : Set X))
  haveI : GlobalTheory.QCoh.IsFiniteQC E := ⟨hE.1, hE.2⟩
  have hA := hH.pull_of_isOpenImmersion O.ι
  obtain ⟨n, k, φ, hφ⟩ := (hA.eventually_exists_epi_sigma E).exists
  have hL := GlobalTheory.Twist.isLB_lbZPow hH.isLB (-n)
  haveI : GlobalTheory.QCoh.IsFiniteQC (GlobalTheory.LB.toMod (GlobalTheory.lbZPow H (-n))) := (GlobalTheory.VB.isVB_toMod hL).isFiniteQC
  let P : X.Modules := ∐ fun _ : Fin k => GlobalTheory.LB.toMod (GlobalTheory.lbZPow H (-n))
  have hP : GlobalTheory.QCoh.IsFiniteQC P := inferInstance
  let e : P.restrict O.ι ≅ ∐ fun _ : Fin k => GlobalTheory.LB.toMod (GlobalTheory.lbZPow (H.pull O.ι) (-n)) :=
    (Scheme.Modules.restrictFunctorIsoPullback O.ι).app P ≪≫
      PreservesCoproduct.iso (Scheme.Modules.pullback O.ι) _ ≪≫
      Sigma.mapIso (fun _ => GlobalTheory.LB.pullbackIso hL O.ι ≪≫ toModPullZPowIso hH.isLB O.ι (-n))
  exact ⟨P, ⟨hP.1, hP.2⟩, e.hom ≫ φ, epi_comp _ _⟩

end GlobalTheory.CompanionTheory.GE.Present
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentNoetherianMaximalSubsheafStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coherent_noetherian_maximal_subsheaf : ∀ {X : Scheme.{0}} [IsNoetherian X] {P : X.Modules}, IsCoherent P → ∀ F : Set (Subobject P), F.Nonempty → (∀ B ∈ F, (B : X.Modules).IsQuasicoherent) → ∃ M ∈ F, ∀ B ∈ F, M ≤ B → B = M := by
  first | exact @GlobalTheory.CompanionTheory.GE.exists_maximal_qcoh_subobject | exact GlobalTheory.CompanionTheory.GE.exists_maximal_qcoh_subobject | (intros; apply GlobalTheory.CompanionTheory.GE.exists_maximal_qcoh_subobject <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CokernelSequenceOperatorSequenceStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cokernel_sequence_operator_sequence : ∀ {X : AlgebraicGeometry.Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules} {T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (hM : GlobalTheory.CompanionTheory.GE.OpSeq (k + 1) M T d), GlobalTheory.CompanionTheory.GE.OpSeq k (GlobalTheory.CompanionTheory.GE.UV.cokSeq M T) (GlobalTheory.CompanionTheory.GE.UV.cokOps hM.comm) d := by
  first | exact @GlobalTheory.CompanionTheory.GE.UV.cokOpSeq | exact GlobalTheory.CompanionTheory.GE.UV.cokOpSeq | (intros; apply GlobalTheory.CompanionTheory.GE.UV.cokOpSeq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompareQuotientBijectiveStatement
section
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compare_quotient_bijective : ∀ (R : Type) [CommRing R] (C : Type 1) [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R) (l n i : ℕ), Function.Bijective ((cmpq A l n).f i) := by
  first | exact @GlobalTheory.CompanionTheory.LsCmp.cmpq_bijective | exact GlobalTheory.CompanionTheory.LsCmp.cmpq_bijective | (intros; apply GlobalTheory.CompanionTheory.LsCmp.cmpq_bijective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjCompactOfDiagonalNilradical
section
noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan.Slice

def dg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (Matrix.diag M)

theorem continuous_dg {n : ℕ} : Continuous (dg (n := n)) :=
  continuous_id.matrix_diag.matrix_diagonal

theorem dg_one_add_mul {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ)
    (hZ : ∀ i, Z i i = 0) : dg ((1 + Z) * Matrix.diagonal a) = Matrix.diagonal a := by
  unfold dg
  congr 1
  funext i
  simp [Matrix.diag_apply, Matrix.mul_diagonal, hZ]

theorem dg_mul_one_add {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ)
    (hZ : ∀ i, Z i i = 0) : dg (Matrix.diagonal a * (1 + Z)) = Matrix.diagonal a := by
  unfold dg
  congr 1
  funext i
  simp [Matrix.diag_apply, Matrix.diagonal_mul, hZ]

theorem isCompact_units {n : ℕ} {B₁ B₂ : Set (Matrix (Fin n) (Fin n) ℂ)}
    (h₁ : IsCompact B₁) (h₂ : IsCompact B₂) :
    IsCompact {u : GL (Fin n) ℂ | u.val ∈ B₁ ∧ (u⁻¹ : GL (Fin n) ℂ).val ∈ B₂} := by
  have h := (Units.isClosedEmbedding_embedProduct
    (α := Matrix (Fin n) (Fin n) ℂ)).isCompact_preimage
      (h₁.prod (h₂.image MulOpposite.continuous_op))
  convert h using 1
  ext u
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, ⟨_, h', rfl⟩⟩
  · rintro ⟨h, ⟨x, hx, e⟩⟩
    have e' : x = (u⁻¹ : GL (Fin n) ℂ).val := MulOpposite.op_injective e
    exact ⟨h, e' ▸ hx⟩

theorem conj_uOf_val {n : ℕ} {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (P : GL (Fin n) ℂ)
    (X : nilrad W₁ W₂) :
    (P⁻¹ * uOf X * P).val = 1 + (P⁻¹ : GL (Fin n) ℂ).val * X.1 * P.val := by
  have h1 : (P⁻¹ : GL (Fin n) ℂ).val * P.val = 1 := by rw [← Units.val_mul]; simp
  simp only [uOf_val, Units.val_mul, mul_add, add_mul, mul_one, h1]

theorem slice_measure_ne_top : ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)] (d : GL (Fin n) ℂ)
  (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure] (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
  (P : GL (Fin n) ℂ), W₁ ≤ W₂ →
  (∀ t ∈ twCent (thC n) d, ∃ a : Fin n → ℂ, (P⁻¹ * t * P).val = Matrix.diagonal a) →
  (∀ X ∈ nilrad W₁ W₂, ∀ i, ((P⁻¹ : GL (Fin n) ℂ).val * X * P.val) i i = 0) →
  ∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∀ g : GL (Fin n) ℂ,
    μd {t : twCent (thC n) d | (t : GL (Fin n) ℂ) * g ∈ nSet W₁ W₂ C} ≠ ⊤ := by
  intro n _ _ d μd _ W₁ W₂ P hW hdiag hzero C hC g
  let D₁ : GL (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
    fun c => dg (P⁻¹ * (c * g⁻¹) * P).val
  let D₂ : GL (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
    fun c => dg (P⁻¹ * (g * c⁻¹) * P).val
  have hD₁ : Continuous D₁ := continuous_dg.comp
    (Units.continuous_val.comp ((continuous_const.mul (continuous_id.mul continuous_const)).mul
      continuous_const))
  have hD₂ : Continuous D₂ := continuous_dg.comp
    (Units.continuous_val.comp ((continuous_const.mul (continuous_const.mul continuous_inv)).mul
      continuous_const))
  have hK := isCompact_units (hC.image hD₁) (hC.image hD₂)
  have hK' := hK.image (f := fun u : GL (Fin n) ℂ => P * u * P⁻¹)
    ((continuous_const.mul continuous_id).mul continuous_const)
  have hKT := (isClosed_twCent d).isClosedEmbedding_subtypeVal.isCompact_preimage hK'
  refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) hKT.measure_lt_top)
  rintro ⟨t, ht⟩ ⟨X, c, hc, hX⟩
  change uOf X * c = t * g at hX
  obtain ⟨a, ha⟩ := hdiag t ht
  obtain ⟨b, hb⟩ := hdiag t⁻¹ ((twCent (thC n) d).inv_mem ht)
  have hcX : c = (uOf X)⁻¹ * (t * g) := eq_inv_mul_of_mul_eq hX
  have e₁ : P⁻¹ * (c * g⁻¹) * P = (P⁻¹ * uOf (ninv hW X) * P) * (P⁻¹ * t * P) := by
    rw [uOf_ninv, hcX]; group
  have e₂ : P⁻¹ * (g * c⁻¹) * P = (P⁻¹ * t⁻¹ * P) * (P⁻¹ * uOf X * P) := by
    rw [hcX]; group
  have e₃ : (P⁻¹ * t * P)⁻¹ = P⁻¹ * t⁻¹ * P := by group
  refine ⟨P⁻¹ * t * P, ⟨⟨c, hc, ?_⟩, ⟨c, hc, ?_⟩⟩, by group⟩
  · change dg (P⁻¹ * (c * g⁻¹) * P).val = _
    rw [e₁, Units.val_mul, conj_uOf_val, ha]
    exact dg_one_add_mul _ _ (hzero _ (ninv hW X).2)
  · change dg (P⁻¹ * (g * c⁻¹) * P).val = _
    rw [e₂, e₃, Units.val_mul, conj_uOf_val, hb]
    exact dg_mul_one_add _ _ (hzero _ X.2)

end GlobalTheory.CompanionTheory.LocVan.Slice
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLogSizeM
section
noncomputable section

open NumberField IsDedekindDomain Matrix Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.E1
open GlobalTheory.CompanionTheory.Size

namespace GlobalTheory.CompanionTheory.SizeCont

theorem continuous_iSup_fin {X ι : Type} [TopologicalSpace X] [Fintype ι] (f : ι → X → ℝ)
    (hf : ∀ i, Continuous (f i)) : Continuous fun x => ⨆ i, f i x := by
  rcases isEmpty_or_nonempty ι with h | h
  · simpa [Real.iSup_of_isEmpty] using continuous_const
  · have : (fun x => ⨆ i, f i x) = fun x => Finset.univ.sup' Finset.univ_nonempty fun i => f i x := by
      funext x
      rw [Finset.sup'_univ_eq_ciSup]
    rw [this]
    exact Continuous.finset_sup'_apply _ fun i _ => hf i

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

theorem continuous_cW (w : HeightOneSpectrum (𝓞 E)) : Continuous (cW w : Ad E → w.adicCompletion E) :=
  (RestrictedProduct.continuous_eval w).comp continuous_snd

theorem continuous_elem (p : Fin n × Fin n) :
    Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) => A p.1 p.2 :=
  continuous_id.matrix_elem p.1 p.2

theorem continuous_inf (v : InfinitePlace E) : Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) =>
    Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (A p.1 p.2)‖ ^ 2) :=
  Real.continuous_posLog.comp (continuous_iSup_fin _ fun p =>
    (((continuous_cV v).comp (continuous_elem p)).norm).pow 2)

theorem continuous_fin (w : HeightOneSpectrum (𝓞 E)) : Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) =>
    Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖) :=
  Real.continuous_posLog.comp (continuous_iSup_fin _ fun p =>
    ((continuous_cW w).comp (continuous_elem p)).norm)

theorem eventually_finsum (hS : SzFin) (A₀ : Matrix (Fin n) (Fin n) (Ad E)) :
    ∀ᶠ A in 𝓝 A₀, ∑ᶠ w, Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖) =
      ∑ w ∈ (hS E (Fin n) (Fin n) A₀).toFinset,
        Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖) := by
  have hev : ∀ p : Fin n × Fin n, ∀ᶠ A : Matrix (Fin n) (Fin n) (Ad E) in 𝓝 A₀,
      ∀ w, ‖cW w (A p.1 p.2)‖ ≤ max ‖cW w (A₀ p.1 p.2)‖ 1 := fun p =>
    (continuous_elem p).continuousAt.eventually (eventually_fin (A₀ p.1 p.2))
  filter_upwards [Filter.eventually_all.2 hev] with A hA
  refine finsum_eq_sum_of_support_subset _ fun w hw => ?_
  rw [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  by_contra hn
  have h0 : sz (A₀.map (cW w)) ≤ 1 := not_lt.1 hn
  refine hw ((Real.posLog_eq_zero_iff _).2 ?_)
  have h1 : 0 ≤ ⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  rw [abs_of_nonneg h1]
  refine Real.iSup_le (fun p => (hA p w).trans (max_le ?_ le_rfl)) zero_le_one
  exact (le_sup (fun q : Fin n × Fin n => ‖cW w (A₀ q.1 q.2)‖) p).trans h0

theorem continuous_logSizeM (hS : SzFin) :
    Continuous (logSizeM : Matrix (Fin n) (Fin n) (Ad E) → ℝ) := by
  refine continuous_iff_continuousAt.2 fun A₀ => ?_
  have hc : Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) =>
      ∑ v, Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (A p.1 p.2)‖ ^ 2) +
        ∑ w ∈ (hS E (Fin n) (Fin n) A₀).toFinset,
          Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖) :=
    (continuous_finset_sum _ fun v _ => continuous_inf v).add
      (continuous_finset_sum _ fun w _ => continuous_fin w)
  refine hc.continuousAt.congr ?_
  filter_upwards [eventually_finsum hS A₀] with A hA
  rw [logSizeM, hA]

theorem sizeCont : SzFin → SizeCont := by
  intro hS E _ _ _ n
  have h := continuous_logSizeM (E := E) (n := n) hS
  exact (h.comp Units.continuous_val).add (h.comp Units.continuous_coe_inv)

end GlobalTheory.CompanionTheory.SizeCont

end
end

