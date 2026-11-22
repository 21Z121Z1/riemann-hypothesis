import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOfSamePlace
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0192
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0180
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0169
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceEqConjugatePlaceAndEmbedding
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TypeTame

theorem conjSP_w_of_isConjPl : ∀ (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host), IsConjPl D.host w s.w → (GlobalTheory.TypeTame.conjSP s).w = w ∧ ∀ x : D.host.E, (GlobalTheory.TypeTame.conjSP s).i x = s.i (D.host.conj x) := by
  intro D s w hw
  have hc : ∀ z : D.host.E, IsCMField.complexConj D.host.E z = D.host.conj z := by
    intro z
    apply D.host.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  refine ⟨?_, fun x => by rw [conjSP_i, hc]⟩
  let c : 𝓞 D.host.E →+* 𝓞 D.host.E :=
    RingOfIntegers.mapRingHom (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E)
  have hce : ∀ e : 𝓞 D.host.E, ((c e : 𝓞 D.host.E) : D.host.E) = IsCMField.complexConj D.host.E (e : D.host.E) :=
    fun e => rfl
  ext x
  have h1 : x ∈ (conjSP s).w.asIdeal ↔ c x ∈ s.w.asIdeal := by
    show Valued.v ((conjSP s).i (x : D.host.E)) < 1 ↔ Valued.v (s.i ((c x : 𝓞 D.host.E) : D.host.E)) < 1
    rw [conjSP_i, hce]
  rw [h1, hw x (c x) (by rw [hce, hc])]

end GlobalTheory.TypeTame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceUnitaryLocEqTransposeInv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open TensorProduct

namespace GlobalTheory.ConjLoc

theorem proj_conjSP {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (a : AL L) :
    (GlobalTheory.TypeTame.conjSP s).proj a = s.proj (conjAL L a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x b =>
    simp [SplitPlace.proj, conjAL, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem loc_conjSP : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (x : GAf L n), ((GlobalTheory.TypeTame.conjSP s).loc n x).val = ((s.loc n x)⁻¹ : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))).val.transpose := by
  intro L _ _ _ n s x
  have hx : (x.1 : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := x.2
  have h1 : (s.loc n x).val * ((GlobalTheory.TypeTame.conjSP s).loc n x).val.transpose = 1 := by
    have e : ((GlobalTheory.TypeTame.conjSP s).loc n x).val.transpose
        = (conjT (conjAL L) (x.1 : Matrix (Fin n) (Fin n) (AL L))).map s.proj := by
      refine Matrix.ext fun i j => ?_
      exact proj_conjSP s _
    have e' : (s.loc n x).val = (x.1 : Matrix (Fin n) (Fin n) (AL L)).map s.proj := rfl
    rw [e, e', ← Matrix.map_mul, hx, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 := Units.inv_eq_of_mul_eq_one_right h1
  rw [h2, Matrix.transpose_transpose]

end GlobalTheory.ConjLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalJacquetSubquotientAtMostOneNonemptyBlockStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_jacquet_subquotient_at_most_one_nonempty_block : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (s' : ℕ) (b : Fin s' → ℕ) (f : (Σ j, Fin (b j)) ≃ Fin d) (X : Fin s' → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (ρ : ∀ j, Representation ℂ (GL (Fin (b j)) k) (X j)), GlobalTheory.SmGL.IsCuspidal σ → (∀ j, Nontrivial (X j)) → GlobalTheory.SmGL.IsSubquotient (GlobalTheory.SmGL.piTensor ρ) (GlobalTheory.SmGL.jac f σ) → ∀ j j', 0 < b j → 0 < b j' → j = j' := by
  first | exact @GlobalTheory.SmGL.CuspRow.block_unique_of_isCuspidal | exact GlobalTheory.SmGL.CuspRow.block_unique_of_isCuspidal | (intros; apply GlobalTheory.SmGL.CuspRow.block_unique_of_isCuspidal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamAndJumpsRankOneLAdicCharacter
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.TripleGal GlobalTheory.Pst
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CharAboveRead

open scoped TensorProduct

theorem exists_isInduced_of {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (τ : E →+* Om l) (w : HeightOneSpectrum (𝓞 E)) (hw : w ∈ placesOver E l)
    (hτ : ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal) (A : ValuationSubring Ω) (hA : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O)
    (hj : Induces Bw) : ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1, IsInduced Bw τ τ' := by
  let jE : E →+* Om l := Bw.j.comp (algebraMap E Ω)
  have hjE : ∀ x : 𝓞 E, ‖jE (x : E)‖ < 1 ↔ x ∈ w.asIdeal := fun x =>
    (hj.valuation_lt_one_iff _).symm.trans (hA x)
  have iso := GlobalTheory.GalFirstClause.Emb.norm_eq_of_samePlace τ jE w hw hτ hjE
  have hker : ∀ t ∈ RingHom.ker (GlobalTheory.GalFirstClause.Emb.tensLift jE), GlobalTheory.GalFirstClause.Emb.tensLift τ t = 0 := fun t ht =>
    norm_eq_zero.1 (le_antisymm ((GlobalTheory.GalFirstClause.Emb.norm_tensLift_le jE τ (fun x => (iso x).symm) t).trans
      (by rw [RingHom.mem_ker.1 ht, norm_zero])) (norm_nonneg _))
  have hrange : (GlobalTheory.GalFirstClause.Emb.tensLift jE).range ≤ Bw.Kw.1.toSubalgebra := by
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      change GlobalTheory.GalFirstClause.Emb.tensLift jE (a ⊗ₜ y) ∈ _
      rw [GlobalTheory.GalFirstClause.Emb.tensLift_tmul]
      exact mul_mem (Bw.Kw.1.algebraMap_mem a) (Bw.j_E y)
    | add t₁ t₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  have hfin : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule (GlobalTheory.GalFirstClause.Emb.tensLift jE).range) := by
    haveI : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule Bw.Kw.1.toSubalgebra) := Bw.Kw.2
    exact Submodule.finiteDimensional_of_le (Subalgebra.toSubmodule.monotone hrange)
  have hclosed : IsClosed ((GlobalTheory.GalFirstClause.Emb.tensLift jE).range : Set (Om l)) :=
    Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule (GlobalTheory.GalFirstClause.Emb.tensLift jE).range)
  have hle : Bw.Kw.1.toSubalgebra ≤ (GlobalTheory.GalFirstClause.Emb.tensLift jE).range := by
    intro y hy
    refine closure_minimal ?_ hclosed (Bw.j_dense hy)
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by
      change GlobalTheory.GalFirstClause.Emb.tensLift jE (1 ⊗ₜ x) = jE x; rw [GlobalTheory.GalFirstClause.Emb.tensLift_tmul, map_one, one_mul]⟩
  let σ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l :=
    ((Ideal.Quotient.liftₐ (RingHom.ker (GlobalTheory.GalFirstClause.Emb.tensLift jE)) (GlobalTheory.GalFirstClause.Emb.tensLift τ) hker).comp
      (Ideal.quotientKerEquivRange (GlobalTheory.GalFirstClause.Emb.tensLift jE)).symm.toAlgHom).comp (Subalgebra.inclusion hle)
  refine ⟨σ.codRestrict Bw.LL.1.toSubalgebra (fun y => Bw.LL_split σ y), fun x => ?_⟩
  have key : (Ideal.quotientKerEquivRange (GlobalTheory.GalFirstClause.Emb.tensLift jE)).symm
      (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩) = Ideal.Quotient.mk _ (1 ⊗ₜ x) := by
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    change jE x = GlobalTheory.GalFirstClause.Emb.tensLift jE (1 ⊗ₜ x)
    rw [GlobalTheory.GalFirstClause.Emb.tensLift_tmul, map_one, one_mul]
  change τ x = σ ⟨jE x, Bw.j_E x⟩
  change τ x = Ideal.Quotient.liftₐ _ (GlobalTheory.GalFirstClause.Emb.tensLift τ) hker
    ((Ideal.quotientKerEquivRange (GlobalTheory.GalFirstClause.Emb.tensLift jE)).symm (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩))
  rw [key, Ideal.Quotient.liftₐ_apply]
  change τ x = GlobalTheory.GalFirstClause.Emb.tensLift τ (1 ⊗ₜ x)
  rw [GlobalTheory.GalFirstClause.Emb.tensLift_tmul, map_one, one_mul]

theorem continuous_rankOneOperator {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    (μ : Γ →* Kˣ) (hμ : Continuous μ) : Continuous fun g => ((rk1 μ g : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) := by
  have hv : Continuous fun g => ((μ g : Kˣ) : K) := Units.continuous_val.comp hμ
  refine continuous_pi fun i => continuous_pi fun k => ?_
  have e : ∀ g, ((rk1 μ g : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) i k = ((μ g : Kˣ) : K) := fun g => by
    fin_cases i; fin_cases k; simp [rk1]
  simp only [e]
  exact hv

end GlobalTheory.CharAboveRead

namespace GlobalTheory.CharAboveRead

set_option maxHeartbeats 1000000 in

theorem deRham_and_jumps_rankOne_lAdic_character : ∀ (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (μ : G D.host.E D.nd.Om →* (Qbar l)ˣ), Continuous μ → ∀ (J : (D.host.E →+* Qbar l) → Multiset ℤ)
    (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ placesOver D.host.E l →
    (∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), Induces Bw →
      IsdRAt (D.loc l) Bw ((rk1 μ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) ∧
      ∀ (τ : D.host.E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt (D.loc l) Bw ((rk1 μ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ (J τ)) →
    W.IsdRW l ι (rk1 μ) w ∧ ∀ τ : D.host.E →+* Qbar l, (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) →
      W.jumpsW l ι (rk1 μ) τ = J τ := by
  intro D T W l _ ι μ hμ J w hw H
  have hcont : Continuous fun g => (rk1 μ g : Matrix (Fin 1) (Fin 1) (Qbar l)) := continuous_rankOneOperator μ hμ
  obtain ⟨K, ρ, hρc, hρ⟩ := GlobalTheory.GalFirstClause.finextRep l D.host.E D.nd.Om 1 (rk1 μ) hcont
  obtain ⟨j, L0, hj, hLL⟩ := GlobalTheory.PlaceBridge.exists_locBridge l D.host.E D.nd.Om w (D.nd.plOm.1 w) hw (D.nd.plOm.2 w)
  obtain ⟨Bw, hBj, hBLL, -, hBto⟩ := hLL L0 le_rfl
  have hind : Induces Bw := fun x => by rw [hBj]; exact hj x
  let LL' : FinExt l := supExt K Bw.LL
  have hK : K.1 ≤ LL'.1 := le_sup_left
  have hB : Bw.LL.1 ≤ LL'.1 := le_sup_right
  let ρ' : G D.host.E D.nd.Om →* GL (Fin 1) ↥LL'.1 := mapRep (IntermediateField.inclusion hK).toRingHom ρ
  have hρ' : mapRep (algebraMap ↥LL'.1 (Om l)) ρ' = rk1 μ := by
    rw [← hρ]
    ext g i k
    rfl
  have hρ'c : Continuous fun g => (ρ' g : Matrix (Fin 1) (Fin 1) ↥LL'.1) := by
    have hi : Continuous (IntermediateField.inclusion hK) :=
      continuous_induced_rng.2 continuous_subtype_val
    exact hρc.matrix_map hi
  have hmodel : IsModel Bw (resDec D.nd.plOm.1 (rk1 μ) w) LL'
      (ρ'.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
    ⟨hB, by rw [← hρ']; rfl⟩
  let φ : ↥(OL L0) →+* Qbar l := L0.1.val.toRingHom.comp (OL L0).val.toRingHom
  have hφ : ∀ x, φ x = ((Bw.toLL x : ↥Bw.LL.1) : Om l) := fun x => (hBto x).symm
  have hcl := (W.loc l ι w hw _ Bw hind φ hφ).2 LL' hB 1 ρ' hρ'c
  rw [hρ'] at hcl
  have hab := H _ Bw hind
  have hdR : Bw.IsdRE (D.loc l) LL' (ρ'.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
    (hmodel.isdRAt_iff (D.loc l)).1 hab.1
  refine ⟨hcl.2.1.2 hdR, fun τ hτ => ?_⟩
  obtain ⟨τ₀, hτ₀⟩ := exists_isInduced_of τ w hw hτ _ (D.nd.plOm.2 w) _ Bw hind
  let τ'' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1 := (IntermediateField.inclusion hB).comp τ₀
  have hτ'' : IsInduced Bw τ τ'' := fun x => hτ₀ x
  have hJ := hab.2 τ LL' τ'' hτ''
  ext n
  apply Nat.cast_injective (R := ℤ)
  rw [(hcl.2.2.2 τ τ'' hτ'').2 hdR n, IsJumpsAt.count_eq (D.loc l) hmodel hτ'' hJ n]

end GlobalTheory.CharAboveRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamGaloisSideIffDeRhamAtLocalEmbeddingStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_galoisSide_iff_deRham_at_localEmbedding : ∀ (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ placesOver D.host.E l → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw → ∀ (a : ℕ) (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)), Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → (W.IsdRW l ι r w ↔ GlobalTheory.Pst.IsdRAt (D.loc l) Bw (GlobalTheory.Pst.resDec D.nd.plOm.1 r w)) := by
  first | exact @GlobalTheory.DeRhamRead.isdRW_iff_isdRAt | exact GlobalTheory.DeRhamRead.isdRW_iff_isdRAt | (intros; apply GlobalTheory.DeRhamRead.isdRW_iff_isdRAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagUniformiserConjTransposeInvMemUpperParahoric
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockConj

open Matrix
open Formalism.UG (bc GLint)

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

theorem exp_neg_one_lt_one : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num

section Pure

variable {K : Type} [Field K] {n : ℕ}

theorem inv_val_of_diagonal {d : GL (Fin n) K} {D : Fin n → K} (hd : d.val = Matrix.diagonal D) (hD : ∀ i, D i ≠ 0) :
    (d⁻¹ : GL (Fin n) K).val = Matrix.diagonal fun i => (D i)⁻¹ := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [hd, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one with i
  exact mul_inv_cancel₀ (hD i)

theorem conj_diag_apply {d : GL (Fin n) K} {D : Fin n → K} (hd : d.val = Matrix.diagonal D) (hD : ∀ i, D i ≠ 0)
    (g : GL (Fin n) K) (p q : Fin n) : (d * g * d⁻¹).val p q = D p * g.val p q * (D q)⁻¹ := by
  rw [Units.val_mul, Units.val_mul, inv_val_of_diagonal hd hD, hd, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem mem_GLint_of {O : Subring K} {x : GL (Fin n) K} (h1 : ∀ i j, x.1 i j ∈ O) (h2 : ∀ i j, (x⁻¹).1 i j ∈ O) :
    x ∈ GLint (Fin n) O := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

variable (v : Valuation K (WithZero (Multiplicative ℤ))) {r : ℕ} {ϖ : K}

theorem conj_le_one (hϖ : v ϖ = WithZero.exp (-1)) {M : Matrix (Fin n) (Fin n) K} (h1 : ∀ i j, v (M i j) ≤ 1)
    (h2 : ∀ q p : Fin n, p.val < r → q ≠ p → v (M q p) < 1) (p q : Fin n) :
    v ((if (p : ℕ) < r then 1 else ϖ) * M q p * (if (q : ℕ) < r then 1 else ϖ)⁻¹) ≤ 1 := by
  have hne : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
  rw [map_mul, map_mul, map_inv₀]
  by_cases hp : (p : ℕ) < r <;> by_cases hq : (q : ℕ) < r <;>
    simp only [hp, hq, if_true, if_false, map_one, inv_one, one_mul, mul_one, hϖ]
  · exact h1 q p
  · have hqp : q ≠ p := fun e => hq (e ▸ hp)
    calc v (M q p) * (WithZero.exp (-1))⁻¹ ≤ WithZero.exp (-1) * (WithZero.exp (-1))⁻¹ :=
          mul_le_mul' (le_exp_neg_one_of_lt_one (h2 q p hp hqp)) le_rfl
      _ = 1 := mul_inv_cancel₀ hne
  · calc WithZero.exp (-1) * v (M q p) ≤ 1 * 1 := mul_le_mul' exp_neg_one_lt_one.le (h1 q p)
      _ = 1 := one_mul 1
  · rw [mul_comm (WithZero.exp (-1)), mul_assoc, mul_inv_cancel₀ hne, mul_one]; exact h1 q p

theorem conj_lower_lt_one (hϖ : v ϖ = WithZero.exp (-1)) {M : Matrix (Fin n) (Fin n) K} (h1 : ∀ i j, v (M i j) ≤ 1)
    (p q : Fin n) (hp : r ≤ p.val) (hq : q.val < r) :
    v ((if (p : ℕ) < r then 1 else ϖ) * M q p * (if (q : ℕ) < r then 1 else ϖ)⁻¹) < 1 := by
  rw [if_neg (not_lt.2 hp), if_pos hq, inv_one, mul_one, map_mul, hϖ]
  calc WithZero.exp (-1) * v (M q p) ≤ WithZero.exp (-1) * 1 := mul_le_mul' le_rfl (h1 q p)
    _ < 1 := by rw [mul_one]; exact exp_neg_one_lt_one

end Pure

section Place

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem valued_lt_one_iff_w (s : SplitPlace L) (x : s.w.adicCompletion L) :
    ValuativeRel.valuation (s.w.adicCompletion L) x < 1 ↔ Valued.v x < 1 := by
  have : (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (s.w.adicCompletion L))
    (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one

theorem valued_le_one_iff_w (s : SplitPlace L) (x : s.w.adicCompletion L) :
    ValuativeRel.valuation (s.w.adicCompletion L) x ≤ 1 ↔ Valued.v x ≤ 1 := by
  have : (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (s.w.adicCompletion L))
    (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

theorem facts_of_mem (s : SplitPlace L) (r t : ℕ)
    (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hc : ∀ x, Valued.v (c x) = Valued.v x)
    (a : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)))
    (ha : Matrix.GeneralLinearGroup.map c.toRingHom a ∈ blockGrp (s.w.adicCompletion L) r t) :
    (∀ i j, Valued.v (a.val i j) ≤ 1) ∧
      ∀ q p : Fin (r + t), p.val < r → Valued.v (a.val q p - if q = p then 1 else 0) < 1 := by
  obtain ⟨hK, hcol⟩ := ha
  refine ⟨fun i j => ?_, fun q p hp => ?_⟩
  · have := val_le_one_of_mem_KO hK i j
    rw [valued_le_one_iff_w] at this
    simpa [hc] using this
  · have := hcol q ⟨p, hp⟩
    have e : Fin.castAdd t (⟨p, hp⟩ : Fin r) = p := Fin.ext rfl
    rw [e, valued_lt_one_iff_w] at this
    have e2 : ((Matrix.GeneralLinearGroup.map c.toRingHom a).val - 1) q p =
        c (a.val q p - if q = p then 1 else 0) := by
      by_cases h : q = p <;> simp [Matrix.one_apply, h]
    rw [e2, hc] at this
    exact this

end Place

end GlobalTheory.BlockConj

namespace GlobalTheory.BlockConj

open Formalism.UG (GLint)

theorem conj_transpose_inv_uniRT : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), (∀ x, Valued.v (c x) = Valued.v x) → ∀ (a b : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))), b.val = (a⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val.transpose → Matrix.GeneralLinearGroup.map c.toRingHom a ∈ blockGrp (s.w.adicCompletion L) r t → ∀ ϖ : s.v.adicCompletion (maximalRealSubfield L), Valued.v ϖ = WithZero.exp (-1) → ∀ d : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), d.val = Matrix.diagonal (fun i : Fin (r + t) => if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ) → NG.UniRT s r (d * b * d⁻¹) ∧ Valued.v (NG.supDiag s r (d * b * d⁻¹)) < 1 := by
  intro L _ _ _ s r t c hc a b hb ha ϖ hϖ d hd
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hD : ∀ i : Fin (r + t), (if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ) ≠ 0 := by
    intro i; split_ifs
    · exact one_ne_zero
    · exact hϖ0
  obtain ⟨ha1, ha2⟩ := facts_of_mem s r t c hc a ha
  obtain ⟨hi1, hi2⟩ := facts_of_mem s r t c hc a⁻¹ (by rw [map_inv]; exact (blockGrp _ r t).inv_mem ha)
  have ha2' : ∀ q p : Fin (r + t), p.val < r → q ≠ p → Valued.v (a.val q p) < 1 := fun q p hp hqp => by
    simpa [hqp] using ha2 q p hp
  have hi2' : ∀ q p : Fin (r + t), p.val < r → q ≠ p → Valued.v ((a⁻¹).val q p) < 1 := fun q p hp hqp => by
    simpa [hqp] using hi2 q p hp
  have hbinv : (b⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val = a.val.transpose := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hb, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have hN : ∀ p q, (d * b * d⁻¹).val p q = (if (p : ℕ) < r then 1 else ϖ) * (a⁻¹).val q p *
      (if (q : ℕ) < r then 1 else ϖ)⁻¹ := by
    intro p q; rw [conj_diag_apply hd hD, hb, Matrix.transpose_apply]
  have hNi : ∀ p q, ((d * b * d⁻¹)⁻¹).val p q = (if (p : ℕ) < r then 1 else ϖ) * a.val q p *
      (if (q : ℕ) < r then 1 else ϖ)⁻¹ := by
    have e : (d * b * d⁻¹)⁻¹ = d * b⁻¹ * d⁻¹ := by group
    intro p q; rw [e, conj_diag_apply hd hD, hbinv, Matrix.transpose_apply]

  have hUL : ∀ p q : Fin (r + t), p.val < r → q.val < r → (d * b * d⁻¹).val p q = (a⁻¹).val q p := by
    intro p q hp hq; rw [hN, if_pos hp, if_pos hq, inv_one, one_mul, mul_one]
  refine ⟨⟨⟨mem_GLint_of (fun i j => ?_) (fun i j => ?_), fun p q hp hq => ?_⟩, fun p q hp hq => ⟨fun hlt => ?_, fun he => ?_⟩⟩, ?_⟩
  · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
    rw [hN]
    exact conj_le_one Valued.v hϖ hi1 hi2' i j
  · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
    rw [hNi]
    exact conj_le_one Valued.v hϖ ha1 ha2' i j
  · rw [hN]; exact conj_lower_lt_one Valued.v hϖ hi1 p q hp hq
  · rw [hUL p q hp hq]; exact hi2' q p hp (Fin.ne_of_lt hlt)
  · subst he; rw [hUL p p hp hp]; simpa using hi2 p p hp
  · unfold NG.supDiag
    refine Valuation.map_sum_lt _ one_ne_zero fun p _ => Valuation.map_sum_lt _ one_ne_zero fun q _ => ?_
    split_ifs with h
    · rw [hUL p q (by omega) h.2]
      exact hi2' q p (by omega) (fun e => by rw [e] at h; omega)
    · rw [map_zero]; exact zero_lt_one

end GlobalTheory.BlockConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DoubleCosetOperatorTranslateDeeperLevelEqSmulStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCosetOperator_translate_deeper_level_eq_smul : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J J' : Subgroup (GAf L n)) (h : GAf L n), J' ≤ J → (∀ κ ∈ J', h⁻¹ * κ * h ∈ J) → {c : GAf L n ⧸ J' | ∃ x ∈ (J : Set (GAf L n)), (x : GAf L n ⧸ J') = c}.Finite → ∃ m : ℕ, 0 < m ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ J, NG.rt L n κ f = f) → NG.heckeD J' (J : Set (GAf L n)) (NG.rt L n h f) = (m : ℂ) • NG.heckeD J {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * h * u'} f := by
  first | exact @GlobalTheory.HeckeAverage.heckeD_rt_eq_smul | exact GlobalTheory.HeckeAverage.heckeD_rt_eq_smul | (intros; apply GlobalTheory.HeckeAverage.heckeD_rt_eq_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_or_isConjPlace_of_over_splitPlace : ∀ (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host), NG.OverPl w s.v → s.w = w ∨ IsConjPl D.host w s.w := by
  first | exact @GlobalTheory.SplitPlaceOver.eq_or_isConjPl | exact GlobalTheory.SplitPlaceOver.eq_or_isConjPl | (intros; apply GlobalTheory.SplitPlaceOver.eq_or_isConjPl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivariantIsoOfTranslationStableGraphStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_iso_of_translationStable_graph : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (ρa : Representation ℂ (GQ L n) A) (ρb : Representation ℂ (GQ L n) B) (S₁ : Submodule ℂ (GAf L n → A)) (S₂ : Submodule ℂ (GAf L n → B)) (W : Submodule ℂ ((GAf L n → A) × (GAf L n → B))), NG.IsIrrRep ρa S₁ → NG.IsIrrRep ρb S₂ → (∀ w ∈ W, w.1 ∈ S₁ ∧ w.2 ∈ S₂) → (∀ h, ∀ w ∈ W, (NG.rt L n h w.1, NG.rt L n h w.2) ∈ W) → (∀ u, ((0 : GAf L n → A), u) ∈ W → u = 0) → (∀ u, (u, (0 : GAf L n → B)) ∈ W → u = 0) → W ≠ ⊥ → NG.IsoRep S₁ S₂ := by
  first | exact @GlobalTheory.isoRep_of_stable_graph | exact GlobalTheory.isoRep_of_stable_graph | (intros; apply GlobalTheory.isoRep_of_stable_graph <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdjoinSplitHeckeGeneratorsDualsSphericalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adjoin_splitHeckeGenerators_duals_spherical : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), conjPl P ≠ P → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (d : List ℤ), ∃ a ∈ Algebra.adjoin ℂ {x : Module.End ℂ M | ∃ k, k ≤ V.rank ∧ (x = opOf π P (Finsupp.single (splitLab V.rank k) 1) ∨ x = opOf π P (Finsupp.single (dualLab (splitLab V.rank k)) 1))}, ∀ u : M, (∀ k ∈ hyp V P, π k u = u) → a u = opOf π P (Finsupp.single d 1) u := by
  first | exact @GlobalTheory.SplitGen.gen_split | exact GlobalTheory.SplitGen.gen_split | (intros; apply GlobalTheory.SplitGen.gen_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBaseLevelVectorInGoodAlgebraicFormsSpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3

theorem exists_part_level_vector : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → ∀ j c, R.Wc' j c ≠ ⊥ → ∃ w ∈ R.Wc' j c, w ≠ 0 ∧ w ∈ R.toRealDat.WS F.lv2 false j (sg0 D A3.A) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hW hEx hSch s hOk hGG hU j c hne
  obtain ⟨hCoreF, hSF, -, -, -, hWc, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hW
  have hCore := hCoreF hEx
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨h, -, -, -, hsup, hstab, -, -⟩ := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hCore hSch hX R.SF hSF j
  obtain ⟨hid, -, -, -⟩ := eH_laws R.toRealDat F.lv2 hCore hX j
  have hfix : ∀ u ∈ Wcc R.toRealDat R.SF j c, eH R.toRealDat j u = u := by
    intro u hu
    have hr : u ∈ LinearMap.range (eH R.toRealDat j) := hsup ▸ (le_iSup (fun c => Wcc R.toRealDat R.SF j c) c) hu
    obtain ⟨x, rfl⟩ := hr
    rw [← Module.End.mul_apply, hid]
  rw [hWc] at hne ⊢
  obtain ⟨u, huU, hu0, hup⟩ := GlobalTheory.T.exists_level_vector_goodType_stable_subspace (sg0 D A3.A) A3.A.X F.P0 F.ψ0⁻¹ (R.gW j (sg0 D A3.A))
    (Wcc R.toRealDat R.SF j c) hX hGG (fun g => hstab c g) hne (fun u hu => by
      have := hfix u hu
      simpa [eH, RealDat.eC] using this)
  refine ⟨u, huU, hu0, ?_⟩
  have hlev := (GlobalTheory.T.goodForms_baseLevel_iff_goodProjection R.toRealDat F.lv2 hCore hX j u).2 ⟨hfix u huU, hup⟩
  have hL := GlobalTheory.LevelForms.levelW_of_irr R.toRealDat F.lv2 hX hU hCore.models.HW
  rw [hL false j (sg0 D A3.A)]
  exact hlev

end GlobalTheory.Hk3
end
end

