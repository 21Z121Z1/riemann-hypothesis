import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemBasicOpenOfMemBasicOpenNormCoeff
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeEmbeddingMemUnitGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0172
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0190
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0645
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import ReciprocityTheory.GaloisValuations.Global
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0154
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0168
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0194
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0100
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemBasicOpenOfMemBasicOpenNormCoeffStatement
section
open AlgebraicGeometry CategoryTheory Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_basicOpen_of_mem_basicOpen_normCoeff' : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] {V : X.Opens} (hV : IsAffineOpen V)
    [IsDomain Γ(X, V)] [IsIntegrallyClosed Γ(X, V)] (τ : Γ(Y, f ⁻¹ᵁ V)) (x : X) (k : ℕ), x ∈ V → 1 ≤ k →
    x ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k) → ∃ y ∈ Y.basicOpen τ, f y = x := by
  first | exact @GlobalTheory.NormalDescent.exists_mem_basicOpen_of_mem_basicOpen_normCoeff | exact GlobalTheory.NormalDescent.exists_mem_basicOpen_of_mem_basicOpen_normCoeff | (intros; apply GlobalTheory.NormalDescent.exists_mem_basicOpen_of_mem_basicOpen_normCoeff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNontrivialAdeleCharTrivialOnTotallyReal
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.CharZero

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
private theorem extensionEmbedding_infiniteAdele_algebraMap (F : Type) [Field F] [NumberField F]
    (x : F) (v : InfinitePlace F) :
    InfinitePlace.Completion.extensionEmbedding v ((algebraMap F (InfiniteAdeleRing F) x) v) =
      v.embedding x := by
  simp [InfinitePlace.Completion.extensionEmbedding_coe]

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
private theorem sum_infinitePlace_embedding_eq_trace (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (x : F) :
    ∑ v : InfinitePlace F, v.embedding x = ((Algebra.trace ℚ F x : ℚ) : ℂ) := by
  let e : InfinitePlace F ≃ (F →+* ℂ) :=
    { toFun := fun v => v.embedding
      invFun := InfinitePlace.mk
      left_inv := fun v => InfinitePlace.mk_embedding v
      right_inv := fun φ => InfinitePlace.embedding_mk_eq_of_isReal
        (IsTotallyReal.complexEmbedding_isReal φ) }
  rw [Fintype.sum_equiv e (fun v => v.embedding x) (fun φ => φ x) (fun _ => rfl)]
  have h := trace_eq_sum_embeddings (K := ℚ) (L := F) (E := ℂ) (x := x)
  rw [← eq_ratCast (algebraMap ℚ ℂ), h]
  convert Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ : F →+* ℂ => φ x)
    (fun φ : F →ₐ[ℚ] ℂ => φ x) (fun _ => rfl)

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in

theorem _root_.GlobalTheory.GaugeEx.CharZero.exists_isCharAF :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ ψ, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF F ψ := by
  intro F _ _ _
  let L : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F →+ ℂ := ∑ v : InfinitePlace F,
    (InfinitePlace.Completion.extensionEmbedding v).toAddMonoidHom.comp
      (Pi.evalAddMonoidHom (fun w : InfinitePlace F => w.Completion) v)
  have hLapply : (L : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F → ℂ) = fun a => ∑ v : InfinitePlace F,
      InfinitePlace.Completion.extensionEmbedding v (a v) := by
    ext a
    simp only [L, AddMonoidHom.finset_sum_apply]
    rfl
  have hL : Continuous L := by
    rw [hLapply]
    exact continuous_finset_sum _ fun v _ =>
      (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp
        (continuous_apply v)
  obtain ⟨ψ, hψ, -⟩ := _root_.GlobalTheory.StdAdelicChar.exists_char_of_trace F L hL (fun x => by
    rw [hLapply]
    change ∑ v : InfinitePlace F, InfinitePlace.Completion.extensionEmbedding v
      ((algebraMap F (InfiniteAdeleRing F) x) v) = _
    simp only [extensionEmbedding_infiniteAdele_algebraMap]
    exact sum_infinitePlace_embedding_eq_trace F x)
  exact ⟨ψ, hψ⟩

end GlobalTheory.GaugeEx.CharZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters
section
noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

namespace StagesInhab

def HasLetters (P : Pre) : Prop :=
  ∃ (Del : ℚ) (letter : P.Word → Fin (P.R.k - 2) → Bool), 0 < Del ∧ Function.Injective letter ∧
    (∀ w τ (l : ℕ) (h : l + 1 < P.R.k - 1), (P.hcW w τ).v ⟨l, by omega⟩ - (P.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del) ∧
    ∀ w τ (l : ℕ) (h : l < P.R.k - 2), (P.hcW w τ).u ⟨l + 1, by omega⟩ =
      (P.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0)

theorem ipC_conj (B : Base) (u : B.Word)
    (φ ψ : ((ColsModel.cols B).mem u).C.cls 0 → ((ColsModel.cols B).mem u).C.Y 0 → ℂ) :
    ((ColsModel.cols B).fm u).ipC 0 ψ φ = starRingEnd ℂ (((ColsModel.cols B).fm u).ipC 0 φ ψ) := by
  rw [RowsModel.ipC_cols, RowsModel.ipC_cols, map_sum]
  exact Finset.sum_congr rfl fun c _ => by simp [mul_comm]

theorem ipC_pos (B : Base) (u : B.Word)
    (φ : ((ColsModel.cols B).mem u).C.cls 0 → ((ColsModel.cols B).mem u).C.Y 0 → ℂ) (hφ : φ ≠ 0) :
    0 < (((ColsModel.cols B).fm u).ipC 0 φ φ).re := by
  rw [RowsModel.ipC_cols, Complex.re_sum]
  obtain ⟨c, hc⟩ : ∃ c, φ c () ≠ 0 := by
    by_contra h
    exact hφ (funext fun c => funext fun _ => not_not.mp fun hc => h ⟨c, hc⟩)
  refine Finset.sum_pos' (fun c _ => ?_) ⟨c, Finset.mem_univ _, ?_⟩
  · rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    positivity
  · rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    positivity

theorem exists_rows (B : Base) (D : ℕ) :
    ∃ W : RowsRest B (ColsModel.cols B), W.Drows = D ∧ W.Dall = D ∧ ∀ u, Nontrivial (W.Mu u) := by
  classical
  have hf : ∀ u, ∃ e : RowsModel.Euc ((ColsModel.cols B).mem u).A.du ≃ₗ[ℂ] ((ColsModel.cols B).mem u).A.Mram,
      ∀ φ ψ, inner ℂ φ ψ = ((ColsModel.cols B).fm u).ipC 0 (e φ).1 (e ψ).1 := fun u =>
    haveI := RowsModel.mram_fd (ColsModel.cols B) u
    RowsModel.exists_frame (RowsModel.ramCore (ColsModel.cols B) u (fun φ _ ψ _ => ipC_conj B u φ ψ)
      (fun φ _ h => ipC_pos B u φ h))
  choose eM heM using hf
  let e : ℂ ≃ₗ[ℂ] RowsModel.Euc 1 :=
    (LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm.trans (WithLp.linearEquiv 2 ℂ _).symm
  refine ⟨RowsModel.model (ColsModel.cols B) (fun _ => 1) D (fun _ => e) (fun _ _ => e) eM heM, rfl, rfl,
    fun u => ?_⟩
  have : Fact (B.T u).Prime := ⟨B.T_prime u⟩
  have hne : ((ColsModel.cols B).mem u).A.Mram ≠ ⊥ :=
    MemberTorsor.mram_ne_bot B.R (Tau B.R) (B.hcW u) (B.T u) (card_Tau B.host) (ColsModel.two_lt_alt B.toPre u)
  have := Submodule.nontrivial_iff_ne_bot.mpr hne
  exact (eM u).toEquiv.nontrivial

theorem exists_stages_over (B : Base) (hB : HasLetters B.toPre) (D : ℕ) :
    ∃ X : Stages, X.B = B ∧ X.W.Drows = D ∧ X.W.Dall = D ∧ (∀ u, Nontrivial (X.W.Mu u)) ∧
      (∀ u i, Nonempty ((X.C.mem u).C.cls i)) ∧ Nonempty X.G.jet.Sit := by
  obtain ⟨Del, letter, hD, hinj, gap, hu⟩ := hB
  obtain ⟨W, h1, h2, h3⟩ := exists_rows B D
  have hc : ∀ u i, Nonempty (((ColsModel.cols B).mem u).C.cls i) :=
    fun u _ => ⟨(1 : Tau B.R → (ZMod (B.T u))ˣ)⟩
  obtain ⟨L⟩ := locStage_inhabited
  obtain ⟨N, -⟩ := GaloisStage.exists_nStage_adapt B _ W L
  obtain ⟨V, -⟩ := DivInhab.exists_divStage B _ (GaloisStage.adapt W)
  obtain ⟨S⟩ := SStageInhab.nonempty_sStage B _ (GaloisStage.adapt W) Del hD gap letter hinj hu
    (fun u x _ y _ => (ipC_conj B u y x).symm) (fun u x _ h => ipC_pos B u x h)
    (show W.Drows ≤ W.Dall by omega)
  obtain ⟨G, -, hG⟩ := (GJInhab.inhabited_stage B (ColsModel.cols B)).2.2 (hc _ _) (hc _ _)
  exact ⟨⟨B, _, GaloisStage.adapt W, V, S, N, G⟩, rfl, h1, h2, h3, hc, hG⟩

theorem exists_pre_hasLetters : ∃ P : Pre, HasLetters P ∧ Nonempty (PreX P) ∧ 2 ≤ Fintype.card P.Word := by
  obtain ⟨P, h1, h2, -, -, h3⟩ := exists_pre_two_words
  exact ⟨P, h3, h1, h2⟩

theorem exists_stages_large (P : Pre) (hP : HasLetters P) (D : ℕ) (S₀ S₁ S₂ : Finset ℂ)
    (h₀ : ∀ z ∈ S₀, IsAlgebraic ℚ z) (h₁ : ∀ z ∈ S₁, IsAlgebraic ℚ z) (h₂ : ∀ z ∈ S₂, IsAlgebraic ℚ z) :
    ∃ X : Stages, X.B.toPre = P ∧ (∀ z ∈ S₀, ∃ x ∈ X.B.Ks, X.B.embLL x = z) ∧
      (∀ z ∈ S₁, ∃ x ∈ X.B.LL0, X.B.embLL x = z) ∧ (∀ z ∈ S₂, ∃ x : X.B.LL, X.B.embLL x = z) ∧
      X.W.Drows = D ∧ X.W.Dall = D ∧ (∀ u, Nontrivial (X.W.Mu u)) ∧
      (∀ u i, Nonempty ((X.C.mem u).C.cls i)) ∧ Nonempty X.G.jet.Sit := by
  obtain ⟨B, rfl, a, b, c⟩ := BaseExt.exists_base P S₀ S₁ S₂ h₀ h₁ h₂
  obtain ⟨X, rfl, h⟩ := exists_stages_over B hP D
  exact ⟨X, rfl, a, b, c, h⟩

end StagesInhab

theorem exists_stages : ∃ X : GlobalTheory.Mem.Stages, 0 < X.W.Drows ∧ (∀ u, Nontrivial (X.W.Mu u)) ∧
    ∀ u i, Nonempty ((X.C.mem u).C.cls i) := by
  obtain ⟨P, hP, -⟩ := StagesInhab.exists_pre_hasLetters
  obtain ⟨X, -, -, -, -, h1, -, h2, h3, -⟩ :=
    StagesInhab.exists_stages_large P hP 1 ∅ ∅ ∅ (by simp) (by simp) (by simp)
  exact ⟨X, by omega, h2, h3⟩

theorem nonempty_stages : Nonempty Stages := exists_stages.elim fun X _ => ⟨X⟩

theorem nonempty_record : Nonempty Formalism.BasicNotions.D7 := nonempty_stages.map Stages.toD7

end GlobalTheory.Mem

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReadOfMatrixTie
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem sharp_iota_eq (D : D7) (μ : D.what₂.Tup) : (RowSide.sharp D).iota μ = D.what₂.iota μ := by
  unfold RowSide.iota Rows.Data.iota
  rw [PrimeDegreeVariant.sharp_downTo]
  rfl

theorem exists_read_of_matrix_tie (D : D7) {Bs : DefBase D.what₂.LL} {A : DefAmb Bs} (X : CxData A)
    (fc : DefSub A → DefFace Bs) (cr : Crd A fc) (μ : D.what₂.Tup) (hμ : μ = D.what₂.mu0)
    (hv : Bs.v0 = InfinitePlace.mk D.what₂.embLL) {n : ℕ}
    (jA : (Fin n → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ)
    (H E : Matrix (Fin n) (Fin n) D.what₂.LL) (V : Matrix (Fin n) (Fin ((fc X.zs).Df1.nV Bs.μ0)) D.what₂.LL)
    (wU : D.what₂.Word → (fc X.zs).Dc.Mem)
    (eNu : ∀ u, (Fin ((fc X.zs).Dc.a (wU u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V)
    (eRR : (Fin (X.data cr true).D → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V)
    (hF : FormsTie D.what₂.embLL (W := (RowSide.sharp D).Amb μ) jA H E ((RowSide.sharp D).eOp μ))
    (hE : LinearMap.range E.mulVecLin = LinearMap.range V.mulVecLin)
    (hι : ∀ y, (RowSide.sharp D).iota μ (jA (V.mulVec y)) =
      (RowSide.sharp D).jEE (eRR (((X.data cr true).ι Bs.μ0).mulVec (((fc X.zs).Df1.Pq Bs.μ0).mulVec y))))
    (hNu : ∀ u, ∃ L, HLatTie (D.div.Nu u) L ((fc X.zs).Dc.Xc (wU u)) (eNu u)) :
    ∃ Rd : Read D X fc (twAt D.what₂.embLL Bs.v0), HEq Rd.wU wU ∧ HEq Rd.eNu eNu ∧ HEq Rd.eRR eRR ∧
      (∀ y, HEq (Rd.jV y) (jA (V.mulVec y))) ∧ Rd.ReadingFormsSpanGoodSubspace ∧ Rd.IotaRd cr ∧ Rd.NuTie ∧
      ((∃ L, HLatTie D.div.RR L (X.data cr true).XE eRR) → Rd.RRTie cr) ∧
      ((∀ (u : D.what₂.Word) (x : Fin ((fc X.zs).Dc.a (wU u)) → D.what₂.LL)
          (y : Fin ((fc X.zs).Df1.nV Bs.μ0) → D.what₂.LL),
          D.what₂.embLL ((fc X.zs).Dc.Pt (wU u) Bs.μ0 x y) =
            D.what₂.perCol u μ (D.jN u (eNu u x)) (jA (V.mulVec y))) → Rd.DcPt) := by
  subst hμ
  refine ⟨⟨wU, eNu, eRR, jA.comp V.mulVecLin, hv, fun a => ?_⟩, HEq.rfl, HEq.rfl, HEq.rfl, fun _ => HEq.rfl,
    ?_, fun y => ?_, hNu, fun h => h, fun h => h⟩
  · rw [emb_eq D.what₂.embLL Bs.v0 a, sgAt_mk D.what₂.embLL hv]
  · exact (GlobalTheory.range_op_eq_span_of_formsTie D.what₂.embLL (W := (RowSide.sharp D).Amb D.what₂.mu0) jA H E _ V hF hE).symm
  · have h := hι y
    rw [sharp_iota_eq] at h
    exact h

end GlobalTheory.Mem.SJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueCharOfTameCharPrimeResidueField
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

theorem tameChar_of_prime_residue : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (P : HeightOneSpectrum (𝓞 E)) (g : ℕ), g.Prime → normV P = g → ((g : ℕ) : 𝓞 E) ∈ P.asIdeal → ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → (∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ ∈ Ine (F := E) A, χ σ ^ (g - 1) = 1) → ∃ τ : (ZMod g)ˣ →* Oˣ, ∀ (x : (ZMod g)ˣ) (u : 𝓞 E), (((x : ZMod g).val : 𝓞 E) - u) ∈ P.asIdeal → τ x = NX.tameVal χ P 1 u := by
  intro E Ω _ _ _ _ _ P g hg hN hgP O _ _ _ _ _ hadic χ hχc hχI
  have : NeZero g := ⟨hg.ne_zero⟩
  have : Fact (1 < g) := ⟨hg.one_lt⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  set m := g - 1 with hm_def
  have hm0 : 0 < m := by have := hg.two_le; omega
  have hPtop : P.asIdeal ≠ ⊤ := P.isPrime.ne_top
  have hmP : ((m : ℕ) : 𝓞 E) ∉ P.asIdeal := by
    intro h
    apply hPtop
    rw [Ideal.eq_top_iff_one]
    have h1 : ((g : ℕ) : 𝓞 E) = (m : 𝓞 E) + 1 := by
      have : g = m + 1 := by have := hg.two_le; omega
      rw [this]; push_cast; ring
    have := P.asIdeal.sub_mem hgP h
    rwa [h1, add_sub_cancel_left] at this
  have hNm : normV P - 1 = m := by rw [hN]
  obtain ⟨ϖ, hϖ, hϖ2⟩ : ∃ ϖ : 𝓞 E, ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 := by
    have hlt : P.asIdeal ^ (1 + 1) < P.asIdeal ^ 1 := Ideal.pow_succ_lt_pow P.ne_bot 1
    rw [pow_one] at hlt
    exact SetLike.exists_of_lt hlt
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (ϖ : E)) hm0
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hm0.ne', eq_comm, map_eq_zero_iff _ (algebraMap E Ω).injective] at hπ
    have hϖ0 : ϖ = 0 := by exact_mod_cast hπ
    exact hϖ2 (hϖ0 ▸ Ideal.zero_mem _)
  obtain ⟨A₀, hA₀⟩ := exists_isPlaceOver Ω P
  have hvm : ¬ A₀.valuation (m : Ω) < 1 := by
    intro h; apply hmP; rw [← hA₀]; simpa using h
  have hex : ∀ u : 𝓞 E, u ∉ P.asIdeal → ∃ σ : G E Ω, σ ∈ Ine (F := E) A₀ ∧ ∃ ζ : Ω, ζ ^ m = 1 ∧
      A₀.valuation (ζ - algebraMap E Ω (u : E)) < 1 ∧ σ π = ζ * π := by
    intro u hu
    obtain ⟨ζ, hζ, hζu⟩ := GlobalTheory.T.exists_rootOfUnity_congr_unit_at_place A₀ P hA₀ u hu
    rw [hNm] at hζ
    obtain ⟨σ, hσ, hσπ⟩ := GlobalTheory.T.inertia_acts_on_tame_root A₀ P hA₀ m hm0 hmP ϖ hϖ hϖ2 π hπ ζ hζ
    exact ⟨σ, hσ, ζ, hζ, hζu, hσπ⟩
  have hrep : ∀ σ ∈ Ine (F := E) A₀, ∀ u : 𝓞 E, A₀.valuation (σ π / π - algebraMap E Ω (u : E)) < 1 →
      NX.TameRep P 1 σ u := by
    intro σ hσ u h
    refine ⟨A₀, hA₀, hσ, ϖ, π, hϖ, hϖ2, by rw [hNm]; exact hπ, ?_⟩
    rw [zpow_one]; exact h
  have hkey : ∀ (σ : G E Ω) (u : 𝓞 E), NX.TameRep P 1 σ u → NX.tameVal χ P 1 u = χ σ := by
    intro σ u h
    rw [NX.tameVal, dif_pos ⟨σ, h⟩]
    exact GlobalTheory.T.tameChar_eq_of_tameRep_congr P hadic χ hχc (by rw [hNm]; exact hm0) (by rw [hNm]; exact hmP)
      (by intro A hA σ' hσ'; rw [hNm]; exact hχI A hA σ' hσ') _ σ u u (⟨σ, h⟩ : ∃ σ, NX.TameRep P 1 σ u).choose_spec h (by simp)
  have hlt : ∀ a b : Ω, A₀.valuation a ≤ 1 → A₀.valuation b < 1 → A₀.valuation (a * b) < 1 := by
    intro a b ha hb
    rw [map_mul]
    calc A₀.valuation a * A₀.valuation b ≤ 1 * A₀.valuation b := by gcongr
      _ = A₀.valuation b := one_mul _
      _ < 1 := hb
  have hle : ∀ a b : Ω, A₀.valuation a ≤ 1 → A₀.valuation (a - b) < 1 → A₀.valuation b ≤ 1 := by
    intro a b ha hab
    have e : b = a - (a - b) := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le ha hab.le)
  have hP1 : ∀ w : 𝓞 E, w ∈ P.asIdeal → A₀.valuation (algebraMap E Ω (w : E)) < 1 := fun w hw => (hA₀ w).2 hw
  let U : (ZMod g)ˣ → 𝓞 E := fun x => (((x : ZMod g)).val : 𝓞 E)
  have hcong : ∀ x y : (ZMod g)ˣ, U x * U y - U (x * y) ∈ P.asIdeal := by
    intro x y
    simp only [U, Units.val_mul, ZMod.val_mul]
    have e : (((x : ZMod g).val * (y : ZMod g).val : ℕ) : 𝓞 E) =
        (g : 𝓞 E) * (((x : ZMod g).val * (y : ZMod g).val / g : ℕ) : 𝓞 E) +
          (((x : ZMod g).val * (y : ZMod g).val % g : ℕ) : 𝓞 E) := by
      exact_mod_cast (Nat.div_add_mod ((x : ZMod g).val * (y : ZMod g).val) g).symm
    rw [← Nat.cast_mul, e, add_sub_cancel_right]
    exact P.asIdeal.mul_mem_right _ hgP
  have hU1 : U 1 = 1 := by
    show (((1 : (ZMod g)ˣ) : ZMod g).val : 𝓞 E) = 1
    rw [Units.val_one, ZMod.val_one, Nat.cast_one]
  have hUP : ∀ x, U x ∉ P.asIdeal := by
    intro x hx
    have h := hcong x x⁻¹
    rw [mul_inv_cancel, hU1] at h
    apply hPtop
    rw [Ideal.eq_top_iff_one]
    have e : (1 : 𝓞 E) = U x * U x⁻¹ - (U x * U x⁻¹ - 1) := by ring
    rw [e]
    exact P.asIdeal.sub_mem (P.asIdeal.mul_mem_right _ hx) h
  choose σx hσx ζx hζx hζu hσπ using fun x => hex (U x) (hUP x)
  have hq : ∀ x, σx x π / π = ζx x := fun x => by rw [hσπ x, mul_div_cancel_right₀ _ hπ0]
  have hζ1 : ∀ x, A₀.valuation (ζx x) = 1 := fun x => valuation_eq_one_of_pow_eq_one A₀ hm0.ne' (hζx x)
  have hrepx : ∀ x, NX.TameRep P 1 (σx x) (U x) := fun x => hrep _ (hσx x) _ (by rw [hq]; exact hζu x)
  refine ⟨MonoidHom.mk' (fun x => χ (σx x)) ?_, ?_⟩
  · intro x y
    rw [← map_mul, ← hkey _ _ (hrepx (x * y))]
    refine hkey _ _ (hrep _ ((Ine (F := E) A₀).mul_mem (hσx x) (hσx y)) _ ?_)
    rw [GlobalTheory.TameTau.quot_mul (hσx x) m hvm hπ0 hπ, hq, hq]
    have e : ζx x * ζx y - algebraMap E Ω (U (x * y) : E) =
        ζx x * (ζx y - algebraMap E Ω (U y : E)) + algebraMap E Ω (U y : E) * (ζx x - algebraMap E Ω (U x : E)) +
          algebraMap E Ω ((U x * U y - U (x * y) : 𝓞 E) : E) := by
      push_cast; ring
    rw [e]
    refine Valuation.map_add_lt _ (Valuation.map_add_lt _ (hlt _ _ (hζ1 x).le (hζu y))
      (hlt _ _ (hle _ _ (hζ1 y).le (hζu y)) (hζu x))) (hP1 _ (hcong x y))
  · intro x u hxu
    show χ (σx x) = _
    refine (hkey _ _ (hrep _ (hσx x) _ ?_)).symm
    rw [hq]
    have e : ζx x - algebraMap E Ω (u : E) = (ζx x - algebraMap E Ω (U x : E)) +
        algebraMap E Ω ((U x - u : 𝓞 E) : E) := by
      push_cast; ring
    rw [e]
    exact Valuation.map_add_lt _ (hζu x) (hP1 _ hxu)

end GlobalTheory.TameTau
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSecNormCoeffLocalStatement
section
open AlgebraicGeometry CategoryTheory Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sec_normCoeff_local' : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    {M : LB X}, M.IsLB → ∀ t : (M.pull f).Sec, ∃ u : ∀ k, (lbPow M k).Sec, ∀ x : X,
      ∃ (V : X.Opens) (hV : IsAffineOpen V) (_ : IsDomain Γ(X, V)) (_ : IsIntegrallyClosed Γ(X, V))
        (τ : Γ(Y, f ⁻¹ᵁ V)), x ∈ V ∧ (∀ y : Y, f y ∈ V → (y ∈ nonzeroLocus t ↔ y ∈ Y.basicOpen τ)) ∧
        ∀ (k : ℕ) (z : X), z ∈ V →
          (z ∈ nonzeroLocus (u k) ↔ z ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k)) := by
  first | exact @GlobalTheory.NormalDescent.exists_sec_normCoeff_local | exact GlobalTheory.NormalDescent.exists_sec_normCoeff_local | (intros; apply GlobalTheory.NormalDescent.exists_sec_normCoeff_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSectionCompatibleSquareThickening
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SectionLimitSq

section Flat

variable {X Y Z : Scheme.{0}} {L : LB X}

theorem good_sq_iff (z : Z) (J' : (Z ⟶ X) → L.ι) :
    Good (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)) z (fun ψ _ => J' ψ) ↔ Good L z J' := by
  constructor
  · intro h ψ
    have := GlobalTheory.Algebraise.mem_wc.1 (h ψ)
    simpa using this
  · intro h ψ
    exact GlobalTheory.Algebraise.mem_wc.2 (by simpa using h ψ)

theorem eq_const_of_fin_one {α β : Type} (J : α → (Fin 1 → β)) : J = fun ψ _ => J ψ 0 :=
  funext fun ψ => funext fun κ => congrArg (J ψ) (Subsingleton.elim _ _)

theorem sval_flat {a n m : ℤ} {g : Y ⟶ X} {t : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m))}
    {s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g)
      (fun _ => n))}
    (h : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι), g (r z) ∈ L.U j →
      gs r z _ (t.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j))
    (r : Z ⟶ Y) (z : Z) (J' : (Z ⟶ X) → L.ι) (hJ : Good L z J') :
    sval t r z J' = sval s r z (fun ψ _ => J' ψ) :=
  h Z r z (J' (r ≫ g)) (by simpa using hJ (r ≫ g))

end Flat

theorem existsUnique_sec_of_compatible_sq : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ), 1 ≤ n → ∀ s : ∀ e : ℕ, LB.Sec (LB.LinComb (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) (K := Fin 1) (fun _ => (fstG I e P.A).left) (fun _ => (n : ℤ))), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).ι), Good (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) z J → sval (s (e + 1)) (r ≫ thickMap R I e P.A) z J = sval (s e) r z J) → ∃! σ : H0 (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) n, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).ι), Good (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) z J → sval σ (r ≫ (fstG I e P.A).left) z J = sval (s e) r z J := by
  intro hS R _ _ _ I _ P n hn s hs
  have hm : (((2 * n : ℕ) : ℤ)) = 2 * (n : ℤ) := by push_cast; ring
  have hn2 : 1 ≤ 2 * n := by omega
  choose t ht using fun e => GlobalTheory.T.linComb_pow_section_flatten P.L 2 (n : ℤ) ((2 * n : ℕ) : ℤ) hm (fstG I e P.A).left (s e)
  have htc : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι),
      Good P.L z J → sval (t (e + 1)) (r ≫ thickMap R I e P.A) z J = sval (t e) r z J := by
    intro e Z r z J hJ
    rw [sval_flat (ht (e + 1)) _ z J hJ, sval_flat (ht e) r z J hJ]
    exact hs e Z r z _ ((good_sq_iff z J).2 hJ)
  obtain ⟨σ₀, hσ₀, hσ₀u⟩ := GlobalTheory.SectionLimit.existsUnique_sec_of_compatible hS R I P (2 * n) hn2 t htc
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.linComb_pow_section_unflatten P.L 2 (n : ℤ) ((2 * n : ℕ) : ℤ) hm (𝟙 P.A.left) σ₀
  refine ⟨σ, fun e Z r z J hJ => ?_, fun σ' hσ' => ?_⟩
  · obtain ⟨J', rfl⟩ : ∃ J' : (Z ⟶ P.A.left) → P.L.ι, J = fun ψ _ => J' ψ := ⟨_, eq_const_of_fin_one J⟩
    have hJ' := (good_sq_iff z J').1 hJ
    rw [← sval_flat hσ _ z J' hJ', hσ₀ e Z r z J' hJ', sval_flat (ht e) r z J' hJ']
  · obtain ⟨τ, hτ⟩ := GlobalTheory.T.linComb_pow_section_flatten P.L 2 (n : ℤ) ((2 * n : ℕ) : ℤ) hm (𝟙 P.A.left) σ'
    have hτσ : τ = σ₀ := hσ₀u τ fun e Z r z J hJ => by
      rw [sval_flat hτ _ z J hJ, hσ' e Z r z _ ((good_sq_iff z J).2 hJ), ← sval_flat (ht e) r z J hJ]
    have hL := LB.isLB_linComb P.isLB (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => (2 : ℤ))
    refine DVR.SecOps.sec_ext (sec_ext_val hL fun y J hJ => ?_)
    obtain ⟨J', rfl⟩ : ∃ J' : (P.A.left ⟶ P.A.left) → P.L.ι, J = fun ψ _ => J' ψ := ⟨_, eq_const_of_fin_one J⟩
    have hJ' := (good_sq_iff y J').1 hJ
    rw [← sval_flat hτ _ y J' hJ', ← sval_flat hσ _ y J' hJ', hτσ]

end GlobalTheory.SectionLimitSq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreFamilyHermitianQuadraticFormAtUnitPropsStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure R) (β : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)), ν.IsAddHaarMeasure → IsUnit β → FibAt R σ J μ ν β m → m {X | qR R σ J (X 0) ≠ β} = 0 ∧ IsFiniteMeasureOnCompacts m ∧ ∀ m', FibAt R σ J μ ν β m' → m' = m := by
  first | exact @GlobalTheory.GaugeEx.FibBasic.fibAt_basic | exact GlobalTheory.GaugeEx.FibBasic.fibAt_basic | (intros; apply GlobalTheory.GaugeEx.FibBasic.fibAt_basic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianVectorAnnihilatorEquationsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianVector_annihilator_equations : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (v : F.H), HasCoeff F v (expPS (gaussPoly A x)) → (∀ (i : Fin P) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inl i) * f)) v = x (Sum.inl i) * inner ℂ (F.ι f) v + ∑ j, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inr j) f)) v) ∧ (∀ (j : Fin Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inr j) * f)) v = x (Sum.inr j) * inner ℂ (F.ι f) v + ∑ i, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) f)) v) := by
  first | exact @GlobalTheory.OscGauss.gauss_annihilator | exact GlobalTheory.OscGauss.gauss_annihilator | (intros; apply GlobalTheory.OscGauss.gauss_annihilator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusProductFormulaTotallyRealStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haarModulus_product_formula_totallyReal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (e : F), e ≠ 0 → (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => modu (Fv F v) (algebraMap F (Fv F v) e)).Finite ∧ modu (Ainf F) (algebraMap F (Ainf F) e) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), modu (Fv F v) (algebraMap F (Fv F v) e) = 1 := by
  first | exact @GlobalTheory.GaugeProdFormula.prod_modu_eq_one | exact GlobalTheory.GaugeProdFormula.prod_modu_eq_one | (intros; apply GlobalTheory.GaugeProdFormula.prod_modu_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusTensorEqModulusNormStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haarModulus_tensor_eq_modulus_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (u : R ⊗[F] E) (k : R), IsUnit u → algebraMap R (R ⊗[F] E) k = u * sigR R σ u → IsUnit k ∧ modu (R ⊗[F] E) u = modu R k := by
  first | exact @GlobalTheory.GaugeEx.modu_eq_modu_norm | exact GlobalTheory.GaugeEx.modu_eq_modu_norm | (intros; apply GlobalTheory.GaugeEx.modu_eq_modu_norm <;> assumption)
end

