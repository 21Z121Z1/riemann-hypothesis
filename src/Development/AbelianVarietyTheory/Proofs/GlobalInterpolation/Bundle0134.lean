import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0131
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArchimedeanUnitaryGroupStabilisersUnimodular
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0001
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0115
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLevelPrimePointModelRealisation
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0132
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Formalism.LocalToGlobal.HermitianForms.TiedSym
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0011
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0133
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeckeLawPointKernelOfCoefficientKernel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BadPrimeNormPrimeNeLevelPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0085

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupStabilisersUnimodularStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_unitaryGroup_stabilisers_unimodular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → UnimodularOver (AF F) σ J := by
  first | exact @GlobalTheory.AdelicStabUnimod.unimodularOver_adele | exact GlobalTheory.AdelicStabUnimod.unimodularOver_adele | (intros; apply GlobalTheory.AdelicStabUnimod.unimodularOver_adele <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArchimedeanUnitaryGroupStabilisersUnimodularStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_unitaryGroup_stabilisers_unimodular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → UnimodularOver (Ainf F) σ J := by
  first | exact @GlobalTheory.ArchUnitaryUnimod.unimodularOver_infinite | exact GlobalTheory.ArchUnitaryUnimod.unimodularOver_infinite | (intros; apply GlobalTheory.ArchUnitaryUnimod.unimodularOver_infinite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CompactSubgroupQuotientInvariantMeasureStatement
section
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactSubgroup_quotient_invariant_measure : CompactClause := by
  first | exact @GlobalTheory.QuotientMeasureCompact.compactClause | exact GlobalTheory.QuotientMeasureCompact.compactClause | (intros; apply GlobalTheory.QuotientMeasureCompact.compactClause <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjugatePrimeBoundPointKernelOfCoefficientKerneStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugatePrimeBound_pointKernel_of_coefficientKernel : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (Co : M.Coord) (Co' : M'.Coord) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Co.Ok → Co'.Ok → R.ValIs Co → R'.ValIs Co' → Built.Dat.KerBar k → K.IntBar Co Co' := by
  first | exact @GlobalTheory.LvT.Built.BarPass.intBar_of_kerBar | exact GlobalTheory.LvT.Built.BarPass.intBar_of_kerBar | (intros; apply GlobalTheory.LvT.Built.BarPass.intBar_of_kerBar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DilateLawPointKernelOfCoefficientKernelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dilateLaw_pointKernel_of_coefficientKernel : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Built.Dat.KerDil k → K.DilLaw := by
  first | exact @GlobalTheory.LvT.Built.DilPass.dilLaw_of_kerDil | exact GlobalTheory.LvT.Built.DilPass.dilLaw_of_kerDil | (intros; apply GlobalTheory.LvT.Built.DilPass.dilLaw_of_kerDil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLevelPrimePointModelRealisationStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelPrimePointModel_realisation : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T), ∃ M : PtModel B.ch i, Nonempty (B.Real i sp M) := by
  first | exact @GlobalTheory.LvT.Built.RealM.exists_real | exact GlobalTheory.LvT.Built.RealM.exists_real | (intros; apply GlobalTheory.LvT.Built.RealM.exists_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPointKernelRealisedModelsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pointKernel_realised_models : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) , Built.Dat.KerEq k → ∃ K : KerPt M M', K.TgtEq ∧ Built.Dat.KerIs R R' K k := by
  first | exact @GlobalTheory.LvT.Built.KerExt.exists_kerPt | exact GlobalTheory.LvT.Built.KerExt.exists_kerPt | (intros; apply GlobalTheory.LvT.Built.KerExt.exists_kerPt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueIsStandardAdeleCharUnramifiedCMBase
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex

namespace GlobalTheory.StdCharUnique

variable (F : Type) [Field F] [NumberField F]

theorem sum_mult_re_eq_trace (x : F) :
    ∑ w : InfinitePlace F, (w.mult : ℝ) * (w.embedding x).re = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  classical
  have h1 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ∑ φ : F →+* ℂ, φ x := by
    have h := trace_eq_sum_embeddings ℂ (K := ℚ) (L := F) (x := x)
    rw [eq_ratCast] at h
    rw [h]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _ fun _ => rfl).symm
  have h2 : ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ φ : F →+* ℂ, (φ x).re := by
    rw [← Complex.re_sum, ← h1, Complex.ratCast_re]
  rw [h2, ← Finset.sum_fiberwise Finset.univ (fun φ : F →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← InfinitePlace.card_filter_mk_eq, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr (by congr) fun φ hφ => ?_
  have hw : InfinitePlace.mk φ = w := (Finset.mem_filter.1 hφ).2
  subst hw
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]

theorem traceInf_add (x y : Ainf F) : traceInf F (x + y) = traceInf F x + traceInf F y := by
  rw [traceInf, traceInf, traceInf, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show (x + y) w = x w + y w from rfl, map_add, Complex.add_re, mul_add]

theorem continuous_traceInf : Continuous (traceInf F) := by
  refine continuous_finset_sum _ fun w _ => continuous_const.mul (Complex.continuous_re.comp ?_)
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)

theorem traceInf_algebraMap (x : F) :
    traceInf F (algebraMap F (Ainf F) x) = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  rw [← sum_mult_re_eq_trace, traceInf]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 2
  exact InfinitePlace.Completion.extensionEmbedding_coe w _

theorem existsUnique_isStdChar : ∃! ψ₀ : AddChar (AF F) ℂ, IsStdChar F ψ₀ := by
  let L : Ainf F →+ ℂ := AddMonoidHom.mk' (fun x => (traceInf F x : ℂ)) fun a b => by
    rw [traceInf_add, Complex.ofReal_add]
  obtain ⟨ψ, h1, h2⟩ := GlobalTheory.StdAdelicChar.exists_char_of_trace F L
    (Complex.continuous_ofReal.comp (continuous_traceInf F)) fun x => by
      show ((traceInf F (algebraMap F (Ainf F) x) : ℝ) : ℂ) = _
      rw [traceInf_algebraMap, Complex.ofReal_ratCast]
  have hψ : IsStdChar F ψ := ⟨h1, fun x => by
    rw [h2, stdInf]
    congr 1
    show _ * ((traceInf F x : ℝ) : ℂ) = _
    push_cast
    ring⟩
  exact ⟨ψ, hψ, fun ψ' h' => GlobalTheory.StdAdelicChar.eq_of_psiInf_eq h'.1 hψ.1
    fun x => (h'.2 x).trans (hψ.2 x).symm⟩

theorem existsUnique_isStdChar_cm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
      (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E →
      ∃! ψ₀ : AddChar (AF F) ℂ, IsStdChar F ψ₀ :=
  fun F _ _ _ _ _ _ _ _ _ _ _ => existsUnique_isStdChar F

end GlobalTheory.StdCharUnique

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdelicUnitaryGroupStabilizersUnimodular
section
open MeasureTheory NumberField IsDedekindDomain Matrix Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicUnimod
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure
open Formalism.UG (UJ cT intAd)
open scoped TensorProduct NNReal ENNReal Pointwise RestrictedProduct

noncomputable section

namespace GlobalTheory.FiniteAdelicUnimod

open GlobalTheory.AdelicPointsUnimod (exists_sum_tmul exists_compact_subring congSub isCompact_congSub
  modular_of_mem_compact isCompact_intAd)

section Adeles

variable {F : Type} [Field F] [NumberField F]

theorem exists_split_finiteAdele {κ : Type} [Finite κ] (a : κ → Af F) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra F R) (p : Af F →ₐ[F] R) (e : Af F),
    IsArtinianRing R ∧ Function.Surjective p ∧ p e = 1 ∧ (∀ x, p x = 0 → e * x = 0) ∧
      ∀ k, (1 - e) * a k ∈ intAd F := by
  classical
  let S := ⋃ k, {v : HeightOneSpectrum (𝓞 F) | a k v ∉ v.adicCompletionIntegers F}
  have hS : S.Finite := Set.finite_iUnion fun k => Filter.eventually_cofinite.1 (a k).2
  haveI : Finite S := hS.to_subtype
  let p : Af F →ₐ[F] (∀ v : S, v.1.adicCompletion F) :=
    { toFun := fun x v => x v.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  let s : (∀ v : S, v.1.adicCompletion F) → Af F := fun y =>
    ⟨fun v => if h : v ∈ S then y ⟨v, h⟩ else 0, by
      filter_upwards [hS.compl_mem_cofinite] with v hv
      rw [dif_neg hv]
      exact zero_mem _⟩
  have hs : ∀ y, p (s y) = y := fun y => funext fun v => dif_pos v.2
  have hs1 : ∀ v, s 1 v = if v ∈ S then 1 else 0 := fun v => by
    show dite _ _ _ = _
    split_ifs <;> rfl
  refine ⟨_, inferInstance, inferInstance, p, s 1, inferInstance, fun y => ⟨_, hs y⟩, hs 1, fun x hx => ?_,
    fun k v => ?_⟩
  · refine FiniteAdeleRing.ext _ fun v => ?_
    show s 1 v * x v = 0
    rw [hs1]
    split_ifs with h
    · rw [one_mul]
      exact congrFun hx ⟨v, h⟩
    · exact zero_mul _
  · show (1 - s 1 v) * a k v ∈ _
    rw [hs1]
    split_ifs with h
    · rw [sub_self, zero_mul]
      exact zero_mem _
    · rw [sub_zero, one_mul]
      exact not_not.1 fun h' => h (Set.mem_iUnion.2 ⟨k, h'⟩)

end Adeles

section Tensor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_split_tensor (σ : E →ₐ[F] E) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ) {κ : Type} [Finite κ]
    (C : NonUnitalSubring (Af F ⊗[F] E)) (hC : ∀ r ∈ intAd F, ∀ β : 𝓞 E, r ⊗ₜ[F] (β : E) ∈ C)
    (x : κ → Af F ⊗[F] E) : ∃ (B : Type) (_ : CommRing B) (σ' : B →+* B) (π : Af F ⊗[F] E →+* B)
      (e : Af F ⊗[F] E), (∀ x, π (sigR (Af F) σ x) = σ' (π x)) ∧ Function.Surjective π ∧ π e = 1 ∧
      (∀ x, π x = 0 → e * x = 0) ∧ sigR (Af F) σ e = e ∧ Generic σ' ∧ ∀ k, (1 - e) * x k ∈ C := by
  classical
  choose a ha using fun k => exists_sum_tmul (x k)
  obtain ⟨R, _, _, p, e, hR, hp, hpe, hker, hint⟩ :=
    exists_split_finiteAdele (κ := κ × _) fun q => a q.1 q.2
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsArtinianRing (R ⊗[F] E) := IsArtinianRing.of_finite R _
  letI : Algebra ℚ (R ⊗[F] E) := ((inclR (F := F) R).comp (algebraMap ℚ E)).toAlgebra
  refine ⟨R ⊗[F] E, inferInstance, sigR R σ, (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom,
    e ⊗ₜ 1, fun y => ?_, Algebra.TensorProduct.map_surjective _ _ hp Function.surjective_id, ?_, fun y hy => ?_, ?_,
    generic_of_semilocal (δ := inclR R δ) (hδ.isUnit.map _) ?_, fun k => ?_⟩
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [sigR]
    | add x y hx hy => simp only [map_add, hx, hy]
  · simp [hpe, Algebra.TensorProduct.one_def]
  · have hy' : y ∈ RingHom.ker (Algebra.TensorProduct.map p (AlgHom.id F E)) := hy
    rw [Algebra.TensorProduct.rTensor_ker _ hp] at hy'
    clear hy
    induction hy' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      simp [hker z hz]
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul a x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
  · simp [sigR]
  · simp [sigR, inclR, hσδ, TensorProduct.tmul_neg]
  · rw [ha k, Finset.mul_sum, Algebra.TensorProduct.one_def, ← TensorProduct.sub_tmul]
    refine sum_mem fun i _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact hC _ (hint (k, i)) _

theorem isUnimodularLC_finiteAdele (σ : E →ₐ[F] E) (hss : ∀ x, σ (σ x) = x) {δ : E} (hδ : δ ≠ 0)
    (hσδ : σ δ = -δ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) :
    IsUnimodularLC (HA (Af F) σ J) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  obtain ⟨h⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Af F)
  haveI : T2Space (Af F ⊗[F] E) := h.isEmbedding.t2Space
  obtain ⟨_, _, _⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (Af F) σ n J
  haveI : BorelSpace (HA (Af F) σ J) := ⟨rfl⟩
  haveI : IsTopologicalGroup (HA (Af F) σ J) := inferInstanceAs (IsTopologicalGroup (HR (Af F) σ J))
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨Measure.haar, inferInstance⟩, fun μ _ => ?_⟩
  have hσ := GlobalTheory.AdelicUnitaryTop.continuous_sigR (Af F) σ
  obtain ⟨C, hCc, hC⟩ := exists_compact_subring (F := F) (E := E) (intAd F).toNonUnitalSubring
    (isCompact_intAd F)
  obtain ⟨M, hM⟩ := exists_framed (σ := (σ : E →+* E)) hss (J := J) (by ext i j; exact hJ.1 i j) hJ.2
  have hF : Framed (sigR (Af F) σ) (JR (Af F) J) (M.map (inclR (Af F))) :=
    hM.map fun x => by simp [sigR, inclR]
  have hss' := GlobalTheory.AdelicPointsUnimod.sigR_sigR (R := Af F) hss
  obtain ⟨T, hTc, hT, hT'⟩ := exists_involution hσ hss' hF
  refine ⟨fun g => ?_⟩
  obtain ⟨B, _, σ', π, e, h1, h2, h3, h4, h5, h6, h7⟩ := exists_split_tensor σ hδ hσδ
    (κ := Bool × Fin n × Fin n) C hC fun p =>
      (mat (σ := sigR (Af F) σ) (J := JR (Af F) J) (bif p.1 then g else g⁻¹) - 1) p.2.1 p.2.2
  let χ : HA (Af F) σ J →* ℝ≥0 := Measure.modularCharacter
  have hχ := modular_involution (G := HA (Af F) σ J) T hTc hT
  obtain ⟨k, hk, hk', hkg⟩ := exists_char_eq h1 h2 h3 h4 h5 hss' hF h6 χ
    (fun x x' h => by
      rw [hT' x x' h]
      exact hχ x) g
  have hkK : k ∈ congSub (sigR (Af F) σ) (JR (Af F) J) C :=
    ⟨fun i j => by rw [hk]; exact h7 (true, i, j), fun i j => by rw [hk']; exact h7 (false, i, j)⟩
  let K : Subgroup (HA (Af F) σ J) := congSub (sigR (Af F) σ) (JR (Af F) J) C
  have hKc : IsCompact (K : Set (HA (Af F) σ J)) := isCompact_congSub hσ _ C hCc
  have h8 := modular_of_mem_compact K hKc (k := k) hkK
  rw [map_mul_right_eq, show Measure.modularCharacter g = 1 from hkg.symm.trans h8, one_smul]

end Tensor

theorem unimodularOver_finiteAdele : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      UnimodularOver (Af F) σ J := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have hss := GlobalTheory.HermLineZeros.conj_invol hσ
  obtain ⟨d, hd⟩ := GlobalTheory.HermLineZeros.exists_conj_ne hσ
  exact GlobalTheory.ArchUnitaryUnimod.unimodularOver_of_forall (Af F) hss
    (fun _ _ h => isUnimodularLC_finiteAdele σ hss (sub_ne_zero.2 hd) (by rw [map_sub, hss, neg_sub]) h) hJ

end GlobalTheory.FiniteAdelicUnimod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FormsTiedSymChiZeroFinite
section
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem formsTiedSym_chi_zero_finite : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf), (∀ i, (∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i)) ∧ ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i - 1)) → ∃ n : ℕ, 0 < n ∧ ∀ x : (Tf.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U, (((Tf.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧ ∃ r : D.what₂.LL, D.what₂.embLL r = (((Tf.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ) :=
  fun D _ _ _ Tf h =>
    GlobalTheory.T.unipotentTypeLevel_character_finiteOrder_rootsOfUnity _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Tf.glev0 D.what₂.LL D.what₂.embLL D.host.g_prime (fun i => (h i).1)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeckeLawPointKernelOfCoefficientKernelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeLaw_pointKernel_of_coefficientKernel : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Built.Dat.KerUK k → K.UKLaw := by
  first | exact @GlobalTheory.LvT.Built.UK.ukLaw_of_kerUK | exact GlobalTheory.LvT.Built.UK.ukLaw_of_kerUK | (intros; apply GlobalTheory.LvT.Built.UK.ukLaw_of_kerUK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntAtOfLocTop
section
namespace GlobalTheory.LvT.Built.Box

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2
open GlobalTheory.ColPeriod GlobalTheory.LvT.Built.IsTerm

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ} {u : Pr.Word}

theorem pow_dvd_cA (P : rowSG Pr sel mu) : qOf P.1 ^ cst.A ∣ cAof sel mu cst :=
  pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun Q : rowSG Pr sel mu => qOf Q.1) (Finset.mem_univ P)) _

theorem intAt_of_locTop (hL : L.Ok Ch sel mu cst G m2) (P : rowSG Pr sel mu) {j : ℕ} (hj : j = R.m)
    (x : HomE X.E (R.N (m2 + 1)) (R.N j)) (y : Sp X.E (R.N (m2 + 1)))
    (h : TopStep.locTop Ch sel mu cst m2 P (castSp X.E (congrArg R.N hj) ∘ₗ x) y ≠ 0) (s : Fin (R.N (m2 + 1))) (l : Fin (R.N j)) :
    IntAt P.1 ((qOf P.1 : X.E) ^ cst.A * x (Pi.single s 1) l) := by
  subst hj
  have hm := hL.hm
  rw [castSp_comp] at h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  have hl2 := l.2
  by_cases hlt : l.1 < R.N R.m - 1
  · have h3 := GlobalTheory.SuppTop.intAt_of_phiTop Ch mu cst.sharp _ hm P.1 _ h1 l.1 s.1 hlt s.2
    have e1 : LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) (Loc.eN X.E (R.N (m2 + 1) + cOf R (m2 + 1)) s.1) =
        Pi.single s 1 := by
      funext t
      simp [LinearMap.funLeft_apply, Loc.eN, Pi.single_apply, Fin.ext_iff]
    simp only [LinearMap.comp_apply, e1] at h3
    have hlt' : l.1 < R.N R.m - 1 + 0 := hlt
    simp only [Loc.atN, dif_pos hlt', prXp, LinearMap.funLeft_apply] at h3
    have h4 := (GlobalTheory.SuppTop.intAt_nat P.1 (qOf P.1 ^ cst.A)).mul h3
    rwa [Nat.cast_pow] at h4
  · have h3 := GlobalTheory.SuppTop.intAt_of_ftY sel mu cst P _ _ h2 s
    have hl3 : R.N R.m - 1 < R.N R.m := by omega
    have hl4 : (⟨R.N R.m - 1, hl3⟩ : Fin (R.N R.m)) = l := Fin.ext (by simp only; omega)
    simp only [LinearMap.comp_apply, atNL, dif_pos hl3, LinearMap.proj_apply, hl4] at h3
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hL.cst_ok.M_le_A
    have h4 := (GlobalTheory.SuppTop.intAt_nat P.1 (qOf P.1 ^ k)).mul h3
    rw [Nat.cast_pow, ← mul_assoc, ← pow_add] at h4
    rwa [hk]

theorem intAt_of_xiAt (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < R.m) {b : Idx sel mu L i} {b' : Idx sel mu L (i + 1)}
    {p : PtAt R sel mu cst u i} {p' : PtAt R sel mu cst u (i + 1)} {x : HomE X.E (R.N i) (R.N (i + 1))}
    (hx : xiAt Ch sel mu cst L u i b b' p p' x ≠ 0) (P : rowSG Pr sel mu) (s : Fin (R.N i)) (l : Fin (R.N (i + 1))) :
    IntAt P.1 ((qOf P.1 : X.E) ^ cst.A * inFr (frsF sel mu p.1.1 P) (frsF sel mu p'.1.1 P) x (Pi.single s 1) l) := by
  have hm := hL.hm
  rcases lt_trichotomy (i + 2) R.m with h | h | h
  · rw [xiAt_entry Ch sel mu cst L h (b.some_get (by omega)).symm (b'.some_get (by omega)).symm] at hx
    exact hL.xiSupp i (by omega) _ _ P _
      (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) P (Finset.mem_univ _)) s l
  · obtain rfl : i = m2 := by omega
    rw [xiAt_penultimate_eq_xiCpl1 Ch sel mu cst L h (b.some_get (by omega)).symm] at hx
    exact hL.psiSuppX _ P _ _ (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) P (Finset.mem_univ _)) s l
  · obtain rfl : i = m2 + 1 := by omega
    have h1 : m2 + 1 + 1 = R.m := by omega
    rw [xiAt_last Ch sel mu cst L h1] at hx
    exact intAt_of_locTop hL P h1 _ _ (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) P (Finset.mem_univ _)) s l

theorem inBox_xiAt : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → L.Ok Ch sel mu cst G m2 → i < R.m → (∃ (σ₀ : X.K →+* ℂ) (e : Fin R.m → X.Tau → ℚ) (m0 : Fin R.m → Formalism.L2.Host.HChar X.E) (eta : Formalism.L2.Host.HChar X.E), Ch.Tied σ₀ e m0 eta) → ∀ (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)) (p : PtAt R sel mu cst u i) (p' : PtAt R sel mu cst u (i + 1)), GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.InBox (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.1.1.deco.1.N p'.1.1.deco.1.N (xiAt Ch sel mu cst L u i b b' p p') := by
  classical
  rintro X Pr R Ch sel S mu cst L G m2 u i hX hPr hsel hS hg hL hi ⟨σ₀, e, m0, eta, ht⟩ b b' p p'
  refine ⟨fun x hx P hP y hy => ?_, fun x y hy => ?_⟩
  · change ((cAof sel mu cst : ℕ) : 𝓞 X.E) • x y ∈ _
    have hP' : P ∈ Pr.vT u ∨ P ∈ rowSG Pr sel mu := by
      unfold Sall at hP
      exact Finset.mem_union.1 hP
    rcases hP' with hP | hP
    · exact Submodule.smul_mem _ _ (phiT_of_xiAt_ne_zero Ch sel mu cst L hx ⟨P, hP⟩ y hy).1
    · obtain ⟨k, hk⟩ : qOf P ^ cst.A ∣ cAof sel mu cst :=
        pow_dvd_cA ⟨P, hP⟩
      have h := GlobalTheory.SuppTop.smul_mem_of_inFr P _ _ _ _ (isFrames_frsF p.1.1 ⟨P, hP⟩) (isFrames_frsF p'.1.1 ⟨P, hP⟩)
        (cAof sel mu cst) x (fun s l => by
          have h4 := (GlobalTheory.SuppTop.intAt_nat P k).mul (intAt_of_xiAt hL hi hx ⟨P, hP⟩ s l)
          rw [hk, Nat.cast_mul, Nat.cast_pow, mul_comm _ (k : X.E), mul_assoc]
          exact h4) y hy
      simpa [Nat.cast_smul_eq_nsmul] using h
  · obtain ⟨Φ, hΦ⟩ := exists_local hX hPr hsel hS hL (muqUnit_of_tied hX hPr hsel hS hg hL ht) hi b b'
    obtain ⟨w, hw⟩ := exists_place X.K (hPr.T_prime u)
    rw [(hΦ p p').1, (hΦ p p').1]
    congr 1
    · exact phiT_add _ p'.1.1.deco.2 (T := Pr.T u) (fun Q => T_mem_of_piT_mem hPr u (GlobalTheory.ColPeriod.mem_divs Q.2)) x fun Q =>
        exists_of_mem_mulLat (Dvd.intro _ rfl) hy (Finset.mem_union_left _ Q.2)
    · refine Finset.prod_congr rfl fun P _ => ?_
      have hdv : qOf P.1 ^ cst.B ∣ cBof sel mu cst u :=
        Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ P)) _) _
      obtain ⟨z, hz, rfl⟩ := exists_of_mem_mulLat hdv hy (Finset.mem_union_right _ P.2)
      rw [Nat.cast_pow]
      exact (awayAt_inFr (isFrames_frsF p.1.1 P) (isFrames_frsF p'.1.1 P) ((hΦ p p').2 P w hw)).2 x z hz

end GlobalTheory.LvT.Built.Box
end

