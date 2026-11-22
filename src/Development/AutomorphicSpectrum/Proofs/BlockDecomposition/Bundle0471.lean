import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.PropsExh
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0447
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0448
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactStandardMaximal
section
noncomputable section

namespace GlobalTheory.CompanionTheory.StdK

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_intBasis : ∃ b : Module.Basis (Fin (Module.finrank F E)) F E, ∀ i, IsIntegral ℤ (b i) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h : ∀ x : E, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ (m • x) := fun x => by
    obtain ⟨m, hm, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (Algebra.IsAlgebraic.isAlgebraic x)).exists_integral_multiple
    exact ⟨m, hm, hi⟩
  choose m hm hi using h
  let b := Module.finBasis F E
  let u : Fin (Module.finrank F E) → Fˣ := fun i => Units.mk0 (m (b i) : F) (by exact_mod_cast hm _)
  refine ⟨b.unitsSMul u, fun i => ?_⟩
  rw [Module.Basis.unitsSMul_apply]
  have e : u i • b i = m (b i) • b i := by
    change ((m (b i) : F)) • b i = _
    exact Int.cast_smul_eq_zsmul F _ _
  rw [e]
  exact hi _

theorem isOpen_intAd : IsOpen {a : AF F | ∀ v, evFin F v a ∈ v.adicCompletionIntegers F} := by
  have h : IsOpen {f : FiniteAdeleRing (𝓞 F) F | ∀ v, f v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  exact h.preimage continuous_snd

theorem evFin_finOne (v : HeightOneSpectrum (𝓞 F)) : evFin F v (finOne F) = 1 := rfl

theorem evI_finOne_mul (a : AF F) : evI F (finOne F * a) = 0 := by
  have e : (finOne F * a).1 = 0 := by
    change (0 : Ainf F) * a.1 = 0
    exact zero_mul _
  unfold evI
  rw [e, map_zero]

variable (F E) in

def finInt : AddSubgroup (AE F E) :=
  (intHat F E).comap (DistribMulAction.toAddMonoidHom (AE F E) (finOne F))

theorem mem_finInt {z : AE F E} : z ∈ finInt F E ↔ finOne F • z ∈ intHat F E := Iff.rfl

theorem smul_incl_mem_finInt {a : AF F} (ha : ∀ v, evFin F v a ∈ v.adicCompletionIntegers F) (o : 𝓞 E) :
    a • inclR (F := F) (E := E) (AF F) (o : E) ∈ finInt F E := by
  rw [mem_finInt, smul_smul]
  refine AddSubgroup.subset_closure ⟨finOne F * a, evI_finOne_mul a, fun v => ?_, o, rfl⟩
  rw [map_mul, evFin_finOne, one_mul]
  exact ha v

theorem isOpen_finInt : IsOpen (finInt F E : Set (AE F E)) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨b, hb⟩ := exists_intBasis (F := F) (E := E)
  let e := (Algebra.TensorProduct.basis (AF F) b).equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hS : IsOpen {z : AE F E | ∀ i, ∀ v, evFin F v (e z i) ∈ v.adicCompletionIntegers F} := by
    have e0 : {z : AE F E | ∀ i, ∀ v, evFin F v (e z i) ∈ v.adicCompletionIntegers F} =
        ⋂ i, (fun z => e z i) ⁻¹' {a : AF F | ∀ v, evFin F v a ∈ v.adicCompletionIntegers F} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [e0]
    exact isOpen_iInter_of_finite fun i => (isOpen_intAd (F := F)).preimage ((continuous_apply i).comp he)
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (Filter.mem_of_superset (hS.mem_nhds ?_) ?_)
  · intro i v
    simp
  · intro z hz
    have e1 : z = ∑ i, e z i • (Algebra.TensorProduct.basis (AF F) b i) :=
      ((Algebra.TensorProduct.basis (AF F) b).sum_equivFun z).symm
    rw [e1]
    refine sum_mem fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply]
    exact smul_incl_mem_finInt (hz i) ⟨b i, hb i⟩

theorem isClosed_finInt : IsClosed (finInt F E : Set (AE F E)) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact AddSubgroup.isClosed_of_isOpen _ isOpen_finInt

theorem compFin_finOne_smul (v : HeightOneSpectrum (𝓞 F)) (z : AE F E) :
    compFin F E v (finOne F • z) = compFin F E v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul a e =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    simp [compFin, map_mul, evFin_finOne]

theorem absFin_le_one_of_mem {z : AE F E} (hz : z ∈ intHat F E) (v : HeightOneSpectrum (𝓞 F)) :
    absFin F v (compFin F E v z) ≤ 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, o, rfl⟩ := hz
    have e : compFin F E v (a • inclR (F := F) (E := E) (AF F) (o : E)) = evFin F v a ⊗ₜ[F] (o : E) := by
      simp [compFin, inclR, TensorProduct.smul_tmul']
    rw [e]
    refine (absFin_tmul_le F v _ o).trans ?_
    exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 (ha v)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (absFin_add_le F v _ _).trans (max_le hx hy)
  | neg x _ hx =>
    rw [map_neg, absFin_neg]
    exact hx

theorem opNorm_le_one {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ} (h : M * Mᴴ = 1) : opNorm M ≤ 1 := by
  have e : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M * star (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M) = 1 := by
    rw [← map_star, ← map_mul, Matrix.star_eq_conjTranspose, h, map_one]
  have h2 := CStarRing.norm_self_mul_star (x := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M)
  rw [e] at h2
  have h3 : ‖(1 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have h4 := norm_nonneg (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M)
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M‖₊ ≤ 1
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  nlinarith

variable {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem heightGL_eq_one {ι : Type} [Fintype ι] [DecidableEq ι] (B : Base F E) (hcm : IsCMExt F E σ)
    (g : GL ι (AE F E)) (hu : ∀ w, (g.1.map (piInf (B.emb w))) * (g.1.map (piInf (B.emb w)))ᴴ = 1)
    (hf : ∀ i j, g.1 i j ∈ finInt F E) (hf' : ∀ i j, (g⁻¹).1 i j ∈ finInt F E) : heightGL F g = 1 := by
  rw [heightGL_eq_one_iff]
  refine ⟨fun w => htOf_eq_one.2 ⟨?_, ?_⟩, fun v => htOf_eq_one.2 ⟨?_, ?_⟩⟩
  · rw [normInf_eq_opNorm hcm (B.emb w)]
    exact opNorm_le_one (hu w)
  · rw [normInf_eq_opNorm hcm (B.emb w), ← map_inv]
    change opNorm ((g⁻¹).1.map (piInf (B.emb w))) ≤ 1
    have hM : g.1.map (piInf (B.emb w)) * (g⁻¹).1.map (piInf (B.emb w)) = 1 := by
      rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have h1 := mul_eq_one_comm.1 (hu w)
    have h2 : (g⁻¹).1.map (piInf (B.emb w)) = (g.1.map (piInf (B.emb w)))ᴴ := by
      calc _ = (g.1.map (piInf (B.emb w)))ᴴ * g.1.map (piInf (B.emb w)) * (g⁻¹).1.map (piInf (B.emb w)) := by
            rw [h1, Matrix.one_mul]
        _ = _ := by rw [Matrix.mul_assoc, hM, Matrix.mul_one]
    rw [h2]
    exact opNorm_le_one (by rw [Matrix.conjTranspose_conjTranspose]; exact h1)
  · refine (normFin_le_iff F v).2 fun i j => ?_
    change absFin F v (compFin F E v (g.1 i j)) ≤ 1
    rw [← compFin_finOne_smul]
    exact absFin_le_one_of_mem (hf i j) v
  · refine (normFin_le_iff F v).2 fun i j => ?_
    rw [← map_inv]
    change absFin F v (compFin F E v ((g⁻¹).1 i j)) ≤ 1
    rw [← compFin_finOne_smul]
    exact absFin_le_one_of_mem (hf' i j) v

theorem isCompact_of_isStdK (B : Base F E) (hcm : IsCMExt F E σ) (b : GL (Fin n ⊕ Fin n) E)
    (K : Subgroup (G2 σ Y)) (hK : IsStdK (σ := σ) (Y := Y) B b K) : IsCompact (K : Set (G2 σ Y)) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  let bA : GL (Fin n ⊕ Fin n) (AE F E) := Formalism.UG.bc (inclR (F := F) (E := E) (AF F)) b
  let m : G2 σ Y → GL (Fin n ⊕ Fin n) (AE F E) := fun x => bA⁻¹ * x.1 * bA
  have hm : ∀ x, (m x).1 = inFrame b x := fun x => rfl
  have hv : Continuous fun x : G2 σ Y => (x.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :=
    Units.continuous_val.comp continuous_subtype_val
  have hfr : Continuous fun x : G2 σ Y => inFrame b x := (continuous_const.matrix_mul hv).matrix_mul continuous_const
  have hfi : Continuous fun x : G2 σ Y => inFrame b x⁻¹ := hfr.comp continuous_inv
  have hcl : IsClosed (K : Set (G2 σ Y)) := by
    have e1 : (K : Set (G2 σ Y)) = (⋂ w, {k : G2 σ Y | (inFrame b k).map (piInf (B.emb w)) *
          ((inFrame b k).map (piInf (B.emb w)))ᴴ = 1}) ∩
        ((⋂ i, ⋂ j, (fun k : G2 σ Y => inFrame b k i j) ⁻¹' (finInt F E : Set (AE F E))) ∩
          ⋂ i, ⋂ j, (fun k : G2 σ Y => inFrame b k⁻¹ i j) ⁻¹' (finInt F E : Set (AE F E))) := by
      ext k
      simp only [SetLike.mem_coe, hK k, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_preimage,
        Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, mem_finInt]
    rw [e1]
    refine (isClosed_iInter fun w => isClosed_eq ?_ continuous_const).inter
      ((isClosed_iInter fun i => isClosed_iInter fun j => isClosed_finInt.preimage ?_).inter
        (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_finInt.preimage ?_))
    · have h := hfr.matrix_map (GlobalTheory.ContMapReal.continuous_piInf (B.emb w))
      exact h.matrix_mul h.matrix_conjTranspose
    · exact (continuous_apply j).comp ((continuous_apply i).comp hfr)
    · exact (continuous_apply j).comp ((continuous_apply i).comp hfi)
  have hσ : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hUG : IsClosed (UG (cA σ) (dbl (incM F Y.J)) : Set (GL (Fin n ⊕ Fin n) (AE F E))) := by
    have hg : Continuous fun g : GL (Fin n ⊕ Fin n) (AE F E) => (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :=
      Units.continuous_val
    exact isClosed_eq ((hg.matrix_transpose.matrix_mul continuous_const).matrix_mul (hg.matrix_map hσ)) continuous_const
  have hC := hUG.isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_heightGL_le (E := E) (n := Fin n ⊕ Fin n) F (heightGL F bA * heightGL F bA⁻¹))
  refine hC.of_isClosed_subset hcl fun k hk => ?_
  obtain ⟨hu, hf⟩ := (hK k).1 hk
  have hinv : (m k)⁻¹ = m k⁻¹ := by
    change (bA⁻¹ * k.1 * bA)⁻¹ = bA⁻¹ * (k.1)⁻¹ * bA
    group
  have h1 : heightGL F (m k) = 1 := heightGL_eq_one B hcm (m k) hu
    (fun i j => mem_finInt.2 (hf k (by simp) i j))
    (fun i j => by
      rw [hinv]
      exact mem_finInt.2 (hf k⁻¹ (by simp) i j))
  have e2 : k.1 = bA * m k * bA⁻¹ := by
    change k.1 = bA * (bA⁻¹ * k.1 * bA) * bA⁻¹
    group
  change heightGL F k.1 ≤ _
  rw [e2]
  refine (heightGL_mul_le F _ _).trans ?_
  rw [(heightGL_mul_of_eq_one F h1 bA).1]

theorem isCompact_K : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → IsCompact (K : Set (G2 σ Y)) := by
  intro F E _ _ _ _ _ σ B n Y r s hB _ _ b K a _ hK _
  exact isCompact_of_isStdK B hB.cm b K hK

end GlobalTheory.CompanionTheory.StdK

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOrderedFormSnoc
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.ExhGood

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ind₂_map_injective_right {r t N : ℕ} (e : Fin r ⊕ Fin t ≃ Fin N) {U W W' : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ (GL (Fin r) k) U)
    {ρ : Representation ℂ (GL (Fin t) k) W} {ρ' : Representation ℂ (GL (Fin t) k) W'} (f : ρ.IntertwiningMap ρ')
    (hf : Function.Injective f) :
    ∃ F : (ind₂ e (extTensor σ ρ)).IntertwiningMap (ind₂ e (extTensor σ ρ')), Function.Injective F := by
  have hι : Function.Injective (GlobalTheory.ParIndExact.extTensorMapRight σ f) :=
    Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf
  have hι' : Function.Injective
      (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ f) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := hι
  exact ⟨parIndMap (two e)
      (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ f) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom),
    GlobalTheory.ParIndExact.parIndMap_injective _ _ hι'⟩

theorem pair_equiv {N : ℕ} (y : Fin 2 → IrrGL k) (hd : ∑ i, (y i).1 = N) {a : IrrGL k} (ha : y 0 = a)
    (h : a.1 + (y 1).1 = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor a.rep (y 1).rep)).Equiv (prodIrr y hd)) := by
  subst ha h
  exact nonempty_prod₂_equiv_prodIrr_rep y hd

theorem embed_family {N c : ℕ} (y : Fin 2 → IrrGL k) (v : Fin (c + 1) → IrrGL k) (t : Fin c → IrrGL k)
    (h0 : y 0 = v 0) (hs : ∀ i, v i.succ = t i) (hd : ∑ i, (y i).1 = N) (hv : ∑ i, (v i).1 = N)
    (ht : ∑ i, (t i).1 = (y 1).1) (g : (y 1).rep.IntertwiningMap (prodIrr t ht)) (hg : Function.Injective g) :
    ∃ F : (prodIrr y hd).IntertwiningMap (prodIrr v hv), Function.Injective F := by
  have e : t = fun i => v i.succ := funext fun i => (hs i).symm
  subst e
  have h : (v 0).1 + (y 1).1 = N := by
    rw [← h0, ← hd, Fin.sum_univ_two]
  have A0 := pair_equiv y hd h0 h
  have B0 := GlobalTheory.ProdReorder.multiProd_head (k := k) (d := fun i => (v i).1) (fun i => (v i).rep)
    (stdBlocks (fun i => (v i).1) hv) h (stdBlocks (fun i : Fin c => (v i.succ).1) ht)
  have F0 := ind₂_map_injective_right (stdSum h) (v 0).rep g hg
  obtain ⟨A⟩ := A0
  obtain ⟨B⟩ := B0
  obtain ⟨F, hF⟩ := F0
  exact ⟨(B.symm.toIntertwiningMap.comp F).comp A.symm.toIntertwiningMap,
    B.symm.toLinearEquiv.injective.comp (hF.comp A.symm.toLinearEquiv.injective)⟩

theorem isOrderedForm_snoc {h : ℕ} {Δ : Fin h → Segment k} {𝔫 : Multiset (Segment k)} (H : IsOrderedForm Δ 𝔫)
    (s : Segment k) (hs : ∀ D ∈ 𝔫, ¬ D.Precedes s) :
    IsOrderedForm (Fin.snoc (α := fun _ => Segment k) Δ s) (𝔫 + {s}) := by
  refine ⟨?_, fun i j hij => ?_⟩
  · rw [← H.1, Fin.univ_val_map, Fin.univ_val_map, List.ofFn_succ']
    simpa using (Multiset.coe_add _ [s]).symm
  · induction j using Fin.lastCases with
    | last =>
      obtain ⟨i, rfl⟩ : ∃ i', Fin.castSucc i' = i :=
        ⟨i.castPred (Fin.ne_last_of_lt hij), by simp⟩
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact hs _ (H.1 ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ_val i))
    | cast j =>
      obtain ⟨i, rfl⟩ : ∃ i', Fin.castSucc i' = i :=
        ⟨i.castPred (Fin.ne_last_of_lt hij), by simp⟩
      simp only [Fin.snoc_castSucc]
      exact H.2 i j (by simpa using hij)

theorem exh_good [CharZero k] (HS : GlobalTheory.Published.StandardCosocleGL) (HL : LSocleGL k) (x : IrrGL k) (y : Fin 2 → IrrGL k)
    (hd : ∑ a, (y a).1 = x.1) (hc : (y 0).IsCusp) (𝔫 : Multiset (Segment k)) (hn : IsL 𝔫 (y 1).rep)
    (hp : ∀ Δ ∈ 𝔫, ¬ Δ.Precedes (Segment.single (y 0) hc))
    (hf : ∃ f : x.rep.IntertwiningMap (prodIrr y hd), Function.Injective f) :
    IsL (𝔫 + {Segment.single (y 0) hc}) x.rep := by
  obtain ⟨f, hf⟩ := hf
  have hn' := hn
  obtain ⟨h, z, hz, ⟨Δ, hΔ, hzL⟩, -⟩ := hn'
  set s := Segment.single (y 0) hc with hs
  let w : Fin (h + 1) → IrrGL k := Fin.snoc (α := fun _ => IrrGL k) z (y 0)
  have hwL : LFactors (𝔫 + {s}) w := by
    refine ⟨_, isOrderedForm_snoc hΔ s hp, fun i => ?_⟩
    induction i using Fin.lastCases with
    | last =>
      have e : w (Fin.last h) = y 0 := Fin.snoc_last (α := fun _ => IrrGL k) _ _
      rw [e, Fin.snoc_last]
      exact (single_spec hc).2.1
    | cast i =>
      have e : w i.castSucc = z i := Fin.snoc_castSucc (α := fun _ => IrrGL k) _ _ _
      rw [e, Fin.snoc_castSucc]
      exact hzL i
  have hwd : ∑ a, (w a).1 = x.1 := by
    rw [Fin.sum_univ_castSucc, ← hd, Fin.sum_univ_two, add_comm, ← hz]
    simp [w]
  have hwr : ∑ a, (w (Fin.rev a)).1 = x.1 := (Equiv.sum_comp Fin.revPerm fun a => (w a).1).trans hwd
  have hzr : ∑ a, (z (Fin.rev a)).1 = (y 1).1 := (Equiv.sum_comp Fin.revPerm fun a => (z a).1).trans hz
  obtain ⟨π, hπ⟩ := HS k (𝔫 + {s}) (h + 1) x.1 w hwd hwL
  have hπL : IsL (𝔫 + {s}) π.ρ := ⟨_, w, hwd, hwL, hπ⟩
  have hsoc := HL (𝔫 + {s}) (h + 1) x.1 w hwr hwL π.ρ hπL
  have hsoc₁ := HL 𝔫 h (y 1).1 z hzr ⟨Δ, hΔ, hzL⟩ (y 1).rep hn
  obtain ⟨-, g, hg, -⟩ := hsoc₁
  obtain ⟨F, hF⟩ := embed_family y (w ∘ Fin.rev) (z ∘ Fin.rev)
    (by simp [w, Function.comp]) (fun i => by simp [w, Function.comp, Fin.rev_succ]) hd hwr hzr g hg
  obtain ⟨e⟩ := hsoc.equiv_of_embeds x.2.rep.irr ⟨F.comp f, hF.comp hf⟩
  exact hπL.of_equiv e.symm

end GlobalTheory.CompanionTheory.ExhGood

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsRegEllIffMemEll
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

namespace GlobalTheory.CompanionTheory.NormPoly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem norm_translate {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) :
    (d * u⁻¹) * thE E n (d * u⁻¹) = nrm d := by
  obtain ⟨h1, h2⟩ := hu
  have hθ : thetaE E n u = u⁻¹ := eq_inv_of_mul_eq_one_right h2
  rw [h1, map_mul, map_inv, hθ, inv_inv, nrm]
  group

theorem polE_translate {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) :
    polE (d * u⁻¹) = (nrm d).val.charpoly := by
  rw [polE, norm_translate hu]

theorem map_thetaE (τ : E →+* ℂ) (d : GL (Fin n) E) :
    GeneralLinearGroup.map τ (thetaE E n d) =
      thetaR (starRingEnd ℂ) n (GeneralLinearGroup.map τ d) := by
  apply Units.ext
  ext i j
  have hv : ∀ g : GL (Fin n) E, ((GeneralLinearGroup.map τ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = g.val.map τ := fun _ => rfl
  rw [hv, thetaR_val, thetaR_val, ← map_inv, hv]
  simp only [Matrix.map_apply, Matrix.transpose_apply]
  exact IsCMField.complexEmbedding_complexConj E τ _

theorem charpoly_map_nrm (τ : E →+* ℂ) (d : GL (Fin n) E) :
    (GeneralLinearGroup.map τ d * thetaR (starRingEnd ℂ) n (GeneralLinearGroup.map τ d)).val.charpoly =
      (nrm d).val.charpoly.map τ := by
  rw [← map_thetaE, ← map_mul, ← Matrix.charpoly_map]
  rfl

theorem isRegEll_iff_mem_Ell (d : GL (Fin n) E) : IsRegEll d ↔ (nrm d).val.charpoly ∈ Ell E n := by
  have hm : (nrm d).val.charpoly.Monic := Matrix.charpoly_monic _
  constructor
  · intro h
    refine ⟨hm, by simp, h.1, fun τ z hz => ?_⟩
    exact h.2 τ z (Polynomial.isRoot_of_mem_roots hz)
  · rintro ⟨-, -, hs, hr⟩
    exact ⟨hs, fun τ z hz => hr τ z ((Polynomial.mem_roots (hm.map τ).ne_zero).2 hz)⟩

theorem polEq : PolEq := by
  intro E _ _ _ n u hu d
  rw [polE_translate hu]
  refine ⟨isRegEll_iff_mem_Ell d, fun v => ⟨charpoly_map_nrm v.embedding d, fun h => ?_⟩⟩
  unfold EllC
  rw [charpoly_map_nrm]
  exact ⟨h.1.map, fun z hz => h.2 v.embedding z hz⟩

end GlobalTheory.CompanionTheory.NormPoly
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSubquotientExtTensorRight
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.ProdSubquot
open TensorProduct

section General
variable {G H V V' W W' : Type} [Group G] [Group H]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem isSubquotient_extTensor_left {σ : Representation ℂ G V} {σ' : Representation ℂ G V'}
    (B : Representation ℂ H W) (h : IsSubquotient σ σ') :
    IsSubquotient (extTensor σ B) (extTensor σ' B) := by
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap σ' :=
    { toLinearMap := S.toSubmodule.subtype, isIntertwining' := fun _ => rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  obtain ⟨ι', hι'⟩ := GlobalTheory.ParIndExact.extTensor_injective_left B ι hι
  have hs : Function.Surjective (GlobalTheory.ParIndExact.extTensorMapLeft B f) :=
    LinearMap.rTensor_surjective W hf
  exact (IsSubquotient.of_surjective _ hs).trans (IsSubquotient.of_injective ι' hι')

theorem isSubquotient_extTensor_right {ρ : Representation ℂ H W} {ρ' : Representation ℂ H W'}
    (A : Representation ℂ G V) (h : IsSubquotient ρ ρ') :
    IsSubquotient (extTensor A ρ) (extTensor A ρ') := by
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap ρ' :=
    { toLinearMap := S.toSubmodule.subtype, isIntertwining' := fun _ => rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  obtain ⟨ι', hι'⟩ := GlobalTheory.ParIndExact.extTensor_injective_right A ι hι
  have hs : Function.Surjective (GlobalTheory.ParIndExact.extTensorMapRight A f) :=
    LinearMap.lTensor_surjective V hf
  exact (IsSubquotient.of_surjective _ hs).trans (IsSubquotient.of_injective ι' hι')

theorem isSubquotient_comp {L : Type} [Group L] {σ : Representation ℂ G V}
    {σ' : Representation ℂ G V'} (s : L →* G) (h : IsSubquotient σ σ') :
    IsSubquotient (σ.comp s) (σ'.comp s) := by
  obtain ⟨S, f, hf⟩ := h
  let T : Subrepresentation (σ'.comp s) :=
    ⟨S.toSubmodule, fun x _ hv => S.apply_mem_toSubmodule (s x) hv⟩
  exact ⟨T, ⟨f.toLinearMap, fun x => f.isIntertwining' (s x)⟩, hf⟩

end General

theorem prod₂_isSubquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (U U' W W' : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ (GL (Fin r) k) U) (σ' : Representation ℂ (GL (Fin r) k) U') (ρ : Representation ℂ (GL (Fin t) k) W) (ρ' : Representation ℂ (GL (Fin t) k) W'), IsSmooth σ' → IsSmooth ρ' → IsSubquotient σ σ' → IsSubquotient ρ ρ' → IsSubquotient (prod₂ σ ρ) (prod₂ σ' ρ') := by
  intro k _ _ _ _ r t U U' W W' _ _ _ _ _ _ _ _ σ σ' ρ ρ' hσ' hρ' hs hr
  have hext : IsSubquotient (extTensor σ ρ) (extTensor σ' ρ') :=
    (isSubquotient_extTensor_left ρ hs).trans (isSubquotient_extTensor_right σ' hr)
  have hsm : IsSmooth ((extTensor σ' ρ').comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) :=
    isSmooth_comp (isSmooth_extTensor hσ' hρ') _
      (show Continuous fun g : Levi k (Two (Fin r) (Fin t)) => (g false, g true) from
        (continuous_apply false).prodMk (continuous_apply true))
  exact GlobalTheory.ParIndSubquot.parInd_isSubquotient k _ _ _ _ _ _ _ _ hsm
    (isSubquotient_comp _ hext)

end GlobalTheory.CompanionTheory.ProdSubquot
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetKernelSpanTwistedCharacterStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_kernel_span_twisted_character : ∀ {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H U : Subgroup G) (hUH : U ≤ H) (_ : U.Normal) (θ : U →* ℂˣ) (ι : G' →* G)
    (_ : ∀ (m : G') (n : U), ∃ h : ι m * (n : G) * (ι m)⁻¹ ∈ U, θ ⟨_, h⟩ = θ n)
    (σ : Representation ℂ H W) (q : W →ₗ[ℂ] W'), IsSmooth σ →
    (∀ w, q w = 0 ↔ w ∈ Submodule.span ℂ {y | ∃ (u : U) (v : W), y = σ ⟨u, hUH u.2⟩ v - (θ u : ℂ) • v}) →
    (∀ g : G, (∃ h ∈ H, ∃ x : G', g = h * ι x) ∨
      ∃ u : U, ∃ hx : g * (u : G) * g⁻¹ ∈ H, (∀ w, σ ⟨_, hx⟩ w = w) ∧ θ u ≠ 1) →
    (∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O) →
    ∀ f : cIndSpace H σ, (∀ x, q (f.1.1.1 (ι x)) = 0) → f ∈ twKer (cInd H σ) U θ := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.Kernel.mem_twKer_of_restrict_zero | exact GlobalTheory.CompanionTheory.LeibPhi.Kernel.mem_twKer_of_restrict_zero | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.Kernel.mem_twKer_of_restrict_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductLocalGlobalStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kuenneth_product_local_global : SiteLaws → MVBij → CovDesc → ZarAbs → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q') (V : X.Opens) (d : ℕ), Nonempty (Coord q V d) → ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q V ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q V) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂ := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.Right.kun_right | exact GlobalTheory.CompanionTheory.KunGlue.Right.kun_right | (intros; apply GlobalTheory.CompanionTheory.KunGlue.Right.kun_right <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolicStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_block_mem_parabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (q : Qp k i t), ∃ h : levi k (i + t) (q : GL (Fin (i + t)) k) ∈ HPG k i t, pgProj k i t ⟨_, h⟩ = (levi k i (qBlocks k i t q).1, (qBlocks k i t q).2) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.levi_Qp_mem_pgProj | exact GlobalTheory.CompanionTheory.BZPsiPG.levi_Qp_mem_pgProj | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.levi_Qp_mem_pgProj <;> assumption)
end

