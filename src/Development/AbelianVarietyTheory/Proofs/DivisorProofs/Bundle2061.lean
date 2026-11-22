import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1482
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1950
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1925
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1831
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1757
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1746
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1820
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2050
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2034

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIsClosed
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.LatAtClosed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def intAt (F : Type) [Field F] [NumberField F] (v : Pl F) : AddSubgroup (AF F) where
  carrier := {a | At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F}
  zero_mem' := ⟨fun u _ => by simp, by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun u hu => ?_, ?_⟩
    · rw [smul_add, ha u hu, hb u hu, add_zero]
    · rw [map_add]; exact add_mem ha' hb'
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨fun u hu => ?_, ?_⟩
    · rw [smul_neg, ha u hu, neg_zero]
    · rw [map_neg]; exact neg_mem ha'

theorem continuous_evFin' (v : Pl F) : Continuous (evFin F v) :=
  (RestrictedProduct.continuous_eval v).comp continuous_snd

theorem continuous_liftV (v : Pl F) : Continuous (GlobalTheory.LatVac.liftV v) := by
  show Continuous fun x => ((0 : Ainf F), singleFin v x)
  exact continuous_const.prodMk (continuous_singleFin v)

theorem isClosed_intAt (v : Pl F) : IsClosed (intAt F v : Set (AF F)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have h1 : IsClosed {a : AF F | At (evFin F v) a} := by
    have : {a : AF F | At (evFin F v) a} = ⋂ u : AF F, ⋂ (_ : evFin F v u = 0), {a | u • a = 0} := by
      ext a; simp [At]
    rw [this]
    exact isClosed_iInter fun u => isClosed_iInter fun _ =>
      isClosed_eq (continuous_const.mul continuous_id) continuous_const
  have h2 : IsClosed {a : AF F | evFin F v a ∈ v.adicCompletionIntegers F} :=
    (GroundTheory.Global.isClosed_adicCompletionIntegers v).preimage (continuous_evFin' v)
  exact h1.inter h2

theorem isCompact_intAt (v : Pl F) : IsCompact (intAt F v : Set (AF F)) := by
  refine ((PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).image (continuous_liftV v)).of_isClosed_subset
    (isClosed_intAt v) ?_
  rintro a ⟨ha, ha'⟩
  refine ⟨evFin F v a, ha', ?_⟩
  rw [← GlobalTheory.ThK.LocalOps.liftV_one_mul]
  have := GlobalTheory.ThK.partFin_of_at (M := AF F) (v := v) ha
  exact this

theorem isCompact_latAt {d : ℕ} (W : Spc F E d) (hL : W.L.IsLattice E) (v : Pl F) :
    IsCompact ((GlobalTheory.InertSph.latAt W v : AddSubgroup (Fin d → AE F E)) : Set (Fin d → AE F E)) := by
  have hZ : (W.L.restrictScalars ℤ).FG := hL.fg.restrictScalars
  obtain ⟨m, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hZ
  have hxL : ∀ k, x k ∈ W.L := fun k => by
    have : x k ∈ Submodule.span ℤ (Set.range x) := Submodule.subset_span ⟨k, rfl⟩
    rw [hx] at this; exact this
  let g : (Fin m → AF F) → Fin d → AE F E := fun c => ∑ k, c k • fun i => inclR (F := F) (AF F) (x k i)
  have hg : Continuous g :=
    continuous_finset_sum _ fun k _ => by
      have hk : Continuous fun c : Fin m → AF F => c k := continuous_apply k
      exact hk.smul (continuous_const (y := fun i => inclR (F := F) (AF F) (x k i)))
  have heq : ((GlobalTheory.InertSph.latAt W v : AddSubgroup (Fin d → AE F E)) : Set (Fin d → AE F E)) =
      g '' Set.pi Set.univ fun _ => (intAt F v : Set (AF F)) := by
    ext z
    constructor
    · intro hz
      induction hz using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, ha, ha', y, hy, rfl⟩ := hy
        have hy' : y ∈ Submodule.span ℤ (Set.range x) := by rw [hx]; exact hy
        obtain ⟨n, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy'
        refine ⟨fun k => n k • a, fun k _ => zsmul_mem (show a ∈ intAt F v from ⟨ha, ha'⟩) _, ?_⟩
        funext i
        simp only [g, Finset.sum_apply, Pi.smul_apply, map_sum, map_zsmul, Finset.smul_sum, smul_comm a, smul_assoc]
      | zero => exact ⟨0, fun k _ => zero_mem _, by simp [g]⟩
      | add y z _ _ hy hz =>
        obtain ⟨c, hc, rfl⟩ := hy
        obtain ⟨c', hc', rfl⟩ := hz
        exact ⟨c + c', fun k _ => add_mem (hc k trivial) (hc' k trivial), by
          simp only [g, Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
      | neg y _ hy =>
        obtain ⟨c, hc, rfl⟩ := hy
        exact ⟨-c, fun k _ => neg_mem (hc k trivial), by
          simp only [g, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]⟩
    · rintro ⟨c, hc, rfl⟩
      refine sum_mem fun k _ => AddSubgroup.subset_closure ⟨c k, (hc k trivial).1, (hc k trivial).2, x k, hxL k, rfl⟩
  rw [heq]
  exact (isCompact_univ_pi fun _ => isCompact_intAt v).image hg

theorem isClosed_latAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ)
    (W : Spc F E d), W.L.IsLattice E → ∀ v : Pl F,
    IsClosed ((GlobalTheory.InertSph.latAt W v : AddSubgroup (Fin d → AE F E)) : Set (Fin d → AE F E)) := by
  intro F E _ _ _ _ _ d W hL v
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : T2Space (AE F E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  exact (isCompact_latAt W hL v).isClosed

end GlobalTheory.LatAtClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMomentSurjective
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LagrCoord

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have hD : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  intro h0
  apply hD
  rw [← hA, ← Matrix.det_submatrix_equiv_self e.symm,
    Matrix.submatrix_mul _ _ e.symm (id : Fin n → Fin n) e.symm Function.bijective_id,
    Matrix.submatrix_mul _ _ e.symm (id : Fin n → Fin n) id Function.bijective_id,
    Matrix.det_mul, Matrix.det_mul, Matrix.submatrix_id_id, h0, mul_zero, zero_mul]

theorem det_ne_zero_of_hasSig_smul {n r s : ℕ} {c : ℂ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig (c • M) r s) :
    M.det ≠ 0 := by
  intro h0
  apply det_ne_zero_of_hasSig h
  rw [Matrix.det_smul, h0, mul_zero]

theorem det_ne_zero_of_map {E : Type} [CommRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ)
    (h : (J.map f).det ≠ 0) : J.det ≠ 0 := by
  intro h0
  apply h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem exists_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (Y : Matrix (Fin n) (Fin d) (Fv F v)), ∃ x : Matrix (Fin n) (Fin d) (AE F E),
      At (evFin F v) x ∧ x.map (piW t) = 0 ∧ -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) = Y := by
  intro F E _ _ _ _ _ σ B hB n d r s r' s' X W hX hW v t Y
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hXd : X.J.det ≠ 0 := det_ne_zero_of_map X.J (B.emb w).1 (det_ne_zero_of_hasSig (hX.sig w))
  have hWd : W.J.det ≠ 0 := det_ne_zero_of_map W.J (B.emb w).1 (det_ne_zero_of_hasSig_smul (hW.sig w))
  have ht : Function.Injective t := t.toRingHom.injective
  have hXt : IsUnit (X.J.map t).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hXd
    apply ht
    rw [map_zero, ← h0]
    exact (RingHom.map_det t.toRingHom X.J)
  have hWt : IsUnit ((W.J.map t)ᵀ).det := by
    rw [Matrix.det_transpose, isUnit_iff_ne_zero]
    intro h0
    apply hWd
    apply ht
    rw [map_zero, ← h0]
    exact (RingHom.map_det t.toRingHom W.J)
  obtain ⟨x, hxat, hx0, hx1⟩ := GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hB.cm v t (0 : Matrix (Fin n) (Fin d) (Fv F v))
    (-((X.J.map t)⁻¹ * Y * ((W.J.map t)ᵀ)⁻¹))
  refine ⟨x, hxat, hx0, ?_⟩
  rw [hx1]
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hWt, Matrix.mul_one,
    Matrix.mul_nonsing_inv_cancel_left _ _ hXt]

end GlobalTheory.LagrCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMomentSurjectiveConj
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.OppLinChar

open scoped TensorProduct
open GlobalTheory.EmbChart (atPlace tensAt compFin_tensAt tensAt_mul_right atPlace_mul_right evFin_atPlace)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_tmul' [FiniteDimensional F E] {R : Type} [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem evFin_trace [FiniteDimensional F E] (v : Pl F) (z : AE F E) :
    evFin F v (Algebra.trace (AF F) (AE F E) z) =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | tmul a x =>
    have e : compFin F E v (a ⊗ₜ[F] x) = evFin F v a ⊗ₜ[F] x := rfl
    rw [e, trace_tmul', trace_tmul', map_mul, AlgHom.commutes]

theorem trace_split {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl F} (t : E →ₐ[F] Fv F v) (y : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y = splitProj t y + splitProj (t.comp σ) y := by
  rw [← Algebra.trace_eq_of_algEquiv (splitAlgEquiv h t) y, Algebra.trace_prod_apply, splitAlgEquiv_apply]
  simp [Algebra.trace_self_apply]

theorem piW_cA {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl F} (t : E →ₐ[F] Fv F v) (y : AE F E) :
    piW (t.comp σ) (cA σ y) = piW t y := by
  have e : compFin F E v (cA σ y) = sigR (Fv F v) σ (compFin F E v y) := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x => rfl
  change splitProj (t.comp σ) (compFin F E v (cA σ y)) = splitProj t (compFin F E v y)
  rw [e]
  exact splitProj_comp_sigR h t _

theorem piW_inclR {v : Pl F} (t : E →ₐ[F] Fv F v) (x : E) : piW t (inclR (AF F) x) = t x := by
  change splitProj t (evFin F v 1 ⊗ₜ[F] x) = t x
  rw [map_one]
  exact splitProj_inclR t x

theorem piW_tensAt {v : Pl F} (t : E →ₐ[F] Fv F v) (y : Fv F v ⊗[F] E) : piW t (tensAt E v y) = splitProj t y := by
  change splitProj t (compFin F E v (tensAt E v y)) = _
  rw [compFin_tensAt]

theorem at_tensAt {v : Pl F} (y : Fv F v ⊗[F] E) : At (evFin F v) (tensAt E v y) := by
  intro a ha
  rw [Algebra.smul_def, mul_comm, tensAt_mul_right]
  have : compFin F E v (algebraMap (AF F) (AE F E) a) = 0 := by
    change evFin F v a ⊗ₜ[F] (1 : E) = 0
    rw [ha, TensorProduct.zero_tmul]
  rw [this, mul_zero, map_zero]

theorem eq_liftV_of_at {v : Pl F} {a : AF F} (ha : At (evFin F v) a) : a = GlobalTheory.LatVac.liftV v (evFin F v a) := by
  have h1 : evFin F v (1 - atPlace v 1) = 0 := by rw [map_sub, map_one, evFin_atPlace, sub_self]
  have h2 := ha _ h1
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h2
  calc a = atPlace v 1 * a := h2
    _ = atPlace v (1 * evFin F v a) := atPlace_mul_right v 1 a
    _ = GlobalTheory.LatVac.liftV v (evFin F v a) := by rw [one_mul]; rfl

end GlobalTheory.OppLinChar

namespace GlobalTheory.OppLinChar

open scoped TensorProduct
open GlobalTheory.EmbChart (tensAt)

theorem char_eq_psi_symp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (Z : Matrix (Fin n) (Fin d) (Fv F v)), ∃ u : Matrix (Fin n) (Fin d) (AE F E),
      At (evFin F v) u ∧ u.map (piW (t.comp σ)) = 0 ∧ ∀ x : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x →
        x.map (piW t) = 0 → B.ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u) =
          GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, (-((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1)) i j * Z i j) := by
  intro F E _ _ _ _ _ σ B hB n d r s r' s' X W hX hW v t Z
  have h := hB.cm
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h.2.2.1
  refine ⟨Matrix.of fun k l => tensAt E v ((splitAlgEquiv h t).symm (-Z k l, 0)), ?_, ?_, ?_⟩
  · intro a ha
    ext k l
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]
    exact at_tensAt _ a ha
  · ext k l
    simp [piW_tensAt]
  · intro x hxv hx
    set u : Matrix (Fin n) (Fin d) (AE F E) := Matrix.of fun k l => tensAt E v ((splitAlgEquiv h t).symm (-Z k l, 0))
      with hu_def
    have hx' : ∀ i j, piW t (x i j) = 0 := fun i j => by simpa using congrFun (congrFun hx i) j
    have hJX : ∀ i k, piW (t.comp σ) (incM F X.J i k) = t (X.J k i) := fun i k => by
      rw [incM, Matrix.map_apply, piW_inclR, AlgHom.comp_apply, hX.herm]
    have hJW : ∀ j l, piW (t.comp σ) (incM F W.J j l) = -t (W.J l j) := fun j l => by
      rw [incM, Matrix.map_apply, piW_inclR, AlgHom.comp_apply, hW.skew, map_neg]
    have hu : ∀ k l, piW (t.comp σ) (cA σ (u k l)) = -Z k l := fun k l => by
      rw [piW_cA h, hu_def, Matrix.of_apply, piW_tensAt, splitProj_symm]
    set S := symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u with hS_def
    have hat : At (evFin F v) S := by
      intro a ha
      rw [smul_eq_mul, ← one_mul S, ← mul_assoc, hS_def, ← GlobalTheory.LatVac.symp_smul_smul]
      have h0 : a • x = 0 := hxv a ha
      rw [h0]
      simp [GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens]
    have hev : evFin F v S = ∑ i, ∑ j, (-((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) *
        (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1)) i j * Z i j := by
      rw [hS_def, GlobalTheory.WeilM.symp, evFin_trace, trace_split h t]
      change piW t _ + piW (t.comp σ) _ = _
      simp only [GlobalTheory.WeilM.hTens, map_mul, map_neg, map_one, map_sum, hx', hJX, hJW, hu]
      have key : ∀ (f : Fin n → Fin d → Fin n → Fin d → Fv F v),
          ∑ a, ∑ b, ∑ i, ∑ j, f a b i j = ∑ i, ∑ j, ∑ b, ∑ a, f a b i j := by
        intro f
        calc ∑ a, ∑ b, ∑ i, ∑ j, f a b i j = ∑ a, ∑ i, ∑ j, ∑ b, f a b i j := by
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
          _ = ∑ i, ∑ j, ∑ b, ∑ a, f a b i j := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
      simp only [zero_mul, Finset.sum_const_zero, mul_zero, zero_add, Units.val_one, Matrix.transpose_one,
        Matrix.one_mul, Matrix.mul_one, Matrix.neg_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
      simp only [Finset.mul_sum, Finset.sum_mul, neg_mul, ← Finset.sum_neg_distrib]
      refine (key _).trans ?_
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
      ring
    change B.ψ S = B.ψ (GlobalTheory.LatVac.liftV v _)
    rw [← hev, ← eq_liftV_of_at hat]

end GlobalTheory.OppLinChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Div.CoordOpp

theorem piW_inclR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : Pl F} (t : E →ₐ[F] Fv F v) (e : E) :
    piW t (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F) e) = t e := by
  have h1 : compFin F E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F) e) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Fv F v) e := by
    simp [compFin, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
  simp only [piW, RingHom.comp_apply, h1]
  exact splitProj_inclR t e

theorem piW_cA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {v : Pl F} (t : E →ₐ[F] Fv F v) (z : AE F E) :
    piW t (cA σ z) = piW (t.comp σ) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [piW, cA, compFin, splitProj]
  | add x y hx hy => simp [map_add, hx, hy]

theorem incM_map_piW {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : Pl F} (t : E →ₐ[F] Fv F v) {m k : Type} (J : Matrix m k E) :
    (incM F J).map (piW t) = J.map t := by
  ext i j
  simp [incM, piW_inclR]

theorem unit_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    ((mat g).map (piW t))ᵀ * J.map t * (mat g).map (piW (t.comp σ)) = J.map t := by
  have hg := g.2
  change ((mat g))ᵀ * incM F J * (mat g).map (cA σ) = incM F J at hg
  have := congrArg (fun M => M.map (piW t)) hg
  simp only [Matrix.map_mul, Matrix.transpose_map, incM_map_piW] at this
  have e2 : ((mat g).map (cA σ)).map (piW t) = (mat g).map (piW (t.comp σ)) := by
    ext i j; simp [piW_cA]
  rw [e2] at this
  simpa [Matrix.transpose_map] using this

end GlobalTheory.Div.CoordOpp

open GlobalTheory.Div.CoordOpp in
theorem GlobalTheory.Div.CoordOpp.coord_opp_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (v : Pl F) (t : E →ₐ[F] Fv F v) (g : UA σ X.J) (h : UA σ W.J)
    (x : Matrix (Fin n) (Fin d) (AE F E)),
    ((mat g).map (piW t))ᵀ * -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (mat g * x * (mat h)ᵀ).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) * (mat h).map (piW t) = -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) := by
  intro F E _ _ _ _ _ σ n d X W v t g h x
  have hg := unit_map σ g t
  have hh := unit_map σ h t
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.map_mul,
    Matrix.transpose_map, Matrix.mul_neg, Matrix.neg_mul, neg_inj]
  set gt := (mat g).map (piW t)
  set gb := (mat g).map (piW (t.comp σ))
  set ht := (mat h).map (piW t)
  set hb := (mat h).map (piW (t.comp σ))
  set xb := x.map (piW (t.comp σ))
  have hh' : hbᵀ * (W.J.map t)ᵀ * ht = (W.J.map t)ᵀ := by
    have := congrArg Matrix.transpose hh
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  calc gtᵀ * (X.J.map t * (gb * xb * ((mat h)ᵀ).map (piW (t.comp σ))) * (W.J.map t)ᵀ) * ht
      = (gtᵀ * X.J.map t * gb) * xb * (hbᵀ * (W.J.map t)ᵀ * ht) := by
        simp only [hb, Matrix.transpose_map, Matrix.mul_assoc]
    _ = X.J.map t * xb * (W.J.map t)ᵀ := by rw [hg, hh']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureHeightShellLeIsotropicFrameQuotient
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

theorem measure_shell_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ (μ : Measure (GAd σ J)) (D : Set (GAd σ J)), μ.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) : Subgroup (GAd σ J)) D μ → ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ j : ℕ, μ.restrict D {x | Real.exp (-(j + 1 : ℝ)) < h x ∧ h x ≤ Real.exp (-(j : ℝ))} ≤ B * ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hD μ D hμ hFD
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_leviCentreFlow_wittFrame F E σ n J r X Y hD.cm hD.herm hD.witt
  obtain ⟨-, hHt, hlaw⟩ := GlobalTheory.T.isCompact_level_height_scales_isotropicFrame F E σ n J r X Y L a h hD
  obtain ⟨-, ν, DN, hν, hDN, hone⟩ := unipRad_frame_closed_mass_one F E σ n J r X Y hD.cm hD.herm hD.witt
  have hmod := GlobalTheory.T.leviCentreFlow_conj_scales_haar_isotropicUnipotent F E σ n J r X Y hD.cm hD.herm hD.witt b hb ν hν
  obtain ⟨π, DM, hSL⟩ := GlobalTheory.T.rational_isotropicStabiliser_splitLattice F E σ n J r X Y hD.cm hD.herm hD.witt ν DN hν hDN hone
  obtain ⟨C, hC, hslab⟩ := GlobalTheory.T.heightSlab_subset_unipotent_levi_compact F E σ n J r X Y L a h hD b hb
  haveI : Countable (ratPts σ J) := inferInstance
  haveI : Countable ((ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) : Subgroup (GAd σ J)) :=
    Function.Injective.countable (Subgroup.inclusion_injective
      (inf_le_left : ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤ ≤ ratPts σ J))
  obtain ⟨B, hB, hsh⟩ := GlobalTheory.ResLine.modulus_mul_measure_shell_le (GAd σ J) _ _ _ ν π DN DM hSL μ D hμ hFD C hC
  refine ⟨B, hB, fun j => ?_⟩
  have hS : MeasurableSet {x | Real.exp (-(j + 1 : ℝ)) < h x ∧ h x ≤ Real.exp (-(j : ℝ))} :=
    (measurableSet_Ioc (a := Real.exp (-(j + 1 : ℝ))) (b := Real.exp (-(j : ℝ)))).preimage hHt.cont.measurable
  have key := hsh (b j) _ (fun m hm => hb.comm j m (Subgroup.mem_inf.mp hm).1) (hmod j) _ hS (fun x hx => by
    obtain ⟨β, hβ, e⟩ := hb.onX j
    have e2 : h (b j * x) = Real.exp j * h x := by rw [hlaw _ β hβ, e]
    have hp : 0 < Real.exp (j : ℝ) := Real.exp_pos _
    refine hslab _ ?_ ?_
    · rw [e2]
      have : Real.exp (-1) = Real.exp j * Real.exp (-(j + 1 : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hx.1.le hp.le
    · rw [e2]
      have : (1 : ℝ) = Real.exp j * Real.exp (-(j : ℝ)) := by rw [← Real.exp_add]; simp
      rw [this]
      exact mul_le_mul_of_nonneg_left hx.2 hp.le)
  rw [Measure.restrict_apply hS]
  have e1 : ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) * ENNReal.ofReal (Real.exp (-(((n : ℝ) - (r + 1)) * j))) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; simp
  calc _ = ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) * (ENNReal.ofReal (Real.exp (-(((n : ℝ) - (r + 1)) * j))) * _) := by
        rw [← mul_assoc, e1, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) * B := by gcongr
    _ = _ := mul_comm _ _

end GlobalTheory.ResidueEisenstein
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIdealIntegralFiniteAdelesOfMemCompletionStatement
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_idealIntegralFiniteAdeles_of_memCompletion : ∀ {D : D7} (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ x : Formalism.MainNotions.StandardLatticesGL3.AE D,
  InHat (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (GlobalTheory.BotFormula.toFinE D x) → x ∈ hatId D 𝔪 := by
  first | exact @GlobalTheory.CosetOrth.mem_hatId_of_inHat | exact GlobalTheory.CosetOrth.mem_hatId_of_inHat | (intros; apply GlobalTheory.CosetOrth.mem_hatId_of_inHat <;> assumption)
end

