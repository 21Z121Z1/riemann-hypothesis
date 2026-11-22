import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoAverageL2Compact
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0207
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0179
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0131
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0081
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0180
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0075
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0103
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0126
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0199
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0053
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoAverageL2CompactStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_average_L2_compact : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → ∀ {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (g : Mt k r → Wp), (∀ K : Set (Mt k r), IsCompact K → AEStronglyMeasurable g (μ.restrict K) ∧ ∫⁻ x in K, (‖g x‖₊ : ENNReal) ^ 2 ∂μ < ⊤) → ∀ K : Set (Mt k r), IsCompact K → Filter.Tendsto (fun j : ℕ => ∫⁻ x in K, (‖avgR μ j g x - g x‖₊ : ENNReal) ^ 2 ∂μ) Filter.atTop (nhds 0) := by
  first | exact @GlobalTheory.SgInf.tendsto_average_L2 | exact GlobalTheory.SgInf.tendsto_average_L2 | (intros; apply GlobalTheory.SgInf.tendsto_average_L2 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceFormDualTranslatedLatticeEqInverseTransposeStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceFormDual_translatedLattice_eq_inverseTranspose : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsLattice E Λ → ∀ g : MatInf E j, 0 < detNorm E j g → dualAt E j (latAt E j Λ g) = latAt E j (trDual E j Λ) (invT E j g) := by
  first | exact @GlobalTheory.MeanDual.dualAt_latAt_eq_latAt_trDual | exact GlobalTheory.MeanDual.dualAt_latAt_eq_latAt_trDual | (intros; apply GlobalTheory.MeanDual.dualAt_latAt_eq_latAt_trDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrivialModChosenPrimesIffMemKg
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

open Inhab GlobalTheory.Mem.RowsBundle

theorem hAf_add_left (I : AutInst) (x x' y : Fin I.n → (I.E ⊗[I.F] Af I.F)) :
    hAf I (x + x') y = hAf I x y + hAf I x' y := by
  unfold hAf Formalism.UG.hform
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hAf_smul_left (I : AutInst) (a : I.E ⊗[I.F] Af I.F) (x y : Fin I.n → (I.E ⊗[I.F] Af I.F)) :
    hAf I (a • x) y = Formalism.UG.sigR I.cm.sig (Af I.F) a * hAf I x y := by
  unfold hAf Formalism.UG.hform
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

theorem mapsTo_conj_of_adjoint (I : AutInst) (w w' : HeightOneSpectrum (𝓞 I.E))
    (T T' : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (hc : IsConj I w w')
    (hadj : ∀ x y, hAf I (T' *ᵥ x) y = hAf I x (T *ᵥ y))
    (hT' : ∀ y ∈ I.Lf, T' *ᵥ y ∈ extId I w.asIdeal • I.Lf) :
    ∀ y ∈ I.Lf, T *ᵥ y ∈ extId I w'.asIdeal • I.Lf := by
  intro y hy
  rw [DualIdeal.mem_extId_smul_iff I _ w'.ne_bot]
  intro y' hy'
  rw [← hadj]
  have key : ∀ u ∈ extId I w.asIdeal • I.Lf, ∃ z ∈ extId I w'.asIdeal,
      (z : I.E ⊗[I.F] Af I.F) = hAf I u y := by
    intro u hu
    refine Submodule.smul_induction_on hu (fun a ha l hl => ?_) (fun u u' hu hu' => ?_)
    · obtain ⟨a', ha', e⟩ := (extId_mul_sup_natCast_conj I).2.2.2.2.2.2 w w' hc a ha
      refine ⟨a' * ⟨_, (GlobalTheory.AdelicLattice.adelicLattice_selfDual I y).1 hy l hl⟩, Ideal.mul_mem_right _ _ ha', ?_⟩
      rw [Subring.coe_mul, e]
      show _ = hAf I ((a : I.E ⊗[I.F] Af I.F) • l) y
      rw [hAf_smul_left]
    · obtain ⟨z, hz, e⟩ := hu
      obtain ⟨z', hz', e'⟩ := hu'
      exact ⟨z + z', add_mem hz hz', by rw [Subring.coe_add, e, e', hAf_add_left]⟩
  exact key _ (hT' y' hy')

theorem PlFrame.trivial_iff {I : AutInst} {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w)
    {x : I.Gf} (hx : x ∈ I.Kset) :
    (∀ (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf), fr.c ⟨_, h⟩ = fr.c y) ↔
      ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ extId I w.asIdeal • I.Lf := by
  have key : ∀ (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf), fr.c ⟨_, h⟩ = fr.c y ↔
      (I.fmat x - 1) *ᵥ (y : Fin I.n → _) ∈ extId I w.asIdeal • I.Lf := by
    intro y h
    rw [← sub_eq_zero, ← map_sub, fr.c_ker, Matrix.sub_mulVec, Matrix.one_mulVec]
    rfl
  exact ⟨fun H y hy => (key ⟨y, hy⟩ (mulVec_mem hx hy)).1 (H _ _), fun H y h => (key y h).2 (H y.1 y.2)⟩

theorem IsChoice.isRadical_mul {I : AutInst} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
    {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} (hC : IsChoice I g Pl w) :
    (Ideal.span {((g 0 * g 1 : ℕ) : 𝓞 I.E)}).IsRadical := by
  have hc : Nat.Coprime (g 0) (g 1) := (Nat.coprime_primes (hC.1 0) (hC.1 1)).2 hC.2.1
  have hc' : IsCoprime ((g 0 : ℕ) : 𝓞 I.E) ((g 1 : ℕ) : 𝓞 I.E) := Nat.Coprime.cast hc
  rw [Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton,
    Ideal.mul_eq_inf_of_isCoprime ((Ideal.isCoprime_span_singleton_iff _ _).2 hc')]
  exact (hC.2.2.1 0).inf (hC.2.2.1 1)

theorem trivial_iff_mem_Kg : ∀ (I : AutInst) (N : ℕ) (g : Fin 2 → ℕ) (Pl : Fin 2 → Type)
    (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)) (fr : ∀ k v, PlFrame I N (g k) (w k v)), I.n = N →
    IsChoice I g Pl w → ∀ x ∈ I.Kset, (∀ k v (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf),
      (fr k v).c ⟨_, h⟩ = (fr k v).c y) ↔ x ∈ I.Kg (g 0 * g 1) := by
  intro I N g Pl w fr _ hC x hx
  have hx' : x⁻¹ ∈ I.Kset := (Ksub I).inv_mem hx
  have hone : 1 ≤ g 0 * g 1 := Nat.mul_pos (hC.1 0).pos (hC.1 1).pos
  have hmem : ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ I.Lf := fun y hy => by
    simpa using sub_one_pow_mem hx 1 hy
  have crt := fun y hy => GlobalTheory.RowLev.SqfCrt.mem_extId_smul_forall_iff I (g 0 * g 1) hone hC.isRadical_mul _ (hmem y hy)
  constructor
  · intro H
    have H1 := fun k v => ((fr k v).trivial_iff hx).1 (H k v)
    have H2 : ∀ k v, ∀ y ∈ I.Lf, (I.fmat x⁻¹ - 1) *ᵥ y ∈ extId I (w k v).asIdeal • I.Lf := by
      intro k v y hy
      have h1 : I.fmat x * I.fmat x⁻¹ = 1 := by rw [← fmat_mul, mul_inv_cancel, fmat_one]
      have h := neg_mem (H1 k v _ (mulVec_mem hx' hy))
      rw [Matrix.mulVec_mulVec, sub_mul, h1, one_mul, ← Matrix.neg_mulVec, neg_sub] at h
      exact h
    refine ⟨hx, fun y hy => (crt y hy).1 fun u hu => ?_⟩
    have hk : ∃ k, ((g k : ℕ) : 𝓞 I.E) ∈ u.asIdeal := by
      rw [Nat.cast_mul] at hu
      exact (u.isPrime.mem_or_mem hu).elim (fun h => ⟨0, h⟩) fun h => ⟨1, h⟩
    obtain ⟨k, hk⟩ := hk
    obtain ⟨v, rfl | hv⟩ := hC.2.2.2.2.2.2 k u hk
    · exact H1 k v y hy
    · refine mapsTo_conj_of_adjoint I _ _ _ _ hv (fun a b => ?_) (H2 k v) y hy
      simpa only [pow_one] using hAf_pow_adjoint x 1 a b
  · intro H k v
    refine ((fr k v).trivial_iff hx).2 fun y hy => (crt y hy).2 (H.2 y hy) _ ?_
    have h := (hC.2.2.2.1 k v).1
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ h
    · exact Ideal.mul_mem_left _ _ h

end GlobalTheory.RowLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizePos
section
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

noncomputable section

namespace GlobalTheory.RationalCount

abbrev op {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)

theorem norm_op_conj_le {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ‖op (g.map (starRingEnd ℂ))‖ ≤ ‖op g‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
  let u' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 fun i => starRingEnd ℂ (u i)
  have h1 : ‖u'‖ = ‖u‖ := by simp [u', EuclideanSpace.norm_eq]
  have h2 : ‖op (g.map (starRingEnd ℂ)) u‖ = ‖op g u'‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have : op (g.map (starRingEnd ℂ)) u i = starRingEnd ℂ (op g u' i) := by
      simp [op, u', Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct]
    rw [this, RCLike.norm_conj]
  rw [h2, ← h1]
  exact (op g).le_opNorm u'

theorem norm_op_conj {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ‖op (g.map (starRingEnd ℂ))‖ = ‖op g‖ := by
  refine le_antisymm (norm_op_conj_le g) ?_
  have h := norm_op_conj_le (g.map (starRingEnd ℂ))
  have e : (g.map (starRingEnd ℂ)).map (starRingEnd ℂ) = g := by ext i j; simp
  rwa [e] at h

theorem finrank_op (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) = 2 * n ^ 2 := by
  rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    ← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin n))
      (F' := EuclideanSpace ℂ (Fin n))).finrank_eq, Module.finrank_linearMap]
  simp [sq]

variable (I : AutInst)

theorem comap_bijective :
    Function.Bijective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) := by
  have key : ∀ w : InfinitePlace I.E, w = InfinitePlace.mk (I.φ (w.comap (algebraMap I.F I.E))) := by
    intro w
    rcases GlobalTheory.Count.Test.embedding_cases I w with h | h
    · rw [← h, InfinitePlace.mk_embedding]
    · rw [← InfinitePlace.mk_conjugate_eq, ← h, InfinitePlace.mk_embedding]
  refine ⟨fun w w' h => ?_, InfinitePlace.comap_surjective⟩
  rw [key w, key w']
  exact congrArg (fun v => InfinitePlace.mk (I.φ v)) h

theorem card_places : Fintype.card (InfinitePlace I.F) = I.f := by
  have hR := I.cm.totReal
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, AutInst.f, IsTotallyReal.finrank,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]

theorem opNormAt_eq (x y : I.GA) (δ : Matrix (Fin I.n) (Fin I.n) I.E) (w : InfinitePlace I.E) :
    opNormAt (bas I) (frm I y) (bas I) (frm I x) w (Matrix.toLin' δ) =
      ‖op ((I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ *
        δ.map (I.φ (w.comap (algebraMap I.F I.E))) *
        (I.P (w.comap (algebraMap I.F I.E)) * uMat (y.1 (w.comap (algebraMap I.F I.E)))))‖ := by
  have e : LinearMap.toMatrix (bas I) (bas I) (Matrix.toLin' δ) = δ := by simp [bas]
  unfold opNormAt frm
  rw [e]
  split_ifs with h
  · rw [h]
  · have h' := (GlobalTheory.Count.Test.embedding_cases I w).resolve_left h
    set v := w.comap (algebraMap I.F I.E)
    have hu : IsUnit (I.P v * uMat (x.1 v)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 ((I.P_unit v).mul (Units.isUnit _))
    have hJ : δ.map w.embedding = (δ.map (I.φ v)).map (starRingEnd ℂ) := by
      rw [h']; rfl
    have hi : ((I.P v * uMat (x.1 v)).map (starRingEnd ℂ))⁻¹ = (I.P v * uMat (x.1 v))⁻¹.map (starRingEnd ℂ) := by
      refine Matrix.inv_eq_left_inv ?_
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu]
      simp [Matrix.map_one]
    rw [hJ, hi, ← Matrix.map_mul, ← Matrix.map_mul]
    exact norm_op_conj _

theorem uMat_eq (x y a : I.GA) (γ : Matrix (Fin I.n) (Fin I.n) I.E) (v : InfinitePlace I.F)
    (h : uMat (a.1 v) = (I.P v)⁻¹ * γ.map (I.φ v) * I.P v) :
    uMat ((x⁻¹ * a * y).1 v) = (I.P v * uMat (x.1 v))⁻¹ * γ.map (I.φ v) * (I.P v * uMat (y.1 v)) := by
  have e : uMat ((x⁻¹ * a * y).1 v) = (uMat (x.1 v))⁻¹ * uMat (a.1 v) * uMat (y.1 v) := by
    simp [uMat]
  rw [e, h, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

theorem mulVec_mem (x y a : I.GA) (γ : GL (Fin I.n) I.E)
    (h : I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)))
    (hK : (x⁻¹ * a * y).2 ∈ I.Kset) (z : Fin I.n → I.E) (hz : z ∈ lamX I y) :
    (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z ∈ lamX I x := by
  have h1 := (GlobalTheory.Count.Test.lamX_equivariant I a y γ h z).2 hz
  rw [GlobalTheory.Count.Test.mem_lamX] at h1 ⊢
  have h2 := (hK _).1 h1
  have h3 : I.fmat (x⁻¹ * a * y).2 * I.fmat (a * y).2⁻¹ = I.fmat x.2⁻¹ := by
    have : (x⁻¹ * a * y).2 * (a * y).2⁻¹ = x.2⁻¹ := by simp [mul_assoc]
    rw [← this]; rfl
  rw [Matrix.mulVec_mulVec] at h2
  rw [← h3]
  exact h2

theorem lamX_ne_bot (hn : 1 ≤ I.n) (x : I.GA) : lamX I x ≠ ⊥ := by
  intro h0
  have h1 := (GlobalTheory.NearLowerCompare.lamX_isLattice I x).span_eq_top
  rw [h0] at h1
  have : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩
  simp at h1

theorem truncatedLeastLatticeSize_pos (hn : 1 ≤ I.n) (x : I.GA) : 0 < tau1 I x :=
  lt_min (by norm_num) (GlobalTheory.StepDualityCompare.least_pos I x
    (GlobalTheory.NearLowerCompare.lamX_isLattice I x).fg (lamX_ne_bot I hn x))

theorem separated (hn : 1 ≤ I.n) (x y a b : I.GA) (ha : a ∈ I.GFset) (hb : b ∈ I.GFset)
    (haK : (x⁻¹ * a * y).2 ∈ I.Kset) (hbK : (x⁻¹ * b * y).2 ∈ I.Kset) (hab : a ≠ b) :
    tau1 I x * tau1 I y ≤ (∏ v, ‖op (uMat ((x⁻¹ * a * y).1 v)) - op (uMat ((x⁻¹ * b * y).1 v))‖) ^
      ((1 : ℝ) / Fintype.card (InfinitePlace I.F)) := by
  have : IsTotallyComplex I.E := I.cm.cmUnram.1
  obtain ⟨γ, -, hγ1, hγ2⟩ := ha
  obtain ⟨η, -, hη1, hη2⟩ := hb
  have hne : (γ : Matrix (Fin I.n) (Fin I.n) I.E) - η ≠ 0 := by
    intro h
    have h' : (γ : Matrix (Fin I.n) (Fin I.n) I.E) = η := sub_eq_zero.1 h
    refine hab (Prod.ext (funext fun v => Subtype.ext (Units.ext ?_)) (Subtype.ext (Units.ext ?_)))
    · exact (hγ1 v).trans (h' ▸ (hη1 v).symm)
    · exact hγ2.trans (h' ▸ hη2.symm)
  have hx := GlobalTheory.NearLowerCompare.lamX_isLattice I x
  have hy := GlobalTheory.NearLowerCompare.lamX_isLattice I y
  have h := sizeIneq I.E _ _ _ _ (bas I) (frm I y) (bas I) (frm I x)
    (GlobalTheory.NearLowerCompare.frm_isUnit I y) (GlobalTheory.NearLowerCompare.frm_isUnit I x)
    (Matrix.toLin' ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - η)) (lamX I y) (lamX I x) hy.fg hx.fg
    (by
      rintro _ ⟨z, hz, rfl⟩
      have := sub_mem (mulVec_mem I x y a γ hγ2 haK z hz) (mulVec_mem I x y b η hη2 hbK z hz)
      simpa [Matrix.sub_mulVec] using this)
    (by
      intro h0
      apply hne
      apply Matrix.toLin'.injective
      rw [map_zero]
      refine LinearMap.ext_on hy.span_eq_top fun z hz => ?_
      exact (Submodule.eq_bot_iff _).1 h0 _ ⟨z, hz, rfl⟩)
  rw [(GlobalTheory.T.orthogonal_canonicalFiltration_steps_autPoint I y).2.1 hn, div_inv_eq_mul] at h
  have e1 : (nPl I.E : ℝ) = Fintype.card (InfinitePlace I.F) := by
    rw [nPl, Fintype.card_of_bijective (comap_bijective I)]
  have e2 : ∏ w, opNormAt (bas I) (frm I y) (bas I) (frm I x) w
      (Matrix.toLin' ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - η)) =
      ∏ v, ‖op (uMat ((x⁻¹ * a * y).1 v)) - op (uMat ((x⁻¹ * b * y).1 v))‖ := by
    refine Fintype.prod_bijective _ (comap_bijective I) _ _ fun w => ?_
    rw [opNormAt_eq, uMat_eq I x y a γ _ (hγ1 _), uMat_eq I x y b η _ (hη1 _), op, op, op, ← map_sub, ← map_sub,
      Matrix.map_sub _ (map_sub _), Matrix.mul_sub, Matrix.sub_mul]
  rw [e1, e2] at h
  refine le_trans ?_ h
  exact mul_le_mul (min_le_right _ _) (min_le_right _ _) (truncatedLeastLatticeSize_pos I hn y).le
    ((truncatedLeastLatticeSize_pos I hn x).le.trans (min_le_right _ _))

theorem count_le (I : AutInst) (x y : I.GA) (r : InfinitePlace I.F → ℝ) (hn : 1 ≤ I.n) (_hr : ∀ v, 0 ≤ r v) :
    {a : I.GA | a ∈ I.GFset ∧ (x⁻¹ * a * y).2 ∈ I.Kset ∧ ∀ v, dOp (uMat ((x⁻¹ * a * y).1 v)) ≤ r v}.Finite ∧
    (({a : I.GA | a ∈ I.GFset ∧ (x⁻¹ * a * y).2 ∈ I.Kset ∧
        ∀ v, dOp (uMat ((x⁻¹ * a * y).1 v)) ≤ r v}.ncard : ℕ) : ℝ) ≤
      (1 + 2 * Real.sqrt I.n * Real.exp ((∑ v, r v) / I.f) / (tau1 I x * tau1 I y)) ^ (2 * (I.n ^ 2 * I.f)) := by
  set A := {a : I.GA | a ∈ I.GFset ∧ (x⁻¹ * a * y).2 ∈ I.Kset ∧ ∀ v, dOp (uMat ((x⁻¹ * a * y).1 v)) ≤ r v}
  let s : I.GA → InfinitePlace I.F → (EuclideanSpace ℂ (Fin I.n) →L[ℂ] EuclideanSpace ℂ (Fin I.n)) :=
    fun a v => op (uMat ((x⁻¹ * a * y).1 v))
  have hla : 0 < tau1 I x * tau1 I y := mul_pos (truncatedLeastLatticeSize_pos I hn x) (truncatedLeastLatticeSize_pos I hn y)
  have hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → tau1 I x * tau1 I y ≤
      (∏ v, ‖s a v - s b v‖) ^ ((1 : ℝ) / Fintype.card (InfinitePlace I.F)) :=
    fun a ha b hb hab => separated I hn x y a b ha.1 hb.1 ha.2.1 hb.2.1 hab
  have hcard : (0 : ℝ) < Fintype.card (InfinitePlace I.F) := by exact_mod_cast Fintype.card_pos
  have hinj : Set.InjOn s A := by
    intro a ha b hb h
    by_contra hab
    have := hsep a ha b hb hab
    rw [h] at this
    simp only [sub_self, norm_zero, Finset.prod_const, Finset.card_univ] at this
    rw [zero_pow Fintype.card_ne_zero, Real.zero_rpow (one_div_pos.2 hcard).ne'] at this
    exact absurd this (not_le.2 hla)
  have : FiniteDimensional ℝ (EuclideanSpace ℂ (Fin I.n) →L[ℂ] EuclideanSpace ℂ (Fin I.n)) :=
    Module.Finite.trans ℂ _
  obtain ⟨hfin, hle⟩ := GlobalTheory.packing_geometric_mean_separated (InfinitePlace I.F)
    (fun _ => EuclideanSpace ℂ (Fin I.n) →L[ℂ] EuclideanSpace ℂ (Fin I.n)) (2 * I.n ^ 2)
    (by nlinarith) (fun _ => finrank_op I.n) (tau1 I x * tau1 I y) (s '' A) (fun v => Real.exp (r v)) hla
    (fun v => Real.exp_pos _) (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
      exact hsep a ha b hb fun h => hab (by rw [h]))
  have hA : {t ∈ s '' A | ∀ v, ‖t v‖ ≤ Real.exp (r v)} = s '' A := by
    refine Set.sep_eq_self_iff_mem_true.2 ?_
    rintro _ ⟨a, ha, rfl⟩ v
    exact (Real.le_exp_log _).trans (Real.exp_le_exp.2 (ha.2.2 v))
  rw [hA] at hfin hle
  refine ⟨hfin.of_finite_image hinj, ?_⟩
  rw [hinj.ncard_image, ← Real.exp_sum, ← Real.exp_mul, card_places, mul_one_div, mul_assoc 2 (I.n ^ 2)] at hle
  refine hle.trans (pow_le_pow_left₀ (by positivity) ?_ _)
  have h1 : (1 : ℝ) ≤ Real.sqrt I.n := Real.one_le_sqrt.2 (by exact_mod_cast hn)
  have h2 := Real.exp_pos ((∑ v, r v) / I.f)
  gcongr
  linarith

end GlobalTheory.RationalCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VENatEqZero
section
open NumberField IsDedekindDomain ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.HL

namespace GlobalTheory.TypeUnifProd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem valuation_natCast_prime_eq_one_of_ne_resChar {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    {l : ℕ} (hl : l.Prime) (hne : l ≠ Loc.resChar p) : p.valuation F (l : F) = 1 := by
  rw [← map_natCast (algebraMap (𝓞 F) F) l, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff]
  intro hmem
  apply hne
  have : p.asIdeal.IsPrime := p.isPrime
  have hz : ((l : ℕ) : 𝓞 F ⧸ p.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  have hdvd : ringChar (𝓞 F ⧸ p.asIdeal) ∣ l := (ringChar.spec _ l).1 hz
  rcases (Nat.dvd_prime hl).1 hdvd with h | h
  · exfalso
    have h1 : ((1 : ℕ) : 𝓞 F ⧸ p.asIdeal) = 0 := (ringChar.spec _ 1).2 (by rw [h])
    simp at h1
  · exact h.symm

private theorem vE_algebraMap_ιF_eq_neg_log_valuation {D : D7} (p : PlF D) (L : Loc.LocE (D.s.atP p).Fp (D.s.atP p).Ep)
    {ϖ : 𝒪[(D.s.atP p).Fp]} (hϖ : Irreducible ϖ) {x : D.host.F} (hx : x ≠ 0) :
    vE L ϖ (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF x)) =
      -WithZero.log (p.valuation D.host.F x) := by
  have := (D.s.atP p).lf
  refine GlobalTheory.ResProd.vE_eq_neg_log p L (D.s.atP p).ιF (D.s.atP p).dense ?_ hϖ hx
  intro a b
  rw [← Valuation.Compatible.vle_iff_le]
  exact (D.s.atP p).val a b

private theorem exists_theta_eq_ιF_valuation_eq_g_mul {D : D7} (Z : LocDat D) (p : PlF D) :
    ∃ t : D.host.F, t ≠ 0 ∧ LocNG.theta (Z.M p) = (D.s.atP p).ιF t ∧
      p.valuation D.host.F t = p.valuation D.host.F ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F) := by
  obtain ⟨-, -, -, -, -, hsp⟩ := Z.agree p
  have hss := D.s_split p
  have hg0 := D.host.g_prime 0
  have hg1 := D.host.g_prime 1
  have hgne := D.host.g_ne
  unfold LocNG.theta
  cases hM : (Z.M p).split with
  | none =>
    cases hS : (D.s.atP p).split with
    | none =>
      rw [hS] at hss
      have h0 : D.host.g 0 ≠ Loc.resChar p := fun h => by simp [h] at hss
      have h1 : D.host.g 1 ≠ Loc.resChar p := fun h => by simp [h] at hss
      refine ⟨1, one_ne_zero, (map_one _).symm, ?_⟩
      push_cast
      rw [map_mul, valuation_natCast_prime_eq_one_of_ne_resChar p hg0 h0, valuation_natCast_prime_eq_one_of_ne_resChar p hg1 h1, map_one, mul_one]
    | some sg =>
      rw [hM, hS] at hsp
      exact (hsp : False).elim
  | some g =>
    cases hS : (D.s.atP p).split with
    | none =>
      rw [hM, hS] at hsp
      exact (hsp : False).elim
    | some sg =>
      rw [hM, hS] at hsp
      obtain ⟨-, hq⟩ := hsp
      have hl : (Loc.resChar p).Prime := (D.s.atP p).ellPrime.out
      have hmem : Loc.resChar p = D.host.g 0 ∨ Loc.resChar p = D.host.g 1 := by
        have := hss.1 (by rw [hS]; rfl)
        simpa using this
      refine ⟨(Loc.resChar p : D.host.F), Nat.cast_ne_zero.2 hl.ne_zero, ?_, ?_⟩
      · change ((g.q : (D.s.atP p).Fp)) = _
        rw [hq, sg.q_eq, map_natCast]
      · push_cast
        rw [map_mul]
        rcases hmem with h | h
        · rw [valuation_natCast_prime_eq_one_of_ne_resChar p hg1 (by rw [h]; exact hgne.symm), mul_one, h]
        · rw [valuation_natCast_prime_eq_one_of_ne_resChar p hg0 (by rw [h]; exact hgne), one_mul, h]

theorem modK_theta {D : D7} (Z : LocDat D) (p : PlF D) {ϖ : 𝒪[(D.s.atP p).Fp]} (hϖ : Irreducible ϖ) :
    (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p))) = (resQ ϖ : ℝ) ^
      (-(2 * vE (Z.M p).L ϖ (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
        ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F))))) := by
  obtain ⟨hOK, -⟩ := Z.agree p
  obtain ⟨t, ht, hθ, hv⟩ := exists_theta_eq_ιF_valuation_eq_g_mul Z p
  have hx : ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  rw [hθ, (GlobalTheory.BaseModule.modK_algebraMap (Z.M p) hOK ϖ hϖ).2 _ ((map_ne_zero _).2 ht),
    vE_algebraMap_ιF_eq_neg_log_valuation p _ hϖ ht, vE_algebraMap_ιF_eq_neg_log_valuation p _ hϖ hx, hv]

noncomputable def placesOf {D : D7} (Z : LocDat D) : Places D.host.F D.host.E D.conjF where
  quad := D.sp.cm.deg2
  loc := D.s.atP
  L := fun p => (Z.M p).L
  L_cj := Z.hcj

theorem card_infinite (D : D7) :
    Fintype.card (InfinitePlace D.host.E) = Module.finrank ℚ D.host.F := by
  have : IsCMField D.host.E := D.host.isCMField_hostE
  have : IsTotallyComplex D.host.E := IsCMField.to_isTotallyComplex
  have h1 := IsTotallyComplex.finrank (K := D.host.E)
  have h2 := D.sp.cm.deg2
  have h3 := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  rw [h2] at h3
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  omega

theorem main : ∀ (D : D7) (Z : LocDat D), (Function.mulSupport fun p : PlF D => (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p)))).Finite ∧ ∏ᶠ p : PlF D, (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p))) = (((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) ^ (2 * Fintype.card (InfinitePlace D.host.E)))⁻¹ := by
  intro D Z
  have hex : ∀ p : PlF D, ∃ ϖ : 𝒪[(D.s.atP p).Fp], Irreducible ϖ := fun p => by
    have := (D.s.atP p).lf
    exact IsDiscreteValuationRing.exists_irreducible _
  choose ϖ hϖ using hex
  have hx : ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  obtain ⟨hfin, hprod⟩ := GlobalTheory.ResProd.prod_resQ_zpow (placesOf Z) ϖ hϖ _ hx
  have hfin' : {p : PlF D | vE (Z.M p).L (ϖ p) (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
      ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F))) ≠ 0}.Finite := hfin
  have hprod' : ∏ᶠ p : PlF D, (resQ (ϖ p) : ℝ) ^ vE (Z.M p).L (ϖ p) (algebraMap (D.s.atP p).Fp
      (D.s.atP p).Ep ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F))) =
      |((Algebra.norm ℚ ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F) : ℚ) : ℝ)| := hprod
  have hterm : ∀ p : PlF D, (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p))) =
      (((resQ (ϖ p) : ℝ) ^ vE (Z.M p).L (ϖ p) (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
        ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)))) ^ 2)⁻¹ := by
    intro p
    rw [modK_theta Z p (hϖ p), zpow_neg, mul_comm, zpow_mul]
    norm_cast
  have hsub : (Function.mulSupport fun p : PlF D => (resQ (ϖ p) : ℝ) ^ vE (Z.M p).L (ϖ p)
      (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
        ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)))) ⊆
      {p : PlF D | vE (Z.M p).L (ϖ p) (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
        ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F))) ≠ 0} := by
    intro p hp
    simp only [Function.mem_mulSupport, ne_eq, Set.mem_ofPred_eq] at hp ⊢
    intro h0
    apply hp
    rw [h0, zpow_zero]
  have hfs := hfin'.subset hsub
  simp_rw [hterm]
  refine ⟨hfs.subset ?_, ?_⟩
  · intro p hp
    simp only [Function.mem_mulSupport, ne_eq] at hp ⊢
    intro h1
    apply hp
    rw [h1, one_pow, inv_one]
  · have hn : Algebra.norm ℚ ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F) =
        ((D.host.g 0 * D.host.g 1 : ℕ) : ℚ) ^ Module.finrank ℚ D.host.F := by
      rw [← map_natCast (algebraMap ℚ D.host.F), Algebra.norm_algebraMap]
    rw [finprod_inv_distrib, ← finprod_pow hfs, hprod', card_infinite D, hn]
    push_cast
    rw [abs_of_nonneg (by positivity), ← pow_mul]
    ring

end GlobalTheory.TypeUnifProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ZlatticeCovolumeEqOfCoprimeScalarsStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zlattice_covolume_eq_of_coprime_scalars : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (A B : Submodule ℤ (ι → κ → ℝ)) [DiscreteTopology A] [IsZLattice ℝ A] [DiscreteTopology B] [IsZLattice ℝ B], (∀ p : ℕ, p.Prime → ∃ (d : ι → ℝ) (N : ℕ), ¬ p ∣ N ∧ ∏ v, d v ^ 2 = N ∧ (∀ y ∈ A, (fun v i => d v * y v i) ∈ B) ∧ ∀ y ∈ B, (fun v i => d v * y v i) ∈ A) → ZLattice.covolume A volume = ZLattice.covolume B volume := by
  first | exact @GlobalTheory.CovScal.covolume_eq_of_scalars | exact GlobalTheory.CovScal.covolume_eq_of_scalars | (intros; apply GlobalTheory.CovScal.covolume_eq_of_scalars <;> assumption)
end

