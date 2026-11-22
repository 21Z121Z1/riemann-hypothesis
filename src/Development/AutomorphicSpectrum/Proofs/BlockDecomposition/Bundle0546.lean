import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0525
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0518
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0096
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0443

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableInnerIBlkU
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.RS.ColN
open PositivityTheory.AdelicQuotientData

section Ring

variable {R : Type} [CommRing R] {a : ℕ}

theorem posM_blk_apply (m : ℕ) (c : UnipotentBlockColumnIndex a m m → R) (i j : Fin a) :
    posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) c i j =
      if h : (i : ℕ) < m ∧ (j : ℕ) = m then c ⟨(i, j), h.1, h.2.ge, h.2.le⟩ else 0 := by
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i, j), h.1, h.2.ge, h.2.le⟩]
    · simp
    · intro t _ ht
      rw [if_neg]
      rintro ⟨e1, e2⟩
      exact ht (Subtype.ext (Prod.ext e1 e2))
    · simp
  · refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rintro ⟨e1, e2⟩
    apply h
    have h1 := t.2
    rw [← e1, ← e2]
    omega

theorem posM_mul_of_row (m : ℕ) (c : UnipotentBlockColumnIndex a m m → R) (M : Matrix (Fin a) (Fin a) R)
    (hM : ∀ r j : Fin a, (r : ℕ) = m → M r j = (1 : Matrix (Fin a) (Fin a) R) r j) :
    posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) c * M = posM Subtype.val c := by
  simp only [posM, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 := t.2
  calc Matrix.single t.1.1 t.1.2 (c t) * M = Matrix.single t.1.1 t.1.2 (c t) * 1 := by
        ext p q
        simp only [Matrix.mul_apply, Matrix.single_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        by_cases h : t.1.1 = p ∧ t.1.2 = l
        · rw [if_pos h, hM l q (by rw [← h.2]; omega)]
        · rw [if_neg h, zero_mul, zero_mul]
    _ = _ := mul_one _

theorem blkU_mul_val (m : ℕ) (c : UnipotentBlockColumnIndex a m m → R) (γ : GL (Fin a) R)
    (hM : ∀ r j : Fin a, (r : ℕ) = m → γ.val r j = (1 : Matrix (Fin a) (Fin a) R) r j) :
    (blkU c * γ).val = γ.val + posM Subtype.val c := by
  change (1 + posM Subtype.val c) * γ.val = _
  rw [add_mul, one_mul, posM_mul_of_row m c _ hM]

theorem blkU_inv_mul_val (m : ℕ) (c : UnipotentBlockColumnIndex a m m → R) (γ : GL (Fin a) R)
    (hM : ∀ r j : Fin a, (r : ℕ) = m → γ.val r j = (1 : Matrix (Fin a) (Fin a) R) r j) :
    ((blkU c)⁻¹ * γ).val = γ.val - posM Subtype.val c := by
  change (1 - posM Subtype.val c) * γ.val = _
  rw [sub_mul, one_mul, posM_mul_of_row m c _ hM]

theorem blkU_add (m : ℕ) (x y : UnipotentBlockColumnIndex a m m → R) : blkU (x + y) = blkU x * blkU y :=
  posU_add _ x y

theorem blkU_neg (m : ℕ) (x : UnipotentBlockColumnIndex a m m → R) : blkU (-x) = (blkU x)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← blkU_add, neg_add_cancel]
  exact posU_zero _

end Ring

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem row_of_blk {m : ℕ} {γ : GL (Fin k) E} (h : GlobalTheory m γ) (r j : Fin k) (hr : (r : ℕ) = m) :
    γ.val r j = (1 : Matrix (Fin k) (Fin k) E) r j := h r j (Or.inl hr.ge)

theorem isMir_blkU_mul {m : ℕ} (c : UnipotentBlockColumnIndex k m m → E) {γ : GL (Fin k) E} (h : GlobalTheory m γ) :
    IsMir m (blkU c * γ) := by
  intro i j hij
  rw [blkU_mul_val m c γ (row_of_blk h), Matrix.add_apply, posM_blk_apply, dif_neg (by omega), add_zero]
  exact h i j (by omega)

def colEquiv (m : ℕ) :
    (UnipotentBlockColumnIndex k m m → E) × ({γ | GlobalTheory m γ} : Set (GL (Fin k) E)) ≃ ({γ | IsMir m γ} : Set (GL (Fin k) E)) :=
  Equiv.ofBijective (fun p => ⟨blkU p.1 * p.2.1, isMir_blkU_mul p.1 p.2.2⟩) (by
    constructor
    · rintro ⟨c, γ, hγ⟩ ⟨c', γ', hγ'⟩ h
      have h0 : blkU c * γ = blkU c' * γ' := congrArg Subtype.val h
      have hv := congrArg Units.val h0
      rw [blkU_mul_val m c γ (row_of_blk hγ), blkU_mul_val m c' γ' (row_of_blk hγ')] at hv
      have hc : c = c' := by
        funext t
        have h1 := t.2
        have h2 := congrFun (congrFun hv t.1.1) t.1.2
        simp only [Matrix.add_apply] at h2
        rw [hγ t.1.1 t.1.2 (Or.inr h1.2.1), hγ' t.1.1 t.1.2 (Or.inr h1.2.1), posM_blk_apply, posM_blk_apply,
          dif_pos ⟨h1.1, by omega⟩, dif_pos ⟨h1.1, by omega⟩] at h2
        exact add_left_cancel h2
      subst hc
      have : γ = γ' := mul_left_cancel h0
      subst this
      rfl
    · rintro ⟨p, hp⟩
      have hrow : ∀ r j : Fin k, (r : ℕ) = m → p.val r j = (1 : Matrix (Fin k) (Fin k) E) r j :=
        fun r j hr => hp r j (Or.inl hr.ge)
      let c : UnipotentBlockColumnIndex k m m → E := fun t => p.val t.1.1 t.1.2
      have hγ : GlobalTheory m ((blkU c)⁻¹ * p) := by
        intro i j hij
        rw [blkU_inv_mul_val m c p hrow, Matrix.sub_apply, posM_blk_apply]
        split_ifs with h
        · have hne : i ≠ j := fun e => by rw [e] at h; omega
          rw [Matrix.one_apply_ne hne]
          exact sub_self _
        · rw [sub_zero]
          exact hp i j (by omega)
      exact ⟨(c, ⟨_, hγ⟩), Subtype.ext (mul_inv_cancel_left _ _)⟩)

theorem colEquiv_val (m : ℕ) (c : UnipotentBlockColumnIndex k m m → E) (γ : ({γ | GlobalTheory m γ} : Set (GL (Fin k) E))) :
    (colEquiv m (c, γ)).1 = blkU c * γ.1 := rfl

theorem blk_ratGL {m : ℕ} {γ : GL (Fin k) E} (h : GlobalTheory m γ) : GlobalTheory m (ratGL E k γ) := by
  intro i j hij
  change algebraMap E (Ad E) (γ.val i j) = _
  rw [h i j hij, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem lintegral_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) {Φ : GA E k → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ h, Φ h ∂nuG Γ d = ∑' γ : Γ, ∫⁻ h, Φ (ratGL E k γ * h) ∂nuD E k d := by
  rw [nuG, lintegral_sum_measure]
  refine tsum_congr fun γ => ?_
  rw [lintegral_map hΦ (measurable_const_mul _)]

theorem measurable_blkU_mul (m : ℕ) :
    Measurable fun p : (UnipotentBlockColumnIndex k m m → Ad E) × GA E k => (blkU p.1 * p.2 : GA E k) :=
  (((continuous_posU (isNil_blk k m m)).comp continuous_fst).mul continuous_snd).measurable

theorem lintegral_nuD_succ (m d : ℕ) (hm : m = k - (d + 1)) [SFinite (nuD E k d)] {Φ : GA E k → ℝ≥0∞}
    (hΦ : Measurable Φ) :
    ∫⁻ h, Φ h ∂nuD E k (d + 1) =
      ∫⁻ x : UnipotentBlockColumnIndex k m m → Ad E, ∫⁻ n, Φ (blkU x * n) ∂nuD E k d ∂vecMeasure E (UnipotentBlockColumnIndex k m m) := by
  subst hm
  rw [nuD, lintegral_map hΦ (measurable_blkU_mul _)]
  exact lintegral_prod (fun p : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) × GA E k => Φ (blkU p.1 * p.2))
    (hΦ.comp (measurable_blkU_mul _)).aemeasurable

theorem unfold_vec (ι : Type) [Fintype ι] (G : (ι → Ad E) → ℝ≥0∞) :
    ∫⁻ y, G y ∂vecMeasure E ι =
      ∑' c : ι → E, ∫⁻ x in vecDomain E ι, G (-x + fun t => algebraMap E (Ad E) (c t)) ∂vecMeasure E ι := by
  haveI : (vecMeasure E ι).IsNegInvariant := Measure.pi.isNegInvariant _
  haveI := GroundTheory.Global.countable_numberField E
  rw [← lintegral_neg_eq_self, (isAddFundamentalDomain_vecDomain (K := E) (ι := ι)).lintegral_eq_tsum']
  let e : (ι → E) ≃ vecLattice E ι := Equiv.ofBijective
    (fun c => ⟨fun t => algebraMap E (Ad E) (c t), c, rfl⟩) (by
      constructor
      · intro c c' h
        funext t
        exact NumberField.AdeleRing.algebraMap_injective (𝓞 E) E (congrFun (congrArg Subtype.val h) t)
      · rintro ⟨_, c, rfl⟩
        exact ⟨c, rfl⟩)
  rw [← e.tsum_eq]
  refine tsum_congr fun c => lintegral_congr fun x => ?_
  congr 1
  change -(-(fun t => algebraMap E (Ad E) (c t)) + x) = _
  rw [neg_add, neg_neg, add_comm]

theorem countable_GL : Countable (GL (Fin k) E) := by
  haveI := GroundTheory.Global.countable_numberField E
  haveI : Countable (Matrix (Fin k) (Fin k) E) := inferInstanceAs (Countable (Fin k → Fin k → E))
  exact Function.Injective.countable (f := fun g : GL (Fin k) E => g.val) Units.val_injective

def innerI (d : ℕ) (F : GA E k → ℝ≥0∞) (g u : GA E k) : ℝ≥0∞ := ∫⁻ n, F (u * (g * n)) ∂nuD E k d

theorem measurable_innerI (d : ℕ) [SFinite (nuD E k d)] {F : GA E k → ℝ≥0∞} (hF : Measurable F) (g : GA E k) :
    Measurable (innerI d F g) :=
  Measurable.lintegral_prod_right' (f := fun p : GA E k × GA E k => F (p.1 * (g * p.2)))
    (hF.comp (measurable_fst.mul (measurable_snd.const_mul g)))

theorem measurable_innerI_blkU (m d : ℕ) [SFinite (nuD E k d)] {F : GA E k → ℝ≥0∞} (hF : Measurable F)
    (g : GA E k) : Measurable fun y : UnipotentBlockColumnIndex k m m → Ad E => innerI d F g (blkU y) :=
  (measurable_innerI d hF g).comp (continuous_posU (isNil_blk k m m)).measurable

theorem left_side (m d : ℕ) (hm : m = k - (d + 1)) (hd : d + 1 ≤ k) (sf : SFinite (nuD E k d))
    (dt1 : ∀ γ : GL (Fin k) E, Dt (ratGL E k γ) = 1)
    (mod : ∀ g : GA E k, GlobalTheory m g → ∀ F : GA E k → ℝ≥0∞, Measurable F →
      ∫⁻ x : UnipotentBlockColumnIndex k m m → Ad E, F (g * blkU x * g⁻¹) ∂vecMeasure E _ =
        ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x : UnipotentBlockColumnIndex k m m → Ad E, F (blkU x) ∂vecMeasure E _)
    {F : GA E k → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ h, F h ∂nuB E k m =
      ∑' γ : ({γ | GlobalTheory m γ} : Set (GL (Fin k) E)),
        ∫⁻ y : UnipotentBlockColumnIndex k m m → Ad E, innerI d F (ratGL E k γ.1) (blkU y) ∂vecMeasure E (UnipotentBlockColumnIndex k m m) := by
  have hkm : k - m = d + 1 := by omega
  rw [nuB, hkm, lintegral_nuG _ _ hF]
  refine tsum_congr fun γ => ?_
  have h1 := lintegral_nuD_succ m d hm (Φ := fun h => F (ratGL E k γ.1 * h)) (hF.comp (measurable_const_mul _))
  have key := mod (ratGL E k γ.1) (blk_ratGL γ.2) (innerI d F (ratGL E k γ.1)) (measurable_innerI d hF _)
  rw [dt1, inv_one, ENNReal.ofReal_one, one_mul] at key
  rw [h1, ← key]
  refine lintegral_congr fun x => lintegral_congr fun n => ?_
  simp only [mul_assoc, inv_mul_cancel_left]

theorem right_inner (m d : ℕ) (hm : m = k - (d + 1)) (hd : d + 1 ≤ k) {F : GA E k → ℝ≥0∞} (hF : Measurable F)
    (x : UnipotentBlockColumnIndex k m m → Ad E) :
    ∫⁻ h, F ((blkU x)⁻¹ * h) ∂nuP E k m =
      ∑' γ : ({γ | GlobalTheory m γ} : Set (GL (Fin k) E)), ∑' c : UnipotentBlockColumnIndex k m m → E,
        innerI d F (ratGL E k γ.1) (blkU (-x + fun t => algebraMap E (Ad E) (c t))) := by
  have hkm' : k - (m + 1) = d := by omega
  rw [nuP, hkm', lintegral_nuG _ _ (Φ := fun h => F ((blkU x)⁻¹ * h)) (hF.comp (measurable_const_mul _)),
    ← (colEquiv m).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
  refine tsum_congr fun γ => tsum_congr fun c => lintegral_congr fun n => ?_
  rw [colEquiv_val, map_mul, ratGL_blkU, blkU_add, blkU_neg]
  simp only [mul_assoc]

theorem main (m d : ℕ) (hm : m = k - (d + 1)) (hd : d + 1 ≤ k) (sf : SFinite (nuD E k d))
    (dt1 : ∀ γ : GL (Fin k) E, Dt (ratGL E k γ) = 1)
    (mod : ∀ g : GA E k, GlobalTheory m g → ∀ F : GA E k → ℝ≥0∞, Measurable F →
      ∫⁻ x : UnipotentBlockColumnIndex k m m → Ad E, F (g * blkU x * g⁻¹) ∂vecMeasure E _ =
        ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x : UnipotentBlockColumnIndex k m m → Ad E, F (blkU x) ∂vecMeasure E _)
    {F : GA E k → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ h, F h ∂nuB E k m =
      ∫⁻ x in vecDomain E (UnipotentBlockColumnIndex k m m), ∫⁻ h, F ((blkU x)⁻¹ * h) ∂nuP E k m ∂vecMeasure E (UnipotentBlockColumnIndex k m m) := by
  haveI := GroundTheory.Global.countable_numberField E
  haveI : Countable (GL (Fin k) E) := countable_GL
  have hmeas : ∀ (γ : ({γ | GlobalTheory m γ} : Set (GL (Fin k) E))) (c : UnipotentBlockColumnIndex k m m → E),
      Measurable fun x : UnipotentBlockColumnIndex k m m → Ad E =>
        innerI d F (ratGL E k γ.1) (blkU (-x + fun t => algebraMap E (Ad E) (c t))) := fun γ c =>
    (measurable_innerI_blkU m d hF _).comp (measurable_neg.add_const _)
  rw [left_side m d hm hd sf dt1 mod hF, lintegral_congr (right_inner m d hm hd hF),
    lintegral_tsum fun γ => (Measurable.ennreal_tsum fun c => hmeas γ c).aemeasurable]
  refine tsum_congr fun γ => ?_
  rw [lintegral_tsum fun c => (hmeas γ c).aemeasurable]
  exact unfold_vec _ _

theorem one_more_column : D0 → N0 → N1 → N3 → ColumnConjugationMeasure → OneMoreAdelicColumn := by
  intro hD _ hN1 _ hM E _ _ _ k m hm F hF
  obtain ⟨d, hd, hmd⟩ : ∃ d, d + 1 ≤ k ∧ m = k - (d + 1) := ⟨k - (m + 1), by omega, by omega⟩
  exact main m d hmd hd (hN1 E k d (by omega)).1 (hD E k).2.2.2.1 (hM E k m hm) hF

end GlobalTheory.CompanionTheory.RS.ColN

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemParabolicOfFlagPreserving
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise
open GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RegInt

noncomputable section
namespace GlobalTheory.CompanionTheory.RegInt

theorem mem_parRat_frameFlag_firstCols : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (j : Fin r) (δ : GF V),
    (∀ l : Fin r, l ≤ j → ∃ b : Fin r → D.host.E, δ.1.1 *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0) →
    δ ∈ (frameFlag (isIsoFrame_firstCols hW j)).parRat D.sp.cm := by
  intro D V r X Y hW j δ h
  have hcoord : ∀ c : Fin V.rank → D.host.E, ratAct D.sp.cm V δ (GlobalTheory.AutFunCompare.vecOf V c) =
      GlobalTheory.AutFunCompare.vecOf V (δ.1.1 *ᵥ c) := by
    intro c
    refine V.frame.ext_elem fun i => ?_
    rw [GlobalTheory.AutFunCompare.repr_vecOf, ratAct, Matrix.repr_toLin]
    congr 1
    funext a
    exact GlobalTheory.AutFunCompare.repr_vecOf V c a
  have hspan : ∀ x ∈ GlobalTheory.AutFunCompare.colSpan V (firstCols X j),
      ratAct D.sp.cm V δ x ∈ GlobalTheory.AutFunCompare.colSpan V (firstCols X j) := by
    have hle : GlobalTheory.AutFunCompare.colSpan V (firstCols X j) ≤
        (GlobalTheory.AutFunCompare.colSpan V (firstCols X j)).comap (ratAct D.sp.cm V δ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      obtain ⟨b, hb, hb0⟩ := h (Fin.castLE j.2 k) (Nat.lt_succ_iff.1 k.2)
      have hcol : (firstCols X j)ᵀ k = fun a => X a (Fin.castLE j.2 k) := rfl
      change ratAct D.sp.cm V δ (GlobalTheory.AutFunCompare.vecOf V ((firstCols X j)ᵀ k)) ∈ GlobalTheory.AutFunCompare.colSpan V (firstCols X j)
      rw [hcoord, hcol, hb]
      have hsum : X *ᵥ b = ∑ l, b l • (fun a => X a l) := by
        funext a
        simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
      rw [hsum, GlobalTheory.AutFunCompare.vecOf, map_sum]
      refine Submodule.sum_mem _ fun l _ => ?_
      rw [map_smul]
      by_cases hl : l ≤ j
      · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨l.val, Nat.lt_succ_iff.2 hl⟩, rfl⟩)
      · rw [hb0 l (not_le.1 hl), zero_smul]
        exact Submodule.zero_mem _
    exact fun x hx => hle hx
  change GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.diagH D.sp.cm.sig V.gram D.host.F δ ∈ IsoFlag.par _ D.sp.cm D.host.F
  rw [frameFlag, IsoFlag.par_single, diagH_mem_parab]
  exact hspan

end GlobalTheory.CompanionTheory.RegInt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingDepthInduction
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_threshold_mem_box {m : ℕ} (y : Fin m → k) (t₀ : kˣ) :
    ∃ t₁ : kˣ, valuation k (t₀ : k) ≤ valuation k (t₁ : k) ∧
      ∀ t : kˣ, valuation k (t₁ : k) ≤ valuation k (t : k) → y ∈ box m t := by
  classical
  have hstep : ∀ (S : Finset (Fin m)), ∃ t₁ : kˣ, valuation k (t₀ : k) ≤ valuation k (t₁ : k) ∧
      ∀ j ∈ S, valuation k (y j) ≤ valuation k (t₁ : k) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨t₀, le_rfl, by simp⟩
    | insert a S _ ih =>
      obtain ⟨t₁, h0, h1⟩ := ih
      by_cases hle : valuation k (y a) ≤ valuation k (t₁ : k)
      · refine ⟨t₁, h0, fun j hj => ?_⟩
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact hle
        · exact h1 j hj
      · have hlt := lt_of_not_ge hle
        have hya : y a ≠ 0 := by
          intro h0'
          rw [h0', map_zero] at hlt
          exact not_lt_zero' hlt
        refine ⟨Units.mk0 (y a) hya, ?_, fun j hj => ?_⟩
        · simpa using h0.trans hlt.le
        · rcases Finset.mem_insert.1 hj with rfl | hj
          · simp
          · simpa using (h1 j hj).trans hlt.le
  obtain ⟨t₁, h0, h1⟩ := hstep Finset.univ
  exact ⟨t₁, h0, fun t ht j => (h1 j (Finset.mem_univ j)).trans ht⟩

variable [MeasurableSpace k] [BorelSpace k]

theorem setIntegral_box_add (ν : Measure k) [ν.IsAddHaarMeasure] {m : ℕ} (t : kˣ) {y : Fin m → k}
    (hy : y ∈ box m t) (f : (Fin m → k) → ℂ) :
    ∫ x in (box m t : Set (Fin m → k)), f (x + y) ∂(piHaar ν m) =
      ∫ x in (box m t : Set (Fin m → k)), f x ∂(piHaar ν m) := by
  haveI : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  haveI : (piHaar ν m).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hpre : (fun x => x + y) ⁻¹' (box m t : Set (Fin m → k)) = box m t := by
    ext x
    exact (box m t).add_mem_cancel_right hy
  have := (measurePreserving_add_right (piHaar ν m) y).setIntegral_preimage_emb
    (measurableEmbedding_addRight y) f (box m t : Set (Fin m → k))
  rwa [hpre] at this

theorem wt_sub (ψ : AddChar k Circle) (n : ℕ) (x y : Fin (n + 1) → k) :
    wt ψ n (x - y) = ((ψ (y (Fin.last n)) : Circle) : ℂ) * wt ψ n x := by
  have h : -(x - y) (Fin.last n) = y (Fin.last n) + -x (Fin.last n) := by
    simp only [Pi.sub_apply]; ring
  simp only [wt]
  rw [h, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem wt_add (ψ : AddChar k Circle) (n : ℕ) (x y : Fin (n + 1) → k) :
    wt ψ n (x + y) = ((ψ (-y (Fin.last n)) : Circle) : ℂ) * wt ψ n x := by
  have h : -(x + y) (Fin.last n) = -y (Fin.last n) + -x (Fin.last n) := by
    simp only [Pi.add_apply]; ring
  simp only [wt]
  rw [h, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem EvVal_translate : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → IsSmooth T → TwInv T T' B s → ∀ (y : Fin (n + 1) → k) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (T (uM (n + 1) y) v) v' (((ψ (y (Fin.last n)) : Circle) : ℂ) * A) ∧ EvVal ν ψ T B v (T' (uM (n + 1) y) v') (((ψ (-y (Fin.last n)) : Circle) : ℂ) * A) := by
  intro k _ _ _ _ _ _ ν _ ψ n V V' _ _ _ _ T T' B s _ _ hB y v v' A hA
  obtain ⟨t₀, ht₀⟩ := hA
  obtain ⟨t₁, h01, h1⟩ := exists_threshold_mem_box y t₀
  obtain ⟨hc1, hc2, -⟩ := GlobalTheory.T.mirabolic_coefficient_translation T T' B s hB
  refine ⟨⟨t₁, fun t ht => ?_⟩, ⟨t₁, fun t ht => ?_⟩⟩
  · have hy := h1 t ht
    have hJ := ht₀ t (h01.trans ht)
    have key := setIntegral_box_add ν t hy (fun x => wt ψ n (x - y) * coef T B v v' x)
    simp only [add_sub_cancel_right] at key
    have e1 : JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) (T (uM (n + 1) y) v) v' =
        ∫ x in (box (n + 1) t : Set (Fin (n + 1) → k)), wt ψ n x * coef T B v v' (x + y)
          ∂(piHaar ν (n + 1)) := by
      simp only [JJ, hc1]
    rw [e1, key, ← hJ, JJ, ← integral_const_mul]
    simp only [wt_sub, mul_assoc]
  · have hy := h1 t ht
    have hy' : -y ∈ box (n + 1) t := neg_mem hy
    have hJ := ht₀ t (h01.trans ht)
    have key := setIntegral_box_add ν t hy' (fun x => wt ψ n (x + y) * coef T B v v' x)
    simp only [← sub_eq_add_neg, sub_add_cancel] at key
    have e1 : JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v (T' (uM (n + 1) y) v') =
        ∫ x in (box (n + 1) t : Set (Fin (n + 1) → k)), wt ψ n x * coef T B v v' (x - y)
          ∂(piHaar ν (n + 1)) := by
      simp only [JJ, hc2]
    rw [e1, key, ← hJ, JJ, ← integral_const_mul]
    simp only [wt_add, mul_assoc]

end GlobalTheory.CompanionTheory.MirPair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilpotentOfProjectionZero
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

theorem hecke_pow_kills_of_proj_eq_zero : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V),
    IsSmooth π → ∀ t : D.T, D.IsStrDom t → ∀ U : Module.End ℂ (fixed π D.J),
    PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U → ∀ v : fixed π D.J, D.proj π (v : V) = 0 →
    ∃ j : ℕ, (U ^ j) v = 0 := by
  intro G _ _ _ D V _ _ π hπ t ht U hU v hv

  have hdom : ∀ r : ℕ, D.IsDom (t ^ r) := by
    intro r
    induction r with
    | zero => simpa using (GlobalTheory.CompanionTheory.Cass.isDom_monoid G D).1
    | succ r ih =>
      rw [pow_succ]
      exact (GlobalTheory.CompanionTheory.Cass.isDom_monoid G D).2 _ _ ih ht.1

  have hecke : ∀ r : ℕ, PositivityTheory.Lbc.IsHeckeOpG π D.J ((t ^ r : D.T) : G) (U ^ r) := by
    intro r
    induction r with
    | zero =>
      intro w l _
      simp
    | succ r ih =>
      rw [pow_succ, pow_succ U]
      exact GlobalTheory.T.casselman_first_property G D V π hπ (t ^ r) t (hdom r) ht.1 _ _ ih hU

  have key : ∀ u ∈ twKer π D.N 1, ∃ R : ℕ, ∀ r ≥ R,
      ∀ l : Module.Dual ℂ V, (∀ x ∈ D.J, l ∘ₗ π x = l) → l (π ((t : G) ^ r) u) = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨n, w, rfl⟩ := hu
      obtain ⟨R, hR⟩ := ht.2.1 (n : G) n.2
      refine ⟨R, fun r hr l hl => ?_⟩
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr
      have hmem : (t : G) ^ (R + j) * (n : G) * ((t : G) ^ (R + j))⁻¹ ∈ D.J ⊓ D.N := by
        have := (hdom j).1 _ hR
        convert this using 1
        simp only [Subgroup.coe_pow]
        rw [add_comm R j, pow_add]
        group
      have hx := hl _ hmem.1
      have hy := LinearMap.congr_fun hx (π ((t : G) ^ (R + j)) w)
      simp only [LinearMap.comp_apply] at hy
      have hz : π ((t : G) ^ (R + j) * (n : G) * ((t : G) ^ (R + j))⁻¹) (π ((t : G) ^ (R + j)) w)
          = π ((t : G) ^ (R + j)) (π (n : G) w) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [hz] at hy
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, hy, sub_self]
    | zero => exact ⟨0, fun r _ l _ => by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨A, hA⟩ := ha
      obtain ⟨B, hB⟩ := hb
      refine ⟨max A B, fun r hr l hl => ?_⟩
      rw [map_add, map_add, hA r (le_trans (le_max_left _ _) hr) l hl,
        hB r (le_trans (le_max_right _ _) hr) l hl, add_zero]
    | smul c a _ ha =>
      obtain ⟨A, hA⟩ := ha
      refine ⟨A, fun r hr l hl => ?_⟩
      rw [map_smul, map_smul, hA r hr l hl, smul_zero]
  obtain ⟨R, hR⟩ := key _ ((Submodule.Quotient.mk_eq_zero _).1 hv)
  refine ⟨R, ?_⟩
  have h0 : (((U ^ R) v : fixed π D.J) : V) = 0 := by
    refine GlobalTheory.T.fixed_vector_zero_of_dual G D.J D.isCompact_J V π hπ _ ((U ^ R) v).2 fun l hl => ?_
    rw [← hecke R v l hl, Subgroup.coe_pow]
    exact hR R le_rfl l hl
  exact Subtype.ext h0

end GlobalTheory.CompanionTheory.Cass
end

