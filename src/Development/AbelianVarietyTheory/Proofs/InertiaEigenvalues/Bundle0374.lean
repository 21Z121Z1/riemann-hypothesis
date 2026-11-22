import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0350
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0363
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0348
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.NonvanishingHypotheses
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevInductionGrowBoundOfPresentation
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismHomsAgreeOnWittStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_prism_homs_agree_on_witt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (w : Wq l bk.a), BK.hf f (C w) = BK.hf g (C w) := by
  first | exact @GlobalTheory.BSP.hf_C_eq_of_pair | exact GlobalTheory.BSP.hf_C_eq_of_pair | (intros; apply GlobalTheory.BSP.hf_C_eq_of_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinQuotientEisensteinEquiv
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem bkStr_quotient_equiv : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (O : Type) [CommRing O] [Algebra (Wq l a) O] (π : O) (Ep : Polynomial (Wq l a)), (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) → (Polynomial.aeval π Ep = 0 ∧ (∀ x : O, ∃ f : Polynomial (Wq l a), Polynomial.aeval π f = x) ∧ ∀ f : Polynomial (Wq l a), Polynomial.aeval π f = 0 → Ep ∣ f) → ∃ str : O ≃+* ((Wq l a)⟦X⟧ ⧸ Ideal.span {(Ep : (Wq l a)⟦X⟧)}), ∀ f : Polynomial (Wq l a), str (Polynomial.aeval π f) = Ideal.Quotient.mk _ (f : (Wq l a)⟦X⟧) := by
  intro l _ a _ O _ _ π Ep hE hπ
  obtain ⟨hmon, -, hdvd, -⟩ := hE
  obtain ⟨h0, hsurj, hker⟩ := hπ
  haveI : IsAdicComplete (Ideal.span {(l : Wq l a)}) (Wq l a) := WittVector.isAdicCompleteIdealSpanP
  have H : Ep.IsDistinguishedAt (Ideal.span {(l : Wq l a)}) :=
    { mem := fun hn => Ideal.mem_span_singleton.2 (hdvd _ hn)
      monic := hmon }
  have hK : RingHom.ker (Polynomial.aeval (R := Wq l a) π) = Ideal.span {Ep} := by
    ext f
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    constructor
    · exact hker f
    · rintro ⟨g, rfl⟩
      simp [h0]
  let e1 := Ideal.quotientKerAlgEquivOfSurjective (f := Polynomial.aeval (R := Wq l a) π)
    (fun x => hsurj x)
  let e2 := Ideal.quotientEquivAlgOfEq (Wq l a) hK
  let e := (e1.symm.trans (e2.trans H.algEquivQuotient)).toRingEquiv
  refine ⟨e, fun f => ?_⟩
  have h1 : e1.symm (Polynomial.aeval π f) = Ideal.Quotient.mk _ f := by
    apply e1.injective
    simp only [AlgEquiv.apply_symm_apply, e1]
    rfl
  simp only [e, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.trans_apply, h1]
  simp [e2, Polynomial.IsDistinguishedAt.algEquivQuotient_apply]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulLeJumpSumOfMemUpperRamificationNotMem
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_mul_le_jumpSum_of_mem_upper_not_mem : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (B : Subgroup (L ≃ₐ[F] L)) (v : ℝ),
    lowerRamificationGroup F L 0 = ⊤ → ∀ σ ∈ upperRamificationGroup F L v, σ ∉ B →
      (Nat.card (L ≃ₐ[F] L) : ℝ) * v ≤ (jumpSum (wild F L) ⊤ B : ℝ) := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ B v h0 σ hσ hσB
  have hσ1 : σ ≠ 1 := fun h ↦ hσB (h ▸ B.one_mem)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (lowerIndex_ne_top (K := F) (L := L) hσ1)
  have hm1 : 1 ≤ m := by
    have : (1 : ℕ∞) ≤ lowerIndex F L σ := one_le_lowerIndex_iff.mpr (h0 ▸ Subgroup.mem_top σ)
    rw [← hm] at this
    exact_mod_cast this
  have hv := (mem_upperRamificationGroup_iff_of_lowerIndex_eq hm.symm).mp hσ
  have hcast : ((m : ℝ) - 1) = ((m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hm1]; simp
  rw [hcast] at hv
  obtain ⟨hanti, hbot⟩ := GlobalTheory.T.wildLowerRamificationGroup_antitone_eventually_bot F L
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_initialSegment_not_inf_le_filtration (L ≃ₐ[F] L) (wild F L) ⊤ B hanti hbot
  have hjs := GlobalTheory.T.ramificationJumpSum_eq_sum_range (L ≃ₐ[F] L) (wild F L) ⊤ B n hanti hn
  have hphi := GlobalTheory.T.card_mul_herbrandPhi_natCast_totallyRamified F L h0 (m - 1)
  have hle : m - 1 ≤ n := by
    by_contra hlt
    push_neg at hlt
    have hmem : σ ∈ wild F L n := by
      rw [wild, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
        mem_lowerRamificationGroup_natCast_iff_lowerIndex, ← hm]
      exact_mod_cast (by omega : n + 1 + 1 ≤ m)
    have : ¬ (⊤ ⊓ wild F L n ≤ B) := fun h ↦ hσB (h ⟨Subgroup.mem_top σ, hmem⟩)
    exact lt_irrefl n ((hn n).mpr this)
  have hcard : (0 : ℝ) ≤ (Nat.card (L ≃ₐ[F] L) : ℝ) := Nat.cast_nonneg _
  calc (Nat.card (L ≃ₐ[F] L) : ℝ) * v ≤ (Nat.card (L ≃ₐ[F] L) : ℝ) * herbrandPhi F L ((m - 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hv hcard
    _ = ((∑ t ∈ Finset.range (m - 1), Nat.card ↥(wild F L t) : ℕ) : ℝ) := hphi
    _ ≤ (jumpSum (wild F L) ⊤ B : ℝ) := by
        rw [hjs]
        simp only [top_inf_eq]
        exact_mod_cast Finset.sum_le_sum_of_subset ((Finset.range_subset_range.mpr hle))

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CayleyIndependent
section
open Matrix

namespace GlobalTheory.CayleyUnitaryQuotient

variable {n : ℕ}

lemma star_mul_self {P : Matrix (Fin n) (Fin n) ℂ} (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Pᴴ * P = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hP

lemma mul_star_self {P : Matrix (Fin n) (Fin n) ℂ} (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    P * Pᴴ = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hP

lemma inv_eq_star {P : Matrix (Fin n) (Fin n) ℂ} (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    P⁻¹ = Pᴴ :=
  Matrix.inv_eq_left_inv (star_mul_self hP)

lemma quotient_mem_K {ε : Fin n → Bool} {P Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = Qᴴ * Formalism.REAL.Jm ε * Q) :
    P * Qᴴ ∈ Formalism.REAL.Kset ε := by
  have hQs : Qᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact star_mul_self hQ
  refine ⟨Submonoid.mul_mem _ hP hQs, ?_⟩
  show P * Qᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * (P * Qᴴ)
  calc P * Qᴴ * Formalism.REAL.Jm ε = P * Qᴴ * Formalism.REAL.Jm ε * (Q * Qᴴ) := by
        rw [mul_star_self hQ, Matrix.mul_one]
    _ = P * (Qᴴ * Formalism.REAL.Jm ε * Q) * Qᴴ := by simp only [Matrix.mul_assoc]
    _ = P * (Pᴴ * Formalism.REAL.Jm ε * P) * Qᴴ := by rw [h]
    _ = (P * Pᴴ) * (Formalism.REAL.Jm ε * (P * Qᴴ)) := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε * (P * Qᴴ) := by rw [mul_star_self hP, Matrix.one_mul]

lemma quotient_mul {P Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (P * Qᴴ) * (Q * Pᴴ) = 1 := by
  calc (P * Qᴴ) * (Q * Pᴴ) = P * (Qᴴ * Q) * Pᴴ := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [star_mul_self hQ, Matrix.mul_one, mul_star_self hP]

lemma conj_eq {P Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) :
    Q⁻¹ * (Q * Pᴴ * g * (P * Qᴴ)) * Q = P⁻¹ * g * P := by
  rw [inv_eq_star hP, inv_eq_star hQ]
  calc Qᴴ * (Q * Pᴴ * g * (P * Qᴴ)) * Q = (Qᴴ * Q) * (Pᴴ * g * P) * (Qᴴ * Q) := by
        simp only [Matrix.mul_assoc]
    _ = Pᴴ * g * P := by rw [star_mul_self hQ, Matrix.one_mul, Matrix.mul_one]

theorem cayley_independent : ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepStatement := by
  intro k r ε lam H _ _ _ σ Q P hQ hP hds
  have hPQ : Pᴴ * Formalism.REAL.Jm ε * P = Qᴴ * Formalism.REAL.Jm ε * Q := hP.1.2.trans hQ.1.2.symm
  have ha := quotient_mem_K hP.2 hQ.2 hPQ
  have hb := quotient_mem_K hQ.2 hP.2 hPQ.symm
  have key := ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.ds_conj (fun g => σ (Q⁻¹ * g * Q))
    (quotient_mul hP.2 hQ.2) (quotient_mul hQ.2 hP.2) ha hb lam hds
  simp only [conj_eq hP.2 hQ.2] at key
  exact key

end GlobalTheory.CayleyUnitaryQuotient
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralActsOnHeckeEigenspaceOfTypeSections
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.PendOf.EigSpanProof

section GroupAlg

variable {R : Type} [CommRing R] {G : Type} [Group G] [Fintype G]

def conjSum (w : MonoidAlgebra R G) : MonoidAlgebra R G :=
  ∑ h : G, MonoidAlgebra.of R G h * w * MonoidAlgebra.of R G h⁻¹

theorem conjSum_comm_of (w : MonoidAlgebra R G) (m : G) :
    conjSum w * MonoidAlgebra.of R G m = MonoidAlgebra.of R G m * conjSum w := by
  unfold conjSum
  rw [Finset.sum_mul, Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft m)]
  refine Finset.sum_congr rfl fun h _ => ?_
  have hm : MonoidAlgebra.of R G m⁻¹ * MonoidAlgebra.of R G m = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  simp only [Equiv.coe_mulLeft, mul_inv_rev, map_mul, mul_assoc, hm, mul_one]

theorem conjSum_mem_center (w : MonoidAlgebra R G) :
    conjSum w ∈ Subalgebra.center R (MonoidAlgebra R G) := by
  rw [Subalgebra.mem_center_iff]
  intro a
  induction a using MonoidAlgebra.induction_on with
  | of m => exact (conjSum_comm_of w m).symm
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem conjSum_add (x y : MonoidAlgebra R G) : conjSum (x + y) = conjSum x + conjSum y := by
  simp only [conjSum, mul_add, add_mul, Finset.sum_add_distrib]

theorem conjSum_smul (r : R) (x : MonoidAlgebra R G) : conjSum (r • x) = r • conjSum x := by
  simp only [conjSum, Finset.smul_sum, mul_smul_comm, smul_mul_assoc]

theorem conjSum_of_central (z : MonoidAlgebra R G) (hz : ∀ a, z * a = a * z) :
    conjSum z = Fintype.card G • z := by
  unfold conjSum
  have e : ∀ h : G, MonoidAlgebra.of R G h * z * MonoidAlgebra.of R G h⁻¹ = z := fun h => by
    rw [mul_assoc, hz, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  simp only [e, Finset.sum_const, Finset.card_univ]

theorem mapCoef_conjSum {S : Type} [CommRing S] (f : R →+* S) (w : MonoidAlgebra R G) :
    PairedCharacterCondition.mapCoef f (conjSum w) = conjSum (PairedCharacterCondition.mapCoef f w) := by
  show MonoidAlgebra.mapRingHom G f (conjSum w) = conjSum (MonoidAlgebra.mapRingHom G f w)
  simp only [conjSum, map_sum, map_mul, MonoidAlgebra.of_apply, MonoidAlgebra.mapRingHom_single, map_one]

theorem mapCoef_of {S : Type} [CommRing S] (f : R →+* S) (m : G) :
    PairedCharacterCondition.mapCoef f (MonoidAlgebra.of R G m) = MonoidAlgebra.of S G m := by
  show MonoidAlgebra.mapRingHom G f _ = _
  simp only [MonoidAlgebra.of_apply, MonoidAlgebra.mapRingHom_single, map_one]

theorem mapCoef_central {S : Type} [CommRing S] (f : R →+* S) (z : MonoidAlgebra R G)
    (hz : z ∈ Subalgebra.center R (MonoidAlgebra R G)) :
    PairedCharacterCondition.mapCoef f z ∈ Subalgebra.center S (MonoidAlgebra S G) := by
  rw [Subalgebra.mem_center_iff] at hz ⊢
  intro a
  induction a using MonoidAlgebra.induction_on with
  | of m =>
    rw [← mapCoef_of f m]
    show MonoidAlgebra.mapRingHom G f _ * MonoidAlgebra.mapRingHom G f _ =
      MonoidAlgebra.mapRingHom G f _ * MonoidAlgebra.mapRingHom G f _
    rw [← map_mul, ← map_mul, hz]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem mapCoef_smul {S : Type} [CommRing S] (f : R →+* S) (r : R) (x : MonoidAlgebra R G) :
    PairedCharacterCondition.mapCoef f (r • x) = f r • PairedCharacterCondition.mapCoef f x := by
  ext g
  simp [PairedCharacterCondition.mapCoef]

theorem mapCoef_add {S : Type} [CommRing S] (f : R →+* S) (x y : MonoidAlgebra R G) :
    PairedCharacterCondition.mapCoef f (x + y) = PairedCharacterCondition.mapCoef f x + PairedCharacterCondition.mapCoef f y :=
  map_add (MonoidAlgebra.mapRingHom G f) x y

end GroupAlg

section Forms

variable {D : D7}

theorem onMt_add (i : D.nd.Loc) {a b : MonoidAlgebra ℂ (G0g D.nd)}
    (ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))
    (hb : b ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) :
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (a + b) =
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i) a + D.ntypes.onMt (D.nd.mu i) (D.nd.j i) b := by
  unfold NTypes.onMt
  rw [dif_pos ha, dif_pos hb, dif_pos (add_mem ha hb), ← map_add]
  rfl

theorem onMt_smul (i : D.nd.Loc) (c : ℂ) {a : MonoidAlgebra ℂ (G0g D.nd)}
    (ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) :
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (c • a) = c • D.ntypes.onMt (D.nd.mu i) (D.nd.j i) a := by
  unfold NTypes.onMt
  rw [dif_pos ha, dif_pos (Subalgebra.smul_mem _ ha c), ← map_smul]
  rfl

theorem onMt_typeSum (hC : OnMtPreservesTypeV D) (i : D.nd.Loc) (z : MonoidAlgebra ℂ (G0g D.nd))
    (o : Option (D.nd.X i)) :
    typeSum D i o ≤ (typeSum D i o).comap (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) z) := by
  refine iSup₂_le fun P hP F hF => ?_
  exact Submodule.mem_comap.2 (le_biSup (D.naut.typeV i) hP (hC i P z F hF))

def ptPart (D : D7) (i : D.nd.Loc) : Submodule ℂ (D.what₂.Mt (D.nd.mu i) (D.nd.j i)) :=
  ⨆ (o : Option (D.nd.X i)) (_ : o ≠ none), typeSum D i o

theorem onMt_ptPart (hC : OnMtPreservesTypeV D) (i : D.nd.Loc) (z : MonoidAlgebra ℂ (G0g D.nd)) :
    ptPart D i ≤ (ptPart D i).comap (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) z) :=
  iSup₂_le fun o ho F hF => Submodule.mem_comap.2
    (Submodule.mem_iSup_of_mem o (Submodule.mem_iSup_of_mem ho (onMt_typeSum hC i z o hF)))

theorem Phi_mem {i : D.nd.Loc} (s : Sec D i) (w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) :
    s.Φ w ∈ ptPart D i := by
  have hw : w ∈ ⨆ x, heckeEig (D.nd.T i) (D.nd.act i) x := by
    rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.EigSpan_holds D.nd i]; exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun w => s.Φ w ∈ ptPart D i) hw
    (fun x v hv => ?_) (by rw [map_zero]; exact Submodule.zero_mem _)
    (fun v v' h h' => by rw [map_add]; exact Submodule.add_mem _ h h')
  exact Submodule.mem_iSup_of_mem (some x)
    (Submodule.mem_iSup_of_mem (Option.some_ne_none x) (s.eig x v hv))

theorem class_step (P : PairedCharacterCondition.Pend D) (hC : OnMtPreservesTypeV D) (i : D.nd.Loc) (s : Sec D i)
    (C : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))))
    (CL : MonoidAlgebra D.what₂.LL (G0g D.nd)) (hCL : ∀ a, CL * a = a * CL)
    (heq : PairedCharacterCondition.mapCoef D.what₂.embLL CL =
      PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (C : MonoidAlgebra (D.nd.O i) (G0g D.nd)))
    (w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) :
    s.Φ ((P.zO i C).baseChange (KK D.nd i) w) =
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (C : MonoidAlgebra (D.nd.O i) (G0g D.nd))) (s.Φ w) := by
  set T := D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
    (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (C : MonoidAlgebra (D.nd.O i) (G0g D.nd))) with hT
  have hw : w ∈ Submodule.span (KK D.nd i) (Set.range (D.nd.prMt i)) := by
    rw [D.nd.prMt_span i]; exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨y, rfl⟩ := hv
    obtain ⟨y', hy'⟩ := P.zL_stable i CL hCL y
    have hy2 : D.what₂.jMt _ _ y' = T (D.what₂.jMt _ _ y) := by rw [hy', heq]
    rw [← P.zO_act i C y y' hy2]
    have hind := (GlobalTheory.PendOf.PrTypeProof.typeSum_indep D i) none
    have h1 := s.split y
    have h2 := s.split y'
    have hA : s.Φ (D.nd.prMt i y') - T (s.Φ (D.nd.prMt i y)) =
        -((D.what₂.jMt _ _ y' - s.Φ (D.nd.prMt i y')) - T (D.what₂.jMt _ _ y - s.Φ (D.nd.prMt i y))) := by
      rw [map_sub T, ← hy2]; abel
    have m1 : s.Φ (D.nd.prMt i y') - T (s.Φ (D.nd.prMt i y)) ∈ typeSum D i none := by
      rw [hA]; exact Submodule.neg_mem _ (Submodule.sub_mem _ h2 (onMt_typeSum hC i _ none h1))
    have m2 : s.Φ (D.nd.prMt i y') - T (s.Φ (D.nd.prMt i y)) ∈ ptPart D i :=
      Submodule.sub_mem _ (Phi_mem s _) (onMt_ptPart hC i _ (Phi_mem s _))
    exact sub_eq_zero.1 ((Submodule.disjoint_def.1 hind) _ m1 m2)
  | zero => simp only [map_zero]
  | add v v' _ _ h h' => simp only [map_add, h, h']
  | smul a v _ h => rw [LinearMap.map_smul, s.semi, h, s.semi, LinearMap.map_smul]

end Forms

section Main

variable {D : D7}

theorem lhs_smul {i : D.nd.Loc} (s : Sec D i) (r : D.nd.O i) (f : Module.End (D.nd.O i) (D.nd.Mt i))
    (w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) :
    s.Φ ((r • f).baseChange (KK D.nd i) w) = iotaO D.nd D.naut i r • s.Φ (f.baseChange (KK D.nd i) w) := by
  rw [LinearMap.baseChange_smul, LinearMap.smul_apply, ← algebraMap_smul (KK D.nd i) r, s.semi]
  rfl

theorem all_central (P : PairedCharacterCondition.Pend D) (hC : OnMtPreservesTypeV D) (i : D.nd.Loc) (s : Sec D i)
    (z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))))
    (w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) :
    s.Φ ((P.zO i z).baseChange (KK D.nd i) w) =
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) (s.Φ w) := by
  classical
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  have hQ : ∀ v : MonoidAlgebra (D.nd.O i) (G0g D.nd), ∀ w,
      s.Φ ((P.zO i ⟨conjSum v, conjSum_mem_center v⟩).baseChange (KK D.nd i) w) =
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (conjSum v)) (s.Φ w) := by
    intro v
    induction v using MonoidAlgebra.induction_on with
    | of m =>
      intro w
      refine class_step P hC i s _ (conjSum (MonoidAlgebra.of D.what₂.LL _ m))
        (fun a => ((Subalgebra.mem_center_iff.1 (conjSum_mem_center _)) a).symm) ?_ w
      show _ = PairedCharacterCondition.mapCoef _ (conjSum _)
      rw [mapCoef_conjSum, mapCoef_conjSum, mapCoef_of, mapCoef_of]
    | add x y hx hy =>
      intro w
      have e : (⟨conjSum (x + y), conjSum_mem_center _⟩ :
          ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd)))) =
          ⟨conjSum x, conjSum_mem_center _⟩ + ⟨conjSum y, conjSum_mem_center _⟩ :=
        Subtype.ext (conjSum_add x y)
      rw [e, map_add, LinearMap.baseChange_add, LinearMap.add_apply, map_add, hx, hy, conjSum_add,
        mapCoef_add, onMt_add i (mapCoef_central _ _ (conjSum_mem_center _))
          (mapCoef_central _ _ (conjSum_mem_center _)), LinearMap.add_apply]
    | smul r x hx =>
      intro w
      have e : (⟨conjSum (r • x), conjSum_mem_center _⟩ :
          ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd)))) =
          r • ⟨conjSum x, conjSum_mem_center _⟩ :=
        Subtype.ext (conjSum_smul r x)
      rw [e, map_smul, lhs_smul, hx, conjSum_smul, mapCoef_smul,
        onMt_smul i _ (mapCoef_central _ _ (conjSum_mem_center _)), LinearMap.smul_apply]
  have hz : ∀ a, (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) * a = a * z :=
    fun a => ((Subalgebra.mem_center_iff.1 z.2) a).symm
  set n : D.nd.O i := (Fintype.card (G0g D.nd) : D.nd.O i) with hn
  have e : (⟨conjSum (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)), conjSum_mem_center _⟩ :
      ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd)))) = n • z := by
    apply Subtype.ext
    show conjSum (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) = _
    rw [conjSum_of_central _ hz, ← Nat.cast_smul_eq_nsmul (D.nd.O i)]
    rfl
  have h := hQ z w
  rw [e, map_smul, lhs_smul, hn, conjSum_of_central _ hz, ← Nat.cast_smul_eq_nsmul (D.nd.O i), mapCoef_smul,
    onMt_smul i _ (mapCoef_central _ _ z.2), LinearMap.smul_apply, map_natCast] at h
  have hne : ((Fintype.card (G0g D.nd) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  exact smul_right_injective _ hne h

theorem main : ∀ (D : D7) (P : PairedCharacterCondition.Pend D), (∀ i, Nonempty (Sec D i)) → OnMtPreservesTypeV D → EigSpan P := by
  intro D P hS hC i z x c hzc u hu
  let s := (hS i).some
  refine s.inj ?_
  have h1 := all_central P hC i s z u
  have h2 : D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) (s.Φ u) =
      iotaO D.nd D.naut i c • s.Φ u := by
    have hle : typeSum D i (some x) ≤ Module.End.eigenspace (D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)))) (iotaO D.nd D.naut i c) :=
      iSup₂_le fun PI hPI F hF => Module.End.mem_eigenspace_iff.2 (hzc PI hPI F hF)
    exact Module.End.mem_eigenspace_iff.1 (hle (s.eig x u hu))
  rw [h1, h2, ← algebraMap_smul (KK D.nd i) c u, s.semi]
  rfl

end Main

end GlobalTheory.PendOf.EigSpanProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfCommStatement
section
open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admALG_of_commG_var : ∀ D : D7, CommG D → IntegralHeckeForms.GroupAlgebraIntegrality D.nexp := by
  first | exact @GlobalTheory.IdemAlg.admALG_of_commG | exact GlobalTheory.IdemAlg.admALG_of_commG | (intros; apply GlobalTheory.IdemAlg.admALG_of_commG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIntegralPreservesLocalisedLatticeImageStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf Formalism.MainNotions.PairedCharacterCondition
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralIntegral_preserves_localisedLatticeImage : ∀ (D : D7) (i : D.nd.Loc) (S : Sec D i), (∀ a : 𝓞 D.what₂.LL, D.nd.embK i (a : D.what₂.LL) ∈ (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).range) → (∀ (c : MonoidAlgebra ℂ (G0g D.nd)) (x y : D.what₂.MtL (D.nd.mu i) (D.nd.j i)), D.what₂.jMt _ _ y = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (D.what₂.jMt _ _ x) → S.Φ (D.nd.prMt i y) = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (S.Φ (D.nd.prMt i x))) → CenInt D → ∀ (c : MonoidAlgebra ℤ (G0g D.nd)), (∀ a, c * a = a * c) → ∀ m : D.nd.Mt i, ∃ m' : D.nd.Mt i, S.Φ ((1 : KK D.nd i) ⊗ₜ[D.nd.O i] m') = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (mapCoef (Int.castRingHom ℂ) c) (S.Φ ((1 : KK D.nd i) ⊗ₜ[D.nd.O i] m)) := by
  first | exact @GlobalTheory.PendOf.CenLat.cenInt_lat | exact GlobalTheory.PendOf.CenLat.cenInt_lat | (intros; apply GlobalTheory.PendOf.CenLat.cenInt_lat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharactersDetectRestrictNormalInfFiniteLevel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem detects_restrictNormal_inf : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)] (r : ℕ) (N N' : Subgroup (GQ l))
    (I : Subgroup (L ≃ₐ[ℚ_[l]] L)) (ι : Type) (x : ι → Om l) (a : ι → GQ l → ℤ),
    (∀ i, x i ∈ Set.range (algebraMap L (Om l))) →
    (∀ i, ∀ σ ∈ N, ‖σ (x i) - x i - (a i σ : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ r) →
    (∀ σ ∈ N, (∀ i, (l : ℤ) ^ r ∣ a i σ) → σ ∈ N') →
    Detects l r (N.map (AlgEquiv.restrictNormalHom L) ⊓ I) (N'.map (AlgEquiv.restrictNormalHom L) ⊓ I) := by
  intro l _ L _ _ _ _ _ _ _ _ _ _ r N N' I ι x a hx hN hN'
  classical
  intro σ₀ hσ₀ hσ₀B

  let lift : (L ≃ₐ[ℚ_[l]] L) → GQ l := fun s =>
    if h : ∃ σ ∈ N, AlgEquiv.restrictNormalHom L σ = s then h.choose else 1
  have hlift : ∀ s ∈ N.map (AlgEquiv.restrictNormalHom L),
      lift s ∈ N ∧ AlgEquiv.restrictNormalHom L (lift s) = s := by
    intro s hs
    have h : ∃ σ ∈ N, AlgEquiv.restrictNormalHom L σ = s := Subgroup.mem_map.mp hs
    simp only [lift, dif_pos h]
    exact h.choose_spec
  obtain ⟨hτN, hτ⟩ := hlift σ₀ hσ₀.1
  have hτN' : lift σ₀ ∉ N' := by
    intro h
    exact hσ₀B ⟨Subgroup.mem_map.mpr ⟨lift σ₀, h, hτ⟩, hσ₀.2⟩
  have hex : ∃ i, ¬ (l : ℤ) ^ r ∣ a i (lift σ₀) := by
    by_contra hc
    push_neg at hc
    exact hτN' (hN' _ hτN hc)
  obtain ⟨i, hi⟩ := hex
  obtain ⟨x', hx'⟩ := hx i
  have hl0 : (l : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hlL : (l : L) ^ r ≠ 0 := by
    refine pow_ne_zero _ ?_
    rw [← map_natCast (algebraMap ℚ_[l] L)]
    exact (map_ne_zero _).mpr (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have hnorm_l : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
    have h : (l : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := by simp
    rw [h, PadicAlgCl.norm_extends, Padic.norm_p]
  refine ⟨x', fun s => a i (lift s), ?_, hi⟩
  intro s hs
  obtain ⟨hσN, hσ⟩ := hlift s hs.1
  have key : algebraMap L (Om l) (s x') = lift s (x i) := by
    rw [← hx']
    conv_lhs => rw [← hσ]
    exact AlgEquiv.restrictNormal_commutes (lift s) L x'
  refine ⟨(s x' - x' - (a i (lift s) : L)) / (l : L) ^ r, ?_, ?_⟩
  · refine ((GlobalTheory.T.localFieldInteger_iff_algebraicClosureNorm l L _).1).mpr ?_
    rw [map_div₀, map_sub, map_sub, map_intCast, map_pow, map_natCast, key, hx', norm_div, norm_pow, hnorm_l]
    rw [div_le_one (by positivity)]
    exact hN i _ hσN
  · rw [mul_div_cancel₀ _ hlL]
    ring

end GlobalTheory.PMon.Ram
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevInductionGrowBoundOfPresentationStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chebotarevInductionGrowBound_of_presentation : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), ThmS bkP → ∀ (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → Grow bkP i s := by
  first | exact @GlobalTheory.Growth.grow | exact GlobalTheory.Growth.grow | (intros; apply GlobalTheory.Growth.grow <;> assumption)
end

