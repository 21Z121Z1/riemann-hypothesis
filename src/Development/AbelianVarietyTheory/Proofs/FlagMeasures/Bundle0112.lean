import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.FormalDegreeBessel.Bundle0002
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0105
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRep
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.PiUnitary

open Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

theorem ellA_mul (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) {g h : Mat k r}
    (hg : col k r g) (hh : col k r h) (a : Fin r) :
    ellA k r z (g * h) a = ellA k r z g a + ellA k r z h a := by
  unfold ellA
  by_cases ha : a.val + 1 < r
  · rw [dif_pos ha, dif_pos ha, dif_pos ha]
    exact mul_apply_add hg hh _ _ (by simp only [eI]; omega) (by simp only [eI]; omega)
      (by simp only [eI]; omega) (by simp only [eI]; omega)
  · rw [dif_neg ha, dif_neg ha, dif_neg ha]
    simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hzj : z j = 0
    · rw [hzj, mul_zero, mul_zero, mul_zero, add_zero]
    · have hjW : r ≤ j.val ∧ j.val ≤ r + k := by
        by_contra hc
        apply hzj
        apply hz
        omega
      rw [mul_apply_add hg hh _ _ (by simp only [eI]; omega) (by omega)
        (by simp only [eI]; omega) (by simp only [eI]; omega), add_mul]

theorem psiGen_mul_N (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (hz : inWb k r z) {g h : Mat k r}
    (hg : g ∈ Nset k r) (hh : h ∈ Nset k r) :
    psiGen k r z c (g * h) = psiGen k r z c g * psiGen k r z c h := by
  have hs : (∑ a, c a * ellA k r z (g * h) a) =
      (∑ a, c a * ellA k r z g a) + ∑ a, c a * ellA k r z h a := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [ellA_mul z hz ((nset_iff g).1 hg).2 ((nset_iff h).1 hh).2 a, mul_add]
  unfold psiGen
  rw [hs, Complex.add_re, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem norm_psiGen (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (g : Mat k r) :
    ‖psiGen k r z c g‖ = 1 := by
  unfold psiGen
  rw [mul_comm Complex.I]
  exact Complex.norm_exp_ofReal_mul_I _

theorem ellA_block (z : Fin (2 * r + k + 1) → ℂ) {h h' g : Mat k r}
    (hh : block k r h) (hh' : block k r h') (hz : h' *ᵥ z = z) (a : Fin r) :
    ellA k r z (h * g * h') a = ellA k r z g a := by
  unfold ellA
  have hrow : ∀ p, h (eI k r a) p = if eI k r a = p then 1 else 0 :=
    fun p => hh.2 _ p (by simp only [eI]; omega)
  by_cases ha : a.val + 1 < r
  · rw [dif_pos ha, dif_pos ha, mul_apply_of_col _ _ _ (fun q => hh'.1 q _ (by simp only [eI]; omega)),
      mul_apply_of_row _ _ _ hrow]
  · rw [dif_neg ha, dif_neg ha, ← Matrix.mulVec_mulVec, hz, ← Matrix.mulVec_mulVec,
      mulVec_apply_of_row _ _ hrow]

theorem psiGen_block (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) {h h' g : Mat k r}
    (hh : block k r h) (hh' : block k r h') (hz : h' *ᵥ z = z) :
    psiGen k r z c (h * g * h') = psiGen k r z c g := by
  simp only [psiGen, ellA_block z hh hh' hz]

theorem block_one : block k r (1 : Mat k r) :=
  ⟨fun _ _ _ => Matrix.one_apply, fun _ _ _ => Matrix.one_apply⟩

theorem psiGen_uw_mul (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) {h g : Mat k r}
    (hh : h ∈ UWset k r z) : psiGen k r z c (h * g) = psiGen k r z c g := by
  have := psiGen_block (g := g) z c (uw_block hh) block_one (Matrix.one_mulVec z)
  rwa [Matrix.mul_one] at this

theorem ellA_continuous (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    Continuous (fun g : Mat k r => ellA k r z g a) := by
  by_cases h : a.val + 1 < r
  · have e : (fun g : Mat k r => ellA k r z g a) =
        fun g => g (eI k r a) (eI k r ⟨a.val + 1, h⟩) := by
      funext g; unfold ellA; rw [dif_pos h]
    rw [e]
    exact (continuous_apply _).comp (continuous_apply _)
  · have e : (fun g : Mat k r => ellA k r z g a) = fun g => (g *ᵥ z) (eI k r a) := by
      funext g; unfold ellA; rw [dif_neg h]
    rw [e]
    exact (continuous_apply (eI k r a)).comp
      (continuous_id.matrix_mulVec continuous_const : Continuous fun g : Mat k r => g *ᵥ z)

theorem psiGen_continuous (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) :
    Continuous (psiGen k r z c) := by
  unfold psiGen
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_finsetSum _ fun a _ =>
      continuous_const.mul (ellA_continuous z a)))))

theorem block_entry {h : Mat k r} (hh : block k r h) {i j : Fin (2 * r + k + 1)}
    (H : ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k))) :
    h i j = if i = j then 1 else 0 := by
  by_cases hj : j.val < r ∨ r + k < j.val
  · exact hh.1 i j hj
  · exact hh.2 i j (by omega)

theorem hPart_mul {z : Fin (2 * r + k + 1) → ℂ} {h m : Mat k r} (hh : h ∈ UWset k r z)
    (hm : m ∈ Nset k r) : hPart k r (h * m) = h := by
  have hb := uw_block hh
  have hc := ((nset_iff m).1 hm).2
  ext i j
  unfold hPart
  by_cases H1 : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)
  · rw [if_pos H1]
    exact block_mul_col hb hc i j H1.2.2 (Or.inr H1.1.1)
  · rw [if_neg H1, block_entry hb H1]

theorem PiS_mul {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (ψ : Mat k r → ℂ)
    (π : Mat k r → (Wp →L[ℂ] Wp)) {z : Fin (2 * r + k + 1) → ℂ} {h m : Mat k r}
    (hh : h ∈ UWset k r z) (hm : m ∈ Nset k r) : PiS ψ π (h * m) = ψ m • π h := by
  unfold PiS
  rw [hPart_mul hh hm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_of_uh hh.1), Matrix.one_mul]

theorem hPart_continuous : Continuous (hPart k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun s : Mat k r => hPart k r s i j
  by_cases H1 : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)
  · simp only [hPart, if_pos H1]
    exact (continuous_apply j).comp (continuous_apply i)
  · simp only [hPart, if_neg H1]
    exact continuous_const

theorem adjoint_eq_of_isometry {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A B : E →L[ℂ] E) (hA : ∀ v, ‖A v‖ = ‖v‖) (hAB : A.comp B = 1) :
    ContinuousLinearMap.adjoint A = B := by
  have h1 : (ContinuousLinearMap.adjoint A).comp A = 1 := (A.norm_map_iff_adjoint_comp_self).1 hA
  ext v
  have e1 := congrArg (fun T : E →L[ℂ] E => T (B v)) h1
  have e2 := congrArg (fun T : E →L[ℂ] E => T v) hAB
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at e1 e2
  rw [e2] at e1
  exact e1

end GlobalTheory.SgInf.PiUnitary

namespace GlobalTheory.SgInf.PiUnitary

open Formalism.QuantumDeterminants.WeylGroupFacts

theorem piS_unitary : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (π : Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → IsURepOn (UWset k r z) π →
    (∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, hPart k r (h * m) = h ∧
        PiS (psiGen k r z c) π (h * m) = psiGen k r z c m • π h) ∧
      IsURepOn (Sset k r z) (PiS (psiGen k r z c) π) ∧
      (∀ s ∈ Sset k r z, ‖PiS (psiGen k r z c) π s‖ ≤ 1 ∧
        ContinuousLinearMap.adjoint (PiS (psiGen k r z c) π s) = PiS (psiGen k r z c) π s⁻¹) ∧
      ContinuousOn (PiS (psiGen k r z c) π) (Sset k r z) ∧
      (∀ m ∈ Nset k r, ‖psiGen k r z c m‖ = 1 ∧
        ∀ m' ∈ Nset k r, psiGen k r z c (m * m') = psiGen k r z c m * psiGen k r z c m') := by
  intro k r Wp _ _ _ _ z c π hz _ hπ
  have hchar : ∀ m ∈ Nset k r, ‖(psiGen k r z c) m‖ = 1 ∧ ∀ m' ∈ Nset k r, (psiGen k r z c) (m * m') = (psiGen k r z c) m * (psiGen k r z c) m' :=
    fun m hm => ⟨norm_psiGen z c m, fun m' hm' => psiGen_mul_N z c hz hm hm'⟩
  have hpsi1 : (psiGen k r z c) 1 = 1 := by
    have e := psiGen_mul_N z c hz (mem_n_one (k := k) (r := r)) (mem_n_one (k := k) (r := r))
    rw [Matrix.one_mul] at e
    have hne : (psiGen k r z c) 1 ≠ 0 := by
      intro h0
      have := norm_psiGen (k := k) (r := r) z c 1
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have e' : (psiGen k r z c) 1 * 1 = (psiGen k r z c) 1 * (psiGen k r z c) 1 := by rw [mul_one]; exact e
    exact (mul_left_cancel₀ hne e').symm
  have hrep : IsURepOn (Sset k r z) (PiS (psiGen k r z c) π) := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [PiS_one, hpsi1, one_smul]
      exact hπ.1.1
    · rintro _ ⟨h, hh, m, hm, rfl⟩ _ ⟨h', hh', m', hm', rfl⟩
      have hu' := isUnit_of_uh hh'.1
      have hn : h'⁻¹ * m * h' ∈ Nset k r := by
        have := (uWNormal k r z hz h'⁻¹ (uw_inv hh') m hm).1
        rwa [Matrix.nonsing_inv_nonsing_inv _ hu'] at this
      have e : h * m * (h' * m') = (h * h') * ((h'⁻¹ * m * h') * m') := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc h' h'⁻¹, Matrix.mul_nonsing_inv _ hu', Matrix.one_mul]
      rw [e, PiS_mul (psiGen k r z c) π (uw_mul hh hh') (mem_n_mul hn hm'), PiS_mul (psiGen k r z c) π hh hm, PiS_mul (psiGen k r z c) π hh' hm',
        psiGen_mul_N z c hz hn hm',
        psiGen_block z c (uw_block (uw_inv hh')) (uw_block hh') hh'.2.2, hπ.1.2 h hh h' hh',
        ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]
    · rintro _ ⟨h, hh, m, hm, rfl⟩ v
      rw [PiS_mul (psiGen k r z c) π hh hm, ContinuousLinearMap.smul_apply, norm_smul, norm_psiGen, one_mul,
        hπ.2.1 h hh v]
    · intro v
      have hmaps : Set.MapsTo (hPart k r) (Sset k r z) (UWset k r z) := by
        rintro _ ⟨h, hh, m, hm, rfl⟩
        rw [hPart_mul hh hm]
        exact hh
      have hc : ContinuousOn (fun s => (psiGen k r z c) s • π (hPart k r s) v) (Sset k r z) :=
        (psiGen_continuous z c).continuousOn.smul
          ((hπ.2.2 v).comp hPart_continuous.continuousOn hmaps)
      refine hc.congr ?_
      rintro _ ⟨h, hh, m, hm, rfl⟩
      show PiS (psiGen k r z c) π (h * m) v = (psiGen k r z c) (h * m) • π (hPart k r (h * m)) v
      rw [PiS_mul (psiGen k r z c) π hh hm, hPart_mul hh hm, psiGen_uw_mul z c hh, ContinuousLinearMap.smul_apply]
  have hiso : ∀ s ∈ Sset k r z, ∀ v, ‖PiS (psiGen k r z c) π s v‖ = ‖v‖ := hrep.2.1
  refine ⟨fun h hh m hm => ⟨hPart_mul hh hm, PiS_mul (psiGen k r z c) π hh hm⟩, hrep, fun s hs => ⟨?_, ?_⟩, ?_, hchar⟩
  · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [hiso s hs v, one_mul]
  · apply adjoint_eq_of_isometry _ _ (hiso s hs)
    have hsU : s ∈ UH (Hpk k r) := by
      obtain ⟨h, hh, m, hm, rfl⟩ := hs
      exact uh_mul hh.1 hm.1
    have hsi : s⁻¹ ∈ Sset k r z := (sGroup k r z hz).2.2 s hs
    rw [← hrep.1.2 s hs s⁻¹ hsi, Matrix.mul_nonsing_inv _ (isUnit_of_uh hsU)]
    exact hrep.1.1
  · exact continuousOn_clm_apply.2 hrep.2.2

end GlobalTheory.SgInf.PiUnitary

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf in
example : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → IsURepOn (UWset k r z) π → (∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, hPart k r (h * m) = h ∧ PiS (psiGen k r z c) π (h * m) = psiGen k r z c m • π h) ∧ IsURepOn (Sset k r z) (PiS (psiGen k r z c) π) ∧ (∀ s ∈ Sset k r z, ‖PiS (psiGen k r z c) π s‖ ≤ 1 ∧ ContinuousLinearMap.adjoint (PiS (psiGen k r z c) π s) = PiS (psiGen k r z c) π s⁻¹) ∧ ContinuousOn (PiS (psiGen k r z c) π) (Sset k r z) ∧ (∀ m ∈ Nset k r, ‖psiGen k r z c m‖ = 1 ∧ ∀ m' ∈ Nset k r, psiGen k r z c (m * m') = psiGen k r z c m * psiGen k r z c m') := GlobalTheory.SgInf.PiUnitary.piS_unitary
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardInnerLatticesWithDefiniteTraceLeNorm
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt.GlueZ

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem star_mem {t : K} (h : t ∈ (1 : Submodule (𝓞 K) K)) : star t ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.1 h
  have h1 : IsIntegral ℤ (star (algebraMap (𝓞 K) K a)) :=
    map_isIntegral_int (starRingEnd K) a.isIntegral_coe
  exact Submodule.mem_one.2 ⟨⟨_, h1⟩, rfl⟩

def Good (H : HermSpace K V) (S : Submodule K V) (z : V) (M : Submodule (𝓞 K) V) : Prop :=
  dual H M = M ∧ Submodule.span K (M : Set V) = S ∧ ∀ t : K, t • z ∈ M ↔ t ∈ (1 : Submodule (𝓞 K) K)

variable {H : HermSpace K V} {S : Submodule K V} {z : V} {M : Submodule (𝓞 K) V}

theorem Good.z_mem (h : Good H S z M) : z ∈ M := by
  simpa using (h.2.2 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)

theorem Good.int (h : Good H S z M) {x y : V} (hx : x ∈ M) (hy : y ∈ M) :
    H.B x y ∈ (1 : Submodule (𝓞 K) K) :=
  ((mem_dual_iff H M x).1 (h.1.symm ▸ hx)).2 y hy

theorem Good.mem_S (h : Good H S z M) {x : V} (hx : x ∈ M) : x ∈ S :=
  h.2.1 ▸ Submodule.subset_span hx

theorem Good.mem_of (h : Good H S z M) {x : V} (hx : x ∈ S)
    (hB : ∀ y ∈ M, H.B x y ∈ (1 : Submodule (𝓞 K) K)) : x ∈ M :=
  h.1 ▸ (mem_dual_iff H M x).2 ⟨h.2.1.symm ▸ hx, hB⟩

theorem Good.exists_one (h : Good H S z M) (hz : H.B z z ≠ 0) : ∃ y ∈ M, H.B y z = 1 := by
  let J : Ideal (𝓞 K) :=
    (M.map ((H.B.flip z).restrictScalars (𝓞 K))).comap (Algebra.linearMap (𝓞 K) K)
  have hJ : ∀ a : 𝓞 K, a ∈ J ↔ ∃ y ∈ M, H.B y z = algebraMap (𝓞 K) K a := fun a => by
    simp [J]
  have hne : J ≠ ⊥ := by
    intro h0
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h.int h.z_mem h.z_mem)
    have : a ∈ J := (hJ a).2 ⟨z, h.z_mem, ha.symm⟩
    rw [h0, Ideal.mem_bot] at this
    exact hz (by rw [← ha, this, map_zero])
  have htop : J = ⊤ := by
    by_contra hJ1
    obtain ⟨x, hx, hx1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := K) hne hJ1
    apply hx1
    rw [FractionalIdeal.mem_inv_iff (by simpa using hne)] at hx
    have h2 : star x • z ∈ M := by
      refine h.mem_of (S.smul_mem _ (h.mem_S h.z_mem)) fun y hy => ?_
      obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h.int hy h.z_mem)
      have h3 := hx (algebraMap (𝓞 K) K a)
        (FractionalIdeal.mem_coeIdeal_of_mem _ ((hJ a).2 ⟨y, hy, ha.symm⟩))
      have h4 : x * algebraMap (𝓞 K) K a ∈ (1 : Submodule (𝓞 K) K) := by
        obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 h3
        exact Submodule.mem_one.2 ⟨b, hb⟩
      have h5 := star_mem h4
      rw [ha, star_mul', H.herm] at h5
      simpa using h5
    have h6 := star_mem ((h.2.2 _).1 h2)
    rw [star_star] at h6
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 h6
    exact (FractionalIdeal.mem_one_iff _).2 ⟨b, hb⟩
  obtain ⟨y, hy, e⟩ := (hJ 1).1 (htop ▸ Submodule.mem_top)
  exact ⟨y, hy, by rw [e, map_one]⟩

theorem Good.proj (h : Good H S z M) {y m : V} (hy : y ∈ M) (hy1 : H.B y z = 1) (hm : m ∈ M) :
    ∃ a : 𝓞 K, m - a • y ∈ M ∧ H.B (m - a • y) z = 0 := by
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h.int hm h.z_mem)
  refine ⟨a, M.sub_mem hm (M.smul_mem a hy), ?_⟩
  rw [← algebraMap_smul K a y, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hy1, ← ha]
  simp

theorem count (T : ℕ) (hT : T ≠ 0) (hz : H.B z z = -(T : K)) (M₁ : Submodule (𝓞 K) V) (h₁ : Good H S z M₁) :
    {M : Submodule (𝓞 K) V | Good H S z M ∧ ∀ y, H.B y z = 0 → (y ∈ M ↔ y ∈ M₁)}.encard ≤
      (T ^ Module.finrank ℚ K : ℕ) := by
  have hz0 : H.B z z ≠ 0 := by rw [hz]; simpa using hT
  obtain ⟨y₁, hy₁, e₁⟩ := h₁.exists_one hz0
  have e₁' : H.B z y₁ = 1 := by rw [← H.herm, e₁, star_one]
  set 𝓢 := {M : Submodule (𝓞 K) V | Good H S z M ∧ ∀ y, H.B y z = 0 → (y ∈ M ↔ y ∈ M₁)} with h𝓢
  have key : ∀ M : Submodule (𝓞 K) V, ∃ (y : V) (u : K) (a : 𝓞 K), M ∈ 𝓢 →
      y ∈ M ∧ H.B y z = 1 ∧ y + u • z ∈ M₁ ∧ algebraMap (𝓞 K) K a = 1 - u * T := by
    intro M
    by_cases hM : M ∈ 𝓢
    swap
    · exact ⟨0, 0, 0, fun h => absurd h hM⟩
    obtain ⟨y, hy, e⟩ := hM.1.exists_one hz0
    have hm : y + (-H.B y y₁) • z ∈ M₁ := by
      refine h₁.mem_of (S.add_mem (hM.1.mem_S hy) (S.smul_mem _ (h₁.mem_S h₁.z_mem))) fun m hm => ?_
      obtain ⟨a, ha, ha0⟩ := h₁.proj hy₁ e₁ hm
      have h2 := hM.1.int hy ((hM.2 _ ha0).2 ha)
      have h3 : H.B z (m - a • y₁) = 0 := by rw [← H.herm, ha0, star_zero]
      have h4 : m = (m - a • y₁) + (algebraMap (𝓞 K) K a) • y₁ := by rw [algebraMap_smul]; abel
      generalize m - a • y₁ = m₀ at h2 h3 h4
      rw [h4]
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, h3, e₁',
        smul_eq_mul]
      convert h2 using 1
      ring
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h₁.int hm h₁.z_mem)
    refine ⟨y, -H.B y y₁, a, fun _ => ⟨hy, e, hm, ?_⟩⟩
    rw [ha, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, e, hz, smul_eq_mul]
    ring
  choose y u a hyu using key
  let I : Ideal (𝓞 K) := Ideal.span {(T : 𝓞 K)}
  have hle : ∀ M ∈ 𝓢, ∀ M' ∈ 𝓢, Ideal.Quotient.mk I (a M) = Ideal.Quotient.mk I (a M') → M ≤ M' := by
    intro M hM M' hM' e
    obtain ⟨p1, p2, p3, p4⟩ := hyu M hM
    obtain ⟨q1, q2, q3, q4⟩ := hyu M' hM'
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 e)
    have hb' : algebraMap (𝓞 K) K b = u M' - u M := by
      have := congrArg (algebraMap (𝓞 K) K) hb
      rw [map_sub, map_mul, map_natCast, p4, q4] at this
      have hT' : (T : K) ≠ 0 := by exact_mod_cast hT
      apply mul_right_cancel₀ hT'
      rw [this]; ring
    have h5 : y M - y M' ∈ M₁ := by
      have := M₁.add_mem (M₁.sub_mem p3 q3) (M₁.smul_mem b h₁.z_mem)
      rw [← algebraMap_smul K b z, hb', sub_smul] at this
      convert this using 1
      abel
    have h6 : H.B (y M - y M') z = 0 := by rw [map_sub, LinearMap.sub_apply, p2, q2, sub_self]
    have h7 : y M ∈ M' := by simpa using M'.add_mem ((hM'.2 _ h6).2 h5) q1
    intro m hm
    obtain ⟨c, hc, hc0⟩ := hM.1.proj p1 p2 hm
    simpa using M'.add_mem ((hM'.2 _ hc0).2 ((hM.2 _ hc0).1 hc)) (M'.smul_mem c h7)
  have hI : I ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hT
  haveI : Finite (𝓞 K ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  have h8 : 𝓢.encard ≤ (Set.univ : Set (𝓞 K ⧸ I)).encard :=
    Set.encard_le_encard_of_injOn (f := fun M => Ideal.Quotient.mk I (a M)) (fun _ _ => Set.mem_univ _)
      fun M hM M' hM' e => le_antisymm (hle M hM M' hM' e) (hle M' hM' M hM e.symm)
  refine h8.trans (le_of_eq ?_)
  rw [Set.encard_univ, ENat.card_eq_coe_natCard, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
    Ideal.absNorm_span_natCast, RingOfIntegers.rank]

theorem mem_lattice_zeroTorus {r : ℕ} (N : NF H r) (Λ : Submodule (𝓞 K) V) (y : V) (hy : H.B y N.F'.z = 0) :
    y ∈ latL N.F' N.F Λ ↔ y ∈ flagPairDefinitePartLattice N.F' N.F Λ := by
  refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
  have hc : star N.c ≠ 0 := by
    intro h0
    have := N.c_norm
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have e : N.F'.z = N.c • N.F.z := N.same (Fin.last r) N.j_le
  have hy2 : H.B y N.F.z = 0 := by
    rw [e, LinearMap.map_smulₛₗ, smul_eq_mul] at hy
    exact (mul_eq_zero.1 hy).resolve_left hc
  have h1 : ∀ x ∈ N.F'.X ⊔ N.F.X, H.B y x = 0 := (mem_perp_iff H _ y).1 h.1
  refine (mem_perp_iff H _ y).2 fun x hx => ?_
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hq
  simp [h1 p hp, hy, hy2, LinearMap.map_smulₛₗ]

end GlobalTheory.DegCnt.GlueZ

theorem GlobalTheory.DegCnt.GlueZ.main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ((({L' : Submodule (𝓞 K) V | ∃ Λ', N.IsTerm g Λ' ∧ L' = latL N.F' N.F Λ' ∧ flagPairDefinitePartLattice N.F' N.F Λ' = flagPairDefinitePartLattice N.F' N.F Λ}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (N.NT ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  have good : ∀ Λ', N.IsTerm g Λ' → GlueZ.Good H (uPerp N.F N.F') N.F'.z (latL N.F' N.F Λ') := fun Λ' h => by
    obtain ⟨-, h2, -, h4, -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ' hg h
    exact ⟨h2.2, h2.1.2, h4⟩
  have hT : N.T ≠ 0 := by
    intro h0
    apply N.F'.hT
    rw [N.hT', h0, Nat.cast_zero]
  have hz : H.B N.F'.z N.F'.z = -(N.T : K) := N.hT' ▸ N.F'.zz
  have h1 := GlueZ.count N.T hT hz _ (good Λ hΛ)
  have h2 : {L' : Submodule (𝓞 K) V | ∃ Λ', N.IsTerm g Λ' ∧ L' = latL N.F' N.F Λ' ∧
      flagPairDefinitePartLattice N.F' N.F Λ' = flagPairDefinitePartLattice N.F' N.F Λ}.encard ≤ (N.T ^ Module.finrank ℚ K : ℕ) := by
    refine (Set.encard_le_encard ?_).trans h1
    rintro _ ⟨Λ', h, rfl, e⟩
    exact ⟨good Λ' h, fun y hy => by rw [GlueZ.mem_lattice_zeroTorus N Λ' y hy, GlueZ.mem_lattice_zeroTorus N Λ y hy, e]⟩
  haveI := hK.1
  have h3 : Module.finrank ℚ K = Formalism.HermitianLatticesTheory.fDeg K * 2 := by
    rw [IsTotallyComplex.finrank, Formalism.HermitianLatticesTheory.fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero]
    ring
  refine (ENat.toENNReal_le.2 h2).trans (le_of_eq ?_)
  rw [NF.NT, ← pow_mul, ← h3, ← Nat.cast_pow, ENNReal.ofReal_natCast]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjLinearOfGramEqStatement
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjLinear_of_gram_eq' : ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (M : Type) [AddCommGroup M] [Module ℂ M] (N : M → M → ℂ) (I : Type) (a : I → W) (b : I → M), (∀ p p' q, N (p + p') q = N p q + N p' q) → (∀ (c : ℂ) p q, N (c • p) q = c * N p q) → (∀ p q, N q p = star (N p q)) → (∀ p, N p p = 0 → p = 0) → Submodule.span ℂ (Set.range a) = ⊤ → (∀ i j, N (b j) (b i) = ⟪a j, a i⟫_ℂ) → ∃ Jm : W →ₗ⋆[ℂ] M, (∀ i, Jm (a i) = b i) ∧ ∀ ξ η, N (Jm η) (Jm ξ) = ⟪η, ξ⟫_ℂ := by
  first | exact @GlobalTheory.exists_conjLinear_of_gram_eq | exact GlobalTheory.exists_conjLinear_of_gram_eq | (intros; apply GlobalTheory.exists_conjLinear_of_gram_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FewOrbitsSubspacesHermitianLatticeDiscriminantStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.few_orbits_subspaces_hermitian_lattice_discriminant : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) → ∀ (j n : ℕ), 1 ≤ n → ∃ s : Finset (Submodule K V), (s.card : ℝ) ≤ (n : ℝ) ^ (1 + Real.logb 2 (Module.finrank ℚ K)) ∧ (∀ U ∈ s, Module.finrank K U = j) ∧ ∀ U : Submodule K V, Module.finrank K U = j → (latsDisc (R := 𝓞 K) (hRes h U) n).Nonempty → ∃ U₀ ∈ s, ∃ g : isom h, g • U₀ = U := by
  first | exact @GlobalTheory.Mass.FewOrbits.main | exact GlobalTheory.Mass.FewOrbits.main | (intros; apply GlobalTheory.Mass.FewOrbits.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagCoefIntegralOfLocalIntegral
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

namespace GlobalTheory.FlagCoef

theorem coef_integral_of_flag {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
    (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {T : E} (F : LFlag S r T) (hc : IsFixedConv Λ g F)
    (j : ℕ) (x : S.V) (hx : x ∈ Xflag F j)
    (hP : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal →
      x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) :
    ∃ w : Fin r → E, x = ∑ c, w c • F.fl.e c ∧ (∀ c : Fin r, j ≤ c.val → w c = 0) ∧
      ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ c, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧
        ∃ o : 𝓞 E, (s : E) * w c = o := by
  classical
  have hxa : x ∈ Submodule.span E (F.fl.e '' {i | i.1 < j}) := hx
  obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination E).1 hxa

  have hxw : x = ∑ i, l i • F.fl.e i := by
    rw [← hlx, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i
    simp
  refine ⟨fun c => l c, hxw, ?_, ?_⟩
  · intro c hc
    by_contra h
    have hmem : c.val < j := hl (Finsupp.mem_support_iff.2 h)
    omega
  · intro P hgP c
    have := P.isPrime
    have key : ∀ {L : Submodule (𝓞 E) S.V} {y : S.V},
        y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L ↔ ∃ u ∈ P.asIdeal.primeCompl, u • y ∈ L := Iff.rfl

    obtain ⟨s, hs, hsx⟩ := key.1 (hP P hgP)
    have hxX : x ∈ Submodule.span E (Set.range F.fl.e) :=
      Submodule.span_mono (Set.image_subset_range _ _) hxa
    have hsX : s • x ∈ Formalism.MainNotions.S.Lat.XLam Λ F := by
      refine Submodule.mem_inf.2 ⟨hsx, ?_⟩
      exact Submodule.smul_of_tower_mem _ s hxX

    obtain ⟨cc, -, hc1, heq⟩ := hc.1 P
    have hloc : s • x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.MainNotions.S.Lat.XLam Λ F) :=
      key.2 ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hsX⟩
    have hfun : (fun a => cc a • F.fl.e a) = F.fl.e :=
      funext fun a => by rw [hc1 hgP a, one_smul]
    rw [heq, hfun] at hloc
    obtain ⟨t, ht, htx⟩ := key.1 hloc
    obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 htx
    have h1 : ∑ i, ((o i : 𝓞 E) : E) • F.fl.e i = t • s • x := by
      rw [← ho]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact algebraMap_smul E (o i) (F.fl.e i)
    have h2 : t • s • x = ∑ i, (((t * s : 𝓞 E) : E) * l i) • F.fl.e i := by
      rw [← mul_smul, ← algebraMap_smul E (t * s) x, hxw, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul]
    have hsum : ∑ i, (((o i : 𝓞 E) : E) - ((t * s : 𝓞 E) : E) * l i) • F.fl.e i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, h1, ← h2, sub_self]
    have hc0 := Fintype.linearIndependent_iff.1 F.fl.e_indep _ hsum c
    exact ⟨t * s, P.asIdeal.primeCompl.mul_mem ht hs, o c, (sub_eq_zero.1 hc0).symm⟩

end GlobalTheory.FlagCoef
end

