import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0198
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0197
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0066
import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0199
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0179
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0189

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HomLatticeCovolumeEmbeddingFamilyStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homLatticeCovolume_embedding_family : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (ι : Type) [Fintype ι] (φ : ι → E →+* ℂ), Function.Bijective (fun v => InfinitePlace.mk (φ v)) → ∀ (r s : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E)) (Λ' : Submodule (𝓞 E) (Fin s → E)), Submodule.IsLattice E Λ → Submodule.IsLattice E Λ' → ∀ (G : ι → Matrix (Fin r) (Fin r) ℂ) (G' : ι → Matrix (Fin s) (Fin s) ℂ), (∀ v, (G v).det ≠ 0) → (∀ v, (G' v).det ≠ 0) → ∀ L : Submodule ℤ (ι → Fin r → Fin s → ℂ), (∀ z, z ∈ L ↔ ∃ T : Matrix (Fin r) (Fin s) E, (∀ y ∈ Λ', T *ᵥ y ∈ Λ) ∧ ∀ v, Matrix.of (z v) = G v * T.map (φ v) * (G' v)⁻¹) → ∃ _ : DiscreteTopology L, IsZLattice ℝ L ∧ ZLattice.covolume L volume = (covStd r Λ * ∏ v, ‖(G v).det‖ ^ 2) ^ s * (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * s) / (covStd s Λ' * ∏ v, ‖(G' v).det‖ ^ 2)) ^ r := by
  first | exact @GlobalTheory.HomCovolumeFamily.homCovolume_family | exact GlobalTheory.HomCovolumeFamily.homCovolume_family | (intros; apply GlobalTheory.HomCovolumeFamily.homCovolume_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IintEquivariantStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.Iint_equivariant_alt : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ (x y : H) (ξ : Wp) (ξ' : Wq) (Om Om' : Set (Mt k r)), MeasurableSet Om → MeasurableSet Om' → ∀ γ ∈ GG k r, ∀ t ∈ Sset k r z, ∀ t' ∈ Sset k r z', Iint (psiGen k r z c) (psiGen k r z' c') π π' (μS.restrict Om) (μS'.restrict Om') σ x y ξ ξ' (t * γ * t'⁻¹) = (PiS (psiGen k r z c) π t).comp ((Iint (psiGen k r z c) (psiGen k r z' c') π π' (μS.restrict (rmulM t '' Om)) (μS'.restrict (rmulM t' '' Om')) σ x y ξ ξ' γ).comp (PiS (psiGen k r z' c') π' t'⁻¹)) := by
  first | exact @GlobalTheory.SgInf.Equivar.Iint_equivariant | exact GlobalTheory.SgInf.Equivar.Iint_equivariant | (intros; apply GlobalTheory.SgInf.Equivar.Iint_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InfiniteGLHaarMeasureEqPiLocalStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infiniteGLHaarMeasure_eq_pi_local : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ), haarGL E j = (Measure.pi fun _ : InfinitePlace E => haarLoc j : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) := by
  first | exact @GlobalTheory.HaarPi.haarGL_eq_pi | exact GlobalTheory.HaarPi.haarGL_eq_pi | (intros; apply GlobalTheory.HaarPi.haarGL_eq_pi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InfiniteLatticeCovolumeSplitLatticeProdStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infiniteLatticeCovolume_split_lattice_prod : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (k : ℕ) (Λ : Submodule (𝓞 E) (Fin (k + 1) → E)) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), Submodule.IsLattice E Λ₀ → Submodule.IsLattice E Λ' → (∀ y, y ∈ Λ ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ') → covAt E (k + 1) (latAt E (k + 1) Λ (oneInf E (k + 1))) = covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) * covAt E k (latAt E k Λ' (oneInf E k)) := by
  first | exact @GlobalTheory.CovProd.covAt_latAt_prod | exact GlobalTheory.CovProd.covAt_latAt_prod | (intros; apply GlobalTheory.CovProd.covAt_latAt_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvLeSizeQAboveOrthogonalSaturatedStatement
section
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_le_sizeQ_above_orthogonal_saturated : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hi : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → ∀ N, perpIn I x R < N → N ≤ lamX I x → hi⁻¹ ≤ sizeQ (bas I) (frm I x) N (perpIn I x R) := by
  first | exact @GlobalTheory.Count.PerpSize.inv_le_sizeQ_perp | exact GlobalTheory.Count.PerpSize.inv_le_sizeQ_perp | (intros; apply GlobalTheory.Count.PerpSize.inv_le_sizeQ_perp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeLatIn
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S IsDedekindDomain
open scoped ENNReal Classical

namespace GlobalTheory.Mass.DetAgree

section
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]

theorem genIdxH_eq_idxN {A B : Submodule (𝓞 K) V} (hBA : B ≤ A) (h0 : idxN A B ≠ 0) :
    Lat.genIdxH A B = (idxN A B : ℝ) := by
  obtain ⟨k, hk, hc⟩ := Formalism.LFunctionChainParameters.LLcv.card_pLen _ A B hBA rfl h0
  let e : HeightOneSpectrum (𝓞 K) ≃ {p : Ideal (𝓞 K) // p.IsMaximal} :=
    { toFun := fun P => ⟨P.asIdeal, P.isMaximal⟩
      invFun := fun p => ⟨p.1, p.2.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField K)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hl : ∀ P : HeightOneSpectrum (𝓞 K), (haveI := P.isPrime; lidx P.asIdeal A B) = (k (e P) : ℤ) := by
    intro P
    have a := hk (e P)
    unfold Formalism.LFunctionChainParameters.LLcv.pLen at a
    unfold lidx
    rw [inf_eq_right.mpr hBA, indexBasic_locLen_self]
    unfold locLen
    erw [a]
    simp
  unfold Lat.genIdxH
  simp only [hl, zpow_natCast]
  have := finprod_comp_equiv (f := fun w : {p : Ideal (𝓞 K) // p.IsMaximal} =>
    ((Ideal.absNorm w.1 : ℕ) : ℝ) ^ k w) e
  refine this.trans ?_
  rw [idxN, hc, finprod_eq_prod_of_mulSupport_subset (s := k.support), Finsupp.prod, Nat.cast_prod]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [Nat.cast_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · intro w hw
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h
    apply hw
    simp [h]

variable [Module K V] [IsScalarTower (𝓞 K) K V]

theorem span_inf_eq (L : Submodule (𝓞 K) V) (hL : Submodule.IsLattice K L) (U : Submodule K V) :
    Submodule.span K ((L ⊓ U.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) = U := by
  refine le_antisymm (Submodule.span_le.2 fun x hx => hx.2) fun u hu => ?_
  obtain ⟨r, hr, hru⟩ := Formalism.LFunctionChainParameters.LLcv.span_le_locS (K := K) L (x := u) (by rw [hL.span_eq_top]; trivial)
  have h1 : algebraMap (𝓞 K) K r ≠ 0 := by simpa using nonZeroDivisors.ne_zero hr
  have h2 : r • u ∈ Submodule.span K ((L ⊓ U.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) :=
    Submodule.subset_span ⟨hru, (U.restrictScalars (𝓞 K)).smul_mem r hu⟩
  rw [← algebraMap_smul K r] at h2
  exact (Submodule.smul_mem_iff _ h1).1 h2

theorem isLattice_latIn (L : Submodule (𝓞 K) V) (hL : Submodule.IsLattice K L) (U : Submodule K V) :
    Submodule.IsLattice K (latIn U L) := by
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype ?_
    exact Submodule.FG.of_le hL.fg (Submodule.map_comap_le _ _)
  · rw [eq_top_iff]
    intro u _
    obtain ⟨r, hr, hru⟩ := Formalism.LFunctionChainParameters.LLcv.span_le_locS (K := K) L (x := u) (by rw [hL.span_eq_top]; trivial)
    have h1 : algebraMap (𝓞 K) K r ≠ 0 := by simpa using nonZeroDivisors.ne_zero hr
    have h2 : r • u ∈ Submodule.span K (latIn U L : Set U) := Submodule.subset_span hru
    rw [← algebraMap_smul K r] at h2
    exact (Submodule.smul_mem_iff _ h1).1 h2

variable [StarRing K]

theorem nondeg_of_pd {h : V →ₗ⋆[K] V →ₗ[K] K} (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have key : ∀ x, h x x = 0 → x = 0 := fun x hx => by
    by_contra h0
    have := hp τ x h0
    rw [hx] at this
    simp at this
  exact ⟨fun x hx => key x (hx x), fun x hx => key x (hx x)⟩

theorem idxN_dualInH (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (hL : Submodule.IsLattice K L)
    (U : Submodule K V) :
    idxN (Lat.dualInH h (L ⊓ U.restrictScalars (𝓞 K))) (L ⊓ U.restrictScalars (𝓞 K)) =
      discN (hRes h U) (latIn U L) := by
  have e1 : (L ⊓ U.restrictScalars (𝓞 K)).toAddSubgroup =
      (latIn U L).toAddSubgroup.map U.subtype.toAddMonoidHom := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h2⟩, h1, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
  have e2 : (Lat.dualInH h (L ⊓ U.restrictScalars (𝓞 K))).toAddSubgroup =
      (dual (hRes h U) (latIn U L)).toAddSubgroup.map U.subtype.toAddMonoidHom := by
    unfold Lat.dualInH
    rw [span_inf_eq L hL U]
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨x, h2⟩, (dualBasic_mem_dual _ _ _).2 fun y hy => ?_, rfl⟩
      exact (dualBasic_mem_dual _ _ _).1 h1 y ⟨hy, y.2⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(dualBasic_mem_dual _ _ _).2 fun z hz => ?_, y.2⟩
      exact (dualBasic_mem_dual _ _ _).1 hy ⟨z, hz.2⟩ hz.1
  rw [discN, idxN, idxN, e1, e2, AddSubgroup.relIndex_map_map_of_injective _ _ U.injective_subtype]

theorem discGen_iff (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (hle : L ≤ dual h L) (e : ℕ) :
    Cnt.DiscGen h L e ↔ ∃ t : Finset V, t.card ≤ e ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V) := by
  set D := dual h L with hD
  set q : D →ₗ[𝓞 K] Cnt.discMod h L := (L.comap D.subtype).mkQ with hq
  have key : ∀ s : Finset D, Submodule.span (𝓞 K) ((s.image q : Finset _) : Set (Cnt.discMod h L)) = ⊤ ↔
      D = L ⊔ Submodule.span (𝓞 K) ((s.image D.subtype : Finset V) : Set V) := by
    intro s
    rw [Finset.coe_image, Finset.coe_image, ← Submodule.map_span, ← Submodule.map_span, hq,
      Submodule.map_mkQ_eq_top, ← (Submodule.map_injective_of_injective D.injective_subtype).eq_iff,
      Submodule.map_sup, Submodule.map_comap_subtype, inf_eq_right.2 hle, Submodule.map_top,
      Submodule.range_subtype, eq_comm]
  constructor
  · rintro ⟨s, hs, hsp⟩
    have hsurj : Function.Surjective q := Submodule.mkQ_surjective _
    refine ⟨(s.image (Function.surjInv hsurj)).image D.subtype,
      Finset.card_image_le.trans (Finset.card_image_le.trans hs), (key _).1 ?_⟩
    rw [Finset.image_image, (Function.rightInverse_surjInv hsurj).comp_eq_id, Finset.image_id, hsp]
  · rintro ⟨t, ht, hsp⟩
    have htD : ∀ x ∈ t, x ∈ D := fun x hx => by
      rw [hsp]; exact Submodule.mem_sup_right (Submodule.subset_span hx)
    have ee : (t.subtype (· ∈ D)).image D.subtype = t := by
      ext x
      simp only [Finset.mem_image, Finset.mem_subtype]
      exact ⟨fun ⟨y, hy, e⟩ => e ▸ hy, fun hx => ⟨⟨x, htD x hx⟩, hx, rfl⟩⟩
    refine ⟨(t.subtype (· ∈ D)).image q, Finset.card_image_le.trans ?_, (key _).2 (by rw [ee]; exact hsp)⟩
    rw [Finset.card_subtype]
    exact (Finset.card_filter_le _ _).trans ht

end

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ L : Submodule (𝓞 K) V, IsIntLat h L → Lat.latDetH h L ^ 2 = (discN h L : ℝ) ∧ 0 < Lat.latDetH h L ∧ (∀ j de : ℕ, Cnt.cntPrim h L j de = (primSp h L j (de ^ 2)).encard) ∧ (∀ e : ℕ, Cnt.DiscGen h L e ↔ (∃ t : Finset V, t.card ≤ e ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V))) ∧ ∀ (U : Submodule K V), Lat.latDetH h (L ⊓ U.restrictScalars (𝓞 K)) ^ 2 = (discN (hRes h U) (latIn U L) : ℝ) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hp L hL
  have hle : L ≤ dual h L := fun x hx => (dualBasic_mem_dual _ _ _).2 fun y hy => hL.2 y hy x hx
  have hn := nondeg_of_pd hp
  have h0 := (DiscOrder.main K V h hK hs hn L hL).1
  have hd : Lat.dualInH h L = dual h L := by
    unfold Lat.dualInH
    rw [hL.1.span_eq_top]
    simp
  have h1 : Lat.latDetH h L = Real.sqrt (discN h L : ℝ) := by
    rw [Lat.latDetH, hd, genIdxH_eq_idxN hle h0, discN]
  have hU : ∀ U : Submodule K V, Lat.latDetH h (L ⊓ U.restrictScalars (𝓞 K)) =
      Real.sqrt (discN (hRes h U) (latIn U L) : ℝ) := by
    intro U
    have hsU : (hRes h U).IsSymm := ⟨fun x y => hs.eq x y⟩
    have hpU : PD (hRes h U) := fun τ x hx => hp τ x fun e => hx (Subtype.ext e)
    have hI : IsIntLat (hRes h U) (latIn U L) :=
      ⟨isLattice_latIn L hL.1 U, fun x hx y hy => hL.2 x hx y hy⟩
    have n0 := (DiscOrder.main K U _ hK hsU (nondeg_of_pd hpU) _ hI).1
    rw [← idxN_dualInH h L hL.1 U] at n0 ⊢
    rw [Lat.latDetH, genIdxH_eq_idxN _ n0]
    intro x hx
    exact ⟨(dualBasic_mem_dual _ _ _).2 fun y hy => hL.2 y hy.1 x hx.1, Submodule.subset_span hx⟩
  refine ⟨by rw [h1, Real.sq_sqrt (Nat.cast_nonneg _)], ?_, fun j de => ?_, discGen_iff h L hle,
    fun U => by rw [hU, Real.sq_sqrt (Nat.cast_nonneg _)]⟩
  · rw [h1]
    exact Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero h0)
  · have hinj : Function.Injective fun U : Submodule K V => L ⊓ U.restrictScalars (𝓞 K) :=
      Function.LeftInverse.injective (g := fun M : Submodule (𝓞 K) V => Submodule.span K (M : Set V))
        (span_inf_eq L hL.1)
    have hsq : ∀ n : ℕ, Real.sqrt (n : ℝ) = de ↔ n = de ^ 2 := fun n => by
      rw [Real.sqrt_eq_iff_eq_sq (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      exact_mod_cast Iff.rfl
    rw [Cnt.cntPrim, ← hinj.encard_image]
    congr 1
    ext M
    constructor
    · rintro ⟨⟨-, a⟩, b, c⟩
      refine ⟨Submodule.span K (M : Set V), ⟨b, ?_⟩, a.symm⟩
      rw [← hsq, ← hU, ← a, c]
    · rintro ⟨U, ⟨a, b⟩, rfl⟩
      refine ⟨⟨inf_le_left, ?_⟩, ?_, ?_⟩
      · simp only
        rw [span_inf_eq L hL.1]
      · simp only
        rw [span_inf_eq L hL.1, a]
      · simp only
        rw [hU, hsq, b]

end GlobalTheory.Mass.DetAgree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeTraceDualAndTraceDualTraceDualStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLattice_traceDual_and_traceDual_traceDual : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsLattice E Λ → Submodule.IsLattice E (trDual E j Λ) ∧ trDual E j (trDual E j Λ) = Λ := by
  first | exact @GlobalTheory.MeanDual.Alg.isLattice_trDual_and_trDual_trDual | exact GlobalTheory.MeanDual.Alg.isLattice_trDual_and_trDual_trDual | (intros; apply GlobalTheory.MeanDual.Alg.isLattice_trDual_and_trDual_trDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsOrthComplementOfUnitVectorAtRealPlaceStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOrthComplementOfUnitVector_at_real_place : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∀ v, qEps (I.ε v) (infVec I v x) = sgn ℝ s ∧ star (infVec I v x) ᵥ* (Formalism.REAL.Jm (I.ε v) * infMat D v A) = 0 ∧ (infMat D v A)ᴴ * Formalism.REAL.Jm (I.ε v) * infMat D v A = Formalism.REAL.Jm (D.ε v) := by
  first | exact @GlobalTheory.StabUnfold.isPerp_at_place | exact GlobalTheory.StabUnfold.isPerp_at_place | (intros; apply GlobalTheory.StabUnfold.isPerp_at_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPairMoveByIntegralUnipotent
section
noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.PairMove

open GlobalTheory.LoopC.FrEqv

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
  {Λ : Submodule (𝓞 E) S.V}

theorem aut_mul {n m : S.V ≃ₗ[E] S.V} (hm : IsAutLam S Λ m) (hn : IsAutLam S Λ n) : IsAutLam S Λ (m * n) := by
  refine ⟨Subgroup.mul_mem _ hm.1 hn.1, ?_⟩
  have key : ∀ y, (m * n) y ∈ Λ ↔ y ∈ Λ := fun y => by
    show m (n y) ∈ Λ ↔ y ∈ Λ
    rw [aut_mem_iff hm, aut_mem_iff hn]
  ext x
  rw [mem_gmap, ← key ((m * n).symm x), LinearEquiv.apply_symm_apply]

theorem aut_symm {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) : IsAutLam S Λ n.symm := by
  refine ⟨Subgroup.inv_mem _ hn.1, ?_⟩
  ext x
  rw [mem_gmap, LinearEquiv.symm_symm, aut_mem_iff hn]

theorem mem_iff_of_map {n : S.V ≃ₗ[E] S.V} {U W : Submodule E S.V}
    (h : U.map (n : S.V →ₗ[E] S.V) = W) (x : S.V) : n x ∈ W ↔ x ∈ U := by
  rw [← h, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

theorem map_of_mem_iff {n : S.V ≃ₗ[E] S.V} {U W : Submodule E S.V}
    (h : ∀ x, n x ∈ W ↔ x ∈ U) : U.map (n : S.V →ₗ[E] S.V) = W := by
  ext y
  rw [Submodule.mem_map_equiv, ← h (n.symm y), LinearEquiv.apply_symm_apply]

theorem map_symm {n : S.V ≃ₗ[E] S.V} {U W : Submodule E S.V}
    (h : U.map (n : S.V →ₗ[E] S.V) = W) : W.map (n.symm : S.V →ₗ[E] S.V) = U := by
  ext y
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm]
  exact mem_iff_of_map h y

theorem orth_mem {n : S.V ≃ₗ[E] S.V} (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) {U W : Submodule E S.V}
    (h : U.map (n : S.V →ₗ[E] S.V) = W) {x : S.V} (hx : x ∈ orth S U) : n x ∈ orth S W := by
  have hn' : ∀ a b, S.hT (n a) (n b) = S.hT a b := hn
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro w hw
  rw [← h] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  show S.hT (n u) (n x) = 0
  rw [hn']
  exact hx u hu

theorem lrep_mem {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {F : LFlag S r T} {G : LFlag S r T'}
    (h : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp G) {x : S.V} (hx : x ∈ Lrep Λ F) : n x ∈ Lrep Λ G := by
  simp only [Lrep, Submodule.mem_inf, Submodule.restrictScalars_mem] at hx ⊢
  exact ⟨(aut_mem_iff hn x).2 hx.1, orth_mem hn.1 h hx.2⟩

theorem xlam_mem {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {F : LFlag S r T} {G : LFlag S r T'}
    (h : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp G) {x : S.V} (hx : x ∈ XLam Λ F) : n x ∈ XLam Λ G := by
  simp only [XLam, Submodule.mem_inf, Submodule.restrictScalars_mem] at hx ⊢
  exact ⟨(aut_mem_iff hn x).2 hx.1, (mem_iff_of_map h x).2 hx.2⟩

theorem ngx_mem {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {F G : LFlag S r T} {F' G' : LFlag S r T'}
    (h : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp G) (h' : (Xsp F').map (n : S.V →ₗ[E] S.V) = Xsp G') (g : ℕ)
    {x : S.V} (hx : x ∈ NgX Λ g F F') : n x ∈ NgX Λ g G G' := by
  have hΛ : Λ.map ((n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) = Λ := hn.2
  have hle : (NgX Λ g F F').map ((n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) ≤ NgX Λ g G G' := by
    rw [NgX, NgX, Submodule.map_sup, Submodule.map_sup, Submodule.map_smul'', hΛ]
    refine sup_le_sup (sup_le_sup le_rfl ?_) ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact xlam_mem hn h hy
    · rintro _ ⟨y, hy, rfl⟩
      exact xlam_mem hn h' hy
  exact hle (Submodule.mem_map_of_mem hx)

theorem ngx_iff {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {F G : LFlag S r T} {F' G' : LFlag S r T'}
    (h : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp G) (h' : (Xsp F').map (n : S.V →ₗ[E] S.V) = Xsp G') (g : ℕ)
    (x : S.V) : n x ∈ NgX Λ g G G' ↔ x ∈ NgX Λ g F F' := by
  constructor
  · intro hx
    have := ngx_mem (aut_symm hn) (map_symm h) (map_symm h') g hx
    rwa [LinearEquiv.symm_apply_apply] at this
  · exact ngx_mem hn h h' g

theorem nlam_map {n : S.V ≃ₗ[E] S.V} {F : LFlag S r T} (hn : n ∈ NLam Λ F) :
    (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp F := by
  have key : ∀ m ∈ NLam Λ F, ∀ x ∈ Xsp F, m x ∈ Xsp F := by
    intro m hm x hx
    rw [← sub_add_cancel (m x) x]
    exact add_mem (hm.2.2 x (X_le_orth hx)) hx
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact key n hn x hx
  · intro x hx
    exact ⟨n.symm x, key _ (symm_mem_NLam hn) x hx, by simp⟩

theorem xflag_top (F : LFlag S r T) : Xflag F r = Xsp F := by
  show Submodule.span E (F.fl.e '' {i | i.1 < r}) = Submodule.span E (Set.range F.fl.e)
  rw [show {i : Fin r | i.1 < r} = Set.univ from Set.eq_univ_of_forall fun i => i.2, Set.image_univ]

theorem finrank_X (F : LFlag S r T) : finrank E (Xsp F) = r := by
  show finrank E (Submodule.span E (Set.range F.fl.e)) = r
  rw [finrank_span_eq_card F.fl.e_indep, Fintype.card_fin]

theorem frame_move {n : S.V ≃ₗ[E] S.V} {F A : LFlag S r T} {ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)}
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1)
    (h3 : frame A = frameAct (fun a => n (frame F a)) ξ) :
    (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp A ∧ n F.fl.z - A.fl.z ∈ Xsp A := by
  have hFe : ∀ i : Fin r, frame F i.castSucc = F.fl.e i := fun i => by
    show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z i.castSucc = F.fl.e i
    simp
  have hAe : ∀ i : Fin r, frame A i.castSucc = A.fl.e i := fun i => by
    show Fin.snoc (α := fun _ => S.V) A.fl.e A.fl.z i.castSucc = A.fl.e i
    simp
  have hFz : frame F (Fin.last r) = F.fl.z := by
    show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z (Fin.last r) = F.fl.z
    simp
  have hAz : frame A (Fin.last r) = A.fl.z := by
    show Fin.snoc (α := fun _ => S.V) A.fl.e A.fl.z (Fin.last r) = A.fl.z
    simp
  have hmem : ∀ i : Fin r, n (frame F i.castSucc) ∈ (Xsp F).map (n : S.V →ₗ[E] S.V) := fun i =>
    Submodule.mem_map_of_mem (by rw [hFe]; exact Submodule.subset_span ⟨i, rfl⟩)
  have hX : Xsp A ≤ (Xsp F).map (n : S.V →ₗ[E] S.V) := by
    show Submodule.span E (Set.range A.fl.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [← hAe j, h3]
    simp only [frameAct, SetLike.mem_coe]
    refine Submodule.sum_mem _ fun a _ => ?_
    by_cases ha : j.castSucc < a
    · rw [h1 a j.castSucc ha]
      simp
    · have hne : a ≠ Fin.last r := by
        rintro rfl
        exact ha (Fin.castSucc_lt_last j)
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hne
      exact Submodule.smul_mem _ _ (hmem i)
  have hF : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp A := by
    have : FiniteDimensional E (Xsp F) := FiniteDimensional.span_of_finite E (Set.finite_range _)
    symm
    apply Submodule.eq_of_le_of_finrank_eq hX
    rw [LinearEquiv.finrank_map_eq, finrank_X, finrank_X]
  refine ⟨hF, ?_⟩
  rw [← hAz, h3]
  simp only [frameAct]
  rw [Fin.sum_univ_castSucc, h2 (Fin.last r), hFz]
  have hs : ∑ i : Fin r, ((ξ i.castSucc (Fin.last r) : 𝓞 E) : E) • n (frame F i.castSucc) ∈ Xsp A := by
    rw [← hF]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i)
  have e : ((1 : 𝓞 E) : E) • n F.fl.z = n F.fl.z := by simp
  rw [e, sub_add_eq_sub_sub_swap, sub_self, zero_sub]
  exact neg_mem hs

theorem move {g : ℕ} {F : LFlag S r T} {F' F'' A B : LFlag S r T'} {β n' n'' : S.V ≃ₗ[E] S.V}
    (hp : IsPair Λ F F' F'' β g) (hn' : n' ∈ NLam Λ F) (hn'' : n'' ∈ NLam Λ F)
    (hA : (Xsp F').map (n' : S.V →ₗ[E] S.V) = Xsp A) (zA : n' F'.fl.z - A.fl.z ∈ Xsp A)
    (hB : (Xsp F'').map (n'' : S.V →ₗ[E] S.V) = Xsp B) (zB : n'' F''.fl.z - B.fl.z ∈ Xsp B) :
    IsAutLam S Λ (n'' * β * n'⁻¹) ∧
      (Xsp A).map ((n'' * β * n'⁻¹ : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) = Xsp B ∧
      (n'' * β * n'⁻¹) A.fl.z - B.fl.z ∈ Xsp B ∧ IotaCompat Λ F A B (n'' * β * n'⁻¹) g := by
  have hn'A : IsAutLam S Λ n' := hn'.1
  have hn''A : IsAutLam S Λ n'' := hn''.1
  obtain ⟨hβ, hβF, hβz, hι⟩ := hp
  have hγ : ∀ x, (n'' * β * n'⁻¹) x = n'' (β (n'.symm x)) := fun x => rfl
  have hβX : (Xsp F').map (β : S.V →ₗ[E] S.V) = Xsp F'' := by
    have := hβF r
    rwa [xflag_top, xflag_top] at this
  have hAB : (Xsp A).map ((n'' * β * n'⁻¹ : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) = Xsp B := by
    apply map_of_mem_iff
    intro x
    rw [hγ, mem_iff_of_map hB, mem_iff_of_map hβX, mem_iff_of_map (map_symm hA)]
  have hFn' : (Xsp F).map (n' : S.V →ₗ[E] S.V) = Xsp F := nlam_map hn'
  have hFn'' : (Xsp F).map (n'' : S.V →ₗ[E] S.V) = Xsp F := nlam_map hn''
  refine ⟨aut_mul (aut_mul hn''A hβ) (aut_symm hn'A), hAB, ?_, ?_⟩
  · have e : (n'' * β * n'⁻¹) A.fl.z - B.fl.z =
        (n'' F''.fl.z - B.fl.z) - (n'' * β * n'⁻¹) (n' F'.fl.z - A.fl.z) := by
      simp only [hγ, map_sub, LinearEquiv.symm_apply_apply, hβz]
      abel
    rw [e]
    exact sub_mem zB (by rw [← hAB]; exact Submodule.mem_map_of_mem zA)
  · intro x' hx' l hl
    have hy : n'.symm x' ∈ Lrep Λ F' := lrep_mem (aut_symm hn'A) (map_symm hA) hx'
    have hm : n'.symm l ∈ Lrep Λ F := lrep_mem (aut_symm hn'A) (map_symm hFn') hl
    simp only [Lrep, Submodule.mem_inf, Submodule.restrictScalars_mem] at hl
    have h1 : l - x' ∈ NgX Λ g F A ↔ n'.symm l - n'.symm x' ∈ NgX Λ g F F' := by
      rw [← ngx_iff hn'A hFn' hA g, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    have h3 : n'.symm l - β (n'.symm x') ∈ NgX Λ g F F'' ↔
        n'' (n'.symm l) - (n'' * β * n'⁻¹) x' ∈ NgX Λ g F B := by
      rw [hγ x', ← ngx_iff hn''A hFn'' hB g, map_sub]
    have hd : l - n'' (n'.symm l) ∈ NgX Λ g F B := by
      obtain ⟨hνA, -, hνo⟩ := mul_mem_NLam (symm_mem_NLam hn') hn''
      have e1 : n'' (n'.symm l) - l ∈ XLam Λ F := by
        simp only [XLam, Submodule.mem_inf, Submodule.restrictScalars_mem]
        exact ⟨sub_mem ((aut_mem_iff hνA l).2 hl.1) hl.1, hνo l hl.2⟩
      have e2 : n'' (n'.symm l) - l ∈ NgX Λ g F B := by
        rw [NgX]
        exact Submodule.mem_sup_left (Submodule.mem_sup_right e1)
      rw [← neg_sub]
      exact neg_mem e2
    have h4 : n'' (n'.symm l) - (n'' * β * n'⁻¹) x' ∈ NgX Λ g F B ↔
        l - (n'' * β * n'⁻¹) x' ∈ NgX Λ g F B := by
      rw [show l - (n'' * β * n'⁻¹) x' = (n'' (n'.symm l) - (n'' * β * n'⁻¹) x') + (l - n'' (n'.symm l)) by abel]
      exact (add_mem_cancel_right hd).symm
    exact h1.trans ((hι _ hy _ hm).trans (h3.trans h4))

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pair_move : ∀ (D : D7) (T T' : D.host.E) (Λ : LatV D) (g : ℕ) (F : Fg D T) (F' F'' A B : Fg D T') (β n' n'' : (hS D).V ≃ₗ[D.host.E] (hS D).V), IsPair Λ F F' F'' β g → n' ∈ NLam Λ F → n'' ∈ NLam Λ F → FrameEqv D n' F' A → FrameEqv D n'' F'' B → IsAutLam (hS D) Λ (n'' * β * n'⁻¹) ∧ (Xsp A).map ((n'' * β * n'⁻¹ : (hS D).V ≃ₗ[D.host.E] (hS D).V) : (hS D).V →ₗ[D.host.E] (hS D).V) = Xsp B ∧ (n'' * β * n'⁻¹) A.fl.z - B.fl.z ∈ Xsp B ∧ IotaCompat Λ F A B (n'' * β * n'⁻¹) g := by
  intro D T T' Λ g F F' F'' A B β n' n'' hp hn' hn'' hA hB
  obtain ⟨ξ, h1, h2, h3⟩ := hA
  obtain ⟨η, k1, k2, k3⟩ := hB
  obtain ⟨a1, a2⟩ := frame_move h1 h2 h3
  obtain ⟨b1, b2⟩ := frame_move k1 k2 k3
  exact move hp hn' hn'' a1 a2 b1 b2

end GlobalTheory.LoopC.PairMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentDimEqSumPairsStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlagUnipotentDim_eq_sum_pairs : ∀ (n a : ℕ) (j : Fin a → ℕ) (r : ℕ → ℕ), (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) → r a = n - 2 * ∑ i, j i → (∀ b, 2 * a + 1 ≤ b → r b = 0) → dimN n j = ∑ c ∈ Finset.range (2 * a + 1), ∑ b ∈ Finset.range (2 * a + 1), r b * r (b + c + 1) := by
  first | exact @GlobalTheory.RadicalDimSum.dimN_eq_sum_pairs | exact GlobalTheory.RadicalDimSum.dimN_eq_sum_pairs | (intros; apply GlobalTheory.RadicalDimSum.dimN_eq_sum_pairs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalEqLoweringStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlagUnipotentRadical_eq_lowering : ∀ (n a : ℕ) (ε : Fin n → Bool) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (W' : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsDualFlag (Formalism.REAL.Jm ε) W (2 * a + 1) → W (2 * a + 1) = ⊤ → (∀ i : Fin (a + 1), W' i = W i) → flagN ε W' = {g | uMat g - 1 ∈ lowers W 0} := by
  first | exact @GlobalTheory.RadFullFlag.flagN_eq_lowers | exact GlobalTheory.RadFullFlag.flagN_eq_lowers | (intros; apply GlobalTheory.RadFullFlag.flagN_eq_lowers <;> assumption)
end

