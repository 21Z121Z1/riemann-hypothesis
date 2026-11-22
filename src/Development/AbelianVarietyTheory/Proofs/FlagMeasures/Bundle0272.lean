import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0208
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0238
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0268
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0222
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0223
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0184
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularStabilizerPointMatrixBlockDiagonal
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0001
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDatumEquivariantFlagIsometries
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.DatumOf

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem mem_smul_iff (g : S.GLV) (P : Submodule L.O S.V) (x : S.V) :
    x ∈ g • P ↔ ∃ b ∈ P, g b = x := by
  simp only [Submodule.mem_smul_pointwise_iff_exists, LinearEquiv.smul_def]

theorem inner_le_of_unip (Y : Submodule E S.V) (n : S.GLV) (hn : n ∈ unipOn (perp L S.Hm Y) Y)
    (Λ : Submodule L.O S.V) :
    ((n • Λ) ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O ≤
      (Λ ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O := by
  refine sup_le ?_ le_sup_right
  rintro z ⟨hz1, hz2⟩
  obtain ⟨y, hy, rfl⟩ := (mem_smul_iff S n Λ z).1 hz1
  have hyP : y ∈ perp L S.Hm Y := (hn.1 y).1 hz2
  have e : n y = y + (n y - y) := by abel
  rw [e]
  exact Submodule.add_mem_sup ⟨hy, hyP⟩ (hn.2 y hyP)

theorem inner_eq_of_unip (Y : Submodule E S.V) (n : S.GLV) (hn : n ∈ unipOn (perp L S.Hm Y) Y)
    (Λ : Submodule L.O S.V) :
    ((n • Λ) ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O =
      (Λ ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O := by
  refine le_antisymm (inner_le_of_unip S Y n hn Λ) ?_
  have h1 := inner_le_of_unip S Y n⁻¹ (inv_mem hn) (n • Λ)
  rwa [inv_smul_smul] at h1

theorem complementGroup_fixes_frameSpan {g : S.GLV} (hg : g ∈ S.H0) {x : S.V} (hx : x ∈ S.ME) : g x = x :=
  sub_eq_zero.1 ((Submodule.mem_bot E).1 (hg.2.2 x hx))

theorem X_le : S.X ≤ S.ME := by
  refine le_trans (Submodule.span_mono (Set.image_mono fun i hi => ?_)) le_sup_left
  simp only [Set.mem_setOf_eq] at hi ⊢
  omega

theorem X'_le : S.X' ≤ S.ME := by
  refine le_trans (Submodule.span_mono (Set.image_mono fun i hi => ?_)) le_sup_right
  simp only [Set.mem_setOf_eq] at hi ⊢
  omega

theorem hermitianOrthogonalComplement_mapsTo_of_mem_stabilizer (Y : Submodule E S.V) (hY : Y ≤ S.ME) {g : S.GLV} (hg : g ∈ S.H0) {y : S.V}
    (hy : y ∈ perp L S.Hm Y) : g y ∈ perp L S.Hm Y := by
  intro w hw
  have e := hg.1 y w
  rw [complementGroup_fixes_frameSpan S hg (hY hw)] at e
  rw [e]
  exact hy w hw

theorem inTh_smul (g : S.GLV) (Λ : Submodule L.O S.V) {v : S.V} (hv : S.InTh Λ v) :
    S.InTh (g • Λ) (g v) := by
  obtain ⟨y, hy, rfl⟩ := hv
  exact ⟨g y, (mem_smul_iff S g Λ _).2 ⟨y, hy, rfl⟩, map_smul g _ y⟩

theorem smul_inner_lattice_le_of_mem_hermitianStabilizer (Y : Submodule E S.V) (hY : Y ≤ S.ME) {g : S.GLV} (hg : g ∈ S.H0)
    (Λ : Submodule L.O S.V) :
    g • ((Λ ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O) ≤
      ((g • Λ) ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O := by
  intro z hz
  obtain ⟨b, hb, rfl⟩ := (mem_smul_iff S g _ z).1 hz
  obtain ⟨y, ⟨hy1, hy2⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 hb
  rw [map_add, complementGroup_fixes_frameSpan S hg (hY hx)]
  exact Submodule.add_mem_sup ⟨(mem_smul_iff S g Λ _).2 ⟨y, hy1, rfl⟩, hermitianOrthogonalComplement_mapsTo_of_mem_stabilizer S Y hY hg hy2⟩ hx

theorem smul_inner_lattice_eq_of_mem_hermitianStabilizer (Y : Submodule E S.V) (hY : Y ≤ S.ME) {g : S.GLV} (hg : g ∈ S.H0)
    (Λ : Submodule L.O S.V) :
    ((g • Λ) ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O =
      g • ((Λ ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O) := by
  refine le_antisymm ?_ (smul_inner_lattice_le_of_mem_hermitianStabilizer S Y hY hg Λ)
  have h1 := smul_inner_lattice_le_of_mem_hermitianStabilizer S Y hY (inv_mem hg) (g • Λ)
  rw [inv_smul_smul] at h1
  intro z hz
  have h2 := Submodule.smul_mem_pointwise_smul _ g _ (h1 (Submodule.smul_mem_pointwise_smul z g⁻¹ _ hz))
  rwa [smul_inv_smul] at h2

theorem smul_graphOf_subset_of_mem_hermitianStabilizer {g : S.GLV} (hg : g ∈ S.H0) (Λ : Submodule L.O S.V) :
    g • S.graphOf Λ ⊆ S.graphOf (g • Λ) := by
  rintro _ ⟨p, ⟨y', hy', y, hy, h1, h2, h3, h4, h5⟩, rfl⟩
  refine ⟨g y', (mem_smul_iff S g Λ _).2 ⟨y', hy', rfl⟩, g y, (mem_smul_iff S g Λ _).2 ⟨y, hy, rfl⟩,
    hermitianOrthogonalComplement_mapsTo_of_mem_stabilizer S _ (X'_le S) hg h1, hermitianOrthogonalComplement_mapsTo_of_mem_stabilizer S _ (X_le S) hg h2, ?_, ?_, ?_⟩
  · show g y' - g p.1 ∈ S.X'
    rw [← map_sub, complementGroup_fixes_frameSpan S hg (X'_le S h3)]
    exact h3
  · show g y - g p.2 ∈ S.X
    rw [← map_sub, complementGroup_fixes_frameSpan S hg (X_le S h4)]
    exact h4
  · rw [← map_sub]
    exact inTh_smul S g Λ h5

theorem graphOf_smul_eq_of_mem_hermitianStabilizer {g : S.GLV} (hg : g ∈ S.H0) (Λ : Submodule L.O S.V) :
    S.graphOf (g • Λ) = g • S.graphOf Λ := by
  refine subset_antisymm ?_ (smul_graphOf_subset_of_mem_hermitianStabilizer S hg Λ)
  intro p hp
  have h1 := smul_graphOf_subset_of_mem_hermitianStabilizer S (inv_mem hg) (g • Λ) ⟨p, hp, rfl⟩
  rw [inv_smul_smul] at h1
  exact ⟨g⁻¹ • p, h1, smul_inv_smul g p⟩

theorem datOf_smul_eq_of_mem_hermitianStabilizer {g : S.GLV} (hg : g ∈ S.H0) (Λ : Submodule L.O S.V) :
    S.datOf (g • Λ) = g • S.datOf Λ :=
  Prod.ext (smul_inner_lattice_eq_of_mem_hermitianStabilizer S S.X (X_le S) hg Λ)
    (Prod.ext (smul_inner_lattice_eq_of_mem_hermitianStabilizer S S.X' (X'_le S) hg Λ) (graphOf_smul_eq_of_mem_hermitianStabilizer S hg Λ))

theorem std_inner [IsNonarchimedeanLocalField F] [CharZero F] (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (hgs : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) (A : Submodule L.O S.V) (hA : S.IsInner g gs A) :
    (S.stdLat g gs A ⊓ (perp L S.Hm (S.spanTo g r)).restrictScalars L.O) ⊔
      (S.spanTo g r).restrictScalars L.O = A := by
  have h3 := (StdLat.stdLat_spec L r k S g gs hgs A hA).2.2
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rintro y ⟨hy1, hy2⟩
      exact (h3 y).2 ⟨y, hy1, hy2, by simp⟩
    · intro x hx
      exact hA.1 x hx
  · intro x hx
    obtain ⟨y, hy, hyp, hyx⟩ := (h3 x).1 hx
    have e : x = y - (y - x) := by abel
    rw [e]
    exact Submodule.sub_mem_sup ⟨hy, hyp⟩ hyx

theorem datOf_term [IsNonarchimedeanLocalField F] [CharZero F] {d : S.Datum} {Λ : Submodule L.O S.V}
    (h : S.IsTerm d Λ) : d = S.datOf Λ := by
  obtain ⟨⟨n, n'⟩, hA, hA', hn, hn', hΛ, hΛ', -, hg⟩ := h
  refine Prod.ext ?_ (Prod.ext ?_ hg)
  · show d.1 = (Λ ⊓ (perp L S.Hm S.X).restrictScalars L.O) ⊔ S.X.restrictScalars L.O
    rw [hΛ, inner_eq_of_unip S S.X n hn.2]
    exact (std_inner S S.f S.es (Or.inl ⟨rfl, rfl⟩) _ hA).symm
  · show d.2.1 = (Λ ⊓ (perp L S.Hm S.X').restrictScalars L.O) ⊔ S.X'.restrictScalars L.O
    rw [hΛ', inner_eq_of_unip S S.X' n' hn'.2]
    exact (std_inner S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) _ hA').symm

theorem exists_unitri (g : Fin (r + 1) → S.V) (φ : S.GLV) (h : ∀ b : Fin (r + 1), φ (g b) - g b ∈ S.spanTo g b) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧
      ∀ j, φ (g j) = ∑ i, s i j • g i := by
  choose c hc0 hc using fun b : Fin (r + 1) => StdLat.exists_coef g {i | (i : ℕ) < b} (h b)
  refine ⟨fun i j => c j i + if i = j then 1 else 0, ⟨fun i j hij => ?_, fun i => ?_⟩, fun j => ?_⟩
  · have hne : i ≠ j := (ne_of_lt hij).symm
    have h0 : c j i = 0 := hc0 j i fun hi => by
      have := Fin.lt_def.1 hij
      simp only [Set.mem_setOf_eq] at hi
      omega
    simp [h0, hne]
  · have h0 : c i i = 0 := hc0 i i fun hi => lt_irrefl (i : ℕ) hi
    simp [h0]
  · have e1 : ∑ i, (c j i + if i = j then (1 : E) else 0) • g i = ∑ i, c j i • g i + g j := by
      simp [add_smul, Finset.sum_add_distrib, ite_smul]
    rw [e1, ← hc j]
    abel

theorem mem_hermitianStabilizer_of_preserves_both_flags [IsNonarchimedeanLocalField F] [CharZero F] (φ : S.GLV) (hφ : φ ∈ isomG L S.Hm)
    (h1 : ∀ b : Fin (r + 1), φ (S.f b) - S.f b ∈ S.spanTo S.f b)
    (h2 : ∀ b : Fin (r + 1), φ (S.f' b) - S.f' b ∈ S.spanTo S.f' b) :
    ∃ s ∈ S.St, ∃ h ∈ S.H0, φ = s * h := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  obtain ⟨s, hs, hsφ⟩ := exists_unitri S S.f φ h1
  obtain ⟨s', hs', hsφ'⟩ := exists_unitri S S.f' φ h2
  have hz : cT L s * S.Zh * s' = S.Zh := by
    ext a b
    rw [← FrameStab.pair_eq S s s' a b, ← hsφ, ← hsφ']
    exact hφ _ _
  obtain ⟨h, hh, hf, hf'⟩ := ((FrameStab.stab_eq L r k S).2 s s' hs hs').1 hz
  have k1 : ∀ (g : Fin (r + 1) → S.V) (m : ℕ), (∀ i, φ (g i) = h (g i)) → ∀ v ∈ S.spanTo g m, φ v = h v := by
    intro g m hg v hv
    have hle : S.spanTo g m ≤ LinearMap.eqLocus (φ : S.V →ₗ[E] S.V) (h : S.V →ₗ[E] S.V) := by
      rw [Frames.spanTo, Submodule.span_le]
      rintro _ ⟨i, -, rfl⟩
      exact hg i
    exact hle hv
  have hfix : ∀ v ∈ S.ME, φ v = h v := by
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, map_add, k1 S.f _ (fun i => by rw [hsφ, hf]) a ha,
      k1 S.f' _ (fun i => by rw [hsφ', hf']) b hb]
  have hiso : h ∈ isomG L S.Hm := hh.1.1.1
  refine ⟨h, hh, h⁻¹ * φ, Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hiso) hφ, ?_⟩, (mul_inv_cancel_left h φ).symm⟩
  refine FrameStab.mem_unipOn' bot_le _ fun v hv => ?_
  show h.symm (φ v) - v ∈ (⊥ : Submodule E S.V)
  rw [hfix v hv, LinearEquiv.symm_apply_apply, sub_self]
  exact zero_mem _

end

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ d Λ, S.IsTerm d Λ → d = S.datOf Λ) ∧ (∀ h ∈ S.H0, ∀ Λ, S.datOf (h • Λ) = h • S.datOf Λ) ∧ (∀ n ∈ S.N, ∀ Λ, (S.datOf (n • Λ)).1 = (S.datOf Λ).1) ∧ (∀ n ∈ S.N', ∀ Λ, (S.datOf (n • Λ)).2.1 = (S.datOf Λ).2.1) ∧ ∀ φ ∈ isomG L S.Hm, (∀ b : Fin (r + 1), φ (S.f b) - S.f b ∈ S.spanTo S.f b) → (∀ b : Fin (r + 1), φ (S.f' b) - S.f' b ∈ S.spanTo S.f' b) → ∃ s ∈ S.St, ∃ h ∈ S.H0, φ = s * h := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  exact ⟨fun d Λ h => datOf_term S h, fun g hg Λ => datOf_smul_eq_of_mem_hermitianStabilizer S hg Λ,
    fun n hn Λ => inner_eq_of_unip S S.X n hn.2 Λ, fun n hn Λ => inner_eq_of_unip S S.X' n hn.2 Λ,
    fun φ hφ h1 h2 => mem_hermitianStabilizer_of_preserves_both_flags S φ hφ h1 h2⟩

end GlobalTheory.HL.DatumOf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHsNormSqDoubleCosetLeFatou
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.FatouI

theorem lintegral_le_of_liminf {X : Type*} [MeasurableSpace X] (ν : Measure X) (F : X → ENNReal)
    (g : ℕ → X → ENNReal) (hg : ∀ j, Measurable (g j))
    (hF : ∀ᵐ γ ∂ν, F γ ≤ Filter.liminf (fun j => g j γ) Filter.atTop) (b : ℕ → ℝ) (L : ℝ)
    (hb : ∀ j, ∫⁻ γ, g j γ ∂ν = ENNReal.ofReal (b j))
    (hL : Filter.Tendsto b Filter.atTop (nhds L)) : ∫⁻ γ, F γ ∂ν ≤ ENNReal.ofReal L := by
  refine (lintegral_mono_ae hF).trans ((lintegral_liminf_le hg).trans ?_)
  simp_rw [hb]
  exact (ENNReal.tendsto_ofReal hL).liminf_eq.le

variable {k r : ℕ}

theorem measurable_besselTwoSidedAction_joint :
    Measurable fun q : Mt k r × (Mt k r × Mt k r) => act2 (Matrix.of q.1) q.2 := by
  let m : Mt k r × Mt k r → Mt k r := fun q => lmulM (Matrix.of q.1) q.2
  have hmul : Continuous m :=
    Continuous.matrix_mul (X := Mt k r × Mt k r) continuous_fst continuous_snd
  have hm : Measurable m := hmul.measurable
  have h1 : Measurable fun q : Mt k r × (Mt k r × Mt k r) => m (q.2.1, q.1) :=
    hm.comp (measurable_snd.fst.prodMk measurable_fst)
  have h2 : Measurable fun q : Mt k r × (Mt k r × Mt k r) => invM q.2.2 :=
    measurable_invM.comp measurable_snd.snd
  have h3 : Measurable fun q : Mt k r × (Mt k r × Mt k r) => m (m (q.2.1, q.1), invM q.2.2) :=
    hm.comp (h1.prodMk h2)
  exact h3

theorem hsNormSq_eq_sum {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) :
    hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

theorem DD_stable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (w : H) (hσ : IsURepOn (GG k r) σ) (hG : IsClosedSub k r (GG k r)) :
    ∀ g ∈ GG k r, ∀ v ∈ (DD σ w : Set H), σ g v ∈ (DD σ w : Set H) := by
  intro g hg v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨h, hh, rfl⟩ := hv
    have := mem_DD σ w (hG.2.2.2.1 g hg h hh)
    rw [hσ.1.2 g hg h hh] at this
    exact this
  | zero => simp
  | add u v _ _ hu hv => rw [map_add]; exact (DD σ w).add_mem hu hv
  | smul a v _ hv => rw [map_smul]; exact (DD σ w).smul_mem a hv

theorem integrable_coef {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (hσ : IsURepOn (GG k r) σ) {S : Set (Mat k r)} (hS : IsClosedSub k r S)
    {μ : Measure (Mt k r)} (hμ : IsHaarOn S μ) {a C : ℝ} (hfin : normInt μ a < ⊤) (u v : H)
    (hC : ∀ g ∈ GG k r, ‖coef σ u v g‖ ≤ C * opn g ^ (-a)) :
    Integrable (fun p : Mt k r => coef σ u v (Matrix.of p)) μ := by
  have hae : ∀ᵐ p ∂μ, (Matrix.of p : Mat k r) ∈ S := hμ.2.2.1
  have hSm : MeasurableSet {p : Mt k r | (Matrix.of p : Mat k r) ∈ S} :=
    IsClosed.measurableSet (α := Mt k r) hS.2.1
  refine ⟨?_, ?_⟩
  · have hc : ContinuousOn (fun p : Mt k r => coef σ u v (Matrix.of p))
        {p : Mt k r | (Matrix.of p : Mat k r) ∈ S} :=
      ContinuousOn.inner (𝕜 := ℂ) continuousOn_const ((hσ.2.2 u).mono hS.1)
    have := hc.aestronglyMeasurable (μ := μ) hSm
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {p : Mt k r | (Matrix.of p : Mat k r) ∈ S}) hae] at this
  · refine lt_of_le_of_lt (b := ∫⁻ x, ENNReal.ofReal C * ENNReal.ofReal (opn (Matrix.of x) ^ (-a)) ∂μ)
      (lintegral_mono_ae ?_) ?_
    · filter_upwards [hae] with p hp
      rw [← ENNReal.ofReal_mul' (Real.rpow_nonneg (opn_nonneg _) _), ← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hC _ (hS.1 hp))
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

theorem dis_of_continuousOn {Ω S S' : Set (Mat k r)} {μG μS μS' ν : Measure (Mt k r)}
    (hG : IsClosedSub k r (GG k r)) (hS : IsClosedSub k r S) (hS' : IsClosedSub k r S')
    (hμG : IsHaarOn (GG k r) μG) (hμ : IsHaarOn S μS) (hμ' : IsHaarOn S' μS') (hΩ : Ω ⊆ GG k r)
    (hν : IsDis Ω μG μS μS' ν) (f : Mat k r → ℝ) (hf0 : ∀ g, 0 ≤ f g) (hf : ContinuousOn f (GG k r))
    (hfi : Integrable (fun g : Mt k r => f (Matrix.of g)) μG) :
    ∃ g : Mt k r → ENNReal, Measurable g ∧
      (∀ γ : Mt k r, Matrix.of γ ∈ Ω →
        g γ = ∫⁻ p, ENNReal.ofReal (f (Matrix.of (act2 (Matrix.of γ) p))) ∂(μS.prod μS')) ∧
      ∫⁻ γ, g γ ∂ν = ENNReal.ofReal (∫ g, f (Matrix.of g) ∂μG) := by
  classical
  haveI := hμ.1
  haveI := hμ'.1
  have hGm : MeasurableSet {p : Mt k r | (Matrix.of p : Mat k r) ∈ GG k r} :=
    IsClosed.measurableSet (α := Mt k r) hG.2.1
  let f0 : Mt k r → ℝ := {p : Mt k r | (Matrix.of p : Mat k r) ∈ GG k r}.piecewise
    (fun p => f (Matrix.of p)) (fun _ => 0)
  have hf0m : Measurable f0 :=
    ContinuousOn.measurable_piecewise (f := fun p : Mt k r => f (Matrix.of p)) hf continuousOn_const hGm
  have hf0e : ∀ p : Mt k r, Matrix.of p ∈ GG k r → f0 p = f (Matrix.of p) := fun p hp =>
    Set.piecewise_eq_of_mem _ _ _ hp
  have hF : Measurable fun p => ENNReal.ofReal (f0 p) := hf0m.ennreal_ofReal
  refine ⟨fun γ => ∫⁻ p, ENNReal.ofReal (f0 (act2 (Matrix.of γ) p)) ∂(μS.prod μS'), ?_, ?_, ?_⟩
  · exact (hF.comp measurable_besselTwoSidedAction_joint).lintegral_prod_right'
  · intro γ hγ
    have h1 : ∀ᵐ p ∂μS, (Matrix.of p : Mat k r) ∈ S := hμ.2.2.1
    have h2 : ∀ᵐ p ∂μS', (Matrix.of p : Mat k r) ∈ S' := hμ'.2.2.1
    have h1' := Measure.quasiMeasurePreserving_fst (μ := μS) (ν := μS') |>.ae h1
    have h2' := Measure.quasiMeasurePreserving_snd (μ := μS) (ν := μS') |>.ae h2
    refine lintegral_congr_ae ?_
    filter_upwards [h1', h2'] with p hp hp'
    rw [hf0e]
    exact hG.2.2.2.1 _ (hG.2.2.2.1 _ (hS.1 hp) _ (hΩ hγ)) _ (hG.2.2.2.2 _ (hS'.1 hp'))
  · rw [← hν.2.2 _ hF, ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall fun g => hf0 _)]
    have h1 : ∀ᵐ p ∂μG, (Matrix.of p : Mat k r) ∈ GG k r := hμG.2.2.1
    refine lintegral_congr_ae ?_
    filter_upwards [h1] with p hp
    rw [hf0e p hp]

end GlobalTheory.SgInf.FatouI

open GlobalTheory.SgInf.FatouI in

theorem GlobalTheory.SgInf.lintegral_hsNormSq_Iint_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ ν : Measure (Mt k r), IsDis (Greg k r z z') μG μS μS' ν → ∀ x ∈ DD σ w, ∀ y ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq), ∫⁻ γ, ENNReal.ofReal (hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ x y ξ ξ' (Matrix.of γ))) ∂ν ≤ ENNReal.ofReal (d⁻¹ * (⟪ξ, be (psiGen k r z c) π μS σ y y ξ⟫_ℂ).re * (⟪ξ', be (psiGen k r z' c') π' μS' σ x x ξ'⟫_ℂ).re) := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' hStd hSd hSd' ν hν x hx y hy ξ ξ'
  obtain ⟨hG, -, -, hS, -⟩ := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSd.1 hSd.2.1
  obtain ⟨-, -, -, hS', -⟩ := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z' hSd'.1 hSd'.2.1
  obtain ⟨Om, hOm⟩ := GlobalTheory.T.exists_isFolnerSequenceBessel k r z μS hSd.1 hSd.2.1 hSd.2.2.2.1
  obtain ⟨Om', hOm'⟩ := GlobalTheory.T.exists_isFolnerSequenceBessel k r z' μS' hSd'.1 hSd'.2.1 hSd'.2.2.2.1
  have hdec := hStd.2.2.2.2.2.2.2.1
  have ha : 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < a := by
    have h1 : (2 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
      have := hStd.1
      exact_mod_cast (by omega : 2 ≤ 2 * r + k + 1)
    have h2 : ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < ((2 * r + k + 1 : ℕ) : ℝ) ^ 5 :=
      pow_lt_pow_right₀ (by linarith) (by norm_num)
    have := hStd.2.2.2.2.2.2.1
    linarith
  have hiy : Integrable (fun p : Mt k r => coef σ y y (Matrix.of p)) μS := by
    obtain ⟨C, hC⟩ := hdec y hy y hy
    exact integrable_coef σ hStd.2.1 hS hSd.2.2.2.1 (GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r _ μS a hS hSd.2.2.2.1 ha) y y hC
  have hix : Integrable (fun p : Mt k r => coef σ x x (Matrix.of p)) μS' := by
    obtain ⟨C, hC⟩ := hdec x hx x hx
    exact integrable_coef σ hStd.2.1 hS' hSd'.2.2.2.1 (GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r _ μS' a hS' hSd'.2.2.2.1 ha) x x hC
  have h62 := fun j => GlobalTheory.T.bessel_functional_two_sided k r σ w a μG d z c π μS z' c' π' μS' hStd hSd hSd' x y ξ ξ' (Om j) (Om' j)
    (hOm.1 j).1 (hOm'.1 j).1 (hOm.1 j).2.2.2.2 (hOm'.1 j).2.2.2.2 hiy hix
  have h63 := GlobalTheory.T.besselFolner_overlap_average_tendsto_form k r σ w a μG d z c π μS hStd hSd Om hOm y hy ξ
  have h63' := GlobalTheory.T.besselFolner_overlap_average_tendsto_form k r σ w a μG d z' c' π' μS' hStd hSd' Om' hOm' x hx ξ'
  have h64 := GlobalTheory.T.hsNormSq_Iint_le_liminf_alt k r σ w a μG d z c π μS z' c' π' μS' hStd hSd hSd' Om Om' hOm hOm' x hx y hy ξ ξ'
  have hadj := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSd (DD σ w) (DD_stable σ w hStd.2.1 hG) hdec
    y hy y hy).2.2.1
  have him : (⟪ξ, be (psiGen k r z c) π μS σ y y ξ⟫_ℂ).im = 0 := by
    rw [← Complex.conj_eq_iff_im, inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right, hadj]
  have hcont : Continuous (hsNormSq : (Wq →L[ℂ] Wp) → ℝ) := by
    have : (hsNormSq : (Wq →L[ℂ] Wp) → ℝ) = fun A => ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 :=
      funext hsNormSq_eq_sum
    rw [this]
    fun_prop
  have hnn : ∀ A : Wq →L[ℂ] Wp, 0 ≤ hsNormSq A := fun A => by
    rw [hsNormSq_eq_sum]; positivity
  have hdis := fun j => dis_of_continuousOn hG hS hS' hStd.2.2.2.2.1 hSd.2.2.2.1 hSd'.2.2.2.1
    (Greg_subset z z') hν (fun g => hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π'
      (μS.restrict (Om j)) (μS'.restrict (Om' j)) σ x y ξ ξ' g)) (fun g => hnn _)
      (hcont.comp_continuousOn (h62 j).1) (h62 j).2.1
  choose g hgm hge hgi using hdis
  have hpos : ∀ j, 0 < (μS (Om j)).toReal := fun j =>
    ENNReal.toReal_pos (hOm.1 j).2.2.2.1.ne' (hOm.1 j).2.2.2.2.ne
  have hpos' : ∀ j, 0 < (μS' (Om' j)).toReal := fun j =>
    ENNReal.toReal_pos (hOm'.1 j).2.2.2.1.ne' (hOm'.1 j).2.2.2.2.ne
  refine lintegral_le_of_liminf ν _ (fun j γ => g j γ / (μS (Om j) * μS' (Om' j)))
    (fun j => (hgm j).div_const _) ?_
    (fun j => (∫ g, hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π'
      (μS.restrict (Om j)) (μS'.restrict (Om' j)) σ x y ξ ξ' (Matrix.of g)) ∂μG) /
        ((μS (Om j)).toReal * (μS' (Om' j)).toReal)) _ ?_ ?_
  · have h1 : ∀ᵐ γ ∂ν, (Matrix.of γ : Mat k r) ∈ Greg k r z z' := hν.2.1
    filter_upwards [h1] with γ hγ
    simp_rw [fun j => hge j γ hγ]
    exact h64 _ hγ
  · intro j
    simp_rw [div_eq_mul_inv (g j _)]
    rw [lintegral_mul_const _ (hgm j), hgi j, ENNReal.ofReal_div_of_pos (mul_pos (hpos j) (hpos' j)),
      ENNReal.ofReal_mul (hpos j).le, ENNReal.ofReal_toReal (hOm.1 j).2.2.2.2.ne,
      ENNReal.ofReal_toReal (hOm'.1 j).2.2.2.2.ne, div_eq_mul_inv]
  · have hT := (Complex.continuous_re.tendsto _).comp ((h63.const_mul ((d : ℂ)⁻¹)).mul h63')
    convert hT using 2 with j
    · have e := (h62 j).2.2
      rw [Function.comp_apply, ← mul_div_assoc (d : ℂ)⁻¹, div_mul_div_comm, ← e]
      norm_cast
    · rw [← Complex.ofReal_inv, mul_assoc (_ : ℂ), Complex.re_ofReal_mul, Complex.mul_re, him]
      ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdShiftedCyclicWordExpansion
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

namespace GlobalTheory.TraceBinom

variable {R : Type} [Ring R] {n : ℕ}

theorem pow_succ_apply_path (M : Matrix (Fin n) (Fin n) R) (m : ℕ) (i j : Fin n) :
    (M ^ (m + 1)) i j = ∑ a : Fin m → Fin n,
      (List.ofFn fun l : Fin (m + 1) =>
        M ((Fin.cons i (Fin.snoc a j : Fin (m + 1) → Fin n) : Fin (m + 2) → Fin n) l.castSucc)
          ((Fin.cons i (Fin.snoc a j : Fin (m + 1) → Fin n) : Fin (m + 2) → Fin n) l.succ)).prod := by
  induction m generalizing i with
  | zero => simp; rfl
  | succ m ih =>
    rw [pow_succ', Matrix.mul_apply]
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin n)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ih x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_rhs => rw [List.ofFn_succ, List.prod_cons]
    dsimp only [Fin.consEquiv, Equiv.coe_fn_mk]
    simp only [← Fin.cons_snoc_eq_snoc_cons, ← Fin.succ_castSucc, Fin.cons_succ,
      Fin.castSucc_zero, Fin.cons_zero]

theorem sum_cycWord_eq_trace (M : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    ∑ a : Fin (k + 1) → Fin n, ((cycWord a).map fun p => M p.1 p.2).prod = trace (M ^ (k + 1)) := by
  rw [Matrix.trace]
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin n)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, pow_succ_apply_path]
  refine Finset.sum_congr rfl fun a _ => ?_
  dsimp only [Fin.consEquiv, Equiv.coe_fn_mk]
  rw [cycWord, List.map_ofFn]
  congr 2
  funext l
  simp only [Function.comp_apply]
  rw [Fin.cons_snoc_eq_snoc_cons, Fin.snoc_castSucc, ← Fin.cons_snoc_eq_snoc_cons, Fin.cons_succ]
  congr 1
  refine Fin.lastCases ?_ (fun l => ?_) l
  · simp
  · have e : finRotate (k + 1) l.castSucc = l.succ := by
      ext
      simp [Fin.val_add_one_of_lt (Fin.castSucc_lt_last l)]
    rw [e, Fin.cons_succ, Fin.snoc_castSucc]

theorem trace_add_algebraMap_pow [Algebra ℂ R] (M : Matrix (Fin n) (Fin n) R) (c : ℂ) (k : ℕ) :
    trace ((M + algebraMap ℂ (Matrix (Fin n) (Fin n) R) c) ^ (k + 1)) =
      algebraMap ℂ R (c ^ (k + 1) * n) + ∑ j ∈ range (k + 1),
        algebraMap ℂ R (((k + 1).choose (j + 1) : ℂ) * c ^ (k - j)) * trace (M ^ (j + 1)) := by
  rw [Commute.add_pow (Algebra.commute_algebraMap_right c M), Finset.sum_range_succ', trace_add, trace_sum,
    add_comm]
  congr 1
  · rw [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero, ← map_pow, Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.algebraMap_matrix_apply, if_true]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, map_mul, map_natCast, Nat.cast_comm]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hjk : k + 1 - (j + 1) = k - j := by omega
    have e : M ^ (j + 1) * algebraMap ℂ (Matrix (Fin n) (Fin n) R) c ^ (k + 1 - (j + 1)) *
        (((k + 1).choose (j + 1) : ℕ) : Matrix (Fin n) (Fin n) R) =
        (((k + 1).choose (j + 1) : ℂ) * c ^ (k - j)) • M ^ (j + 1) := by
      rw [hjk, ← map_pow, ← map_natCast (algebraMap ℂ (Matrix (Fin n) (Fin n) R)), mul_assoc, ← map_mul,
        ← Algebra.commutes, ← Algebra.smul_def, mul_comm (c ^ (k - j))]
    rw [e, trace_smul, Algebra.smul_def]

theorem trace_binomial : ∀ (R : Type) [Ring R] [Algebra ℂ R] (n : ℕ) (T : Fin n → Fin n → R) (c : ℂ) (k : ℕ), ∑ a : Fin (k + 1) → Fin n, ((cycWord a).map (fun p => T p.1 p.2 + if p.1 = p.2 then algebraMap ℂ R c else 0)).prod = algebraMap ℂ R (c ^ (k + 1) * n) + ∑ j ∈ range (k + 1), algebraMap ℂ R (((k + 1).choose (j + 1) : ℂ) * c ^ (k - j)) * ∑ a : Fin (j + 1) → Fin n, ((cycWord a).map (fun p => T p.1 p.2)).prod := by
  intro R _ _ n T c k
  have hA : (fun p : Fin n × Fin n => T p.1 p.2 + if p.1 = p.2 then algebraMap ℂ R c else 0) =
      fun p => (Matrix.of T + algebraMap ℂ (Matrix (Fin n) (Fin n) R) c) p.1 p.2 := by
    funext p
    simp [Matrix.algebraMap_matrix_apply]
  have hT : ∀ j : ℕ, ∑ a : Fin (j + 1) → Fin n, ((cycWord a).map (fun p => T p.1 p.2)).prod =
      trace (Matrix.of T ^ (j + 1)) := fun j => sum_cycWord_eq_trace (Matrix.of T) j
  rw [hA, sum_cycWord_eq_trace, trace_add_algebraMap_pow]
  simp_rw [hT]

end GlobalTheory.TraceBinom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularStabilizerPointMatrixBlockDiagonalStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitriangularStabilizer_pointMatrix_blockDiagonal : ∀ {K : Type} [Field K] (sig : K →+* K), (∀ x, sig (sig x) = x) → ∀ (r : ℕ) (w : Formalism.MainNotions.S.Point K (r + 1)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K), Formalism.MainNotions.S.ZhatOM Z = Formalism.MainNotions.S.ptMat w → (∀ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Formalism.MainNotions.S.IsUpUni s → Formalism.MainNotions.S.IsUpUni s' → (s.map sig).transpose * Z * s' = Z → ∀ a b : Fin (r + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 → s' a b = 0) ∧ ∀ s' : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Formalism.MainNotions.S.IsUpUni s' → (∀ a b : Fin (r + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 → s' a b = 0) → ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Formalism.MainNotions.S.IsUpUni s ∧ (s.map sig).transpose * Z * s' = Z := by
  first | exact @GlobalTheory.PointStab.stab_blockDiag | exact GlobalTheory.PointStab.stab_blockDiag | (intros; apply GlobalTheory.PointStab.stab_blockDiag <;> assumption)
end

