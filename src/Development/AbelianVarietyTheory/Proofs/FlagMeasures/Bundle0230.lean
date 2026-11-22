import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FullySplitStabilizers
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.HermitianMassFormula
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.FiniteDimensionalOfOrtho
import Formalism.HermitianLattices.FinalMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportInnerLattices

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanEqTopOfSelfDual
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct ENNReal

namespace GlobalTheory.SgSpan

theorem form_smul_left {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (a : E) (x y : Fin n → E) : form σ J (a • x) y = a * form σ J x y := by
  simp only [form, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_smul_right {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (a : E) (x y : Fin n → E) : form σ J x (a • y) = σ a * form σ J x y := by
  simp only [form, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem form_add_right {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (x y z : Fin n → E) : form σ J x (y + z) = form σ J x y + form σ J x z := by
  simp only [form, dotProduct, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem form_zero_right {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (x : Fin n → E) : form σ J x 0 = 0 := by
  simp [form, dotProduct]

theorem span_eq_top_of_selfDual : ∀ (E : Type) [Field E] [NumberField E] (σ : E →+* E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)), (∀ x : 𝓞 E, IsIntegral ℤ (σ (x : E))) → GlobalTheory.SgGlob.SelfDual σ J Λ → Submodule.span E (Λ : Set (Fin n → E)) = ⊤ := by
  classical
  intro E _ _ σ n J Λ hσ h
  obtain ⟨⟨s, hs⟩, hd⟩ := h
  rw [eq_top_iff]
  intro v _
  obtain ⟨N, hN0, hN⟩ := exists_integral_multiples ℤ ℚ (s.image fun w => form σ J v w)
  have hrange : ∀ x : E, x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x := by
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.isIntegral_coe
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hNE : (N : E) ≠ 0 := by exact_mod_cast hN0
  have hmem : (N : E) • v ∈ Λ := by
    rw [hd]
    intro w hw
    rw [hrange]
    rw [← hs] at hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      rw [form_smul_left]
      have := hN _ (Finset.mem_image_of_mem _ hw)
      simpa [zsmul_eq_mul] using this
    | zero => rw [form_zero_right]; exact isIntegral_zero
    | add x y _ _ hx hy => rw [form_add_right]; exact hx.add hy
    | smul a x _ hx =>
      have : a • x = (a : E) • x := rfl
      rw [this, form_smul_right]
      exact (hσ a).mul hx
  have : v = (N : E)⁻¹ • ((N : E) • v) := by
    rw [smul_smul, inv_mul_cancel₀ hNE, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GlobalTheory.SgSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StdLatIsOrthoLatticeAndMassProperties
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

namespace GlobalTheory.Mass.StdMass

open NumberField Matrix in
open scoped ENNReal Classical in

theorem _root_.GlobalTheory.Mass.StdMass.isSymm_of_ortho {K V : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ} (hL : _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) :
    h.IsSymm := by
  unfold _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice at hL
  obtain ⟨e, -, hspan, -, horth⟩ := hL
  refine LinearMap.IsSymm.mk fun x y => ?_
  obtain ⟨c, rfl⟩ := _root_.ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums.exists_coord hspan x
  obtain ⟨d, rfl⟩ := _root_.ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums.exists_coord hspan y
  rw [_root_.ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums.form_sum horth, _root_.ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums.form_sum horth]
  simp only [map_sum, starRingEnd_apply, star_mul, star_star]

open NumberField Matrix in
open scoped ENNReal Classical in
private theorem massU_zero_eq_one (K : Type) [Field K] [NumberField K] [StarRing K] :
    _root_.Formalism.MainNotions.S.Cnt.massU K 0 = 1 := by
  have hsub : ∀ M N : Submodule (𝓞 K) (Fin 0 → K), M = N := fun M N => Subsingleton.elim M N
  haveI : Subsingleton ((Fin 0 → K) ≃ₗ[K] (Fin 0 → K)) :=
    ⟨fun f g => LinearEquiv.ext fun x => Subsingleton.elim _ _⟩
  have hlat : Submodule.IsLattice K (_root_.Formalism.MainNotions.S.Cnt.stdLat K 0) := _root_.ReciprocityTheory.ChartRestriction.L3.isLattice_of_ortho (_root_.Formalism.MainNotions.StandardLattice.stdLat_ortho K 0)
  have hgen : _root_.Formalism.MainNotions.S.Cnt.stdLat K 0 ∈ _root_.Formalism.HermitianLatticesTheory.genus (_root_.Formalism.MainNotions.S.Cnt.stdH K 0) (_root_.Formalism.MainNotions.S.Cnt.stdLat K 0) := by
    unfold _root_.Formalism.HermitianLatticesTheory.genus _root_.Formalism.HermitianLatticesTheory.SameGenus
    exact ⟨hlat, fun p _ => ⟨1, one_mem _, hsub _ _⟩⟩
  have hs : ∃ s, _root_.Formalism.ThetaLiftIndependence.IsClassReps (_root_.Formalism.MainNotions.S.Cnt.stdH K 0) (_root_.Formalism.MainNotions.S.Cnt.stdLat K 0) s := by
    refine ⟨{_root_.Formalism.MainNotions.S.Cnt.stdLat K 0}, ?_⟩
    unfold _root_.Formalism.ThetaLiftIndependence.IsClassReps
    refine ⟨fun M hM => ?_, fun M _ => ⟨_root_.Formalism.MainNotions.S.Cnt.stdLat K 0,
      ⟨Finset.mem_singleton_self _, 1, one_mem _, hsub _ _⟩,
      fun N hN => Finset.mem_singleton.mp hN.1⟩⟩
    rw [Finset.mem_singleton.mp hM]
    exact hgen
  have hchoose : hs.choose = {_root_.Formalism.MainNotions.S.Cnt.stdLat K 0} := by
    have hspec := hs.choose_spec
    unfold _root_.Formalism.ThetaLiftIndependence.IsClassReps at hspec
    obtain ⟨N, ⟨hN, -⟩, -⟩ := hspec.2 _ hgen
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨?_, fun M _ => hsub _ _⟩
    have hN' : N = _root_.Formalism.MainNotions.S.Cnt.stdLat K 0 := hsub _ _
    exact hN' ▸ hN
  have hcard : Nat.card (_root_.Formalism.ThetaLiftIndependence.autL (_root_.Formalism.MainNotions.S.Cnt.stdH K 0) (_root_.Formalism.MainNotions.S.Cnt.stdLat K 0)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨inferInstance, ⟨⟨1, ?_⟩⟩⟩
    unfold _root_.Formalism.ThetaLiftIndependence.autL
    exact ⟨one_mem _, hsub _ _⟩
  unfold _root_.Formalism.MainNotions.S.Cnt.massU
  rw [_root_.Formalism.HermitianLatticesTheory.massBasic_mass_eq _ _ hs, hchoose, Finset.sum_singleton, hcard]
  norm_num

open NumberField Matrix in
open scoped ENNReal Classical in

theorem _root_.GlobalTheory.Mass.StdMass.main : ∀ (K : Type) [Field K] [NumberField K]
    [StarRing K], _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ j : ℕ, (_root_.Formalism.MainNotions.S.Cnt.stdH K j).IsSymm ∧
      _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice (_root_.Formalism.MainNotions.S.Cnt.stdH K j) (_root_.Formalism.MainNotions.S.Cnt.stdLat K j) j ∧ 0 < _root_.Formalism.MainNotions.S.Cnt.massU K j ∧ _root_.Formalism.MainNotions.S.Cnt.massU K 0 = 1 ∧
      ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
        (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V), _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice h L j →
        _root_.Formalism.HermitianLatticesTheory.mass h L = _root_.Formalism.MainNotions.S.Cnt.massU K j ∧ _root_.GlobalTheory.Mass.PD h := by
  intro K _ _ _ hK j
  have hsymm : (_root_.Formalism.MainNotions.S.Cnt.stdH K j).IsSymm := _root_.ReciprocityTheory.ChartRestriction.L3.stdForm_isSymm K j
  have hortho : _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice (_root_.Formalism.MainNotions.S.Cnt.stdH K j) (_root_.Formalism.MainNotions.S.Cnt.stdLat K j) j := _root_.Formalism.MainNotions.StandardLattice.stdLat_ortho K j
  refine ⟨hsymm, hortho, ?_, massU_zero_eq_one K, fun V _ _ _ _ h L hL => ⟨?_, ?_⟩⟩
  · unfold _root_.Formalism.MainNotions.S.Cnt.massU
    exact _root_.ReciprocityTheory.ChartRestriction.L3.mass_pos_of_ortho hK hsymm hortho
  · exact (_root_.Formalism.MainNotions.StandardLattice.mass_ortho K hK j V h L hL).trans rfl
  · have hpos := _root_.ReciprocityTheory.ChartRestriction.L3.isTotPosDef_of_ortho hK (_root_.GlobalTheory.Mass.StdMass.isSymm_of_ortho hL) hL
    unfold _root_.ReciprocityTheory.ChartRestriction.L3.IsTotPosDef at hpos
    unfold _root_.GlobalTheory.Mass.PD
    exact fun τ x hx => hpos x hx τ

end GlobalTheory.Mass.StdMass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryImageStandardLatticeEqSelfDualLattice
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

noncomputable section

namespace GlobalTheory.StdLatImg

open GlobalTheory.HL.CoordInnerSnd

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

def gen (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)) : Set V :=
  {v | (∀ a, H.h v (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h v (Fr.e a) ∈ M.L.O) ∧
    ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF v ∧ H.mkW Fr.f w ∈ L}

lemma cj_mem' {x : E} (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := GlobalTheory.UnramOrder.cj_mem M.L hx

lemma smul_mem_lat (Λ : Submodule M.L.O V) {c : E} (hc : c ∈ M.L.O) {w : V} (hw : w ∈ Λ) :
    c • w ∈ Λ := Λ.smul_mem (⟨c, hc⟩ : M.L.O) hw

lemma h_prF_left (Fr : FrameD H r) (p s : V) (h1 : ∀ a, H.h p (Fr.e a) = 0)
    (h2 : ∀ a, H.h p (Fr.es a) = 0) : H.h (Fr.prF s) p = H.h s p := by
  rw [← hl_apply, ← hl_apply]
  simp only [FrameD.prF, map_sub, map_sum, map_smul, hl_apply, h_swap_zero (h1 _),
    h_swap_zero (h2 _)]
  simp

lemma decomp (Fr : FrameD H r) (v s : V) : H.h v s = H.h (Fr.prF v) s +
    ∑ a, H.h v (Fr.es a) * H.h (Fr.e a) s + ∑ a, H.h v (Fr.e a) * H.h (Fr.es a) s := by
  rw [← hl_apply, ← hl_apply]
  simp only [FrameD.prF, map_sub, map_sum, map_smul, hl_apply, smul_eq_mul]
  ring

end GlobalTheory.StdLatImg

namespace GlobalTheory.StdLatImg

open GlobalTheory.HL.CoordInnerSnd

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

lemma memL_iff (Fr : FrameD H r) (Λ : Submodule M.L.O V) (L : Submodule M.L.O (H.Wb Fr.f))
    (hL : (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f) (w : ↥(H.perp (H.X Fr.f))) :
    H.mkW Fr.f w ∈ L ↔ ∃ x : ↥(H.perp (H.X Fr.f)), (x : V) ∈ Λ ∧ (x : V) - w ∈ H.X Fr.f := by
  rw [← SetLike.mem_coe, hL]
  constructor
  · rintro ⟨x, hx, he⟩; exact ⟨x, hx, (mkW_eq Fr x w).1 he⟩
  · rintro ⟨x, hx, he⟩; exact ⟨x, hx, (mkW_eq Fr x w).2 he⟩

lemma symm_mem_gen (Fr : FrameD H r) (Λ : Submodule M.L.O V) (hSD : H.IsSelfDual Λ)
    (he : ∀ a : Fin r, Fr.f a.castSucc ∈ Λ) (L : Submodule M.L.O (H.Wb Fr.f))
    (hL : (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f) (n : V ≃ₗ[E] V) (hn : IsUnitary H n)
    (hfix : ∀ a : Fin r, n (Fr.f a.castSucc) = Fr.f a.castSucc) (hes : ∀ a, n (Fr.es a) ∈ Λ)
    (hX : ∀ v ∈ H.perp (H.X Fr.f), n v - v ∈ H.X Fr.f) {u : V} (hu : u ∈ Λ) :
    n.symm u ∈ gen Fr L := by
  set v := n.symm u with hv
  have hnv : n v = u := by simp [hv]
  have hve : ∀ a, H.h v (Fr.e a) = H.h u (Fr.e a) := fun a => by
    rw [← hn v (Fr.e a), hnv]; exact congrArg _ (hfix a)
  have hveO : ∀ a, H.h v (Fr.e a) ∈ M.L.O := fun a => by
    rw [hve]; exact (hSD.2.2 u).1 hu _ (he a)
  have hvesO : ∀ a, H.h v (Fr.es a) ∈ M.L.O := fun a => by
    rw [← hn v (Fr.es a), hnv]; exact (hSD.2.2 u).1 hu _ (hes a)
  refine ⟨hvesO, hveO, ⟨Fr.prF v, prF_perp Fr v⟩, rfl, ?_⟩
  set v' := v - ∑ a, H.h v (Fr.e a) • Fr.es a with hv'
  have hv'p : v' ∈ H.perp (H.X Fr.f) := by
    rw [mem_perpX]
    intro b
    rw [← hl_apply]
    simp only [hv', map_sub, map_sum, map_smul, hl_apply, h_es_e, smul_eq_mul]
    simp
  have hx : n v' = u - ∑ a, H.h v (Fr.e a) • n (Fr.es a) := by
    simp [hv', map_sub, map_sum, hnv]
  have hxΛ : n v' ∈ Λ := by
    rw [hx]
    exact Λ.sub_mem hu (Λ.sum_mem fun a _ => smul_mem_lat Λ (hveO a) (hes a))
  have hxv' := hX v' hv'p
  have hxp : n v' ∈ H.perp (H.X Fr.f) := by
    have := (H.perp (H.X Fr.f)).add_mem hv'p (X_le_perp Fr hxv')
    simpa using this
  rw [memL_iff Fr Λ L hL]
  refine ⟨⟨n v', hxp⟩, hxΛ, ?_⟩
  have hpr : Fr.prF v - v' = -∑ a, H.h v (Fr.es a) • Fr.e a := by
    simp only [FrameD.prF, hv']; abel
  have : (n v' : V) - Fr.prF v = (n v' - v') - (Fr.prF v - v') := by abel
  show n v' - Fr.prF v ∈ H.X Fr.f
  rw [this, hpr]
  exact (H.X Fr.f).sub_mem hxv' ((H.X Fr.f).neg_mem
    ((H.X Fr.f).sum_mem fun a _ => (H.X Fr.f).smul_mem _ (e_mem_X Fr a)))

end GlobalTheory.StdLatImg

namespace GlobalTheory.StdLatImg

open GlobalTheory.HL.CoordInnerSnd

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

lemma h_gen_mem (Fr : FrameD H r) (Λ : Submodule M.L.O V) (hSD : H.IsSelfDual Λ)
    (L : Submodule M.L.O (H.Wb Fr.f)) (hL : (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f)
    {v s : V} (hv : v ∈ gen Fr L) (hs : s ∈ gen Fr L) : H.h v s ∈ M.L.O := by
  obtain ⟨hv1, hv2, wv, hwv, hwvL⟩ := hv
  obtain ⟨hs1, hs2, ws, hws, hwsL⟩ := hs
  obtain ⟨x, hxΛ, hxd⟩ := (memL_iff Fr Λ L hL wv).1 hwvL
  obtain ⟨x', hx'Λ, hx'd⟩ := (memL_iff Fr Λ L hL ws).1 hwsL
  rw [hwv] at hxd
  rw [hws] at hx'd

  have hpp : H.h (Fr.prF v) (Fr.prF s) = H.h (x : V) (x' : V) := by
    have e1 : Fr.prF v = x - ((x : V) - Fr.prF v) := by abel
    have e2 : Fr.prF s = x' - ((x' : V) - Fr.prF s) := by abel
    have k1 : H.h ((x : V) - Fr.prF v) (Fr.prF s) = 0 :=
      h_swap_zero (prF_perp Fr s _ hxd)
    have k2 : H.h (x : V) ((x' : V) - Fr.prF s) = 0 := x.2 _ hx'd
    calc H.h (Fr.prF v) (Fr.prF s)
        = H.h (x : V) (Fr.prF s) - H.h ((x : V) - Fr.prF v) (Fr.prF s) := by
          rw [← hl_apply, ← hl_apply, ← hl_apply, ← map_sub, ← e1]
      _ = H.h (x : V) (Fr.prF s) := by rw [k1, sub_zero]
      _ = H.h (x : V) (x' : V) := by
          rw [e2, ← neg_add_eq_sub, h_add_right, ← neg_one_smul E ((x' : V) - Fr.prF s),
            h_smul_right, k2, mul_zero, zero_add]
  have hpO : H.h (Fr.prF v) s ∈ M.L.O := by
    have e3 : H.h (Fr.prF v) s = M.L.cj (H.h s (Fr.prF v)) := H.h_herm _ _
    rw [e3, ← h_prF_left Fr (Fr.prF v) s (h_prF_e Fr v) (h_prF_es Fr v), H.h_herm, M.L.cj_cj, hpp]
    exact (hSD.2.2 x).1 hxΛ _ hx'Λ
  rw [decomp Fr v s]
  refine M.L.O.add_mem (M.L.O.add_mem hpO ?_) ?_
  · refine M.L.O.sum_mem fun a _ => M.L.O.mul_mem (hv1 a) ?_
    rw [H.h_herm]; exact cj_mem' (hs2 a)
  · refine M.L.O.sum_mem fun a _ => M.L.O.mul_mem (hv2 a) ?_
    rw [H.h_herm]; exact cj_mem' (hs1 a)

theorem eq_img_lamStd : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → (∀ a : Fin r, Fr.f a.castSucc ∈ Λ) → ∀ L : Submodule M.L.O (H.Wb Fr.f), (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f → ∀ n : V ≃ₗ[E] V, IsUnitary H n → (∀ a : Fin r, n (Fr.f a.castSucc) = Fr.f a.castSucc) → (∀ a, n (Fr.es a) ∈ Λ) → (∀ v ∈ H.perp (H.X Fr.f), n v - v ∈ H.X Fr.f) → Λ = img n (Fr.LamStd L) := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Fr Λ hSD he L hL n hn hfix hes hX
  have hb := fun {u : V} (hu : u ∈ Λ) => symm_mem_gen Fr Λ hSD he L hL n hn hfix hes hX hu
  have hgen : FrameD.LamStd Fr L = Submodule.span M.L.O (gen Fr L) := rfl
  apply le_antisymm
  · intro u hu
    rw [hgen]
    exact ⟨n.symm u, Submodule.subset_span (hb hu), by simp⟩
  · rw [hgen, img, Submodule.map_le_iff_le_comap, Submodule.span_le]
    intro s hs
    show n s ∈ Λ
    refine (hSD.2.2 (n s)).2 fun t ht => ?_
    have ht' : n (n.symm t) = t := by simp
    rw [← ht', hn]
    exact h_gen_mem Fr Λ hSD L hL hs (hb ht)

end GlobalTheory.StdLatImg
end
end

