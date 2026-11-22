import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0234
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0233
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0246
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0240
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0247
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDatumOfTwoCongruentFrames
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocOver.TermOver

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

lemma mem_img (g : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) (x : V) :
    x ∈ img g Λ ↔ ∃ y ∈ Λ, g y = x := by
  simp [img, Submodule.mem_map]

lemma img_mul (g k : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) : img (g * k) Λ = img g (img k Λ) := by
  ext x
  simp only [mem_img]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨k y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

lemma img_one (Λ : Submodule M.L.O V) : img (1 : V ≃ₗ[E] V) Λ = Λ := by
  ext x
  simp only [mem_img]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma img_selfDual (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g)
    {Λ : Submodule M.L.O V} (hΛ : H.IsSelfDual Λ) : H.IsSelfDual (img g Λ) := by
  obtain ⟨h1, h2, h3⟩ := hΛ
  refine ⟨h1.map _, ?_, ?_⟩
  · have himg : ((img g Λ : Submodule M.L.O V) : Set V) = (g : V →ₗ[E] V) '' (Λ : Set V) := by
      ext x
      simp only [SetLike.mem_coe, mem_img, Set.mem_image]
      rfl
    rw [himg, ← Submodule.map_span, h2, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr g.surjective
  · intro x
    constructor
    · intro hx y hy
      obtain ⟨a, ha, rfl⟩ := (mem_img g Λ x).1 hx
      obtain ⟨b, hb, rfl⟩ := (mem_img g Λ y).1 hy
      rw [hg]
      exact (h3 a).1 ha b hb
    · intro hx
      obtain ⟨a, rfl⟩ := g.surjective x
      refine (mem_img g Λ _).2 ⟨a, (h3 a).2 fun y hy => ?_, rfl⟩
      have := hx (g y) ((mem_img g Λ _).2 ⟨y, hy, rfl⟩)
      rwa [hg] at this

lemma img_frame (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g)
    {Λ : Submodule M.L.O V} {r : ℕ} {f : Fin (r + 1) → V} {T : F} (hf : H.IsFrame Λ r f T) :
    H.IsFrame (img g Λ) r (fun b => g (f b)) T := by
  obtain ⟨⟨p1, p2, p3⟩, h2, h3, h4, h5⟩ := hf
  refine ⟨⟨fun a => (mem_img g Λ _).2 ⟨f a, p1 a, rfl⟩, ?_, ?_⟩, ?_, ?_, h4, h5⟩
  · exact p2.map' (g : V →ₗ[E] V) (LinearEquiv.ker g)
  · intro x hx hs
    obtain ⟨y, hy, rfl⟩ := (mem_img g Λ x).1 hx
    have hrange : Set.range (fun b => g (f b)) = (g : V →ₗ[E] V) '' Set.range f := by
      rw [← Set.range_comp]
      rfl
    rw [hrange, ← Submodule.map_span] at hs
    obtain ⟨y', hy', hyy⟩ := hs
    have hyy' : y' = y := g.injective hyy
    subst hyy'
    have hO := p3 y' hy hy'
    have hmap : ∀ v ∈ Submodule.span M.L.O (Set.range f),
        g v ∈ Submodule.span M.L.O (Set.range fun b => g (f b)) := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨b, rfl⟩ := hv
        exact Submodule.subset_span ⟨b, rfl⟩
      | zero => simp
      | add a b _ _ ha hb =>
        rw [map_add]
        exact Submodule.add_mem _ ha hb
      | smul c a _ ha =>
        have : g (c • a) = c • g a := by
          change g ((c : E) • a) = (c : E) • g a
          exact map_smul g (c : E) a
        rw [this]
        exact Submodule.smul_mem _ c ha
    exact hmap y' hO
  · intro a b hab
    rw [hg]
    exact h2 a b hab
  · rw [hg]
    exact h3

lemma side (hM : M.OK) (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) {Λ : Submodule M.L.O V}
    {f : Fin (r + 1) → V} (hΛ : H.IsSelfDual Λ) (hf : H.IsFrame Λ r f Fr.T) (hT : Tri E Fr.f f) :
    ∃ L : Submodule M.L.O (H.Wb Fr.f), Fr.IsInner L ∧
      ∃ n ∈ Fr.N, f = (fun b => n (Fr.f b)) ∧ Λ = img n (Fr.LamStd L) := by
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.frameDual_unipotentGroup_acts_unitriangular_onto M hM H r Fr hf.2.2.2.2
  obtain ⟨n, hn, hnf⟩ := h3 f hT
  have hu : IsUnitary H n⁻¹ := ((h1 _).1 (Fr.N.inv_mem hn)).1
  have hfr : H.IsFrame (img n⁻¹ Λ) r Fr.f Fr.T := by
    have := img_frame H hu hf
    have he : (fun b => n⁻¹ (f b)) = Fr.f := by
      funext b
      rw [hnf]
      exact n.symm_apply_apply _
    rwa [he] at this
  obtain ⟨L, hL, -, n0, hn0, hfix, hΛ0⟩ :=
    GlobalTheory.T.selfDual_lattice_frame_eq_standard_translate M hM H r Fr (img n⁻¹ Λ) (img_selfDual H hu hΛ) hfr
  refine ⟨L, hL, n * n0, Fr.N.mul_mem hn hn0, ?_, ?_⟩
  · rw [hnf]
    funext b
    change n (Fr.f b) = n (n0 (Fr.f b))
    rw [hfix]
  · rw [img_mul, ← hΛ0, ← img_mul, mul_inv_cancel, img_one]

end

theorem exists_datum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (P : FPair H r) (t : Term V M r), H.IsTerm t → t.T = P.A.T → t.T' = P.B.T → Tri E P.A.f t.f → Tri E P.B.f t.f' → ∃ d : Datum P, IsTermOver P d t := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r P t ht hT hT' hf hf'
  obtain ⟨hsd, hfr, hfr', -, -, hg⟩ := ht
  rw [hT] at hfr
  rw [hT'] at hfr'
  obtain ⟨L, hL, n, hn, hnf, hnΛ⟩ := side hM H r P.A hsd hfr hf
  obtain ⟨L', hL', n', hn', hnf', hnΛ'⟩ := side hM H r P.B hsd hfr' hf'
  let s : Term V M r := ⟨t.abelian₂, P.A.f, P.B.f, t.T, t.T'⟩
  refine ⟨⟨L, L', hL, hL', {p | ∃ g, M.split = some g ∧ p ∈ H.iotaGraph g s}, ?_⟩, hT, hT',
    ⟨n, hn, hnf, hnΛ⟩, ⟨n', hn', hnf', hnΛ'⟩, ?_⟩
  · intro h
    ext p
    simp [h]
  · intro g hgs
    refine ⟨(hg g hgs).2.2, ?_⟩
    ext p
    constructor
    · intro hp
      exact ⟨g, hgs, hp⟩
    · rintro ⟨g', hg', hp⟩
      obtain rfl : g = g' := Option.some.inj (hgs.symm.trans hg')
      exact hp

end GlobalTheory.LocOver.TermOver
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralUnipotentLiftCorner
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.LiftCorner

lemma hpk_eI (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) j = if j = esI k r a then 1 else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

lemma herm_bvec (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) (x : ℂ) :
    herm (Hpk k r) (bvec j) (x • bvec (eI k r a)) = star x * (if j = esI k r a then 1 else 0) := by
  rw [← hpk_eI]
  simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply, apply_ite (starRingEnd ℂ), ite_mul]

lemma form_smul_left {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (u v : Fin n → E) (x : E) : form σ J (x • u) v = x * form σ J u v := by
  simp [form, Matrix.mulVec_smul, dotProduct_smul]

lemma form_smul_right {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (u v : Fin n → E) (x : E) : form σ J u (x • v) = σ x * form σ J u v := by
  simp [form, dotProduct, Finset.mul_sum, mul_assoc]

lemma form_cols {E : Type} [Field E] (σ : E →+* E) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P : Matrix (Fin n) (Fin m) E) (x z : Fin m) :
    form σ J (fun i => P i z) (fun i => P i x) = pairM σ J P P x z := by
  simp only [form, pairM, cT, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem lift_corner : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (p : UTr r) (l : InfinitePlace E → ℂ), l ∈ ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inr (.inl p))) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inr (.inl p))) → degB r β ≤ degB r (.inr (.inr (.inl p))) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV p l hl
  obtain ⟨⟨a, b⟩, hab⟩ := p
  have hab' : a.val < b.val := hab
  have ha := a.isLt
  have hb := b.isLt
  obtain ⟨-, -, -, -, hFr, -, hLat, -, -, hAd⟩ := id hV
  obtain ⟨c, hc, hlc⟩ := hl
  dsimp only at hc hlc
  let e : Fin (2 * r + k + 1) → E := fun i => P i a.castSucc
  let y : Fin (2 * r + k + 1) → E := c • e
  have hiso : ∀ x z : Fin r,
      form (σ : E →+* E) J (fun i => P i z.castSucc) (fun i => P i x.castSucc) = 0 := by
    intro x z
    rw [form_cols, hFr.2]
    simp [TF, Matrix.diagonal_apply, Fin.castSucc_ne_last]
  have hd : ∀ j, dInv E j ≠ 0 := fun j =>
    pow_ne_zero _ (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot))
  have hG : rowE (σ : E →+* E) J (fun i => P i b.castSucc) y 0 ∈ GN (σ : E →+* E) J Λ P := by
    refine GlobalTheory.T.rowE_mem_GN_of_form_add_trace_eq_zero F E σ k r J Λ P f T A s hV b y 0 ?_ ?_ ?_ ?_
    · intro c' _
      show form _ J (c • e) _ = 0
      rw [form_smul_left, hiso, mul_zero]
    · show form _ J (c • e) (c • e) + 0 + (σ : E →+* E) 0 = 0
      rw [form_smul_left, form_smul_right, hiso]
      simp
    · intro c' hc'
      have hmem : c' * c ∈ dInv E (r - a.val) := by
        have := FractionalIdeal.mul_mem_mul hc' hc
        rwa [mul_comm (dInv E (r - a.val)), ← mul_assoc, inv_mul_cancel₀ (hd _), one_mul] at this
      have hy : c' • y = (c' * c) • e := by
        simp only [y, smul_smul]
      rw [hy]
      apply hLat
      apply Submodule.subset_span
      refine ⟨Fin.castAdd r a.castSucc, c' * c, ?_, ?_⟩
      · simpa [id1, Fin.append_left] using hmem
      · ext i
        simp [sideM, Fin.append_left, e]
    · exact (dInv E _ : Submodule (𝓞 E) E).zero_mem
  have hAy : ∀ w : InfinitePlace E, (A w).mulVec (fun l => w.embedding (y l)) =
      (w.embedding c * (s a : ℂ)) • bvec (eI k r a) := by
    intro w
    have h1 : (fun l => w.embedding (y l)) = w.embedding c • fun l => w.embedding (P l a.castSucc) := by
      ext l
      simp [y, e]
    rw [h1, Matrix.mulVec_smul, (hAd w a).1, smul_smul]
  have hent : ∀ w i j, gM A (rowE (σ : E →+* E) J (fun i => P i b.castSucc) y 0) w i j =
      (if i = j then 1 else 0) +
        (if i = eI k r a ∧ j = esI k r b then (s a : ℂ) * s b * w.embedding c else 0) -
        (if i = eI k r b ∧ j = esI k r a then (s b : ℂ) * star (w.embedding c * (s a : ℂ)) else 0) := by
    intro w i j
    rw [GlobalTheory.T.rowIsometry_entries_in_modelCoordinates F E σ k r J Λ P f T A s hV b y 0 w i j, hAy w, herm_bvec]
    simp only [bvec, Pi.smul_apply, Pi.single_apply, smul_eq_mul, map_zero, mul_zero, add_zero, ite_and]
    split_ifs <;> ring
  refine ⟨_, hG, fun w => ?_, fun β hβ _ w => ?_⟩
  · show gM A _ w (eI k r a) (esI k r b) = l w
    rw [hent, hlc w]
    have h1 : eI k r a ≠ esI k r b := by simp [Fin.ext_iff, eI, esI]; omega
    have h2 : eI k r a ≠ eI k r b := by simp [Fin.ext_iff, eI]; omega
    simp [h1, h2]
    first | done | (push_cast; ring)
  · rcases β with p' | a' | p' | a'
    · obtain ⟨⟨a', b'⟩, h'⟩ := p'
      have h'' : a'.val < b'.val := h'
      show gM A _ w (eI k r a') (eI k r b') = 0
      rw [hent]
      simp only [eI, esI, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · show (fun j' => gM A _ w (eI k r a') (wI k r j')) = (0 : Fin (k + 1) → ℂ)
      funext j'
      have := j'.isLt
      rw [hent]
      simp only [eI, esI, wI, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · obtain ⟨⟨a', b'⟩, h'⟩ := p'
      have h'' : a'.val < b'.val := h'
      have hne : ¬ (a'.val = a.val ∧ b'.val = b.val) := by
        rintro ⟨e1, e2⟩
        obtain rfl := Fin.ext e1
        obtain rfl := Fin.ext e2
        exact hβ rfl
      show gM A _ w (eI k r a') (esI k r b') = 0
      rw [hent]
      simp only [eI, esI, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · show (gM A _ w (eI k r a') (esI k r a')).im = 0
      rw [hent]
      simp only [eI, esI, Fin.ext_iff]
      split_ifs <;> first | omega | simp

end GlobalTheory.SnMass.VolN.LiftCorner
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralUnipotentLiftEntry
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.LiftEntry

theorem eI_inj {k r : ℕ} {a b : Fin r} : eI k r a = eI k r b ↔ a = b := by
  simp [eI, Fin.ext_iff]

theorem eI_ne_esI {k r : ℕ} (a b : Fin r) : eI k r a ≠ esI k r b := by
  simp only [eI, esI, ne_eq, Fin.ext_iff]; omega

theorem eI_ne_wI {k r : ℕ} (a : Fin r) (j : Fin (k + 1)) : eI k r a ≠ wI k r j := by
  simp only [eI, wI, ne_eq, Fin.ext_iff]; omega

theorem Hpk_esI {k r : ℕ} (b : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r b) j = if j = eI k r b then 1 else 0 := by
  simp only [Hpk, esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem herm_single {k r : ℕ} (b : Fin r) (c : ℂ) (j : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (bvec j) (c • bvec (esI k r b)) = if j = eI k r b then star c else 0 := by
  simp only [herm, bvec, dotProduct, mulVec, Pi.star_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single (esI k r b)]
  · simp only [if_true, mul_one, star_mul', star_one]
    rw [Finset.sum_eq_single j]
    · simp [Hpk_esI]
    · intro m _ hm; simp [hm]
    · simp
  · intro m _ hm; simp [hm]
  · simp

theorem wI_ne_eI {k r : ℕ} (j : Fin (k + 1)) (a : Fin r) : wI k r j ≠ eI k r a := (eI_ne_wI a j).symm

theorem esI_ne_eI {k r : ℕ} (a b : Fin r) : esI k r a ≠ eI k r b := (eI_ne_esI b a).symm

end GlobalTheory.SnMass.VolN.LiftEntry

namespace GlobalTheory.SnMass.VolN.LiftEntry

theorem form_smul_left {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (c : E) (x z : Fin n → E) : form σ J (c • x) z = c * form σ J x z := by
  simp [form, mulVec_smul, dotProduct_smul]

theorem form_smul_right {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (c : E) (x z : Fin n → E) : form σ J x (c • z) = σ c * form σ J x z := by
  simp only [form, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem form_col {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} {a b : Type} [Fintype a] [Fintype b]
    (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) b E) (Y : Matrix (Fin n) a E) (i : a) (j : b) :
    form σ J (fun l => X l j) (fun l => Y l i) = pairM σ J X Y i j := by
  simp only [form, pairM, cT, dotProduct, mulVec, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end GlobalTheory.SnMass.VolN.LiftEntry

namespace GlobalTheory.SnMass.VolN.LiftEntry

theorem lift_entry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (p : UTr r) (l : InfinitePlace E → ℂ), l ∈ ideLat (dInv E (r - p.1.1.val) * (dInv E (r - p.1.2.val))⁻¹) (s p.1.1 / s p.1.2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inl p) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inl p) → degB r β ≤ degB r (.inl p) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV p l hl
  have hV' := hV
  obtain ⟨hcm, -, -, -, -, hdu, htup, -, hs, had⟩ := hV'
  have hi : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    change τ (σ (σ x)) = _
    rw [hcm.2.2.2, hcm.2.2.2, star_star]
  obtain ⟨u, hu, hlu⟩ := hl
  obtain ⟨⟨a, b⟩, hab⟩ := p
  simp only at hu hlu hab ⊢
  set y : Fin (2 * r + k + 1) → E := (-(σ u)) • fun i => f i b with hy
  refine ⟨rowE (σ : E →+* E) J (fun i => P i a.castSucc) y 0, ?_, ?_⟩
  · refine GlobalTheory.T.rowE_mem_GN_of_form_add_trace_eq_zero F E σ k r J Λ P f T A s hV a y 0 (fun c hc => ?_) ?_ (fun c hc => ?_)
      (FractionalIdeal.zero_mem _)
    · rw [hy, form_smul_left, form_col, hdu.1]
      have : c.castSucc ≠ b.castSucc := fun h => absurd (Fin.castSucc_injective _ h ▸ hc) (not_le.2 hab)
      simp [this]
    · rw [hy, form_smul_left, form_smul_right, form_col, hdu.2]
      simp
    · have hsu : (σ : E →+* E) u ∈ dInv E (r - a.val) * (dInv E (r - b.val))⁻¹ :=
        (GlobalTheory.SnMass.FrameDual.Stab.mul (GlobalTheory.SnMass.FrameDual.stab_dInv hi _)
          ((GlobalTheory.SnMass.FrameDual.stab_dInv hi _).inv hi (GlobalTheory.SnMass.FrameDual.dInv_ne_zero _))) u hu
      have hm : c * σ u ∈ (dInv E (r - b.val))⁻¹ := by
        have := FractionalIdeal.mul_mem_mul hc hsu
        rwa [← mul_assoc, inv_mul_cancel₀ (GlobalTheory.SnMass.FrameDual.dInv_ne_zero _), one_mul] at this
      have e : c • y = (-(c * σ u)) • fun i => sideM P f i (Fin.natAdd (r + 1) b) := by
        ext i; simp [hy, sideM, mul_comm, mul_left_comm]
      rw [e]
      refine htup (Submodule.subset_span ⟨Fin.natAdd (r + 1) b, -(c * σ u), ?_, rfl⟩)
      rw [GlobalTheory.SnMass.FrameDual.frameDualTupleIdeals_natAdd]
      exact Submodule.neg_mem _ hm
  · have hv : ∀ w : InfinitePlace E, (A w).mulVec (fun l => w.embedding (y l)) =
        (-(star (w.embedding u)) * ((s b)⁻¹ : ℂ)) • bvec (esI k r b) := by
      intro w
      have e : (fun l => w.embedding (y l)) = (-(w.embedding (σ u))) • fun l => w.embedding (f l b) := by
        ext l; simp [hy]
      rw [e, mulVec_smul, (had w b).2, smul_smul, hcm.2.2.2]
    have key : ∀ (w : InfinitePlace E) (a' : Fin r) (j : Fin (2 * r + k + 1)),
        gM A (rowE (σ : E →+* E) J (fun i => P i a.castSucc) y 0) w (eI k r a') j =
          (if eI k r a' = j then 1 else 0) - (if a' = a ∧ j = eI k r b then
            (s a : ℂ) * star (-(star (w.embedding u)) * ((s b)⁻¹ : ℂ)) else 0) := by
      intro w a' j
      rw [GlobalTheory.T.rowIsometry_entries_in_modelCoordinates F E σ k r J Λ P f T A s hV a y 0 w, hv w, herm_single]
      simp [bvec, Pi.single_apply, eI_ne_esI, eI_inj, ite_and]
    refine ⟨fun w => ?_, fun β hβ _ w => ?_⟩
    · change gM A _ w (eI k r a) (eI k r b) = l w
      rw [key, hlu]
      simp only [eI_inj, hab.ne, if_false, true_and, if_true, zero_sub]
      push_cast
      simp only [star_mul', star_neg, star_star, Complex.star_def, Complex.conj_ofReal, map_inv₀, Complex.conj_conj]
      ring
    · rcases β with ⟨⟨a', b'⟩, hab'⟩ | a' | ⟨⟨a', b'⟩, hab'⟩ | a'
      · change gM A _ w (eI k r a') (eI k r b') = 0
        rw [key]
        have hne : ¬ (a' = a ∧ eI k r b' = eI k r b) := by
          rintro ⟨rfl, h⟩
          obtain rfl := eI_inj.1 h
          exact hβ rfl
        have hne' : a' ≠ b' := ne_of_lt hab'
        rw [if_neg hne, if_neg (fun h => hne' (eI_inj.1 h)), sub_zero]
      · change (fun j => gM A _ w (eI k r a') (wI k r j)) = (0 : Fin (k + 1) → ℂ)
        funext j
        rw [key]
        simp [eI_ne_wI, wI_ne_eI]
      · change gM A _ w (eI k r a') (esI k r b') = 0
        rw [key]
        simp [eI_ne_esI, esI_ne_eI]
      · change (gM A _ w (eI k r a') (esI k r a')).im = 0
        rw [key]
        simp [eI_ne_esI, esI_ne_eI]

end GlobalTheory.SnMass.VolN.LiftEntry
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMixedSpaceReImCoordsTotallyComplexStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mixedSpace_reIm_coords_totallyComplex : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∃ e : mixedEmbedding.mixedSpace E ≃L[ℝ] ((InfinitePlace E → ℝ) × (InfinitePlace E → ℝ)), MeasurePreserving e volume volume ∧ ∀ x : E, e (mixedEmbedding E x) = (reV x, imV x) := by
  first | exact @GlobalTheory.SnMass.SkewVol.mixedSpace_reIm_coords | exact GlobalTheory.SnMass.SkewVol.mixedSpace_reIm_coords | (intros; apply GlobalTheory.SnMass.SkewVol.mixedSpace_reIm_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FourMulAddFiveLeRank
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.CmHermitianRankFrames

theorem four_mul_add_five_le_rank (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) :
    4 * D.R.rS + 5 ≤ X.B.I.n := by

  rw [X.n_eq]
  have hk := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
  omega

theorem cm_herm_rank_frames : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), IsCMExt X.B.I.F X.B.I.E X.B.I.cm.sig ∧ IsHermND X.B.I.cm.sig X.B.I.J ∧ 4 * D.R.rS + 5 ≤ X.B.I.n ∧ ∀ u, ∃ T : X.B.I.F, (Formalism.L2.SG.TypedSets.frameOf X u).IsStd X.B.I.cm.sig X.B.I.J T :=
  fun D X => ⟨MassDataVolumesW.stepCM X, MassDataVolumesW.stepHerm X, four_mul_add_five_le_rank D X,
    fun u => MassDataLevelSSteps.frameStd_holds X u⟩

end GlobalTheory.CmHermitianRankFrames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FractionalIdealBasisTransportMeasurePreservingStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionalIdeal_basis_transport_measurePreserving : ∀ (K : Type) [Field K] [NumberField K] {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] [BorelSpace W] (μ : Measure W) (e : mixedEmbedding.mixedSpace K ≃L[ℝ] W), MeasurePreserving e volume μ → ∀ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ W), (Submodule.span ℤ (Set.range b) : Set W) = (fun x : K => e (mixedEmbedding K x)) '' {x : K | x ∈ (J : FractionalIdeal (𝓞 K)⁰ K)} ∧ μ (ZSpan.fundamentalDomain b) = ENNReal.ofReal (FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 K)⁰ K) * (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|) := by
  first | exact @GlobalTheory.SnMass.VolN.fractionalIdeal_basis_transport | exact GlobalTheory.SnMass.VolN.fractionalIdeal_basis_transport | (intros; apply GlobalTheory.SnMass.VolN.fractionalIdeal_basis_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadical
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory

theorem haarLie_isHaarOn_Nset : ∀ (k r : ℕ) (κ : ENNReal), 0 < κ → κ < ⊤ →
    IsHaarOn (Nset k r) (haarLie (Nset k r) κ) :=
  fun k r κ h0 h1 => Formalism.MainNotions.BridgeCSB.haarLieN k r κ h0.ne' h1.ne

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFrameWeightSumSameDatumLeStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFrame_weightSum_sameDatum_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ') ≤ ENNReal.ofReal ((N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  first | exact @GlobalTheory.DegCnt.omSum_sameDat_le | exact GlobalTheory.DegCnt.omSum_sameDat_le | (intros; apply GlobalTheory.DegCnt.omSum_sameDat_le <;> assumption)
end

