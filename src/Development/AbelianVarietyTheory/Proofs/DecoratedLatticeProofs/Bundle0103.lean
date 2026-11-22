import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureFirst
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.AutomorphicFormsFiniteDimensional
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalConjUnipotentRadicalIsotropic
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.S Formalism.UG

namespace GlobalTheory.CuspGeo

theorem hform_mulVec_mulVec {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J g : Matrix (Fin n) (Fin n) A)
    (hg : cT s g * J * g = J) (x y : Fin n → A) : hform s J (g *ᵥ x) (g *ᵥ y) = hform s J x y := by
  have h1 : ∀ x y : Fin n → A, hform s J x y = (s ∘ x) ⬝ᵥ (J *ᵥ y) := fun x y => by
    simp only [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc, Function.comp_apply]
  have h2 : s ∘ (g *ᵥ x) = g.map s *ᵥ (s ∘ x) := funext fun i => RingHom.map_mulVec s g x i
  rw [h1, h1, h2]
  conv_rhs => rw [← hg, ← mulVec_mulVec, ← mulVec_mulVec, cT, mulVec_transpose]
  rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm]

theorem inUnipRad_conj (I : AutInst) {A : Type} [CommRing A] (s : A →+* A) (JA : Matrix (Fin I.n) (Fin I.n) A)
    (WA WA' : Submodule A (Fin I.n → A)) (g gi m : Matrix (Fin I.n) (Fin I.n) A) (hgi : gi * g = 1)
    (hU : ∀ x y, hform s JA (g *ᵥ x) (g *ᵥ y) = hform s JA x y) (h1 : ∀ x ∈ WA, g *ᵥ x ∈ WA')
    (h2 : ∀ y ∈ WA', ∃ x ∈ WA, y = g *ᵥ x) (hm : I.InUnipRad s JA WA' m) :
    I.InUnipRad s JA WA (gi * m * g) := by
  obtain ⟨m1, m2, m3⟩ := hm
  have e : gi * m * g - 1 = gi * (m - 1) * g := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hgi]
  have e' : ∀ z, (gi * m * g - 1) *ᵥ z = gi *ᵥ ((m - 1) *ᵥ (g *ᵥ z)) := fun z => by
    rw [e, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have back : ∀ x, gi *ᵥ (g *ᵥ x) = x := fun x => by rw [mulVec_mulVec, hgi, one_mulVec]
  refine ⟨fun x hx => ?_, fun y hy => ?_, fun y x hx => ?_⟩
  · rw [e', m1 _ (h1 x hx), mulVec_zero]
  · have hy' : g *ᵥ y ∈ {y | ∀ x ∈ WA', hform s JA x y = 0} := fun x' hx' => by
      obtain ⟨x, hx, rfl⟩ := h2 x' hx'
      rw [hU]; exact hy x hx
    obtain ⟨x, hx, hxe⟩ := h2 _ (m2 _ hy')
    rw [e', hxe, back]; exact hx
  · rw [e', ← hU, mulVec_mulVec _ g gi, mul_eq_one_comm.1 hgi, one_mulVec]
    exact m3 (g *ᵥ y) _ (h1 x hx)

theorem span_map_mulVec {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ} (c : Matrix (Fin n) (Fin n) E)
    (W : Submodule E (Fin n → E)) :
    (∀ x ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set _)),
      c.map ι *ᵥ x ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W.map c.mulVecLin : Set _))) ∧
    ∀ y ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W.map c.mulVecLin : Set _)),
      ∃ x ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set _)), y = c.map ι *ᵥ x := by
  have key : ∀ w : Fin n → E, (c.map ι *ᵥ fun i => ι (w i)) = fun i => ι ((c *ᵥ w) i) := fun w =>
    funext fun i => (RingHom.map_mulVec ι c w i).symm
  constructor
  · intro x hx
    have : Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set _)) ≤
        (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W.map c.mulVecLin : Set _))).comap
          (c.map ι).mulVecLin := by
      rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, mulVecLin_apply, key]
      exact Submodule.subset_span ⟨c *ᵥ w, ⟨w, hw, rfl⟩, rfl⟩
    exact this hx
  · intro y hy
    have : Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W.map c.mulVecLin : Set _)) ≤
        (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set _))).map (c.map ι).mulVecLin := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨_, Submodule.subset_span ⟨w, hw, rfl⟩, by rw [mulVecLin_apply, key]; rfl⟩
    obtain ⟨x, hx, rfl⟩ := this hy
    exact ⟨x, hx, rfl⟩

theorem naconj : ∀ (I : AutInst), ∀ γ ∈ I.GFset, ∀ W, I.IsIsot W → ∃ W', I.IsIsot W' ∧
    ∀ m ∈ I.NA W', γ⁻¹ * m * γ ∈ I.NA W := by
  intro I γ hγ W hW
  obtain ⟨c, hcU, hinf, hfin⟩ := hγ
  have hcU' : cT (starRingEnd I.E) (c : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * (c : Matrix (Fin I.n) (Fin I.n) I.E) =
      I.J := hcU
  have hcm := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND I.F I.E I.cm).1
  refine ⟨W.map (c : Matrix (Fin I.n) (Fin I.n) I.E).mulVecLin, ⟨?_, ?_⟩, fun m hm => ?_⟩
  · intro h
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW.1
    have : (c : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ w = 0 := by
      rw [← Submodule.mem_bot I.E, ← h]
      exact ⟨w, hw, rfl⟩
    apply hw0
    rw [← one_mulVec w, ← c.inv_mul, ← mulVec_mulVec, this, mulVec_zero]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [mulVecLin_apply, mulVecLin_apply, hform_mulVec_mulVec _ _ _ hcU']
    exact hW.2 x hx y hy
  obtain ⟨hmi, hmf⟩ := hm
  refine ⟨fun v => ?_, ?_⟩
  · have hst : ∀ y : I.E, I.φ v (star y) = star (I.φ v y) := fun y => hcm.2.2.2 (I.φ v) y
    have hPd : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
    have hPP : (I.P v)⁻¹ * I.P v = 1 := Matrix.nonsing_inv_mul _ hPd
    have hPP' : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hPd
    have hg : I.P v * uMat (γ.1 v) * (I.P v)⁻¹ = (c : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) := by
      rw [hinf v, Matrix.mul_assoc, Matrix.mul_assoc, hPP', Matrix.mul_one, ← Matrix.mul_assoc, hPP',
        Matrix.one_mul]
    have hu : ∀ a : Formalism.REAL.UJ (I.ε v), uMat a⁻¹ * uMat a = 1 := fun a => by simp [uMat]
    have hmul : ∀ a b : Formalism.REAL.UJ (I.ε v), uMat (a * b) = uMat a * uMat b := fun a b => by simp [uMat]
    have hgi : (I.P v * uMat ((γ.1 v)⁻¹) * (I.P v)⁻¹) * (I.P v * uMat (γ.1 v) * (I.P v)⁻¹) = 1 := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hPd]
      rw [← Matrix.mul_assoc (uMat _), hu, Matrix.one_mul, hPP']
    have hconj : I.P v * uMat ((γ⁻¹ * m * γ).1 v) * (I.P v)⁻¹ = (I.P v * uMat ((γ.1 v)⁻¹) * (I.P v)⁻¹) *
        (I.P v * uMat (m.1 v) * (I.P v)⁻¹) * (I.P v * uMat (γ.1 v) * (I.P v)⁻¹) := by
      show I.P v * uMat ((γ.1 v)⁻¹ * m.1 v * γ.1 v) * (I.P v)⁻¹ = _
      rw [hmul, hmul]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hPd]
    have hU : cT (starRingEnd ℂ) ((c : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) * I.J.map (I.φ v) *
        (c : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = I.J.map (I.φ v) := by
      have e : cT (starRingEnd ℂ) ((c : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) =
          (cT (starRingEnd I.E) (c : Matrix (Fin I.n) (Fin I.n) I.E)).map (I.φ v) := by
        ext a b
        simp only [cT, Matrix.map_apply, Matrix.transpose_apply, starRingEnd_apply]
        exact (hst _).symm
      rw [e, ← Matrix.map_mul, ← Matrix.map_mul, hcU']
    obtain ⟨s1, s2⟩ := span_map_mulVec (I.φ v) (c : Matrix (Fin I.n) (Fin I.n) I.E) W
    rw [hconj]
    refine inUnipRad_conj I _ _ _ _ _ _ _ hgi ?_ ?_ ?_ (hmi v)
    · rw [hg]; exact hform_mulVec_mulVec _ _ _ hU
    · rw [hg]; exact s1
    · rw [hg]; exact s2
  · have hfm : ∀ a b : I.Gf, I.fmat (a * b) = I.fmat a * I.fmat b := fun a b => by simp [AutInst.fmat]
    have hgi : I.fmat γ.2⁻¹ * I.fmat γ.2 = 1 := by rw [← hfm, inv_mul_cancel]; simp [AutInst.fmat]
    have hconj : I.fmat (γ⁻¹ * m * γ).2 = I.fmat γ.2⁻¹ * I.fmat m.2 * I.fmat γ.2 := by
      show I.fmat (γ.2⁻¹ * m.2 * γ.2) = _
      rw [hfm, hfm]
    have hU : cT (sigR I.cm.sig (Af I.F)) (I.fmat γ.2) * I.J.map (inclE (F := I.F) (Af I.F)) * I.fmat γ.2 =
        I.J.map (inclE (F := I.F) (Af I.F)) := γ.2.2
    obtain ⟨s1, s2⟩ := span_map_mulVec (inclE (F := I.F) (Af I.F)) (c : Matrix (Fin I.n) (Fin I.n) I.E) W
    rw [hconj]
    refine inUnipRad_conj I _ _ _ _ _ _ _ hgi ?_ ?_ ?_ hmf
    · exact hform_mulVec_mulVec _ _ _ hU
    · rw [hfin]; exact s1
    · rw [hfin]; exact s2

end GlobalTheory.CuspGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShortVectorCuspUnipotentCoverAllInstances
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.CuspGeo

section

variable (I : AutInst)

theorem hform_eq_dot {K : Type} [Field K] [StarRing K] {n : ℕ} (J : Matrix (Fin n) (Fin n) K)
    (x y : Fin n → K) : Formalism.UG.hform (starRingEnd K) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_NInf_of_NA {W : Submodule I.E (Fin I.n → I.E)} {m : I.Ginf} (hm : ((m, 1) : I.GA) ∈ I.NA W) :
    m ∈ CompanionTheory.D.gk.RF.NInf I W := by
  intro v
  obtain ⟨h1, h2, h3⟩ := hm.1 v
  show CompanionTheory.D.gk.RF.Lowers (Formalism.REAL.Jm (I.ε v)) (CompanionTheory.D.gk.RF.Wv I W v) (uMat (m v) - 1)
  have hdet := CompanionTheory.D.gk.RF.P_det I v
  have hPi : I.P v * (I.P v)⁻¹ = 1 := mul_nonsing_inv _ hdet
  have hiP : (I.P v)⁻¹ * I.P v = 1 := nonsing_inv_mul _ hdet
  have hB : ∀ z, (I.P v * uMat (m v) * (I.P v)⁻¹ - 1) *ᵥ (I.P v *ᵥ z) =
      I.P v *ᵥ ((uMat (m v) - 1) *ᵥ z) := fun z => by
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc _ (I.P v)⁻¹ (I.P v), hiP,
      Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one]
  have hWC : ∀ w ∈ CompanionTheory.D.gk.RF.Wv I W v, I.P v *ᵥ w ∈
      Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)) := fun w hw => by
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      rw [CompanionTheory.D.gk.RF.P_atV]
      exact Submodule.subset_span ⟨u, hu, rfl⟩
    | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mulVec_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [mulVec_smul]; exact Submodule.smul_mem _ _ ha
  have hWv : ∀ x ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
      (I.P v)⁻¹ *ᵥ x ∈ CompanionTheory.D.gk.RF.Wv I W v := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      exact Submodule.subset_span ⟨u, hu, rfl⟩
    | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mulVec_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [mulVec_smul]; exact Submodule.smul_mem _ _ ha
  have hfP : ∀ w z, CompanionTheory.D.gk.RF.hf (Formalism.REAL.Jm (I.ε v)) w z =
      Formalism.UG.hform (starRingEnd ℂ) (I.J.map (I.φ v)) (I.P v *ᵥ w) (I.P v *ᵥ z) := fun w z => by
    rw [hform_eq_dot, CompanionTheory.D.gk.RF.hf, ← I.P_spec v, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
      mulVec_mulVec, Matrix.mul_assoc]
  have hc1 : ∀ z ∈ CompanionTheory.D.gk.RF.perp (Formalism.REAL.Jm (I.ε v)) (CompanionTheory.D.gk.RF.Wv I W v),
      ∀ x ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
      Formalism.UG.hform (starRingEnd ℂ) (I.J.map (I.φ v)) x (I.P v *ᵥ z) = 0 := fun z hz x hx => by
    have e : x = I.P v *ᵥ ((I.P v)⁻¹ *ᵥ x) := by rw [mulVec_mulVec, hPi, one_mulVec]
    rw [e, ← hfP]
    exact hz _ (hWv x hx)
  have hc2 : ∀ z, (∀ x ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
      Formalism.UG.hform (starRingEnd ℂ) (I.J.map (I.φ v)) x (I.P v *ᵥ z) = 0) →
      z ∈ CompanionTheory.D.gk.RF.perp (Formalism.REAL.Jm (I.ε v)) (CompanionTheory.D.gk.RF.Wv I W v) := fun z h w hw => by
    rw [hfP]
    exact h _ (hWC w hw)
  have inj : ∀ a : Fin I.n → ℂ, a = (I.P v)⁻¹ *ᵥ (I.P v *ᵥ a) := fun a => by
    rw [mulVec_mulVec, hiP, one_mulVec]
  refine ⟨fun w hw => ?_, fun z hz => ?_, fun z => ?_⟩
  · have := h1 _ (hWC w hw)
    rw [hB] at this
    rw [inj ((uMat (m v) - 1) *ᵥ w), this, mulVec_zero]
  · have := h2 _ (hc1 z hz)
    rw [hB] at this
    rw [inj ((uMat (m v) - 1) *ᵥ z)]
    exact hWv _ this
  · refine hc2 _ fun x hx => ?_
    have := h3 (I.P v *ᵥ z)
    rw [hB] at this
    exact this x hx

theorem shortCusp_holds : ShortCusp I := by
  intro U hU
  obtain ⟨M, hM, hMU⟩ := CompanionTheory.D.gk.RF.congruence_subgroup_compact_open I U hU
  obtain ⟨s₁, hs₁, hSI⟩ := CompanionTheory.D.gk.RF.short_isotropic_vector_of CompanionTheory.D.gk.RF.transport_to_standard_form I
  obtain ⟨C₁, hC₁, hCS⟩ := CompanionTheory.D.gk.RF.covolume_span I
  obtain ⟨C₂, hC₂, hCP⟩ := CompanionTheory.D.gk.RF.covolume_orthogonal_complement CompanionTheory.D.gk.RF.transport_to_standard_form I
  obtain ⟨C₃, hC₃, hNC⟩ := CompanionTheory.D.gk.RF.nilpotent_cover_of CompanionTheory.D.gk.RF.transport_to_standard_form CompanionTheory.D.gk.RF.gamSub
    CompanionTheory.D.gk.RF.nilpotent_lie_algebra CompanionTheory.D.gk.RF.nilpotent_subgroup_representation I M hM
  set s₀ := min s₁ 1
  have hs₀ : 0 < s₀ := lt_min hs₁ one_pos
  have hD : 0 < 2 * (C₁ + C₂ + 1) := by positivity
  refine ⟨s₀, 1 / (2 * (C₁ + C₂ + 1)), C₃ * (C₁ + C₂), hs₀, by positivity, fun y η hη hηη₀ hc => ?_⟩
  have hηD : η * (2 * (C₁ + C₂ + 1)) ≤ 1 := (le_div_iff₀ hD).1 hηη₀
  have hη1 : η < 1 := by nlinarith [mul_pos hη hC₁, mul_pos hη hC₂]
  have hηb : (C₁ + C₂) * η ≤ 1 := by nlinarith [mul_pos hη hC₁, mul_pos hη hC₂]
  have hηa : 2 * C₁ * η ≤ 1 := by nlinarith [mul_pos hη hC₁, mul_pos hη hC₂]
  obtain ⟨u, hu, hu0, hus⟩ := hc
  have hc' : ∃ u ∈ CompanionTheory.D.gk.RF.IntV I, u ≠ 0 ∧ ‖CompanionTheory.D.gk.RF.vecAt I y u‖ ≤ s₀ * η ^ (I.n + 1) :=
    ⟨u, hu, hu0, hus⟩
  obtain ⟨t, ht, hts, d, w, hd, hw, hne, hall⟩ := CompanionTheory.D.gk.RF.successive_minima_gap I.E I.n (CompanionTheory.D.gk.RF.IntV I)
    (fun u => ‖CompanionTheory.D.gk.RF.vecAt I y u‖) s₀ η hs₀ hη hη1 hc'
  have ht1 : t ≤ 1 := hts.trans (min_le_right _ _)
  have hs : η * t ≤ s₁ := (mul_le_of_le_one_left ht.le hη1.le).trans (hts.trans (min_le_left _ _))
  have hI : CompanionTheory.D.gk.RF.Isot I.J (Submodule.span I.E (Set.range w)) := Submodule.span_le.2 (by
    rintro _ ⟨j, rfl⟩
    exact CompanionTheory.D.gk.RF.mem_perp_spanC fun i => hSI y _ (hw i).1 _ (hw j).1 ((hw i).2.trans hs) ((hw j).2.trans hs))
  have c1 := hCS y d w (η * t) hd (by positivity) hw
  have c2 := hCP y _ _ t ht (by nlinarith) c1 fun u hu hn => by
    by_contra h
    exact hn (hall u hu (not_le.1 h).le)
  have hρ : η * t * (C₁ * (η * t) + C₂ / t) ≤ (C₁ + C₂) * η := by
    have e : η * t * (C₁ * (η * t) + C₂ / t) = C₁ * η * (η * t * t) + C₂ * η := by field_simp
    have : η * t * t ≤ 1 := mul_le_one₀ (mul_le_one₀ hη1.le ht.le ht1) ht.le ht1
    have := mul_le_of_le_one_right (by positivity : 0 ≤ C₁ * η) this
    rw [e]; linarith
  refine ⟨Submodule.span I.E (Set.range w), ⟨hne, fun x hx z hz => ?_⟩, fun m hm => ?_⟩
  · have := hI hz x hx
    rw [hform_eq_dot]
    exact this
  obtain ⟨γ, h1, -, h3⟩ := hNC y d w (η * t) (C₁ * (η * t) + C₂ / t) hd (by positivity) (by positivity)
    (hρ.trans hηb) hw hI (c1.mono (le_add_of_nonneg_right (by positivity)))
    (c2.mono (le_add_of_nonneg_left (by positivity))) m (mem_NInf_of_NA I hm)
  obtain ⟨x, hxU, hx⟩ := hMU γ h1
  refine ⟨(γ, x), hx, hxU, fun v i j => (h3 v i j).trans ?_⟩
  rw [mul_assoc C₃]
  exact mul_le_mul_of_nonneg_left hρ hC₃.le

end

theorem shortCusp_all : ∀ I : AutInst, ShortCusp I := shortCusp_holds

end GlobalTheory.CuspGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardCharacterConductorAlmostAll
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer NumberField Filter
open IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.Conductor

theorem exists_denominator (E : Type) [Field E] [NumberField E] :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ x : E, (∀ o : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (x * o) = n) → ∃ o : 𝓞 E, (o : E) = N • x := by
  classical
  let b := NumberField.integralBasis E
  obtain ⟨N, hN, h⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image b.traceDual)
  refine ⟨N, hN, fun x hx => ?_⟩
  have hi : IsIntegral ℤ (N • x) := by
    rw [← b.traceDual.sum_repr x, Finset.smul_sum]
    refine IsIntegral.sum _ fun i _ => ?_
    obtain ⟨n, hn⟩ := hx (RingOfIntegers.basis E i)
    have e : b.traceDual.repr x i = (n : ℚ) := by
      rw [← hn, Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply]
      simp [b]
    rw [e, Int.cast_smul_eq_zsmul, smul_comm]
    exact (h _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))).zsmul n
  exact ⟨⟨_, hi⟩, rfl⟩

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem af_ext {a b : Af F} (h : ∀ w, evalV F w a = evalV F w b) : a = b :=
  DFunLike.ext _ _ h

theorem ev_same (v : HeightOneSpectrum (𝓞 F)) : evalV F v (singleV F v 1) = 1 :=
  GlobalTheory.LatVac.evalV_singleV_same F v

theorem ev_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : evalV F w (singleV F v 1) = 0 :=
  GlobalTheory.LatVac.evalV_singleV_ne F v w h

theorem idem_mul (v : HeightOneSpectrum (𝓞 F)) (z : Af F ⊗[F] E)
    (h : ∀ w, w ≠ v → Algebra.TensorProduct.map (evalV F w) (AlgHom.id F E) z = 0) :
    (singleV F v 1 ⊗ₜ[F] (1 : E)) * z = z := by
  classical
  let b := Module.finBasis F E
  have key : ∀ (w) (z : Af F ⊗[F] E) i,
      (Algebra.TensorProduct.basis (Fv F w) b).repr (Algebra.TensorProduct.map (evalV F w) (AlgHom.id F E) z) i =
        evalV F w ((Algebra.TensorProduct.basis (Af F) b).repr z i) := by
    intro w z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  have e : (singleV F v 1 ⊗ₜ[F] (1 : E)) * z = singleV F v 1 • z := by
    rw [Algebra.smul_def]; rfl
  rw [e]
  refine (Algebra.TensorProduct.basis (Af F) b).ext_elem fun i => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  refine af_ext fun w => ?_
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; rw [ev_same, one_mul]
  · rw [ev_ne hw, zero_mul, ← key, h w hw, map_zero, Finsupp.zero_apply]

theorem idem_mul_mem {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (h : evalV F v α ∈ v.adicCompletionIntegers F) :
    singleV F v 1 * α ∈ intAf F := fun w => by
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; rwa [ev_same, one_mul]
  · rw [ev_ne hw, zero_mul]; exact zero_mem _

theorem tmul_denominator {A : Type} [CommRing A] [Algebra F A] (a : A) {N : ℤ} (hN : N ≠ 0) (x : E) :
    (a ⊗ₜ[F] (1 : E)) * (1 ⊗ₜ[F] x) = (a * algebraMap F A (N : F)⁻¹) ⊗ₜ[F] (N • x) := by
  have hN' : (N : F) ≠ 0 := Int.cast_ne_zero.2 hN
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul,
    ← Int.cast_smul_eq_zsmul F, smul_smul, inv_mul_cancel₀ hN', one_smul]

theorem trace_map {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (f : A →ₐ[F] B) (z : A ⊗[F] E) :
    Algebra.trace B (B ⊗[F] E) (Algebra.TensorProduct.map f (AlgHom.id F E) z) = f (Algebra.trace A (A ⊗[F] E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a e =>
    rw [Algebra.TensorProduct.map_tmul, GlobalTheory.LatVac.trace_tmul, GlobalTheory.LatVac.trace_tmul, map_mul, AlgHom.commutes]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end General

variable {D : D7}

theorem trace_parts (s : AE D) : Algebra.trace (AF D.host.F) (AE D) s =
    pairA D.host.F (Algebra.trace (Ainf D.host.F) _ (infPart D s)) (Algebra.trace (Af D.host.F) _ (finPart D s)) :=
  Prod.ext (trace_map (fstA D.host.F) s).symm (trace_map (sndA D.host.F) s).symm

def chi (ψ : AddChar (AF D.host.F) ℂ) (z : Af D.host.F ⊗[D.host.F] D.host.E) : ℂ :=
  ψ (pairA D.host.F 0 (Algebra.trace (Af D.host.F) _ z))

theorem chi_add (ψ : AddChar (AF D.host.F) ℂ) (x y : Af D.host.F ⊗[D.host.F] D.host.E) :
    chi ψ (x + y) = chi ψ x * chi ψ y := by
  rw [chi, map_add, GlobalTheory.LatVac.pair_add, ψ.map_add_eq_mul]; rfl

theorem chi_zero (ψ : AddChar (AF D.host.F) ℂ) : chi ψ 0 = 1 := by
  rw [chi, map_zero]; exact ψ.map_zero_eq_one

theorem psiE_eq_chi (ψ : AddChar (AF D.host.F) ℂ) {s : AE D} (h : infPart D s = 0) : psiE ψ s = chi ψ (finPart D s) := by
  rw [psiE, trace_parts, h, map_zero]; rfl

theorem chi_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (x : D.host.E) :
    chi ψ (1 ⊗ₜ[D.host.F] x) = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ D.host.E x = n := by
  rw [chi, GlobalTheory.LatVac.trace_tmul, one_mul, GlobalTheory.LatVac.char_rat hψ]

theorem chi_int {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {z : Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ intAE D) : chi ψ z = 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    rw [chi, GlobalTheory.LatVac.trace_tmul]
    refine GlobalTheory.IntDense.addChar_eq_one_of_integral D.host.F ψ hψ.1.1 _ (fun a => ?_) _ hα
    rw [← smul_eq_mul, ← map_smul, GlobalTheory.LatVac.char_rat hψ]
    have hi : IsIntegral ℤ ((a : D.host.F) • (o : D.host.E)) := by
      rw [Algebra.smul_def]
      exact (a.isIntegral_coe.map (IsScalarTower.toAlgHom ℤ D.host.F D.host.E)).mul o.isIntegral_coe
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_trace (L := ℚ) hi)
    exact ⟨n, hn.symm⟩
  | zero => exact chi_zero ψ
  | add x y _ _ hx hy => rw [chi_add, hx, hy, one_mul]
  | neg x _ hx =>
    have := chi_add ψ x (-x)
    rwa [add_neg_cancel, chi_zero, hx, one_mul, eq_comm] at this

theorem tmul_mem {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (o : 𝓞 D.host.E) :
    α ⊗ₜ[D.host.F] (o : D.host.E) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨α, hα, o, rfl⟩

theorem mul_mem_int {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    induction hy using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨β, hβ, o', rfl⟩ := hw
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem (GlobalTheory.LatVac.mul_mem_intAf hα hβ) (o * o')
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem approx (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ x : D.host.E, ∃ u ∈ intAE D, z = 1 ⊗ₜ[D.host.F] x + u := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, u, hu, rfl⟩ := hx
    obtain ⟨b, u', hu', rfl⟩ := hy
    exact ⟨a + b, u + u', add_mem hu hu', by rw [TensorProduct.tmul_add, add_add_add_comm]⟩
  | tmul a x =>
    obtain ⟨N, hN, h⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset D.host.E)
    have hi : IsIntegral ℤ (N.natAbs • x) := by
      have := h x (Finset.mem_singleton_self x)
      rcases Int.natAbs_eq N with e | e
      · rwa [e, natCast_zsmul] at this
      · rw [e, neg_smul, natCast_zsmul] at this
        simpa using this.neg
    obtain ⟨a0, β, hβ, hab⟩ :=
      (GlobalTheory.AdLat.strong_approximation_mod_nat D.host.F N.natAbs (Int.natAbs_pos.2 hN)).1 a
    refine ⟨a0 • x, _, tmul_mem (α := β) hβ ⟨_, hi⟩, ?_⟩
    rw [hab]
    exact GlobalTheory.LatVac.approx_tmul a0 _ β x

theorem lift_mem (v : Pl D) (o : 𝓞 D.host.E) :
    pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (o : D.host.E) ∈ intAt D (· = v) := by
  refine ⟨⟨GlobalTheory.LatVac.infPart_pair _ _, ?_⟩, ?_⟩
  · refine (Submodule.mem_iInf _).2 fun w => ?_
    have : compAt D w.1 (pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (o : D.host.E)) =
        evalV D.host.F w.1 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (o : D.host.E) := rfl
    rw [RingHom.mem_ker, this, ev_ne w.2, TensorProduct.zero_tmul]
  · rw [GlobalTheory.LatVac.finPart_pair]
    have := idem_mul_mem (v := v) (α := 1) (by rw [map_one]; exact one_mem _)
    rw [mul_one] at this
    exact tmul_mem this o

theorem eventually_conductor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ᶠ v : Pl D in cofinite, ∀ s ∈ idAt D (· = v),
      (∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1) ↔ s ∈ intAt D (· = v) := by
  intro D ψ hψ
  obtain ⟨N, hN, hden⟩ := exists_denominator D.host.E
  have hev : ∀ᶠ v : Pl D in cofinite,
      evalV D.host.F v (algebraMap D.host.F (Af D.host.F) (N : D.host.F)⁻¹) ∈ v.adicCompletionIntegers D.host.F :=
    (algebraMap D.host.F (Af D.host.F) (N : D.host.F)⁻¹).2
  filter_upwards [hev] with v hv s hs
  have hinf : ∀ o, infPart D (s * o) = 0 := fun o => by
    have : infPart D s = 0 := hs.1
    rw [RingHom.map_mul, this, zero_mul]
  refine ⟨fun h => ⟨hs, ?_⟩, fun h o ho => ?_⟩
  · have hz : (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D s = finPart D s :=
      idem_mul v _ fun w hw => (Submodule.mem_iInf _).1 hs.2 ⟨w, hw⟩
    obtain ⟨x, u, hu, e⟩ := approx (finPart D s)
    have hε : singleV D.host.F v 1 ∈ intAf D.host.F := by
      have := idem_mul_mem (v := v) (α := 1) (by rw [map_one]; exact one_mem _)
      rwa [mul_one] at this
    obtain ⟨y, hy⟩ := hden x fun o => by
      have h1 := h _ (lift_mem v o)
      have e1 : singleV D.host.F v 1 ⊗ₜ[D.host.F] (o : D.host.E) =
          (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * (1 ⊗ₜ[D.host.F] (o : D.host.E)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [psiE_eq_chi ψ (hinf _), RingHom.map_mul, GlobalTheory.LatVac.finPart_pair, e1, ← mul_assoc, mul_comm (finPart D s), hz, e,
        add_mul, chi_add, chi_int hψ (mul_mem_int hu (tmul_mem (GlobalTheory.LatVac.one_mem_intAf _) o)), mul_one,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one] at h1
      exact (chi_rat hψ _).1 h1
    rw [← hz, e, mul_add]
    refine add_mem ?_ (mul_mem_int (tmul_mem hε 1) hu)
    rw [tmul_denominator _ hN, ← hy]
    exact tmul_mem (idem_mul_mem hv) y
  · rw [psiE_eq_chi ψ (hinf _), RingHom.map_mul]
    exact chi_int hψ (mul_mem_int h.2 ho.2)

end GlobalTheory.FinPl.Conductor
end
end

