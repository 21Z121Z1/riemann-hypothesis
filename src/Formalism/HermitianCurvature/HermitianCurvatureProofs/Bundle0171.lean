import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0169
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0054
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurePreservingProdPermThree
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0166

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrablePairOfSquareIntegrable
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section L2

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hs_self_re (A : Wq →L[ℂ] Wp) : (B.hsInner A A).re = ‖B.hsVec A‖ ^ 2 := by
  unfold B.hsInner
  simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (B.hsVec A)

theorem norm_hs_le (A C : Wq →L[ℂ] Wp) : ‖B.hsInner A C‖ ≤ ‖B.hsInner A A‖ + ‖B.hsInner C C‖ := by
  unfold B.hsInner
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (B.hsVec C) (B.hsVec A)
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp only [norm_pow, RCLike.norm_ofReal, Complex.norm_real, abs_norm, norm_norm]
  nlinarith [norm_nonneg (B.hsVec A), norm_nonneg (B.hsVec C), sq_nonneg (‖B.hsVec A‖ - ‖B.hsVec C‖)]

end L2

section Cls

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem slice_pair_measurable (c : Fin r → ℂ) (Φ Ψ : RadSp k r z z' π π') :
    Measurable (fun x : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) := by
  obtain ⟨s, hs⟩ : ∃ s : Set (Mt k r), s = (fun x : Mt k r => (c, Matrix.of x)) ⁻¹' DomR k r z z' := ⟨_, rfl⟩
  have hsm : MeasurableSet s := by
    rw [hs, DomR_eq, Set.preimage_inter]
    exact ((P.Qx5.isOpen_OpR k r z z').preimage (cslice_continuous c)).measurableSet.inter
      (((P.Qx5.Glev_closed (Fin.last r)).preimage continuous_snd).preimage (cslice_continuous c)).measurableSet
  have hA : ∀ Ξ : RadSp k r z z' π π', ContinuousOn (fun x : Mt k r => (Ξ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) s :=
    fun Ξ => (radSp_continuousOn Ξ).comp ((cslice_continuous c).continuousOn : ContinuousOn _ s)
      (fun x hx => by rw [hs] at hx; exact hx)
  refine measurable_of_continuousOn_zero hsm
    ((P.B6.hsInner_continuous (Wp := Wp) (Wq := Wq)).comp_continuousOn ((hA Φ).prodMk (hA Ψ))) ?_
  intro x hx
  have h0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) = 0 :=
    radSp_zero_off Φ (x := (c, Matrix.of x)) (by rw [hs] at hx; exact hx)
  show B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) _ = 0
  rw [h0, hsInner_zero_left]

def SliceSquareIntegrable (μ : Measure (Mt k r)) (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) : Prop :=
  Integrable (fun x : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
    ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) μ

theorem integrable_pair_of_square_integrable (μ : Measure (Mt k r)) {Φ Ψ : RadSp k r z z' π π'} {c : Fin r → ℂ} (hΦ : SliceSquareIntegrable μ Φ c)
    (hΨ : SliceSquareIntegrable μ Ψ c) :
    Integrable (fun x : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) μ := Integrable.mono' (hΦ.norm.add hΨ.norm) (slice_pair_measurable c Φ Ψ).aestronglyMeasurable
  (ae_of_all _ fun x => norm_hs_le _ _)

theorem slice_square_integrable_zero (μ : Measure (Mt k r)) (c : Fin r → ℂ) : SliceSquareIntegrable μ (0 : RadSp k r z z' π π') c := by
  have h0 : ∀ A : Wq →L[ℂ] Wp, B.hsInner 0 A = 0 := by
    intro A
    have h : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
      unfold B.hsVec; ext i; simp
    unfold B.hsInner
    rw [h, inner_zero_right]
  unfold SliceSquareIntegrable
  simpa [h0] using (integrable_zero (Mt k r) ℂ μ)

theorem slice_square_integrable_add (μ : Measure (Mt k r)) {Φ Ψ : RadSp k r z z' π π'} {c : Fin r → ℂ} (hΦ : SliceSquareIntegrable μ Φ c)
    (hΨ : SliceSquareIntegrable μ Ψ c) : SliceSquareIntegrable μ (Φ + Ψ) c := by
  have hΦΨ := integrable_pair_of_square_integrable μ hΦ hΨ
  have hΨΦ := integrable_pair_of_square_integrable μ hΨ hΦ
  unfold SliceSquareIntegrable at *
  simp only [Submodule.coe_add, Pi.add_apply, hs_add_left, hs_add_right]
  exact (hΦ.add hΨΦ).add (hΦΨ.add hΨ)

theorem slice_square_integrable_smul (μ : Measure (Mt k r)) (a : ℂ) {Φ : RadSp k r z z' π π'} {c : Fin r → ℂ} (hΦ : SliceSquareIntegrable μ Φ c) :
    SliceSquareIntegrable μ (a • Φ) c := by
  unfold SliceSquareIntegrable at *
  have e : ∀ x : Mt k r, B.hsInner (((a • Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
      (((a • Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) =
      a * (conj a * B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
        ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) := by
    intro x
    rw [Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, hs_smul_left, hs_smul_right]
  exact ((hΦ.const_mul (conj a)).const_mul a).congr (ae_of_all _ fun x => (e x).symm)

abbrev Lt := (Fin 2 × Fin 2 × ℂ) ⊕ Fin 6

def lop (X : ActualOps k r z z' π π') : Lt → Module.End ℂ (RadSp k r z z' π π') :=
  Sum.elim (fun p => X.t p.2.2 p.1 p.2.1) (fun j => X.fn j)

def wop (X : ActualOps k r z z' π π') (w : List Lt) : Module.End ℂ (RadSp k r z z' π π') :=
  (w.map (lop X)).prod

theorem wop_append_single (X : ActualOps k r z z' π π') (w : List Lt) (l : Lt) :
    wop X (w ++ [l]) = wop X w * lop X l := by
  simp [wop, List.prod_append]

def TopCls (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) : Submodule ℂ (RadSp k r z z' π π') where
  carrier := {Φ | ∀ c ∈ OmX r, (∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ Glev k r (Fin.last r), GGl k r z z' g < ε →
      (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0) ∧ ∀ w : List Lt, SliceSquareIntegrable μ (wop X w Φ) c}
  zero_mem' := fun c _ => ⟨⟨1, one_pos, fun _ _ _ => rfl⟩, fun w => by rw [map_zero]; exact slice_square_integrable_zero μ c⟩
  add_mem' := by
    intro Φ Ψ hΦ hΨ c hc
    obtain ⟨⟨ε1, h1, h10⟩, hΦw⟩ := hΦ c hc
    obtain ⟨⟨ε2, h2, h20⟩, hΨw⟩ := hΨ c hc
    refine ⟨⟨min ε1 ε2, lt_min h1 h2, fun g hg hG => ?_⟩, fun w => ?_⟩
    · show (Φ : Fn k r (Wq →L[ℂ] Wp)) c g + (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = 0
      rw [h10 g hg (lt_of_lt_of_le hG (min_le_left _ _)), h20 g hg (lt_of_lt_of_le hG (min_le_right _ _)), add_zero]
    · rw [map_add]; exact slice_square_integrable_add μ (hΦw w) (hΨw w)
  smul_mem' := by
    intro a Φ hΦ c hc
    obtain ⟨⟨ε, h1, h10⟩, hΦw⟩ := hΦ c hc
    refine ⟨⟨ε, h1, fun g hg hG => ?_⟩, fun w => ?_⟩
    · show a • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0
      rw [h10 g hg hG, smul_zero]
    · rw [map_smul]; exact slice_square_integrable_smul μ a (hΦw w)

theorem lop_vanish (X : ActualOps k r z z' π π') (l : Lt) (Φ : RadSp k r z z' π π') (c : Fin r → ℂ)
    (hc : c ∈ OmX r) (ε : ℝ)
    (h0 : ∀ g ∈ Glev k r (Fin.last r), GGl k r z z' g < ε → (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0) :
    ∀ g ∈ Glev k r (Fin.last r), GGl k r z z' g < ε → (lop X l Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0 := by
  intro g hg hG
  by_cases hd : (c, g) ∈ DomR k r z z'
  · rcases l with ⟨a, b, Y⟩ | j
    · show (X.t Y a b Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0
      have e := X.t_apply Y a b Φ (c, g) hd
      simp only at e
      rw [e]
      set D : Set (Mx k r) := {g | 0 < GGl k r z z' g ∧ GGl k r z z' g < ε} with hDdef
      have hDo : IsOpen D := (isOpen_lt continuous_const (P.Qx5.GGl_continuous k r z z')).inter
        (isOpen_lt (P.Qx5.GGl_continuous k r z z') continuous_const)
      have hDG : D ⊆ {g | 0 < GGl k r z z' g} := fun g hg => hg.1
      have hgD : g ∈ Glev k r (Fin.last r) ∩ D := ⟨hg, hd.2.2, hG⟩
      have hS1 := smoothLev_slice Φ c hc D hDG
      have hS0 : SmoothLev k r (Fin.last r) D (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) := by
        intro g₀ _
        exact ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
      have hL := Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' (Fin.last r) D Y a b
        (fun g => (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) (fun _ => 0) 1 hDo hS1 hS0 g hgD
      have hL0 := Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' (Fin.last r) D Y a b
        (fun _ => (0 : Wq →L[ℂ] Wp)) (fun _ => 0) 1 hDo hS0 hS0 g hgD
      have h00 : tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g = 0 := by
        have h := hL0.1
        simp only [smul_zero, add_zero, one_smul] at h
        have h2 : tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g +
            tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g =
            tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g + 0 := by
          rw [add_zero]; exact h.symm
        exact add_left_cancel h2
      have hloc := hL.2 (fun x hx => h0 x hx.1 hx.2.2)
      rw [show (Φ : Fn k r (Wq →L[ℂ] Wp)) c = fun g => (Φ : Fn k r (Wq →L[ℂ] Wp)) c g from rfl, hloc, h00]
    · show (X.fn j Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0
      have e := X.fn_apply j Φ (c, g) hd
      simp only at e
      rw [e, h0 g hg hG, smul_zero]
  · exact radSp_zero_off (lop X l Φ) (x := (c, g)) hd

theorem lop_mem (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) (l : Lt) :
    ∀ Φ ∈ TopCls X μ, lop X l Φ ∈ TopCls X μ := by
  intro Φ hΦ c hc
  obtain ⟨⟨ε, hε, h0⟩, hw⟩ := hΦ c hc
  refine ⟨⟨ε, hε, lop_vanish X l Φ c hc ε h0⟩, fun w => ?_⟩
  have := hw (w ++ [l])
  rw [wop_append_single] at this
  exact this

theorem square_integrable_slice_of_mem (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) {Φ : RadSp k r z z' π π'}
    (hΦ : Φ ∈ TopCls X μ) {c : Fin r → ℂ} (hc : c ∈ OmX r) : SliceSquareIntegrable μ Φ c := by
  have := (hΦ c hc).2 []
  simpa [wop] using this

theorem intOn_topCls (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) : IntOn μ (TopCls X μ) := fun c hc Φ hΦ Ψ hΨ => integrable_pair_of_square_integrable μ (square_integrable_slice_of_mem X μ hΦ hc) (square_integrable_slice_of_mem X μ hΨ hc)

end Cls

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

def UpperLeftBlockAdjoint (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r)) : Prop :=
  ∀ Y : ℂ, star Y = Y → ∀ c ∈ OmX P.r, ∀ Φ ∈ TopCls X μ, ∀ Ψ ∈ TopCls X μ,
    pairAt μ (X.t Y 0 0 Φ) Ψ c = pairAt μ Φ (X.t (star Y) 0 0 Ψ) c

theorem QQ_mem_adjAlg_top (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (hP : IsPlace P z z' π π') (X : ActualOps P.k P.r z z' π π')
    (μ : Measure (Mt P.k P.r)) (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ)
    (h11 : UpperLeftBlockAdjoint P z z' π π' X μ) (Y : ℂ) (hY : star Y = Y) (a b : Fin 2) :
    X.QQ Y a b ∈ adjAlg μ (TopCls X μ) (intOn_topCls X μ) := by
  refine ⟨lop_mem X μ (Sum.inl (a, b, Y)), lop_mem X μ (Sum.inl (b, a, star Y)), fun c hc Φ hΦ Ψ hΨ => ?_⟩
  show pairAt μ (X.t Y a b Φ) Ψ c = pairAt μ Φ (X.t (star Y) b a Ψ) c
  by_cases hab : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := hab
    exact h11 Y hY c hc Φ hΦ Ψ hΨ
  · have hab' : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push_neg at h
      exact hab h
    obtain ⟨⟨ε1, h1, h10⟩, -⟩ := hΦ c hc
    obtain ⟨⟨ε2, h2, h20⟩, -⟩ := hΨ c hc
    have hm := fun (l : Lt) (Θ : RadSp P.k P.r z z' π π') (hΘ : Θ ∈ TopCls X μ) =>
      square_integrable_slice_of_mem X μ (lop_mem X μ l Θ hΘ) hc
    exact pairAt_t_adj_cut P z z' π π' hP X μ hμ Φ Ψ c hc (min ε1 ε2) (lt_min h1 h2)
      (fun g hg hG => h10 g hg (lt_of_lt_of_le hG (min_le_left _ _)))
      (fun g hg hG => h20 g hg (lt_of_lt_of_le hG (min_le_right _ _))) Y a b hab'
      (integrable_pair_of_square_integrable μ (hm (Sum.inl (a, b, Y)) Φ hΦ) (square_integrable_slice_of_mem X μ hΨ hc))
      (integrable_pair_of_square_integrable μ (square_integrable_slice_of_mem X μ hΦ hc) (hm (Sum.inl (b, a, star Y)) Ψ hΨ))
      (integrable_pair_of_square_integrable μ (hm (Sum.inl (1, 1, Y)) Φ hΦ) (square_integrable_slice_of_mem X μ hΨ hc))
      (integrable_pair_of_square_integrable μ (square_integrable_slice_of_mem X μ hΦ hc) (hm (Sum.inl (1, 1, star Y)) Ψ hΨ))

theorem adjTop_topCls (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0) (h11 : UpperLeftBlockAdjoint P z z' π π' X μ)
    (hK : K (Fin.last P.r) ≤ TopCls X μ) :
    AdjTop (S := S) P z z' π π' μ L st K l0 := by
  exact adjTop_of_tAdj (S := S) P z z' π π' X μ L st K l0 hD (TopCls X μ) (intOn_topCls X μ) hK
    (fun j Φ hΦ => lop_mem X μ (Sum.inr j) Φ hΦ)
    (fun Y hY a b => QQ_mem_adjAlg_top P z z' π π' hD.1 X μ hD.2.1 h11 Y hY a b)

end Top

end Formalism.FourierDecayAlt.P5.HerB
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiCStarMul
section
open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section pw

variable {k r : ℕ}

theorem hMat_monoP (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) : U.hMat σ d = C2.monoP σ.symm d := by
  ext i a
  simp only [U.hMat, U.wP, C2.monoP, Matrix.mul_diagonal, Matrix.of_apply]
  by_cases h : σ i = a
  · have h' : i = σ.symm a := by rw [← h, Equiv.symm_apply_apply]
    simp [h, h']
  · have h' : ¬ i = σ.symm a := fun hh => h (by rw [hh, Equiv.apply_symm_apply])
    simp [h, h']

theorem headH_eq (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (v : U.LW σ → ℂ) (u : G.UT r → ℂ) :
    U.headH σ d v u = StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)) * C2.monoP σ.symm d * G.upper u := by
  have h := StabilizerDisintegration.UC.permutationMatrix_mul_lowerUnipotent (σ := σ) (fun q => v (StabilizerDisintegration.UC.iota σ q))
  simp only [Equiv.apply_symm_apply] at h
  rw [U.headH, h, Matrix.mul_assoc (StabilizerDisintegration.lowP σ.symm _) (U.wP σ), ← U.hMat, hMat_monoP]

theorem psiC_add (c x y : ℂ) : C2.psiC c (x + y) = C2.psiC c x * C2.psiC c y := by
  unfold C2.psiC
  rw [← Complex.exp_add]
  congr 1
  simp only [mul_add, Complex.add_re, Complex.ofReal_add]

theorem psiC_star_mul (c x : ℂ) : C2.psiC c x * star (C2.psiC c x) = 1 := by
  have key : ∀ t : ℝ, Complex.exp (Complex.I * t) * star (Complex.exp (Complex.I * t)) = 1 := by
    intro t
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    rw [show Complex.I * (t : ℂ) + -Complex.I * (t : ℂ) = 0 by ring, Complex.exp_zero]
  exact key _

end pw

section pwmain

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def Amat (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (x0 : C2.Lstidx σ.symm → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  (C2.monoP σ.symm d)⁻¹ * StabilizerDisintegration.lowS σ.symm x0 * C2.monoP σ.symm d

private theorem mul_mem_utset_of_mem {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.UTset m)
    (hB : B ∈ C2.UTset m) : A * B ∈ C2.UTset m := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    rcases lt_or_ge l i with hl | hl
    · rw [hA.1 i l hl, zero_mul]
    · rw [hB.1 l j (lt_of_lt_of_le hji hl), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA.2 i, hB.2 i, mul_one]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with hl' | hl'
      · rw [hA.1 i l hl', zero_mul]
      · rw [hB.1 l i hl', mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi

theorem integrand_pw (S : B.RealPlaceData k r Wp Wq) (z0 z0' : Fin (2 * 0 + k + 1) → ℂ)
    (hz : S.z = liftVec k r 0 z0) (hz' : S.z' = liftVec k r 0 z0')
    (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ0 : B.Mat k 0) (hγ0 : γ0 ∈ B.GV k 0)
    (hrel : C6.IsRelevant S (U.mMap k r 0 (U.hMat σ d) γ0)) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (h h' : Mt k r) (hh : Matrix.of h ∈ UWset k r S.z) (hh' : Matrix.of h' ∈ UWset k r S.z')
    (p : (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ) :
    theta0 S.z σ.symm (TN k r ((h, (phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) p).1),
        (h', (phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) p).2))) •
      D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F
        (TN k r ((h, (phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) p).1),
          (h', (phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) p).2))) =
    chiL σ.symm p.1 • ((S.π (Matrix.of h)).comp
      ((U.psiStar k 0 σ S.z S.z' p.2 • F (U.gaXi k 0 σ d p.2 (fun a => a.elim0)
        ((midB r 0 (Matrix.of h))⁻¹ * γ0 * midB r 0 (Matrix.of h')))).comp (S.π' (Matrix.of h')⁻¹))) := by
  obtain ⟨x0, ⟨⟨y, y'⟩, ⟨⟨a, b⟩, ⟨v, u⟩⟩⟩⟩ := p
  have hhL : Matrix.of h ∈ UWset k (r + 0) (liftVec k r 0 z0) := hz ▸ hh
  have hhL' : Matrix.of h' ∈ UWset k (r + 0) (liftVec k r 0 z0') := hz' ▸ hh'
  have hY := uw_mid r 0 z0 _ hhL
  have hY' := uw_mid r 0 z0' _ hhL'
  have hYu : IsUnit (midB r 0 (Matrix.of h)).det := Formalism.FourierDecayAlt.P.PBG.isUnit_det_of_UH hY.1
  have hY'u : IsUnit (midB r 0 (Matrix.of h')).det := Formalism.FourierDecayAlt.P.PBG.isUnit_det_of_UH hY'.1
  have hAm : Amat σ d x0 ∈ C2.UTset r := conjS_UT hd x0
  have hAmi : (Amat σ d x0)⁻¹ ∈ C2.UTset r := ut_inv_mem hAm
  have hup : G.upper u ∈ C2.UTset r := StabilizerDisintegration.UC.upper_mem u
  have hprod : (Amat σ d x0)⁻¹ * G.upper u ∈ C2.UTset r := mul_mem_utset_of_mem hAmi hup
  have hV' : G.upper (StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)) = (Amat σ d x0)⁻¹ * G.upper u := ut_of_mem hprod
  have hAmu : IsUnit (Amat σ d x0).det := ut_det hAm
  have hZu : IsUnit (U.hMat σ d).det := by
    rw [U.hMat, Matrix.det_mul, Matrix.det_diagonal]
    exact (Formalism.FourierDecayAlt.P.Dx2.SL.isUnit_wP σ).mul
      (isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => hd a))
  have hγ0u : IsUnit γ0.det := gv_unit hγ0
  have hmat : (G.upper (StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q)))))ᴴ * U.hMat σ d * G.upper (StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)) = U.headH σ d v u := by
    rw [hMat_monoP, orbit_split hd, headH_eq, hV']
    show _ * _ * G.upper (StabilizerDisintegration.utc (Amat σ d x0 * ((Amat σ d x0)⁻¹ * G.upper u))) = _
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hAmu, Matrix.one_mul, StabilizerDisintegration.UC.utc_upper]
  have hsgs : B.sgs ((h, psiR k r (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', psiR k r (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) (U.mMap k r 0 (U.hMat σ d) γ0) =
      U.gaXi k 0 σ d ((y, y'), ((a, b), (v, u))) (fun a => a.elim0) ((midB r 0 (Matrix.of h))⁻¹ * γ0 * midB r 0 (Matrix.of h')) := by
    rw [sgs_formula z0 z0' h h' hhL hhL', rnAct_inv_rnAct hYu, rnAct_inv_rnAct hY'u, hmat, gaXi_zero]
  have hθ : theta0 S.z σ.symm ((h, psiR k r (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', psiR k r (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) = chiL σ.symm x0 := by
    simp only [theta0, psiR, Equiv.apply_symm_apply, blkU_uMap_muP_Rn, x0c, StabilizerDisintegration.UC.utc_upper]
    show chiL σ.symm ((StabilizerDisintegration.UC.eSp σ.symm).symm (StabilizerDisintegration.UC.eSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))).1 = chiL σ.symm x0
    rw [MeasurableEquiv.symm_apply_apply]
  have hUU : ∀ w : G.UT r → ℂ, Formalism.DoubleCosetMeasures.IsUpUni (G.upper w) := fun w =>
    ⟨fun i j hij => (StabilizerDisintegration.UC.upper_mem w).1 i j hij, (StabilizerDisintegration.UC.upper_mem w).2⟩
  have hr1 : psi k r S.z cStd (U.Rn k r 0 (rnAct (midB r 0 (Matrix.of h)) y)) = psi k r S.z cStd (U.Rn k r 0 y) := by
    have e := psi_rnAct z0 cStd _ hY (rnAct (midB r 0 (Matrix.of h)) y)
    rw [rnAct_inv_rnAct hYu] at e
    rw [hz]
    exact e.symm
  have hr2 : psi k r S.z' cStd (U.Rn k r 0 (rnAct (midB r 0 (Matrix.of h')) y')) = psi k r S.z' cStd (U.Rn k r 0 y') := by
    have e := psi_rnAct z0' cStd _ hY' (rnAct (midB r 0 (Matrix.of h')) y')
    rw [rnAct_inv_rnAct hY'u] at e
    rw [hz']
    exact e.symm
  have hs1 : C2.simpleUp (G.upper (StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))) = C2.simpleUp (StabilizerDisintegration.lowS σ.symm x0)ᴴ +
      C2.simpleUp (StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)))ᴴ := by
    rw [StabilizerDisintegration.UC.upper_fSp]
    exact simpleUp_mul (StabilizerDisintegration.UC.LT_ct (StabilizerDisintegration.UC.lowS_mem σ.symm x0).1)
      (StabilizerDisintegration.UC.LT_ct (StabilizerDisintegration.UC.lowerUnipotent_mem σ.symm _).1)
  have hs2 : C2.simpleUp (G.upper (StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u))) = C2.simpleUp (Amat σ d x0)⁻¹ + C2.simpleUp (G.upper u) := by
    rw [hV']
    exact simpleUp_mul hAmi hup
  have hMu : IsUnit (C2.monoP σ.symm d).det := hMat_monoP σ d ▸ hZu
  have hinv : (U.hMat σ d)⁻¹ * ((StabilizerDisintegration.lowS σ.symm x0)ᴴᴴ)⁻¹ * U.hMat σ d = (Amat σ d x0)⁻¹ := by
    rw [Matrix.conjTranspose_conjTranspose, hMat_monoP]
    show _ = ((C2.monoP σ.symm d)⁻¹ * StabilizerDisintegration.lowS σ.symm x0 * C2.monoP σ.symm d)⁻¹
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hMu]
    simp only [Matrix.mul_assoc]
  have hrelU : C2.psiC cStd (C2.simpleUp (StabilizerDisintegration.lowS σ.symm x0)ᴴ) =
      C2.psiC cStd (C2.simpleUp (Amat σ d x0)⁻¹) := by
    have hQ : (StabilizerDisintegration.lowS σ.symm x0)ᴴ ∈ C2.UTset r := StabilizerDisintegration.UC.LT_ct (StabilizerDisintegration.UC.lowS_mem σ.symm x0).1
    have hQ' : (U.hMat σ d)⁻¹ * ((StabilizerDisintegration.lowS σ.symm x0)ᴴᴴ)⁻¹ * U.hMat σ d ∈ C2.UTset r := by
      rw [hinv]
      exact hAmi
    rw [relevance_U S (U.hMat σ d) hZu γ0 hγ0u hrel _ hQ hQ', hinv]
  have hw : U.wP σ * U.lowW σ v * (U.wP σ)⁻¹ = StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)) := by
    have e := StabilizerDisintegration.UC.conj_lowW σ (fun q => v (StabilizerDisintegration.UC.iota σ q))
    simp only [Equiv.apply_symm_apply] at e
    exact e
  have hright : G.psi U.betaU (U.subS (U.wP σ * U.lowW σ v * (U.wP σ)⁻¹) + U.supS (G.upper u)) =
      C2.psiC cStd (C2.simpleUp (StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)))ᴴ) * star (C2.psiC cStd (C2.simpleUp (G.upper u))) := by
    rw [StabilizerDisintegration.UC.psi_conj, map_add, psiC_add, hw, ← StabilizerDisintegration.UC.subS_eq, ← StabilizerDisintegration.UC.psi_conj,
      StabilizerDisintegration.UC.psi_star, StabilizerDisintegration.UC.supS_eq]
  have hstar := psiC_star_mul cStd (C2.simpleUp (Amat σ d x0)⁻¹)
  have hxi : B.xiTau S (1, 1) ((h, psiR k r (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', psiR k r (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) = U.psiStar k 0 σ S.z S.z' ((y, y'), ((a, b), (v, u))) := by
    rw [xiTau_one, psiStar_zero]
    simp only [psiR, Equiv.apply_symm_apply]
    rw [Formalism.FourierDecayAlt.P.PBG.psi_mul_nset S.z S.z_mem cStd (Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_nset _ (hUU _))
        (Formalism.FourierDecayAlt.P.Ux3.rn_nset _),
      Formalism.FourierDecayAlt.P.PBG.psi_mul_nset S.z' S.z'_mem cStd (Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_nset _ (hUU _))
        (Formalism.FourierDecayAlt.P.Ux3.rn_nset _),
      psi_muP S.z S.z_mem, psi_muP S.z' S.z'_mem, hr1, hr2, hs1, hs2, psiC_add, psiC_add, hrelU, hright,
      star_mul', star_mul']
    linear_combination (C2.psiC cStd (C2.simpleUp (StabilizerDisintegration.lowP σ.symm (fun q => v (StabilizerDisintegration.UC.iota σ q)))ᴴ) *
      psi k r S.z cStd (U.Rn k r 0 y) * star (C2.psiC cStd (C2.simpleUp (G.upper u))) *
      star (psi k r S.z' cStd (U.Rn k r 0 y'))) * hstar
  have hphi : phiC σ (midB r 0 (Matrix.of h)) (midB r 0 (Matrix.of h')) (Amat σ d) (x0, ((y, y'), ((a, b), (v, u)))) =
      ((rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q)))), (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u))) := rfl
  rw [hphi]
  dsimp only
  rw [show TN k r ((h, (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) = ((h, psiR k r (rnAct (midB r 0 (Matrix.of h)) y, StabilizerDisintegration.UC.fSp σ.symm (x0, (fun q => v (StabilizerDisintegration.UC.iota σ q))))), (h', psiR k r (rnAct (midB r 0 (Matrix.of h')) y', StabilizerDisintegration.utc ((Amat σ d x0)⁻¹ * G.upper u)))) from rfl,
    D.orbIntegrand, B.rho]
  dsimp only
  rw [hθ, hxi, hsgs, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

end pwmain

end Formalism.FourierDecayAlt.P.PBM
end
end

