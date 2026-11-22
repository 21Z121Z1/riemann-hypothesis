import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0234
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0237
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0236
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0214
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGWave
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0222
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0073
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormZeroEqSlotPairingOfLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0224
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0217

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothOnHOfLoc
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def KrAA : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)), KB.CptCoef Bs F → ∀ (u : ℂ), ∀ x ∈ B.GV k r,
      PBG.Kr Bs (C3.AAop k r r le_rfl u F) x = C3.AAop k r r le_rfl u (PBG.Kr Bs F) x

section point

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem ptSize_app (h : C.LPt) (s : ℕ) (t : ℂ) : D.ptSize (h ++ [(s, t)]) = D.ptSize h + s := by
  simp [D.ptSize]

theorem smoothOnH_of_loc {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E}
    (hf : ∀ x ∈ B.GV k r, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ⊤ f x) : SmoothOnH (Hpk k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hgU, hf', fun g hg hgG => hfe g hg hgG⟩

theorem pt_poly (hKA : KrAA) (Bs : B.RealPlaceData k r Wp Wq) {G : B.Mat k r → (Wq →L[ℂ] Wp)} (hG : KB.CptCoef Bs G)
    (h : C.LPt) (s : ℕ) (t : ℂ) (hs : 2 ≤ s) (hq : D.IsLocPt (h ++ [(s, t)]) (r + 1)) {γ : B.Mat k r}
    (hγ : γ ∈ B.GV k r) (hZγ : Zhat k r Bs.z Bs.z' γ = D.ptMatN (h ++ [(s, t)]) (r + 1))
    (hpos : 0 < Gf k r Bs.z Bs.z' γ) {x : Mt k r × Mt k r}
    (hx : (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z ∧ (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r) :
    ∃ c : Fin (D.ptSize h + 1) → (Wq →L[ℂ] Wp),
      c (Fin.last _) = ((-1) ^ (s - 1) / t) • PBG.Kr Bs G ((Matrix.of x.1)⁻¹ * (Matrix.of x.2)⁻¹ * γ) ∧
      ∀ y : ℝ, PBG.Kr Bs (PBN.aaTop Bs y G) ((Matrix.of x.1)⁻¹ * (Matrix.of x.2)⁻¹ * γ) =
        ∑ n : Fin (D.ptSize h + 1), ((y : ℂ) ^ (n : ℕ)) • c n := by
  set σ : B.Mat k r := (Matrix.of x.1 : B.Mat k r)⁻¹ * (Matrix.of x.2 : B.Mat k r)⁻¹ with hσ
  set Gσ : B.Mat k r → (Wq →L[ℂ] Wp) := fun g => G (σ * g) with hGσdef
  have hGσ : KB.CptCoef Bs Gσ := cpt_left Bs hG hx
  have hp := inSS_pL Bs hx
  have hσS : σ ∈ Sset k r Bs.z :=
    ⟨(Matrix.of x.1 : B.Mat k r)⁻¹, Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hx.1, (Matrix.of x.2 : B.Mat k r)⁻¹,
      Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hx.2, rfl⟩
  have h1S : (1 : B.Mat k r) ∈ Sset k r Bs.z := ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, 1, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_one,
    (Matrix.mul_one 1).symm⟩
  have h1S' : (1 : B.Mat k r) ∈ Sset k r Bs.z' := ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, 1, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_one,
    (Matrix.mul_one 1).symm⟩
  have hdσ : ∀ (g : B.Mat k r) (l : Fin (r + 2)), Dmin k r Bs.z Bs.z' (σ * g) l = Dmin k r Bs.z Bs.z' g l := by
    intro g l
    have := Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp g l
    rwa [sgs_pL] at this

  have hsz : D.ptSize h + s = r + 1 := by rw [← ptSize_app h s t]; exact hq.2
  have ht : t ≠ 0 := (hq.1 (s, t) (by simp)).2
  set i0 := D.ptSize h with hi0
  set hh := D.ptMatN h i0 with hhh
  have hZ : ∀ a b : Fin (r + 1), Zhat k r Bs.z Bs.z' γ a b = C3.Zb i0 s hh t a.val b.val := by
    intro a b
    rw [hZγ]
    exact ptMatN_zb h s t (r + 1) hsz.symm a b
  have hDlast : Dmin k r Bs.z Bs.z' γ (Fin.last (r + 1)) ≠ 0 := by
    intro h0
    have hTT : 0 ≤ Tz k r Bs.z * Tz k r Bs.z' := mul_nonneg Bs.T_pos.le Bs.T'_pos.le
    have : Gf k r Bs.z Bs.z' γ ≤ 0 := by
      unfold Gf
      rw [h0, map_zero]
      nlinarith [Complex.normSq_nonneg (Dmin k r Bs.z Bs.z' γ ⟨r, by omega⟩)]
    linarith
  have hdet : hh.det ≠ 0 := by
    intro h0
    apply hDlast
    rw [dmin_zb Bs.z Bs.z' γ i0 s hh t hZ]
    have := (Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb i0 s hh t).2
    rw [show ((Fin.last (r + 1) : Fin (r + 2)) : ℕ) = i0 + s by simp; omega, this, h0]
    ring
  have hT' : herm (Hpk k r) Bs.z' Bs.z' ≠ 0 := by
    intro h0
    have := Bs.T'_pos
    unfold Tz at this
    rw [h0] at this
    simp at this
  obtain ⟨n0, hn0, yb, hyb, hzy, hnf1, hnf2⟩ :=
    nf_top Bs.z Bs.z' Bs.z'_mem hT' γ hγ i0 s hs hsz hh hdet t ht hZ
  have hn0N : n0 ∈ Formalism.QuantumDeterminants.Nset k r := stabilizer_mem_unipotent hn0
  have hn0S : n0 ∈ Sset k r Bs.z' := ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, n0, hn0N, (Matrix.one_mul n0).symm⟩
  have hx₁G : γ * n0 ∈ B.GV k r := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hγ hn0N.1
  have hZ₁ : ∀ a b : Fin (r + 1), Zhat k r Bs.z Bs.z' (γ * n0) a b = C3.Zb i0 s hh t a.val b.val := by
    intro a b; rw [corner_matrix_right_translate Bs.z Bs.z' γ n0 hn0]; exact hZ a b
  have hD₁ : ∀ l : Fin (r + 2), Dmin k r Bs.z Bs.z' (γ * n0) l = Dmin k r Bs.z Bs.z' γ l := by
    intro l; unfold Dmin; rw [corner_matrix_right_translate Bs.z Bs.z' γ n0 hn0]

  set K : B.Mat k r → (Wq →L[ℂ] Wp) := PBG.Kr Bs Gσ with hKdef
  have hKloc := loc_kr Bs hGσ
  have hKn0 : ∀ g, K (g * n0) = K g := by
    intro g
    rw [hKdef, PBG.kr_rightEq Bs Gσ g n0 hn0N, character_stabilizer_eq_one Bs.z'_mem cStd hn0, one_smul]
  have hKσ : ∀ g, K g = PBG.Kr Bs G (σ * g) := fun g => kr_left Bs G σ g
  have hR : ∀ g ∈ Q.Glev k r 0 ∩ Set.univ, ∀ p q, C3.InNp k r p q →
      Q.EH k r p q K g = C3.dpsiP k r Bs.z' p q • K g :=
    fun g _ p q hpq => PBG.kr_rule Bs Gσ g p q hpq
  obtain ⟨c, hc, hcy⟩ := top_poly isOpen_univ Bs.z Bs.z' yb i0 s hs hsz hh t hdet ht (γ * n0)
    ⟨(Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 _).2 hx₁G, Set.mem_univ _⟩ Bs.z'_mem hyb hzy hnf1 hnf2 hZ₁ K
    (smoothLev_of_loc hKloc) hR
  refine ⟨c, ?_, fun y => ?_⟩
  · rw [hc, hKn0, hKσ]
  · rw [← hcy y, hD₁]
    set u : ℂ := (y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2 with hu

    have hX1 := (Formalism.FourierDecayAlt.P.operators_commute_translations' (Wq →L[ℂ] Wp) k r Bs.z Bs.z' r le_rfl u 0 K Bs.z_mem Bs.z'_mem
      (smoothOnH_of_loc hKloc) 1 h1S n0 hn0S γ hγ).1
    have e1 : (fun g => K (1 * g * n0)) = K := by
      funext g; rw [Matrix.one_mul, hKn0]
    rw [e1, Matrix.one_mul] at hX1
    rw [← hX1]

    have hleft : ∀ g ∈ B.GV k r, PBN.aaTop Bs y G (σ * g) = PBN.aaTop Bs y Gσ g := by
      intro g hg
      unfold PBN.aaTop
      rw [hdσ]
      have hX0 := (Formalism.FourierDecayAlt.P.operators_commute_translations' (Wq →L[ℂ] Wp) k r Bs.z Bs.z' r le_rfl u 0 G Bs.z_mem Bs.z'_mem
        (smoothOnH_of_ckOn hG.1) σ hσS 1 h1S' g hg).1
      have e2 : (fun x => G (σ * x * 1)) = Gσ := by funext x; rw [Matrix.mul_one]
      rw [e2, Matrix.mul_one] at hX0
      rw [hX0]
    have hKA' := hKA k r Wp Wq Bs Gσ hGσ u γ hγ
    calc PBG.Kr Bs (PBN.aaTop Bs y G) (σ * γ)
        = PBG.Kr Bs (fun g => PBN.aaTop Bs y G (σ * g)) γ := (kr_left Bs _ σ γ).symm
      _ = PBG.Kr Bs (PBN.aaTop Bs y Gσ) γ := kr_congr Bs hleft hγ
      _ = (Dmin k r Bs.z Bs.z' γ (Fin.last _))⁻¹ • PBG.Kr Bs (C3.AAop k r r le_rfl u Gσ) γ :=
          kr_dmin Bs (C3.AAop k r r le_rfl u Gσ) (Fin.last _) γ
      _ = (Dmin k r Bs.z Bs.z' γ (Fin.last _))⁻¹ • C3.AAop k r r le_rfl u K γ := by rw [hKA']

end point

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.VLetZeroNear
section
open Matrix Finset MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section supp

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem qminorOp_zero {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    qminorOp (Q.EH k r) a b u (fun _ : Q.Mx k r => (0 : E)) = fun _ => 0 := by
  have htop : ∀ (v : ℂ) (p q : Fin (2 * r + k + 1)),
      QuantumDeterminants.Top (Q.EH k r) v p q (fun _ : Q.Mx k r => (0 : E)) = fun _ => 0 := by
    intro v p q
    funext x
    simp only [QuantumDeterminants.Top, smul_zero, ite_self, zero_add]
    exact eabH_zero p q x
  have hfold : ∀ L : List ((Q.Mx k r → E) → Q.Mx k r → E), (∀ T ∈ L, T (fun _ => 0) = fun _ => 0) →
      L.foldr (fun T h => T h) (fun _ : Q.Mx k r => (0 : E)) = fun _ => 0 := by
    intro L
    induction L with
    | nil => intro _; rfl
    | cons T L ih =>
      intro hT
      simp only [List.foldr_cons]
      rw [ih (fun T' h' => hT T' (by simp [h']))]
      exact hT T (by simp)
  funext x
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_eq_zero
  intro σ _
  rw [hfold _ (fun T hT => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hT
    exact htop _ _ _)]
  simp

theorem AAop_zero' (m : ℕ) (hm : m ≤ r) (u : ℂ) (g : Q.Mx k r) :
    C3.AAop k r m hm u (fun _ : Q.Mx k r => (0 : E)) g = 0 := by
  unfold C3.AAop
  apply Finset.sum_eq_zero
  intro c _
  split_ifs
  · rw [qminorOp_zero]; simp
  · rfl

theorem AAvop_zero' (m : ℕ) (hm : m ≤ r) (ell : ℂ) (g : Q.Mx k r) :
    C3.AAvop k r m hm ell (fun _ : Q.Mx k r => (0 : E)) g = 0 := by
  unfold C3.AAvop
  apply Finset.sum_eq_zero
  intro c _
  split_ifs
  · rw [qminorOp_zero]; simp
  · rfl

theorem vLet_zero_near (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (l : C.Letter) (e : Fin 2)
    (f : B.Mat k r → E) {V : Set (Q.Mx k r)} (hV : IsOpen V) (hf : ∀ x ∈ V, x ∈ B.GV k r → f x = 0)
    (g : B.Mat k r) (hg : g ∈ V) (hgG : g ∈ B.GV k r) : D.vLet k r z z' j hj l e f g = 0 := by
  have hgl : g ∈ Q.Glev k r 0 ∩ V := ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hgG, hg⟩
  have hloc : ∀ x ∈ Q.Glev k r 0 ∩ V, f x = (fun _ : Q.Mx k r => (0 : E)) x := fun x hx => hf x hx.2 hx.1.1
  unfold D.vLet
  split_ifs
  · rfl
  · rw [AAop_loc hV _ _ _ f _ hloc g hgl, AAop_zero', smul_zero]
  · rw [AAvop_loc hV _ _ _ f _ hloc g hgl, AAvop_zero', smul_zero]

theorem uwG_supp (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (R : ℝ)
    (hR : ∀ g ∈ B.GV k r, F g ≠ 0 → B.gN g ≤ R) (j : ℕ) (hj : j ≤ r) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), ∀ g ∈ B.GV k r,
      D.uwG k r z z' F j hj w e g ≠ 0 → B.gN g ≤ R
  | [], _, g, hg, hne => hR g hg hne
  | l :: w, e, g, hg, hne => by
    by_contra hgt
    push Not at hgt
    apply hne
    show D.vLet k r z z' j hj l (e 0) (D.uwG k r z z' F j hj w fun a => e a.succ) g = 0
    refine vLet_zero_near z z' j hj l (e 0) _ (V := {x | R < B.gN x})
      (isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous) (fun x hx hxG => ?_) g hgt hg
    by_contra h0
    exact absurd (uwG_supp z z' F R hR j hj w _ x hxG h0) (not_le.2 hx)

theorem contOn_of_loc {f : B.Mat k r → E} {S : Set (B.Mat k r)}
    (h : ∀ x ∈ S, x ∈ B.GV k r → CapelliWordSumExpansion.Loc (⊤ : ℕ∞) f x) : ContinuousOn f {x | x ∈ B.GV k r ∧ x ∈ S} := by
  intro x hx
  obtain ⟨U, f', hU, hxU, hf', he⟩ := h x hx.2 hx.1
  have hc : ContinuousWithinAt f' {x | x ∈ B.GV k r ∧ x ∈ S} x :=
    ((hf'.continuousOn).continuousAt (hU.mem_nhds hxU)).continuousWithinAt
  refine hc.congr_of_eventuallyEq ?_ (he x hxU hx.1)
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hxU), self_mem_nhdsWithin] with y hyU hyS
  exact he y hyU hyS.1

end supp

end Formalism.FourierDecayAlt.P.PBG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveDiffForm
section
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

def DecayUnif : Prop :=
  P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ)
    (cut : ℕ → B.Mat P.k P.r → ℂ) (lo hi : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f →
    (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * (((N + 3 : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    (∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) →
    (∀ Y, lo ≤ Y → Y ≤ hi → I.OnCut P.u P.u' p.l0 Y) → 10 * ((N : ℝ) + 3 * (2 * P.r + 1) + 1) ≤ hi - lo →
    ∀ (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter), KB.CutWord P p.l0 w → w.length ≤ N →
    ∀ (h h' : C.LPt) (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j),
    ∃ C : ℝ, ∀ n : ℕ,
      (∀ c : ℂ, c ≠ 0 → ‖(KB.levW P (j + 1) c : ℂ) * p.RR (fun g => cut n g • D.cutF p.T.base χ f ε g) (j + 1) w
        (h ++ [(1, c)]) (h' ++ [(1, c)])‖ ≤ C * ((1 + ‖c‖) ^ 3)⁻¹) ∧
      ∀ s : ℂ, ‖p.form j hj w (KB.waveG (p.T.bs j) s w
        (KB.slv p.T (fun g => cut n g • D.cutF p.T.base χ f ε g) j hj w h hh.2))
        (KB.slv p.T (fun g => cut n g • D.cutF p.T.base χ f ε g) j hj w h' hh'.2)‖ ≤ C * ((1 + ‖s‖) ^ 3)⁻¹

section wave

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def waveL (Bs : B.RealPlaceData k ρ Wp Wq) (s : ℂ) (w : List C.Letter) :
    (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) →ₗ[ℂ] (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) where
  toFun := KB.waveG Bs s w
  map_add' x y := by simpa using Formalism.FourierDecayAlt.P.PBG.waveG_add_smul Bs s w x y 1
  map_smul' c x := by
    simpa [Formalism.FourierDecayAlt.P.PBG.waveG_zero] using Formalism.FourierDecayAlt.P.PBG.waveG_add_smul Bs s w 0 x c

def mDiff (Bs : B.RealPlaceData k ρ Wp Wq) (σ : ℂ) (w : List C.Letter) :
    (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) →ₗ[ℂ] (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) :=
  (waveL Bs σ w - 1) ^ 3

end wave

def WaveDiffForm : Prop :=
  P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ)
    (cut : ℕ → B.Mat P.k P.r → ℂ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f →
    (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * (((N + 3 : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    (∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) →
    ∀ (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter), KB.CutWord P p.l0 w → w.length ≤ N →
    ∀ (h : C.LPt) (hh : D.IsLocPt h j), ∀ ys : List ℝ, ys.length ≤ 3 → KB.CutWord P p.l0 (KB.plusW ys w) →
      ∃ C : ℝ, ∀ (n : ℕ) (σ : ℂ), ‖σ‖ ≤ 2 →
      ‖p.form j hj (KB.plusW ys w) (KB.onOld (mDiff (p.T.bs j) σ w) ys
        (KB.slv p.T (fun g => cut n g • D.cutF p.T.base χ f ε g) j hj (KB.plusW ys w) h hh.2))
        (KB.onOld (mDiff (p.T.bs j) σ w) ys
        (KB.slv p.T (fun g => cut n g • D.cutF p.T.base χ f ε g) j hj (KB.plusW ys w) h hh.2))‖ ≤ C * ‖σ‖ ^ 6

theorem cutWord_sub (P : M.Par) (l0 : ℕ) (w : List C.Letter) (ys zs : List ℝ) (hz : ∀ z ∈ zs, z ∈ ys)
    (hpw : zs.Pairwise (fun y y' => 2 < |y - y'|)) (h1 : KB.CutWord P l0 (KB.plusW ys w))
    (h2 : KB.CutWord P l0 (KB.minusW ys w)) :
    KB.CutWord P l0 (KB.plusW zs w) ∧ KB.CutWord P l0 (KB.minusW zs w) := by
  have hsub := hz
  have hplus : ∀ ys : List ℝ, KB.plusW ys w = ys.map (fun y => ((true, y) : C.Letter)) ++ w := by
    intro ys
    induction ys with
    | nil => rfl
    | cons y ys ih => simp [KB.plusW, ih]
  have hminus : ∀ ys : List ℝ, KB.minusW ys w = ys.map (fun y => ((false, y + 1) : C.Letter)) ++ w := by
    intro ys
    induction ys with
    | nil => rfl
    | cons y ys ih => simp [KB.minusW, ih]
  have hiff : ∀ L : List C.Letter, KB.CutWord P l0 L ↔
      (∀ l ∈ L, I.OnCut P.u P.u' l0 l.2) ∧ L.Pairwise (fun l l' => 2 < |l.2 - l'.2|) := by
    intro L
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun l hl => ?_, ?_⟩
      · obtain ⟨a, rfl⟩ := List.get_of_mem hl
        exact h1 a
      · rw [List.pairwise_iff_get]
        intro i j hij
        exact h2 i j (ne_of_lt hij)
    · rintro ⟨h1, h2⟩
      refine ⟨fun a => h1 _ (List.get_mem L a), fun a b hab => ?_⟩
      rw [List.pairwise_iff_get] at h2
      rcases lt_or_gt_of_ne hab with h | h
      · exact h2 a b h
      · rw [abs_sub_comm]
        exact h2 b a h
  rw [hiff, hplus, List.pairwise_append] at h1
  rw [hiff, hminus, List.pairwise_append] at h2
  obtain ⟨h1on, -, h1w, h1x⟩ := h1
  obtain ⟨h2on, -, h2w, h2x⟩ := h2
  rw [hiff, hiff, hplus, hminus, List.pairwise_append, List.pairwise_append]
  refine ⟨⟨fun l hl => ?_, ?_, h1w, fun a ha b hb => ?_⟩, ⟨fun l hl => ?_, ?_, h2w, fun a ha b hb => ?_⟩⟩
  · rcases List.mem_append.1 hl with hl | hl
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hl
      exact h1on _ (List.mem_append_left _ (List.mem_map.2 ⟨z, hsub z hz, rfl⟩))
    · exact h1on _ (List.mem_append_right _ hl)
  · exact List.pairwise_map.2 hpw
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ha
    exact h1x _ (List.mem_map.2 ⟨z, hsub z hz, rfl⟩) b hb
  · rcases List.mem_append.1 hl with hl | hl
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hl
      exact h2on _ (List.mem_append_left _ (List.mem_map.2 ⟨z, hsub z hz, rfl⟩))
    · exact h2on _ (List.mem_append_right _ hl)
  · refine List.pairwise_map.2 (hpw.imp fun {a b} hab => ?_)
    simpa [add_sub_add_right_eq_sub] using hab
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ha
    exact h2x _ (List.mem_map.2 ⟨z, hsub z hz, rfl⟩) b hb

theorem grid_exists (P : M.Par) (l0 : ℕ) (lo hi : ℝ) (hcut : ∀ Y, lo ≤ Y → Y ≤ hi → I.OnCut P.u P.u' l0 Y)
    (w : List C.Letter) (hw : KB.CutWord P l0 w) (j : ℕ)
    (hroom : 10 * ((w.length : ℝ) + 3 * (2 * j + 1) + 1) ≤ hi - lo) :
    ∃ grid : Fin 3 → Fin (2 * j + 1) → ℝ, (∀ a, Function.Injective (grid a)) ∧
      ∀ n : Fin 3 → Fin (2 * j + 1), KB.CutWord P l0 (KB.plusW (List.ofFn fun a => grid a (n a)) w) ∧
        KB.CutWord P l0 (KB.minusW (List.ofFn fun a => grid a (n a)) w) ∧
        (List.ofFn fun a => grid a (n a)).Pairwise (fun y y' => 2 < |y - y'|) := by
  obtain ⟨ys, hl, -, hp, h1, h2⟩ := Formalism.FourierDecayAlt.P.room_off_grid P l0 lo hi hcut w (3 * (2 * j + 1)) ∅ hw
    (by simpa using hroom)
  have hget : ∀ i i' : Fin ys.length, i ≠ i' → 4 < |ys.get i - ys.get i'| := by
    intro i i' hne
    rw [List.pairwise_iff_get] at hp
    rcases lt_or_gt_of_ne hne with h | h
    · exact hp i i' h
    · have := hp i' i h
      rwa [abs_sub_comm] at this
  let idx : Fin 3 → Fin (2 * j + 1) → Fin ys.length := fun a i => ⟨a.val * (2 * j + 1) + i.val, by
    rw [hl]; have := a.isLt; have := i.isLt; nlinarith⟩
  have hidx : ∀ a b i i', idx a i = idx b i' → a = b ∧ i = i' := by
    intro a b i i' he
    have e : a.val * (2 * j + 1) + i.val = b.val * (2 * j + 1) + i'.val := congrArg Fin.val he
    have hi := i.isLt
    have hi' := i'.isLt
    have hab : a.val = b.val := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have : (a.val + 1) * (2 * j + 1) ≤ b.val * (2 * j + 1) := Nat.mul_le_mul_right _ h
        nlinarith
      · have : (b.val + 1) * (2 * j + 1) ≤ a.val * (2 * j + 1) := Nat.mul_le_mul_right _ h
        nlinarith
    refine ⟨Fin.ext hab, Fin.ext ?_⟩
    rw [hab] at e
    omega
  refine ⟨fun a i => ys.get (idx a i), fun a i i' he => ?_, fun n => ?_⟩
  · by_contra hne
    have := hget (idx a i) (idx a i') (fun h => hne (hidx a a i i' h).2)
    simp only at he
    rw [he, sub_self, abs_zero] at this
    linarith
  · have hpw : (List.ofFn fun a => ys.get (idx a (n a))).Pairwise (fun y y' => 2 < |y - y'|) := by
      rw [List.pairwise_ofFn]
      intro a b hab
      have := hget (idx a (n a)) (idx b (n b)) (fun h => (ne_of_lt hab) (hidx a b _ _ h).1)
      linarith
    have hz : ∀ z ∈ (List.ofFn fun a => ys.get (idx a (n a))), z ∈ ys := by
      intro z hz
      obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hz
      exact List.get_mem _ _
    obtain ⟨c1, c2⟩ := cutWord_sub P l0 w ys _ hz hpw h1 h2
    exact ⟨c1, c2, hpw⟩

theorem onOld_cpt {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {w : List C.Letter} (Bs : B.RealPlaceData k ρ Wp Wq)
    (M : (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) → Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp))
    (hM : ∀ x, (∀ e, KB.CptCoef Bs (x e)) → ∀ e, KB.CptCoef Bs (M x e)) :
    ∀ (ys : List ℝ) (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat k ρ → (Wq →L[ℂ] Wp)),
      (∀ e, KB.CptCoef Bs (x e)) → ∀ e, KB.CptCoef Bs (KB.onOld M ys x e)
  | [], x, h => hM x h
  | _ :: ys, x, h => fun e => onOld_cpt Bs M hM ys
      (fun e' => x (Fin.cons (e (0 : Fin ((KB.plusW ys w).length + 1))) e')) (fun _ => h _) _

theorem wave_bound3 (hP : P5.ThmPActualCpt) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef p.T.base F)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h h' : C.LPt) (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j)
    (grid : Fin 3 → Fin (2 * j + 1) → ℝ) (hinj : ∀ a, Function.Injective (grid a))
    (hgr : ∀ n : Fin 3 → Fin (2 * j + 1), KB.CutWord P p.l0 (KB.plusW (List.ofFn fun a => grid a (n a)) w) ∧
        KB.CutWord P p.l0 (KB.minusW (List.ofFn fun a => grid a (n a)) w) ∧
        (List.ofFn fun a => grid a (n a)).Pairwise (fun y y' => 2 < |y - y'|))
    (Mo : (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) →ₗ[ℂ]
      (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)))
    (hMo : ∀ ε x, (∀ e, JC.NiceCoef (p.T.bs j) ε (x e)) → ∀ e, JC.NiceCoef (p.T.bs j) ε (Mo x e))
    (hMoC : ∀ x, (∀ e, KB.CptCoef (p.T.bs j) (x e)) → ∀ e, KB.CptCoef (p.T.bs j) (Mo x e)) (s : ℂ) :
    ‖s‖ ^ 3 * ‖p.form j hj w (KB.waveG (p.T.bs j) s w (Mo (KB.slv p.T F j hj w h hh.2)))
      (KB.slv p.T F j hj w h' hh'.2)‖ ≤
    ∑ n : Fin 3 → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| *
      Real.sqrt ((p.form j hj (KB.plusW (List.ofFn fun a => grid a (n a)) w)
        (KB.onOld Mo _ (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (n a)) w) h hh.2))
        (KB.onOld Mo _ (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (n a)) w) h hh.2))).re *
        (p.form j hj (KB.minusW (List.ofFn fun a => grid a (n a)) w)
          (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (n a)) w) h' hh'.2)
          (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (n a)) w) h' hh'.2)).re /
        ((List.ofFn fun a => grid a (n a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) y).re).prod) := by
  have hdeg := Formalism.FourierDecayAlt.P.degree_of_plane_wave Wp Wq P p F j hj w h h' hh hh' 3 grid s Mo hMo hF hinj
  rw [← norm_pow, ← norm_mul, hdeg]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  obtain ⟨hc1, hc2, hpw⟩ := hgr n
  set ys := List.ofFn fun a => grid a (n a) with hys
  obtain ⟨hq, hss⟩ := Formalism.FourierDecayAlt.P.size_standard_compact hP Wp Wq P p j hj w ys hc1 hc2 hpw
  set X := KB.slv p.T F j hj (KB.plusW ys w) h hh.2 with hX
  set Y := KB.slv p.T F j hj (KB.minusW ys w) h' hh'.2 with hY
  have hXc : ∀ e, KB.CptCoef (p.T.bs j) (X e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj (KB.plusW ys w) h hh hF e
  have hYc : ∀ e, KB.CptCoef (p.T.bs j) (Y e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj (KB.minusW ys w) h' hh' hF e
  have hOc : ∀ e, KB.CptCoef (p.T.bs j) (KB.onOld Mo ys X e) := onOld_cpt (p.T.bs j) Mo hMoC ys X hXc
  obtain ⟨hWc, hiso⟩ := Formalism.FourierDecayAlt.P.vector_isomorphism_compact_support hP Wp Wq P p j hj (KB.plusW ys w) hc1 s
    (KB.onOld Mo ys X) (KB.onOld Mo ys X) hOc hOc
  have key := hss (KB.waveG (p.T.bs j) s (KB.plusW ys w) (KB.onOld Mo ys X)) Y hWc hYc
  rw [hiso] at key
  have hqpos : 0 < (ys.map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) y).re).prod := by
    refine List.prod_pos fun a ha => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
    exact hq y hy
  have habs := Real.abs_le_sqrt ((le_div_iff₀ hqpos).2 key)
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

end Formalism.FourierDecayAlt.P.PBO
end
end

