import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeNeZeroComplex
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0197
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0184
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0198
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0192
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0147
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FormSmulL
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section formh

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
  (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) {ε : ℝ}

theorem form_zero_l (y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (hy : NV (p.T.bs j) ε y) :
    p.form j hj w 0 y = 0 := by
  have h := form_sl p j hj w 0 0 y 1 nv_zero nv_zero hy
  simp only [one_smul, add_zero, one_mul] at h
  linear_combination -h

theorem form_zero_r (x : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (hx : NV (p.T.bs j) ε x) :
    p.form j hj w x 0 = 0 := by
  have h := form_sr p j hj w x 0 0 1 hx nv_zero nv_zero
  simp only [one_smul, add_zero, map_one, one_mul] at h
  linear_combination -h

theorem form_smul_l (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : NV (p.T.bs j) ε x) (hy : NV (p.T.bs j) ε y) : p.form j hj w (c • x) y = c * p.form j hj w x y := by
  have h := form_sl p j hj w 0 x y c nv_zero hx hy
  rw [zero_add, form_zero_l p j hj w y hy, zero_add] at h
  exact h

theorem form_smul_r (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : NV (p.T.bs j) ε x) (hy : NV (p.T.bs j) ε y) : p.form j hj w x (c • y) = conj c * p.form j hj w x y := by
  have h := form_sr p j hj w x 0 y c hx nv_zero hy
  rw [zero_add, form_zero_r p j hj w x hx, zero_add] at h
  exact h

end formh

section block0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def uB (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (h : C.LPt) :
    Wd.Ix (Fin w.length) → B.Mat S.G.k (S.G.r - j) → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :=
  if hh : D.IsLocPt h j then
    (((√(nnS S h) / bS S h : ℝ) : ℂ)) • KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)
  else 0

theorem dW_split (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (j : ℕ) (w : List C.Letter) (h h' : C.LPt) :
    dW S v j w h h' = (√(nnS S h) / bS S h) * (√(nnS S h') / bS S h') * (1 / (ΓS S j * S.sizeAt v w)) := by
  unfold dW; ring

theorem uB_nv {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (h : C.LPt) :
    ∃ ε', 0 < ε' ∧ NV ((p v).T.bs j) ε' (uB S p F v ε j hj w h) := by
  have hgpos := g_pos_of_built hB
  unfold uB
  split_ifs with hh
  · have hH : D.IsLocPt (stdS S h) j := (PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
    obtain ⟨ε', hε', hn⟩ := slv_nv (p v) (hF v ε hε) j hj w (stdS S h) hH
    exact ⟨ε', hε', nv_smul _ hn⟩
  · exact ⟨1, one_pos, nv_zero⟩

end block0

section block0b

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem nv_pair {k ρ : ℕ} {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] {Sx Sy : Type} {Bs : B.RealPlaceData k ρ Wp' Wq'} {x : Wd.Ix Sx → B.Mat k ρ → (Wq' →L[ℂ] Wp')}
    {y : Wd.Ix Sy → B.Mat k ρ → (Wq' →L[ℂ] Wp')}
    (hx : ∃ ε, 0 < ε ∧ NV Bs ε x) (hy : ∃ ε, 0 < ε ∧ NV Bs ε y) : ∃ ε, 0 < ε ∧ NV Bs ε x ∧ NV Bs ε y := by
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨b, hb, hyb⟩ := hy
  exact ⟨min a b, lt_min ha hb, nv_mono hxa (min_le_left _ _), nv_mono hyb (min_le_right _ _)⟩

theorem gN_uB (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (h h' : C.LPt) :
    KB.gN (setC S p F) v ε j w h h' =
      ((1 / (ΓS S j * S.sizeAt v w) : ℝ) : ℂ) * (p v).form j hj w (uB S p F v ε j hj w h) (uB S p F v ε j hj w h') := by
  have hgpos := g_pos_of_built hB
  obtain ⟨ε1, hε1, hx, hx'⟩ := nv_pair (uB_nv hB F hF v ε hε j hj w h) (uB_nv hB F hF v ε hε j hj w h')
  by_cases hloc : D.IsLocPt h j ∧ D.IsLocPt h' j
  · obtain ⟨hh, hh'⟩ := hloc
    have hH : D.IsLocPt (stdS S h) j := (PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
    have hH' : D.IsLocPt (stdS S h') j := (PBD.isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
    obtain ⟨ε2, hε2, hs, hs'⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj w (stdS S h) hH)
      (slv_nv (p v) (hF v ε hε) j hj w (stdS S h') hH')
    rw [gN_setC_form hB F v ε j hj w h h' hh hh']
    have e1 : uB S p F v ε j hj w h = (((√(nnS S h) / bS S h : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2) := by
      unfold uB; rw [dif_pos hh]
    have e2 : uB S p F v ε j hj w h' = (((√(nnS S h') / bS S h' : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S h') ((stdS_size S h').trans hh'.2) := by
      unfold uB; rw [dif_pos hh']
    rw [e1, e2, form_smul_l (p v) j hj w _ _ _ hs (nv_smul _ hs'), form_smul_r (p v) j hj w _ _ _ hs hs',
      Complex.conj_ofReal, dW_split]
    push_cast
    ring
  · rw [gN_setC_zero hB F v ε j w h h' hloc]
    have : uB S p F v ε j hj w h = 0 ∨ uB S p F v ε j hj w h' = 0 := by
      by_cases hh : D.IsLocPt h j
      · right; unfold uB; rw [dif_neg (fun hh' => hloc ⟨hh, hh'⟩)]
      · left; unfold uB; rw [dif_neg hh]
    rcases this with h0 | h0
    · rw [h0, form_zero_l (p v) j hj w _ hx', mul_zero]
    · rw [h0, form_zero_r (p v) j hj w _ hx, mul_zero]

theorem hatB_uB (hA : P5.ThmPActual) (hPS : KB.PStd) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (l : ℂ) (h h' : C.LPt)
    (hsz : D.ptSize h = j) (hsz' : D.ptSize h' = j) :
    KB.hatB (setC S p F) v ε (j + 1) 1 w l h h' =
      ((1 / (ΓS S j * S.sizeAt v w) : ℝ) : ℂ) * (p v).form j hj w
        (KB.waveG ((p v).T.bs j) (sW S j l) w (uB S p F v ε j hj w h)) (uB S p F v ε j hj w h') := by
  have hgpos := g_pos_of_built hB
  obtain ⟨ε1, hε1, hx, hx'⟩ := nv_pair (uB_nv hB F hF v ε hε j hj w h) (uB_nv hB F hF v ε hε j hj w h')
  have hwx := PBFV.waveG_nice ((p v).T.bs j) ε1 (sW S j l) w _ hx
  by_cases hloc : D.IsLocPt h j ∧ D.IsLocPt h' j
  · obtain ⟨hh, hh'⟩ := hloc
    have hH : D.IsLocPt (stdS S h) j := (PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
    have hH' : D.IsLocPt (stdS S h') j := (PBD.isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
    obtain ⟨ε2, hε2, hs, hs'⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj w (stdS S h) hH)
      (slv_nv (p v) (hF v ε hε) j hj w (stdS S h') hH')
    rw [hatB_setC hA hPS hB F hF v ε hε j hj w hw l h h' hh hh']
    have e1 : uB S p F v ε j hj w h = (((√(nnS S h) / bS S h : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2) := by
      unfold uB; rw [dif_pos hh]
    have e2 : uB S p F v ε j hj w h' = (((√(nnS S h') / bS S h' : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S h') ((stdS_size S h').trans hh'.2) := by
      unfold uB; rw [dif_pos hh']
    have hws := PBFV.waveG_nice ((p v).T.bs j) ε2 (sW S j l) w _ hs
    have ew : KB.waveG ((p v).T.bs j) (sW S j l) w ((((√(nnS S h) / bS S h : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)) =
        (((√(nnS S h) / bS S h : ℝ) : ℂ)) • KB.waveG ((p v).T.bs j) (sW S j l) w
          (KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)) := by
      have := PBG.waveG_add_smul ((p v).T.bs j) (sW S j l) w 0
        (KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)) (((√(nnS S h) / bS S h : ℝ) : ℂ))
      rw [zero_add, PBG.waveG_zero, zero_add] at this
      exact this
    rw [e1, e2, ew, form_smul_l (p v) j hj w _ _ _ hws (nv_smul _ hs'), form_smul_r (p v) j hj w _ _ _ hws hs',
      Complex.conj_ofReal, dW_split]
    push_cast
    ring
  · rw [hatB_setC_zero hB F v ε j w l h h' hsz hsz' hloc]
    have : uB S p F v ε j hj w h = 0 ∨ uB S p F v ε j hj w h' = 0 := by
      by_cases hh : D.IsLocPt h j
      · right; unfold uB; rw [dif_neg (fun hh' => hloc ⟨hh, hh'⟩)]
      · left; unfold uB; rw [dif_neg hh]
    rcases this with h0 | h0
    · rw [h0, PBG.waveG_zero, form_zero_l (p v) j hj w _ hx', mul_zero]
    · rw [h0, form_zero_r (p v) j hj w _ hwx, mul_zero]

theorem block0 (hA : P5.ThmPActual) (hPS : KB.PStd) (hVI : KB.VIso) (hFP : FormPos)
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (l : ℂ) (Y : Finset C.LPt)
    (hY : ∀ h ∈ Y, D.ptSize h = j) :
    KB.BlockPSD Y Y (KB.gN (setC S p F) v ε j w) (KB.hatB (setC S p F) v ε (j + 1) 1 w l)
      (KB.gN (setC S p F) v ε j w) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -, -, -, -⟩ := hv v
  have hw' : KB.CutWord (D.parOf S v) (p v).l0 w := by rw [hl0]; exact hw
  obtain ⟨ε0, hε0, hall⟩ := nv_common Y (uB S p F v ε j hj w) (fun h _ => uB_nv hB F hF v ε hε j hj w h)
  set Dv := NV ((p v).T.bs j) ε0 (S := Fin w.length) with hDv
  refine block_iso Dv ((p v).form j hj w) nv_zero (fun x y hx hy => nv_add hx hy) (fun c x hx => nv_smul c hx)
    (fun x₁ x₂ y c h₁ h₂ hy => form_sl (p v) j hj w x₁ x₂ y c h₁ h₂ hy)
    (fun x y₁ y₂ c hx h₁ h₂ => form_sr (p v) j hj w x y₁ y₂ c hx h₁ h₂)
    (fun x hx => hFP hA _ _ (D.parOf S v) (p v) j hj w hw' x ε0 hε0 hx)
    (KB.waveG ((p v).T.bs j) (sW S j l) w) (fun x hx => PBFV.waveG_nice ((p v).T.bs j) ε0 (sW S j l) w x hx)
    (fun x y hx hy => (hVI hA _ _ (D.parOf S v) (p v) j hj w hw' (sW S j l) x y ε0 hε0 hx hy).2)
    Y (fun h => if h ∈ Y then uB S p F v ε j hj w h else 0)
    (fun h => by by_cases hh : h ∈ Y <;> simp only [hh, if_true, if_false] <;> first | exact hall h hh | exact nv_zero)
    (1 / (ΓS S j * S.sizeAt v w)) ?_ _ _ ?_ ?_
  · have : 0 ≤ ΓS S j * S.sizeAt v w := by
      refine mul_nonneg ?_ (sizeAt_nonneg S v w)
      unfold ΓS
      have hgpos := g_pos_of_built hB
      have hrd := PBD.rd_pos' E
      exact (PBD.gamLev_pos _ _ _ _ (by unfold D.kapG; positivity) (by unfold D.deG; positivity) _).le
    positivity
  · intro h hh h' hh'
    simp only [hh, hh', if_true]
    exact gN_uB hB F hF v ε hε j hj w h h'
  · intro h hh h' hh'
    simp only [hh, hh', if_true]
    exact hatB_uB hA hPS hB F hF v ε hε j hj w hw l h h' (hY h hh) (hY h' hh')

end block0b

end

end Formalism.FourierDecayAlt.P.PBL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfLeaves
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def GEqs (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : B.Mat k r → E) : Prop :=
  Q.CkLev k r 0 (2 * r + k + 1) (Q.OmPlus k r z z') J ∧
  (∀ X ∈ JfS.lieOf (Nset k r), ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Formalism.REAL.RdV X J g = c • J g) ∧
  (∀ X ∈ JfS.lieOf (Nset k r), ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Q.LdV X J g = c • J g) ∧
  (∀ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z] Bs → ∀ w : ℂ, ∃ c : ℂ,
    ∀ g ∈ JF.Om k r z z', Q.capLft k r Bs w J g = c • J g) ∧
  (∀ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z'] Bs → ∀ w : ℂ, ∃ c : ℂ,
    ∀ g ∈ JF.Om k r z z', Q.capR k r Bs w J g = c • J g) ∧
  (∀ Y : ℝ, ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Q.CV k r (Y : ℂ) J g = c • J g)

def NDiff : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (m : ℕ∞) (J : B.Mat k r → (Wq →L[ℂ] Wp)),
    J ∈ Gr.FFlM m k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') →
    (∀ X ∈ JfS.lieOf (Nset k r), ∃ c : ℂ, ∀ g ∈ JF.Om k r D.z D.z', Formalism.REAL.RdV X J g = c • J g) ∧
    (∀ X ∈ JfS.lieOf (Nset k r), ∃ c : ℂ, ∀ g ∈ JF.Om k r D.z D.z', Q.LdV X J g = c • J g)

def UCap : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (u u' : ℕ → ℝ) (J : B.Mat k r → (Wq →L[ℂ] Wp)),
    Q.IsType k r D.z D.π u → Q.IsType k r D.z' D.π' u' →
    J ∈ Gr.FFlM ((2 * r + k + 1 : ℕ) : ℕ∞) k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') →
    (∀ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [D.z] Bs → ∀ w : ℂ, ∃ c : ℂ,
      ∀ g ∈ JF.Om k r D.z D.z', Q.capLft k r Bs w J g = c • J g) ∧
    (∀ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [D.z'] Bs → ∀ w : ℂ, ∃ c : ℂ,
      ∀ g ∈ JF.Om k r D.z D.z', Q.capR k r Bs w J g = c • J g)

def GEqsPost : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : B.Mat k r → E) (ℓ : E →L[ℂ] ℂ), GEqs k r z z' J → GEqs k r z z' (fun g => ℓ (J g))

def SmoothOfCoeffs : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (Dm : Set (B.Mat k r))
    (J : B.Mat k r → E), (∀ ℓ : E →L[ℂ] ℂ, Q.SmoothLev k r 0 Dm (fun g => ℓ (J g))) → Q.SmoothLev k r 0 Dm J

def GChart : Prop :=
  ∀ (k r : ℕ), ∃ d : ℕ, ∀ g₀ ∈ B.GV k r, ∃ (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)),
    IsOpen O ∧ IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ κ O ∧ ContDiffOn ℝ ∞ Φ U ∧
    (∀ x ∈ O, κ x ∈ B.GV k r ∧ κ x ∈ U ∧ Φ (κ x) = x) ∧ (∀ g ∈ U, g ∈ B.GV k r → Φ g ∈ O ∧ κ (Φ g) = g)

def ChartEqs : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ),
    1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    IsOpen O → IsOpen U → ContDiffOn ℝ ∞ κ O → ContDiffOn ℝ ∞ Φ U →
    (∀ x ∈ O, κ x ∈ B.GV k r ∧ κ x ∈ U ∧ Φ (κ x) = x) → (∀ g ∈ U, g ∈ B.GV k r → Φ g ∈ O ∧ κ (Φ g) = g) →
    (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') → GEqs k r z z' u →
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → SOp d),
      (∀ j i w, ContDiffOn ℝ ∞ ((P j).a i w) O) ∧ (∀ j, (P j).ord ≤ 2 * r + k + 1) ∧
      ContDiffOn ℝ ((2 * r + k + 1 : ℕ) : WithTop ℕ∞) (fun x => u (κ x)) O ∧
      (∀ j, ∀ x ∈ O, (P j).app (fun y => u (κ y)) x = 0) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, ξ ≠ 0 → (∀ j, (P j).symb x ξ = 0) →
        ∃ Ξ : B.Mat k r, B.inLie k r Ξ ∧ Ξ ≠ 0 ∧ IsNilpotent Ξ ∧
          (∀ X ∈ JfS.lieOf (UWset k r z) ∪ JfS.lieOf (Nset k r), (Matrix.trace (Ξ * X)).re = 0) ∧
          (∀ X ∈ JfS.lieOf (UWset k r z') ∪ JfS.lieOf (Nset k r),
            (Matrix.trace (Ξ * (κ x * X * (κ x)⁻¹))).re = 0)

def ClassToWeak : Prop :=
  ∀ (d N : ℕ) (P : SOp d) (U : Set (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ),
    IsOpen U → (∀ i w, ContDiffOn ℝ ∞ (P.a i w) U) → P.ord ≤ N → ContDiffOn ℝ (N : WithTop ℕ∞) u U →
    (∀ x ∈ U, P.app u x = 0) →
    ∀ φ : (Fin d → ℝ) → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x, u x * P.tr φ x = 0

def LieSsetSplit : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∀ X ∈ JfS.lieOf (Sset k r z), ∃ A ∈ JfS.lieOf (UWset k r z), ∃ Bn ∈ JfS.lieOf (Nset k r), X = A + Bn

def GRegScalar : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (u : B.Mat k r → ℂ),
    1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → GEqs k r z z' u →
    Q.SmoothLev k r 0 (Q.OmPlus k r z z') u

theorem gRegJ_of (hN : NDiff) (hU : UCap) (hP : GEqsPost) (hC : SmoothOfCoeffs) (hS : GRegScalar) : GRegJ := by
  intro k r Wp Wq _ _ _ _ _ _ D u u' J hT hT' hF hCV
  have hG : GEqs k r D.z D.z' J := by
    obtain ⟨hn1, hn2⟩ := hN k r Wp Wq D _ J hF
    obtain ⟨hu1, hu2⟩ := hU k r Wp Wq D u u' J hT hT' hF
    refine ⟨?_, hn1, hn2, hu1, hu2, hCV⟩
    intro g₀ hg₀
    obtain ⟨U, F, hUo, hgU, hFc, hJF⟩ := hF.1 g₀ hg₀
    exact ⟨U, F, hUo, hgU, by simpa [Gr.smM] using hFc, hJF⟩
  exact hC k r (Wq →L[ℂ] Wp) _ J (fun ℓ =>
    hS k r D.z D.z' _ D.k_pos D.z_mem D.z'_mem D.T_pos D.T'_pos (hP k r D.z D.z' _ J ℓ hG))

theorem gRegScalar_of (hK : GChart) (hE : ChartEqs) (hW : ClassToWeak) (hR : EllRegW) (hSym : JfS.SymbolNil)
    (hL : LieSsetSplit) : GRegScalar := by
  intro k r z z' u hk hz hz' hT hT' hG g₀ hg₀
  obtain ⟨d, hd⟩ := hK k r
  have hg₀G : g₀ ∈ B.GV k r := hg₀.1.1
  obtain ⟨O, U, κ, Φ, hO, hU, hg₀U, hκ, hΦ, hκO, hΦU⟩ := hd g₀ hg₀G
  have hO' : IsOpen (O ∩ κ ⁻¹' Q.OmPlus k r z z') :=
    hκ.continuousOn.isOpen_inter_preimage hO (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open z z')
  have hU' : IsOpen (U ∩ Φ ⁻¹' (O ∩ κ ⁻¹' Q.OmPlus k r z z')) :=
    hΦ.continuousOn.isOpen_inter_preimage hU hO'
  have hΦg₀ : Φ g₀ ∈ O ∩ κ ⁻¹' Q.OmPlus k r z z' := by
    obtain ⟨h1, h2⟩ := hΦU g₀ hg₀U hg₀G
    refine ⟨h1, ?_⟩
    show κ (Φ g₀) ∈ Q.OmPlus k r z z'
    rw [h2]; exact hg₀.2
  have hκO' : ∀ x ∈ O ∩ κ ⁻¹' Q.OmPlus k r z z',
      κ x ∈ B.GV k r ∧ κ x ∈ U ∩ Φ ⁻¹' (O ∩ κ ⁻¹' Q.OmPlus k r z z') ∧ Φ (κ x) = x := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hκO x hx.1
    refine ⟨h1, ⟨h2, ?_⟩, h3⟩
    show Φ (κ x) ∈ O ∩ κ ⁻¹' Q.OmPlus k r z z'
    rw [h3]; exact hx
  have hΦU' : ∀ g ∈ U ∩ Φ ⁻¹' (O ∩ κ ⁻¹' Q.OmPlus k r z z'), g ∈ B.GV k r →
      Φ g ∈ O ∩ κ ⁻¹' Q.OmPlus k r z z' ∧ κ (Φ g) = g :=
    fun g hg hgG => ⟨hg.2, (hΦU g hg.1 hgG).2⟩
  obtain ⟨ι, hι, P, hPc, hPo, huc, hPu, hsym⟩ := hE k r z z' d _ _ κ Φ u hk hz hz' hT hT' hO' hU'
    (hκ.mono Set.inter_subset_left) (hΦ.mono Set.inter_subset_left) hκO' hΦU' (fun x hx => hx.2) hG
  have := hι
  have hsm : ContDiffOn ℝ ∞ (fun x => u (κ x)) (O ∩ κ ⁻¹' Q.OmPlus k r z z') := by
    refine hR d ι P _ _ hO' hPc huc.continuousOn
      (fun j φ hφ hφc hφs => hW d _ (P j) _ _ hO' (hPc j) (hPo j) huc (hPu j) φ hφ hφc hφs) ?_
    intro x hx ξ hξ
    by_contra hall
    simp only [not_exists, not_not] at hall
    obtain ⟨Ξ, hΞ, hΞ0, hnil, hl, hr⟩ := hsym x hx ξ hξ hall
    apply hΞ0
    have hxG := (hκO' x hx).1
    have hxOm : κ x ∈ Q.OmPlus k r z z' := hx.2
    refine hSym k r z z' hk hz hz' hT hT' (κ x) hxG ⟨hxOm.2, fun a => hxOm.1 ⟨(a : ℕ) + 1, by omega⟩ a.isLt⟩
      Ξ hΞ hnil ?_ ?_
    · intro X hX
      obtain ⟨A, hA, Bn, hB, rfl⟩ := hL k r z hz hT X hX
      simp only [mul_add, Matrix.trace_add, Complex.add_re]
      rw [hl A (Or.inl hA), hl Bn (Or.inr hB), add_zero]
    · intro X hX
      obtain ⟨A, hA, Bn, hB, rfl⟩ := hL k r z' hz' hT' X hX
      simp only [mul_add, add_mul, Matrix.trace_add, Complex.add_re]
      rw [hr A (Or.inl hA), hr Bn (Or.inr hB), add_zero]
  refine ⟨U ∩ Φ ⁻¹' (O ∩ κ ⁻¹' Q.OmPlus k r z z'), fun g => u (κ (Φ g)), hU', ⟨hg₀U, hΦg₀⟩, ?_, ?_⟩
  · exact hsm.comp (hΦ.mono Set.inter_subset_left) (fun g hg => hg.2)
  · intro g hg hgG
    show u g = u (κ (Φ g))
    rw [(hΦU g hg.1 hgG.1).2]

theorem jfSmoothBuilt_of_leaves (hN : NDiff) (hU : UCap) (hP : GEqsPost) (hC : SmoothOfCoeffs) (hK : GChart)
    (hE : ChartEqs) (hW : ClassToWeak) (hR : EllRegW) (hSym : JfS.SymbolNil) (hL : LieSsetSplit) :
    JfSmoothBuilt :=
  transfer_smooth_of_regularity (gRegJ_of hN hU hP hC (gRegScalar_of hK hE hW hR hSym hL))

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniOfCore
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniReduction

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem leftFubini_of_core (hC : LeftFubiniLemmas.CoreLF) : LeftFubiniLemmas.LeftFubini := by
  intro k r Wp Wq _ _ _ _ _ _ T hT j hj hj1 a ha
  obtain ⟨hab, rfl⟩ := ha
  have e : D.ptSize a + (r - D.ptSize a) = r := by omega
  have hd : ∀ q, D.ptDiag a q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne a hab q q.2
  obtain ⟨X, hX, μ, ℓ, sx, hsx, hmain⟩ := hC k (D.ptSize a) (r - D.ptSize a) r e hj1 (D.ptPerm a) (D.ptDiag a) hd
    Wp Wq (T.bs (D.ptSize a)) T.base (T.z_lev _ hj) (T.z'_lev _ hj) (T.π'_lev _ hj) (hT _ hj).2.1
    (Formalism.FourierDecayAlt.P.PBM.tower_haarW' T hT _ hj e) (hT _ hj).2.2 (hT 0 (Nat.zero_le r)).2.2
  refine ⟨X, hX, μ, ℓ, sx, hsx, fun g hg H hH hR => ?_⟩
  have hx : ∀ (h1 : D.ptSize a ≤ r) (h2 : r - D.ptSize a = r - D.ptSize a),
      LeftFubiniLemmas.levelZeroPointOver a h1 (D.castM h2 g) = D.castM e (U.mMap k (D.ptSize a) (r - D.ptSize a)
        (U.hMat (D.ptPerm a) (D.ptDiag a)) g) := by
    intro h1 h2
    unfold LeftFubiniLemmas.levelZeroPointOver
    rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  have hs : ∀ h2 : r - D.ptSize a = r - D.ptSize a,
      D.castF h2 (D.sliceAt k r T.base.z T.base.z' H a) =
        U.PhiFun (s := 0) k (r - D.ptSize a) (D.ptPerm a) (D.ptDiag a) (D.castV e.symm T.base.z)
          (D.castV e.symm T.base.z') (D.castF e H) (fun a => a.elim0) := by
    intro h2
    funext y
    unfold D.castF
    rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, D.sliceAt, dif_pos hj]
    rfl
  simp only [hx, hs]
  exact hmain g hg H hH hR

end Formalism.FourierDecayAlt.P.LeftFubiniReduction
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LowVLift
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

theorem om_cast {a b : ℕ} (h : a = b) (v v' : Fin (2 * a + k + 1) → ℂ) (g : B.Mat k a) (hg : g ∈ JF.Om k a v v') :
    D.castM h g ∈ JF.Om k b (D.castV h v) (D.castV h v') := by
  subst h; rwa [Dx2.MN.castM_rfl, Dx2.Tower.castV_rfl, Dx2.Tower.castV_rfl]

theorem lowV_lift (ρ : ℕ) (v : Fin (2 * ρ + k + 1) → ℂ) : U.lowV k 1 ρ (liftVec k 1 ρ v) = v := by
  funext i
  simp only [U.lowV, liftVec]
  rw [dif_pos (by omega)]
  congr 1; ext; simp

theorem mcOm : MCOm := by
  intro k ρ z0 z0' hz0 hz0' c hc γ hγ hγO
  apply om_cast
  set Z : Matrix (Fin 1) (Fin 1) ℂ := Matrix.of fun _ _ => c with hZd
  have hZdet : Z.det = c := by rw [Matrix.det_unique]; rfl
  have hz := Qx4.lift_inWb hz0
  have hz' := Qx4.lift_inWb hz0'
  have hZ : Zhat k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) =
      Matrix.reindex (Ux3.eC 1 ρ) (Ux3.eC 1 ρ) (Matrix.fromBlocks Z 0 0 (Zhat k ρ z0 z0' γ)) := by
    unfold U.mMap
    rw [Ux3.z_hat_of_block3 _ _ hz hz', Formalism.QuantumDeterminants.Zhat_eq, lowV_lift, lowV_lift]
    congr 1
    simp [← Matrix.mul_assoc, Ux3.wMat_mul_self]
  refine ⟨(Formalism.FourierDecayAlt.P.slice_membership k 1 ρ).1 Z γ (by rw [hZdet]; exact hc) hγ, ?_, ?_⟩
  · intro l hl
    obtain ⟨lv, hlv⟩ := l
    rcases Nat.eq_zero_or_pos lv with h0 | hpos
    · subst h0
      unfold Dmin
      rw [Matrix.det_isEmpty]; exact one_ne_zero
    · obtain ⟨l', rfl⟩ : ∃ l', lv = 1 + l' := ⟨lv - 1, by omega⟩
      have hl' : l' ≤ ρ := by simp only at hl; omega
      unfold Dmin
      rw [hZ, Ux3.minor_blocks Z _ l' (by omega) (by omega), hZdet]
      refine mul_ne_zero hc ?_
      exact hγO.1 ⟨l', by omega⟩ hl'
  · have h1 : Dmin k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) (Fin.last _) =
        Z.det * Dmin k ρ z0 z0' γ (Fin.last _) := by
      unfold Dmin
      rw [hZ]
      exact Ux3.minor_blocks _ _ (ρ + 1) le_rfl _
    have h0 : Dmin k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) ⟨1 + ρ, by omega⟩ =
        Z.det * Dmin k ρ z0 z0' γ ⟨ρ, by omega⟩ := by
      unfold Dmin
      rw [hZ]
      exact Ux3.minor_blocks _ _ ρ (by omega) _
    have ht : Tz k (1 + ρ) (liftVec k 1 ρ z0) = Tz k ρ z0 := by rw [Ux3.tz_low _ hz, lowV_lift]
    have ht' : Tz k (1 + ρ) (liftVec k 1 ρ z0') = Tz k ρ z0' := by rw [Ux3.tz_low _ hz', lowV_lift]
    have hG : Gf k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) =
        Complex.normSq c * Gf k ρ z0 z0' γ := by
      unfold Gf
      rw [h1, h0, ht, ht', hZdet, Complex.normSq_mul, Complex.normSq_mul]
      ring
    rw [hG]
    exact mul_pos (Complex.normSq_pos.2 hc) hγO.2

theorem jfStep : JFStep := jfStep_of mcOm

end Formalism.FourierDecayAlt.P.PBH
end
end

