import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0033
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0227
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteSumLocalExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0181
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0076
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0081
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.GramSchmidtFramesLocal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.GsFramesOfIso
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0230
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ToStdAppendBlk

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnDatumBd
section
open Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section pair

variable {k r : ℕ} {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℂ E₂]

theorem ssn_ckOn_subset {m : ℕ∞} {UU UU' : Set (Mat k r)} {f : Mat k r → E₁} (h : CkOn m UU f) (hs : UU' ⊆ UU) :
    CkOn m UU' f := fun g hg => h g (hs hg)

theorem ssn_ckOn_pair {m : ℕ∞} {UU : Set (Mat k r)} {f₁ : Mat k r → E₁} {f₂ : Mat k r → E₂}
    (h₁ : CkOn m UU f₁) (h₂ : CkOn m UU f₂) : CkOn m UU (fun g => (f₁ g, f₂ g)) := by
  intro g₀ hg₀
  obtain ⟨U₁, f₁', hU₁, hg₁, hc₁, he₁⟩ := h₁ g₀ hg₀
  obtain ⟨U₂, f₂', hU₂, hg₂, hc₂, he₂⟩ := h₂ g₀ hg₀
  refine ⟨U₁ ∩ U₂, fun g => (f₁' g, f₂' g), hU₁.inter hU₂, ⟨hg₁, hg₂⟩,
    (hc₁.mono Set.inter_subset_left).prodMk (hc₂.mono Set.inter_subset_right), fun g hg hgG => ?_⟩
  show (f₁ g, f₂ g) = (f₁' g, f₂' g)
  rw [he₁ g hg.1 hgG, he₂ g hg.2 hgG]

theorem ssn_Dw_pair {U : Set (Mat k r)} (hU : IsOpen U) {f₁ : Mat k r → E₁} {f₂ : Mat k r → E₂}
    (h₁ : CkOn ⊤ (U ∩ GV k r) f₁) (h₂ : CkOn ⊤ (U ∩ GV k r) f₂) :
    ∀ w : List (Bool × Mat k r), (∀ x ∈ w, inLie k r x.2) → ∀ g ∈ GV k r, g ∈ U →
      Dw w (fun g => (f₁ g, f₂ g)) g = (Dw w f₁ g, Dw w f₂ g) := by
  intro w
  induction w with
  | nil => intro _ g _ _; rfl
  | cons x w ih =>
    intro hw g hg hgU
    have hx : inLie k r x.2 := hw x (by simp)
    have hw' : ∀ y ∈ w, inLie k r y.2 := fun y hy => hw y (by simp [hy])
    show Dx x (Dw w (fun g => (f₁ g, f₂ g))) g = (Dx x (Dw w f₁) g, Dx x (Dw w f₂) g)
    rw [Dx_congr_loc hx hU (f₂ := fun g => (Dw w f₁ g, Dw w f₂ g)) (fun g hg hgU => ih hw' g hg hgU) g hg hgU]
    have c₁ : CkOn 1 (U ∩ GV k r) (Dw w f₁) := CkOn_Dw hw' (sCkOn_mono le_top h₁)
    have c₂ : CkOn 1 (U ∩ GV k r) (Dw w f₂) := CkOn_Dw hw' (sCkOn_mono le_top h₂)
    have d₁ := CkOn_diff hx c₁ ⟨hgU, hg⟩ hg
    have d₂ := CkOn_diff hx c₂ ⟨hgU, hg⟩ hg
    rw [Dx_eq]
    exact (d₁.prodMk d₂).deriv

end pair

theorem datumBd_of_chain (hCh : SSn.ChainBd) : DatumBd := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v Bg a a' ι Ψ hBg hD hΨ
  intro ε hε m
  set U : Set (B.Mat S.G.k S.G.r) := {g | ε / 2 < GfP S T v g} with hUdef
  have hUo : IsOpen U := isOpen_lt continuous_const (Gf_cont (T v).base.z (T v).base.z')
  set K : Set (B.Mat S.G.k S.G.r) := {g | g ∈ B.GV S.G.k S.G.r ∧ ε ≤ GfP S T v g} with hKdef
  have hUG : U ∩ B.GV S.G.k S.G.r ⊆ B.GPos (T v).base := fun g hg =>
    ⟨hg.2, lt_trans (by linarith) hg.1⟩
  have hKU : K ⊆ U := fun g hg => show ε / 2 < GfP S T v g by linarith [hg.2]
  have hKG : K ⊆ B.GV S.G.k S.G.r := fun g hg => hg.1
  set F : B.Mat S.G.k S.G.r → (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × (Fin (2 * S.G.r + S.G.k + 1) → ℂ) ×
      B.Mat S.G.k S.G.r := fun g => (a g, (a' g, ι g)) with hFdef
  have cka : CkOn ⊤ (U ∩ B.GV S.G.k S.G.r) a := ssn_ckOn_subset hD.1 hUG
  have cka' : CkOn ⊤ (U ∩ B.GV S.G.k S.G.r) a' := ssn_ckOn_subset hD.2.1 hUG
  have ckι : CkOn ⊤ (U ∩ B.GV S.G.k S.G.r) ι := ssn_ckOn_subset hD.2.2.1 hUG
  have ckF : CkOn ⊤ (U ∩ B.GV S.G.k S.G.r) F := ssn_ckOn_pair cka (ssn_ckOn_pair cka' ckι)
  have hFb : ∀ m : ℕ, ∃ C : ℝ, ∀ u w : List (B.Mat S.G.k S.G.r), (∀ X ∈ u, unitLie S.G.k S.G.r X) →
      (∀ X ∈ w, unitLie S.G.k S.G.r X) → u.length + w.length ≤ m → ∀ g ∈ K,
        ‖dLR u w F g‖ ≤ C * gN g ^ (Bg * m) := by
    intro m
    obtain ⟨C₁, h₁⟩ := hD.2.2.2.2.1 ε hε m
    obtain ⟨C₂, h₂⟩ := hD.2.2.2.2.2.1 ε hε m
    obtain ⟨C₃, h₃⟩ := hD.2.2.2.2.2.2.1 ε hε m
    refine ⟨C₁ + C₂ + C₃, fun u w hu hw hl g hg => ?_⟩
    have hlie := lie_LR (unit_lie hu) (unit_lie hw)
    have e1 : dLR u w F g = (dLR u w a g, (dLR u w a' g, dLR u w ι g)) := by
      rw [dLR_eq, dLR_eq, dLR_eq, dLR_eq]
      rw [ssn_Dw_pair hUo cka (ssn_ckOn_pair cka' ckι) _ hlie g hg.1 (hKU hg),
        ssn_Dw_pair hUo cka' ckι _ hlie g hg.1 (hKU hg)]
    rw [e1]
    have b₁ := h₁ u w hu hw hl g hg.1 hg.2
    have b₂ := h₂ u w hu hw hl g hg.1 hg.2
    have b₃ := h₃ u w hu hw hl g hg.1 hg.2
    calc ‖(dLR u w a g, (dLR u w a' g, dLR u w ι g))‖
        ≤ ‖dLR u w a g‖ + (‖dLR u w a' g‖ + ‖dLR u w ι g‖) :=
          (norm_prod_le_iff.2 ⟨le_add_of_nonneg_right (by positivity),
            (norm_prod_le_iff.2 ⟨le_add_of_nonneg_right (norm_nonneg _),
              le_add_of_nonneg_left (norm_nonneg _)⟩).trans (le_add_of_nonneg_left (norm_nonneg _))⟩)
      _ ≤ C₁ * gN g ^ (Bg * m) + (C₂ * gN g ^ (Bg * m) + C₃ * gN g ^ (Bg * m)) := by
          linarith
      _ = (C₁ + C₂ + C₃) * gN g ^ (Bg * m) := by ring
  obtain ⟨C, hC⟩ := hCh S.G.k S.G.r _ _ (fun x => Ψ x.1 x.2.1 x.2.2) hΨ F U K hUo ckF hKU hKG Bg hBg hFb m
  refine ⟨C, fun u w hu hw hl g hg hεg => ?_⟩
  have hgK : g ∈ K := ⟨hg, hεg⟩
  have hO : IsOpen {g : B.Mat S.G.k S.G.r | 0 < GfP S T v g} :=
    isOpen_lt continuous_const (Gf_cont (T v).base.z (T v).base.z')
  have hlie := lie_LR (unit_lie hu) (unit_lie hw)
  have e : dLR u w (datumCoef S T v Ψ a a' ι) g = dLR u w (fun g => (fun x : (Fin (2 * S.G.r + S.G.k + 1) → ℂ) ×
      (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × B.Mat S.G.k S.G.r => Ψ x.1 x.2.1 x.2.2) (F g)) g := by
    rw [dLR_eq, dLR_eq]
    refine Dw_congr_loc hlie hO (fun g' hg' hg'O => ?_) g hg (show 0 < GfP S T v g by linarith)
    exact datumCoef_pos S T v a a' ι Ψ ⟨hg', hg'O⟩
  rw [e]
  exact hC u w hu hw hl g hgK

end Formalism.FourierDecayAlt.P.CutMP.JA
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjIntAsm
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem hasCompactSupport_rho (D : B.RealPlaceData k r Wp Wq) {q : B.SS k r} (hq : D.inSS q)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : HasCompactSupport F) : HasCompactSupport (B.rho D q F) := by
  have ha := Formalism.FourierDecayAlt.P.B5.inSS_left D hq
  have hb := Formalism.FourierDecayAlt.P.B5.inSS_right D hq
  have himg : B.sgs q ⁻¹' tsupport F ⊆ (fun g => (Matrix.of q.1.2 * Matrix.of q.1.1 : B.Mat k r) * g *
      (Matrix.of q.2.2 * Matrix.of q.2.1 : B.Mat k r)⁻¹) '' tsupport F := by
    intro x hx
    refine ⟨B.sgs q x, hx, ?_⟩
    dsimp only
    rw [Formalism.FourierDecayAlt.P.B5.sgs_eq]
    have key : ∀ (a b y : B.Mat k r), a * a⁻¹ = 1 → b * b⁻¹ = 1 → a * (a⁻¹ * y * b) * b⁻¹ = y := by
      intro a b y ha hb
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hb, Matrix.mul_one, ← Matrix.mul_assoc, ha, Matrix.one_mul]
    exact key _ _ x (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv ha).1 (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv hb).1
  have hcK : IsCompact ((fun g => (Matrix.of q.1.2 * Matrix.of q.1.1 : B.Mat k r) * g *
      (Matrix.of q.2.2 * Matrix.of q.2.1 : B.Mat k r)⁻¹) '' tsupport F) :=
    hF.image ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
  refine hcK.of_isClosed_subset isClosed_closure (closure_minimal (fun x hx => himg (subset_tsupport _ ?_)) hcK.isClosed)
  intro h0
  apply hx
  show B.rho D q F x = 0
  unfold B.rho
  rw [h0]
  simp

variable [FiniteDimensional ℂ Wq]

noncomputable def II (D : B.RealPlaceData k r Wp Wq) (X Y : B.Mat k r → (Wq →L[ℂ] Wp)) : ℂ :=
  ∫ x : Mt k r, B.hsInner (X (Matrix.of x)) (Y (Matrix.of x)) ∂D.μG

theorem ii_swap (D : B.RealPlaceData k r Wp Wq) (X Y : B.Mat k r → (Wq →L[ℂ] Wp)) : II D X Y = conj (II D Y X) := by
  unfold II
  rw [← integral_conj]
  congr 1
  funext x
  unfold B.hsInner
  rw [inner_conj_symm]

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hermitian_curvature_adjoint_integral : AdjIntAsm := by
  intro hU hF k r Wp Wq _ _ _ _ _ _ D Θ hs hc f hf hfc hfs p hp φ hφ hφc hφs
  obtain ⟨p', hp', hUp⟩ := hU k r Wp Wq D p hp
  have hU' : ∀ X Y, II D (B.rho D p X) Y = II D X (B.rho D p' Y) := hUp
  have hF' : ∀ F F' : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F → HasCompactSupport F →
      B.SuppIn (B.GPos D) F → B.CkOn ⊤ (B.GV k r) F' → HasCompactSupport F' → B.SuppIn (B.GPos D) F' →
      II D (B.opApply Θ F) F' = II D F (B.opAdj Θ F') := hF k r Wp Wq D Θ hs hc
  have hcomm : II D (B.opApply Θ (B.rho D p' φ)) f = II D (B.rho D p' (B.opApply Θ φ)) f := by
    unfold II
    refine integral_congr_ae ?_
    filter_upwards [Formalism.FourierDecayAlt.P.B5.haar_ae D.haarG] with x hx
    by_cases hxp : Matrix.of x ∈ B.GPos D
    · rw [hc p' hp' φ (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hφ) _ hxp]
    · have h0 : f (Matrix.of x) = 0 := by
        by_contra hne
        exact hxp (hfs (subset_closure ⟨hx, hne⟩))
      simp only [h0, Formalism.FourierDecayAlt.P.B5.hs_zero_right]
  show II D (B.opAdj Θ (B.rho D p f)) φ = II D (B.rho D p (B.opAdj Θ f)) φ
  calc II D (B.opAdj Θ (B.rho D p f)) φ = conj (II D φ (B.opAdj Θ (B.rho D p f))) := ii_swap D _ _
    _ = conj (II D (B.opApply Θ φ) (B.rho D p f)) := by
        rw [hF' φ (B.rho D p f) hφ hφc hφs (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hf) (hasCompactSupport_rho D hp hfc)
          (suppIn_rho D hp hfs)]
    _ = II D (B.rho D p f) (B.opApply Θ φ) := (ii_swap D _ _).symm
    _ = II D f (B.rho D p' (B.opApply Θ φ)) := hU' _ _
    _ = conj (II D (B.rho D p' (B.opApply Θ φ)) f) := ii_swap D _ _
    _ = conj (II D (B.opApply Θ (B.rho D p' φ)) f) := by rw [hcomm]
    _ = conj (II D (B.rho D p' φ) (B.opAdj Θ f)) := by
        rw [hF' (B.rho D p' φ) f (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp' hφ) (hasCompactSupport_rho D hp' hφc)
          (suppIn_rho D hp' hφs) hf hfc hfs]
    _ = II D (B.opAdj Θ f) (B.rho D p' φ) := (ii_swap D _ _).symm
    _ = II D (B.rho D p (B.opAdj Θ f)) φ := (hU' _ _).symm

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjJComm
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.GA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem gAJComm_of_thetaJ (hT : LT.ThetaJ) : GAJComm := by
  refine ⟨12, 0, by norm_num, le_rfl, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v Θ d Bg hd hBg hΘ _hCoef η F _hη hFs hFg _hFsupp
    U J hU hJ hagree x hx hxU
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hBg0 : 0 ≤ Bg := le_trans (by simp) hBg

  have hAg := LT.agreement_on_domain_holds S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base J F U hJ
    (fun q hq hqU => hagree q ⟨hq.1, by rw [hTT]; exact hq.2⟩ hqU)
  set V : Set (B.Mat S.G.k S.G.r) := Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' ∩
    (fun g => Gf S.G.k S.G.r (T v).base.z (T v).base.z' g) ⁻¹' U with hVdef
  have hVo : IsOpen V := (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open _ _).inter
    (hU.preimage (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.gf_cont _ _))
  have hJV : ∀ y ∈ V, y ∈ B.GV S.G.k S.G.r → J y = B.JF (T v).base F y := fun y hy hyG =>
    hAg y ⟨hyG, hy.1⟩ hy.2
  have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, by rw [← hTT]; exact hx.2⟩
  have hg0 := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
  have hg0V : B.gq (T v).base x ∈ V := ⟨hg0.2, hxU⟩

  have hJck : B.CkOn ⊤ (JF.Om S.G.k S.G.r (T v).base.z (T v).base.z') J :=
    Formalism.FourierDecayAlt.P.CutMP.jdc_ckOn_om _ _ hJ.1
  set UU : Set (B.Mat S.G.k S.G.r) := JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' ∩ V with hUUdef
  have hUU : UU ⊆ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' := Set.inter_subset_left
  have hCkF : B.CkOn (B.opOrder Θ : ℕ∞) UU (B.JF (T v).base F) := by
    intro g₀ hg₀
    obtain ⟨U₁, f', hU₁, hgU₁, hc, he⟩ := hJck g₀ hg₀.1
    refine ⟨U₁ ∩ V, f', hU₁.inter hVo, ⟨hgU₁, hg₀.2⟩, (hc.mono Set.inter_subset_left).of_le ?_, ?_⟩
    · exact_mod_cast le_top
    · intro g hg hgG
      rw [← hJV g hg.2 hgG]
      exact he g hg.1 hgG
  have hg0UU : B.gq (T v).base x ∈ UU := ⟨hg0, hg0V⟩

  have hThr : Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold S.G.k S.G.r
      (B.AB S.G.k S.G.r + 12 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 +
          6 * (S.G.r : ℝ) * ((B.opOrder Θ : ℝ) + 5) + d + 2 * Bg * ((B.opOrder Θ : ℝ) + 5) -
        Bg * ((B.opOrder Θ : ℕ) : ℝ)) (B.opOrder Θ) := by
    have hAB : (0 : ℝ) ≤ B.AB S.G.k S.G.r := by unfold B.AB; positivity
    have hr : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
    have ho : (0 : ℝ) ≤ (B.opOrder Θ : ℝ) := Nat.cast_nonneg _
    apply Formalism.FourierDecayAlt.P.CutMP.jdc_thrW (B.opOrder Θ) _ (B.AB S.G.k S.G.r + 30 * (S.G.r : ℝ) + d +
      Bg * ((B.opOrder Θ : ℝ) + 10)) (by positivity)
    linarith
  obtain ⟨hT1, hT2⟩ := hT S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base Θ _ F UU hThr hΘ.1 hΘ.2 hFs
    (hFg (B.opOrder Θ)) hUU hCkF

  have hg0G : B.gq (T v).base x ∈ B.GV S.G.k S.G.r := hg0.1
  refine ⟨?_, ?_⟩
  · rw [← hT1 _ hg0]
    unfold B.opApply
    congr 1
    apply List.map_congr_left
    intro Tm _
    rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.rw_local Tm.word Tm.word_lie hVo hJV _ hg0V hg0G]
  · rw [← hT2 _ hg0UU]
    unfold B.opAdj
    congr 1
    apply List.map_congr_left
    intro Tm _
    rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.rw_local Tm.word.reverse
      (fun X hX => Tm.word_lie X (List.mem_reverse.1 hX)) hVo
      (f := fun y => Tm.coefAdj y (J y)) (f' := fun y => Tm.coefAdj y (B.JF (T v).base F y))
      (fun y hy hyG => by simp only [hJV y hy hyG]) _ hg0V hg0G]

theorem gAJComm_of_adjComm (hAC : Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AdjComm) : GAJComm :=
  gAJComm_of_thetaJ (LT.thetaJ_of_adjComm hAC)

end Formalism.FourierDecayAlt.P.CutMP.JA.GA

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomCut
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.AdmissibleLieWords
open scoped ComplexConjugate Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def nuG (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  unitH k r (PI.UnitaryGroupMassFormula.GsFr.omW k r z z' g)

def nuG' (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  unitH k r (PI.UnitaryGroupMassFormula.GsFr.omW' k r z z' g)

def PpG (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : B.Mat k r :=
  PI.UnitaryGroupMassFormula.GsFr.Pm k r z' - PI.UnitaryGroupMassFormula.GsFr.Rk k r (nuG' z z' g) (nuG' z z' g) * PI.UnitaryGroupMassFormula.GsFr.Pm k r z'

def ioG (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : B.Mat k r :=
  PI.UnitaryGroupMassFormula.GsFr.Phi k r z z' g * PpG z z' g

def posG (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (B.Mat k r) :=
  {g | g ∈ B.GV k r ∧ 0 < Gf k r z z' g}

def geG (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (ε : ℝ) : Set (B.Mat k r) :=
  {g | g ∈ B.GV k r ∧ ε ≤ Gf k r z z' g}

def GeomSmooth : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' →
    B.CkOn ⊤ (posG k r z z') (nuG z z') ∧ B.CkOn ⊤ (posG k r z z') (nuG' z z') ∧
      B.CkOn ⊤ (posG k r z z') (ioG z z')

def GeomEqvNu : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, ∀ h' ∈ UWset k r z', ∀ n' ∈ Nset k r, ∀ g ∈ posG k r z z',
      nuG z z' g = h *ᵥ nuG z z' (h⁻¹ * n⁻¹ * g * n' * h') ∧
        nuG' z z' g = h' *ᵥ nuG' z z' (h⁻¹ * n⁻¹ * g * n' * h')

def GeomEqvIo : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, ∀ h' ∈ UWset k r z', ∀ n' ∈ Nset k r, ∀ g ∈ posG k r z z',
      ioG z z' g = h * ioG z z' (h⁻¹ * n⁻¹ * g * n' * h') * h'⁻¹

def GeomAtGq : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), 1 ≤ k →
    C2.StdZ k r z → C2.StdZ k r z' → IsSection k r z z' μsec →
    ∀ (c : Fin r → ℂ) (ζ : ℂ), (∀ l, c l ≠ 0) → Tz k r z * Tz k r z' < Complex.normSq ζ →
      nuG z z' (bigCell k r c (μsec ζ)) = phD c • nu0 k r z z' μsec ζ ∧
        nuG' z z' (bigCell k r c (μsec ζ)) = conj (phD c) • nu0' k r z z' μsec ζ ∧
          ioG z z' (bigCell k r c (μsec ζ)) = io0 k r z z' μsec ζ

def GeomBd0 : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' →
    ∃ C : ℝ, ∀ g ∈ posG k r z z', ‖nuG z z' g‖ ≤ C ∧ ‖nuG' z z' g‖ ≤ C ∧ ‖ioG z z' g‖ ≤ C

def UBLInvSqrt : Prop :=
  ∀ (k r d : ℕ) (P : B.Mat k r → ℂ), U.IsPolyDeg d P → ∀ (S : Set (B.Mat k r)), S ⊆ B.GV k r →
    ∀ c : ℝ, 0 < c → (∀ g ∈ S, c ≤ (P g).re) → ∀ n : ℕ,
      UBL (fun g => (((Real.sqrt (P g).re)⁻¹ : ℝ) : ℂ)) S n 0 d

def GeomUBL : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' → ∀ ε : ℝ, 0 < ε →
    (∃ e γ : ℕ, e ≤ 4 * (r + 1) ∧ γ ≤ 2 * (r + 1) ∧ ∀ n, UBL (nuG z z') (geG k r z z' ε) n e γ) ∧
    (∃ e γ : ℕ, e ≤ 4 * (r + 1) ∧ γ ≤ 2 * (r + 1) ∧ ∀ n, UBL (nuG' z z') (geG k r z z' ε) n e γ) ∧
    (∃ e γ : ℕ, e ≤ 4 * (r + 1) ∧ γ ≤ 2 * (r + 1) ∧ ∀ n, UBL (ioG z z') (geG k r z z' ε) n e γ)

def GeomAssemble : Prop :=
  GeomSmooth → GeomEqvNu → GeomEqvIo → GeomAtGq → GeomBd0 → GeomUBL → SSnGeom

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameTransportToLastLevel
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.WordCorrespondence

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

theorem transport_gen {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (k n i r' : ℕ) (hn : i + r' = n) (hr' : r' = 0)
    {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * r' + k + 1) → ℂ}
    (hz : D.castV hn (liftVec k i r' zs) = z) (hz' : D.castV hn (liftVec k i r' zs') = z')
    {π : Mx k n → (Wp →L[ℂ] Wp)} {π' : Mx k n → (Wq →L[ℂ] Wq)} {πs : Mx k r' → (Wp →L[ℂ] Wp)}
    {πs' : Mx k r' → (Wq →L[ℂ] Wq)}
    (hπ : ∀ y, πs y = π (D.castM hn (ιLev k i r' y))) (hπ' : ∀ y, πs' y = π' (D.castM hn (ιLev k i r' y)))
    (X₀ : ActualOps k n z z' π π') (L₀ : R.LevelData (Pr (RadSp k n z z' π π')) n)
    (st₀ : Fr.Start (Pr (RadSp k n z z' π π')))
    (X : ActualOps k r' zs zs' πs πs') (L : R.LevelData (Pr (RadSp k r' zs zs' πs πs')) r')
    (st : Fr.Start (Pr (RadSp k r' zs zs' πs πs')))
    (hL₀ : IsActualLevel X₀ L₀) (hL : IsActualLevel X L) (s : ℂ) (hst₀ : ∀ Y, st₀.QQ Y = s • X₀.QQ Y)
    (hst : ∀ Y, st.QQ Y = s • X.QQ Y) (hq : st₀.q = st.q) (hinv : st₀.inv = st.inv)
    (hSL₀ : Fr.IsStarLevel L₀) (hSL : Fr.IsStarLevel L) (hs₀ : Fr.IsLevelStart L₀ st₀) (hs : Fr.IsLevelStart L st)
    (c : Fin n → ℂ) (hc : c ∈ OmX n) :
    ∃ T : RadSp k n z z' π π' →ₗ[ℂ] RadSp k r' zs zs' πs πs',
      (∀ Ψ c' g, (T Ψ : Fn k r' (Wq →L[ℂ] Wp)) c' g = (Ψ : Fn k n (Wq →L[ℂ] Wp)) c (D.castM hn (ιLev k i r' g))) ∧
      ∀ (w : List C.Letter), Fr.admitted st₀ (D.positionted w) → Fr.admitted st (D.positionted w) →
      ∀ (Ψ : Wd.Ix (Fin w.length) → RadSp k n z z' π π') (e : Wd.Ix (Fin w.length)) (c' : Fin r' → ℂ)
        (g : B.Mat k r'),
        (P5.act (Fr.ofWord L₀ st₀ (D.positionted w)).F Ψ e : Fn k n (Wq →L[ℂ] Wp)) c (D.castM hn (ιLev k i r' g)) =
          (P5.act (Fr.ofWord L st (D.positionted w)).F (fun e' => T (Ψ e')) e : Fn k r' (Wq →L[ℂ] Wp)) c' g := by
  subst hn
  rw [P.JCTx5.castV_rfl] at hz hz'
  subst hz hz'
  obtain rfl : πs = fun y => π (ιLev k i r' y) := funext fun y => by rw [hπ, P.JCTx5.castM_rfl]
  obtain rfl : πs' = fun y => π' (ιLev k i r' y) := funext fun y => by rw [hπ', P.JCTx5.castM_rfl]
  have fr := fun (j : Fin 6) v => fn_rs hr' hc X₀ X j v
  have tr := fun Y (a b : Fin 2) v => t_rs hr' hc X₀ X Y a b v
  obtain ⟨-, -, -, -, -, -, h0ζ, h0ζi, h0ζb, h0ζbi, h0G, h0Gi, h0TT⟩ := hL₀
  obtain ⟨-, -, -, -, -, -, hζ, hζi, hζb, hζbi, hG, hGi, hTT⟩ := hL
  have G : Gen (rsL hr' hc zs zs' π π') L₀ L :=
    { ζ := by rw [h0ζ, hζ]; exact rel_mk (fr 0) (fr 2)
      ζi := by rw [h0ζi, hζi]; exact rel_mk (fr 1) (fr 3)
      ζb := by rw [h0ζb, hζb]; exact rel_mk (fr 2) (fr 0)
      ζbi := by rw [h0ζbi, hζbi]; exact rel_mk (fr 3) (fr 1)
      GG := by rw [h0G, hG]; exact rel_mk (fr 4) (fr 4)
      GGi := by rw [h0Gi, hGi]; exact rel_mk (fr 5) (fr 5)
      TT := by rw [h0TT, hTT, tz_lift, tz_lift] }
  have hQ : ∀ Y, MRel (rsL hr' hc zs zs' π π') (st₀.QQ Y) (st.QQ Y) := fun Y => by
    rw [hst₀, hst]
    exact mrel_smul s fun a b => rel_mk (fun v => tr Y a b v) (fun v => tr (star Y) b a v)
  refine ⟨rsL hr' hc zs zs' π π', fun Ψ c' g => by rw [P.JCTx5.castM_rfl]; rfl, fun w h₀ h Ψ e c' g => ?_⟩
  rw [P.JCTx5.castM_rfl]
  have key := act_frame G hQ hq hinv hSL₀ hSL hs₀ hs (D.positionted w) h₀ h Ψ e
  exact congrArg (fun v : RadSp k r' zs zs' _ _ => (v : Fn k r' (Wq →L[ℂ] Wp)) c' g) key

end Formalism.FourierDecayAlt.P.WordCorrespondence

theorem Formalism.FourierDecayAlt.P.frame_transport_to_last_level : Formalism.FourierDecayAlt.P.PBI.FrameTransport := by
  intro Wp Wq _ _ _ _ _ _ P p X₀ μ₀ L₀ st₀ X μ L st hD₀ hD c hc
  obtain ⟨T, hT, hact⟩ := Formalism.FourierDecayAlt.P.WordCorrespondence.transport_gen P.k P.r P.r (P.r - P.r) (by omega) (by omega)
    (p.T.z_lev P.r le_rfl) (p.T.z'_lev P.r le_rfl) (p.T.π_lev P.r le_rfl) (p.T.π'_lev P.r le_rfl)
    X₀ L₀ st₀ X L st hD₀.2.2.1 hD.2.2.1 (Formalism.FourierDecayAlt.M.sgn P p.l0) hD₀.2.2.2.1 hD.2.2.2.1
    (hD₀.2.2.2.2.1.trans hD.2.2.2.2.1.symm) (hD₀.2.2.2.2.2.1.trans hD.2.2.2.2.2.1.symm)
    hD₀.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.1 hD₀.2.2.2.2.2.2.2 hD.2.2.2.2.2.2.2 c hc
  exact ⟨T, hT, fun w h₀ h Ψ e c' g _ _ => hact w h₀ h Ψ e c' g⟩
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ProdOfFnMap
section
namespace Formalism.FourierDecayAlt.P.LiftDegreeLemmas

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section blockL

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

def uS (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (Y : Finset C.LPt) (blk : ℕ × ℂ) (h : C.LPt) :
    Wd.Ix (Fin w.length) → B.Mat S.G.k (S.G.r - j) → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :=
  uY S p F v ε j hj w (Y.image fun h => h ++ [blk]) (h ++ [blk])

theorem uS_mem (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (Y : Finset C.LPt) (blk : ℕ × ℂ) (h : C.LPt) (hh : h ∈ Y) :
    uS S p F v ε j hj w Y blk h = uB S p F v ε j hj w (h ++ [blk]) :=
  uY_mem S p F v ε j hj w _ _ (Finset.mem_image_of_mem _ hh)

theorem glob_pos' (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) : 0 < S.G.g ∧ 0 < S.G.ka := by
  obtain ⟨hg1, hg2, -⟩ := hB
  refine ⟨by unfold Sz.Glob.g; exact_mod_cast Nat.mul_pos hg1 hg2, ?_⟩
  unfold Sz.Glob.ka; rw [S.hv]; exact div_pos Real.pi_pos (by linarith [PBD.rd_pos' E])

theorem prod_ofFn_map' {K : ℕ} (g0 : Fin K → ℝ) (g : ℝ → ℝ) : ((List.ofFn g0).map g).prod = ∏ c, g (g0 c) := by
  rw [List.map_ofFn, List.prod_ofFn]; rfl

end blockL

end

end Formalism.FourierDecayAlt.P.LiftDegreeLemmas
end

