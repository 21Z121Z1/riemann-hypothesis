import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0107
import Formalism.HermitianCurvature.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0087
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0068
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0055
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0047
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0054
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseIndexConstantInjective
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0025
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0041
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0040
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0039
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Jets.SurjectiveAppTopSqCube
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0079
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPref
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GsSpMapGermAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0075
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffEv
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartHatCoeffBounds
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0108
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUnitCoeffMulSeriesLeNorm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0109

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselBigCellPointVectorEqBesselStatement
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselBigCellPoint_vector_eq_bessel : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ), (¬ ((∀ a, c a ≠ 0) ∧ TBB.TTp p < Complex.normSq (c (Fin.last P.r))) → p.V H (TBB.bigPt P.r c) = 0) ∧ (((∀ a, c a ≠ 0) ∧ TBB.TTp p < Complex.normSq (c (Fin.last P.r))) → 0 < TBB.Gp p (TBB.bigPt P.r c) ∧ ∀ γ ∈ B.GV P.k P.r, Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN (TBB.bigPt P.r c) (P.r + 1) → D.IsDFrame p.T.base p.ν' p.m₀ γ → γ ∈ B.GPos p.T.base ∧ p.V H (TBB.bigPt P.r c) = B.JF p.T.base H γ) := by
  first | exact @GlobalTheory.vec_bigPt_eq_bessel | exact GlobalTheory.vec_bigPt_eq_bessel | (intros; apply GlobalTheory.vec_bigPt_eq_bessel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapExistsFunctional
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_normalised_bessel_map : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∃ l, IsBeL R z π μW μN l := by
  intro H k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hgap hok hside
  have hconv := GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap H k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hside
  by_cases hz : ∃ w ∈ R.sm, ∃ v ∈ R.TK, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ≠ 0
  · obtain ⟨l₀, La, hB, hnz, hshape⟩ :=
      GlobalTheory.T.bessel_gap_exists_nonzero H k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hside hz
    have hTK : ∀ v ∈ R.TK, v ∈ R.sm :=
      (GlobalTheory.rep_basic_of_isDS H.1.2.2.1 k r ε mu R hDS).2.2.2.2.1
    obtain ⟨v₀, hv₀, hl₀⟩ := GlobalTheory.bessel_nonzero_on_translates H k r ε mu R Wp z π l₀ hDS hB hnz
    obtain ⟨c₀, -, hc₀⟩ := GlobalTheory.BesselDegree.schur_fdeg H k r ε μG hside.2.2.2.2.2.2.1
    have hP := GlobalTheory.T.bessel_integral_l2_norm_eq_div_formal_degree H k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hside _ (hc₀ mu R hDS).1
    have hadj := GlobalTheory.T.adjoint_besselIntegral_eq_swap_of_gap H k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hside
    obtain ⟨c, hc, hLa⟩ := GlobalTheory.T.positive_rank_one_proportional R.TK Wp (fun v => l₀ v) (fun v => La v)
      (fun v w => by
        have := hadj v v.2 w w.2
        rwa [hshape w (hTK _ w.2) v v.2, hshape v (hTK _ v.2) w w.2] at this)
      (fun v ξ => by
        have := hP v v.2 ξ
        rw [hshape v (hTK _ v.2) v v.2] at this
        exact ⟨this.1, this.2.1⟩)
      ⟨⟨v₀, hv₀⟩, hl₀⟩
    refine ⟨fun w => ((Real.sqrt c : ℝ) : ℂ) • l₀ w, Formalism.FourierDecayAlt.P.DDSmoothness.bessel_smul hB _, ?_⟩
    intro w hw v hv
    refine ⟨(hconv v hv).1 w hw, ?_⟩
    have hv' : La v = (c : ℂ) • l₀ v := hLa ⟨v, hv⟩
    rw [hshape w hw v hv, hv']
    ext ξ
    have hs : ((Real.sqrt c : ℝ) : ℂ) * ((Real.sqrt c : ℝ) : ℂ) = (c : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left, Complex.conj_ofReal,
      smul_smul]
    congr 1
    rw [← hs]; ring
  · push Not at hz
    refine ⟨fun _ => 0, Formalism.FourierDecayAlt.P.DDSmoothness.bessel_zero, ?_⟩
    intro w hw v hv
    refine ⟨(hconv v hv).1 w hw, ?_⟩
    rw [hz w hw v hv]
    ext ξ
    simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliModuleModel
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

noncomputable section
namespace GlobalTheory
namespace CapelliModel

open Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.PBG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem mem_lev {g : B.Mat k r} : g ∈ Q.Glev k r 0 ∩ Set.univ ↔ g ∈ B.GV k r :=
  ⟨fun h => h.1.1, fun h => ⟨⟨h, fun a ha => absurd ha (by simp)⟩, trivial⟩⟩

theorem smooth_iff {f : B.Mat k r → F} :
    Q.SmoothLev k r 0 Set.univ f ↔ B.CkOn ⊤ (B.GV k r) f := by
  constructor
  · intro h g₀ hg₀
    obtain ⟨U, f', hU, hg, hf, he⟩ := h g₀ (mem_lev.2 hg₀)
    exact ⟨U, f', hU, hg, hf, fun g hgU hgG => he g hgU (mem_lev.2 hgG).1⟩
  · intro h g₀ hg₀
    obtain ⟨U, f', hU, hg, hf, he⟩ := h g₀ (mem_lev.1 hg₀)
    exact ⟨U, f', hU, hg, hf, fun g hgU hgG => he g hgU hgG.1⟩

theorem dLR_zero (u v : List (B.Mat k r)) : B.dLR u v (0 : B.Mat k r → F) = 0 := by
  have h1 : B.Rw v (0 : B.Mat k r → F) = 0 := by
    unfold B.Rw
    induction v with
    | nil => rfl
    | cons X v ih =>
      rw [List.foldr_cons, ih]
      funext g
      simp [RdV]
  unfold B.dLR
  rw [h1]
  induction u with
  | nil => rfl
  | cons X u ih =>
    rw [List.foldr_cons, ih]
    funext g
    simp [B.LdV]

theorem inCC_zero (A : ℝ) (m : ℕ) : B.InCC A m (0 : B.Mat k r → F) := by
  refine ⟨0, fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩, ?_⟩
  intro u v _ _ _ g _
  simp [dLR_zero]

abbrev Sm (k r : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] := VS k r 0 Set.univ F

abbrev Eu (k r : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] (a b : Fin (2 * r + k + 1)) :
    Module.End ℂ (Sm k r F) := E0 isOpen_univ a b

theorem sm_ext (v v' : Sm k r F) (h : ∀ g ∈ B.GV k r, (v : B.Mat k r → F) g = (v' : B.Mat k r → F) g) :
    v = v' := by
  refine Subtype.ext (funext fun g => ?_)
  by_cases hg : g ∈ Q.Glev k r 0 ∩ Set.univ
  · exact h g (mem_lev.1 hg)
  · rw [v.2.2 g hg, v'.2.2 g hg]

theorem ev_Eu (a b : Fin (2 * r + k + 1)) (v : Sm k r F) (g : B.Mat k r) (hg : g ∈ B.GV k r) :
    (Eu k r F a b v : B.Mat k r → F) g = Q.EH k r a b (v : B.Mat k r → F) g := by
  have := ev_E (i := 0) isOpen_univ (c0 a) (c0 b) v (mem_lev.2 hg)
  rwa [position_level_zero_coord, position_level_zero_coord] at this

theorem qminorOp_cast {n t t' : ℕ} (h : t = t')
    (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → F) → (Matrix (Fin n) (Fin n) ℂ → F))
    (a : Fin t' → Fin n) (a' : Fin t → Fin n) (ha : ∀ j, a' j = a (Fin.cast h j)) (u : ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → F) : qminorOp Eop a' a' u f = qminorOp Eop a a u f := by
  subst h
  have : a' = a := funext ha
  rw [this]

theorem CV_eq (Y : ℂ) (f : B.Mat k r → F) :
    Q.CV k r Y f = qminorOp (Q.EH k r) id id (Y + (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2) f := by
  have hm : Q.mdim k r 0 = 2 * r + k + 1 := by simp [Q.mdim]
  unfold Q.CV Q.capL Q.uC
  rw [qminorOp_cast hm _ id _ (fun j => by ext; simp [Q.posL]), hm]

theorem ev_qdet (Y : ℂ) (v : Sm k r F) (g : B.Mat k r) (hg : g ∈ B.GV k r) :
    (qdet (Eu k r F) (Y + (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2) v : B.Mat k r → F) g =
      Q.CV k r Y (v : B.Mat k r → F) g := by
  rw [CV_eq]
  exact quantum_minor_level_eq_hat isOpen_univ id id _ v g (mem_lev.2 hg)

def eig (k r : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] (χ : ℂ → ℂ) (A : ℝ) :
    Submodule ℂ (Sm k r F) where
  carrier := {v | (∀ m : ℕ, B.InCC A m (v : B.Mat k r → F)) ∧ ∀ u : ℂ, qdet (Eu k r F) u v = χ u • v}
  zero_mem' := ⟨fun m => inCC_zero A m, fun u => by simp⟩
  add_mem' := by
    rintro v w ⟨hv, hv'⟩ ⟨hw, hw'⟩
    refine ⟨fun m => ?_, fun u => by rw [map_add, hv', hw', smul_add]⟩
    obtain ⟨c, hc⟩ := hv m
    obtain ⟨c', hc'⟩ := hw m
    exact ⟨_, (Formalism.FourierDecayAlt.P.matrix_coefficient_linear k r F A m _ _ c c' 1 hc hc').1⟩
  smul_mem' := by
    rintro a v ⟨hv, hv'⟩
    refine ⟨fun m => ?_, fun u => by rw [map_smul, hv', smul_comm]⟩
    obtain ⟨c, hc⟩ := hv m
    exact ⟨_, (Formalism.FourierDecayAlt.P.matrix_coefficient_linear k r F A m _ _ c c a hc hc).2⟩

open Classical in

def mulOp (k r : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] (c : B.Mat k r → ℂ) :
    Module.End ℂ (Sm k r F) :=
  if h : B.CkOn ⊤ (B.GV k r) c then Mh isOpen_univ c (smooth_iff.2 h) else 0

theorem glRel_of_intertwine {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ W) (ι : W →ₗ[ℂ] V)
    (hι : Function.Injective ι) (h : ∀ a b w, ι (E' a b w) = E a b (ι w)) (hE : GlRel E) : GlRel E' := by
  intro a b c d
  refine LinearMap.ext fun w => hι ?_
  have := LinearMap.congr_fun (hE a b c d) (ι w)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, h] at this ⊢
  rw [this]
  congr 1 <;> split_ifs <;> simp [h]

end CapelliModel

open CapelliModel Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.PBG in

theorem capelli_module_model : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (A : ℝ), ∃ (V W : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : AddCommGroup W) (_ : Module ℂ W) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ V) (E' : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ W) (ι : W →ₗ[ℂ] V) (ev : V →ₗ[ℂ] (B.Mat k r → (Wq →L[ℂ] Wp))) (mul : (B.Mat k r → ℂ) → Module.End ℂ V), GlRel E ∧ GlRel E' ∧ (∀ a b w, ι (E' a b w) = E a b (ι w)) ∧ (∀ (u : ℂ) (w : W), qdet E' u w = (∏ s, (u + ((lam s : ℂ) - (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2))) • w) ∧ (∀ v, B.CkOn ⊤ (B.GV k r) (ev v)) ∧ (∀ v v', (∀ g ∈ B.GV k r, ev v g = ev v' g) → v = v') ∧ (∀ w, ∀ m : ℕ, B.InCC A m (ev (ι w))) ∧ (∀ f : B.Mat k r → (Wq →L[ℂ] Wp), (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A) m (f)) → (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → ∃ w, ∀ g ∈ B.GV k r, ev (ι w) g = f g) ∧ (∀ a b v, ∀ g ∈ B.GV k r, ev (E a b v) g = Q.EH k r a b (ev v) g) ∧ (∀ (Y : ℂ) v, ∀ g ∈ B.GV k r, ev (qdet E (Y + (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2) v) g = Q.CV k r Y (ev v) g) ∧ (∀ c : B.Mat k r → ℂ, B.CkOn ⊤ (B.GV k r) c → (∀ v, ∀ g ∈ B.GV k r, ev (mul c v) g = c g • ev v g) ∧ ∀ a b v, ∀ g ∈ B.GV k r, ev (E a b (mul c v)) g = c g • ev (E a b v) g + Q.EH k r a b c g • ev v g) := by
  intro k r Wp Wq _ _ _ _ _ _ lam A
  let χ : ℂ → ℂ := fun u => ∏ s, (u + ((lam s : ℂ) - (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2))
  have hgl : GlRel (Eu k r (Wq →L[ℂ] Wp)) := level_zero_derivation_relation isOpen_univ
  have hst : ∀ a b, ∀ v ∈ eig k r (Wq →L[ℂ] Wp) χ A, Eu k r (Wq →L[ℂ] Wp) a b v ∈ eig k r (Wq →L[ℂ] Wp) χ A := by
    rintro a b v ⟨hv, hv'⟩
    refine ⟨fun m => ?_, fun u => ?_⟩
    · exact (GlobalTheory.ckOn_inCC_congr_on_group k r _ A _ _ (fun g hg => (ev_Eu a b v g hg).symm)).2 m
        ((GlobalTheory.T.operatorEab_preserves_smooth_classCC k r Wp Wq A a b _ ⟨smooth_iff.1 v.2.1, hv⟩).2 m)
    · have := LinearMap.congr_fun (qDetCentral _ _ _ hgl u a b) v
      rw [Module.End.mul_apply, Module.End.mul_apply, hv', map_smul] at this
      exact this
  have hint : ∀ a b (w : eig k r (Wq →L[ℂ] Wp) χ A),
      (eig k r (Wq →L[ℂ] Wp) χ A).subtype ((Eu k r (Wq →L[ℂ] Wp) a b).restrict (hst a b) w) =
        Eu k r (Wq →L[ℂ] Wp) a b ((eig k r (Wq →L[ℂ] Wp) χ A).subtype w) := fun _ _ _ => rfl
  refine ⟨Sm k r (Wq →L[ℂ] Wp), eig k r (Wq →L[ℂ] Wp) χ A, inferInstance, inferInstance, inferInstance,
    inferInstance, Eu k r (Wq →L[ℂ] Wp), fun a b => (Eu k r (Wq →L[ℂ] Wp) a b).restrict (hst a b),
    (eig k r (Wq →L[ℂ] Wp) χ A).subtype, (Sm k r (Wq →L[ℂ] Wp)).subtype, mulOp k r _, hgl,
    glRel_of_intertwine _ _ _ (Submodule.subtype_injective _) hint hgl, hint, ?_,
    fun v => smooth_iff.1 v.2.1, sm_ext, fun w => w.2.1, ?_, ev_Eu, ev_qdet, ?_⟩
  · intro u w
    apply Submodule.subtype_injective
    unfold qdet
    rw [qminor_intertwine _ _ _ _ _ _ _ hint, map_smul]
    exact w.2.2 u
  · rintro f ⟨hf, hfc⟩ hY
    have hcut : ∀ g ∈ B.GV k r, f g = (vK isOpen_univ f (smooth_iff.2 hf) : B.Mat k r → (Wq →L[ℂ] Wp)) g :=
      fun g hg => (cut_of_mem f (mem_lev.2 hg)).symm
    refine ⟨⟨vK isOpen_univ f (smooth_iff.2 hf), fun m => (GlobalTheory.ckOn_inCC_congr_on_group k r _ A _ _ hcut).2 m (hfc m),
      fun u => ?_⟩, fun g hg => (hcut g hg).symm⟩
    refine sm_ext _ _ fun g hg => ?_
    have h1 := ev_qdet (u - (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2) (vK isOpen_univ f (smooth_iff.2 hf)) g hg
    rw [sub_add_cancel] at h1
    have h2 := GlobalTheory.capelli_eigen_real_to_complex k r Wp Wq lam f hf hY (u - (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2) g hg
    rw [CV_eq] at h1 h2
    rw [h1, ← qminorOp_loc isOpen_univ id id _ f _ (fun x hx => hcut x (mem_lev.1 hx)) g (mem_lev.2 hg), h2,
      Submodule.coe_smul, Pi.smul_apply, ← hcut g hg]
    congr 1
    exact Finset.prod_congr rfl fun s _ => by ring
  · intro c hc
    simp only [mulOp, dif_pos hc]
    refine ⟨fun v g hg => ev_M isOpen_univ (smooth_iff.2 hc) v (mem_lev.2 hg), fun a b v g hg => ?_⟩
    have := ev_EM (i := 0) isOpen_univ (c0 a) (c0 b) (smooth_iff.2 hc) v (mem_lev.2 hg)
    rw [position_level_zero_coord, position_level_zero_coord, ← ev_Eu a b v g hg] at this
    exact this

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartFromPointDatumOfLaws
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChartLink

theorem cubical_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (h : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom) {L : RigLB G} (c c' : CubicalStr G L) : c = c' := by
  have e : c.t.s = c'.t.s := by
    refine JetSer.gen_ext_val (φ := thφ G (x3 G)) (ε := thε) L.isLB c.isGen c'.isGen fun y J hJ => ?_
    refine gen_unique L.isLB (G ⊗ G ⊗ G).hom (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1)).left (Over.w _) h c.isGen c'.isGen
      (fun y J hJ => ?_) _ _ y J hJ
    exact ((isCub_cubV c (T := 𝟙_ (Over S)) hJ).face 1 1).trans ((isCub_cubV c' (T := 𝟙_ (Over S)) hJ).face 1 1).symm
  obtain ⟨⟨s⟩, _, _, _, _, _⟩ := c
  obtain ⟨⟨s'⟩, _, _, _, _, _⟩ := c'
  obtain rfl : s = s' := e
  rfl

theorem surjective_of_sq {S : Scheme.{0}} {G : Over S} (h : Function.Surjective (G ⊗ G).hom.appTop.hom) :
    Function.Surjective G.hom.appTop.hom := by
  intro f
  obtain ⟨a, ha⟩ := h ((fst G G).left.appTop.hom f)
  refine ⟨a, ?_⟩
  have e₁ : (lift (𝟙 G) (𝟙 G)).left ≫ (G ⊗ G).hom = G.hom := Over.w _
  have e₂ : (lift (𝟙 G) (𝟙 G)).left ≫ (fst G G).left = 𝟙 _ := congrArg (fun q => q.left) (lift_fst (𝟙 G) (𝟙 G))
  have := congrArg (lift (𝟙 G) (𝟙 G)).left.appTop.hom ha
  rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
    ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, e₁, e₂] at this
  simpa using this

theorem psJet_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {κ : Type} [Fintype κ] [DecidableEq κ]
    (m : ℕ) (g : MvPowerSeries κ R) : psJet m (MvPowerSeries.map f g) = jetCoef f κ m (psJet m g) := by
  unfold psJet jetCoef
  rw [Ideal.Quotient.lift_mk, RingHom.comp_apply]
  congr 1
  unfold psTrunc
  simp [map_sum, MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem germA_comb {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {D : DegData V I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) {κ : Type} [Fintype κ] [DecidableEq κ] (z : JetPts G κ) (τ : Frames U.LG.L z) (hτ : τ.Gen)
    (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (q : ℕ)
    {l : ℕ} (c : Fin l → F) (σ : Fin l → H0 U.LG.L q) (g : Fin l → MvPowerSeries κ V)
    (hσ : ∀ i m (y : Sp (Jet V κ m)) J, Good U.LG.L y J →
      sval (σ i) (z m).left y J = gs (𝟙 _) y ⊤ (toΓ _ (psJet m (g i))) * (val (τ m) (𝟙 _) y J ^ q).val)
    (σ' : U.SecGF F q)
    (hlin : GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => (q : ℤ)) σ'
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (q : ℤ)) σ (UnifPre.gFK (G := G) F)
      (fun i => scal (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left (c i))) :
    GermA U z τ F q σ' (∑ i, c i • MvPowerSeries.map (algebraMap V F) (g i)) := by
  intro m
  have hL := U.LG.isLB
  have key : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet V κ m)) (y : Z) (J), Good U.LG.L y J →
      sval (σ i) (r ≫ (z m).left) y J = cst r y (psJet m (g i)) * (val (τ m) r y J ^ q).val := by
    intro i
    obtain ⟨v, hv⟩ := ExpansionValueZero.exists_coeff (A := Jet V κ m) hL (σ i) (z m).left
      (GeneratorPullback.powGen U.LG.L _ _ (τ m) q) (powGen_isGen_of_isGen _ (hτ m) q)
      (fun W _ h => by simp only [Category.comp_id, _root_.mul_one])
    have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet V κ m)) (y : Z) (J), Good U.LG.L y J →
        sval (σ i) (r ≫ (z m).left) y J = cst r y v * (val (τ m) r y J ^ q).val := fun Z r y J hJ =>
      (hv Z r y J hJ).trans (congrArg (fun u => cst r y v * Units.val u) (map_pow _ _ _))
    obtain rfl : v = psJet m (g i) := H1.cst_ext fun y => by
      obtain ⟨J, hJ, -⟩ := exists_good U.LG.L hL y (K := PEmpty) PEmpty.elim PEmpty.elim (fun k => k.elim) (fun k => k.elim)
      have e := hv' _ (𝟙 _) y J hJ
      rw [Category.id_comp] at e
      exact (Units.mul_left_inj _).1 (e.symm.trans (hσ i m y J hJ))
    exact hv'
  obtain ⟨a, a₁, a₂⟩ := GermBasic.exists_jetPt (F := F) z m
  refine ⟨a, a₁, a₂, fun y J hJ => ?_⟩
  refine (BoxExpansion.secLin_val hlin a y hJ).trans ?_
  have e : gs (𝟙 _) y ⊤ (toΓ _ (psJet m (∑ i, c i • MvPowerSeries.map (algebraMap V F) (g i)))) =
      ∑ i, cst (𝟙 _) y (algebraMap F (Jet F κ m) (c i)) *
        cst (𝟙 _) y (psJet m (MvPowerSeries.map (algebraMap V F) (g i))) := by
    refine (congrArg (cst (𝟙 _) y) (GermBasic.psJet_sum m c _)).trans ((ExpansionValueZero.cst_sum _ _ _ _).trans ?_)
    exact Finset.sum_congr rfl fun i _ => H1.cst_mul _ _ _ _
  rw [e, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [a₂, key i _ _ y J hJ, _root_.mul_assoc]
  refine congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·) ?_ rfl)
  · refine (gs_pull a _ y ⊤ trivial _).trans ?_
    rw [a₁, ← ExpansionValueZero.cst_comp, Category.id_comp]
    rfl
  · rw [psJet_map, ← ExpansionValueZero.cst_comp, Category.id_comp]

theorem exists_chartData {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {V : Type} [CommRing V]
    [IsLocalRing V] (t : SAB H (Sp V)) (Lr : RigLB t.G) (h : Lr = t.PP) (c : CubicalStr t.G Lr)
    (s₂ : Function.Surjective (t.G ⊗ t.G).hom.appTop.hom)
    (s₃ : Function.Surjective (t.G ⊗ t.G ⊗ t.G).hom.appTop.hom) :
    letI := H.starRing
    ∀ (d : ℕ) (BT : FB V d (𝓞 E)) (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
      (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m) (wPT : PrimTyG t),
      IsChartG t (𝟙 (Sp V)) d BT.G.F BT.A.act tg (fun j : Fin d => Pi.single j (1 : V)) xT →
      IsFrameG t (𝟙 (Sp V)) d xT BT.G.F BT.A.act BT.ph1 BT.ph2 BT.sy BT.ad eT → IsPrimG t wPT →
      IsUnivJ t.G (Fin 1 × Fin d) xT → FrTrunc t (𝟙 (Sp V)) d xT eT →
    ∀ τ : Frames Lr.L (κ := Fin 1 × Fin d) xT,
      (∀ (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) (J : (Sp (Jet V (Fin 1 × Fin d) m) ⟶ t.G.left) → Lr.L.ι),
        Good Lr.L y J → val (τ m) (𝟙 _) y J =
          val (genCast (congrArg RigLB.L h).symm _ _ (eLG t (𝟙 (Sp V)) d xT BT.A.act eT wPT m)) (𝟙 _) y J) →
    ∃ (x : JetSer.Fam t.G (Fin d)) (j : Lr.L.ι)
      (u : ∀ a : 𝓞 E, LB.Gen (LB.LinComb Lr.L (rosatiφ t.G (t.act.act a) (t.act.act (star a))) rosatiε))
      (B : FB V d (𝓞 E)) (ρ : LB.Gen (LB.LinComb Lr.L (JetSer.primφ (t.act.act H.w0)) JetSer.primε)) (ε : PS V 2 d),
      Chart.IsUnivChart t.G d x ∧ ⊤ ≤ η[t.G].left ⁻¹ᵁ Lr.L.U j ∧ (∀ a, JetSer.IsNormRos Lr.L _ _ (u a)) ∧
      JetSer.IsFBOf Lr c t.act u x j B ∧ ρ.IsGen ∧ JetSer.Related B BT (pt V (n := 1) d 0) (pt V (n := 1) d 0) ε ∧
      ∀ (q : ℕ) (σ : H0 Lr.L q) (r S g : PS V 1 d), JetSer.IsSer1 x _ (ρ.s (fun _ => j)).val r →
        JetSer.IsSer1 x _ (σ.f (fun _ => j)) S → g * (diagSer BT H.w0 ε * r) ^ q = S →
        ∀ (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) (J : (Sp (Jet V (Fin 1 × Fin d) m) ⟶ t.G.left) → Lr.L.ι),
          Good Lr.L y J →
          sval σ (xT m).left y J = gs (𝟙 _) y ⊤ (toΓ _ (psJet m g)) * (val (τ m) (𝟙 _) y J ^ q).val := by
  subst h
  obtain rfl : c = t.cub := cubical_eq s₃ _ _
  letI := H.starRing
  intro d BT tg xT eT wPT hC hF hW hU hT τ hEL
  obtain ⟨x, hx, hM⟩ := univConv V t.G _ xT hU d (oneCol d)
  obtain ⟨j, hj⟩ := JetSer.exists_index_of_local t.PP.L t.PP.isLB η[t.G].left
  have hu : ∀ a : 𝓞 E, ∃ u, JetSer.IsNormRos t.PP.L (t.act.act a) (t.act.act (star a)) u := fun a => by
    have := t.act.hom a
    have := t.act.hom (star a)
    exact (NormRos.normRos_of_lbIso _ t.G t.PP.L t.PP.isLB _ _ (t.adj a)).1
  choose u hu using hu
  obtain ⟨B, hB⟩ := JetRoad.jetRoad.2.2.2.2.2.2.2.2.2.1 V t.G s₂ s₃ t.PP t.cub (𝓞 E) t.act u hu d x hx j hj
  have := t.act.hom H.w0
  obtain ⟨ρ, hρ, hρc⟩ := (JetSer.exists_unique_normPrim _ t.G t.PP (t.act.act H.w0) t.prim).1
  obtain ⟨ε, hε⟩ := GlobalTheory.T.truncation_frames_local_series E H V t d _ _ _ _ _ _ tg xT eT wPT hC hF hW hT j hj
  refine ⟨x, j, u, B, ρ, ε, hx, hj, hu, hB, hρ,
    LinkRel.linkRel E H V t s₂ d BT tg xT eT wPT hC hF hW x hx hM j hj u hu B hB ε hε,
    fun q σ r S g hr hS hg m y J hJ => ?_⟩
  rw [hEL m y J hJ]
  exact LinkSec.linkSec E H V t (surjective_of_sq s₂) d BT tg xT eT wPT hC hF hW x hx hM j hj ρ hρ hρc ε hε q σ r S g
    hr hS hg m y J hJ

theorem isUnit_diagSer {V : Type} [CommRing V] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {B B' : FB V d O}
    {φ φi : Pt V 1 d} {ε : PS V 2 d} (h : JetSer.Related B B' φ φi ε) (w0 : O) : IsUnit (diagSer B' w0 ε) := by
  have e₀ : MvPowerSeries.constantCoeff ε = 1 := by
    rw [← GaugeAdjoint.constantCoeff_ev (a := ![0, pt V (n := 1) d 0]) (fun j i => by fin_cases j <;> simp [pt]) ε,
      h.ax0, map_one]
  have c : comp1 (B'.A.act w0) (pt V (n := 1) d 0) = B'.A.act w0 := funext fun i => LinkSec.ev_pt_one _
  rw [MvPowerSeries.isUnit_iff_constantCoeff, diagSer, c, GaugeAdjoint.constantCoeff_ev (fun j i => ?_) ε, e₀]
  · exact isUnit_one
  · fin_cases j
    · simp [pt]
    · exact B'.A.const w0 i

theorem linkSt_holds : LinkSt := by
  intro E _ _ _ H V _ _ _ hc t P tors ϖ hϖ Q hQ F _ _ _ _ v hv d BT tg xT eT wPT hC hF hW hU hT τ hτ hEL
  letI := H.starRing
  obtain ⟨s₂, s₃⟩ := FamGerm.surjective_appTop_sq_cube P.U.toUnifPre
  obtain ⟨x, j, u, B, ρ, ε, hx, hj, hu, hB, hρ, hR, hS⟩ := exists_chartData H t P.U.LG P.bundle P.U.cubG s₂ s₃
    d BT tg xT eT wPT hC hF hW hU hT τ hEL
  refine ⟨x, hx, j, hj, u, hu, B, hB, ρ, hρ, ε, hR, ?_⟩
  rintro q s f f' ⟨l, c, σ, fi, g, r, h₁, h₂, h₃, h₄, h₅⟩ hf
  obtain ⟨w, hw⟩ := (isUnit_diagSer hR H.w0).exists_right_inv
  obtain ⟨σ', hσ'⟩ := BoxExpansion.exists_secLin P.U.LG.isLB
    (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj t.G)).left (UnifPre.gFK (R := V) (G := t.G) F)
    (fun _ : Fin 1 => UnifPre.gFK (R := V) (G := t.G) F) (fun _ => (Category.comp_id _).symm) σ c
  refine ⟨σ', ⟨l, c, σ, fi, h₁, hσ', h₂⟩, ?_⟩
  have eV : TWO.algVF (V := V) (F := F) = algebraMap V F := (IsScalarTower.algebraMap_eq V _ F).symm
  have e : f' = ∑ i, c i • MvPowerSeries.map (algebraMap V F) (g i * w ^ q) := by
    have e₁ : f' = f * MvPowerSeries.map (algebraMap V F) (w ^ q) := by
      rw [← hf, _root_.mul_assoc, ← map_pow, ← map_mul, ← mul_pow, hw, one_pow, map_one, _root_.mul_one]
    rw [e₁, h₅, Finset.sum_mul, eV]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPowerSeries.smul_eq_C_mul, _root_.mul_assoc]
  rw [e]
  refine germA_comb P.U.toUnifPre xT τ hτ F q c σ _ (fun i m y J hJ => ?_) σ' hσ'
  obtain ⟨S, hS₁, hS₂⟩ := h₄ i
  refine hS q (σ i) r S _ h₃ hS₁ ?_ m y J hJ
  rw [← hS₂, _root_.mul_assoc, ← mul_pow, ← _root_.mul_assoc, _root_.mul_comm w, hw, _root_.one_mul]

theorem link : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → LinkSt := fun _ _ _ _ => linkSt_holds

end GlobalTheory.ChartLink
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartHatCoeffBoundsStatement
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_hat_coeff_bounds : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (t : ℂ), M.Chart ℓ → ¬ M.Small t → Bd 1 (hat M.ι ℓ (fun z => M.x (z + t))) ∧ Bd 1 (hat M.ι ℓ (fun z => M.y (z + t))) ∧ ∀ r : ℝ, r < 1 → ∃ n, 0 < n ∧ r < ‖coeff n (hat M.ι ℓ (fun z => M.x (z + t)))‖ := by
  first | exact @GlobalTheory.MomOne.Transl.translate_integral | exact GlobalTheory.MomOne.Transl.translate_integral | (intros; apply GlobalTheory.MomOne.Transl.translate_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffBoundedTaylorEllipticOfPolesStatement
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cpSeriesCoeffBounded_taylor_elliptic_of_poles : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (φ : ℂ → ℂ), M.Chart ℓ → Ell M.L φ → AnalyticAt ℂ φ 0 → (∀ p, meromorphicOrderAt φ p < 0 → ¬ M.Small p) → Bdd (hat M.ι ℓ φ) := by
  first | exact @GlobalTheory.MomOne.EllBdd.bdd_hat_of_ell | exact GlobalTheory.MomOne.EllBdd.bdd_hat_of_ell | (intros; apply GlobalTheory.MomOne.EllBdd.bdd_hat_of_ell <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRegularRepBesselBigCellVectorEqBesselStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regularRep_besselBigCellVector_eq_bessel : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ), D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → ∃ γ ∈ JF.Om P.k P.r p.T.base.z p.T.base.z', Formalism.QuantumDeterminants.Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN (TBB.bigPt P.r c) (P.r + 1) ∧ ∀ F : B.Mat P.k P.r → (Wq →L[ℂ] Wp), p.V F (TBB.bigPt P.r c) = B.JF p.T.base F γ := by
  first | exact @GlobalTheory.exists_regular_rep_vec_bigPt_eq_bessel | exact GlobalTheory.exists_regular_rep_vec_bigPt_eq_bessel | (intros; apply GlobalTheory.exists_regular_rep_vec_bigPt_eq_bessel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUnitCoeffMulSeriesLeNormStatement
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_coeff_mul_series_le_norm : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (β : ℂ) (N : ℕ), M.Chart ℓ → β ≠ 0 → (∀ l ∈ M.L.lattice, β * l ∈ M.L.lattice) → (N : ℂ) = β * conj β → Bd 1 (hat M.ι ℓ (fun z => M.u (β * z))) → ∃ n ≤ N, ‖coeff n (hat M.ι ℓ (fun z => M.u (β * z)))‖ = 1 := by
  first | exact @GlobalTheory.MomOne.MulDegree.exists_unit_coeff | exact GlobalTheory.MomOne.MulDegree.exists_unit_coeff | (intros; apply GlobalTheory.MomOne.MulDegree.exists_unit_coeff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordOperatorColumnMemNormalFormProductSpanStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wordOperator_column_mem_normalFormProductSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ w : List (Letter ℂ S), admitted st w → ∀ e : Ix S, ((ofWord L st w).F * TL.bTA L w) e e1 ∈ nfSpan d (hats d.L) w.length 0 w.length := by
  first | exact @GlobalTheory.HatNF.word_mem_nfSpan | exact GlobalTheory.HatNF.word_mem_nfSpan | (intros; apply GlobalTheory.HatNF.word_mem_nfSpan <;> assumption)
end

