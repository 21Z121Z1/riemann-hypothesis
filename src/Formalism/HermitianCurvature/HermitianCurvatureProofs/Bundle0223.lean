import Formalism.HermitianCurvature.StatementHeads
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0214
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0215
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0192
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0010
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0055

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLift
section
open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem nice_mono {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {Bs : B.RealPlaceData k ρ Wp Wq} {ε ε' : ℝ} {F : B.Mat k ρ → (Wq →L[ℂ] Wp)}
    (h : JC.NiceCoef Bs ε F) (hε : ε' ≤ ε) : JC.NiceCoef Bs ε' F :=
  ⟨h.1, h.2.1, fun g hg hne => hε.trans (h.2.2 g hg hne)⟩

theorem poly_coeff_unique {V : Type} [AddCommGroup V] [Module ℂ V] (n : ℕ) (A B : Fin n → V)
    (h : ∀ y : ℝ, ∑ l : Fin n, ((y : ℂ) ^ (l : ℕ)) • A l = ∑ l : Fin n, ((y : ℂ) ^ (l : ℕ)) • B l) : A = B := by
  set τ : Fin n → ℂ := fun i => (((i : ℕ) : ℝ) : ℂ) with hτdef
  have hτ : Function.Injective τ := by
    intro a b hab
    simp only [hτdef, Complex.ofReal_inj, Nat.cast_inj] at hab
    exact Fin.ext hab
  have key : ∀ (C : Fin n → V) (l : Fin n),
      C l = ∑ i : Fin n, (Matrix.vandermonde τ)⁻¹ l i • ∑ m : Fin n, (τ i ^ (m : ℕ)) • C m := by
    intro C l
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    simp only [vand_row τ hτ l, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  funext l
  rw [key A l, key B l]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact h ((i : ℕ) : ℝ)

section lift

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem sum_pad {V : Type} [AddCommGroup V] [Module ℂ V] {d n : ℕ} (hdn : d ≤ n) (c : Fin (d + 1) → V) (y : ℂ) :
    ∑ m : Fin (d + 1), (y ^ (m : ℕ)) • c m =
      ∑ l : Fin (n + 1), (y ^ (l : ℕ)) • (if hl : (l : ℕ) ≤ d then c ⟨l, by omega⟩ else 0) := by
  classical
  have e := Finset.sum_map (Finset.univ : Finset (Fin (d + 1))) (Fin.castLEEmb (by omega : d + 1 ≤ n + 1))
    (fun l : Fin (n + 1) => (y ^ (l : ℕ)) • (if hl : (l : ℕ) ≤ d then c ⟨l, by omega⟩ else 0))
  symm
  rw [← Finset.sum_subset (Finset.subset_univ ((Finset.univ : Finset (Fin (d + 1))).map
    (Fin.castLEEmb (by omega : d + 1 ≤ n + 1)))) ?_, e]
  · apply Finset.sum_congr rfl
    intro m _
    simp only [Fin.castLEEmb_apply, Fin.val_castLE]
    rw [dif_pos (by omega)]
  · intro l _ hl
    rw [dif_neg, smul_zero]
    intro hle
    apply hl
    rw [Finset.mem_map]
    exact ⟨⟨l, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩

theorem reduceJ {k r : ℕ} (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (j s : ℕ) (hj : j ≤ r)
    (h : C.LPt) (τ : ℂ) (ha : D.ptSize (h ++ [(s, τ)]) = j) (hs : s ≤ j)
    (hSP : SlicePoly T F j hj (h ++ [(s, τ)]) ha) (hLD : LiftDeg T F j s hj h τ ha)
    (w' : List C.Letter) (hN : ∃ ε, ∀ a', JC.NiceCoef (T.bs j) ε (KB.slv T F j hj w' (h ++ [(s, τ)]) ha a'))
    (b : Bool) (δ : ℝ) :
    ∃ E : Fin (j + 1) → Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp),
      (∀ l, ∃ ε, ∀ a', JC.NiceCoef (T.bs j) ε (E l a')) ∧ (∀ l : Fin (j + 1), j - s < (l : ℕ) → E l = 0) ∧
      E ⟨j - s, by omega⟩ = cLift s τ b • KB.slv T F j hj w' (h ++ [(s, τ)]) ha ∧
      ∀ (y : ℝ) (a' : Wd.Ix (Fin w'.length)), ∀ g ∈ JF.Om k (r - j) (T.bs j).z (T.bs j).z',
        B.JF (T.bs j) (KB.slv T F j hj ((b, y + δ) :: w') (h ++ [(s, τ)]) ha (Fin.cons 1 a')) g =
          B.JF (T.bs j) ((∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • E l) a') g := by
  classical
  obtain ⟨C1, -, hC1n, hC1⟩ := hSP w' b δ 1
  obtain ⟨εN, hεN⟩ := hN
  set E : Fin (j + 1) → Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp) := fun l =>
    if (l : ℕ) < j - s then C1 l else if (l : ℕ) = j - s then cLift s τ b • KB.slv T F j hj w' (h ++ [(s, τ)]) ha
    else 0 with hE

  choose εC hεC using hC1n
  set ε0 : ℝ := min εN (Finset.univ.inf' Finset.univ_nonempty εC) with hε0
  have hC1n' : ∀ l a', JC.NiceCoef (T.bs j) ε0 (C1 l a') := fun l a' =>
    nice_mono (hεC l a') ((min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ l)))
  have hNn' : ∀ a', JC.NiceCoef (T.bs j) ε0 (KB.slv T F j hj w' (h ++ [(s, τ)]) ha a') := fun a' =>
    nice_mono (hεN a') (min_le_left _ _)
  have hEn : ∀ l a', JC.NiceCoef (T.bs j) ε0 (E l a') := by
    intro l a'
    simp only [hE]
    split_ifs
    · exact hC1n' l a'
    · exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (hNn' a')
    · exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero
  refine ⟨E, fun l => ⟨ε0, hEn l⟩, fun l hl => ?_, ?_, fun y a' g hg => ?_⟩
  · simp only [hE]; rw [if_neg (by omega), if_neg (by omega)]
  · simp only [hE]; rw [if_neg (by simp), if_pos (by simp)]
  ·
    have hsum : ∀ (y : ℝ) (V : Fin (j + 1) → Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp)),
        (∀ l, JC.NiceCoef (T.bs j) ε0 (V l a')) →
        B.JF (T.bs j) ((∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • V l) a') g =
          ∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • B.JF (T.bs j) (V l a') g := by
      intro y V hV
      have e1 : (∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • V l) a' = ∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • V l a' := by
        simp [Finset.sum_apply]
      rw [e1, Formalism.FourierDecayAlt.P.JCx2.bc_JF_sum Finset.univ (fun l : Fin (j + 1) => ((y : ℂ) ^ (l : ℕ)) • V l a')
        (fun l _ => Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (hV l)) hg]
      apply Finset.sum_congr rfl
      intro l _
      exact Formalism.FourierDecayAlt.P.JCx2.bc_JF_smul _ _ _
    have hgGV : g ∈ B.GV k (r - j) := hg.1

    have hL : ∀ y' : ℝ, B.JF (T.bs j) (KB.slv T F j hj ((b, y' + δ) :: w') (h ++ [(s, τ)]) ha (Fin.cons 1 a')) g =
        ∑ l : Fin (j + 1), ((y' : ℂ) ^ (l : ℕ)) • B.JF (T.bs j) (C1 l a') g := by
      intro y'
      rw [Formalism.FourierDecayAlt.P.JCx2.sq_jf_congr (T.bs j) (fun g' hg' => hC1 y' a' g' hg') hgGV]
      exact hsum y' C1 (fun l => hC1n' l a')
    obtain ⟨c, hcl, hcy⟩ := hLD w' a' b δ g hg
    have hcomp := poly_coeff_unique (j + 1) (fun l => B.JF (T.bs j) (C1 l a') g)
      (fun l => if hl : (l : ℕ) ≤ j - s then c ⟨l, by omega⟩ else 0) (fun y' => by
        rw [← hL y', hcy y', sum_pad (n := j) (by omega) c (y' : ℂ)])
    rw [hL y, hsum y E (fun l => hEn l a')]
    apply Finset.sum_congr rfl
    intro l _
    congr 1
    have hcl' := congrFun hcomp l
    by_cases h1 : (l : ℕ) < j - s
    · simp only [hE, if_pos h1]
    · rw [show B.JF (T.bs j) (C1 l a') g = _ from hcl']
      by_cases h2 : (l : ℕ) = j - s
      · simp only [hE, if_neg h1, if_pos h2]
        rw [dif_pos (by omega)]
        have e3 : (⟨(l : ℕ), by omega⟩ : Fin (j - s + 1)) = Fin.last (j - s) := Fin.ext (by simp [h2])
        rw [e3, hcl]
        exact (Formalism.FourierDecayAlt.P.JCx2.bc_JF_smul _ _ _).symm
      · simp only [hE, if_neg h1, if_neg h2]
        rw [dif_neg (by omega)]
        exact (Formalism.FourierDecayAlt.P.JCx2.bc_JF_zero g).symm

theorem nice_lincomb {k ρ : ℕ} {Bs : B.RealPlaceData k ρ Wp Wq} {S ι : Type} [Fintype S] [Fintype ι] [Nonempty ι]
    (V : ι → Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)) (hV : ∀ l, ∃ ε, ∀ a, JC.NiceCoef Bs ε (V l a)) (c : ι → ℂ) :
    ∃ ε, ∀ a, JC.NiceCoef Bs ε ((∑ l, c l • V l) a) := by
  classical
  choose ε hε using hV
  refine ⟨Finset.univ.inf' Finset.univ_nonempty ε, fun a => ?_⟩
  have e : (∑ l, c l • V l) a = fun g => ∑ l, c l • V l a g := by
    funext g; simp [Finset.sum_apply]
  rw [e]
  exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_sum Finset.univ (fun l g => c l • V l a g)
    (fun l _ => Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (nice_mono (hε l a) (Finset.inf'_le _ (Finset.mem_univ l))))

end lift

end Formalism.FourierDecayAlt.P.PBG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialRaisingTopOfParts
section
open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section loc

variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem pOp_locO (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → E} (h : ∀ c ∈ OmX r, f₁ c = f₂ c) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) : pOp l f₁ c = pOp l f₂ c := by
  have hev : f₁ =ᶠ[nhds c] f₂ := by
    filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc] with c' hc' using h c' hc'
  simp only [pOp, wirt, if_pos hc, hev.fderiv_eq]

theorem vAB_loc (Y : ℂ) : ∀ (i : ℕ) (f₁ f₂ : (Fin r → ℂ) → E), (∀ c ∈ OmX r, f₁ c = f₂ c) →
    ∀ c ∈ OmX r, (Q.vAB r Y i).1 f₁ c = (Q.vAB r Y i).1 f₂ c ∧ (Q.vAB r Y i).2 f₁ c = (Q.vAB r Y i).2 f₂ c
  | 0, f₁, f₂, h, c, hc => ⟨h c hc, rfl⟩
  | i + 1, f₁, f₂, h, c, hc => by
    have ih := vAB_loc Y i f₁ f₂ h
    by_cases hi : i < r
    · simp only [Q.vAB, dif_pos hi]
      refine ⟨?_, ?_⟩
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, cOp]
        rw [(ih c hc).1, (ih c hc).2, pOp_locO _ (fun c' hc' => (ih c' hc').1) hc]
      · simp only [ciOp]
        rw [(ih c hc).1]
    · simp only [Q.vAB, dif_neg hi]
      exact ih c hc

end loc

section jd

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem jf_dinv (Bs : B.RealPlaceData k r Wp Wq) (H : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.JF Bs (fun x => (Dmin k r Bs.z Bs.z' x (Fin.last _))⁻¹ • H x) g =
      (Dmin k r Bs.z Bs.z' g (Fin.last _))⁻¹ • B.JF Bs H g := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p (fun x => (Dmin k r Bs.z Bs.z' x (Fin.last _))⁻¹ • H x) g ∂Bs.μSS =
    (Dmin k r Bs.z Bs.z' g (Fin.last _))⁻¹ • ∫ p, JF.xiP Bs p • B.rho Bs p H g ∂Bs.μSS
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
  simp only [B.rho]
  rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]

end jd

end Formalism.FourierDecayAlt.P.PBN

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBN

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_raising_top_of_parts : PBN.RadAATopOfParts := by
  intro hJ hC hM hR hCp Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 y hD F hF
  refine ⟨hCp P.k P.r Wp Wq Bs F y hF, fun Φ hΦ x hx => ?_⟩
  have hL : Q.IsActualLevel X L := hD.2.2.1
  have hc0 : (∏ a, x.1 a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hx.1 a
  have hcell := Formalism.FourierDecayAlt.P.big_cell_values P.k P.r Wp Wq Bs x hx
  have hγ := Formalism.FourierDecayAlt.P.TLB.wCell_om Bs hx

  have e1 : (TL.aP L (y : ℂ)).1 Φ = (L.ζi).1 ((L.Ar (y : ℂ)).1 Φ) := rfl
  rw [e1, hL.2.2.2.2.2.2.2.1]
  show ((X.fn 1 ((L.Ar (y : ℂ)).1 Φ) : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = _
  rw [X.fn_apply 1 _ x hx, hR P.k P.r Bs.z Bs.z' Wp Wq Bs.π Bs.π' X L (y : ℂ) hL Φ x hx]
  have eΦ : Q.crd (Q.vAB P.r (y : ℂ) P.r).1 (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
      Q.crd (Q.vAB P.r (y : ℂ) P.r).1 (Q.resG P.k P.r (Fin.last P.r) (B.JF Bs F)) x.1 x.2 :=
    (vAB_loc (y : ℂ) P.r _ _ (fun c' hc' => hΦ (c', x.2) ⟨hc', hx.2⟩) x.1 hx.1).1
  rw [eΦ, ← hM P.k P.r Wp Wq Bs F (y : ℂ) hF x hx]

  simp only [Q.resG]
  have eJ : B.JF Bs (aaTop Bs y F) (Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2) =
      (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2)⁻¹ •
        qminorOp (EabH (Hpk P.k P.r)) (C3.xR P.k P.r P.r le_rfl) (C3.xR P.k P.r P.r le_rfl)
          ((y : ℂ) + ((2 * P.r + P.k : ℕ) : ℂ) / 2) (B.JF Bs F) (Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2) := by
    unfold aaTop
    rw [jf_dinv, hJ P.k P.r Wp Wq Bs F _ hF _ hγ, hC P.k P.r _ _ _ _ _ hx.2.1, hcell.2.2.1, smul_smul]
    congr 1
    rw [mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  rw [eJ, smul_comm]
  rfl

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RaisingCompactSupport
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.GaugeNormPower

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section closed

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem aa_closed (P : (Mat k r → E) → Prop)
    (hRd : ∀ (X : Mat k r) (f : Mat k r → E), inLie k r X → P f → P (RdV X f))
    (hadd : ∀ f₁ f₂ : Mat k r → E, P f₁ → P f₂ → P (fun x => f₁ x + f₂ x))
    (hmul : ∀ (φ : Mat k r → ℂ), ContDiff ℝ (⊤ : ℕ∞) φ → ∀ f : Mat k r → E, P f → P (fun x => φ x • f x))
    (hzero : P (fun _ => 0)) (m : ℕ) (hm : m ≤ r) (u : ℂ) (f : Mat k r → E) (hf : P f) :
    P (C3.AAop k r m hm u f) :=
  _root_.UpperTheory.Reformulated.B.Qj20.aa_closed P hRd hadd hmul hzero m hm u f hf

theorem loc_add' {m : ℕ∞} {f₁ f₂ : Mat k r → E} {g : Mat k r} (h₁ : Loc m f₁ g) (h₂ : Loc m f₂ g) :
    Loc m (fun x => f₁ x + f₂ x) g := by
  obtain ⟨U₁, f₁', hU₁, hg₁, hf₁, he₁⟩ := h₁
  obtain ⟨U₂, f₂', hU₂, hg₂, hf₂, he₂⟩ := h₂
  exact ⟨U₁ ∩ U₂, fun x => f₁' x + f₂' x, hU₁.inter hU₂, ⟨hg₁, hg₂⟩,
    (hf₁.mono Set.inter_subset_left).add (hf₂.mono Set.inter_subset_right),
    fun x hx hxG => by show f₁ x + f₂ x = f₁' x + f₂' x; rw [he₁ x hx.1 hxG, he₂ x hx.2 hxG]⟩

theorem loc_smulFun {m : ℕ∞} (φ : Mat k r → ℂ) {V : Set (Mat k r)} (hV : IsOpen V)
    (hφ : ContDiffOn ℝ (m : WithTop ℕ∞) φ V) {f : Mat k r → E} {g : Mat k r} (hgV : g ∈ V) (h : Loc m f g) :
    Loc m (fun x => φ x • f x) g := by
  obtain ⟨U, f', hU, hgU, hf, he⟩ := h
  exact ⟨U ∩ V, fun x => φ x • f' x, hU.inter hV, ⟨hgU, hgV⟩,
    (hφ.mono Set.inter_subset_right).smul (hf.mono Set.inter_subset_left),
    fun x hx hxG => by show φ x • f x = φ x • f' x; rw [he x hx.1 hxG]⟩

theorem loc_zero' {m : ℕ∞} {g : Mat k r} : Loc m (fun _ => (0 : E)) g :=
  ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

theorem loc_AAop {f : Mat k r → E} {g : Mat k r} (h : Loc ⊤ f g) (m : ℕ) (hm : m ≤ r) (u : ℂ) :
    Loc ⊤ (C3.AAop k r m hm u f) g := by
  refine aa_closed (fun f => Loc ⊤ f g) (fun X f hX hf => ?_) (fun _ _ h₁ h₂ => loc_add' h₁ h₂)
    (fun φ hφ f hf => loc_smulFun φ isOpen_univ hφ.contDiffOn (Set.mem_univ g) hf) loc_zero' m hm u f h
  have hf' : Loc ((⊤ : ℕ∞) + 1) f g := by rw [top_add]; exact hf
  exact loc_RdV hX hf'

theorem zero_AAop {f : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U) (h : ∀ x ∈ U, x ∈ GV k r → f x = 0)
    (m : ℕ) (hm : m ≤ r) (u : ℂ) : ∀ x ∈ U, x ∈ GV k r → C3.AAop k r m hm u f x = 0 := by
  refine aa_closed (fun f => ∀ x ∈ U, x ∈ GV k r → f x = 0) (fun X f hX hf => ?_)
    (fun f₁ f₂ h₁ h₂ x hx hxG => by simp [h₁ x hx hxG, h₂ x hx hxG])
    (fun φ _ f hf x hx hxG => by simp [hf x hx hxG]) (fun _ _ _ => rfl) m hm u f h
  intro x hx hxG
  rw [rdV_congr (f₂ := fun _ => (0 : E)) hU hx hxG hX (fun y hy hyG => hf y hy hyG)]
  simp [RdV]

end closed

end Formalism.FourierDecayAlt.P.GaugeNormPower

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.GaugeNormPower

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem raising_compact_support : PBN.AACpt := by
  intro k r Wp Wq _ _ _ _ Bs F y hF
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, hε, hG⟩⟩ := hF
  have hGc : Continuous fun g : Mat k r => Gf k r Bs.z Bs.z' g :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').continuous
  have hvan : ∀ U : Set (Mat k r), IsOpen U → (∀ x ∈ U, x ∈ GV k r → F x = 0) →
      ∀ x ∈ U, x ∈ GV k r → PBN.aaTop Bs y F x = 0 := by
    intro U hU hF0 x hx hxG
    have := zero_AAop hU hF0 r le_rfl ((y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) x hx hxG
    simp only [PBN.aaTop, this, smul_zero]
  have hUε : IsOpen {x : Mat k r | Gf k r Bs.z Bs.z' x < ε} := isOpen_lt hGc continuous_const
  have hFε : ∀ x ∈ {x : Mat k r | Gf k r Bs.z Bs.z' x < ε}, x ∈ GV k r → F x = 0 := by
    intro x hx hxG
    by_contra h
    exact absurd (hG x hxG h) (not_le.mpr hx)
  refine ⟨?_, ⟨R, ?_⟩, ⟨ε, hε, ?_⟩⟩
  · intro g₀ hg₀
    by_cases hlt : Gf k r Bs.z Bs.z' g₀ < ε
    · exact ⟨_, fun _ => 0, hUε, hlt, contDiffOn_const, fun x hx hxG => hvan _ hUε hFε x hx hxG⟩
    · push Not at hlt
      have hD : Dmin k r Bs.z Bs.z' g₀ (Fin.last (r + 1)) ≠ 0 := by
        intro h0
        have h1 : 0 ≤ Tz k r Bs.z * Tz k r Bs.z' * Complex.normSq (Dmin k r Bs.z Bs.z' g₀ ⟨r, by omega⟩) :=
          mul_nonneg (mul_pos Bs.T_pos Bs.T'_pos).le (Complex.normSq_nonneg _)
        simp only [Gf, h0, map_zero] at hlt
        linarith
      have hDc : ContDiff ℝ (⊤ : ℕ∞) fun x : Mat k r => Dmin k r Bs.z Bs.z' x (Fin.last (r + 1)) :=
        Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin Bs.z Bs.z' _
      have hV : IsOpen {x : Mat k r | Dmin k r Bs.z Bs.z' x (Fin.last (r + 1)) ≠ 0} :=
        isOpen_ne_fun hDc.continuous continuous_const
      have hloc : Loc ⊤ (C3.AAop k r r le_rfl ((y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) F) g₀ :=
        loc_AAop (hs g₀ hg₀) r le_rfl _
      exact loc_smulFun (fun x => (Dmin k r Bs.z Bs.z' x (Fin.last (r + 1)))⁻¹) hV
        (hDc.contDiffOn.inv fun x hx => hx) hD hloc
  · intro g hg hne
    by_contra hgt
    push Not at hgt
    have hU : IsOpen {x : Mat k r | R < gN x} := isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous
    refine hne (hvan _ hU (fun x hx hxG => ?_) g hgt hg)
    by_contra h
    exact absurd (hR x hxG h) (not_le.mpr hx)
  · intro g hg hne
    by_contra hlt
    push Not at hlt
    exact hne (hvan _ hUε hFε g hlt hg)

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeActionHolds
section
open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace RightTypeActionHermitianCurvature

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)} {i : Fin (r + 1)} {mm : ℕ∞}

theorem mem_right (hD : IsDom k r z z' i D) {g h : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (hh : h ∈ UWset k r z') : g * h ∈ Glev k r i ∩ D := by
  have := Qx8.dom_mem hD hg (Qx8.uw_one z) (Qx8.nlev_one _) hh (Qx8.nlev_one _)
  simpa using this

theorem J_right (hπ' : IsCRepOn (UWset k r z') π') (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D) {g h : Mx k r}
    (hg : g ∈ Glev k r i ∩ D) (hh : h ∈ UWset k r z') : J (g * h) = (J g).comp (π' h) := by
  have e1 := hJ.2.2.2 g hg 1 (Qx8.uw_one z) 1 (Qx8.uw_one z')
  have e2 := hJ.2.2.2 g hg 1 (Qx8.uw_one z) h hh
  rw [Matrix.one_mul, Matrix.mul_one, hπ'.1] at e1
  rw [Matrix.one_mul] at e2
  have e3 : (J g).comp (1 : Wq →L[ℂ] Wq) = J g := ContinuousLinearMap.comp_id _
  rw [e3] at e1
  rw [e2, ← ContinuousLinearMap.comp_assoc, ← e1]

theorem rd_right (hD : IsDom k r z z' i D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wq →L[ℂ] Wq}
    (hF : ∀ g ∈ Glev k r i ∩ D, F g = (J g).comp B) {X : Mx k r} (hX : QrD.InLieW k r z' X)
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : RdV X F g = (J g).comp ((QrD.dOp π' X).comp B) := by
  have h := QrD.dOp_hasDeriv hπ' hc hX
  let L : (Wq →L[ℂ] Wq) →L[ℂ] (Wq →L[ℂ] Wp) :=
    (ContinuousLinearMap.compL ℂ Wq Wq Wp (J g)).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wq).flip B)
  have h2 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have h3 : (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) =
      (L.restrictScalars ℝ) ∘ fun t : ℝ => π' (NormedSpace.exp ((t : ℂ) • X)) := by
    funext t
    rw [hF _ (mem_right hD hg (QrD.exp_uw hX t)), J_right hπ' hJ hg (QrD.exp_uw hX t)]
    rfl
  unfold RdV
  rw [h3]
  exact h2.deriv

theorem rz_right (hD : IsDom k r z z' i D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wq →L[ℂ] Wq}
    (hF : ∀ g ∈ Glev k r i ∩ D, F g = (J g).comp B) {Z : Mx k r}
    (h1 : QrD.InLieW k r z' (hpart1 (Hpk k r) Z)) (h2 : QrD.InLieW k r z' (hpart2 (Hpk k r) Z))
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    RZ (Hpk k r) Z F g = (J g).comp ((QrD.ecOp π' Z).comp B) := by
  unfold RZ QrD.ecOp
  rw [rd_right hD hπ' hc hJ hF h1 hg, rd_right hD hπ' hc hJ hF h2 hg]
  ext v
  simp

theorem fold_right (hD : IsDom k r z z' i D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    (L : List (ℂ × Mx k r))
    (hL : ∀ p ∈ L, QrD.InLieW k r z' (hpart1 (Hpk k r) p.2) ∧ QrD.InLieW k r z' (hpart2 (Hpk k r) p.2)) :
    ∃ B : Wq →L[ℂ] Wq,
      (∀ g ∈ Glev k r i ∩ D,
        (L.map fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + RZ (Hpk k r) p.2 y).foldr (fun T h => T h) J g =
          (J g).comp B) ∧
      ∀ v, B v = (L.map fun p => fun y : Wq => p.1 • y + EcRep (Hpk k r) π' p.2 y).foldr (fun T h => T h) v := by
  induction L with
  | nil => exact ⟨1, fun g _ => (ContinuousLinearMap.comp_id _).symm, fun v => rfl⟩
  | cons p L ih =>
    obtain ⟨B, hB1, hB2⟩ := ih fun q hq => hL q (by simp [hq])
    have hp := hL p (by simp)
    refine ⟨p.1 • B + (QrD.ecOp π' p.2).comp B, fun g hg => ?_, fun v => ?_⟩
    · simp only [List.map_cons, List.foldr_cons, Pi.add_apply, Pi.smul_apply]
      rw [rz_right hD hπ' hc hJ hB1 hp.1 hp.2 hg, hB1 g hg]
      ext v
      simp
    · simp only [List.map_cons, List.foldr_cons]
      rw [← hB2 v, QrD.ecRep_eq hπ' hc hp.1 hp.2]
      rfl

end RightTypeActionHermitianCurvature

theorem right_type_action_holds : RightTypeAction0 := by
  intro Wp Wq _ _ _ _ _ k r m z z' π π' D mm _ _ hD hπ' hc J hJ g hg Bs hB w v
  unfold capR capRep qmF
  simp only [Finset.sum_apply, Pi.smul_apply, _root_.sum_apply, _root_.smul_apply,
    map_sum, map_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  obtain ⟨B, hB1, hB2⟩ := RightTypeActionHermitianCurvature.fold_right hD hπ' hc hJ
    (List.ofFn fun j : Fin m => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0 : ℂ), unitB (Hpk k r) Bs (σ j) j))
    (by
      intro p hp
      rw [List.mem_ofFn] at hp
      obtain ⟨j, rfl⟩ := hp
      exact QrD.frame_lie hB (σ j) j)
  have e1 := hB1 g hg
  have e2 := hB2 v
  simp only [List.map_ofFn, Function.comp_def, ite_smul, zero_smul] at e1 e2
  simp only [id]
  rw [e1, ← e2]
  rfl

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
end

