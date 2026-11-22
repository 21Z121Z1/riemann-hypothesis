import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0160
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0164
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0201
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0257
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHFamJFDeriv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0275
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RdVZeroOfVanish
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0277
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0278
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0276
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0273
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0265

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHOpClosed
section
open scoped ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section opc

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem opc_cc_zero (j : ℕ) (hj : j + 1 ≤ P.r) (t : ℂ) (c : Fin (P.r - (j + 1)) → ℂ) :
    cc (P := P) j hj t c ⟨0, by omega⟩ = t := by
  unfold cc consC
  simp

theorem opc_cc_line (j : ℕ) (hj : j + 1 ≤ P.r) (t v : ℂ) (s : ℝ) (c : Fin (P.r - (j + 1)) → ℂ) :
    cc (P := P) j hj (t + (s : ℂ) * v) c =
      cc (P := P) j hj t c + s • (Pi.single (⟨0, by omega⟩ : Fin (P.r - j)) v : Fin (P.r - j) → ℂ) := by
  funext l
  unfold cc consC
  by_cases hl : (l : ℕ) = 0
  · have e : l = ⟨0, by omega⟩ := Fin.ext hl
    simp [hl, Pi.single_apply, e, Complex.real_smul]
  · have hne : l ≠ ⟨0, by omega⟩ := fun h => hl (by rw [h])
    simp [hl, Pi.single_apply, hne]

theorem opc_mul (h2 : FamAlg) (h4 : RepLin) {T : D.LevTower P.k P.r Wp Wq}
    (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π') (hT : D.TowerNormalised T) {j : ℕ} {hj : j + 1 ≤ P.r}
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    {Ψ Ψ' : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
    {G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)} (hG : GoodFam T j G) (hR : Rep T j hj Ψ G)
    (m : ℂ → ℂ) (hm : ContDiffOn ℝ ∞ m {t | t ≠ 0})
    (hv : ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
      (Ψ' : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (cc j hj t x.1) (gi j hj x.2) =
        m t • (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (cc j hj t x.1) (gi j hj x.2)) :
    InC T j hj Ψ' := by
  refine ⟨fun t γ => m t • G t γ, (h2 Wp Wq P T j G G hG hG m hm).2, fun t ht x hx => ?_⟩
  rw [hv t ht x hx, hR t ht x hx]
  exact (h4 Wp Wq P T hP hT j hj hPs G G hG hG t ht (m t) x hx).2.symm

theorem opc_two (h2 : FamAlg) (h3 : FamDeriv) (h4 : RepLin) {T : D.LevTower P.k P.r Wp Wq}
    (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π') (hT : D.TowerNormalised T) {j : ℕ} {hj : j + 1 ≤ P.r}
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    {Ψ' : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
    {G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)} (hG : GoodFam T j G)
    (m1 m2 : ℂ → ℂ) (hm1 : ContDiffOn ℝ ∞ m1 {t | t ≠ 0}) (hm2 : ContDiffOn ℝ ∞ m2 {t | t ≠ 0}) (v1 v2 : ℂ)
    (hv : ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
      (Ψ' : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (cc j hj t x.1) (gi j hj x.2) =
        m1 t • resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (famP j G v1 t)) x.1 x.2 +
        m2 t • resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (famP j G v2 t)) x.1 x.2) :
    InC T j hj Ψ' := by
  have hd1 := h3 Wp Wq P T j G hG v1
  have hd2 := h3 Wp Wq P T j G hG v2
  have hA : GoodFam T j (fun t γ => m1 t • famP j G v1 t γ) := (h2 Wp Wq P T j _ _ hd1 hd1 m1 hm1).2
  have hB : GoodFam T j (fun t γ => m2 t • famP j G v2 t γ) := (h2 Wp Wq P T j _ _ hd2 hd2 m2 hm2).2
  refine ⟨fun t γ => m1 t • famP j G v1 t γ + m2 t • famP j G v2 t γ,
    (h2 Wp Wq P T j _ _ hA hB (fun _ => 1) contDiffOn_const).1, fun t ht x hx => ?_⟩
  have e0 := (h4 Wp Wq P T hP hT j hj hPs _ _ hA hB t ht 0 x hx).1
  have e1 := (h4 Wp Wq P T hP hT j hj hPs _ _ hd1 hd1 t ht (m1 t) x hx).2
  have e2 := (h4 Wp Wq P T hP hT j hj hPs _ _ hd2 hd2 t ht (m2 t) x hx).2
  rw [hv t ht x hx, ← e1, ← e2]
  exact e0.symm

theorem opc_fderiv (h5 : FamJFDeriv) (h6 : CellTie) (T : D.LevTower P.k P.r Wp Wq)
    (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π') (hT : D.TowerNormalised T) (j : ℕ) (hj : j + 1 ≤ P.r)
    (hPj : IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    (Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)) (hG : GoodFam T j G) (hR : Rep T j hj Ψ G)
    (t : ℂ) (ht : t ≠ 0) (x : (Fin (P.r - (j + 1)) → ℂ) × Mx P.k (P.r - (j + 1)))
    (hx : x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z') (v : ℂ) :
    fderiv ℝ (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2)) (cc j hj t x.1)
        (Pi.single (⟨0, by omega⟩ : Fin (P.r - j)) v) =
      resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (famP j G v t)) x.1 x.2 := by
  have hy := (h6 Wp Wq P T hP hT j hj hPj hPs t ht x hx).1
  obtain ⟨-, hs, -⟩ := Ψ.2
  obtain ⟨U, F, hU, hyU, hF, hΨF⟩ := hs _ hy
  have hg : gi j hj x.2 ∈ Glev P.k (P.r - j) (Fin.last _) := hy.2.1
  have hemb : Continuous fun c' : Fin (P.r - j) → ℂ => (c', gi j hj x.2) :=
    continuous_id.prodMk continuous_const
  have hev : (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2)) =ᶠ[𝓝 (cc j hj t x.1)]
      fun c' => F (c', gi j hj x.2) := by
    have hU' : ∀ᶠ c' in 𝓝 (cc j hj t x.1), (c', gi j hj x.2) ∈ U :=
      hemb.continuousAt.preimage_mem_nhds (hU.mem_nhds hyU)
    filter_upwards [hU'] with c' hc'
    exact hΨF (c', gi j hj x.2) hc' hg
  have hFd : DifferentiableAt ℝ (fun c' => F (c', gi j hj x.2)) (cc j hj t x.1) :=
    ((hF.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)).comp (cc j hj t x.1)
      (differentiableAt_id.prodMk (differentiableAt_const _))
  have hφ := (hFd.congr_of_eventuallyEq hev).hasFDerivAt
  have hφ' : HasFDerivAt (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (fderiv ℝ (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2)) (cc j hj t x.1))
      (cc j hj t x.1 + (0 : ℝ) • (Pi.single (⟨0, by omega⟩ : Fin (P.r - j)) v : Fin (P.r - j) → ℂ)) := by
    rw [zero_smul, add_zero]; exact hφ
  have hline := ((hasDerivAt_id (0 : ℝ)).smul_const
    (Pi.single (⟨0, by omega⟩ : Fin (P.r - j)) v : Fin (P.r - j) → ℂ)).const_add (cc j hj t x.1)
  rw [one_smul] at hline
  have hcomp := hφ'.comp_hasDerivAt (0 : ℝ) hline
  have hJ := h5 Wp Wq P T hP hT j hj hPs G hG t ht x hx v
  have hc : Continuous fun s : ℝ => t + (s : ℂ) * v :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hne : ∀ᶠ s : ℝ in 𝓝 0, t + (s : ℂ) * v ≠ 0 :=
    hc.continuousAt.eventually_ne (by simpa using ht)
  have heq : ((fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2)) ∘
      fun s : ℝ => cc j hj t x.1 + id s • (Pi.single (⟨0, by omega⟩ : Fin (P.r - j)) v : Fin (P.r - j) → ℂ))
      =ᶠ[𝓝 0] fun s : ℝ =>
        resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G (t + (s : ℂ) * v))) x.1 x.2 := by
    filter_upwards [hne] with s hs
    simp only [Function.comp, id]
    rw [← opc_cc_line]
    exact hR _ hs x hx
  exact hcomp.unique (hJ.congr_of_eventuallyEq heq)

end opc

theorem cutSH_opClosed_of (h2 : FamAlg) (h3 : FamDeriv) (h4 : RepLin) (h5 : FamJFDeriv) (h6 : CellTie) :
    OpClosed := by
  intro Wp Wq _ _ _ _ _ _ P T hP hT j hj hPj hPs X i Ψ hΨ
  obtain ⟨G, hG, hR⟩ := hΨ
  have hom : ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
      cc j hj t x.1 ∈ OmX (P.r - j) := fun t ht x hx => (h6 Wp Wq P T hP hT j hj hPj hPs t ht x hx).1.1
  have hD := fun v t ht x hx => opc_fderiv h5 h6 T hP hT j hj hPj hPs Ψ G hG hR t ht x hx v
  have hid : ContDiff ℝ ∞ (fun t : ℂ => t) := contDiff_id
  have hst : ContDiff ℝ ∞ (fun t : ℂ => star t) := Complex.conjCLE.contDiff
  fin_cases i
  · refine opc_two h2 h3 h4 hP hT hPs hG (fun t => t / 2) (fun t => -(t * Complex.I / 2))
      (hid.div_const 2).contDiffOn ((hid.mul contDiff_const).div_const 2).neg.contDiffOn 1 Complex.I
      (fun t ht x hx => ?_)
    rw [X.op_apply]
    change pOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold pOp
    rw [if_pos (hom t ht x hx), opc_cc_zero]
    unfold wirt
    rw [hD 1 t ht x hx, hD Complex.I t ht x hx]
    module
  · refine opc_mul h2 h4 hP hT hPs hG hR (fun t => t) hid.contDiffOn (fun t ht x hx => ?_)
    rw [X.op_apply]
    change cOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold cOp
    rw [opc_cc_zero]
  · refine opc_mul h2 h4 hP hT hPs hG hR (fun t => t⁻¹) (hid.contDiffOn.inv fun t ht => ht)
      (fun t ht x hx => ?_)
    rw [X.op_apply]
    change ciOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold ciOp
    rw [opc_cc_zero]
  · refine opc_two h2 h3 h4 hP hT hPs hG (fun t => star t / 2) (fun t => star t * Complex.I / 2)
      (hst.div_const 2).contDiffOn ((hst.mul contDiff_const).div_const 2).contDiffOn 1 Complex.I
      (fun t ht x hx => ?_)
    rw [X.op_apply]
    change pbOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold pbOp
    rw [if_pos (hom t ht x hx), opc_cc_zero]
    unfold wirtBar
    rw [hD 1 t ht x hx, hD Complex.I t ht x hx]
    module
  · refine opc_mul h2 h4 hP hT hPs hG hR (fun t => star t) hst.contDiffOn (fun t ht x hx => ?_)
    rw [X.op_apply]
    change cbOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold cbOp
    rw [opc_cc_zero]
  · refine opc_mul h2 h4 hP hT hPs hG hR (fun t => (star t)⁻¹)
      (hst.contDiffOn.inv fun t ht => star_ne_zero.mpr ht) (fun t ht x hx => ?_)
    rw [X.op_apply]
    change cbiOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold cbiOp
    rw [opc_cc_zero]

end Formalism.FourierDecayAlt.P.CutSH

theorem Formalism.FourierDecayAlt.P.cutSH_opClosed_of (h2 : Formalism.FourierDecayAlt.P.CutSH.FamAlg) (h3 : Formalism.FourierDecayAlt.P.CutSH.FamDeriv)
    (h4 : Formalism.FourierDecayAlt.P.CutSH.RepLin) (h5 : Formalism.FourierDecayAlt.P.CutSH.FamJFDeriv) (h6 : Formalism.FourierDecayAlt.P.CutSH.CellTie) :
    Formalism.FourierDecayAlt.P.CutSH.OpClosed :=
  Formalism.FourierDecayAlt.P.CutSH.cutSH_opClosed_of h2 h3 h4 h5 h6

theorem Formalism.FourierDecayAlt.P.cutSH_opClosed_of_famJFDeriv (h5 : Formalism.FourierDecayAlt.P.CutSH.FamJFDeriv) : Formalism.FourierDecayAlt.P.CutSH.OpClosed :=
  Formalism.FourierDecayAlt.P.CutSH.cutSH_opClosed_of Formalism.FourierDecayAlt.P.CutSH.family_algebraic Formalism.FourierDecayAlt.P.family_derivative
    Formalism.FourierDecayAlt.P.CutSH.representation_linear h5 Formalism.FourierDecayAlt.P.CutSH.cell_compatibility

theorem Formalism.FourierDecayAlt.P.operator_class_closed : Formalism.FourierDecayAlt.P.CutSH.OpClosed :=
  Formalism.FourierDecayAlt.P.cutSH_opClosed_of_famJFDeriv Formalism.FourierDecayAlt.P.family_orbital_derivative_identity
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DetLowW
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBQ

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem kr_agree {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (l : Fin (r + 2)) (a : ℂ) (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp))
    (hH : ∀ g ∈ B.GV k r, Dmin k r Bs.z Bs.z' g l = a → H₁ g = H₂ g) (y : B.Mat k r) (hy : y ∈ B.GV k r)
    (hya : Dmin k r Bs.z Bs.z' y l = a) : PBG.Kr Bs H₁ y = PBG.Kr Bs H₂ y := by
  unfold PBG.Kr
  refine integral_congr_ae ?_
  filter_upwards [PBG.ae_inR Bs] with ξ hξ
  have hg : y * Matrix.of ξ.2 * Matrix.of ξ.1 ∈ B.GV k r :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hy hξ.2.1) hξ.1.1
  rw [hH _ hg (by rw [PBG.dmin_pR Bs hξ y l, hya])]

theorem pbT_agree (P : M.Par) (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r) (a : ℂ)
    (H₁ H₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hH : ∀ g ∈ B.GV P.k P.r, Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = a → H₁ g = H₂ g)
    (g : B.Mat P.k P.r) (hg : g ∈ B.GV P.k P.r)
    (hga : Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = a) :
    pbT p j (by omega) H₁ g = pbT p j (by omega) H₂ g := by
  unfold pbT
  have e : j + (P.r - j) = P.r := by omega
  rw [PartialBesselProperness.pbF_eq_TI, PartialBesselProperness.pbF_eq_TI]
  unfold PartialBesselProperness.TI
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [PartialBesselProperness.gI]
  split_ifs with hx
  · have hs : PartialBesselProperness.sE (p.T.bs j) e x ∈ Sset P.k P.r p.T.base.z := by
      have := PartialBesselProperness.sE_mem_S (p.T.bs j) e x
      rwa [p.T.z_lev j (by omega)] at this
    have hyG : PartialBesselProperness.sE (p.T.bs j) e x * g ∈ B.GV P.k P.r := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (PartialBesselProperness.sE_GV _ e x) hg
    have hyD : Dmin P.k P.r p.T.base.z p.T.base.z' (PartialBesselProperness.sE (p.T.bs j) e x * g) ⟨j + 1, by omega⟩ = a := by
      have := Formalism.QuantumDeterminants.diagonal_inverse_holds P.k P.r p.T.base.z p.T.base.z' p.T.base.z_mem p.T.base.z'_mem _ hs 1
        (Formalism.FourierDecayAlt.P.PBG.one_mem_Sset P.k P.r _) g ⟨j + 1, by omega⟩
      rw [Matrix.mul_one] at this
      rw [this, hga]
    rw [kr_agree p.T.base ⟨j + 1, by omega⟩ a H₁ H₂ hH _ hyG hyD]
  · rfl

def aVal (h : C.LPt) (t : ℂ) : ℂ := (U.hMat (D.ptPerm h) (D.ptDiag h)).det * t

def CutOffStep : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))),
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → γ ∈ B.GV P.k (P.r - (j + 1)) →
    γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length)) (Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
    KB.CptCoef p.T.base Fc →
    (∀ g, Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = aVal h t →
      Fc g = D.uwG P.k P.r p.T.base.z p.T.base.z' F (j + 1) hj w e g) →
    B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e) γ =
      B.JF (p.T.bs j) (KB.slv p.T Fc j (by omega) [] h hh.2 fun a => a.elim0) (mLev P j hj t γ)

def CutOffExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j),
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∀ (t : ℂ), D.IsLocPt (h ++ [(1, t)]) (j + 1) → ∀ e : Wd.Ix (Fin w.length),
    ∃ Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base Fc ∧
      ∀ g, Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = aVal h t →
        Fc g = D.uwG P.k P.r p.T.base.z p.T.base.z' F (j + 1) hj w e g

theorem det_lowW {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : (U.lowW σ v).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [U.lowW]
  · intro a b hab
    simp only [U.lowW, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
    have hab' : a < b := hab
    rw [if_neg (ne_of_lt hab'), dif_neg (fun h => absurd h.1 (not_lt.mpr hab'.le)), add_zero]

theorem zxH_det (h : C.LPt) (j : ℕ) (hh : D.IsLocPt h j) (v : XH h) :
    (zxH h j hh.2 v).det = (U.hMat (D.ptPerm h) (D.ptDiag h)).det := by
  have hH : (U.hMat (D.ptPerm h) (D.ptDiag h)).det ≠ 0 :=
    Formalism.FourierDecayAlt.P.PBM.hMat_det_ne _ _ (CutHB.ptDiag_ne hh)
  have hw : IsUnit (U.wP (D.ptPerm h)) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro h0
    apply hH
    rw [U.hMat, Matrix.det_mul, h0, zero_mul]
  unfold zxH LeftFubiniLemmas.lhOf
  rw [Matrix.det_reindex_self, Matrix.det_mul, Matrix.det_conj hw, det_lowW, one_mul]

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LettersPassPartialBessel
section
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselProperness

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section congr

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem pbF_congr_D (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (hzS : B0.z = D.castV e (liftVec k p ρ Bj.z)) (i : ℕ) (hi : i ≤ n) {c0 : ℂ} {r : ℝ}
    {H1 H2 : B.Mat k n → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ B.GV k n, dist (Dmin k n B0.z B0.z' g ⟨i, by omega⟩) c0 < r → H1 g = H2 g)
    {y : B.Mat k n} (hy : y ∈ B.GV k n) (hyD : dist (Dmin k n B0.z B0.z' y ⟨i, by omega⟩) c0 < r) :
    PBQ.pbF Bj B0 e H1 y = PBQ.pbF Bj B0 e H2 y := by
  rw [pbF_eq_TI, pbF_eq_TI]
  unfold TI
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : PBQ.GoodP Bj x
  · simp only [gI, if_pos hx]
    congr 2
    have hs : sE Bj e x ∈ Sset k n B0.z := hzS ▸ sE_mem_S Bj e x
    have hs1 : (1 : B.Mat k n) ∈ Sset k n B0.z' := Formalism.FourierDecayAlt.P.PBG.one_mem_Sset k n B0.z'
    have hmem : sE Bj e x * y ∈ B.GV k n := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (sE_GV Bj e x) hy
    have hD : Dmin k n B0.z B0.z' (sE Bj e x * y) ⟨i, by omega⟩ = Dmin k n B0.z B0.z' y ⟨i, by omega⟩ := by
      have := Formalism.QuantumDeterminants.diagonal_inverse_holds k n B0.z B0.z' B0.z_mem B0.z'_mem _ hs 1 hs1 y ⟨i, by omega⟩
      rwa [Matrix.mul_one] at this
    unfold PBG.Kr
    refine integral_congr_ae ?_
    filter_upwards [Formalism.FourierDecayAlt.P.PBG.ae_inR B0] with ξ hξ
    have hG : sE Bj e x * y * Matrix.of ξ.2 * Matrix.of ξ.1 ∈ B.GV k n :=
      Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hmem hξ.2.1) hξ.1.1
    rw [h _ hG (by rw [Formalism.FourierDecayAlt.P.PBG.dmin_pR B0 hξ, hD]; exact hyD)]
  · simp [gI, hx]

end congr

section words

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem pbWords_core (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (hzS : B0.z = D.castV e (liftVec k p ρ Bj.z)) (i : ℕ) (hi : i ≤ n) (H : B.Mat k n → (Wq →L[ℂ] Wp))
    (Cs : Set (B.Mat k n))
    (hL : ∀ g ∈ B.GV k n, Dmin k n B0.z B0.z' g ⟨i, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc ⊤ H g)
    (hCs : IsCompact Cs) (hS : ∀ g ∈ B.GV k n, g ∉ Cs → H g = 0) (U : Set (B.Mat k n)) (hU : IsOpen U)
    (hD : ∀ g ∈ U, Dmin k n B0.z B0.z' g ⟨i, by omega⟩ ≠ 0) (hP : Proper Bj B0 e Cs U) :
    ∀ (w : List C.Letter) (ew : Wd.Ix (Fin w.length)), ∀ y ∈ U, y ∈ B.GV k n →
      D.uwG k n B0.z B0.z' (PBQ.pbF Bj B0 e H) i hi w ew y =
        PBQ.pbF Bj B0 e (D.uwG k n B0.z B0.z' H i hi w ew) y
  | [], _, _, _, _ => rfl
  | l :: w, ew, y, hyU, hy => by
    have ih := pbWords_core Bj B0 e hzS i hi H Cs hL hCs hS U hU hD hP w (fun a => ew a.succ)
    set H' := D.uwG k n B0.z B0.z' H i hi w (fun a => ew a.succ) with hH'
    obtain ⟨hL', hS'⟩ := uwG_locSupp B0.z B0.z' i hi hCs.isClosed hL hS w (fun a => ew a.succ)
    set c0 := Dmin k n B0.z B0.z' y ⟨i, by omega⟩ with hc0
    have hc0ne : c0 ≠ 0 := hD y hyU
    obtain ⟨Ht, hHt, hHtS, hHtE⟩ := cutoff_exists B0.z B0.z' i hi hL' hS' hc0ne
    have hDc : Continuous (fun g : B.Mat k n => Dmin k n B0.z B0.z' g ⟨i, by omega⟩) :=
      (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin B0.z B0.z' ⟨i, by omega⟩).continuous
    set W0 := {g : B.Mat k n | dist (Dmin k n B0.z B0.z' g ⟨i, by omega⟩) c0 < ‖c0‖ / 4} with hW0
    have hW0o : IsOpen W0 := isOpen_lt (hDc.dist continuous_const) continuous_const
    have hyW0 : y ∈ W0 := by
      show dist c0 c0 < ‖c0‖ / 4
      rw [dist_self]; have := norm_pos_iff.mpr hc0ne; positivity
    have hV0o : IsOpen (U ∩ W0) := hU.inter hW0o

    have e1 : ∀ g ∈ U ∩ W0, g ∈ B.GV k n →
        D.uwG k n B0.z B0.z' (PBQ.pbF Bj B0 e H) i hi w (fun a => ew a.succ) g = PBQ.pbF Bj B0 e Ht g := by
      intro g hg hgG
      rw [ih g hg.1 hgG]
      exact pbF_congr_D Bj B0 e hzS i hi (fun g' hg' hd => (hHtE g' hg' hd).symm) hgG hg.2
    have hvK : VanishL Bj e (PBG.Kr B0 Ht) U := vanish_kr Bj B0 e hHtS hP
    show D.vLet k n B0.z B0.z' i hi l (ew 0) (D.uwG k n B0.z B0.z' (PBQ.pbF Bj B0 e H) i hi w fun a => ew a.succ) y =
      PBQ.pbF Bj B0 e (D.vLet k n B0.z B0.z' i hi l (ew 0) H') y
    rw [Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts.vLet_congr B0.z B0.z' i hi l (ew 0) hV0o e1 y ⟨hyU, hyW0⟩ hy,
      vLet_pb Bj B0 e hzS hHt hCs hHtS hU hvK i hi l (ew 0) hyU hy hc0ne]
    refine pbF_congr_D Bj B0 e hzS i hi (r := ‖c0‖ / 4) (c0 := c0) (fun g hg hd => ?_) hy hyW0
    exact Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts.vLet_congr B0.z B0.z' i hi l (ew 0) hW0o (fun g' hg' hg'G => hHtE g' hg'G hg') g hd hg

end words

theorem _root_.Formalism.FourierDecayAlt.P.letters_pass_partial_bessel : PbWords := by
  intro k p ρ n Wp Wq _ _ _ _ _ _ Bj B0 e hzS i hi H Cs hL hCs hS U hU hD hP w ew y hyU hy
  exact pbWords_core Bj B0 e hzS i hi H Cs hL hCs hS U hU hD hP w ew y hyU hy

end Formalism.FourierDecayAlt.P.PartialBesselProperness
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceTopZero
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXSl0

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem om_zero {k ρ : ℕ} (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (γ : B.Mat k ρ) (hγ : γ ∈ B.GV k ρ)
    (hG : 0 < Q.GGl k ρ z z' γ) : γ ∈ JF.Om k ρ z z' := by
  subst hρ
  refine ⟨hγ, fun l hl => ?_, ?_⟩
  · have hl0 : l = (⟨0, by norm_num⟩ : Fin (0 + 2)) := Fin.ext (by simp only; omega)
    subst hl0
    unfold Dmin
    rw [Matrix.det_fin_zero]
    exact one_ne_zero
  · have e : Gf k 0 z z' γ = Q.GGl k 0 z z' γ := by
      unfold Gf Q.GGl Dmin
      rw [Matrix.det_fin_zero, Matrix.det_fin_one]
      simp only [Complex.normSq_one, mul_one]
      rfl
    rw [e]
    exact hG

theorem sliceTop_zero (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (hr : P.r = 0) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hG : CutEX.TopCls p.T.base G)
    (h : C.LPt) (hh : D.IsLocPt h P.r) (γ : B.Mat P.k (P.r - P.r)) (hγ : γ ∈ B.GV P.k (P.r - P.r))
    (hGG : 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ) :
    Integrable (fun v : PBQ.XH h => PBQ.ellH h v (CutEX.pbTop p G (PBQ.zxH h P.r hh.2 v) γ)) ∧
      B.JF (p.T.bs P.r) (D.castF (by rw [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) γ =
        ∫ v, PBQ.ellH h v (CutEX.pbTop p G (PBQ.zxH h P.r hh.2 v) γ) := by
  have hOm := om_zero (by omega : P.r - P.r = 0) _ _ γ hγ hGG
  rcases P with ⟨k, r, T, T', u, u'⟩
  dsimp only at hr
  subst hr
  have hnil : h = [] := by
    cases h with
    | nil => rfl
    | cons b t =>
      exfalso
      have h1 := (hh.1 b (List.mem_cons.2 (Or.inl rfl))).1
      have h2 := hh.2
      simp only [D.ptSize, List.map_cons, List.sum_cons] at h2
      omega
  subst hnil
  have hE : IsEmpty (U.LW (D.ptPerm ([] : C.LPt))) := ⟨fun q => Fin.elim0 (q.1.1 : Fin 0)⟩
  set x₀ : PBQ.XH ([] : C.LPt) := fun q => (hE.false q).elim with hx₀
  have hvol : (volume : Measure (PBQ.XH ([] : C.LPt))) = Measure.dirac x₀ := by
    rw [volume_pi, Measure.pi_of_empty (fun _ => volume) x₀]
  have hxe : ∀ v : PBQ.XH ([] : C.LPt), v = x₀ := fun v => funext fun q => (hE.false q).elim
  refine ⟨?_, ?_⟩
  · rw [hvol]
    refine (integrable_const (PBQ.ellH ([] : C.LPt) x₀ (CutEX.pbTop p G (PBQ.zxH [] _ hh.2 x₀) γ))).congr
      (Filter.Eventually.of_forall fun v => ?_)
    simp only [hxe v]
  · have hone : ∫ v, PBQ.ellH ([] : C.LPt) v (CutEX.pbTop p G (PBQ.zxH [] _ hh.2 v) γ) =
        CutEX.pbTop p G (PBQ.zxH [] _ hh.2 x₀) γ := by
      rw [hvol, integral_dirac]
      unfold PBQ.ellH
      have hF0 : IsEmpty (Fin (D.ptSize ([] : C.LPt))) := ⟨fun i => Fin.elim0 (i : Fin 0)⟩
      have hs : U.subS (LeftFubiniLemmas.lhOf (D.ptPerm ([] : C.LPt)) x₀) = 0 := by
        unfold U.subS
        exact Finset.sum_of_isEmpty _
      rw [hs]
      simp [Formalism.FourierDecayAlt.G.psi]
    rw [hone]
    have e3 : D.castF (by simp) (D.sliceAt k 0 p.T.base.z p.T.base.z' G []) = G := by
      funext y
      simp only [D.castF]
      refine (Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil k 0 _ _ p.T.base.z_mem p.T.base.z'_mem G _).trans ?_
      exact congrArg G (Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl y)
    have hCpt : KB.CptCoef (p.T.bs 0) G := hG.1
    have hL := SliceIntegralLemmas.jf_left (p.T.bs 0) G (Formalism.FourierDecayAlt.P.PBH.asm_contOn_of_ckOn hCpt.1) γ hγ
      (Formalism.FourierDecayAlt.P.PBH.rhs_int (p.T.bs 0) G hCpt γ hOm)
    have hx : CutEX.xT k 0 (PBQ.zxH [] _ hh.2 x₀) γ = γ := by
      unfold CutEX.xT U.mMap
      rw [SliceIntegralLemmas.block_three_zero_size_eq]
      exact Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl γ
    rw [e3, hL]
    unfold CutEX.pbTop PBQ.pbT
    rw [hx, SliceIntegralLemmas.pbF_zero]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    beta_reduce
    rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
    rfl

end Formalism.FourierDecayAlt.P.CutEXSl0
end
end

