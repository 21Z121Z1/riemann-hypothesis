import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0157
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0158
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0073

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMRealInv
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def JDRInvFnM : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Y : ℂ) (p : B.SS k r), D.inSS p →
    ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ((r + k : ℕ) : ℕ∞) (B.GV k r) F →
      ∀ g ∈ B.GPos D, rvhatOp k r D.z D.z' Y (B.rho D p F) g = B.rho D p (rvhatOp k r D.z D.z' Y F) g

section poly

open Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

variable {k r : ℕ}

theorem rim_herm (v w : Fin (2 * r + k + 1) → ℂ) :
    U.IsPolyDeg 1 (fun g : Q.Mx k r => herm (Hpk k r) (g *ᵥ v) w) := by
  have e : (fun g : Q.Mx k r => herm (Hpk k r) (g *ᵥ v) w) =
      fun g => ∑ a, star (w a) * ∑ b, Hpk k r a b * ∑ c, g b c * v c := by
    funext g
    simp only [herm, Matrix.mulVec, dotProduct, Pi.star_apply]
  rw [e]
  exact pd_sum _ fun a _ => ri_mul_left _ (pd_sum _ fun b _ => ri_mul_left _
    (pd_sum _ fun c _ => ri_mul_right (pd_entry b c) _))

theorem rim_rowV (z : Fin (2 * r + k + 1) → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) (p q : Fin (2 * r + k + 1)) :
    U.IsPolyDeg 1 (fun g => rowV k r z g J p q) := by
  unfold rowV
  by_cases h : p.val < r
  · simp only [dif_pos h]
    exact rim_herm _ _
  · by_cases h2 : p.val = r
    · simp only [dif_neg h, dif_pos h2]
      exact rim_herm _ _
    · simp only [dif_neg h, dif_neg h2]
      exact pd_const _ 1

theorem rim_alJ (z : Fin (2 * r + k + 1) → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) :
    U.IsPolyDeg (2 * r + k + 1) (fun g => alJ k r z g J) :=
  pd_det (fun g => Matrix.of fun p q => rowV k r z g J p q) fun a b => by
    simpa only [Matrix.of_apply] using rim_rowV z J a b

end poly

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def rimCat {ι : Type} (Θs : ι → B.DiffOp k r Wp Wq) : List ι → B.DiffOp k r Wp Wq
  | [] => []
  | i :: l => Θs i ++ rimCat Θs l

theorem rimCat_poly {ι : Type} {Θs : ι → B.DiffOp k r Wp Wq} {t κ : ℕ} (h : ∀ i, PolyOp t κ (Θs i)) :
    ∀ l, PolyOp t κ (rimCat Θs l)
  | [] => fun T hT => absurd hT List.not_mem_nil
  | i :: l => QMinOp.polyOp_append (h i) (rimCat_poly h l)

theorem rimCat_apply {ι : Type} (Θs : ι → B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    ∀ l, B.opApply (rimCat Θs l) F g = (l.map fun i => B.opApply (Θs i) F g).sum
  | [] => by simp [rimCat, B.opApply]
  | i :: l => by rw [rimCat, QMinOp.opApply_append, rimCat_apply Θs F g l, List.map_cons, List.sum_cons]

theorem rimCat_order {ι : Type} {Θs : ι → B.DiffOp k r Wp Wq} {t κ : ℕ} (h : ∀ i, PolyOp t κ (Θs i))
    (ho : ∀ i, B.opOrder (Θs i) = t) (i : ι) (l : List ι) :
    B.opOrder (rimCat Θs (i :: l)) = t := by
  rw [rimCat, QMinOp.opOrder_append, ho i]
  exact max_eq_left (ri_order_le _ (rimCat_poly h l))

theorem residue_rows_strict_mono : StrictMono (rowsR k r 0) := by
  intro a b h
  have h' : a.val < b.val := h
  show (rowsR k r 0 a).val < (rowsR k r 0 b).val
  simp only [rowsR]
  split_ifs <;> omega

theorem rim_mem : rowsR k r 0 ∈ jSetR k r := by
  classical
  simp only [jSetR, Finset.mem_filter, Finset.mem_univ, true_and]
  convert (residue_rows_strict_mono (k := k) (r := r))

theorem rim_real (z z' : Fin (2 * r + k + 1) → ℂ) (Y ε : ℂ) :
    ∃ Θ : B.DiffOp k r Wp Wq, PolyOp (r + k) (2 * r + k + 1) Θ ∧ B.opOrder Θ = r + k ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ((r + k : ℕ) : ℕ∞) UU F →
        ∀ g ∈ UU, g ∈ B.GV k r → B.opApply Θ F g = ε • rvhatOp k r z z' Y F g := by
  have h : ∀ x : Fin (k + 1) × (Fin (r + k) → Fin (2 * r + k + 1)),
      ∃ Θ : B.DiffOp k r Wp Wq, PolyOp (r + k) (2 * r + k + 1) Θ ∧ B.opOrder Θ = r + k ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ((r + k : ℕ) : ℕ∞) UU F →
        ∀ g ∈ UU, g ∈ B.GV k r → B.opApply Θ F g = ∑ j ∈ ({()} : Finset Unit),
          (fun (_ : Unit) (g : B.Mat k r) =>
            ε * (((-1 : ℂ) ^ (x.1 : ℕ)) * z' (wI k r x.1) * alJ k r z g x.2)) j g •
            qminorOp (Q.EH k r) x.2 ((fun (_ : Unit) => colsV k r x.1) j) (Q.uC k r (Fin.last r) Y - 1) F g := fun x =>
    QMinOp.qminOpRep {()} x.2 (fun _ => colsV k r x.1) _
      (fun _ _ => ri_mul_left _ (ri_mul_left _ (rim_alJ z x.2))) _
  choose Θs hP hO hR using h
  let idx : List (Fin (k + 1) × (Fin (r + k) → Fin (2 * r + k + 1))) :=
    ((Finset.univ : Finset (Fin (k + 1))) ×ˢ jSetR k r).toList
  have hmem : ((0 : Fin (k + 1)), rowsR k r 0) ∈ idx := by
    simp only [idx, Finset.mem_toList, Finset.mem_product, Finset.mem_univ, true_and]
    exact rim_mem
  refine ⟨rimCat Θs idx, rimCat_poly hP _, ?_, ?_⟩
  · obtain ⟨i, l, hl⟩ : ∃ i l, idx = i :: l := by
      cases h' : idx with
      | nil => rw [h'] at hmem; exact absurd hmem List.not_mem_nil
      | cons i l => exact ⟨i, l, rfl⟩
    rw [hl]
    exact rimCat_order hP hO _ _
  · intro UU F hF g hgU hg
    rw [rimCat_apply]
    simp only [idx]
    rw [Finset.sum_map_toList, Finset.sum_product]
    simp only [rvhatOp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [hR (t, J) UU F hF g hgU hg, Finset.sum_singleton, smul_smul]

end ops

theorem jDRRealInvM_of_inv (hI : JDRInvFnM) : JDRRealInvM := by
  intro ε Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨Θ, hP, hO, hR⟩ := rim_real (Wp := Wp (S.pl v)) (Wq := Wq (S.pl v)) (T v).base.z (T v).base.z' (y : ℂ) ε
  have hn : 0 < 2 * S.G.r + S.G.k + 1 := by omega
  refine ⟨Θ, QMinOp.polyOp_mono hP (by omega) (Nat.le_mul_of_pos_left _ (by omega)), ?_, ?_⟩
  · intro p hp F hF g hg
    rw [hO] at hF
    have hgG : g ∈ B.GV S.G.k S.G.r := hg.1
    have hsg : B.sgs p g ∈ B.GV S.G.k S.G.r := Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group (T v).base hp hgG
    rw [hR _ _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho (T v).base hp hF) g hgG hgG]
    have e2 : B.rho (T v).base p (B.opApply Θ F) g =
        B.rho (T v).base p (fun x => ε • rvhatOp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) F x) g := by
      simp only [B.rho]
      rw [hR _ _ hF _ hsg hsg]
    rw [e2, hI S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base (y : ℂ) p hp F hF g hg]
    simp only [B.rho, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  · intro U F hU hF g hg
    have hgG : g ∈ B.GV S.G.k S.G.r := by simpa [Q.Glev] using hg.1
    refine hR (Q.Glev S.G.k S.G.r 0 ∩ U) F ?_ g hg hgG
    intro g₀ hg₀
    obtain ⟨U', F', hU', hg₀U, hc, he⟩ := hF g₀ hg₀
    refine ⟨U', F', hU', hg₀U, hc.of_le (by exact_mod_cast le_top), fun x hx hxG => he x hx ?_⟩
    simpa [Q.Glev] using hxG

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPTop
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix

noncomputable section

section

variable {k r : ℕ}

theorem unipotent_fixes_anisotropic_vector (l : Fin r) (c : ℂ) (v : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v) : Q.w1 k r l c *ᵥ v = v := by
  have hsum : v = ∑ q, v q • bvec q := by
    funext p
    simp [bvec, Finset.sum_apply, Pi.single_apply]
  rw [hsum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Matrix.mulVec_smul]
  by_cases h1 : q = eI k r l
  · have : v q = 0 := hv q (Or.inl (by rw [h1]; simp [eI]))
    rw [this, zero_smul, zero_smul]
  by_cases h2 : q = esI k r l
  · have : v q = 0 := hv q (Or.inr (by rw [h2]; simp [esI]; omega))
    rw [this, zero_smul, zero_smul]
  rw [Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector l c h1 h2]

theorem top_wlist_wb (c : Fin r → ℂ) (L : List (Fin r)) (v : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v) :
    (L.map fun a => Q.w1 k r a (c a)).prod *ᵥ v = v := by
  induction L with
  | nil => simp
  | cons a L ih => rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih, unipotent_fixes_anisotropic_vector a _ v hv]

theorem inv_wCell_last_mul_mulVec_of_inWb {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r))
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    (Q.wCell k r (Fin.last r) c * g)⁻¹ *ᵥ z = g⁻¹ *ᵥ z := by
  have hW : Q.wCell k r (Fin.last r) c ∈ Q.Glev k r 0 := Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _
  have hgu : IsUnit g.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg.1
  have hu : IsUnit (Q.wCell k r (Fin.last r) c * g).det := by
    rw [Matrix.det_mul]
    exact (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hW.1).mul hgu
  have hv : (Q.wCell k r (Fin.last r) c * g) *ᵥ (g⁻¹ *ᵥ z) = z := by
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z g, Matrix.mul_nonsing_inv _ hgu, Matrix.one_mulVec]
    exact top_wlist_wb c _ z hz
  conv_lhs => rw [← hv]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

theorem top_qminor_cast {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n t t' : ℕ}
    (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (h : t = t') (a b : Fin t' → Fin n) (u : ℂ) :
    qminorOp Eop (a ∘ Fin.cast h) (b ∘ Fin.cast h) u = qminorOp Eop a b u := by
  subst h
  rfl

theorem top_chatL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {t : ℕ} (h : t = k + 1)
    (pos : Fin t → Fin (2 * r + k + 1)) (hpos : ∀ j, (pos j).val = r + j.val) (u : ℂ)
    (a β : Q.Mx k r → Fin t → ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    Q.chatL (Q.EH k r) pos u a β f g = ∑ s : Fin (k + 1), ∑ t' : Fin (k + 1),
      (((-1 : ℂ) ^ ((s : ℕ) + (t' : ℕ))) * β g (Fin.cast h.symm s) * a g (Fin.cast h.symm t')) •
        qminorOp (Q.EH k r) (rowsN k r (Fin.last r) s) (rowsN k r (Fin.last r) t') u f g := by
  subst h
  unfold Q.chatL
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t' _ => ?_
  have hc : k + 1 - 1 = r - (Fin.last r).val + k := by simp
  have e : ∀ i : Fin (k + 1), pos ∘ Q.skip1 i = rowsN k r (Fin.last r) i ∘ Fin.cast hc := by
    intro i
    funext j
    apply Fin.ext
    simp only [Function.comp_apply, Q.skip1, rowsN, Fin.val_last, Fin.val_cast]
    split_ifs <;> simp_all <;> omega
  rw [e s, e t', top_qminor_cast]
  rfl

end

theorem residue_top_holds : JDRTop := by
  intro Wp Wq _ _ _ _ k r z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
  have hm : Q.mdim k r (Fin.last r) = k + 1 := by simp [Q.mdim]
  have hpos : ∀ j, (Q.posL k r (Fin.last r) j).val = r + j.val := fun j => by
    simp [Q.posL]; omega
  simp only [FN, Q.resG, Q.QL, Q.grp, Q.tL, Pi.neg_apply, neg_neg]
  have e1 : Q.resG k r (Fin.last r) J c =
      ((∏ a : Fin r, (if a.val < (Fin.last r).val then ‖c a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ) •
        (fun g' => J (Q.wCell k r (Fin.last r) c * g')) := rfl
  rw [e1, Formalism.FourierDecayAlt.P5.chatL_smulC, Pi.smul_apply]
  congr 1
  rw [top_chatL hm _ hpos]
  unfold NL
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian, inv_wCell_last_mul_mulVec_of_inWb hc hg hz]
  congr 2
  · congr 1
    simp only [Q.xbv, fvec]
    congr 1
    · congr 1; apply Fin.ext; simp [Q.posL, wI]; omega
    · simp
  · simp only [Q.yv, fvec]
    congr 2
    · simp
    · apply Fin.ext; simp [Q.posL, wI]; omega

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH2
section
open MeasureTheory
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section defs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

def cc (j : ℕ) (hj : j + 1 ≤ P.r) (t : ℂ) (c : Fin (P.r - (j + 1)) → ℂ) : Fin (P.r - j) → ℂ :=
  fun l => consC t c (Fin.cast (by omega) l)

def gi (j : ℕ) (hj : j + 1 ≤ P.r) (g : Mx P.k (P.r - (j + 1))) : Mx P.k (P.r - j) :=
  D.castM (by omega) (ιLev P.k 1 (P.r - (j + 1)) g)

def GoodFam (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)) : Prop :=
  (∀ t₀ : ℂ, t₀ ≠ 0 → ∀ γ₀ ∈ B.GV P.k (P.r - (j + 1)), ∃ (U : Set (ℂ × B.Mat P.k (P.r - (j + 1))))
      (f : ℂ × B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)), IsOpen U ∧ (t₀, γ₀) ∈ U ∧ ContDiffOn ℝ ∞ f U ∧
      ∀ p ∈ U, p.2 ∈ B.GV P.k (P.r - (j + 1)) → G p.1 p.2 = f p) ∧
  ∀ K : Set ℂ, IsCompact K → (∀ t ∈ K, t ≠ 0) → ∃ C : Set (B.Mat P.k (P.r - (j + 1))), IsCompact C ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ K, ∀ γ, G t γ ≠ 0 → γ ∈ C ∧
      (γ ∈ B.GV P.k (P.r - (j + 1)) → ε ≤ Gf P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' γ)

def famP (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)) (v : ℂ) :
    ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp) :=
  fun t => (B.GV P.k (P.r - (j + 1))).indicator fun γ => fderiv ℝ (fun u : ℂ => G u γ) t v

def Rep (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r)
    (Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
    (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (cc j hj t x.1) (gi j hj x.2) =
      resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G t)) x.1 x.2

def InC (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r)
    (Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π') : Prop :=
  ∃ G, GoodFam T j G ∧ Rep T j hj Ψ G

def sliceFam (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r) (F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) :
    ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp) :=
  fun t => (B.GV P.k (P.r - (j + 1))).indicator fun γ =>
    ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) • ∫ xx : U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1)),
      (psi P.k (P.r - j) (T.bs j).z cStd (rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.1) *
          star (psi P.k (P.r - j) (T.bs j).z' cStd (rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.2))) •
        F ((rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.1)⁻¹ * mc (by omega : P.r - (j + 1) + 1 = P.r - j) t γ *
          rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.2)
      ∂((U.muRC P.k 1 (P.r - (j + 1))).prod (U.muRC P.k 1 (P.r - (j + 1))))

end defs

def FamJFOK : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)),
    GoodFam T j G → ∀ t : ℂ, t ≠ 0 → JFOKCpt (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (G t)

def FamAlg : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G G' : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)),
    GoodFam T j G → GoodFam T j G' → ∀ m : ℂ → ℂ, ContDiffOn ℝ ∞ m {t | t ≠ 0} →
      GoodFam T j (fun t γ => G t γ + G' t γ) ∧ GoodFam T j (fun t γ => m t • G t γ)

def FamDeriv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)),
    GoodFam T j G → ∀ v : ℂ, GoodFam T j (famP j G v)

def RepLin : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ), j + 1 ≤ P.r →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ (G G' : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)), GoodFam T j G → GoodFam T j G' →
    ∀ t : ℂ, t ≠ 0 → ∀ (a : ℂ), ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
      resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (fun γ => G t γ + G' t γ)) x.1 x.2 =
          resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G t)) x.1 x.2 +
            resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G' t)) x.1 x.2 ∧
        resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (fun γ => a • G t γ)) x.1 x.2 =
          a • resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G t)) x.1 x.2

def FamJFDeriv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ), j + 1 ≤ P.r →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)), GoodFam T j G →
    ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z', ∀ v : ℂ,
      HasDerivAt (fun s : ℝ =>
          resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G (t + (s : ℂ) * v))) x.1 x.2)
        (resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (famP j G v t)) x.1 x.2) 0

def CellTie : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r),
    IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
      (cc j hj t x.1, gi j hj x.2) ∈ DomR P.k (P.r - j) (T.bs j).z (T.bs j).z' ∧
        wCell P.k (P.r - (j + 1)) (Fin.last _) x.1 * x.2 ∈ B.GV P.k (P.r - (j + 1)) ∧
        wCell P.k (P.r - (j + 1)) (Fin.last _) x.1 * x.2 ∈ OmPlus P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z'

def SliceFamGood : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r),
    IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp), JFOKCpt (JC.parLev P j) (T.bs j).z (T.bs j).z' F →
      GoodFam T j (sliceFam T j hj F)

def SliceFamJF : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r),
    IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp), JFOKCpt (JC.parLev P j) (T.bs j).z (T.bs j).z' F →
    ∀ t : ℂ, t ≠ 0 → ∀ γ ∈ B.GV P.k (P.r - (j + 1)),
      γ ∈ OmPlus P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' →
      B.JF (T.bs (j + 1)) (sliceFam T j hj F t) γ =
        ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) • B.JF (T.bs j) F (mc (by omega : P.r - (j + 1) + 1 = P.r - j) t γ)

def OpClosed : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r),
    IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ (X : ActualOps P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π') (i : Fin 6)
      (Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'),
      InC T j hj Ψ → InC T j hj (X.op ⟨0, by omega⟩ i Ψ)

def BTlAdjoin : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r : ℕ)
    (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r), IsActualLevel X L →
    ∀ (S : Type) [Fintype S] [DecidableEq S] (l : Fin r) (w : List (Wd.Letter ℂ S)) (a b : Wd.Ix S),
      (bTl L l w a b).1 ∈ Algebra.adjoin ℂ (Set.range (X.op l))

def UUiwScalar : Prop :=
  ∀ (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (S : Type) [Fintype S] [DecidableEq S] (s : ℂ)
    (w : List (Wd.Letter ℂ S)) (a b : Wd.Ix S), Wd.UUiw (A := A) s w a b ∈ (⊥ : Subalgebra ℂ A)

end Formalism.FourierDecayAlt.P.CutSH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevTransportU
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTie

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

def LevTransportU : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (Bs : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → Bs.z = z → Bs.z' = z' → Bs.π = π → Bs.π' = π' →
    ∀ (i : Fin (P.r + 1)),
    ∃ Tw : D.LevTower P.k P.r Wp Wq, D.TowerNormalised Tw ∧
      Tw.base.z = z ∧ Tw.base.z' = z' ∧ Tw.base.π = π ∧ Tw.base.π' = π' ∧
    ∃ (Di : B.RealPlaceData P.k (P.r - i) Wp Wq)
      (Xi : ActualOps (JC.parLev P i).k (JC.parLev P i).r Di.z Di.z' Di.π Di.π') (μi : Measure (Mt P.k (P.r - i)))
      (Li : R.LevelData (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π')) (P.r - i))
      (sti : Fr.Start (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π'))) (κ : ℝ),
      Di = Tw.bs i ∧ 0 < κ ∧ IsData (JC.parLev P i) Di.z Di.z' Di.π Di.π' Xi μi Li sti l0 ∧
      ∀ (c : Fin P.r → ℂ), (∀ l : Fin P.r, l.val < i.val → c l ≠ 0) →
      ∃ T : RadSp P.k P.r z z' π π' →ₗ[ℂ] RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π',
        LevTrClauses P μ L st l0 i c Di μi Li sti T ∧
        ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' = (κ : ℂ) * pairAt μ Φ Ψ (glue i c (shiftCf i c''))

end Formalism.FourierDecayAlt.P.PTie
end
end

