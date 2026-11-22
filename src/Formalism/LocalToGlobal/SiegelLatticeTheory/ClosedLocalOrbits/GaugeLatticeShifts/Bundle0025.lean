import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0022
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPfB

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfJ
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
open PI.ScalarPairDr.W (mem_orth hT_swap orth_orth fvec_castSucc fvec_last mem_orth_Xplus hT_smul_left)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Scal

variable {D : D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}

theorem span_left_le (F : LFlag (VS D) D.R.rS T) (F₁ : LFlag (VS D) D.R.rS T') :
    Submodule.span D.host.E (Set.range F.fl.fvec) ≤
      Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec F₁.fl.fvec)) :=
  Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inl a, rfl⟩)

theorem span_right_le (F : LFlag (VS D) D.R.rS T) (F₁ : LFlag (VS D) D.R.rS T') :
    Submodule.span D.host.E (Set.range F₁.fl.fvec) ≤
      Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec F₁.fl.fvec)) :=
  Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inr a, rfl⟩)

theorem Xsp_le_span (F : LFlag (VS D) D.R.rS T) :
    Xsp F ≤ Submodule.span D.host.E (Set.range F.fl.fvec) := by
  rw [Xsp, FlagG.X, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a.castSucc, fvec_castSucc _ _⟩

theorem Xsp_eq_Xs (F : LFlag (VS D) D.R.rS T) : Xsp F = Xs (S := VS D) F.fl.fvec := (Xs_fvec F.fl).symm

theorem z_mem_span (F : LFlag (VS D) D.R.rS T) :
    F.fl.z ∈ Submodule.span D.host.E (Set.range F.fl.fvec) :=
  Submodule.subset_span ⟨Fin.last _, fvec_last _⟩

theorem Gom'_mem (u v : Fin (D.R.rS + 1) → (VS D).V) : Gom' u v ∈ Submodule.span D.host.E (Set.range v) :=
  Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem Gom_mem (u v : Fin (D.R.rS + 1) → (VS D).V) : Gom u v ∈ Submodule.span D.host.E (Set.range u) :=
  Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem scal_dir (F : LFlag (VS D) D.R.rS T) (F₁ F₂ : LFlag (VS D) D.R.rS T')
    (hz : F.zt = F.fl.z) (hz₁ : F₁.zt = F₁.fl.z) (hz₂ : F₂.zt = F₂.fl.z) (hT0 : T ≠ 0)
    (hU2 : UUE Λ F F₂ = Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec F₂.fl.fvec)))
    (htr : ∀ y ∈ UUE Λ F F₂, y ∈ orth (VS D) (Xplus F) → y ∈ UUE Λ F F₁)
    (hsc : ∀ y, y ∈ Ylift Λ F F₁ → y ∈ Ylift Λ F F₂ → ∀ α α', SgRel F F₂ y 0 α α' → SgRel F F₁ y 0 α α')
    (hind : LinearIndependent D.host.E F₁.fl.fvec)
    (hD1 : GDl F.fl.fvec F₁.fl.fvec (D.R.rS + 1) ≠ 0) :
    (∃ x ∈ Xsp F, GDl F.fl.fvec F₂.fl.fvec (D.R.rS + 1) • Gom' F.fl.fvec F₁.fl.fvec =
      GDl F.fl.fvec F₁.fl.fvec (D.R.rS + 1) • (Gom' F.fl.fvec F₂.fl.fvec - x)) ∧
    GDl F.fl.fvec F₁.fl.fvec (D.R.rS + 1) * GDl F.fl.fvec F₂.fl.fvec D.R.rS =
      GDl F.fl.fvec F₂.fl.fvec (D.R.rS + 1) * GDl F.fl.fvec F₁.fl.fvec D.R.rS := by
  set f := F.fl.fvec with hf
  set f1 := F₁.fl.fvec with hf1
  set f2 := F₂.fl.fvec with hf2
  set D1 := GDl f f1 (D.R.rS + 1) with hD1def
  set D2 := GDl f f2 (D.R.rS + 1) with hD2def
  set R1 := GDl f f1 D.R.rS with hR1def
  set R2 := GDl f f2 D.R.rS with hR2def
  set om1 := Gom' f f1 with hom1
  set om2 := Gom' f f2 with hom2
  have hfl : f (Fin.last _) = F.fl.z := fvec_last _
  have hfc : ∀ a : Fin D.R.rS, f a.castSucc = F.fl.e a := fun a => fvec_castSucc _ a
  have p1 : ∀ a, (VS D).hT (f a) om1 = if a = Fin.last _ then D1 else 0 := om'_pair f f1
  have p2 : ∀ a, (VS D).hT (f a) om2 = if a = Fin.last _ then D2 else 0 := om'_pair f f2
  have hzz : (VS D).hT F.fl.z F.fl.z = -T := F.fl.z_norm
  set u2 := om2 + (D2 / T) • F.fl.z with hu2
  have hu2U : u2 ∈ UUE Λ F F₂ := by
    rw [hU2]
    exact Submodule.add_mem _ (span_right_le F F₂ (Gom'_mem f f2))
      (Submodule.smul_mem _ _ (span_left_le F F₂ (z_mem_span F)))
  have hu2o : u2 ∈ orth (VS D) (Xplus F) := by
    rw [Xplus, mem_orth_Xplus]
    refine ⟨fun a => ?_, ?_⟩
    · have h1 := p2 a.castSucc
      rw [if_neg (Fin.castSucc_ne_last a), hfc] at h1
      rw [hu2, map_add, map_smul, h1, F.fl.z_orth a, smul_zero, add_zero]
    · have h1 := p2 (Fin.last _)
      rw [if_pos rfl, hfl] at h1
      rw [hu2, map_add, map_smul, h1, hzz, smul_eq_mul]
      field_simp
      ring
  have hu2U1 := htr u2 hu2U hu2o
  have hx2 : om2 - R2 • F₂.fl.z ∈ Xsp F₂ := by
    rw [Xsp_eq_Xs, ← fvec_last F₂.fl]
    exact om'_decomp f f2
  have hsg : SgRel F F₂ u2 0 (D2 / T) R2 :=
    ⟨0, Submodule.zero_mem _, om2 - R2 • F₂.fl.z, hx2, by rw [hz, hz₂, hu2]; abel⟩
  obtain ⟨x, hx, x1, hx1, heq⟩ := hsc u2 (Submodule.mem_inf.2 ⟨hu2U1, hu2o⟩)
    (Submodule.mem_inf.2 ⟨hu2U, hu2o⟩) _ _ hsg
  rw [hz, hz₁, hu2, sub_zero] at heq
  have hp : R2 • F₁.fl.z + x1 = om2 - x := by
    have : om2 - x = (om2 + (D2 / T) • F.fl.z) - (D2 / T) • F.fl.z - x := by abel
    rw [this, heq]
    abel
  have hpspan : om2 - x ∈ Submodule.span D.host.E (Set.range f1) := by
    rw [← hp]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (z_mem_span F₁)) (Xsp_le_span F₁ hx1)
  have hxX : x ∈ F.fl.X := hx
  have hq0 : D1 • (om2 - x) - D2 • om1 = 0 := by
    refine lemB f f1 hD1 (Submodule.sub_mem _ (Submodule.smul_mem _ _ hpspan)
      (Submodule.smul_mem _ _ (Gom'_mem f f1))) fun a => ?_
    rw [map_sub, map_smul, map_smul, map_sub, p1, p2, smul_eq_mul, smul_eq_mul]
    induction a using Fin.lastCases with
    | last =>
      rw [if_pos rfl, if_pos rfl, hfl, hT_z_X F.fl hxX]
      ring
    | cast a =>
      rw [if_neg (Fin.castSucc_ne_last a), if_neg (Fin.castSucc_ne_last a), hfc,
        hT_X_X F.fl (Submodule.subset_span ⟨a, rfl⟩) hxX]
      ring
  refine ⟨⟨x, hx, (sub_eq_zero.1 hq0).symm⟩, ?_⟩
  have hy1 : om1 - R1 • f1 (Fin.last _) ∈ Xs (S := VS D) f1 := om'_decomp f f1
  have hx1' : x1 ∈ Xs (S := VS D) f1 := by rw [← Xsp_eq_Xs]; exact hx1
  have hlast1 : f1 (Fin.last _) = F₁.fl.z := fvec_last _
  have e : (D1 * R2 - D2 * R1) • f1 (Fin.last _) =
      D2 • (om1 - R1 • f1 (Fin.last _)) - D1 • x1 + (D1 • (om2 - x) - D2 • om1) := by
    rw [← hp, hlast1]
    module
  rw [hq0, add_zero] at e
  have hmem : (D1 * R2 - D2 * R1) • f1 (Fin.last _) ∈ Xs (S := VS D) f1 := by
    rw [e]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hy1) (Submodule.smul_mem _ _ hx1')
  have hc := lemC f1 hind hmem
  linear_combination hc

end Scal

end Formalism.L2.SG.Pf.ScalarFramePf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPfC
section
noncomputable section

open Matrix Formalism.MainNotions.S
open scoped ComplexOrder

namespace Formalism.L2.SG.RealObj.InfCut.PtRepPf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ}

theorem uMat_mul_inv (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by simp [uMat]

theorem eN_single (i0 : Fin k) (z : ℂ) : eN (Pi.single i0 z) = ‖z‖ := by
  unfold eN
  rw [Finset.sum_eq_single i0 (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same,
    Real.sqrt_sq (norm_nonneg _)]

theorem single_last_smul (L : Fin (r + 1)) (d : ℂ) : Pi.single L d = d • Pi.single L (1 : ℂ) := by
  funext j
  by_cases hj : j = L
  · subst hj; simp
  · simp [hj]

theorem realize (A B : Fr ε r k) (i0 : Fin k) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hZ : IsUnit Z.det)
    (σ : ℝ) (hσ2 : σ ^ 2 = (A.T)⁻¹ - B.T * ‖(Z⁻¹ *ᵥ Pi.single (Fin.last r) 1) (Fin.last r)‖ ^ 2) :
    ∃ g : Formalism.REAL.UJ ε, ∃ y : Fin (r + 1) → Fin n → ℂ, ∃ t : Fin (r + 1) → ℂ,
      t ⬝ᵥ (Z⁻¹ *ᵥ Pi.single (Fin.last r) 1) = σ ∧
      (∀ b, uMat g *ᵥ fam B.e B.z b = y b) ∧ (∀ i, i ≠ i0 → uMat g *ᵥ B.wb i = A.wb i) ∧
      (∀ a b, hJ ε (fam A.e A.z a) (y b) = Z a b) ∧
      (∀ i b, hJ ε (A.wb i) (y b) = if i = i0 then t b else 0) := by
  classical
  set L := Fin.last r with hL
  set c := Z⁻¹ *ᵥ Pi.single L 1 with hcdef
  have hZc : Z *ᵥ c = Pi.single L 1 := by rw [hcdef, mulVec_mulVec, mul_nonsing_inv _ hZ, one_mulVec]
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, mulVec_zero] at hZc
    have := congrFun hZc L
    simp at this
  obtain ⟨N, hNdef⟩ : ∃ N : ℂ, N = star c ⬝ᵥ c := ⟨_, rfl⟩
  have hN : N ≠ 0 := by rw [hNdef]; exact fun h => hc0 (dotProduct_star_self_eq_zero.1 h)
  obtain ⟨t, htdef⟩ : ∃ t : Fin (r + 1) → ℂ, t = ((σ : ℂ) / N) • star c := ⟨_, rfl⟩
  have htc : t ⬝ᵥ c = σ := by rw [htdef, smul_dotProduct, smul_eq_mul, ← hNdef, div_mul_cancel₀ _ hN]
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ,
      Γ = Matrix.of fun b c' => if b = L then (if c' = L then -(B.T : ℂ) else 0) else 0 := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ,
      Q = Γ + ((A.T : ℂ)⁻¹) • vecMulVec (star (Z L)) (Z L) - vecMulVec (star t) t := ⟨_, rfl⟩
  have hAstar : star ((A.T : ℂ)⁻¹) = (A.T : ℂ)⁻¹ := by rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hBstar : star (-(B.T : ℂ)) = -(B.T : ℂ) := by rw [star_neg, Complex.star_def, Complex.conj_ofReal]
  have hQ : Qᴴ = Q := by
    ext b c'
    simp only [hQdef, hΓ, conjTranspose_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, of_apply,
      vecMulVec_apply, Pi.star_apply, smul_eq_mul, star_add, star_sub, star_mul', star_star, hAstar]
    by_cases hb : b = L <;> by_cases hc : c' = L <;> simp [hb, hc, hBstar] <;> ring
  have hzc : Z L ⬝ᵥ c = 1 := by
    have := congrFun hZc L
    simpa [mulVec] using this
  have hΓv : Γ *ᵥ c = Pi.single L (-(B.T : ℂ) * c L) := by
    funext b
    by_cases hb : b = L
    · subst hb; simp [hΓ, mulVec, dotProduct, Finset.sum_ite_eq']
    · simp [hΓ, mulVec, dotProduct, hb]
  have hcQ : star c ⬝ᵥ (Q *ᵥ c) = 0 := by
    rw [hQdef, sub_mulVec, add_mulVec, smul_mulVec, dotProduct_sub, dotProduct_add, dotProduct_smul, dot_vmv,
      dot_vmv, hΓv, dotProduct_single, star_dotProduct_star, star_dotProduct_star, hzc, htc, smul_eq_mul,
      star_one, mul_one, mul_one]
    have h1 : star (c L) * c L = ((‖c L‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
    have h2 : star (σ : ℂ) * σ = ((σ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]; push_cast; ring
    rw [h2, hσ2, Pi.star_apply, show star (c L) * (-(B.T : ℂ) * c L) = -(B.T : ℂ) * (star (c L) * c L) by ring, h1]
    push_cast
    ring
  obtain ⟨Aα, hAlast, hAeq⟩ := solveHerm Z Q hZ hQ hcQ
  set y := A.yv i0 Z Aα t with hydef
  have hgram : ∀ b c', hJ ε (y b) (y c') = hJ ε (fam B.e B.z b) (fam B.e B.z c') := by
    intro b c'
    rw [hydef, A.gram i0 Z Aα t hAlast, B.gf]
    have hq := congrFun (congrFun hAeq b) c'
    rw [Matrix.add_apply] at hq
    have hQbc : Q b c' = Γ b c' + (A.T : ℂ)⁻¹ * (star (Z L b) * Z L c') - star (t b) * t c' := by
      simp [hQdef, vecMulVec_apply]
    have hΓbc : Γ b c' = if b = L ∧ c' = L then -(B.T : ℂ) else 0 := by
      rw [hΓ, of_apply]
      by_cases hb : b = L <;> by_cases hc : c' = L <;> simp [hb, hc]
    rw [← hΓbc]
    linear_combination hq + hQbc
  let s : (Fin (r + 1) ⊕ {i : Fin k // i ≠ i0}) → Fin n → ℂ := Sum.elim (fam B.e B.z) (fun i => B.wb i.1)
  let tt : (Fin (r + 1) ⊕ {i : Fin k // i ≠ i0}) → Fin n → ℂ := Sum.elim y (fun i => A.wb i.1)
  have hs : LinearIndependent ℂ s :=
    li_of_pair ε s (Sum.elim B.Fv (fun i => B.wb i.1)) 1 (by simp) (by
      rintro (a|j) (b|i)
      · simp [s, B.Fv_fam, one_apply]
      · simp [s, B.Fv_w, one_apply]
      · simp [s, B.w_fam, one_apply]
      · simp [s, B.ww, one_apply, Subtype.ext_iff])
  have ht : LinearIndependent ℂ tt :=
    li_of_pair ε tt (Sum.elim (fam A.e A.z) (fun i => A.wb i.1)) (Matrix.fromBlocks Z 0 0 1)
      (by rw [det_fromBlocks_zero₂₁, det_one, mul_one]; exact hZ) (by
      rintro (a|j) (b|i)
      · simp [tt, hydef, A.p1]
      · simp [tt, A.fam_w]
      · simp [tt, hydef, A.p4, j.2]
      · simp [tt, A.ww, one_apply, Subtype.ext_iff])
  have hG : ∀ i j, hJ ε (tt i) (tt j) = hJ ε (s i) (s j) := by
    rintro (b|i) (c'|j)
    · exact hgram b c'
    · show hJ ε (y b) (A.wb j.1) = hJ ε (fam B.e B.z b) (B.wb j.1)
      rw [swapJ (A.p4 i0 Z Aα t j.1 b), if_neg j.2, star_zero, B.fam_w]
    · show hJ ε (A.wb i.1) (y c') = hJ ε (B.wb i.1) (fam B.e B.z c')
      rw [hydef, A.p4, if_neg i.2, B.w_fam]
    · show hJ ε (A.wb i.1) (A.wb j.1) = hJ ε (B.wb i.1) (B.wb j.1)
      rw [A.ww, B.ww]
  obtain ⟨g, hg⟩ := wittFam ε s tt hs ht hG
  exact ⟨g, y, t, htc, fun b => hg (Sum.inl b), fun i hi => hg (Sum.inr ⟨i, hi⟩), A.p1 i0 Z Aα t,
    A.p4 i0 Z Aα t⟩

end Formalism.L2.SG.RealObj.InfCut.PtRepPf
end
end

