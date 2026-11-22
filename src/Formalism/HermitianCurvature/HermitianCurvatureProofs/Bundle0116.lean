import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0110
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadCorrespondenceOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0108

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DframeCommute
section
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBI

section commute

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem inWb_of_zero (hr : r = 0) (v : Fin (2 * r + k + 1) → ℂ) : inWb k r v := by
  subst hr; intro i hi; exfalso; have := i.isLt; omega

theorem prW_perp0 (hr : r = 0) (z v : Fin (2 * r + k + 1) → ℂ) (hvz : herm (Hpk k r) v z = 0) :
    D.prW k r z v = v := by
  rw [prW_eq, Wb_of_inWb (inWb_of_zero hr v), hvz, zero_div, zero_smul, sub_zero]

theorem herm_unit {g : B.Mat k r} (hg : g ∈ UH (Hpk k r)) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g *ᵥ v) w = herm (Hpk k r) v (g⁻¹ *ᵥ w) := by
  have hu := WeylGroupFacts.isUnit_of_uh hg
  conv_lhs => rw [show w = g *ᵥ (g⁻¹ *ᵥ w) by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mulVec]]
  exact herm_m0_mulVec_invariant g hg v _

theorem dframe_commute (S : B.RealPlaceData k r Wp Wq) (hr : r = 0) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) (hD : D.IsDFrame S ν' m₀ γ)
    (hdet : (Zhat k r S.z S.z' γ).det ≠ 0) {hB : B.Mat k r} (hhB : hB ∈ UWset k r S.z') (hBν : hB *ᵥ ν' = ν') :
    (m₀ * hB * m₀⁻¹) * γ * hB⁻¹ = γ := by
  obtain ⟨hν, hνz, hνν, ⟨hmU, hmfix⟩, hmz⟩ := hbase
  obtain ⟨⟨a1, ha1, h1⟩, ⟨a2, ha2, h2⟩, h3⟩ := hD
  have hz := S.z_mem
  have hz' := S.z'_mem
  have um := WeylGroupFacts.isUnit_of_uh hmU
  have uγ := WeylGroupFacts.isUnit_of_uh hγ
  have uB := WeylGroupFacts.isUnit_of_uh hhB.1
  set ζ := (Zhat k r S.z S.z' γ).det with hζdef
  have hzν : herm (Hpk k r) S.z' ν' = 0 := herm_zν hνz
  have hzz0 : herm (Hpk k r) S.z' S.z' ≠ 0 := by
    rw [herm_self_alt]; have := S.T'_pos; intro h; simp at h; linarith
  have hzz0' : herm (Hpk k r) S.z S.z ≠ 0 := by
    rw [herm_self_alt]; have := S.T_pos; intro h; simp at h; linarith

  have hlast : ∀ b : Fin (r + 1), b = Fin.last r := fun b => Fin.ext (by have := b.isLt; simp only [Fin.val_last]; omega)
  have hfz : ∀ (x : Fin (2 * r + k + 1) → ℂ) (b : Fin (r + 1)), fvec k r x b = x := by
    intro x b; rw [hlast b]; exact fvec_lastI x
  have hadj : ∀ a b : Fin (r + 1), (Zhat k r S.z S.z' γ).adjugate a b = 1 := by
    subst hr; intro a b
    rw [Matrix.adjugate_fin_one]; fin_cases a; fin_cases b; rfl
  have hcofR : D.cofR S γ = γ *ᵥ S.z' := by
    unfold D.cofR; subst hr; simp [hadj, hfz]
  have hcofL : D.cofL S γ = S.z := by
    unfold D.cofL; subst hr; simp [hadj, hfz]
  rw [hcofR, prW_eq, Wb_of_inWb (inWb_of_zero hr _)] at h1
  rw [hcofL, prW_eq, Wb_of_inWb (inWb_of_zero hr _)] at h2

  set c1 := herm (Hpk k r) (γ *ᵥ S.z') S.z / herm (Hpk k r) S.z S.z with hc1
  set c2 := herm (Hpk k r) (γ⁻¹ *ᵥ S.z) S.z' / herm (Hpk k r) S.z' S.z' with hc2
  have hγz' : γ *ᵥ S.z' = c1 • S.z + ((a1 : ℂ) * ζ) • (m₀ *ᵥ ν') := by rw [← h1]; abel
  have hγiz : γ⁻¹ *ᵥ S.z = c2 • S.z' + ((a2 : ℂ) * conj ζ) • ν' := by rw [← h2]; abel
  set μ := Real.sqrt (Tz k r S.z' / Tz k r S.z) with hμdef
  have hμ : 0 < μ := Real.sqrt_pos.2 (div_pos S.T'_pos S.T_pos)
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  have hmiz : m₀⁻¹ *ᵥ S.z = (μ : ℂ)⁻¹ • S.z' := by
    have : S.z = (μ : ℂ)⁻¹ • (m₀ *ᵥ S.z') := by rw [hmz, smul_smul, inv_mul_cancel₀ hμ', one_smul]
    rw [this, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ um, Matrix.one_mulVec]
  set σ := m₀⁻¹ * γ with hσdef

  have hσz' : σ *ᵥ S.z' = (c1 * (μ : ℂ)⁻¹) • S.z' + ((a1 : ℂ) * ζ) • ν' := by
    rw [hσdef, ← Matrix.mulVec_mulVec, hγz', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hmiz,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ um, Matrix.one_mulVec, smul_smul]
  have ha2ζ : (a2 : ℂ) * conj ζ ≠ 0 := by
    refine mul_ne_zero (by exact_mod_cast ha2.ne') ?_
    simpa using hdet
  have hγν : γ *ᵥ ν' = ((a2 : ℂ) * conj ζ)⁻¹ • (S.z - c2 • (γ *ᵥ S.z')) := by
    have e : γ *ᵥ (γ⁻¹ *ᵥ S.z) = S.z := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ uγ, Matrix.one_mulVec]
    rw [hγiz, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul] at e
    rw [← e]
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ha2ζ, one_smul]
  have hσν : σ *ᵥ ν' = (((a2 : ℂ) * conj ζ)⁻¹ * (μ : ℂ)⁻¹) • S.z' -
      (((a2 : ℂ) * conj ζ)⁻¹ * c2) • (σ *ᵥ S.z') := by
    simp only [hσdef, ← Matrix.mulVec_mulVec]
    rw [hγν, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, hmiz, smul_sub, smul_smul, smul_smul]

  have hfix : ∀ u, herm (Hpk k r) u S.z' = 0 → herm (Hpk k r) u ν' = 0 → σ *ᵥ u = u := by
    intro u hu1 hu2
    have e1 : herm (Hpk k r) (γ *ᵥ u) S.z = 0 := by
      rw [herm_unit hγ, hγiz, B2x4.herm_add_right, B2x4.herm_smul_right, B2x4.herm_smul_right, hu1, hu2]
      simp
    have e2 : herm (Hpk k r) (γ *ᵥ u) (γ *ᵥ S.z') = 0 := by rw [herm_m0_mulVec_invariant γ hγ, hu1]
    have key := h3 (γ *ᵥ u) (fun a => ⟨by rw [hfz]; exact e1, by rw [hfz]; exact e2⟩)
    rw [prW_perp0 hr S.z _ e1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ uγ, Matrix.one_mulVec,
      prW_perp0 hr S.z' u hu1] at key
    rw [hσdef, ← Matrix.mulVec_mulVec, key, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ um, Matrix.one_mulVec]

  have hBz' : hB *ᵥ S.z' = S.z' := hhB.2.2
  have hBperp : ∀ u, herm (Hpk k r) u S.z' = 0 → herm (Hpk k r) u ν' = 0 →
      herm (Hpk k r) (hB *ᵥ u) S.z' = 0 ∧ herm (Hpk k r) (hB *ᵥ u) ν' = 0 := by
    intro u h1u h2u
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [← hBz']
      rw [herm_m0_mulVec_invariant hB hhB.1, h1u]
    · conv_lhs => rw [← hBν]
      rw [herm_m0_mulVec_invariant hB hhB.1, h2u]

  have hcomm : σ * hB = hB * σ := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply]
    set α := herm (Hpk k r) v S.z' / herm (Hpk k r) S.z' S.z' with hα
    set β := herm (Hpk k r) v ν' with hβ
    set v0 := v - α • S.z' - β • ν' with hv0
    have hv0z : herm (Hpk k r) v0 S.z' = 0 := by
      rw [hv0, B2x4.herm_sub_left, B2x4.herm_sub_left, B2x4.herm_smul_left, B2x4.herm_smul_left, hνz, hα]
      field_simp; ring
    have hv0ν : herm (Hpk k r) v0 ν' = 0 := by
      rw [hv0, B2x4.herm_sub_left, B2x4.herm_sub_left, B2x4.herm_smul_left, B2x4.herm_smul_left, hzν, hνν, hβ]
      ring
    have hv : v = v0 + α • S.z' + β • ν' := by rw [hv0]; abel
    obtain ⟨hb1, hb2⟩ := hBperp v0 hv0z hv0ν
    rw [← Matrix.mulVec_mulVec v σ hB, ← Matrix.mulVec_mulVec v hB σ, hv]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hBz', hBν, hfix v0 hv0z hv0ν,
      hfix (hB *ᵥ v0) hb1 hb2]
    rw [hσν, hσz']
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hBz', hBν]

  have hγσ : γ = m₀ * σ := by rw [hσdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ um, Matrix.one_mul]
  rw [hγσ]
  calc m₀ * hB * m₀⁻¹ * (m₀ * σ) * hB⁻¹ = m₀ * hB * (m₀⁻¹ * m₀) * σ * hB⁻¹ := by simp only [Matrix.mul_assoc]
    _ = m₀ * (σ * hB) * hB⁻¹ := by rw [Matrix.nonsing_inv_mul _ um, hcomm]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = m₀ * σ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ uB, Matrix.mul_one]

end commute

end Formalism.FourierDecayAlt.P.PBI
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormAnisotropicPart
section
namespace Formalism.FourierDecayAlt.P.PBI

open Finset Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate

noncomputable section

section lev

variable {k : ℕ}

theorem castV_mulVec' {a b : ℕ} (h : a = b) (M : B.Mat k a) (v : Fin (2 * a + k + 1) → ℂ) :
    D.castV h (M *ᵥ v) = D.castM h M *ᵥ D.castV h v := by
  subst h
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl]

theorem zL_lift {o ρ r : ℕ} (h : o + ρ = r) (v : Fin (2 * ρ + k + 1) → ℂ) :
    Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h (D.castV h (liftVec k o ρ v)) = v := by
  subst h
  rw [Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl]
  funext i
  have := Formalism.FourierDecayAlt.P.Dx2.Tower.liftVec_levPos_gen (k := k) o ρ v i
  simpa [Formalism.FourierDecayAlt.P.Dx2.Tower.zL, levPos] using this

theorem zL_smul {o ρ r : ℕ} (h : o + ρ = r) (c : ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h (c • v) = c • Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h v := by
  funext i; simp [Formalism.FourierDecayAlt.P.Dx2.Tower.zL]

theorem hermitian_form_anisotropic_part {m : ℕ} (v w : Fin (2 * m + k + 1) → ℂ) (hv : inWb k m v) (hw : inWb k m w) :
    herm (Hpk k m) v w = herm (Hb k) (wbPart k m v) (wbPart k m w) := by
  have := Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_jV (k := k) (r := m) (wbPart k m v) (wbPart k m w)
  rwa [Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hv, Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hw] at this

theorem herm_zL {o ρ r : ℕ} (h : o + ρ = r) (v w : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v) (hw : inWb k r w) :
    herm (Hpk k ρ) (Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h v) (Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h w) = herm (Hpk k r) v w := by
  rw [hermitian_form_anisotropic_part _ _ (Formalism.FourierDecayAlt.P.Dx2.Tower.zL_wb o ρ h v hv) (Formalism.FourierDecayAlt.P.Dx2.Tower.zL_wb o ρ h w hw),
    Formalism.FourierDecayAlt.P.Dx2.Tower.zL_wbPart, Formalism.FourierDecayAlt.P.Dx2.Tower.zL_wbPart, hermitian_form_anisotropic_part v w hv hw]

theorem inWb_last {r : ℕ} (v : Fin (2 * (r - r) + k + 1) → ℂ) : inWb k (r - r) v := by
  intro i hi; exfalso; have := i.isLt; omega

theorem inWb_liftLast {r : ℕ} (h : r + (r - r) = r) (v : Fin (2 * (r - r) + k + 1) → ℂ) :
    inWb k r (D.castV h (liftVec k r (r - r) v)) := by
  intro i hi
  simp only [D.castV]
  apply Formalism.FourierDecayAlt.P.Dx2.Tower.liftVec_out_gen
  simp only [Fin.val_cast]
  omega

end lev

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def nuR (p : KB.Pl P Wp Wq) : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ :=
  Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) (by omega) p.ν'

def m0R (p : KB.Pl P Wp Wq) : B.Mat P.k (P.r - P.r) :=
  fun i j => p.m₀ ⟨i.val + P.r, by have := i.isLt; omega⟩ ⟨j.val + P.r, by have := j.isLt; omega⟩

theorem base_point_block_eq (p : KB.Pl P Wp Wq) :
    D.castM (by omega : P.r + (P.r - P.r) = P.r) (ιLev P.k P.r (P.r - P.r) (m0R p)) = p.m₀ := by
  obtain ⟨-, -, -, ⟨hmU, hmfix⟩, -⟩ := p.hF
  have hme : ∀ a : Fin P.r, p.m₀ *ᵥ ee P.k P.r a = ee P.k P.r a := fun a => (hmfix a a.isLt).1
  have hms : ∀ a : Fin P.r, p.m₀ *ᵥ es P.k P.r a = es P.k P.r a := fun a => (hmfix a a.isLt).2
  have hcol : ∀ (i j : Fin (2 * P.r + P.k + 1)), (j.val < P.r ∨ P.r + P.k < j.val) →
      p.m₀ i j = if i = j then 1 else 0 := by
    intro i j hj
    rcases hj with hj | hj
    · have e : bvec j = ee P.k P.r ⟨j.val, hj⟩ := by simp [ee, eI]
      have := congrFun (hme ⟨j.val, hj⟩) i
      rw [← e] at this
      simp only [mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at this
      rw [this, eq_comm]
    · have hj2 := j.isLt
      have e : bvec j = es P.k P.r ⟨2 * P.r + P.k - j.val, by omega⟩ := by
        simp only [es, esI]; congr 1; ext; simp; omega
      have := congrFun (hms ⟨2 * P.r + P.k - j.val, by omega⟩) i
      rw [← e] at this
      simp only [mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at this
      rw [this, eq_comm]
  have hrow : ∀ (i j : Fin (2 * P.r + P.k + 1)), (i.val < P.r ∨ P.r + P.k < i.val) →
      (P.r ≤ j.val ∧ j.val ≤ P.r + P.k) → p.m₀ i j = 0 := by
    intro i j hi hj
    have hmj : (p.m₀ *ᵥ bvec j) i = p.m₀ i j := by
      simp [mulVec, dotProduct, bvec, Pi.single_apply]
    rcases hi with hi | hi
    · have h1 := herm_es (k := P.k) (r := P.r) (p.m₀ *ᵥ bvec j) ⟨i.val, hi⟩
      rw [← hms ⟨i.val, hi⟩, Formalism.FourierDecayAlt.P.Dx2.DF.herm_m0_mulVec_invariant p.m₀ hmU, herm_es] at h1
      have hi' : eI P.k P.r ⟨i.val, hi⟩ = i := by ext; simp [eI]
      rw [hi', hmj] at h1
      rw [← h1]
      simp only [bvec, Pi.single_apply]
      rw [if_neg]; intro h; have := congrArg Fin.val h; omega
    · have hi2 := i.isLt
      have h1 := herm_ee (k := P.k) (r := P.r) (p.m₀ *ᵥ bvec j) ⟨2 * P.r + P.k - i.val, by omega⟩
      rw [← hme ⟨2 * P.r + P.k - i.val, by omega⟩, Formalism.FourierDecayAlt.P.Dx2.DF.herm_m0_mulVec_invariant p.m₀ hmU, herm_ee] at h1
      have hi' : esI P.k P.r ⟨2 * P.r + P.k - i.val, by omega⟩ = i := by ext; simp [esI]; omega
      rw [hi', hmj] at h1
      rw [← h1]
      simp only [bvec, Pi.single_apply]
      rw [if_neg]; intro h; have := congrArg Fin.val h; omega
  ext i j
  simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply]
  unfold ιLev
  by_cases hi : P.r ≤ i.val ∧ i.val ≤ P.r + P.k <;> by_cases hj : P.r ≤ j.val ∧ j.val ≤ P.r + P.k
  · rw [dif_pos (by simp; omega), dif_pos (by simp; omega)]
    simp only [m0R]
    congr 1 <;> ext <;> simp <;> omega
  · rw [dif_pos (by simp; omega), dif_neg (by simp; omega), hcol i j (by omega)]
    rw [if_neg]; intro h; rw [h] at hi; exact hj hi
  · rw [dif_neg (by simp; omega)]
    rw [hrow i j (by omega) hj, if_neg]
    · intro h; apply hi; have := congrArg Fin.val h; simp at this; omega
  · rw [dif_neg (by simp; omega), hcol i j (by omega)]
    congr 1
    apply propext; constructor
    · intro h; ext; have := congrArg Fin.val h; simpa using this
    · intro h; subst h; rfl

theorem levFrame_nuR (p : KB.Pl P Wp Wq) : LevFrame p (nuR p) (m0R p) := by
  obtain ⟨hν, hνz, hνν, ⟨hmU, hmfix⟩, hmz⟩ := p.hF
  have h : P.r + (P.r - P.r) = P.r := by omega
  have hZ : (p.T.bs P.r).z = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h p.T.base.z := by
    show (p.T.bs P.r).z = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h (p.T.bs 0).z
    rw [← p.T.z_lev P.r le_rfl, zL_lift]
  have hZ' : (p.T.bs P.r).z' = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h p.T.base.z' := by
    show (p.T.bs P.r).z' = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h (p.T.bs 0).z'
    rw [← p.T.z'_lev P.r le_rfl, zL_lift]
  have hz := p.T.base.z_mem
  have hz' := p.T.base.z'_mem
  have hblk := base_point_block_eq p

  set Lf : (Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) → (Fin (2 * P.r + P.k + 1) → ℂ) :=
    fun v => D.castV h (liftVec P.k P.r (P.r - P.r) v) with hLf
  have hLm : ∀ v, Lf (m0R p *ᵥ v) = p.m₀ *ᵥ Lf v := by
    intro v
    simp only [hLf]
    rw [← Formalism.FourierDecayAlt.P.Dx2.Tower.lev_mulVec_lift, castV_mulVec', hblk]
  have hLh : ∀ v w, herm (Hpk P.k (P.r - P.r)) v w = herm (Hpk P.k P.r) (Lf v) (Lf w) := by
    intro v w
    rw [← herm_zL h (Lf v) (Lf w) (inWb_liftLast h v) (inWb_liftLast h w), zL_lift, zL_lift]
  refine ⟨Formalism.FourierDecayAlt.P.Dx2.Tower.lift_zL P.r (P.r - P.r) h p.ν' hν, hblk, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · exact inWb_last _
  · rw [hZ', nuR, herm_zL h _ _ hν hz', hνz]
  · rw [nuR, herm_zL h _ _ hν hν, hνν]
  · apply B2x4.mem_UH_of_herm
    intro x y
    rw [hLh, hLh x y, hLm, hLm, Formalism.FourierDecayAlt.P.Dx2.DF.herm_m0_mulVec_invariant p.m₀ hmU]
  · intro a _; exact absurd a.isLt (by omega)
  · have e1 : m0R p *ᵥ (p.T.bs P.r).z' = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h (p.m₀ *ᵥ p.T.base.z') := by
      have := congrArg (Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h) (hLm (p.T.bs P.r).z')
      rw [zL_lift] at this
      rw [this, hZ']
      simp only [hLf]
      rw [Formalism.FourierDecayAlt.P.Dx2.Tower.lift_zL P.r (P.r - P.r) h _ hz']
    rw [e1, hmz, zL_smul, ← hZ, hZ', hZ, Formalism.FourierDecayAlt.P.Dx2.Tower.zL_Tz _ _ h _ hz,
      Formalism.FourierDecayAlt.P.Dx2.Tower.zL_Tz _ _ h _ hz']

end place

end

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

theorem levFrameExists_statement : PBI.LevFrameExists := by
  intro Wp Wq _ _ _ _ _ _ P p
  exact ⟨PBI.nuR p, PBI.m0R p, PBI.levFrame_nuR p⟩

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralAdjoint
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def aInt {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H))
    (w0 a : H) (t : Mx k r) (p : Mt k r × Mt k r) : Wp →L[ℂ] Wp :=
  (psi k r z c (Matrix.of p.2) * ⟪a, σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.2)⁻¹ * t) w0⟫_ℂ) • π (Matrix.of p.1)

def bInt {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wq →L[ℂ] Wq)) (σ : Mx k r → (H →L[ℂ] H))
    (w0 y : H) (t γ : Mx k r) (p : Mt k r × Mt k r) : Wq →L[ℂ] Wq :=
  (star (psi k r z c (Matrix.of p.2)) * ⟪w0, σ (t⁻¹ * γ * Matrix.of p.2 * Matrix.of p.1) y⟫_ℂ) •
    π (Matrix.of p.1)⁻¹

theorem aInt_eq {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    {σ : Mx k r → (H →L[ℂ] H)} (hU : PI.WBL.Cv.SigU σ) (w0 a : H) {t : Mx k r} (ht : t ∈ UH (Hpk k r))
    {p : Mt k r × Mt k r} (hp1 : Matrix.of p.1 ∈ UWset k r z) (hp2 : Matrix.of p.2 ∈ Nset k r) :
    beInt z c π σ (σ t w0) a (Prod.map B7.invM B7.invM p) = aInt z c π σ w0 a t p := by
  obtain ⟨p1, p2⟩ := p
  simp only at hp1 hp2
  have hh : Matrix.of p1 ∈ UH (Hpk k r) := hp1.1
  have hn : Matrix.of p2 ∈ UH (Hpk k r) := hp2.1
  have hinv : ((Matrix.of p1)⁻¹)⁻¹ = Matrix.of p1 :=
    Matrix.inv_eq_left_inv (PI.WBL.Cv.uh_inv hh).1
  have hmul : σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹ * t) =
      (σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹)).comp (σ t) :=
    hU.2.1 _ (PI.WBL.Cv.uh_mul (PI.WBL.Cv.uh_inv hh).2.2 (PI.WBL.Cv.uh_inv hn).2.2) t ht
  have hpsi := Formalism.QuantumDeterminants.BesselUnipotentEquiv.star_psi_inv z c hz (Matrix.of p2) hp2
  show (⟪a, σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹) (σ t w0)⟫_ℂ *
      star (psi k r z c (Matrix.of p2)⁻¹)) • π ((Matrix.of p1)⁻¹)⁻¹ =
    (psi k r z c (Matrix.of p2) * ⟪a, σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹ * t) w0⟫_ℂ) •
      π (Matrix.of p1)
  rw [hinv, hpsi, hmul, ContinuousLinearMap.comp_apply, mul_comm]

private theorem ae_mem_uwset_prod_nset_of_isHaarOn {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)}
    (hW : B.IsHaarOn (UWset k r z) μW) (hN : B.IsHaarOn (Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r := by
  haveI : IsFiniteMeasureOnCompacts μW := ⟨fun K hK => hW.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts μN := ⟨fun K hK => hN.finite_compact K hK⟩
  rw [ae_iff]
  apply measure_mono_null (t := ((UWset k r z)ᶜ : Set (Mt k r)) ×ˢ (Set.univ : Set (Mt k r)) ∪
    (Set.univ : Set (Mt k r)) ×ˢ ((Nset k r)ᶜ : Set (Mt k r)))
  · intro p hp
    simp only [Set.mem_setOf_eq, not_and_or] at hp
    rcases hp with hp | hp
    · exact Or.inl ⟨hp, Set.mem_univ _⟩
    · exact Or.inr ⟨Set.mem_univ _, hp⟩
  · apply measure_union_null
    · rw [Measure.prod_prod, hW.conc, zero_mul]
    · rw [Measure.prod_prod, hN.conc, mul_zero]

theorem sideA {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    {σ : Mx k r → (H →L[ℂ] H)} (hU : PI.WBL.Cv.SigU σ) {μW μN : Measure (Mt k r)}
    (hW : B.IsHaarOn (UWset k r z) μW) (hN : B.IsHaarOn (Nset k r) μN) (w0 a : H) {t : Mx k r}
    (ht : t ∈ UH (Hpk k r)) (hI : Integrable (beInt z c π σ (σ t w0) a) (μW.prod μN)) :
    Integrable (aInt z c π σ w0 a t) (μW.prod μN) ∧
      ∫ p, aInt z c π σ w0 a t p ∂(μW.prod μN) = be z c π σ μW μN (σ t w0) a := by
  haveI : IsFiniteMeasureOnCompacts μW := ⟨fun K hK => hW.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts μN := ⟨fun K hK => hN.finite_compact K hK⟩
  have hmp : MeasurePreserving (Prod.map (B7.invM (k := k) (r := r)) (B7.invM (k := k) (r := r)))
      (μW.prod μN) (μW.prod μN) :=
    (measurePreserving_invM_of_isHaarOn hW).prod (mp_inv_N hN)
  have hae : (fun p => beInt z c π σ (σ t w0) a (Prod.map B7.invM B7.invM p)) =ᵐ[μW.prod μN]
      aInt z c π σ w0 a t := by
    filter_upwards [ae_mem_uwset_prod_nset_of_isHaarOn hW hN] with p hp
    exact aInt_eq hz c π hU w0 a ht hp.1 hp.2
  have hcomp : Integrable (fun p => beInt z c π σ (σ t w0) a (Prod.map B7.invM B7.invM p))
      (μW.prod μN) :=
    (hmp.integrable_comp hI.aestronglyMeasurable).mpr hI
  refine ⟨hcomp.congr hae, ?_⟩
  rw [← integral_congr_ae hae]
  unfold be
  conv_rhs => rw [← hmp.map_eq]
  rw [integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hI.aestronglyMeasurable)]

theorem integral_adjoint {α : Type*} [MeasurableSpace α] {μ : Measure α} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {f : α → (E →L[ℂ] F)} (hf : Integrable f μ) :
    Integrable (fun x => ContinuousLinearMap.adjoint (f x)) μ ∧
      ∫ x, ContinuousLinearMap.adjoint (f x) ∂μ = ContinuousLinearMap.adjoint (∫ x, f x ∂μ) := by
  let L : (E →L[ℂ] F) ≃ₗᵢ[ℝ] (F →L[ℂ] E) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := F)).toIsometryEquiv.toRealLinearIsometryEquivOfMapZero
      (map_zero (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := F)))
  have hL : ∀ g, L g = ContinuousLinearMap.adjoint g := fun g => rfl
  refine ⟨?_, ?_⟩
  · have := L.toLinearIsometry.toContinuousLinearMap.integrable_comp hf
    simpa [hL] using this
  · have := L.toLinearIsometry.toContinuousLinearMap.integral_comp_comm hf
    simpa [hL] using this

theorem bInt_eq {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq]
    {z : Fin (2 * r + k + 1) → ℂ} (c : ℂ) {π : Mx k r → (Wq →L[ℂ] Wq)} (hrep : IsCRepOn (UWset k r z) π)
    (hun : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖)
    {σ : Mx k r → (H →L[ℂ] H)} (hU : PI.WBL.Cv.SigU σ) (w0 y : H) {t γ : Mx k r} (ht : t ∈ UH (Hpk k r))
    (hγ : γ ∈ UH (Hpk k r))
    {p : Mt k r × Mt k r} (hp1 : Matrix.of p.1 ∈ UWset k r z) (hp2 : Matrix.of p.2 ∈ Nset k r) :
    bInt z c π σ w0 y t γ p = ContinuousLinearMap.adjoint (aInt z c π σ w0 y (γ⁻¹ * t) p) := by
  obtain ⟨p1, p2⟩ := p
  simp only at hp1 hp2
  unfold bInt aInt
  have hh : Matrix.of p1 ∈ UH (Hpk k r) := hp1.1
  have hn : Matrix.of p2 ∈ UH (Hpk k r) := hp2.1
  obtain ⟨-, hh2, hhi⟩ := PI.WBL.Cv.uh_inv hh
  obtain ⟨-, hn2, hni⟩ := PI.WBL.Cv.uh_inv hn
  obtain ⟨-, hγ2, hγi⟩ := PI.WBL.Cv.uh_inv hγ
  obtain ⟨ht1, -, hti⟩ := PI.WBL.Cv.uh_inv ht
  have hXU : (Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹ * (γ⁻¹ * t) ∈ UH (Hpk k r) :=
    PI.WBL.Cv.uh_mul (PI.WBL.Cv.uh_mul hhi hni) (PI.WBL.Cv.uh_mul hγi ht)
  have hYU : t⁻¹ * γ * Matrix.of p2 * Matrix.of p1 ∈ UH (Hpk k r) :=
    PI.WBL.Cv.uh_mul (PI.WBL.Cv.uh_mul (PI.WBL.Cv.uh_mul hti hγ) hn) hh
  have hXY : (Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹ * (γ⁻¹ * t) * (t⁻¹ * γ * Matrix.of p2 * Matrix.of p1)
      = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc t t⁻¹, ht1, Matrix.one_mul, ← Matrix.mul_assoc γ⁻¹ γ, hγ2, Matrix.one_mul,
      ← Matrix.mul_assoc (Matrix.of p2)⁻¹ (Matrix.of p2), hn2, Matrix.one_mul, hh2]
  have hσ : σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹ * (γ⁻¹ * t))
      (σ (t⁻¹ * γ * Matrix.of p2 * Matrix.of p1) y) = y := by
    rw [← ContinuousLinearMap.comp_apply, ← hU.2.1 _ hXU _ hYU, hXY, hU.1,
      ContinuousLinearMap.one_apply]
  let LX : H →ₗᵢ[ℂ] H :=
    { toLinearMap := (σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹ * (γ⁻¹ * t))).toLinearMap
      norm_map' := hU.2.2 _ hXU }
  have hinner : ⟪σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹ * (γ⁻¹ * t)) w0, y⟫_ℂ =
      ⟪w0, σ (t⁻¹ * γ * Matrix.of p2 * Matrix.of p1) y⟫_ℂ := by
    conv_lhs => rw [← hσ]
    exact LX.inner_map_map w0 _
  rw [map_smulₛₗ, adjoint_pi hrep hun hp1]
  congr 1
  rw [map_mul, inner_conj_symm, hinner]
  rfl

theorem sideB {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq]
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) {π : Mx k r → (Wq →L[ℂ] Wq)}
    (hrep : IsCRepOn (UWset k r z) π) (hun : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖)
    {σ : Mx k r → (H →L[ℂ] H)} (hU : PI.WBL.Cv.SigU σ) {μW μN : Measure (Mt k r)}
    (hW : B.IsHaarOn (UWset k r z) μW) (hN : B.IsHaarOn (Nset k r) μN) (w0 y : H) {t γ : Mx k r}
    (ht : t ∈ UH (Hpk k r)) (hγ : γ ∈ UH (Hpk k r))
    (hI : Integrable (beInt z c π σ (σ (γ⁻¹ * t) w0) y) (μW.prod μN))
    (hadj : ContinuousLinearMap.adjoint (be z c π σ μW μN (σ (γ⁻¹ * t) w0) y) =
      be z c π σ μW μN y (σ (γ⁻¹ * t) w0)) :
    Integrable (bInt z c π σ w0 y t γ) (μW.prod μN) ∧
      ∫ p, bInt z c π σ w0 y t γ p ∂(μW.prod μN) = be z c π σ μW μN y (σ (γ⁻¹ * t) w0) := by
  have hγt : γ⁻¹ * t ∈ UH (Hpk k r) := PI.WBL.Cv.uh_mul (PI.WBL.Cv.uh_inv hγ).2.2 ht
  obtain ⟨hAi, hAe⟩ := sideA hz c π hU hW hN w0 y hγt hI
  obtain ⟨hBi, hBe⟩ := integral_adjoint hAi
  have hae : bInt z c π σ w0 y t γ =ᵐ[μW.prod μN]
      fun p => ContinuousLinearMap.adjoint (aInt z c π σ w0 y (γ⁻¹ * t) p) := by
    filter_upwards [ae_mem_uwset_prod_nset_of_isHaarOn hW hN] with p hp
    exact bInt_eq c hrep hun hU w0 y ht hγ hp.1 hp.2
  refine ⟨hBi.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, hBe, hAe, hadj]

end Formalism.FourierDecayAlt.P.S3dx6
end
end

