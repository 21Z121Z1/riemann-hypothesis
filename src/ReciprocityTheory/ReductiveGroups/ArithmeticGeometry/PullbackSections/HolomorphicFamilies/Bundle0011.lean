import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.TorusMatchPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0005

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Pin1
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Complex ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate

section Pin1b

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

theorem pin1 (hx : (U.X k).IsOrtho x.1) (a' : (W.F.Di (W.ik k)).La) :
    A.φ ((W.φ k a' : (U.X k).Λ) : Fin r → E) = Lmap hU hσ W A (star (W.Pm a')) := by
  obtain ⟨v, hv⟩ : ∃ v : Fin r → E, v = ((W.φ k a' : (U.X k).Λ) : Fin r → E) := ⟨_, rfl⟩
  rw [← hv]
  have hdet : ∀ τ : (U.X k).Ψ, (mat x.1 τ).det ≠ 0 := fun τ => (x.2 τ).1
  have hrel : ∀ ρ : E →+* ℂ, relab c σ ((relabE c σ).symm (conjEmb ρ)) = conjEmb ρ :=
    fun ρ => (relabE c σ).apply_symm_apply _
  ext ⟨ρ, a⟩
  rw [Lmap_apply, Pi.star_apply, W.pm_eq, letT_e, ← hv]
  simp only [hrel]
  rw [fibE_val]
  by_cases h : ρ ∈ (U.X k).Ψ
  · rw [if_pos h]
    have ha := index_lt_signature_of_mem hU A h a
    rw [perFr_conj (U.X k) x.1 v h _ (by omega)]
    have e1 := A.coord_pos ⟨ρ, h⟩ a v
    refine e1.trans ?_
    rw [e_mul A hx hdet]
    rw [ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.hermC_smul_right, wt, dif_pos h, star_def,
      ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.hermC_conj ρ (U.X k).Gm (U.X k).Gm_herm]
    have hidx : (⟨(U.X k).p0 - 1 - ((U.X k).p0 - 1 - (a : ℕ)), by have := (U.X k).p0_le; omega⟩ : Fin r) =
        Fin.castLE (by rw [A.dim_pos ⟨ρ, h⟩]; exact (U.X k).p0_le) a := Fin.ext (by simp; omega)
    rw [hidx]
    have hcast : ∀ (h1 : A.T.dim ρ ≤ r), Fin.castLE h1 a = ⟨a, lt_of_lt_of_le a.2 h1⟩ := fun _ => rfl
    simp only [yf, hcast]
    ring
  · rw [if_neg h]
    obtain ⟨τ, rfl⟩ : ∃ τ, conjEmb τ = ρ := ⟨conjEmb ρ, conjEmb_conjEmb ρ⟩
    have hτ : conjEmb (conjEmb τ) ∈ (U.X k).Ψ := (conj_mem_iff _).mpr h
    have hτ' : τ ∈ (U.X k).Ψ := by rwa [conjEmb_conjEmb] at hτ
    have ha := index_lt_complementSignature_of_not_mem hU A h a
    have hp := (U.X k).p0_le
    rw [perFr_self (U.X k) x.1 v hτ a (by omega), inv_coord (U.X k) x.1 hx _ (hdet _) (Data.emb _ v), wt, dif_neg h]
    have hsub : (⟨conjEmb (conjEmb τ), hτ⟩ : (U.X k).Ψ) = ⟨τ, hτ'⟩ := Subtype.ext (conjEmb_conjEmb τ)
    simp only [hsub]
    rw [conjEmb_conjEmb]
    have e1 := A.coord_neg ⟨τ, hτ'⟩ a v
    refine e1.trans ?_
    rw [e_mul A hx hdet, ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.hermC_smul_right]
    have hs : (sgn (U.X k).p0 ((U.X k).p0 + (a : ℕ)) : ℂ) = -1 := by
      unfold sgn
      rw [if_neg (by omega)]
      norm_num
    simp only [yf, star_def, map_neg, map_mul, Complex.conj_conj, hs, map_one]
    ring

end Pin1b

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Pin4
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Pin4

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

include hU in

theorem pin4 (hPP : PPSemicharSt) (Wu : UnitAt W) (hu : ∀ τ' i', ‖dmin (U.X k).Gm x.1 τ' i'‖ = 1)
    (hw : A.w0 = H.w0) (a : (W.F.Di (W.ik k)).La) :
    ((A.T.eps (A.φ ((W.φ k a : (U.X k).Λ) : Fin r → E)) : ℤ) : ℂ) = Wu.χl (W.Pm a) := by
  rw [hPP Xo c σ r U hU k x W Wu hu a]
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = (W.F.Di (W.ik k)).EF a (H.w0 • a) := ⟨_, rfl⟩
  rw [← hn]
  have hv := (W.φ k a).2
  have hsm : ((H.w0 : E) • ((W.φ k a : (U.X k).Λ) : Fin r → E)) =
      ((W.φ k (H.w0 • a) : (U.X k).Λ) : Fin r → E) := by
    rw [LinearEquiv.map_smul, Submodule.coe_smul]
    rfl
  have he := A.eps_eq _ hv
  rw [hw, hsm, A.im_eq _ hv _ (W.φ k (H.w0 • a)).2] at he
  obtain ⟨q, hq⟩ : ∃ q : ℚ, q = Algebra.trace ℚ E ((U.X k).ξ0 * herm (U.X k).Gm
      ((W.φ k a : (U.X k).Λ) : Fin r → E) ((W.φ k (H.w0 • a) : (U.X k).Λ) : Fin r → E)) := ⟨_, rfl⟩
  rw [← hq] at he
  have hi := W.isom k a (H.w0 • a)
  rw [neg_mul, map_neg, ← hq, ← hn] at hi
  have hqr : (q : ℝ) = -(n : ℝ) := by
    have := congrArg (fun t : ℚ => (t : ℝ)) hi
    push_cast at this
    linarith
  have hc : Real.cos (Real.pi * (A.sg * (q : ℝ))) = (-1 : ℝ) ^ n := by
    rw [hqr]
    rcases A.sg_pm with h | h <;> rw [h]
    · rw [show Real.pi * (1 * -(n : ℝ)) = -((n : ℝ) * Real.pi) by ring, Real.cos_neg, Real.cos_int_mul_pi]
    · rw [show Real.pi * (-1 * -(n : ℝ)) = (n : ℝ) * Real.pi by ring, Real.cos_int_mul_pi]
  rw [hc] at he
  have hC := congrArg (fun t : ℝ => (t : ℂ)) he
  push_cast at hC
  exact hC

end Pin4

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.TorusLinv
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Complex ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate

section Inv

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

theorem e_ne_zero (τ : (U.X k).Ψ) (b : Fin r) : A.e τ b ≠ 0 := by
  intro h0
  have := A.e_orth τ b b
  rw [if_pos rfl, h0] at this
  simp only [hermC, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at this
  unfold sgn at this
  split_ifs at this <;> norm_num at this

theorem yf_ne_zero (hx : (U.X k).IsOrtho x.1) (τ : (U.X k).Ψ) (b : Fin r) : yf A τ b ≠ 0 := by
  intro h0
  have := e_mul A hx (fun τ => (x.2 τ).1) τ b
  change A.e τ b = yf A τ b • col (mat x.1 τ) b at this
  rw [h0, zero_smul] at this
  exact e_ne_zero A τ b this

theorem c_pos (τ : (U.X k).Ψ) : 0 < (U.X k).c τ := by
  unfold Data.c
  have : τ.1 (U.X k).ξ0 ≠ 0 := (map_ne_zero τ.1).mpr (U.X k).ξ0_ne
  have := norm_pos_iff.mpr this
  linarith

theorem wt_ne_zero (hx : (U.X k).IsOrtho x.1) (i : ReciprocityTheory.ChartRestriction.G.I2.Idx A.T.dim) : wt hU A i ≠ 0 := by
  unfold wt
  split_ifs with h
  · refine mul_ne_zero ?_ ?_
    · exact_mod_cast (Real.sqrt_pos.mpr (c_pos _)).ne'
    · rw [map_ne_zero]
      exact yf_ne_zero A hx _ _
  · refine mul_ne_zero ?_ (yf_ne_zero A hx _ _)
    exact_mod_cast (Real.sqrt_pos.mpr (c_pos _)).ne'

include hU hσ in

def Linv : ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim →ₗ[ℂ] (Fin W.g → ℂ) where
  toFun v := fun j => v ((letT hU hσ W A).symm j) / wt hU A ((letT hU hσ W A).symm j)
  map_add' v w := by
    funext j
    simp only [PiLp.add_apply, Pi.add_apply, add_div]
  map_smul' a v := by
    funext j
    simp only [PiLp.smul_apply, smul_eq_mul, Pi.smul_apply, RingHom.id_apply, mul_div_assoc]

theorem Linv_Lmap (hx : (U.X k).IsOrtho x.1) (z : Fin W.g → ℂ) : Linv hU hσ W A (Lmap hU hσ W A z) = z := by
  funext j
  show Lmap hU hσ W A z ((letT hU hσ W A).symm j) / wt hU A ((letT hU hσ W A).symm j) = z j
  rw [Lmap_apply, Equiv.apply_symm_apply, mul_div_cancel_left₀ _ (wt_ne_zero hU A hx _)]

theorem Lmap_Linv (hx : (U.X k).IsOrtho x.1) (v : ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim) :
    Lmap hU hσ W A (Linv hU hσ W A v) = v := by
  ext i
  rw [Lmap_apply]
  show wt hU A i * (v ((letT hU hσ W A).symm (letT hU hσ W A i)) / wt hU A ((letT hU hσ W A).symm (letT hU hσ W A i))) = v i
  rw [Equiv.symm_apply_apply, mul_div_cancel₀ _ (wt_ne_zero hU A hx _)]

end Inv

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

