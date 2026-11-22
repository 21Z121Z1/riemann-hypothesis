import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0016
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0042
import Formalism.LocalToGlobal.ProjectiveLattices.LocalUnitReduction.IsUnitMkOfForallPrime
import Formalism.LocalToGlobal.ProjectiveLattices.FibreUniformisationLevelTwo
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.AxHSupA
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_frMap (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (f : Rul Xo c)
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {K₁ K₂ : Type} [CommRing K₁] [Algebra c.F K₁] [CommRing K₂] [Algebra c.F K₂] (φ : K₁ →ₐ[c.F] K₂)
    (y₁ : FrPt Xo c K₁) (hT1 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y₁)
    (y₂ : FrPt Xo c K₂) (hm : FrMap φ y₁ y₂) : evR Xo c f y₂ = φ (evR Xo c f y₁) := by
  have hT2 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y₂ := by
    obtain ⟨p, ψ, y', hy'⟩ := hT1
    exact ⟨p, φ.comp ψ, y', frMap_trans (Xo := Xo) (c := c) _ _ _ ψ φ y' y₁ y₂ hy' hm⟩
  unfold evR evalAt
  rw [dif_pos hT2, dif_pos hT1]
  exact hWD f hf K₂ _ _ _ _ _ _ y₂ hT2.choose_spec.choose_spec.choose_spec
    (frMap_trans (Xo := Xo) (c := c) _ _ _ _ φ _ y₁ y₂ hT1.choose_spec.choose_spec.choose_spec hm)

end Gen

section Rec

open Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D} (hL : LawsP T) (j : ℕ) [IsCMField D.host.E] [Fintype (Comp (T.Q.Xo j) T.Q.c)]

def SupRLeRec (fn : ∀ σ : T.Q.c.F →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt σ) → Ix (T.Q.Dw j) → ℝ) (i : ℕ)
    (η : (recB hL.toLawsCore).Cusp j (wEt D j i)) : Prop :=
  ∀ sg, supR (T.Q.Xo j) T.Q.c fn sg (wtA (wEt D j i)) (wEt D j i).n η.1 ≤ (recB hL.toLawsCore).supN j _ sg η

end Rec

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CBaseYPDef
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def colR (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (j : Fin r) : ℝ :=
  ‖dmin X.Gm x τ j.succ / dmin X.Gm x τ j.castSucc‖

open Classical in

def letNrm {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (xR : ℝ) (k : U.Comp) (x : Frame (U.X k).Ψ r) : Ix Dw → ℝ
  | none => ∏ τ : (U.X k).Ψ, ∏ j : Fin r, colR (U.X k) x τ j ^ ((if (U.X k).p0 ≤ (j : ℕ) then 1 else -1 : ℝ) / 4)
  | some ⟨τ', i⟩ => Real.exp (Real.log (2 * Real.pi * xR) / 2) *
      (if h : relab c σ τ' ∈ (U.X k).Ψ then
        (if hi : (U.X k).p0 + (i : ℕ) < r then colR (U.X k) x ⟨_, h⟩ ⟨_, hi⟩ ^ ((1 : ℝ) / 2) else 1)
      else if h' : conjEmb (relab c σ τ') ∈ (U.X k).Ψ then
        (if hi : (i : ℕ) < (U.X k).p0 then
          colR (U.X k) x ⟨_, h'⟩ ⟨(U.X k).p0 - 1 - i, by have := (U.X k).p0_le; omega⟩ ^ (-(1 : ℝ) / 2) else 1)
      else 1)

def IsIdOrConj {σ σ' : c.F →+* ℂ} (φ : CAt σ →ₐ[c.F] CAt σ') : Prop :=
  (∀ z : CAt σ, toC (φ z) = toC z) ∨ ∀ z : CAt σ, toC (φ z) = starRingEnd ℂ (toC z)

def RdAt (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ))
    (q : Σ k : (U (goodOf c σ)).Comp, ((U (goodOf c σ)).X k).dom × (Ix Dw → (CAt (goodOf c σ))ˣ)) : Prop :=
  ∃ (y' : FrPt Xo c (CAt (goodOf c σ))) (φ : CAt σ →ₐ[c.F] CAt (goodOf c σ)),
    IsIdOrConj φ ∧ FrMap φ y y' ∧ FrBor q.2.2 ((U (goodOf c σ)).un q.1 q.2.1) y'

open Classical in

def fnDef (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (xR : ℝ) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (i : Ix Dw) : ℝ :=
  if h : ∃ q, RdAt U σ y q then
    cabs ((h.choose.2.2 i : (CAt (goodOf c σ))ˣ) : CAt (goodOf c σ)) *
      letNrm (U (goodOf c σ)) xR h.choose.1 h.choose.2.1.1 i
  else 1

variable (Xo c) in

def CBaseEx (h : GenFrEx Xo c) : Prop :=
  ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ), ∃ y : FrPt Xo c (CAt (sgOf P)), FrMap (PAlg P) (genFr h Z) y

def yPDef (h : GenFrEx Xo c) (hb : CBaseEx Xo c h) (Z : Comp Xo c) (P : Om Z →+* ℂ) : FrPt Xo c (CAt (sgOf P)) :=
  (hb Z P).choose

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CurveOpen
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)

def BIRSt {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF) : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (a : Om Z), ∃ (k : ℕ) (g : (recB h.toLawsCore).Cusp j (wsmul k wL))
    (p : MvPolynomial (Fin G.N) T.Q.c.F), p.IsHomogeneous k ∧
    MvPolynomial.aeval (fun i => evC hG Z ((G.w i : (recB h.toLawsCore).Cusp j wL) : T.R j)) p ≠ 0 ∧
    a * MvPolynomial.aeval (fun i => evC hG Z ((G.w i : (recB h.toLawsCore).Cusp j wL) : T.R j)) p =
      evC hG Z ((g : (recB h.toLawsCore).Cusp j (wsmul k wL)) : T.R j)

def CompSplitSt : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (w : WeightFamilies.Wt D j) (g : (recB h.toLawsCore).Cusp j w),
    ∃ g' : (recB h.toLawsCore).Cusp j w,
      evC hG Z ((g' : (recB h.toLawsCore).Cusp j w) : T.R j) = evC hG Z ((g : (recB h.toLawsCore).Cusp j w) : T.R j) ∧
      ∀ Z', Z' ≠ Z → evC hG Z' ((g' : (recB h.toLawsCore).Cusp j w) : T.R j) = 0

def GenValInjSt : Prop :=
  ∀ (w : WeightFamilies.Wt D j) (g : (recB h.toLawsCore).Cusp j w),
    (∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z ((g : (recB h.toLawsCore).Cusp j w) : T.R j) = 0) → g = 0

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CurveUnit
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct

section Gen

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
  (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

theorem curveUnit_isUnit_emb (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)
    (F : X.Forms) (hF : gF F ≠ 0) :
    IsUnit (lwZ X la N Ω gF w (algebraMap (Rp X la N) (Lw X la w) (emb X la N F))) := by
  rw [lwZ_alg, rzMap_emb]
  have h1 : IsUnit ((1 : X.Kl la) ⊗ₜ[B.KO] gF F) := by
    simpa using (IsUnit.mk0 _ hF).map
      (Algebra.TensorProduct.includeRight : Ω →ₐ[B.KO] X.Kl la ⊗[B.KO] Ω)
  have h2 : IsUnit ((1 : Kp X la N) ⊗ₜ[X.Kl la] ((1 : X.Kl la) ⊗ₜ[B.KO] gF F)) := by
    simpa using h1.map (Algebra.TensorProduct.includeRight :
      X.Kl la ⊗[B.KO] Ω →ₐ[X.Kl la] Kp X la N ⊗[X.Kl la] (X.Kl la ⊗[B.KO] Ω))
  exact h2.map _

theorem curveUnit_isUnit_w0inv (Ω : Type) [CommRing Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) :
    IsUnit (lwZ X la N Ω gF w (w0inv X la w)) := by
  refine IsUnit.of_mul_eq_one (lwZ X la N Ω gF w (algebraMap (Rp X la N) (Lw X la w) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))) ?_
  rw [← map_mul, mul_comm, section_mul_inverse_eq_one, map_one]

variable {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)]
  (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)

theorem nonzero_divisor_cusp_form
    (hInj : ∀ f : ↥(Frac0 X la w), (∀ Z, phiZ X la N (Ω Z) (gF Z) w f = 0) → f = 0)
    (F : X.Forms) (hF : ∀ Z, gF Z F ≠ 0) (b : ↥(Frac0 X la w))
    (hb : (b : Lw X la w) * algebraMap (Rp X la N) (Lw X la w) (emb X la N F) = 0) : b = 0 := by
  refine hInj b fun Z => ?_
  rw [phiZ_apply]
  have h1 := congrArg (lwZ X la N (Ω Z) (gF Z) w) hb
  rw [map_mul, map_zero] at h1
  exact (curveUnit_isUnit_emb X la N w (Ω Z) (gF Z) F (hF Z)).mul_left_eq_zero.mp h1

theorem curveUnit_unit_gen [Fintype ι]
    (hInj : ∀ f : ↥(Frac0 X la w), (∀ Z, phiZ X la N (Ω Z) (gF Z) w f = 0) → f = 0)
    (hone : ∀ Q : Ideal ↥(Frac0 X la w), Q.IsPrime → Jid X la w ≤ Q → ∀ Z Z',
      RingHom.ker (phiZ X la N (Ω Z) (gF Z) w) ≤ Q → RingHom.ker (phiZ X la N (Ω Z') (gF Z') w) ≤ Q → Z = Z')
    (hloc : ∀ Z (r : RZs X la N (Ω Z) (gF Z) w), ∃ a p : ↥(Frac0 X la w),
      (∀ Q : Ideal ↥(Frac0 X la w), Q.IsPrime → Jid X la w ≤ Q →
        RingHom.ker (phiZ X la N (Ω Z) (gF Z) w) ≤ Q → p ∉ Q) ∧
      phiZ X la N (Ω Z) (gF Z) w p * r = phiZ X la N (Ω Z) (gF Z) w a)
    (hfd : FiniteDimensional (Kp X la N) (OsK X la w))
    (u : ↥(Frac0 X la w)) (hu : ∀ Z, IsUnit (phiZ X la N (Ω Z) (gF Z) w u)) :
    IsUnit (toOsK X la w u) := by
  classical
  have hmem : ∀ b : ↥(Frac0 X la w), b * u ∈ Jid X la w → b ∈ Jid X la w := by
    intro b hb
    refine LocalUnitReduction.mem_of_forall_sup_ker (Jid X la w) (R := fun Z => RZs X la N (Ω Z) (gF Z) w)
      (fun Z => phiZ X la N (Ω Z) (gF Z) w) hInj hone fun Z => ?_
    refine LocalUnitReduction.mem_sup_ker (Jid X la w) (R := fun Z => RZs X la N (Ω Z) (gF Z) w)
      (fun Z => phiZ X la N (Ω Z) (gF Z) w) (hloc Z) ?_
    obtain ⟨v, hv⟩ := hu Z
    have h1 : phiZ X la N (Ω Z) (gF Z) w (b * u) ∈
        Ideal.map (phiZ X la N (Ω Z) (gF Z) w) (Jid X la w) := Ideal.mem_map_of_mem _ hb
    rw [map_mul, ← hv] at h1
    have h2 := Ideal.mul_mem_right (↑v⁻¹ : RZs X la N (Ω Z) (gF Z) w) _ h1
    rwa [mul_assoc, Units.mul_inv, mul_one] at h2
  have hinj : Function.Injective (LinearMap.mulRight (Kp X la N) (toOsK X la w u)) := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨b, rfl⟩ := toOsK_surjective X la w y
    rw [LinearMap.mulRight_apply, ← map_mul, toOsK_eq_zero_iff] at hy
    rw [toOsK_eq_zero_iff]
    exact hmem b hy
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) 1
  rw [LinearMap.mulRight_apply] at hy
  exact IsUnit.of_mul_eq_one y (by rw [mul_comm]; exact hy)

end Gen

section U0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X}
  {hM : IntAtExt X E} {ka wL wF : WeightFamilies.Wt D j}

theorem phi_unit_product_cusp_forms (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))
    (g0 : B.Cusp j wF) {e : ℕ} {w' : WeightFamilies.Wt D j} (θ : B.Cusp j w') (hw : wadd wF w' = wsmul e wL)
    (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : (xplus X E hM).Forms →ₐ[B.KO] Ω)
    (hg : gF (X.inc wF g0) ≠ 0) (hθ : gF (X.inc w' θ) ≠ 0) :
    IsUnit (phiZ (xplus X E hM) la G.N Ω gF G.w (u0 G la g0 θ hw)) := by
  rw [phiZ_apply]
  show IsUnit (lwZ (xplus X E hM) la G.N Ω gF G.w (frac (xplus X E hM) la G.w e
    (emb (xplus X E hM) la G.N (X.inc wF g0) * emb (xplus X E hM) la G.N (X.inc w' θ))))
  simp only [frac_apply, map_mul, map_pow]
  exact ((curveUnit_isUnit_emb _ la G.N G.w Ω gF _ hg).mul
    (curveUnit_isUnit_emb _ la G.N G.w Ω gF _ hθ)).mul ((curveUnit_isUnit_w0inv _ la G.N G.w Ω gF).pow e)

end U0

section Inst

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)
  (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)

theorem curveUnit_gF_inc (Z : Comp (T.Q.Xo j) T.Q.c) (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) :
    formsEvR j hG hT Z ((recPJ h j hj).inc u F) = evC hG Z (F : T.R j) :=
  formsEvR_single j hG hT Z _ _

variable {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
  (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (g0 : (recB h.toLawsCore).Cusp j wF)

theorem nonzero_divisor_cusp_form_record
    (hInj : ∀ f : ↥(Frac0 (recPlus h j hj) la G.w),
      (∀ Z : Comp (T.Q.Xo j) T.Q.c, phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w f = 0) →
        f = 0)
    (hg0 : ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z ((g0 : (recB h.toLawsCore).Cusp j wF) : T.R j) ≠ 0) :
    ∀ b : ↥(Frac0 (recPlus h j hj) la G.w),
      (b : Lw (recPlus h j hj) la G.w) *
        algebraMap (Rp (recPlus h j hj) la G.N) (Lw (recPlus h j hj) la G.w)
          (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc wF g0)) = 0 →
        b = 0 :=
  fun b hb => nonzero_divisor_cusp_form (recPlus h j hj) la G.N G.w (fun Z => Om Z) (fun Z => formsEvR j hG hT Z)
    hInj _ (fun Z h0 => hg0 Z ((curveUnit_gF_inc h j hj hG hT Z wF g0).symm.trans h0)) b hb

theorem unit_ideal_cusp_form_record [Fintype (Comp (T.Q.Xo j) T.Q.c)]
    {e : ℕ} {w' : WeightFamilies.Wt D j} (θ : (recB h.toLawsCore).Cusp j w') (hw : wadd wF w' = wsmul e wL)
    (hInj : ∀ f : ↥(Frac0 (recPlus h j hj) la G.w),
      (∀ Z : Comp (T.Q.Xo j) T.Q.c, phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w f = 0) →
        f = 0)
    (hone : ∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
      ∀ Z Z' : Comp (T.Q.Xo j) T.Q.c,
        RingHom.ker (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w) ≤ Q →
        RingHom.ker (phiZ (recPlus h j hj) la G.N (Om Z') (formsEvR j hG hT Z') G.w) ≤ Q → Z = Z')
    (hloc : ∀ (Z : Comp (T.Q.Xo j) T.Q.c)
      (r : RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w),
      ∃ a p : ↥(Frac0 (recPlus h j hj) la G.w),
        (∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
          RingHom.ker (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w) ≤ Q → p ∉ Q) ∧
        phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w p * r =
          phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w a)
    (hfd : FiniteDimensional (Kp (recPlus h j hj) la G.N) (OsK (recPlus h j hj) la G.w))
    (hg0 : ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z ((g0 : (recB h.toLawsCore).Cusp j wF) : T.R j) ≠ 0)
    (hθ : ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z ((θ : (recB h.toLawsCore).Cusp j w') : T.R j) ≠ 0) :
    IsUnit (toOsK (recPlus h j hj) la G.w (u0 G la g0 θ hw)) :=
  curveUnit_unit_gen (recPlus h j hj) la G.N G.w (fun Z => Om Z) (fun Z => formsEvR j hG hT Z)
    hInj hone hloc hfd _ fun Z => phi_unit_product_cusp_forms G la g0 θ hw (Om Z) (formsEvR j hG hT Z)
      (fun h0 => hg0 Z ((curveUnit_gF_inc h j hj hG hT Z wF g0).symm.trans h0))
      (fun h0 => hθ Z ((curveUnit_gF_inc h j hj hG hT Z w' θ).symm.trans h0))

end Inst

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.FullXi
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def cjFin (D : D7) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* (Af D.host.F ⊗[D.host.F] D.host.E)ˣ :=
  Units.map (Algebra.TensorProduct.map (AlgHom.id D.host.F (Af D.host.F)) D.conjF).toRingHom.toMonoidHom

def XiTilde (xi δ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) : Prop := ∀ x, xi (x / cjFin D x) = δ x

def FullExists2 (D : D7) (pb : Fin 2 → IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.K)) (chi₀ : ℕ → (AE D)ˣ →* Circle)
    (δ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (I : Ideal (𝓞 D.host.E)) : Prop :=
  ∃ T : Full D, LawsFull T ∧ T.pb = pb ∧ (∀ j, T.chiW j T.σ₀ = chi₀ j) ∧ XiTilde T.xi δ ∧ T.half₂ = I

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.PerFrLact
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Equiv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hermC_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ G u w = u ⬝ᵥ ((G.map τ) *ᵥ star w) := by
  simp [hermC, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem star_mulVec' (A : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) :
    star (A *ᵥ w) = (A.map (starRingEnd ℂ)) *ᵥ star w := by
  funext a
  simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]

end Equiv

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def GamExt {g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} (F : FamilyUnif Xo σ' ty) (M : ModelsOf F r) : Prop :=
  ModelBase M → ∀ k (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La),
    (∀ a b, (F.Di k).EF (gam a) (gam b) = (F.Di k).EF a b) →
    (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ b, gam a = a + l.M • b) →
    (∀ a, ∃ b, gam a = a + l.A • b) →
    ∃ g0 ∈ (M.X k).Γ, ∀ a, (g0 : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k a : Fin r → E) = (M.φ k (gam a) : Fin r → E)

def FrDet {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) : Prop :=
  ModelBase M → IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) →
    ∀ k (x' x'' : Frame (M.X k).Ψ r), (∀ τ, (mat x' τ).det ≠ 0) → (∀ τ, (mat x'' τ).det ≠ 0) →
      ∀ C : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ,
        (∀ τ (i j : Fin (Dw.mult τ)), j < i → C τ i j = 0) → (∀ τ i, C τ i i ≠ 0) →
        (∀ a, pmOf e M k x'' a = blkL e C (pmOf e M k x' a)) → ∃ b ∈ Bor (M.X k).Ψ r, x' = rmul x'' b

end Fam

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.PtOfSPfBC
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem pos_ppx_le {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

theorem pos_frMap (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) {K₁ K₂ : Type}
    [Field K₁] [Field K₂] [Algebra c.F K₁] [Algebra c.F K₂] (φ : K₁ →ₐ[c.F] K₂) (y : FrPt Xo c K₁) :
    ∃ z : FrPt Xo c K₂, FrMap φ y z := by
  classical
  let _ : Algebra K₁ K₂ := φ.toRingHom.toAlgebra
  have htow : ∀ r : c.F, algebraMap c.F K₂ r = algebraMap K₁ K₂ (algebraMap c.F K₁ r) := fun r => (φ.commutes r).symm
  have : FaithfulSMul K₁ K₂ := (faithfulSMul_iff_algebraMap_injective K₁ K₂).2 (algebraMap K₁ K₂).injective
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback y.x).obj Xo.univ.t.G)
  have hco : ∀ τ i, ∃ cc, y.u τ i = gfpVec y.x xc cc := fun τ i => gfp_exists hx _ (y.tan τ i)
  choose d hdu using hco
  have hdW : ∀ τ i, d τ i ∈ gfpEig (c := c) hx τ := fun τ i =>
    (gfp_eig_iff hx τ _).1 (by rw [← hdu τ i]; exact y.eig τ i)
  have hd : ∀ τ, LinearIndependent K₁ (d τ) := by
    intro τ
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hu : y.u τ = fun i => gfpVec y.x xc (d τ i) := funext (hdu τ)
    have h0 : (0 : Fin n → K₁) ∈ gfpEig (c := c) hx τ := Submodule.zero_mem _
    obtain ⟨a, -, ha⟩ := y.basis τ (gfpVec y.x xc 0) (gfp_tan hx 0) ((gfp_eig_iff hx τ 0).2 h0)
    have e1 : IsCombAt y.x (y.u τ) g (gfpVec y.x xc 0) := by
      rw [hu]
      exact (gfp_comb_iff hx (d τ) g 0).2 hg.symm
    have e2 : IsCombAt y.x (y.u τ) 0 (gfpVec y.x xc 0) := by
      rw [hu]
      exact (gfp_comb_iff hx (d τ) 0 0).2 (by simp)
    have e3 := (ha g e1).trans (ha 0 e2).symm
    exact fun i => congrFun e3 i
  obtain ⟨xc', hx', hv, htm⟩ := gfp_bc (L' := K₂) hx
  have hx0' := gfp_over_bc htow y.x_over
  have hW' : ∀ τ j, (algebraMap K₁ K₂ ∘ d τ j) ∈ gfpEig (c := c) hx' τ := by
    intro τ j
    have h0 := hdW τ j
    unfold gfpEig at h0 ⊢
    rw [ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff] at h0 ⊢
    intro a
    rw [htm a (d τ j), h0 a]
    funext k
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, htow]
  have hli : ∀ τ, LinearIndependent K₂ (fun i => algebraMap K₁ K₂ ∘ d τ i) := fun τ =>
    linearIndependent_algebraMap_comp_iff.mpr (hd τ)
  refine ⟨⟨spMap (algebraMap K₁ K₂) ≫ y.x, hx0', fun τ i => gfpVec _ xc' (algebraMap K₁ K₂ ∘ d τ i),
    fun τ i => gfp_tan hx' _, fun τ i => (gfp_eig_iff hx' τ _).2 (hW' τ i),
    fun τ w hw he => gfp_basis hx0' hx' τ _ (hli τ) (hW' τ) w hw he,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.secCP (ReciprocityTheory.ChartRestriction.G.PullbackSections.cpS (algebraMap K₁ K₂) y.x) y.s,
    fun s' => ReciprocityTheory.ChartRestriction.G.PullbackSections.genBC_frame y.x hS hT (algebraMap K₁ K₂) y.s y.gen s'⟩, rfl, fun τ i => ?_,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.bcPm (algebraMap K₁ K₂) y.x, ReciprocityTheory.ChartRestriction.G.PullbackSections.bcPm_snd _ _, ReciprocityTheory.ChartRestriction.G.PullbackSections.bcPm_fst _ _,
    fun i h => rfl⟩
  show gfpVec _ xc' (algebraMap K₁ K₂ ∘ d τ i) = spMap (dualMap φ.toRingHom) ≫ y.u τ i
  rw [hdu τ i]
  exact hv (d τ i)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.SupPTGePf
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
  Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {Tc : Core D} (hL : LawsCore Tc) (j : ℕ)

def SupPtAt (σ : Tc.Q.c.F →+* ℂ) : Type :=
  Σ k : (Tc.U j σ).Comp, {x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((Tc.U j σ).X k).Ψ D.R.r // x ∈ ((Tc.U j σ).X k).dom}

variable {j} in

def NrmTieK (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c)
    (fn : ∀ σ : Tc.Q.c.F →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt σ) → Ix (Tc.Q.Dw j) → ℝ)
    (yP : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, ∀ P : Om Z →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt (sgOf P)))
    (ka : WeightFamilies.Wt D j)
    (pt : ∀ (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (P : Om Z →+* ℂ), SupPtAt j (goodOf Tc.Q.c (sgOf P))) : Prop :=
  ∀ (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (P : Om Z →+* ℂ) (F : Tc.R j),
    nrmC fn (yP Z) (wtZ (wtA ka) ka.n) (valC h (wtA ka) ka.n F Z) P =
      recNrm (Tc.U j (goodOf Tc.Q.c (sgOf P))) (xiR D) (wtA ka) ka.n F (pt Z P).1 (pt Z P).2.1

def DensK (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c) (ka : WeightFamilies.Wt D j)
    (pt : ∀ (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (P : Om Z →+* ℂ), SupPtAt j (goodOf Tc.Q.c (sgOf P))) : Prop :=
  ∀ (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (F : (recB hL).Cusp j ka), F ∈ (recB hL).Mlat j ka →
    evC h Z (F : Tc.R j) ≠ 0 →
    ∃ F' ∈ (recB hL).Mlat j ka, F' ≠ 0 ∧ ∀ sg : Tc.Q.c.F →+* ℂ,
      (recB hL).supN j ka sg F' ≤
        ⨆ P : PT (Ω := Om Z) sg, recNrm (Tc.U j (goodOf Tc.Q.c (sgOf (P : Om Z →+* ℂ)))) (xiR D) (wtA ka) ka.n
          (F : Tc.R j) (pt Z P).1 (pt Z P).2.1

theorem supPTGe_of (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c)
    (fn : ∀ σ : Tc.Q.c.F →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt σ) → Ix (Tc.Q.Dw j) → ℝ)
    (yP : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, ∀ P : Om Z →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt (sgOf P)))
    (ka : WeightFamilies.Wt D j)
    (pt : ∀ (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (P : Om Z →+* ℂ), SupPtAt j (goodOf Tc.Q.c (sgOf P)))
    (htie : NrmTieK h fn yP ka pt) (hden : DensK hL j h ka pt) :
    SupPTGe hL j h fn yP ka := by
  intro Z F hF hev
  obtain ⟨F', hF', hne, hsup⟩ := hden Z F hF hev
  refine ⟨F', hF', hne, fun sg => (hsup sg).trans (le_of_eq ?_)⟩
  exact iSup_congr fun P => (htie Z P (F : Tc.R j)).symm

end Formalism.L2.Pj
end
end

