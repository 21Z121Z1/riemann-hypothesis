import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0044
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.FrameEx
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0045
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0005
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLoc

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.FnDefB
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

open Classical in

def toGoodR (c : Coeff l) (σ : c.F →+* ℂ) : ℂ →+* ℂ := if GoodEmb c σ then RingHom.id ℂ else starRingEnd ℂ

theorem toGoodR_apply (c : Coeff l) (σ : c.F →+* ℂ) (x : c.F) : toGoodR c σ (σ x) = goodOf c σ x := by
  unfold toGoodR goodOf
  split_ifs <;> rfl

def toGood (c : Coeff l) (σ : c.F →+* ℂ) : CAt σ →ₐ[c.F] CAt (goodOf c σ) :=
  { (toGoodR c σ : ℂ →+* ℂ) with commutes' := fun x => toGoodR_apply c σ x }

theorem isIdOrConj_toGood (c : Coeff l) (σ : c.F →+* ℂ) : IsIdOrConj (toGood c σ) := by
  by_cases h : GoodEmb c σ
  · left; intro z
    show toGoodR c σ (toC z) = toC z
    unfold toGoodR; rw [if_pos h]; rfl
  · right; intro z
    show toGoodR c σ (toC z) = _
    unfold toGoodR; rw [if_neg h]

theorem rdEx_of (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hA : AllTest Xo c)
    (hB : ∀ σ, GoodEmb c σ → BCEx Xo c σ) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) : ∃ q, RdAt U σ y q := by
  have : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  obtain ⟨p, ψ, y0, hy0⟩ := hA (CAt σ) y
  have hg := goodEmb_goodOf c σ
  obtain ⟨z, hz⟩ := hB _ hg p y0 ((toGood c σ).comp ψ)
  have hm : FrMap (toGood c σ) y z := frMap_cancel _ _ _ ψ (toGood c σ) y0 y z hy0 hz
  obtain ⟨k, x, t, ht⟩ := (hU _ hg).2.2.1 z
  exact ⟨⟨k, x, t⟩, z, toGood c σ, isIdOrConj_toGood c σ, hm, ht⟩

variable (Xo c) in

def LetId (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (xR : ℝ) : Prop :=
  ∀ (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n →
    ∀ (k : (U σ).Comp) (x : Frame ((U σ).X k).Ψ r), x ∈ ((U σ).X k).dom →
      ∏ i, |letNrm (U σ) xR k x i|⁻¹ ^ ex Dw a n i =
        lieFac Dw xR a * ∏ τ, ∏ j : Fin r,
          ‖dmin ((U σ).X k).Gm x τ j.succ / dmin ((U σ).X k).Gm x τ j.castSucc‖ ^ (-(laU (U σ) a n k τ j : ℝ) / 2)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.FrameExBor
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix

section Sums

end Sums

section Tri

variable {n : ℕ}

end Tri

section Per

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open Classical in

def Ablk (X : Data E r) (b : Frame X.Ψ r) (τ' : E →+* ℂ) (i l : ℕ) : ℂ :=
  if h : τ' ∈ X.Ψ then
    (if h2 : X.p0 + i < r ∧ X.p0 + l < r then (mat b ⟨τ', h⟩)⁻¹ ⟨X.p0 + i, h2.1⟩ ⟨X.p0 + l, h2.2⟩ else 0)
  else if h' : conjEmb τ' ∈ X.Ψ then
    (if h2 : X.p0 - 1 - l < r ∧ X.p0 - 1 - i < r then
      mat b ⟨conjEmb τ', h'⟩ ⟨X.p0 - 1 - l, h2.1⟩ ⟨X.p0 - 1 - i, h2.2⟩ else 0)
  else if i = l then 1 else 0

end Per

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {M : ModelsOf F r}

variable (c σ) in

theorem relab_rt_iff (hσ : GoodEmb c σ) (τ' : E →+* ℂ) :
    relab c σ τ' (H.rt : E) = H.rt0 ↔ τ' (H.rt : E) = H.rt0 := by
  have hcoe : ∀ x : E, ((embF c τ' x : c.F) : ℂ) = τ' x := fun x => by
    first
      | rfl
      | simp [embF]
  have hsq : (τ' (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow]
    have h1 : ((H.rt : E)) ^ 2 = -((H.d : ℕ) : E) := by
      have h2 := congrArg (fun y : 𝓞 E => (y : E)) H.rt_sq
      simpa using h2
    rw [h1]
    simp
  have hne : H.rt0 ≠ 0 := by
    intro h0
    have h3 := H.sqrt_neg_disc_sq
    rw [h0] at h3
    have hd := H.d_prime.pos
    have : ((H.d : ℕ) : ℂ) = 0 := by
      have h4 : (0 : ℂ) ^ 2 = -((H.d : ℕ) : ℂ) := h3
      simpa using h4.symm
    exact hd.ne' (by exact_mod_cast this)
  have hσρ : σ ⟨H.rt0, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩ = H.rt0 := hσ
  unfold relab
  simp only [RingHom.comp_apply]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · have e : embF c τ' (H.rt : E) = ⟨H.rt0, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩ :=
      Subtype.ext (by rw [hcoe, h])
    rw [e, hσρ]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · have e : embF c τ' (H.rt : E) = -⟨H.rt0, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩ :=
      Subtype.ext (by rw [hcoe, h]; rfl)
    rw [e, map_neg, hσρ, h]

theorem conjEmb_eq' (τ : E →+* ℂ) : conjEmb τ = NumberField.ComplexEmbedding.conjugate τ := by
  ext x
  simp [conjEmb, NumberField.ComplexEmbedding.conjugate_coe_eq]

variable (M) in

def AM (k : Fin F.n) (b : Frame (M.X k).Ψ r) : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ :=
  fun τ i l => Ablk (M.X k) b (relab c σ τ) i l

theorem bor_diag_ne (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ' : X.Ψ) (j : Fin r) :
    b τ' j j ≠ 0 := by
  have h1 := (hb τ').1
  have ht : (mat b τ').BlockTriangular id := fun a c hca => (hb τ').2 a c hca
  rw [Matrix.det_of_upperTriangular ht] at h1
  exact (Finset.prod_ne_zero_iff.1 h1) j (Finset.mem_univ _)

end Main

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.GenValInjPf
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

variable (Xo c) in

def GenSpecSt (hG : GenFrEx Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (m : Ideal p.R) [m.IsMaximal],
    ∃ (Z : Comp Xo c) (q : TRing c.F) (yq : FrPt Xo c q.R),
      (∃ (p' : TRing c.F) (lam : p.R →ₐ[c.F] p'.R) (a : q.R →ₐ[c.F] p'.R)
          (μ : p'.R →ₐ[c.F] Localization.AtPrime m) (y' : FrPt Xo c p'.R),
        FrMap lam y y' ∧ FrMap a yq y' ∧ μ.comp lam = locM c.F m) ∧
      ∀ (p₀ : TRing c.F) (φ₀ : p₀.R →ₐ[c.F] Om Z) (y₀ : FrPt Xo c p₀.R), FrMap φ₀ y₀ (genFr hG Z) →
        ∃ (B : TRing c.F) (β : q.R →ₐ[c.F] B.R) (β₀ : p₀.R →ₐ[c.F] B.R) (yB y₀B : FrPt Xo c B.R)
          (tB : Ix Dw → (B.R)ˣ) (Ω : Type) (_ : Field Ω) (_ : Algebra c.F Ω)
          (κ : Om Z →ₐ[c.F] Ω) (γ : B.R →ₐ[c.F] Ω),
          FrMap β yq yB ∧ FrMap β₀ y₀ y₀B ∧ FrBor tB y₀B yB ∧ γ.comp β₀ = κ.comp φ₀ ∧
            Function.Injective (γ.comp β)

theorem evR_of_frMap (hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    {f : Rul Xo c} (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {S : Type} [CommRing S] [Algebra c.F S] {p : TRing c.F} {φ : p.R →ₐ[c.F] S} {y : FrPt Xo c p.R}
    {w : FrPt Xo c S} (hy : FrMap φ y w) : evR Xo c f w = φ (f p y) := by
  have hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w := ⟨p, φ, y, hy⟩
  unfold evR evalAt
  rw [dif_pos hT]
  exact hW f hf S _ _ _ _ _ _ w hT.choose_spec.choose_spec.choose_spec hy

theorem rule_eq_zero_of_genSpec (hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    (hG : GenFrEx Xo c) (hA : AllTest Xo c) (hS : GenSpecSt Xo c hG) {e : Ix Dw → ℕ} {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    (hw : IsWeight (K := c.F) (fun S _ _ => FrPt Xo c S) (fun t y y' => FrBor t y y') e f)
    (h0 : ∀ Z : Comp Xo c, evC hG Z f = 0) : f = 0 := by
  funext p y
  show f p y = 0
  apply eq_of_locM (K := c.F)
  intro m hm
  obtain ⟨Z, q, yq, ⟨p', lam, a, μ, y', h1, h2, h3⟩, hgen⟩ := hS p y m
  have hq : f q yq = 0 := by
    obtain ⟨p₀, φ₀, y₀, h₀⟩ := hA (Om Z) (genFr hG Z)
    obtain ⟨B, β, β₀, yB, y₀B, tB, Ω, _, _, κ, γ, hβ, hβ₀, hb, hc, hinj⟩ := hgen p₀ φ₀ y₀ h₀
    have hz : φ₀ (f p₀ y₀) = 0 := by
      rw [← evR_of_frMap hW hf h₀]
      exact h0 Z
    apply hinj
    rw [map_zero, AlgHom.comp_apply, ← hf q B β yq yB hβ, hw B tB y₀B yB hb, map_mul,
      hf p₀ B β₀ y₀ y₀B hβ₀, ← AlgHom.comp_apply γ β₀, hc, AlgHom.comp_apply, hz, map_zero, mul_zero]
  have e1 : locM c.F m (f p y) = μ (lam (f p y)) := by
    rw [← AlgHom.comp_apply μ lam, h3]
  rw [e1, ← hf p p' lam y y' h1, hf q p' a yq y' h2, hq, map_zero, map_zero, map_zero]

end Gen

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {T : Top D}

theorem genValInj (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (hS : GenSpecSt (T.Q.Xo j) T.Q.c hG) : GenValInjSt h j hG := by
  intro w g hg
  have hC : (g : T.R j) ∈ T.C j w := cutR_le T.C j w g.2
  have hsec := ((mem_cusp _ _ _ _ _ _).1 hC).1
  apply Subtype.ext
  exact rule_eq_zero_of_genSpec (h.evalWD j hj) hG (h.allTest j hj) hS hsec.1 hsec.2 hg

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.I2AtFramePointsAlpha
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra
  ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections

section Iso

variable {E : Type} [Field E] [NumberField E]

def IsoPT (X X' : ReciprocityTheory.ChartRestriction.G.I2.PT E)
    (e : ReciprocityTheory.ChartRestriction.G.I2.Vsp X.dim ≃ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp X'.dim) : Prop :=
  (∀ v, v ∈ X.L ↔ e v ∈ X'.L) ∧ (∀ v w, ReciprocityTheory.ChartRestriction.G.I2.Hf (e v) (e w) = ReciprocityTheory.ChartRestriction.G.I2.Hf v w) ∧
    (∀ v ∈ X.L, X'.eps (e v) = X.eps v) ∧
    (∀ (a : 𝓞 E) v, e (ReciprocityTheory.ChartRestriction.G.I2.act a v) = ReciprocityTheory.ChartRestriction.G.I2.act a (e v))

end Iso

section I2AtA

variable {D : D7} (T : Top D) (j : ℕ)

def IsAlphaM (α : 𝓞 D.host.E) : Prop :=
  α * T.Q.H.bar α = (T.Q.l.M : 𝓞 D.host.E) ∧ T.Q.l.Mb = Ideal.span {T.Q.H.bar α}

open Classical in

def FrameTieA (xR : ℝ) {N : ℕ} (wR : Fin (N + 1) → Rul (T.Q.Xo j) T.Q.c) (uL : WtR D.host.E) (th : ℝ) {n : ℕ}
    (P₁ : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (α : 𝓞 D.host.E) : Prop :=
  LawsP T → InR D j → IsBlockProd P₁ → (∀ i, wR i ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) uL.1 uL.2) →
  ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r),
    x ∈ ((T.U j σ).X k).dom →
    ∃ x' : ((T.U j σ).X k).dom, (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm x'.1 τ' i'‖ = 1) ∧
      (∀ τ', ReciprocityTheory.ChartRestriction.G.FD.gram τ'.1 ((T.U j σ).X k).Gm (ReciprocityTheory.ChartRestriction.G.FD.mat x'.1 τ') =
        Matrix.diagonal fun a : Fin D.R.r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn ((T.U j σ).X k).p0 (a : ℕ) : ℝ) : ℂ)) ∧
      (∀ i, recNrm (T.U j σ) xR uL.1 uL.2 (wR i) k x'.1 = recNrm (T.U j σ) xR uL.1 uL.2 (wR i) k x) ∧
      ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x'.1 = ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x ∧
      ∃ (W : UnfAt (T.U j σ) k x') (Wu : UnitAt W) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) x'.1)
        (L : (Fin W.g → ℂ) →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim),
        TorusPins W Wu A L ∧ A.T.l2 1 A.s = 1 ∧
        ∃ (X' : ReciprocityTheory.ChartRestriction.G.I2.PT D.host.E)
          (e : ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim ≃ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp X'.dim), IsoPT A.T X' e ∧
          ∃ ρ : (Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ)) → ReciprocityTheory.ChartRestriction.G.I2.Idx X'.dim,
            (∀ y, e (L (Pi.single (W.e.symm y) 1)) =
              ((Real.sqrt (2 * xiR D) : ℝ) : ℂ) • EuclideanSpace.single (ρ y) (1 : ℂ)) ∧
            ∃ (nb : ℕ) (bs : Fin nb → ReciprocityTheory.ChartRestriction.G.I2.Block D.host.E n X'.dim),
              ReciprocityTheory.ChartRestriction.G.I2.Disj bs ∧
              MvPolynomial.rename (fun l : LtN (T.Q.Dw j) n =>
                ((l.2.2, ρ ⟨l.1, l.2.1⟩) : ReciprocityTheory.ChartRestriction.G.I2.Letter n X'.dim))
                  (MvPolynomial.map ((starRingEnd ℂ).comp σ) P₁) = ReciprocityTheory.ChartRestriction.G.I2.P1 bs ∧
              ReciprocityTheory.ChartRestriction.G.I2.DF bs = P₁.totalDegree ∧
              ∃ K, ReciprocityTheory.ChartRestriction.G.I2.IsReps A.T T.Q.l.M n (vspActL α) K

def GenContainA (nab : NabV (T.Q.Xo j) T.Q.c) (xR : ℝ) {N : ℕ} (wR : Fin (N + 1) → Rul (T.Q.Xo j) T.Q.c)
    (uL : WtR D.host.E) {n : ℕ} (P₁ : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (α : 𝓞 D.host.E) : Prop :=
  ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ((T.U j σ).X k).dom),
    (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm x.1 τ' i'‖ = 1) → ∀ (W : UnfAt (T.U j σ) k x)
    (Wu : UnitAt W) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) x.1)
    (L : (Fin W.g → ℂ) →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim), TorusPins W Wu A L →
    ∀ K : Finset (Fin n → ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim), ReciprocityTheory.ChartRestriction.G.I2.IsReps A.T T.Q.l.M n (vspActL α) K →
    ∃ jb : (Fin n → ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim) → Fin (N + 1), Set.InjOn jb K ∧
      ∀ b ∈ K, ∃ (xd x2 : Fin n → (T.Q.Dw j).La) (f : T.R j), IsThRule (T.Q.Xo j) T.Q.c nab xd P₁ f ∧
        (∀ b', x2 b' ∈ (Ideal.span {(2 : 𝓞 D.host.E)} *
          (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) ^ 2) •
            (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La)) ∧
        (∀ b', x2 b' - xd b' ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La)) ∧
        (∀ b', vspActL α (b b' - -((((T.Q.l.M : ℂ) ^ 2)⁻¹) •
          L (star (W.Pm (W.F.t (W.ik k) (T.Q.H.bar α • x2 b')))))) ∈ A.T.L) ∧
        (T.Q.l.M : ℝ) ^ ((P₁.totalDegree : ℝ) / 2) * (2 * Real.pi * xR) ^ (-(P₁.totalDegree : ℝ) / 2) *
            ‖toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un k x))‖ ≤
          recNrm (T.U j σ) xR uL.1 uL.2 (wR (jb b)) k x.1

def RunParA (th tableLineDegreeFive DF cc : ℝ) {n : ℕ} (P₁ : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) : Prop :=
  (P₁.totalDegree : ℝ) = DF ∧
  ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ((T.U j σ).X k).dom)
    (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) x.1) (X' : ReciprocityTheory.ChartRestriction.G.I2.PT D.host.E)
    (e : ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim ≃ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp X'.dim), IsoPT A.T X' e →
    ∀ (nb : ℕ) (bs : Fin nb → ReciprocityTheory.ChartRestriction.G.I2.Block D.host.E n X'.dim), ReciprocityTheory.ChartRestriction.G.I2.Disj bs →
    ReciprocityTheory.ChartRestriction.G.I2.DF bs = P₁.totalDegree →
    ∃ P : ReciprocityTheory.ChartRestriction.G.I2.Par X' (ReciprocityTheory.ChartRestriction.G.I2.DF bs), P.q = T.Q.l.M ∧
      ReciprocityTheory.ChartRestriction.G.I2.th (E := D.host.E) P.q P.R0 = th ∧
      (1 / 2 : ℝ) * ((ReciprocityTheory.ChartRestriction.G.I2.PT.f D.host.E : ℝ) * X'.r * n * Real.log P.q +
        n * (Real.log 24 + (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := D.host.E) P.m : ℝ) / 2 *
          Real.log (2 * (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := D.host.E) P.m : ℝ))) +
        (X'.r + 2) * Real.log 2) ≤ tableLineDegreeFive ∧
      ∃ PP : ℝ, 16200 * Real.pi * n * (P.m : ℝ) ^ 4 *
          (ReciprocityTheory.ChartRestriction.G.I2.dstar (E := D.host.E) P.m : ℝ) ^ 4 ≤ PP ∧
        cc = ReciprocityTheory.ChartRestriction.G.I2.RR (E := D.host.E) * PP * DF ^ 2 / P.q

def I2AtFramePointsAlpha : Prop :=
  ∀ (_hL : LawsP T) (_hj : InR D j) (nab : NabV (T.Q.Xo j) T.Q.c),
    (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c nab) →
    ∀ (w : WeightFamilies.Wt D j) (P₁ : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P₁ ∈ harmA T.Q.c (wtA w) w.n →
    IsBlockProd P₁ →
    ∀ (xR : ℝ) {N : ℕ} (wR : Fin (N + 1) → Rul (T.Q.Xo j) T.Q.c) (uL : WtR D.host.E) (th tableLineDegreeFive DF cc : ℝ),
    xR = xiR D → (∀ i, wR i ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) uL.1 uL.2) →
    ∀ α : 𝓞 D.host.E, IsAlphaM T α →
    ThetaValCAlphaSt → GenContainA T j nab xR wR uL P₁ α → FrameTieA T j xR wR uL th P₁ α →
    RunParA T j th tableLineDegreeFive DF cc P₁ →
    I2AtFramePoints (T.U j) xR wR uL th tableLineDegreeFive DF cc

end I2AtA

section EtA

variable {D : D7} {T : Top D} (h : LawsP T)

def EtProdA (r1 Nc nt : ℕ) : ∀ j i, (recB h.toLawsCore).Cusp j (wEt D j i) → Prop :=
  fun j i η => ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ((T.U j σ).X k).dom),
    (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm x.1 τ' i'‖ = 1) →
    ∃ (W : UnfAt (T.U j σ) k x) (Wu : UnitAt W) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) x.1)
      (L : (Fin W.g → ℂ) →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim), TorusPins W Wu A L ∧
      ∃ c : Fin (2 * r1 ^ 4 * i) → Fin nt → ℤ,
      ∃ a : Fin (2 * r1 ^ 4 * i) → Fin nt → Fin A.T.r → ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim,
      (∀ g t, |c g t| ≤ Nc) ∧ (∀ g t, TrOK A.T r1 (a g t)) ∧
      lieFac (T.Q.Dw j) (xiR D) (wtA (wEt D j i)) *
          ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA (wEt D j i)) (wEt D j i).n k) (rdU (T.U j σ) η.1 k) x.1 ≤
        ∏ g, ∑ t, |(c g t : ℝ)| * thRat A.T A.s (a g t)

def EtArchAlphaSt (th tableLineDegreeTwo : ℝ) (j i : ℕ) (η : (recB h.toLawsCore).Cusp j (wEt D j i)) (DF m r1 Nc nt : ℕ)
    (R0 : ℝ) : Prop :=
  th = ReciprocityTheory.ChartRestriction.G.I2.th (E := D.host.E) T.Q.l.M R0 → 2 ≤ r1 →
    EtNum D.host.E D.R.r T.Q.l.M m r1 Nc nt tableLineDegreeTwo → EtParRun T j DF T.Q.l.M m R0 →
    EtProdA h r1 Nc nt j i η → EtArch h th tableLineDegreeTwo j i η

end EtA

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j}

def ESecSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (y : PtsG G la → E.Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)) (g0 : B.Cusp j wF),
    Nonempty (CurveModel G la g0) →
    (∀ ζ, (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0) →
    ∃ (k : ℕ) (p q : Rp (xplus X E hM) la G.N),
      p ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k) ∧ q ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k) ∧
      (∀ β, β ≠ 0 → hasseRp (xplus X E hM) la G.N β p = 0) ∧
      (∀ β, β ≠ 0 → hasseRp (xplus X E hM) la G.N β q = 0) ∧
      ∀ ζ, (hw ζ).ev p ≠ 0 ∧ (hw ζ).ev q ≠ 0 ∧
        vV (hw ζ).T.V ((hw ζ).ev p) + vV (hw ζ).T.V ((hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0))) =
          vV (hw ζ).T.V ((hw ζ).ev q)

def LocStructSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (y : PtsG G la → E.Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)) (g0 : B.Cusp j wF),
    Nonempty (CurveModel G la g0) →
    (∀ ζ, (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0) →
    ∀ g : ↥(Frac0 (xplus X E hM) la G.w),
      (∀ ζ, 0 ≤ nval (hw ζ).T.V 1 ((hw ζ).toSecPt.lift (g : Lw (xplus X E hM) la G.w))) →
      ∃ (f d : ↥(Frac0 (xplus X E hM) la G.w)) (hd : ∀ ζ, (hw ζ).toSecPt.lift (d : Lw (xplus X E hM) la G.w) ≠ 0),
        toOsK (xplus X E hM) la G.w f = toOsK (xplus X E hM) la G.w d * toOsK (xplus X E hM) la G.w g ∧
        ∀ (l : List (Idx D j G.N →₀ ℕ)) (ζ : PtsG G la),
          0 ≤ nval (hw ζ).T.V 1 (evL (fun ζ => (hw ζ).toSecPt) ζ (hdList (fun ζ => (hw ζ).toSecPt) l
            (ιW (fun ζ => (hw ζ).toSecPt) (f : Lw (xplus X E hM) la G.w) *
              ↑(isUnit_of_lift_ne (fun ζ => (hw ζ).toSecPt) hd).unit⁻¹)))

theorem locRing_of {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}
    (h1 : ESecSt G la) (h2 : LocStructSt G la) : LocRingSt G la :=
  fun y hw g0 hC hg0 => ⟨h1 y hw g0 hC hg0, h2 y hw g0 hC hg0⟩

section Inst

variable {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)

def ValSepSt {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) : Prop :=
  ∀ (y : PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)),
    ∃ (Zc : PtsG G la → Comp (T.Q.Xo j) T.Q.c) (ι : ∀ ζ, Om (Zc ζ) →+* (hw ζ).T.Fr),
      (∀ ζ, ∃ a : Om (Zc ζ), vV (hw ζ).T.V (ι ζ a) = 1) ∧
      (∀ ζ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w),
        evC hG (Zc ζ) ((F : (recB h.toLawsCore).Cusp j w) : T.R j) = 0 →
          (hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) = 0) ∧
      (∀ ζ (w : WeightFamilies.Wt D j) (F F' : (recB h.toLawsCore).Cusp j w),
        ι ζ (evC hG (Zc ζ) ((F : (recB h.toLawsCore).Cusp j w) : T.R j)) *
            (hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F')) =
          ι ζ (evC hG (Zc ζ) ((F' : (recB h.toLawsCore).Cusp j w) : T.R j)) *
            (hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F))) ∧
      ∀ ζ ζ', ζ ≠ ζ' → Zc ζ = Zc ζ' →
        ∃ (w : WeightFamilies.Wt D j) (F F' : (recB h.toLawsCore).Cusp j w),
          (hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F')) ≠ 0 ∧
          (hw ζ').ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F')) ≠ 0 ∧
          nval (hw ζ).T.V 1 ((hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F'))) <
            nval (hw ζ).T.V 1 ((hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F))) ∧
          nval (hw ζ').T.V 1 ((hw ζ').ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F'))) <
            nval (hw ζ').T.V 1 ((hw ζ').ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) -
              (hw ζ').ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F')))

end Inst

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.UnifGam
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

theorem eq_zero_of_trace_int {z : E} (h : ∀ c : 𝓞 E, Algebra.trace ℚ E ((c : E) * z) = 0) : z = 0 := by
  refine (traceForm_nondegenerate ℚ E).1 z fun n => ?_
  rw [Algebra.traceForm_apply, ← (integralBasis E).sum_repr n, Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mul_smul_comm, map_smul, integralBasis_apply, mul_comm z]
  have := h (RingOfIntegers.basis E i)
  rw [RingOfIntegers.coe_eq_algebraMap] at this
  rw [this, smul_zero]

theorem smul_coord (x : 𝓞 E) (w : Fin r → E) (a : Fin r) : (x • w) a = (x : E) * w a := by
  simp [Algebra.smul_def]

end Lat

section Herm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_smul_left (G : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (u w : Fin r → E) :
    herm G (c • u) w = (c : E) * herm G u w := by
  simp only [herm, smul_coord, Finset.mul_sum, mul_assoc]

theorem herm_smul_right (G : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (u w : Fin r → E) :
    herm G u (c • w) = cc (c : E) * herm G u w := by
  simp only [herm, smul_coord, Finset.mul_sum, cc, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem herm_mulVec_smul (G : Matrix (Fin r) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (u : Fin r → E) :
    γ *ᵥ (c • u) = c • (γ *ᵥ u) := Matrix.mulVec_smul γ c u

end Herm

section Gam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {r : ℕ}

end Gam

end Formalism.L2.Pj
end
end

