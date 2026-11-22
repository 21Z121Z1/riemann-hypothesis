import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ExistsSmallMemIdeal
import Formalism.FrobeniusOrbits.HostCorollaries

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameC
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.AnFrameC

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj

section Form

variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)

theorem hermForm_add_left (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  unfold hermForm
  rw [add_dotProduct]

theorem hermForm_add_right (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  unfold hermForm
  rw [star_add, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_zero_left (w : Fin g → ℂ) : hermForm Hm 0 w = 0 := by
  unfold hermForm
  rw [zero_dotProduct]

theorem hermForm_zero_right (z : Fin g → ℂ) : hermForm Hm z 0 = 0 := by
  unfold hermForm
  rw [star_zero, Matrix.mulVec_zero, dotProduct_zero]

theorem hermForm_swap (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = star (hermForm Hm z w) := by
  unfold hermForm dotProduct Matrix.mulVec dotProduct
  simp only [Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hH.apply i j, star_star]
  ring

def rho (z l : Fin g → ℂ) : ℝ := Real.pi * (hermForm Hm z l).re + Real.pi / 2 * (hermForm Hm l l).re

def lam2 (x y l m : Fin g → ℂ) : ℝ := rho Hm (x + y) (l + m) - rho Hm x l - rho Hm y m

theorem rho_zero : rho Hm 0 0 = 0 := by
  simp [rho, hermForm_zero_left]

theorem cube_rho (z l : Fin 3 → Fin g → ℂ) :
    ∑ I : Finset (Fin 3), ((-1 : ℝ) ^ (3 - I.card)) * rho Hm (∑ i ∈ I, z i) (∑ i ∈ I, l i) = 0 := by
  have hu : (Finset.univ : Finset (Fin 3)) = insert 0 (insert 1 (insert 2 ∅)) := by decide
  rw [← Finset.powerset_univ, hu]
  simp only [Finset.sum_powerset_insert (show (0 : Fin 3) ∉ insert 1 (insert 2 (∅ : Finset (Fin 3))) by decide),
    Finset.sum_powerset_insert (show (1 : Fin 3) ∉ insert 2 (∅ : Finset (Fin 3)) by decide),
    Finset.sum_powerset_insert (show (2 : Fin 3) ∉ (∅ : Finset (Fin 3)) by decide), Finset.powerset_empty,
    Finset.sum_singleton]
  simp [Finset.sum_insert, Finset.card_insert_of_notMem]
  simp only [rho, hermForm_add_left, hermForm_add_right, hermForm_zero_left, hermForm_zero_right,
    Complex.add_re, Complex.zero_re]
  norm_num
  ring

theorem prim_rho (A Ab : (Fin g → ℂ) → (Fin g → ℂ)) (hA : ∀ z w, hermForm Hm (A z) w = hermForm Hm z (Ab w))
    (hs : ∀ z, A z + Ab z = z) (z l : Fin g → ℂ) :
    lam2 Hm z (A z) l (A l) = rho Hm z l := by
  have e1 : hermForm Hm z (A l) + hermForm Hm z (Ab l) = hermForm Hm z l := by
    rw [← hermForm_add_right, hs]
  have e2 : hermForm Hm l (A l) + hermForm Hm l (Ab l) = hermForm Hm l l := by
    rw [← hermForm_add_right, hs]
  have r1 := congrArg Complex.re e1
  have r2 := congrArg Complex.re e2
  simp only [Complex.add_re] at r1 r2
  simp only [lam2, rho, hermForm_add_left, hermForm_add_right, hA, Complex.add_re]
  linear_combination Real.pi * r1 + Real.pi / 2 * r2

theorem ad_rho (A Ab : (Fin g → ℂ) → (Fin g → ℂ)) (hA : ∀ z w, hermForm Hm (A z) w = hermForm Hm z (Ab w))
    (hAb : ∀ z w, hermForm Hm (Ab z) w = hermForm Hm z (A w)) (x z l m : Fin g → ℂ) :
    lam2 Hm (A x) z (A l) m = lam2 Hm x (Ab z) l (Ab m) := by
  simp only [lam2, rho, hermForm_add_left, hermForm_add_right, Complex.add_re, hA, hAb]
  ring

theorem adj_symm (hH : Hm.IsHermitian) (A Ab : (Fin g → ℂ) → (Fin g → ℂ))
    (hA : ∀ z w, hermForm Hm (A z) w = hermForm Hm z (Ab w)) (z w : Fin g → ℂ) :
    hermForm Hm (Ab z) w = hermForm Hm z (A w) := by
  rw [hermForm_swap Hm hH, ← hA, ← hermForm_swap Hm hH]

end Form

section Compat

variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)

theorem hermForm_smul_left (c : ℂ) (z w : Fin g → ℂ) : hermForm Hm (c • z) w = c * hermForm Hm z w := by
  unfold hermForm
  rw [smul_dotProduct, smul_eq_mul]

theorem hermForm_smul_right (c : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z (c • w) = star c * hermForm Hm z w := by
  unfold hermForm
  rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem real_smul_eq (r : ℝ) (z : Fin g → ℂ) : r • z = (r : ℂ) • z := by
  funext i
  simp [Complex.real_smul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def tyAct (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (z : Fin g → ℂ) : Fin g → ℂ := fun i => ty i (a : E) * z i

theorem tyAct_add (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (u v : Fin g → ℂ) :
    tyAct ty a (u + v) = tyAct ty a u + tyAct ty a v := by
  funext i
  simp only [tyAct, Pi.add_apply, mul_add]

theorem tyAct_smul (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (c : ℂ) (u : Fin g → ℂ) :
    tyAct ty a (c • u) = c • tyAct ty a u := by
  funext i
  simp only [tyAct, Pi.smul_apply, smul_eq_mul]
  ring

theorem tyAct_zero (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) : tyAct ty a 0 = 0 := by
  funext i
  simp [tyAct]

variable {H : Host E} (D : Datum H) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ))

theorem im_hermForm_act (hP : IsPeriod D ty P) (hc1 : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y)
    (a : 𝓞 E) (u v : Fin g → ℂ) :
    (hermForm Hm (tyAct ty a u) v).im = (hermForm Hm u (tyAct ty (H.bar a) v)).im := by
  have hTP : ∀ (b : 𝓞 E) x, tyAct ty b (P x) = P (b • x) := fun b x => funext fun i => (hP.1 b x i).symm
  have hspan : ∀ w : Fin g → ℂ, w ∈ Submodule.span ℝ (Set.range P) := fun w => by
    rw [hP.2.2.2.1]; trivial
  have base : ∀ x y, (hermForm Hm (tyAct ty a (P x)) (P y)).im =
      (hermForm Hm (P x) (tyAct ty (H.bar a) (P y))).im := by
    intro x y
    rw [hTP, hTP, hc1, hc1, D.adj]
  have step1 : ∀ x (w : Fin g → ℂ), (hermForm Hm (tyAct ty a (P x)) w).im =
      (hermForm Hm (P x) (tyAct ty (H.bar a) w)).im := by
    intro x w
    induction hspan w using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, rfl⟩ := hw
      exact base x y
    | zero => simp [tyAct_zero, hermForm_zero_right]
    | add w w' _ _ h1 h2 =>
      rw [hermForm_add_right, tyAct_add, hermForm_add_right, Complex.add_im, Complex.add_im, h1, h2]
    | smul r w _ h =>
      rw [real_smul_eq, hermForm_smul_right, tyAct_smul, hermForm_smul_right, Complex.mul_im, Complex.mul_im, h]
      simp
  induction hspan u using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, rfl⟩ := hu
    exact step1 x v
  | zero => simp [tyAct_zero, hermForm_zero_left]
  | add u u' _ _ h1 h2 =>
    rw [tyAct_add, hermForm_add_left, hermForm_add_left, Complex.add_im, Complex.add_im, h1, h2]
  | smul r u _ h =>
    rw [real_smul_eq, tyAct_smul, hermForm_smul_left, hermForm_smul_left, Complex.mul_im, Complex.mul_im, h]
    simp

theorem hermForm_act (hP : IsPeriod D ty P) (hc1 : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y)
    (a : 𝓞 E) (u v : Fin g → ℂ) :
    hermForm Hm (tyAct ty a u) v = hermForm Hm u (tyAct ty (H.bar a) v) := by
  apply Complex.ext
  · have h := im_hermForm_act Hm D ty P hP hc1 a (Complex.I • u) v
    rw [tyAct_smul, hermForm_smul_left, hermForm_smul_left, Complex.mul_im, Complex.mul_im] at h
    simpa using h
  · exact im_hermForm_act Hm D ty P hP hc1 a u v

end Compat

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem norm_fr_add {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} {W : UnfAt U k x} (Wu : UnitAt W)
    (a : _) (j : Xo.univ.t.PP.L.ι) (z : Fin W.g → ℂ)
    (h : ⊤ ≤ (W.F.ex (W.ik k) W.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j) :
    ‖Wu.fr j (z + W.Pm a)‖ = ‖Wu.fr j z‖ * Real.exp (-rho Wu.Hm z (W.Pm a)) := by
  obtain ⟨h1, h2⟩ := Wu.c6 a j z
  have hre : ((Real.pi : ℂ) * hermForm Wu.Hm z (W.Pm a) +
      (Real.pi : ℂ) / 2 * hermForm Wu.Hm (W.Pm a) (W.Pm a)).re = rho Wu.Hm z (W.Pm a) := by
    simp only [rho, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat_re,
      Complex.div_ofNat_im, zero_mul, sub_zero, zero_div]
  rw [h2 h, norm_mul, norm_mul, h1, one_mul, Complex.norm_exp, hre, mul_comm, ← mul_assoc, ← Real.exp_add,
    neg_add_cancel, Real.exp_zero, one_mul]

abbrev tyW {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x) : Fin W.g → (E →+* ℂ) :=
  fun j => relab c σ (W.e j).1

theorem unit_hermForm_act {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} {W : UnfAt U k x} (Wu : UnitAt W)
    (a : 𝓞 E) (z w : Fin W.g → ℂ) :
    hermForm Wu.Hm (tyAct (tyW W) a z) w = hermForm Wu.Hm z (tyAct (tyW W) (H.bar a) w) :=
  hermForm_act Wu.Hm (W.F.Di (W.ik k)) (tyW W) W.Pm W.per Wu.c1 a z w

theorem unit_prim_rho {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} {W : UnfAt U k x} (Wu : UnitAt W)
    (z l : Fin W.g → ℂ) :
    lam2 Wu.Hm z (tyAct (tyW W) H.w0 z) l (tyAct (tyW W) H.w0 l) = rho Wu.Hm z l := by
  refine prim_rho Wu.Hm _ (tyAct (tyW W) (H.bar H.w0)) (unit_hermForm_act Wu H.w0) (fun z => ?_) z l
  funext i
  simp only [tyAct, Pi.add_apply, ← add_mul]
  have h := congrArg (fun t : 𝓞 E => tyW W i (t : E)) (CVA.cmHostUnit_add_conj_eq_one H)
  push_cast at h
  simp only [map_add, map_one] at h
  rw [h, one_mul]

theorem unit_ad_rho {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} {W : UnfAt U k x} (Wu : UnitAt W)
    (a : 𝓞 E) (y z l m : Fin W.g → ℂ) :
    lam2 Wu.Hm (tyAct (tyW W) a y) z (tyAct (tyW W) a l) m =
      lam2 Wu.Hm y (tyAct (tyW W) (H.bar a) z) l (tyAct (tyW W) (H.bar a) m) :=
  ad_rho Wu.Hm _ _ (unit_hermForm_act Wu a)
    (adj_symm Wu.Hm Wu.herm _ _ (unit_hermForm_act Wu a)) y z l m

end Frame

end ReciprocityTheory.ChartRestriction.G.PullbackSections.AnFrameC
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

section Letters

variable {T : Type} [Fintype T] (rr : T → ℕ) (n : ℕ)

def colL (m : Formalism.L2.Pj.Letter T rr n →₀ ℕ) (b : Fin n) : (Σ τ : T, Fin (rr τ)) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun ℓ => m ⟨ℓ.1, ℓ.2, b⟩

theorem colM_lEq_colL (m : Formalism.L2.Pj.Letter T rr n →₀ ℕ) (b : Fin n) :
    colM (m.mapDomain (CVA.lEq (T := T) (r := rr) (n := n))) b = colL rr n m b := by
  ext ℓ
  show Finsupp.mapDomain CVA.lEq m (CVA.lEq ⟨ℓ.1, ℓ.2, b⟩) = m ⟨ℓ.1, ℓ.2, b⟩
  rw [Finsupp.mapDomain_apply CVA.lEq.injective]

end Letters

section Main

variable {R k : Type} [CommRing R] [Field k] [Algebra ℚ k] [Algebra R k]

set_option maxHeartbeats 1000000 in
theorem chartValJ (hRQ : IsRQ (R := R) k) (J : Submodule R k) (hJ1 : (1 : k) ∈ J)
    {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O) (h : PS k 2 d) (hg : B.IsCanonGauge k h)
    (w0 : O) (hw0 : w0 + star w0 = 1) (m : ℕ)
    {T : Type} [Fintype T] (rr : T → ℕ) (cc : T → T) (hcc : ∀ τ, cc (cc τ) = τ) (isX : T → Prop)
    (hX : ∀ τ, isX τ ∨ isX (cc τ))
    {π : Type} [Fintype π] [DecidableEq π] (c : T → π) (s : T → Bool)
    (hcs : ∀ τ, c (cc τ) = c τ ∧ s (cc τ) ≠ s τ)
    (u φ : (Σ τ : T, Fin (rr τ)) → Fin d → R) (ψ : (Σ τ : T, Fin (rr τ)) → Fin d → k) (hψ : ∀ ℓ i, ψ ℓ i ∈ J)
    (heig : ∀ ℓ ℓ' : (Σ τ : T, Fin (rr τ)), ℓ'.1 ≠ cc ℓ.1 →
      ∑ i, (algebraMap R k (φ ℓ' i) + ψ ℓ' i - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ' j)) i) *
        algebraMap R k (u ℓ i) = 0)
    (h21a : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1)
      (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
        fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i))
      (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
        fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i)))
    (h21b : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (0, ψ ℓ))
      (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
        fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i)))
    (h21c : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1)
      (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
        fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i))
      (fun ℓ => (0, ψ ℓ)))
    (n : ℕ) (a : T → ℕ → ℕ) (P : MvPolynomial (Formalism.L2.Pj.Letter T rr n) k)
    (hP : P ∈ Formalism.L2.Pj.HaO rr n k (algebraMap R k).range cc isX a)
    (e : ℕ) (he : ∀ mo ∈ P.support, ∑ b, pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1)
      (colL rr n mo b) ≤ e)
    (f : Fin n → PS k 1 d) (hf : ∀ b, IntAA (R := R) k (f b)) :
    ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal k h w0 m (f b) (fun ℓ j => algebraMap R k (u ℓ j))
      (MvPolynomial.monomial (colL rr n mo b) 1) ∈ J ^ e := by
  classical
  set uK : (Σ τ : T, Fin (rr τ)) → Fin d → k := fun ℓ j => algebraMap R k (u ℓ j) with huK
  set φK : (Σ τ : T, Fin (rr τ)) → Fin d → k :=
    fun ℓ i => algebraMap R k (φ ℓ i) + ψ ℓ i - (sg1 k h).mulVec (uK ℓ) i with hφK
  set g : Fin n → PS k 1 d := fun b => FB.expS k ((m : k) • B.hL k h w0) * f b with hgdef
  set P2 := MvPolynomial.rename (CVA.lEq (T := T) (r := rr) (n := n)) P with hP2

  have hvan : ∀ ℓ ℓ' : (Σ τ : T, Fin (rr τ)), ℓ'.1 ≠ cc ℓ.1 → ∑ i, φK ℓ' i * uK ℓ i = 0 := fun ℓ ℓ' hne => heig ℓ ℓ' hne
  have hpair : ∀ ℓ ℓ' : (Σ τ : T, Fin (rr τ)), ℓ'.1 = cc ℓ.1 → (c ℓ.1 = c ℓ'.1 ∧ s ℓ.1 ≠ s ℓ'.1) := by
    intro ℓ ℓ' he'
    rw [he']
    exact ⟨(hcs ℓ.1).1.symm, (hcs ℓ.1).2.symm⟩
  have hL1 : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (uK ℓ, 0))
      (fun ℓ => (uK ℓ, 0)) := by
    intro l l' _
    simp [betaH]
  have hL2 : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (uK ℓ, 0))
      (fun ℓ => (0, φK ℓ)) := by
    intro l l' hnot
    by_cases hl : l'.1 = cc l.1
    · exact absurd (hpair l l' hl) hnot
    · simp only [betaH, Pi.zero_apply, zero_mul, sub_zero]
      exact hvan l l' hl
  have hL3 : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (0, φK ℓ))
      (fun ℓ => (uK ℓ, 0)) := by
    intro l l' hnot
    by_cases hl : l.1 = cc l'.1
    · exfalso
      apply hnot
      have := hpair l' l hl
      exact ⟨this.1.symm, this.2.symm⟩
    · simp only [betaH, Pi.zero_apply, mul_zero, zero_sub, Finset.sum_neg_distrib, neg_eq_zero]
      exact hvan l' l hl

  have hharm := CVA.harm_rename (r := rr) (n := n) cc isX P hP.1.1

  set cfun : (Σ τ : T, Fin (rr τ)) → (Σ τ : T, Fin (rr τ)) → k := fun l l' =>
    if c l.1 = c l'.1 ∧ s l.1 = true ∧ s l'.1 = false then (m : k) * betaH k (0, φK l) (uK l', 0) else 0
    with hcfun
  have hcvan : ∀ l l' : (Σ τ : T, Fin (rr τ)), l'.1 ≠ cc l.1 → cfun l l' = 0 := by
    intro l l' hne
    have hne' : l.1 ≠ cc l'.1 := fun h' => hne (by rw [h', hcc])
    have hz : betaH k (0, φK l) (uK l', 0) = 0 := by
      simp only [betaH, Pi.zero_apply, mul_zero, zero_sub, Finset.sum_neg_distrib, neg_eq_zero]
      exact hvan l' l hne'
    simp only [hcfun, hz, mul_zero, ite_self]
  have hso := harmSecond_holds k T rr cc isX hcc hX n cfun hcvan P2 hharm
  have hfun : (fun p q : (Σ τ : T, Fin (rr τ)) × Fin n =>
      if p.2 = q.2 ∧ c p.1.1 = c q.1.1 ∧ s p.1.1 = true ∧ s q.1.1 = false then
        (m : k) * betaH k (0, φK p.1) (uK q.1, 0) else 0) =
      (fun p q : (Σ τ : T, Fin (rr τ)) × Fin n => if p.2 = q.2 then cfun p.1 q.1 else 0) := by
    funext p q
    by_cases h1 : p.2 = q.2 <;> simp [h1, hcfun]
  have hso' : secondOrder k (fun p q : (Σ τ : T, Fin (rr τ)) × Fin n =>
      if p.2 = q.2 ∧ c p.1.1 = c q.1.1 ∧ s p.1.1 = true ∧ s q.1.1 = false then
        (m : k) * betaH k (0, φK p.1) (uK q.1, 0) else 0) P2 = 0 := by
    rw [hfun]
    exact hso

  have hLH := TB.WickVanishing.Closed.lemma_H_columns R d O k B h hg.ax0 m (Σ τ : T, Fin (rr τ)) π (fun ℓ => c ℓ.1) (fun ℓ => s ℓ.1)
    uK φK hL1 hL2 hL3 n P2 hso' g

  set ξh : (Σ τ : T, Fin (rr τ)) → (Fin d → k) × (Fin d → k) := fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
      fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i) with hξh
  have hxi : (fun ℓ => ξh ℓ + ((0 : Fin d → k), ψ ℓ)) = fun ℓ => (uK ℓ, φK ℓ) := by
    funext ℓ
    refine Prod.ext ?_ ?_
    · funext j
      simp [hξh, huK]
    · funext i
      simp only [hξh, Prod.snd_add, Pi.add_apply, hφK, huK]
      ring
  have he2 : ∀ mo ∈ P2.support, ∑ b, pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1)
      (colM mo b) ≤ e := by
    intro mo hmo
    rw [hP2, MvPolynomial.support_rename_of_injective CVA.lEq.injective] at hmo
    obtain ⟨mo0, hmo0, rfl⟩ := Finset.mem_image.1 hmo
    simp only [colM_lEq_colL]
    exact he mo0 hmo0
  have hSC := TB.WickVanishing.Closed.scaled_connection_columns R d O k hRQ J hJ1 B h hg w0 hw0 m (Σ τ : T, Fin (rr τ)) π (fun ℓ => c ℓ.1)
    (fun ℓ => s ℓ.1) ξh ψ (fun ℓ => ⟨u ℓ, φ ℓ, rfl⟩) hψ h21a h21b h21c n P2
    (CVA.coeff_rename_mem _ P hP.2) e he2 f hf
  rw [hxi] at hSC
  have hchain : ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal k h w0 m (f b) uK
      (MvPolynomial.monomial (colL rr n mo b) 1) =
      ∑ mo ∈ P2.support, P2.coeff mo * ∏ b, constantCoeff (ordNabla k B h m (fun ℓ => s ℓ.1)
        (fun ℓ => (uK ℓ, φK ℓ)) (MvPolynomial.monomial (colM mo b) 1) (liftX k (g b))) := by
    rw [hLH, hP2, CVA.sum_rename]
    refine Finset.sum_congr rfl fun mo _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [colM_lEq_colL]
    simp only [FB.nabVal, hgdef]
    rw [mul_comm]
  rw [hchain]
  have hg' : g = fun b => FB.expS k ((m : k) • B.hL k h w0) * f b := hgdef
  rw [hg']
  exact hSC

end Main

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatIn
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open scoped Pointwise

theorem absNorm_smul_eq {E : Type} [Field E] [NumberField E] (σ : E ≃ₐ[ℚ] E) (I : Ideal (𝓞 E)) :
    Ideal.absNorm (σ • I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I (σ • I) (MulSemiringAction.toRingEquiv _ _ σ)
    (by rw [Ideal.pointwise_smul_def]; rfl)).toEquiv).symm

theorem halfDiffNorm : HalfDiffNormSt := by
  intro D
  obtain ⟨hspec, -⟩ := D.host.𝔟_spec

  have hN : Ideal.absNorm (differentIdeal (𝓞 ↥D.host.K) (𝓞 D.host.E)) =
      Ideal.absNorm D.host.𝔟 ^ 2 := by
    rw [hspec, map_mul, absNorm_smul_eq, sq]

  have htow := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 ↥D.host.K) (𝓞 D.host.E)
  have hne : differentIdeal ℤ (𝓞 D.host.E) ≠ ⊥ := differentIdeal_ne_bot
  have hdisc : Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.E)) = (discr D.host.E).natAbs :=
    NumberField.absNorm_differentIdeal D.host.E (𝓞 D.host.E)
  have hrel0 : differentIdeal (𝓞 ↥D.host.K) (𝓞 D.host.E) ≠ ⊥ := by
    intro h
    apply hne
    rw [htow, h]
    simp
  have hle : Ideal.absNorm (differentIdeal (𝓞 ↥D.host.K) (𝓞 D.host.E)) ≤ (discr D.host.E).natAbs := by
    rw [← hdisc, htow, map_mul]
    apply Nat.le_mul_of_pos_right
    rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    intro h
    apply hne
    rw [htow, h]
    simp
  have hpos2 : 0 < Ideal.absNorm D.host.𝔟 ^ 2 := by
    rw [← hN, Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact hrel0
  have hpos : 0 < Ideal.absNorm D.host.𝔟 := pos_of_ne_zero fun h => by simp [h] at hpos2
  refine ⟨hpos, ?_⟩
  have hsq : ((Ideal.absNorm D.host.𝔟 : ℕ) : ℝ) ^ 2 ≤ |((discr D.host.E : ℤ) : ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    exact_mod_cast hN ▸ hle
  have hlog := Real.log_pow ((Ideal.absNorm D.host.𝔟 : ℕ) : ℝ) 2
  push_cast at hlog
  rw [← hlog]
  exact Real.log_le_log (by positivity) hsq

theorem bb_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h0 := (halfDiffNorm D).1
  rw [h, Ideal.absNorm_bot] at h0
  exact lt_irrefl 0 h0

theorem absNorm_bb_sq_le (D : D7) : Ideal.absNorm D.host.𝔟 ^ 2 ≤ (discr D.host.E).natAbs := by
  obtain ⟨h0, hl⟩ := halfDiffNorm D
  have hd : (0 : ℝ) < |((discr D.host.E : ℤ) : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast NumberField.discr_ne_zero D.host.E
  have hN : (0 : ℝ) < (Ideal.absNorm D.host.𝔟 : ℝ) := by exact_mod_cast h0
  have key : (Ideal.absNorm D.host.𝔟 : ℝ) ^ 2 ≤ |((discr D.host.E : ℤ) : ℝ)| := by
    rw [← Real.log_le_log_iff (by positivity) hd, Real.log_pow]
    push_cast
    linarith
  have h2 : ((discr D.host.E).natAbs : ℝ) = |((discr D.host.E : ℤ) : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have h3 : ((Ideal.absNorm D.host.𝔟 ^ 2 : ℕ) : ℝ) ≤ ((discr D.host.E).natAbs : ℝ) := by
    rw [h2]
    push_cast
    exact key
  exact_mod_cast h3

theorem finrank_E (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  haveI := D.host.galois
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr D.host.gal.toEquiv]
  simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n, Formalism.HC.Frame.GG, Nat.card_prod]
  have h2 : Nat.card ℤˣ = 2 := by
    first
      | rw [Nat.card_eq_fintype_card, Int.card_units_eq_two]
      | simp
      | (rw [Nat.card_eq_fintype_card]; rfl)
      | (rw [Nat.card_eq_fintype_card]; decide)
  have hA : Nat.card D.R.MA = D.R.ord := by
    unfold Formalism.HC.Frame.MA
    rw [Nat.card_congr Multiplicative.toAdd]
    unfold Formalism.HC.Frame.A Formalism.HC.Idx
    exact Nat.card_fin _
  rw [h2, hA]
  ring

end ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI
end
end

