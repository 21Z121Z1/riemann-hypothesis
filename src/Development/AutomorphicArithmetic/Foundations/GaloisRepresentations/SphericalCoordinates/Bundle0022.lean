import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0017
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.Bundle0002
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0019

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PArchEx
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.archEx_of :
    UpperTheory.Gal.W2.FMat → UpperTheory.Gal.W2.FForm → UpperTheory.Gal.W2.SN → UpperTheory.Gal.W2.ArchSpan → UpperTheory.Gal.W2.ArchEx := by
  intro hFM hFF hSN hAS p _ D G L hm
  obtain ⟨kp, σ, hk⟩ := hFM p D G L hm
  obtain ⟨A, hdet, hskew, hform, hcomm⟩ := hFF p D G L kp σ hk
  choose S lam hS hpsi hconj hAv using fun v => UpperTheory.exists_hermitian_diagonalization_at_infinitePlace_of_skewHermitian p G σ A hSN hdet hskew hcomm v
  let th : VQ D →+ Arch G :=
    { toFun := fun w v => S v *ᵥ fun i => v.embedding (kp w i)
      map_zero' := by
        funext v
        simp
        exact Matrix.mulVec_zero _
      map_add' := fun x y => by
        funext v
        have : (fun i => v.embedding (kp (x + y) i)) = (fun i => v.embedding (kp x i)) + (fun i => v.embedding (kp y i)) := by
          funext i; simp
        simp only [this, Matrix.mulVec_add]
        rfl }
  have hth : ∀ w v, th w v = S v *ᵥ fun i => v.embedding (kp w i) := fun _ _ => rfl
  have hact : ∀ (c : G.C) w v, th (L.rep c w) v = G.psi v c *ᵥ th w v := by
    intro c w v
    rw [hth, hth, Matrix.mulVec_mulVec, hpsi, ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    rw [hk c w]
    simp [Matrix.mulVec, dotProduct, map_sum]
  have hform' : ∀ u w, ((D.EF.baseChange ℚ u w : ℚ) : ℝ) = ∑ v, 2 * (lam v * hv (G.gram v) (th u v) (th w v)).re := by
    intro u w
    rw [hform u w]
    exact UpperTheory.trace_conj_dotProduct_eq_sum_infinitePlaces G.F G.n hAS A S G.gram lam hS hAv (kp u) (kp w)
  have hspan : Submodule.span ℝ (Set.range th) = ⊤ := by
    rw [← UpperTheory.span_real_matrix_mulVec_infinitePlace_embedding_eq_top G.F G.n hAS S hS]
    congr 1
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨kp w, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨kp.symm x, by funext v; simp [hth]⟩
  have hpos := UpperTheory.re_mul_signature_I_pos_of_hermitian_trace_formula p D G L th lam hact hform' hspan hconj
  obtain ⟨hd1, hd2⟩ := UpperTheory.finrank_archimedean_eq_two_mul_dim p D G L hm hAS
  have hs2 : ∀ v, sgnV L v * sgnV L v = 1 := by
    intro v
    unfold sgnV
    split_ifs <;> simp
  have hlamim : ∀ v, lam v = ((lam v * sgnV L v * Complex.I).re : ℂ) * (-(sgnV L v) * Complex.I) := by
    intro v
    have hre : (lam v).re = 0 := by
      have := congrArg Complex.re (hconj v)
      simp at this
      linarith
    have hreal : (lam v * sgnV L v * Complex.I).im = 0 := by
      unfold sgnV
      split_ifs <;> simp [hre]
    have hc : ((lam v * sgnV L v * Complex.I).re : ℂ) = lam v * sgnV L v * Complex.I := by
      apply Complex.ext <;> simp [hreal]
    rw [hc]
    have := hs2 v
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (lam v * Complex.I * Complex.I) * this + lam v * hI
  exact ⟨{
    th := th
    r := fun v => 2 * (lam v * sgnV L v * Complex.I).re
    r_pos := fun v => by have := hpos v; linarith
    act := hact
    form := by
      intro u w
      rw [hform' u w]
      refine Finset.sum_congr rfl fun v _ => ?_
      show 2 * (lam v * hv (G.gram v) (th u v) (th w v)).re = 2 * (lam v * sgnV L v * Complex.I).re * (-(sgnV L v) * Complex.I * hv (G.gram v) (th u v) (th w v)).re
      conv_lhs => rw [hlamim v, mul_assoc ((lam v * sgnV L v * Complex.I).re : ℂ), Complex.re_ofReal_mul]
      ring
    span := hspan
    dim := hd1
    dimg := hd2 }⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

def FTrace : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (x : G.F), ((Algebra.trace ℚ G.F x : ℚ) : ℚ_[p]) = ∑ w, Algebra.trace ℚ_[p] (G.Fw w) (G.embW w x) +
    ∑ w, Algebra.trace ℚ_[p] (G.Fw w) (G.embW w (IsCMField.complexConj G.F x))

def FInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (x : G.F), (∀ w, ‖(G.embW w x : PadicAlgCl p)‖ ≤ 1 ∧ ‖(G.embW w (IsCMField.complexConj G.F x) : PadicAlgCl p)‖ ≤ 1) →
    ∃ (m : ℕ) (c : 𝓞 G.F), m.Coprime p ∧ (c : G.F) = m * x

def EmbAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (τ : G.F →+* PadicAlgCl p), ∃ (w : Fin G.m) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
    (∀ x, τ x = σ (G.emb w x)) ∨ ∀ x, τ x = σ (G.emb w (IsCMField.complexConj G.F x))

def FApprox : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (a b : ∀ w : Fin G.m, G.Fw w) (e : ℝ), 0 < e → ∃ x : G.F, ∀ w, ‖((G.embW w x - a w : G.Fw w) : PadicAlgCl p)‖ < e ∧
    ‖((G.embW w (IsCMField.complexConj G.F x) - b w : G.Fw w) : PadicAlgCl p)‖ < e

def TrDual : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (w : Fin G.m), ∃ d : G.Fw w, d ≠ 0 ∧ ∀ a : G.Fw w,
    (∀ z : G.Fw w, ‖(z : PadicAlgCl p)‖ ≤ 1 → ‖Algebra.trace ℚ_[p] (G.Fw w) (a * z)‖ ≤ 1) ↔ ‖((a * d : G.Fw w) : PadicAlgCl p)‖ ≤ 1

def KpMem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (g : Gp G), inclG G 1 g ∈ KHT p G.m G.n 1 G.Fw ↔ IntPt g

def LocLat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (w : Fin G.m) (s : Finset (Fin G.n → G.Fw w)), Submodule.span (G.Fw w) (s : Set (Fin G.n → G.Fw w)) = ⊤ →
    ∃ g : GL (Fin G.n) (G.Fw w), ∀ z : Fin G.n → G.Fw w,
      (∀ i, ‖(((((g⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ z) i : G.Fw w) : PadicAlgCl p)‖ ≤ 1) ↔
        ∃ a : (Fin G.n → G.Fw w) → G.Fw w, (∀ y, ‖(a y : PadicAlgCl p)‖ ≤ 1) ∧ z = ∑ y ∈ s, a y • y

def PFrameEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.m = 1 → ∀ β : G.Cˣ, sh G β = β → Nonempty (PFrame L β)

def PLatOf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (M : AddSubgroup (VQ D)) (s : Finset (VQ D)) (k : ℕ), Submodule.span ℚ (s : Set (VQ D)) = ⊤ →
    (∀ c : D.O, ∀ x ∈ M, actQ D c x ∈ M) → (∀ (m : ℕ) x, m.Coprime p → m • x ∈ M → x ∈ M) → (∀ x ∈ s, p ^ k • x ∈ M) →
    (∀ x ∈ M, ∃ m : ℕ, m.Coprime p ∧ (m * p ^ k) • x ∈ AddSubgroup.closure (s : Set (VQ D))) → IsPLat D M

def MemDual : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∃ d : ∀ w : Fin G.m, G.Fw w, (∀ w, d w ≠ 0) ∧ ∀ a : Loc G,
    ((∀ z : Loc G, IntL z → ‖pairL a z‖ ≤ 1) ↔ IntL (fun w => d w • a w))

def PkLat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (A : PFrame L β), D.m = 1 → ∀ g : Gp G, ∃ M : AddSubgroup (VQ D), (∀ x, x ∈ M ↔ A.Mem g x) ∧ IsPLat D M

def PkEquiv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (A : PFrame L β) (y : GlobalTheory.LKCx.grp G β) (g : Gp G) (x : VQ D), A.Mem (locC G (y : G.Cˣ × ℚˣ) * g) (actY L y x) ↔ A.Mem g x

def PkPerf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (A : PFrame L β) (g : Gp G) (s : ℚ), ‖(s : ℚ_[p]) * (g.1 : ℚ_[p])‖ = 1 → ∀ M : AddSubgroup (VQ D), (∀ x, x ∈ M ↔ A.Mem g x) → PerfAt L β s M

def PkInj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (A : PFrame L β) (g g' : Gp G), (∀ x, A.Mem g x ↔ A.Mem g' x) ↔ IntPt (g⁻¹ * g')

def PkOnto : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (A : PFrame L β), D.m = 1 → ∀ (M : AddSubgroup (VQ D)) (s : ℚ), IsPLat D M → 0 < s → PerfAt L β s M → ∃ g : Gp G, ∀ x, x ∈ M ↔ A.Mem g x

def OOnto : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.m = 1 → Function.Surjective (algebraMap (𝓞 D.F) D.O)

end UpperTheory.Gal.W2
end
end

