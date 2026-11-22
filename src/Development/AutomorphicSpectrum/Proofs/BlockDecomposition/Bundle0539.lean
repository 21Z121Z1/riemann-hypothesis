import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0525
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix TensorProduct

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def hermE (σ : E →ₐ[F] E) (n : ℕ) : Submodule F (Matrix (Fin n) (Fin n) E) where
  carrier := {c | ∀ a b, σ (c b a) = c a b}
  add_mem' := by
    intro c d hc hd a b
    simp [map_add, hc a b, hd a b]
  zero_mem' := by
    intro a b
    simp
  smul_mem' := by
    intro t c hc a b
    simp [hc a b]

def hermIn (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (n : ℕ) :
    hermE σ n →+ HermR R σ n where
  toFun c := hermOf R σ c.1 c.2
  map_zero' := by
    apply Subtype.ext
    ext a b
    simp [hermOf]
  map_add' := by
    intro c d
    apply Subtype.ext
    ext a b
    simp [hermOf]

variable [NumberField E]

def hermO (σ : E →ₐ[F] E) (n : ℕ) : AddSubgroup (hermE σ n) where
  carrier := {c | ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = c.1 a b}
  add_mem' := by
    intro c d hc hd a b
    obtain ⟨o, ho⟩ := hc a b
    obtain ⟨p, hp⟩ := hd a b
    exact ⟨o + p, by simp [ho, hp]⟩
  zero_mem' := fun a b => ⟨0, by simp⟩
  neg_mem' := by
    intro c hc a b
    obtain ⟨o, ho⟩ := hc a b
    exact ⟨-o, by simp [ho]⟩

def Kc {n : ℕ} (c : Matrix (Fin n) (Fin n) E) : AddSubgroup (Fin n → 𝓞 E) where
  carrier := {y | ∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = (c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) i}
  add_mem' := by
    intro y z hy hz i
    obtain ⟨o, ho⟩ := hy i
    obtain ⟨p, hp⟩ := hz i
    refine ⟨o + p, ?_⟩
    have : (fun j => algebraMap (𝓞 E) E ((y + z) j)) =
        (fun j => algebraMap (𝓞 E) E (y j)) + fun j => algebraMap (𝓞 E) E (z j) := by
      funext j
      simp
    rw [this, Matrix.mulVec_add, Pi.add_apply, ← ho, ← hp, map_add]
  zero_mem' := fun i => ⟨0, by
    have h0 : (fun _ : Fin n => (0 : E)) = 0 := rfl
    simp [h0, Matrix.mulVec_zero]⟩
  neg_mem' := by
    intro y hy i
    obtain ⟨o, ho⟩ := hy i
    refine ⟨-o, ?_⟩
    have : (fun j => algebraMap (𝓞 E) E ((-y) j)) = -fun j => algebraMap (𝓞 E) E (y j) := by
      funext j
      simp
    rw [this, Matrix.mulVec_neg, Pi.neg_apply, ← ho, map_neg]

def delta {n : ℕ} (c : Matrix (Fin n) (Fin n) E) : ℕ := (Kc c).index

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepDualInverse
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem ev_unit_inv_mul {m : ℕ} {n : Fin (m + 1) → ℕ} {U : (MP ℤ m n).Opens} (v : Γ(MP ℤ m n, U)ˣ)
    (y : CxPts (mpStr ℤ m n) σ₀) (hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ U) :
    CxPts.ev (mpStr ℤ m n) σ₀ U (↑v⁻¹ : Γ(MP ℤ m n, U)) y *
      CxPts.ev (mpStr ℤ m n) σ₀ U (v : Γ(MP ℤ m n, U)) y = 1 := by
  unfold CxPts.ev ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR
  split_ifs with h
  · rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  · exact (h hy).elim

theorem isHermRep_dual : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)),
    IsHermRep M A → IsHermRep M.dual A.inv := by
  intro m n M A hA
  obtain ⟨u, h1, h2, h3⟩ := hA
  refine ⟨fun i c => (u i c)⁻¹, ?_, ?_, ?_⟩
  · rintro (i : M.B.ι) (j : M.B.ι) c
    change Semi.res _ (u j c)⁻¹ = Semi.res _ (M.B.g i j)⁻¹ * Semi.res _ (u i c)⁻¹
    rw [map_inv, map_inv, map_inv, ← mul_inv]
    exact congrArg (·⁻¹) (h1 i j c)
  · rintro (i : M.B.ι) c c'
    change Semi.res _ (u i c)⁻¹ = Semi.res _ (u i c')⁻¹ * ∏ k, blockUnit (c k) (c' k) _ ^ (-A.a k)
    rw [map_inv, map_inv]
    have h := congrArg (·⁻¹) (h2 i c c')
    simp only [mul_inv, ← Finset.prod_inv_distrib, ← zpow_neg] at h
    exact h
  · rintro (i : M.B.ι) c y z hz (hyin : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c))
    change (A.h z)⁻¹ = (∏ k, ‖z ⟨k, c k⟩‖ ^ (-A.a k)) *
      ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (↑(u i c)⁻¹) y‖ * Real.exp (-(M.φ σ₀).φ i y / 2)
    have e : CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (↑(u i c)⁻¹) y =
        (CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (↑(u i c)) y)⁻¹ :=
      eq_inv_of_mul_eq_one_left (ev_unit_inv_mul (u i c) y hyin)
    rw [h3 i c y z hz hyin]
    simp only [zpow_neg, Finset.prod_inv_distrib, neg_div, Real.exp_neg, mul_inv]
    congr 2
    rw [e, norm_inv]

end GlobalTheory.CompanionTheory.MPDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepOfIsometric
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.IsomT

variable {X : Scheme.{0}}

theorem res_twice {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (u : Γ(X, U)ˣ) :
    res h₂ (res h₁ u) = res (h₂.trans h₁) u := by
  apply Units.ext
  show (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom (u : Γ(X, U))) =
    (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom (u : Γ(X, U))
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem units_ext_cover {ι : Type} (V : ι → X.Opens) (hc : ⨆ i, V i = ⊤) {W : X.Opens}
    {f g : Γ(X, W)ˣ} (h : ∀ i, res (inf_le_left : W ⊓ V i ≤ W) f = res inf_le_left g) : f = g := by
  apply Units.ext
  have hcov : W ≤ ⨆ i, W ⊓ V i := by
    rw [← inf_iSup_eq, hc, inf_top_eq]
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun i => W ⊓ V i) W (fun i => homOfLE inf_le_left) hcov _ _
    fun i => ?_
  exact congrArg Units.val (h i)

theorem exists_glue {ι : Type} (V : ι → X.Opens) (hc : ⨆ i, V i = ⊤) (W : X.Opens)
    (f : ∀ i, Γ(X, W ⊓ V i)ˣ)
    (hf : ∀ i j, res (inf_le_left : (W ⊓ V i) ⊓ (W ⊓ V j) ≤ W ⊓ V i) (f i) =
      res inf_le_right (f j)) :
    ∃ u : Γ(X, W)ˣ, ∀ i, res inf_le_left u = f i := by
  have hcov : W ≤ ⨆ i, W ⊓ V i := by
    rw [← inf_iSup_eq, hc, inf_top_eq]
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun i => W ⊓ V i) W
    (fun i => homOfLE inf_le_left) hcov (fun i => ((f i : Γ(X, W ⊓ V i))))
    (fun i j => congrArg Units.val (hf i j))
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun i => W ⊓ V i) W
    (fun i => homOfLE inf_le_left) hcov (fun i => (((f i)⁻¹ : Γ(X, W ⊓ V i)ˣ) : Γ(X, W ⊓ V i)))
    (fun i j => by
      have := congrArg Units.val (congrArg (·⁻¹) (hf i j))
      rw [← map_inv, ← map_inv] at this
      exact this)
  have hst : s * t = 1 := by
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun i => W ⊓ V i) W (fun i => homOfLE inf_le_left) hcov _ _
      fun i => ?_
    rw [map_mul, map_one, hs i, ht i]
    exact (f i).mul_inv
  refine ⟨⟨s, t, hst, by show (t : Γ(X, W)) * s = 1; rw [mul_comm]; exact hst⟩, fun i => Units.ext ?_⟩
  exact hs i

theorem ofMem {V U : X.Opens} (h : ∀ x, x ∈ V → x ∈ U) : V ≤ U := by
  intro x hx
  exact h x hx

def wu {B C : LB X} (w : LB.Iso B C) (a : C.ι) (b : B.ι) : Γ(X, C.U a ⊓ B.U b)ˣ := w.s (a, b)

theorem cg₁ {G : Type*} [CommGroup G] {x y g p q : G} (h : x * g = y) (h' : q = g * p) :
    x⁻¹ * p = y⁻¹ * q := by
  subst h
  subst h'
  rw [mul_inv, mul_assoc, inv_mul_cancel_left]

theorem cg₂ {G : Type*} [CommGroup G] {x y g p : G} (h : x = g * y) :
    y⁻¹ * p = g * (x⁻¹ * p) := by
  subst h
  rw [mul_inv, mul_assoc g⁻¹, mul_inv_cancel_left]

end GlobalTheory.CompanionTheory.MPDict.IsomT

namespace GlobalTheory.CompanionTheory.MPDict

open IsomT

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem res_blockUnit {k : Fin (m + 1)} (i j : Bk n k)
    {W W' : (MP ℤ m n).Opens} (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) (h' : W' ≤ W) :
    res h' (blockUnit i j h) = blockUnit i j (h'.trans h) := by
  unfold blockUnit
  exact res_twice _ _ _

theorem res_mul_prod (c c' : ∀ k, Bk n k) (e : Fin (m + 1) → ℤ)
    {W W' : (MP ℤ m n).Opens} (x : Γ(MP ℤ m n, W)ˣ)
    (H : ∀ k, W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) (h' : W' ≤ W) :
    res h' (x * ∏ k, blockUnit (c k) (c' k) (H k) ^ e k) =
      res h' x * ∏ k, blockUnit (c k) (c' k) (h'.trans (H k)) ^ e k := by
  rw [map_mul, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, res_blockUnit]

end GlobalTheory.CompanionTheory.MPDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTensorProduct
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.TensRep

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem res_blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W W' : (MP ℤ m n).Opens} (h : W' ≤ W)
    (h' : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) :
    Semi.res h (blockUnit i j h') = blockUnit i j (h.trans h') :=
  DVR.res_res' _ _ _

def mulUnit {P Q C : (MP ℤ m n).Opens} (u : Γ(MP ℤ m n, P ⊓ C)ˣ) (v : Γ(MP ℤ m n, Q ⊓ C)ˣ) :
    Γ(MP ℤ m n, P ⊓ Q ⊓ C)ˣ :=
  Semi.res (inf_le_inf_right _ inf_le_left) u * Semi.res (inf_le_inf_right _ inf_le_right) v

theorem ev_mulUnit {P Q C : (MP ℤ m n).Opens} (u : Γ(MP ℤ m n, P ⊓ C)ˣ) (v : Γ(MP ℤ m n, Q ⊓ C)ˣ)
    {y : CxPts (mpStr ℤ m n) σ₀} (hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ (P ⊓ Q ⊓ C)) :
    CxPts.ev (mpStr ℤ m n) σ₀ (P ⊓ Q ⊓ C) (mulUnit u v : Γ(MP ℤ m n, P ⊓ Q ⊓ C)ˣ) y =
      CxPts.ev (mpStr ℤ m n) σ₀ (P ⊓ C) (u : Γ(MP ℤ m n, P ⊓ C)) y *
        CxPts.ev (mpStr ℤ m n) σ₀ (Q ⊓ C) (v : Γ(MP ℤ m n, Q ⊓ C)) y := by
  rw [mulUnit, Units.val_mul, CxPts.ev_mul]
  exact congrArg₂ (· * ·) (CxPts.ev_res _ hy _) (CxPts.ev_res _ hy _)

theorem frame_mulUnit {P P' Q Q' C : (MP ℤ m n).Opens} (g : Γ(MP ℤ m n, P ⊓ P')ˣ) (g' : Γ(MP ℤ m n, Q ⊓ Q')ˣ)
    (u : Γ(MP ℤ m n, P ⊓ C)ˣ) (u' : Γ(MP ℤ m n, P' ⊓ C)ˣ) (v : Γ(MP ℤ m n, Q ⊓ C)ˣ) (v' : Γ(MP ℤ m n, Q' ⊓ C)ˣ)
    (a₁ : P ⊓ P' ⊓ C ≤ P' ⊓ C) (a₂ : P ⊓ P' ⊓ C ≤ P ⊓ P') (a₃ : P ⊓ P' ⊓ C ≤ P ⊓ C)
    (b₁ : Q ⊓ Q' ⊓ C ≤ Q' ⊓ C) (b₂ : Q ⊓ Q' ⊓ C ≤ Q ⊓ Q') (b₃ : Q ⊓ Q' ⊓ C ≤ Q ⊓ C)
    (hu : Semi.res a₁ u' = Semi.res a₂ g * Semi.res a₃ u) (hv : Semi.res b₁ v' = Semi.res b₂ g' * Semi.res b₃ v)
    (d₁ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ P' ⊓ Q' ⊓ C) (d₂ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ P ⊓ Q ⊓ (P' ⊓ Q'))
    (d₃ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ P ⊓ Q ⊓ C) (f₁ : P ⊓ Q ⊓ (P' ⊓ Q') ≤ P ⊓ P') (f₂ : P ⊓ Q ⊓ (P' ⊓ Q') ≤ Q ⊓ Q') :
    Semi.res d₁ (mulUnit u' v') = Semi.res d₂ (Semi.res f₁ g * Semi.res f₂ g') * Semi.res d₃ (mulUnit u v) := by
  have l₁ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ P ⊓ P' ⊓ C := inf_le_inf_right _ (inf_le_inf inf_le_left inf_le_left)
  have l₂ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ Q ⊓ Q' ⊓ C := inf_le_inf_right _ (inf_le_inf inf_le_right inf_le_right)
  have e₁ := congrArg (Semi.res l₁) hu
  have e₂ := congrArg (Semi.res l₂) hv
  simp only [map_mul, DVR.res_res'] at e₁ e₂
  simp only [mulUnit, map_mul, DVR.res_res']
  exact (congrArg₂ (· * ·) e₁ e₂).trans (mul_mul_mul_comm _ _ _ _)

theorem mono_mulUnit {P Q : (MP ℤ m n).Opens} {c c' : ∀ k, Bk n k} (a b : Fin (m + 1) → ℤ)
    (u : Γ(MP ℤ m n, P ⊓ mchart c)ˣ) (u' : Γ(MP ℤ m n, P ⊓ mchart c')ˣ)
    (v : Γ(MP ℤ m n, Q ⊓ mchart c)ˣ) (v' : Γ(MP ℤ m n, Q ⊓ mchart c')ˣ)
    (a₁ : P ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ mchart c) (a₂ : P ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ mchart c')
    (b₁ : Q ⊓ (mchart c ⊓ mchart c') ≤ Q ⊓ mchart c) (b₂ : Q ⊓ (mchart c ⊓ mchart c') ≤ Q ⊓ mchart c')
    (ta : ∀ k, P ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k)))
    (tb : ∀ k, Q ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k)))
    (hu : Semi.res a₁ u = Semi.res a₂ u' * ∏ k, blockUnit (c k) (c' k) (ta k) ^ a k)
    (hv : Semi.res b₁ v = Semi.res b₂ v' * ∏ k, blockUnit (c k) (c' k) (tb k) ^ b k)
    (d₁ : P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ Q ⊓ mchart c) (d₂ : P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ Q ⊓ mchart c')
    (td : ∀ k, P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) :
    Semi.res d₁ (mulUnit u v) = Semi.res d₂ (mulUnit u' v') * ∏ k, blockUnit (c k) (c' k) (td k) ^ (a k + b k) := by
  have l₁ : P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ (mchart c ⊓ mchart c') := inf_le_inf_right _ inf_le_left
  have l₂ : P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ Q ⊓ (mchart c ⊓ mchart c') := inf_le_inf_right _ inf_le_right
  have e₁ := congrArg (Semi.res l₁) hu
  have e₂ := congrArg (Semi.res l₂) hv
  simp only [map_mul, map_prod, map_zpow, DVR.res_res'] at e₁ e₂
  simp only [mulUnit, map_mul, DVR.res_res']
  refine ((congrArg₂ (· * ·) e₁ e₂).trans (mul_mul_mul_comm _ _ _ _)).trans (congrArg (HMul.hMul _) ?_)
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [res_blockUnit, res_blockUnit, ← zpow_add]

end GlobalTheory.CompanionTheory.MPDict.TensRep

namespace GlobalTheory.CompanionTheory.MPDict

open TensRep

theorem isHermRep_tens : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M N : HermLB (mpStr ℤ m n)) (A B : Geo.HermLine (Bk n)),
    IsHermRep M A → IsHermRep N B → IsHermRep (M.tens N) (A.tensor B) := by
  rintro m n M N A B ⟨u, hu₁, hu₂, hu₃⟩ ⟨v, hv₁, hv₂, hv₃⟩
  refine ⟨fun p c => mulUnit (u p.1 c) (v p.2 c), ?_, ?_, ?_⟩
  · rintro ⟨i, i'⟩ ⟨j, j'⟩ c
    exact frame_mulUnit _ _ _ _ _ _ _ _ _ _ _ _ (hu₁ i j c) (hv₁ i' j' c) _ _ _ _ _
  · rintro ⟨i, i'⟩ c c'
    exact mono_mulUnit A.a B.a _ _ _ _ _ _ _ _ _ _ (hu₂ i c c') (hv₂ i' c c') _ _ _
  · rintro ⟨i, i'⟩ c y z hz hy
    have hy' := mem_ptsIn_inf.1 hy
    have h₁ := mem_ptsIn_inf.1 hy'.1
    have e₁ := hu₃ i c y z hz (mem_ptsIn_inf.2 ⟨h₁.1, hy'.2⟩)
    have e₂ := hv₃ i' c y z hz (mem_ptsIn_inf.2 ⟨h₁.2, hy'.2⟩)
    have hz0 : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k => (hz k (c k)).1.1 (ptsIn_mono (mchart_le c k) hy'.2)
    have hp : ∏ k, ‖z ⟨k, c k⟩‖ ^ (A.a k + B.a k) =
        (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) * ∏ k, ‖z ⟨k, c k⟩‖ ^ B.a k := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => zpow_add₀ (norm_ne_zero_iff.2 (hz0 k)) _ _
    have hev := ev_mulUnit (u i c) (v i' c) hy
    change A.h z * B.h z = (∏ k, ‖z ⟨k, c k⟩‖ ^ (A.a k + B.a k)) *
      ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ N.B.U i' ⊓ mchart c)
        (mulUnit (u i c) (v i' c) : Γ(MP ℤ m n, M.B.U i ⊓ N.B.U i' ⊓ mchart c)ˣ) y‖ *
      Real.exp (((M.φ σ₀).φ i y + (N.φ σ₀).φ i' y) / 2)
    rw [e₁, e₂, hev, hp, norm_mul, add_div, Real.exp_add]
    ring

end GlobalTheory.CompanionTheory.MPDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFamilyAnisotropicJoint
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.ParCocompact.HermNondeg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hE_eq_dot (σ : E →ₐ[F] E) {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hE σ A x y = (fun i => σ (x i)) ⬝ᵥ (A *ᵥ y) := by
  have : hE σ A x y = ∑ i, ∑ j, σ (x i) * A i j * y j := rfl
  rw [this]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hE_normMat (σ : E →ₐ[F] E) {n : ℕ} (l ξ : Fin n → E) :
    hE σ (normMat σ l) ξ ξ = σ (l ⬝ᵥ ξ) * (l ⬝ᵥ ξ) := by
  have : hE σ (normMat σ l) ξ ξ = ∑ i, ∑ j, σ (ξ i) * (σ (l i) * l j) * ξ j := rfl
  rw [this]
  simp only [dotProduct, map_sum, map_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dot_eq_zero_of_hE_normMat (σ : E →ₐ[F] E) {n : ℕ} {l ξ : Fin n → E}
    (h : hE σ (normMat σ l) ξ ξ = 0) : l ⬝ᵥ ξ = 0 := by
  rw [hE_normMat] at h
  rcases mul_eq_zero.1 h with h | h
  · exact (map_eq_zero_iff σ σ.toRingHom.injective).1 h
  · exact h

theorem hE_conj (σ : E →ₐ[F] E) {n : ℕ} (J P : Matrix (Fin n) (Fin n) E) (ξ : Fin n → E) :
    hE σ (cT (σ : E →+* E) P * J * P) ξ ξ = hE σ J (P *ᵥ ξ) (P *ᵥ ξ) := by
  rw [hE_eq_dot, hE_eq_dot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ (cT (σ : E →+* E) P)]
  congr 1
  ext j
  simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, cT, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

theorem anisoProj_mulVec (σ : E →ₐ[F] E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E)
    (ξ : Fin n → E) (hX : ∀ i, rowOf σ J X i ⬝ᵥ ξ = 0) (hY : ∀ i, rowOf σ J Y i ⬝ᵥ ξ = 0) :
    anisoProj σ J X Y *ᵥ ξ = ξ := by
  have h0 : ∀ k, projFam σ J X Y k *ᵥ ξ = 0 := by
    rintro (i | i)
    · simp only [projFam, Sum.elim_inl, lineProj, Matrix.vecMulVec_mulVec, hY i]
      ext k
      simp
    · simp only [projFam, Sum.elim_inr, lineProj, Matrix.vecMulVec_mulVec, hX i]
      ext k
      simp
  rw [anisoProj, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec, Finset.sum_eq_zero fun k _ => h0 k, sub_zero]

end GlobalTheory.CompanionTheory.ParCocompact.HermNondeg

namespace GlobalTheory.CompanionTheory.ParCocompact

theorem hermFam_nondeg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ ξ : Fin n → E,
    (∀ j, hE σ (hermFam σ J X Y j) ξ ξ = 0) → ξ = 0 := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y hW ξ h
  have hY : ∀ i, rowOf σ J Y i ⬝ᵥ ξ = 0 := fun i =>
    HermNondeg.dot_eq_zero_of_hE_normMat σ (h (some (Sum.inl i)))
  have hX : ∀ i, rowOf σ J X i ⬝ᵥ ξ = 0 := fun i =>
    HermNondeg.dot_eq_zero_of_hE_normMat σ (h (some (Sum.inr i)))
  have hπ := HermNondeg.anisoProj_mulVec σ J X Y ξ hX hY
  have hn : hE σ J ξ ξ = 0 := by
    have := h none
    change hE σ (cT (σ : E →+* E) (anisoProj σ J X Y) * J * anisoProj σ J X Y) ξ ξ = 0 at this
    rwa [HermNondeg.hE_conj, hπ] at this
  refine hW.aniso ξ ?_ ?_ hn
  · ext i
    exact hX i
  · ext i
    exact hY i

end GlobalTheory.CompanionTheory.ParCocompact
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianScalarSequenceTendsZeroStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_scalar_sequence_tends_zero : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ r : ℕ, ∃ e : ℕ → Mx D r r, (∀ n, e n ∈ hermA D r) ∧ Filter.Tendsto e Filter.atTop (nhds 0) ∧ ∀ (n : ℕ) (ρ : D.what₂.Tau), compAt θ ρ (e n) = (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path.exists_herm_seq | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path.exists_herm_seq | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path.exists_herm_seq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free

def hypOne {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    Matrix (Fin (M + 2)) (Fin (M + 2)) K :=
  Matrix.of (Fin.cons (Fin.cons 0 (Fin.cons 1 fun _ => 0))
    (Fin.cons (Fin.cons 1 (Fin.cons 0 fun _ => 0)) fun i => Fin.cons 0 (Fin.cons 0 (A i))))

section Entries

variable {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)

theorem hypOne_zero_zero : hypOne A 0 0 = 0 := rfl
theorem hypOne_zero_one : hypOne A 0 1 = 1 := rfl
theorem hypOne_one_zero : hypOne A 1 0 = 1 := rfl
theorem hypOne_one_one : hypOne A 1 1 = 0 := rfl
theorem hypOne_zero_rest (j : Fin M) : hypOne A 0 j.succ.succ = 0 := rfl
theorem hypOne_one_rest (j : Fin M) : hypOne A 1 j.succ.succ = 0 := rfl
theorem hypOne_rest_zero (i : Fin M) : hypOne A i.succ.succ 0 = 0 := rfl
theorem hypOne_rest_one (i : Fin M) : hypOne A i.succ.succ 1 = 0 := rfl
theorem hypOne_rest_rest (i j : Fin M) : hypOne A i.succ.succ j.succ.succ = A i j := rfl

end Entries

end GlobalTheory.CompanionTheory.WeilSiegel.Free
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetThetaReverseBlocksStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Zc.Cos GlobalTheory.CompanionTheory.ThetaProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_theta_reverse_blocks : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    Nonempty ((jac (stdBlocks d hd) (π.comp (thetaW k N))).Equiv
      ((jac (stdBlocks (fun a => d (Fin.rev a)) hd') π).comp (thetaL d))) := by
  first | exact @GlobalTheory.CompanionTheory.JacTheta.nonempty_jac_comp_thetaW | exact GlobalTheory.CompanionTheory.JacTheta.nonempty_jac_comp_thetaW | (intros; apply GlobalTheory.CompanionTheory.JacTheta.nonempty_jac_comp_thetaW <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicScalesIsotropicStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_parabolic_scales_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ δ ∈ ratPts σ J, δ ∈ minPar σ J X → ∃ e : E, e ≠ 0 ∧ Sends σ J δ (e • Xᵀ 0) (Xᵀ 0) := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.exists_sends_of_rat_mem_minPar | exact GlobalTheory.CompanionTheory.RedCov.exists_sends_of_rat_mem_minPar | (intros; apply GlobalTheory.CompanionTheory.RedCov.exists_sends_of_rat_mem_minPar <;> assumption)
end

