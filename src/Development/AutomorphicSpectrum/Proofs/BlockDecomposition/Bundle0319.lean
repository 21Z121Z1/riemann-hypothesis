import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0155
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0293
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0311
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0036
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0022
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0312
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0306
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0287
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0014
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGradedMapGlueD
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0094
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0313
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PderivComp1PtZeroEqZero
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.OntoFirstChernCocycle

section Ring

variable {B : Type} [CommRing B] (a b : Ideal B)

theorem inv_sub_mem {z m : B} (hzm : z * m = 1) (hz : z - 1 ∈ a) : m - 1 ∈ a := by
  have : m - 1 = -((z - 1) * m) := by linear_combination hzm
  rw [this]
  exact neg_mem (a.mul_mem_right _ hz)

theorem log3 (hab : ∀ x y, x ∈ a → y ∈ a → x * y ∈ b) {x y z m : B} (hzm : z * m = 1) (hx : x - 1 ∈ a)
    (hy : y - 1 ∈ a) (hz : z - 1 ∈ a) : x * y * m - 1 - ((y - 1) - (z - 1) + (x - 1)) ∈ b := by
  have hm := inv_sub_mem a hzm hz
  have e : x * y * m - 1 - ((y - 1) - (z - 1) + (x - 1)) =
      (x - 1) * (y - 1) + (-((z - 1) * (m - 1))) + (x - 1) * (m - 1) + (y - 1) * (m - 1) +
        (x - 1) * ((y - 1) * (m - 1)) := by
    linear_combination hzm
  rw [e]
  exact add_mem (add_mem (add_mem (add_mem (hab _ _ hx hy) (neg_mem (hab _ _ hz hm))) (hab _ _ hx hm)) (hab _ _ hy hm))
    (b.mul_mem_left _ (hab _ _ hy hm))

theorem form_key (hab : ∀ x y, x ∈ a → y ∈ a → x * y ∈ b) {W W' Wi t ti c m u e g : B}
    (hW : W = W' * (t * m)) (hWi : W' * Wi = 1) (hti : t * ti = 1) (hcm : c * m = 1)
    (h1 : W - 1 ∈ a) (h2 : W' - 1 ∈ a) (h3 : t * u - 1 ∈ a) (h4 : c * e - 1 ∈ a) (h5 : g + t ∈ a) :
    u - e ∈ a ∧ (W - 1) - (W' - 1) - ((t * u - 1) - (c * e - 1)) - g * (u - e) ∈ b := by
  have hy : t * m - 1 ∈ a := by
    have : t * m - 1 = ((W - 1) - (W' - 1)) * Wi := by
      rw [hW]; linear_combination (1 - t * m) * hWi
    rw [this]
    exact a.mul_mem_right _ (sub_mem h1 h2)
  have hD : u - e ∈ a := by
    have : u - e = ti * ((t * u - 1) - (t * m - 1) - (t * m) * (c * e - 1)) := by
      linear_combination (e - u) * hti + (e * t * ti) * hcm
    rw [this]
    refine a.mul_mem_left _ (sub_mem (sub_mem h3 hy) (a.mul_mem_left _ h4))
  refine ⟨hD, ?_⟩
  have e1 : (W - 1) - (W' - 1) - ((t * u - 1) - (c * e - 1)) - g * (u - e) =
      (W' - 1) * (t * m - 1) + (-((t * m - 1) * (c * e - 1))) + (-((g + t) * (u - e))) := by
    rw [hW]
    linear_combination (t * e) * hcm
  rw [e1]
  exact add_mem (add_mem (hab _ _ h2 hy) (neg_mem (hab _ _ hy h4))) (neg_mem (hab _ _ h5 hD))

end Ring

section Cat

universe v u

variable {R : Type} [CommRing R] {E : Type u} [Category.{v} E] {H : E ⥤ CommAlgCat.{0} R} (a b : IdF H)

def mu {c c' : E} (φ : c ⟶ c') : (H.obj c)ˣ →* (H.obj c')ˣ := Units.map ((H.map φ).hom : H.obj c →* H.obj c')

def dl (W : ∀ {c c' : E}, (c ⟶ c') → (H.obj c')ˣ)
    (hW : ∀ {c c' : E} (φ : c ⟶ c'), ((W φ : (H.obj c')ˣ) : H.obj c') - 1 ∈ a.S c') : CH.Cn (sq a b) 1 :=
  fun s => sqMk a b (((W (s.map' 0 1) : (H.obj (s.obj (Fin.last 1)))ˣ) : H.obj (s.obj (Fin.last 1))) - 1) (hW (s.map' 0 1))

def c0 (x : ∀ c, H.obj c) (hx : ∀ c, x c ∈ a.S c) : CH.Cn (sq a b) 0 := fun s => sqMk a b (x _) (hx _)

theorem map_id_sq {T : E} (ρ : T ⟶ T) (h : ρ = 𝟙 T) (x : sqM a b T) : ((sq a b).map ρ).hom x = x := by
  subst h
  simp

theorem sum3 {T : E} {p q r t : H.obj T} (hp : p ∈ a.S T) (hq : q ∈ a.S T) (hr : r ∈ a.S T) (ht : t ∈ a.S T)
    (h : t - ((p - q) + r) ∈ b.S T) :
    (-1 : ℤ) ^ ((0 : Fin 3) : ℕ) • sqMk a b p hp + (-1 : ℤ) ^ ((1 : Fin 3) : ℕ) • sqMk a b q hq +
      (-1 : ℤ) ^ ((2 : Fin 3) : ℕ) • sqMk a b r hr = sqMk a b t ht := by
  have e2 : ((2 : Fin 3) : ℕ) = 2 := rfl
  have e1 : ((1 : Fin 3) : ℕ) = 1 := rfl
  have e0 : ((0 : Fin 3) : ℕ) = 0 := rfl
  rw [e0, e1, e2, pow_zero, pow_one, show (-1 : ℤ) ^ 2 = 1 by norm_num, one_smul, one_smul, neg_one_smul]
  have : sqMk a b p hp + -sqMk a b q hq + sqMk a b r hr = sqMk a b ((p - q) + r) (add_mem (sub_mem hp hq) hr) :=
    Subtype.ext (show Ideal.Quotient.mk (b.S T) p + -Ideal.Quotient.mk (b.S T) q + Ideal.Quotient.mk (b.S T) r = Ideal.Quotient.mk (b.S T) ((p - q) + r) by
      rw [map_add, map_sub]; ring)
  rw [this]
  exact ((sq_eq a b _ _).2 (by
    have := neg_mem h
    rwa [neg_sub] at this))

def rU (W : ∀ {c c' : E}, (c ⟶ c') → (H.obj c')ˣ) (s : ComposableArrows E 2) : (H.obj (s.obj (Fin.last 2)))ˣ :=
  mu (s.map' 1 2) (W (s.map' 0 1)) * W (s.map' 1 2) * (W (s.map' 0 2))⁻¹

theorem d_dl (hab : ∀ T x y, x ∈ a.S T → y ∈ a.S T → x * y ∈ b.S T) (W : ∀ {c c' : E}, (c ⟶ c') → (H.obj c')ˣ)
    (hW : ∀ {c c' : E} (φ : c ⟶ c'), ((W φ : (H.obj c')ˣ) : H.obj c') - 1 ∈ a.S c') (s : ComposableArrows E 2)
    (hr : (rU W s : H.obj (s.obj (Fin.last 2))) - 1 ∈ a.S _) :
    CH.d (sq a b) 1 (dl a b W hW) s = sqMk a b ((rU W s : H.obj (s.obj (Fin.last 2))) - 1) hr := by
  change ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • ((sq a b).map (toLast i s)).hom (dl a b W hW (face i s)) = _
  rw [Fin.sum_univ_three]
  have t0 := map_id_sq a b (T := s.obj (Fin.last 2)) (toLast 0 s) (s.map_id _) (dl a b W hW (face 0 s))
  have t1 := map_id_sq a b (T := s.obj (Fin.last 2)) (toLast 1 s) (s.map_id _) (dl a b W hW (face 1 s))
  erw [t0, t1]
  have hx : (H.map (s.map' 1 2)).hom ((W (s.map' 0 1) : H.obj _) - 1) ∈ a.S _ := a.map_mem (s.map' 1 2) (hW (s.map' 0 1))
  have t2 : ((sq a b).map (toLast 2 s)).hom (dl a b W hW (face 2 s)) = sqMk a b _ hx := rfl
  erw [t2]
  refine sum3 a b (hW (s.map' 1 2)) (hW (s.map' 0 2)) hx hr ?_
  have e : (H.map (s.map' 1 2)).hom ((W (s.map' 0 1) : H.obj _) - 1) =
      Units.val (mu (s.map' 1 2) (W (s.map' 0 1))) - 1 := by
    rw [map_sub, map_one]; rfl
  have hx' : Units.val (mu (s.map' 1 2) (W (s.map' 0 1))) - 1 ∈ a.S (s.obj (Fin.last 2)) := e ▸ hx
  have key := log3 (a.S (s.obj (Fin.last 2))) (b.S _) (hab _) (Units.mul_inv (W (s.map' 0 2))) hx' (hW (s.map' 1 2)) (hW (s.map' 0 2))
  rw [e]
  exact key

def mv (s : ComposableArrows E 1) (y : H.obj (s.obj 0)) : H.obj (s.obj (Fin.last 1)) := (H.map (s.map' 0 1)).hom y

theorem pderiv_comp1_pt_zero_eq_zero (x : ∀ c, H.obj c) (hx : ∀ c, x c ∈ a.S c) (s : ComposableArrows E 1)
    (hm : x (s.obj (Fin.last 1)) - mv s (x (s.obj 0)) ∈ a.S _) :
    CH.d (sq a b) 0 (c0 a b x hx) s = sqMk a b (x (s.obj (Fin.last 1)) - mv s (x (s.obj 0))) hm := by
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • ((sq a b).map (toLast i s)).hom (c0 a b x hx (face i s)) = _
  rw [Fin.sum_univ_two]
  have t0 := map_id_sq a b (T := s.obj (Fin.last 1)) (toLast 0 s) (s.map_id _) (c0 a b x hx (face 0 s))
  erw [t0]
  have e1 : ((1 : Fin 2) : ℕ) = 1 := rfl
  have e0 : ((0 : Fin 2) : ℕ) = 0 := rfl
  rw [e0, e1, pow_zero, pow_one, one_smul, neg_one_smul]
  exact Subtype.ext (show Ideal.Quotient.mk _ _ + -Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _ by
    rw [map_sub, sub_eq_add_neg]; rfl)

theorem rep_of (x : CH.Cn (sq a b) 1) (hx : CH.d (sq a b) 1 x = 0) (j : CH.Cn (sq a b) 0)
    (z : ∀ s : ComposableArrows E 1, H.obj (s.obj (Fin.last 1)))
    (h : ∀ s, (show sqM a b _ from (x - CH.d (sq a b) 0 j) s).1 = Ideal.Quotient.mk _ (z s)) :
    Rep a b z ((CH.cx (sq a b)).cls x hx) := by
  have hf : CH.d (sq a b) 1 (x - CH.d (sq a b) 0 j) = 0 := by
    rw [map_sub, hx, CH.d_d, sub_zero]
  refine ⟨x - CH.d (sq a b) 0 j, hf, ?_, h⟩
  refine (Submodule.Quotient.eq _).2 ?_
  change x - (x - CH.d (sq a b) 0 j) ∈ LinearMap.range (CH.d (sq a b) 0)
  exact ⟨j, by abel⟩

theorem cls_eq_d {F : E ⥤ ModuleCat.{0} R} {x y : CH.Cn F 2} (hx : CH.d F 2 x = 0) (hy : CH.d F 2 y = 0)
    (h : (CH.cx F).cls x hx = (CH.cx F).cls y hy) : ∃ c : CH.Cn F 1, CH.d F 1 c = x - y := by
  obtain ⟨c, hc⟩ := (Submodule.Quotient.eq _).1 h
  exact ⟨c, hc⟩

end Cat

section Cat2

universe v u

variable {R : Type} [CommRing R] {E : Type u} [Category.{v} E] {H : E ⥤ CommAlgCat.{0} R} (a b : IdF H)

theorem mu_comp {c₀ c₁ c₂ : E} (f : c₀ ⟶ c₁) (g : c₁ ⟶ c₂) (x : (H.obj c₀)ˣ) : mu (f ≫ g) x = mu g (mu f x) := by
  ext
  change (H.map (f ≫ g)).hom _ = (H.map g).hom ((H.map f).hom _)
  rw [H.map_comp]
  rfl

def tw (w : ∀ {c c' : E}, (c ⟶ c') → (H.obj c')ˣ) (t : ∀ c, (H.obj c)ˣ) {c c' : E} (φ : c ⟶ c') : (H.obj c')ˣ :=
  w φ * (t c' * (mu φ (t c))⁻¹)

theorem tw_units {G : Type} [CommGroup G] (x y z p q r : G) :
    (x * (p * r⁻¹)) * (y * (q * p⁻¹)) * (z * (q * r⁻¹))⁻¹ = x * y * z⁻¹ := by
  simp only [mul_inv, inv_inv]
  have : x * (p * r⁻¹) * (y * (q * p⁻¹)) * (z⁻¹ * (q⁻¹ * r)) = x * y * z⁻¹ * (p * p⁻¹) * (q * q⁻¹) * (r * r⁻¹) := by
    simp only [mul_assoc, mul_left_comm, mul_comm]
  rw [this]
  simp

theorem rU_tw (w : ∀ {c c' : E}, (c ⟶ c') → (H.obj c')ˣ) (t : ∀ c, (H.obj c)ˣ) (s : ComposableArrows E 2) :
    rU (fun φ => tw w t φ) s = rU w s := by
  have key : ∀ {c₀ c₁ c₂ : E} (f : c₀ ⟶ c₁) (g : c₁ ⟶ c₂) (h : c₀ ⟶ c₂), h = f ≫ g →
      mu g (tw w t f) * tw w t g * (tw w t h)⁻¹ = mu g (w f) * w g * (w h)⁻¹ := by
    intro c₀ c₁ c₂ f g h e
    subst e
    unfold tw
    rw [map_mul, map_mul, map_inv, mu_comp]
    exact tw_units _ _ _ _ _ _
  exact key (s.map' 0 1) (s.map' 1 2) (s.map' 0 2) (s.map'_comp 0 1 2)

def wt (W : ∀ {c c' : E}, (c ⟶ c') → (H.obj c')ˣ) (s : ComposableArrows E 1) : (H.obj (s.obj (Fin.last 1)))ˣ := W (s.map' 0 1)

def mt (s : ComposableArrows E 1) (x : (H.obj (s.obj 0))ˣ) : (H.obj (s.obj (Fin.last 1)))ˣ := mu (s.map' 0 1) x

theorem form_rep (hab : ∀ T x y, x ∈ a.S T → y ∈ a.S T → x * y ∈ b.S T) (W W' : ∀ {c c' : E}, (c ⟶ c') → (H.obj c')ˣ)
    (hW : ∀ {c c' : E} (φ : c ⟶ c'), ((W φ : (H.obj c')ˣ) : H.obj c') - 1 ∈ a.S c')
    (hW' : ∀ {c c' : E} (φ : c ⟶ c'), ((W' φ : (H.obj c')ˣ) : H.obj c') - 1 ∈ a.S c')
    (τ : ∀ c, (H.obj c)ˣ) (hτ : ∀ {c c' : E} (φ : c ⟶ c'), W φ = W' φ * (τ c' * (mu φ (τ c))⁻¹))
    (u g : ∀ c, H.obj c) (h1 : ∀ c, (τ c : H.obj c) * u c - 1 ∈ a.S c) (h2 : ∀ c, g c + τ c ∈ a.S c)
    (hx : CH.d (sq a b) 1 (dl a b W hW - dl a b W' hW') = 0) :
    Rep a b (fun s : ComposableArrows E 1 => g (s.obj (Fin.last 1)) * (u (s.obj (Fin.last 1)) - mv s (u (s.obj 0))))
      ((CH.cx (sq a b)).cls _ hx) := by
  refine rep_of a b _ hx (c0 a b (fun c => (τ c : H.obj c) * u c - 1) h1) _ fun s => ?_
  have hc : Units.val (mt s (τ (s.obj 0))) * mv s (u (s.obj 0)) - 1 ∈ a.S (s.obj (Fin.last 1)) := by
    have := a.map_mem (s.map' 0 1) (h1 (s.obj 0))
    rw [map_sub, map_mul, map_one] at this
    exact this
  have hm : ((τ (s.obj (Fin.last 1)) : H.obj _) * u (s.obj (Fin.last 1)) - 1) -
      mv s ((τ (s.obj 0) : H.obj _) * u (s.obj 0) - 1) ∈ a.S (s.obj (Fin.last 1)) :=
    sub_mem (h1 _) (a.map_mem (s.map' 0 1) (h1 (s.obj 0)))
  have hWt : Units.val (wt W s) = Units.val (wt W' s) * (Units.val (τ (s.obj (Fin.last 1))) *
      ((mt s (τ (s.obj 0)))⁻¹ : (H.obj (s.obj (Fin.last 1)))ˣ).1) := congrArg Units.val (hτ (s.map' 0 1))
  have e := form_key (a.S (s.obj (Fin.last 1))) (b.S _) (hab _) (W := Units.val (wt W s))
    (W' := Units.val (wt W' s)) (Wi := ((wt W' s)⁻¹ : (H.obj (s.obj (Fin.last 1)))ˣ).1)
    (t := (τ (s.obj (Fin.last 1)) : H.obj _)) (ti := ((τ (s.obj (Fin.last 1)))⁻¹ : (H.obj _)ˣ).1)
    (c := Units.val (mt s (τ (s.obj 0)))) (m := ((mt s (τ (s.obj 0)))⁻¹ : (H.obj _)ˣ).1)
    (u := u (s.obj (Fin.last 1))) (e := mv s (u (s.obj 0))) (g := g (s.obj (Fin.last 1)))
    hWt (Units.mul_inv _) (Units.mul_inv _) (Units.mul_inv _) (hW _) (hW' _) (h1 _) hc (h2 _)
  have e2 : mv s ((τ (s.obj 0) : H.obj _) * u (s.obj 0) - 1) =
      Units.val (mt s (τ (s.obj 0))) * mv s (u (s.obj 0)) - 1 := by
    unfold mv
    rw [map_sub, map_mul, map_one]
    rfl
  have e3 := pderiv_comp1_pt_zero_eq_zero a b (fun c => (τ c : H.obj c) * u c - 1) h1 s hm
  have e4 : (dl a b W hW - dl a b W' hW' - CH.d (sq a b) 0 (c0 a b (fun c => (τ c : H.obj c) * u c - 1) h1)) s =
      dl a b W hW s - dl a b W' hW' s - CH.d (sq a b) 0 (c0 a b (fun c => (τ c : H.obj c) * u c - 1) h1) s := rfl
  rw [e4, e3]
  change Ideal.Quotient.mk (b.S (s.obj (Fin.last 1))) (Units.val (wt W s) - 1) - Ideal.Quotient.mk _ (Units.val (wt W' s) - 1) -
    Ideal.Quotient.mk _ (((τ (s.obj (Fin.last 1)) : H.obj _) * u (s.obj (Fin.last 1)) - 1) -
      mv s ((τ (s.obj 0) : H.obj _) * u (s.obj 0) - 1)) = _
  rw [← map_sub, ← map_sub, Ideal.Quotient.eq, e2]
  exact e.2

end Cat2

end GlobalTheory.CompanionTheory.OntoFirstChernCocycle
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimeNotDividingCoprimeIdealNormStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_not_dividing_coprime_ideal_norm : ∀ (F : Type) [Field F] [NumberField F] (l : ℕ), l.Prime → ∀ 𝔟 : Ideal (𝓞 F), 𝔟 ⊔ Ideal.span {(l : 𝓞 F)} = ⊤ → ¬ l ∣ Ideal.absNorm 𝔟 := by
  first | exact @GlobalTheory.CompanionTheory.DeligneRibet.absNorm_not_dvd_of_sup_span_eq_top | exact GlobalTheory.CompanionTheory.DeligneRibet.absNorm_not_dvd_of_sup_span_eq_top | (intros; apply GlobalTheory.CompanionTheory.DeligneRibet.absNorm_not_dvd_of_sup_span_eq_top <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperPullbackSystemQuasicoherentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_pullback_system_quasicoherent : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] [CompactSpace X] (φ : Z ⟶ X), IsProper φ → φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → ∀ (B : Subobject ((Scheme.Modules.pullback φ).obj E)), (B : Z.Modules).IsQuasicoherent → (∀ e, B ⊔ powSub I _ (e + 1) = pullSys I φ E S e) → ∃ c : ℕ, ∀ e, S (e + c) ≤ adjKer φ B ⊔ powSub I E (e + 1) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Shift.shift | exact GlobalTheory.CompanionTheory.GE.Shift.shift | (intros; apply GlobalTheory.CompanionTheory.GE.Shift.shift <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionNormOneConjClosureStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_norm_one_conj_closure : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  ∀ s w : Pl F, (∃ x : Q d β (Kp s), x ≠ 0 ∧ qn x = 0) → w ≠ s →
  ∀ a ∈ SuppAt d β {w}, (qmap (proj w) a).re ^ 2 ≠ 1 →
    ∃ c : (Q d β (AF F))ˣ, ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) ∈ closure (SAQ d β s) := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.ConjStep.exists_conj_mem_closure | exact GlobalTheory.CompanionTheory.PlaneSA.ConjStep.exists_conj_mem_closure | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.ConjStep.exists_conj_mem_closure <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayClassParametrizationExistsStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_class_parametrization_exists : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ → ∀ 𝔞 : Ideal (𝓞 F), CoprimeTo F 𝔣 𝔞 → ∃ (𝔟 : Ideal (𝓞 F)) (J : Type) (_ : Fintype J) (r' : J → ℕ) (y : J → 𝓞 F) (v' : ∀ j, Fin (r' j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r' y v' ∧ 𝔟 ⊔ 𝔣 = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam_sup_eq_top | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam_sup_eq_top | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam_sup_eq_top <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayRelAntitoneModulusAndPowModStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayRel_antitone_modulus_and_powMod : ∀ (F : Type) [Field F] [NumberField F], (∀ 𝔣 𝔣' I J : Ideal (𝓞 F), 𝔣' ≤ 𝔣 → RayRel F 𝔣' I J → RayRel F 𝔣 I J) ∧ (∀ l n m : ℕ, n ≤ m → powMod F l m ≤ powMod F l n) := by
  first | exact @GlobalTheory.CompanionTheory.RayFacts.rayRel_mono_powMod_anti | exact GlobalTheory.CompanionTheory.RayFacts.rayRel_mono_powMod_anti | (intros; apply GlobalTheory.CompanionTheory.RayFacts.rayRel_mono_powMod_anti <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionCompatibleIteratedInjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

namespace GlobalTheory.CompanionTheory.FormalAlg.IterInj

theorem restriction_compatible_iterated_injective (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (P : Finset ι → Type)
    [∀ S, AddCommGroup (P S)] [∀ S, Module (MvPolynomial ι A) (P S)]
    (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S')
    (hid : ∀ S (h : S ⊆ S) a, res S S h a = a)
    (hcomp : ∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a,
      res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a)
    (hloc : ∀ (S : Finset ι) (j : ι) (a : P S), S.Nonempty →
      res S (insert j S) (Finset.subset_insert j S) a = 0 →
      ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • a = 0)
    (S : Finset ι) (hS : S.Nonempty) (T : Finset ι) :
    ∀ (S' : Finset ι) (_ : S' = S ∪ T) (h : S ⊆ S') (a : P S), res S S' h a = 0 →
      ∃ l : ℕ, xProd A T ^ l • a = 0 := by
  induction T using Finset.induction_on with
  | empty =>
    intro S' hS' h a ha
    have : S' = S := by simpa using hS'
    subst this
    refine ⟨0, ?_⟩
    rw [hid] at ha
    simpa using ha
  | insert j T' hj ih =>
    intro S' hS' h a ha
    have hS'' : S' = insert j (S ∪ T') := by
      rw [hS', Finset.union_insert]
    subst hS''
    have hsub : S ⊆ S ∪ T' := Finset.subset_union_left
    have hb : res (S ∪ T') (insert j (S ∪ T')) (Finset.subset_insert j _) (res S (S ∪ T') hsub a) = 0 := by
      rw [hcomp]; exact ha
    obtain ⟨k, hk⟩ := hloc (S ∪ T') j _ (hS.mono hsub) hb
    have h2 : res S (S ∪ T') hsub ((MvPolynomial.X j : MvPolynomial ι A) ^ k • a) = 0 := by
      rw [map_smul]; exact hk
    obtain ⟨l, hl⟩ := ih (S ∪ T') rfl hsub _ h2
    refine ⟨k + l, ?_⟩
    have hx : xProd A (insert j T') = MvPolynomial.X j * xProd A T' := by
      simp [xProd, Finset.prod_insert hj]
    have : (xProd A (insert j T')) ^ (k + l) =
        ((MvPolynomial.X j : MvPolynomial ι A) ^ l * xProd A T' ^ k) *
          (xProd A T' ^ l * (MvPolynomial.X j : MvPolynomial ι A) ^ k) := by
      rw [hx, mul_pow]; ring
    rw [this, mul_smul _ (xProd A T' ^ l * _), mul_smul (xProd A T' ^ l), hl, smul_zero]

theorem iter_localisation_injective : ∀ (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S (h : S ⊆ S) a, res S S h a = a) → (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (S : Finset ι) (j : ι) (a : P S), S.Nonempty → res S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • a = 0) → (∀ (T S : Finset ι) (a : P S), S.Nonempty → res S (S ∪ T) Finset.subset_union_left a = 0 → ∃ l : ℕ, xProd A T ^ l • a = 0) := by
  intro ι _ A _ P _ _ res hid hcomp hloc T S a hS ha
  exact restriction_compatible_iterated_injective ι A P res hid hcomp hloc S hS T (S ∪ T) rfl Finset.subset_union_left a ha

end GlobalTheory.CompanionTheory.FormalAlg.IterInj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfEvEqZero
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

theorem smul_eq_zero_of_ev_eq_zero : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (A : Type) [CommRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] [∀ S, IsScalarTower A (MvPolynomial ι A) (P S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (T S : Finset ι) (a : P S), S.Nonempty → res S (S ∪ T) Finset.subset_union_left a = 0 → ∃ l : ℕ, xProd A T ^ l • a = 0) → ∀ (I : Finset ι) (hI : I.Nonempty) (m : glue res), ev res I hI m = 0 → ∃ l : ℕ, xProd A I ^ l • m = 0 := by
  intro ι _ _ A _ P _ _ _ _ res hcomp H I hI m hm
  have key : ∀ i, res {i} ({i} ∪ I) Finset.subset_union_left (m.1 i) = 0 := by
    intro i
    have hJ : ({i} ∪ I).Nonempty := ⟨i, Finset.mem_union_left I (Finset.mem_singleton_self i)⟩
    have h1 := ev_eq hcomp hJ (Finset.mem_union_left I (Finset.mem_singleton_self i)) m
    have h2 := res_ev hcomp hI hJ Finset.subset_union_right m
    rw [hm, map_zero] at h2
    exact h1.symm.trans h2.symm
  choose L hL using fun i => H I {i} (m.1 i) (Finset.singleton_nonempty i) (key i)
  refine ⟨∑ j, L j, ?_⟩
  apply Subtype.ext
  funext i
  simp only [Submodule.coe_smul, Pi.smul_apply, Submodule.coe_zero, Pi.zero_apply]
  have hsum : ∑ j, L j = (∑ j, L j - L i) + L i :=
    (Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))).symm
  rw [hsum, pow_add, mul_smul, hL i, smul_zero]

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientOfNonNilpotent
section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeSub

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem finite_cosets {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (hE : IsHk K e) :
    {q : GL ι F ⧸ K | e q.out ≠ 0}.Finite := by
  have hc : IsCompact (tsupport e) := hE.2.2.1
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun g : GL ι F => (fun x => g⁻¹ * x) ⁻¹' (K : Set (GL ι F)))
    (fun g => hE.1.preimage (continuous_const.mul continuous_id))
    (fun g _ => Set.mem_iUnion.2 ⟨g, by simp [K.one_mem]⟩)
  refine (t.finite_toSet.image (fun g => (QuotientGroup.mk g : GL ι F ⧸ K))).subset fun q hq => ?_
  have hq' : q.out ∈ tsupport e := subset_tsupport _ hq
  obtain ⟨g, hg, hgq⟩ := Set.mem_iUnion₂.1 (ht hq')
  exact ⟨g, hg, (QuotientGroup.eq.2 hgq).trans (QuotientGroup.out_eq' q)⟩

theorem hk_map {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL ι F) V) (σ : Representation ℂ (GL ι F) W) (f : V →ₗ[ℂ] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (hE : IsHk K e) (v : V) :
    f (hk ρ K e v) = hk σ K e (f v) := by
  unfold hk
  have hfin : (Function.support fun q : GL ι F ⧸ K => e q.out • ρ q.out v).Finite :=
    (finite_cosets hE).subset fun q hq h0 => hq (by simp [show e q.out = 0 from h0])
  rw [map_finsum f hfin]
  simp only [map_smul, hf]

theorem exists_iterate_eq_zero {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (hE : IsHk K e) (π : Representation ℂ (GL ι F) V)
    (hkill : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL ι F) W), IsSmooth τ →
      τ.IsIrreducible → IsEmpty (τ.Equiv π) → ∀ w ∈ fixed τ K, hk τ K e w = 0)
    (ρ : Representation ℂ (GL ι F) U) (hρ : IsSmooth ρ) (hfl : HasFiniteLength ρ)
    (hns : ¬ IsSubquotient π ρ) (S : Subrepresentation ρ) :
    ∃ r : ℕ, ∀ u ∈ S.toSubmodule, u ∈ fixed ρ K → (hk ρ K e)^[r] u = 0 := by
  obtain ⟨hGT, hLT⟩ := (hasFiniteLength_iff_wellFounded ρ).1 hfl
  induction S using WellFoundedLT.induction with
  | ind S ih =>
    by_cases hS : S = ⊥
    · subst hS
      exact ⟨0, fun u hu _ => hu⟩
    obtain ⟨T, hT, hmax⟩ := (wellFounded_gt (α := Subrepresentation ρ)).has_min {T | T < S}
      ⟨⊥, bot_lt_iff_ne_bot.2 hS⟩
    have hcov : T ⋖ S := ⟨hT, fun c h1 h2 => hmax c h2 h1⟩
    let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    have hsq : IsSubquotient (subQuot S T) ρ := ⟨S, p, Submodule.mkQ_surjective _⟩
    have hne : IsEmpty ((subQuot S T).Equiv π) := ⟨fun φ => hns
      ((IsSubquotient.trans (IsSubquotient.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective) hsq))⟩
    obtain ⟨r, hr⟩ := ih T hT
    refine ⟨r + 1, fun u huS hufix => ?_⟩
    have hfixS : (Submodule.mkQ _ (⟨u, huS⟩ : S.toSubmodule) :
        S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) ∈ fixed (subQuot S T) K := by
      intro h
      have h1 : ρ (h : GL ι F) u = u := by simpa using hufix h
      have h2 : S.toRepresentation (h : GL ι F) ⟨u, huS⟩ = ⟨u, huS⟩ := Subtype.ext h1
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      exact congrArg (Submodule.mkQ _) h2
    have h0 := hkill _ (subQuot S T) (hsq.isSmooth hρ) (isIrreducible_subQuot hcov) hne _ hfixS
    have h1 : (hk S.toRepresentation K e ⟨u, huS⟩ : S.toSubmodule).1 = hk ρ K e u :=
      hk_map S.toRepresentation ρ S.toSubmodule.subtype (fun _ _ => rfl) hE ⟨u, huS⟩
    have h2 := hk_map S.toRepresentation (subQuot S T) (Submodule.mkQ _) (fun _ _ => rfl) hE ⟨u, huS⟩
    rw [h0] at h2
    have h3 : hk ρ K e u ∈ T.toSubmodule := by
      rw [← h1]
      exact (Submodule.Quotient.mk_eq_zero (T.toSubmodule.comap S.toSubmodule.subtype)).1 h2
    rw [Function.iterate_succ_apply]
    exact hr _ h3 (GlobalTheory.CompanionTheory.HeckeFix.hk_mem_fixed F ι K e hE U ρ u hufix).1

theorem subOfNonNil : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], SubOfNonNil F ι := by
  intro F _ _ _ _ ι _ _ K e hE V _ _ π _ _ hkill U _ _ ρ hρ hfl hnil
  by_contra hns
  obtain ⟨r, hr⟩ := exists_iterate_eq_zero hE π hkill ρ hρ hfl hns ⊤
  obtain ⟨u, hu, hne⟩ := hnil r
  exact hne (hr u trivial hu)

end GlobalTheory.CompanionTheory.HeckeSub
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightedSumDecompositionDenominatorsStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_sum_decomposition_denominators : ∀ (r l N : ℕ) (w : (Fin r → ℕ) → ℚ), 0 < l → GoodWeight l w → (∀ m, ∃ z : ℤ, w m = z) → ∃ (Q : Type) (_ : Fintype Q) (cs : Q → List (Fin r)) (u : Q → (Fin r → ℕ) → ℚ) (K : ℕ), (∀ q, BddW (u q)) ∧ (∀ q i, (cs q).count i = N ∨ ∀ m, m i ≠ 0 → u q m = 0) ∧ (∀ q m, ∃ z : ℤ, (l : ℚ) ^ K * u q m = z) ∧ ∀ g : (Fin r → ℕ) → ℂ, Summable g → ∑' m, (w m : ℂ) * g m = ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) g m := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Integral.expansion_all_variables_int | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Integral.expansion_all_variables_int | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Integral.expansion_all_variables_int <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelOneVanishAboveDimStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_level_one_vanish_above_dim : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (U : Cov q) (d : ℕ), (∀ α, U.d α ≤ d) →
    ∀ j, Subsingleton (CH.H (sq (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) ((d : ℤ) + 1)) (IdF.bot _)) j) := by
  first | exact @GlobalTheory.CompanionTheory.WittLevel.Van.witt_level_one_filtration_vanish | exact GlobalTheory.CompanionTheory.WittLevel.Van.witt_level_one_filtration_vanish | (intros; apply GlobalTheory.CompanionTheory.WittLevel.Van.witt_level_one_filtration_vanish <;> assumption)
end

