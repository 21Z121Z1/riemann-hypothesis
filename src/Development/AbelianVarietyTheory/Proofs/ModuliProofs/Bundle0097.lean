import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0095
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FderivFnAddLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.Uniq

section
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}

theorem ex_add_lattice (z : Fin g → ℂ) (l : u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

theorem mem_dom_add_lattice (m : A₀.left ⟶ X) (W : X.Opens) (z : Fin g → ℂ) (l : u.Λ) :
    z + l ∈ dom u m W ↔ z ∈ dom u m W := by
  show ⊤ ≤ ((u.ex (z + l)).left ≫ m) ⁻¹ᵁ W ↔ ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ W
  rw [ex_add_lattice]

theorem fderiv_fn_add_lattice (m : A₀.left ⟶ X) (W : X.Opens) (f : Γ(X, W)) (z : Fin g → ℂ) (l : u.Λ) :
    fderiv ℂ (fn u m W f) (z + l) = fderiv ℂ (fn u m W f) z := by
  have h : (fun w => fn u m W f (w + (l : Fin g → ℂ))) = fn u m W f := by
    funext w
    unfold fn
    rw [ex_add_lattice]
  calc fderiv ℂ (fn u m W f) (z + l) = fderiv ℂ (fun w => fn u m W f (w + (l : Fin g → ℂ))) z :=
        (fderiv_comp_add_right (l : Fin g → ℂ)).symm
    _ = fderiv ℂ (fn u m W f) z := by rw [h]

theorem ptDer_sub {y : Sp ℂ ⟶ X} {δ δ' : ∀ W : X.Opens, Γ(X, W) → ℂ} (h : PtDer y δ) (h' : PtDer y δ') :
    PtDer y (fun W f => δ W f - δ' W f) where
  add W hW f f' := by
    rw [h.add W hW f f', h'.add W hW f f']
    ring
  mul W hW f f' := by
    rw [h.mul W hW f f', h'.mul W hW f f']
    ring
  res W W' hle hW' f := by
    rw [h.res W W' hle hW' f, h'.res W W' hle hW' f]
end

theorem ks_unique : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D Θ Θ' s s', KSRel u p m D Θ s → KSRel u p m D Θ' s' → Θ = Θ' := by
  intro P₀ u Hm χ hG R _ x₀ X p m hp hpb D Θ Θ' s s' hs hs'
  obtain ⟨w, hwd, hw⟩ := GlobalTheory.T.exists_differentiableOn_verticalVectorField P₀ u Hm χ hG R x₀ X p m hp hpb P₀.g Set.univ id
    (fun z W f => s z W f - s' z W f) isOpen_univ differentiable_id
    (fun z _ => ⟨ptDer_sub (hs.der z) (hs'.der z), fun r => by
      show s z ⊤ (constFn p ⊤ r) - s' z ⊤ (constFn p ⊤ r) = 0
      rw [hs.base, hs'.base, sub_self]⟩)
    (fun W f => ((hs.hol W f).sub (hs'.hol W f)).mono fun z hz => hz.2)
  have hw' : ∀ z W f, z ∈ dom u m W → s z W f - s' z W f = fderiv ℂ (fn u m W f) z (w z) :=
    fun z W f hz => hw z (Set.mem_univ z) W f hz
  have hper : ∀ (l : u.Λ) z, w (z + l) = w z + (Θ - Θ').mulVec (star (l : Fin P₀.g → ℂ)) := by
    intro l z
    obtain ⟨v, -, huniq⟩ := GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hG R x₀ X p m hp hpb z
      (fun W f => s z W f - s' z W f) (ptDer_sub (hs.der z) (hs'.der z)) (fun r => by
        show s z ⊤ (constFn p ⊤ r) - s' z ⊤ (constFn p ⊤ r) = 0
        rw [hs.base, hs'.base, sub_self])
    have e1 := huniq (w z) (fun W f hz => hw' z W f hz)
    have e2 := huniq (w (z + l) - (Θ - Θ').mulVec (star (l : Fin P₀.g → ℂ))) (fun W f hz => by
      have a1 := hw' (z + l) W f ((mem_dom_add_lattice u m W z l).2 hz)
      have a2 := hs.per l W f z hz
      have a3 := hs'.per l W f z hz
      rw [fderiv_fn_add_lattice] at a1
      show s z W f - s' z W f = _
      rw [map_sub, Matrix.sub_mulVec, map_sub]
      linear_combination a1 - a2 + a3)
    rw [← e1] at e2
    exact sub_eq_iff_eq_add.mp e2
  have hdisc : DiscreteTopology u.Λ := u.discrete
  have hspan : Submodule.span ℝ (u.Λ : Set (Fin P₀.g → ℂ)) = ⊤ := u.full
  have hwd' : Differentiable ℂ w := differentiableOn_univ.mp hwd
  ext i j
  have key := GlobalTheory.entire_antilinear_periods_const P₀.g u.Λ hdisc hspan (fun z => w z i) ((Θ - Θ') i)
    (differentiable_pi.mp hwd' i) (fun l z => congrFun (hper l z) i)
  have hij := congrFun key.1 j
  simp only [Matrix.sub_apply, Pi.zero_apply, sub_eq_zero] at hij
  exact hij

end GlobalTheory.KS.Uniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KodairaSpencerCommutesWithEndomorphism
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.KS.Endo

private theorem valAt'_comp_lemma {Y Z : Scheme.{0}} (x : Sp ℂ ⟶ Y) (φ : Y ⟶ Z) (U : Z.Opens) (a : Γ(Z, U)) :
    valAt' (x ≫ φ) U a = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom a) := by
  unfold valAt'
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · have h' : ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U := h
    rw [dif_pos h, dif_pos h']
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U := h
    rw [dif_neg h, dif_neg h']

theorem ptDer_push {X Y : Scheme.{0}} (y : Sp ℂ ⟶ X) (f : X ⟶ Y) (δ : ∀ W : X.Opens, Γ(X, W) → ℂ) (h : PtDer y δ) :
    PtDer (y ≫ f) (fun W a => δ (f ⁻¹ᵁ W) ((f.app W).hom a)) where
  add W hW a b := by
    rw [map_add]
    exact h.add (f ⁻¹ᵁ W) hW _ _
  mul W hW a b := by
    rw [map_mul, valAt'_comp_lemma y f W a, valAt'_comp_lemma y f W b]
    exact h.mul (f ⁻¹ᵁ W) hW _ _
  res W W' hle hW a := by
    have hle' : f ⁻¹ᵁ W' ≤ f ⁻¹ᵁ W := fun x hx => hle hx
    have nat : (f.app W').hom (resG Y hle a) = resG X hle' ((f.app W).hom a) :=
      congrArg (fun φ : Γ(Y, W) ⟶ Γ(X, f ⁻¹ᵁ W') => φ.hom a) (f.naturality (homOfLE hle).op)
    rw [nat]
    exact h.res (f ⁻¹ᵁ W) (f ⁻¹ᵁ W') hle' hW _

theorem ptDer_sub {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (δ δ' : ∀ W : X.Opens, Γ(X, W) → ℂ) (h : PtDer y δ) (h' : PtDer y δ') :
    PtDer y (fun W a => δ W a - δ' W a) where
  add W hW a b := by
    rw [h.add W hW, h'.add W hW]
    ring
  mul W hW a b := by
    rw [h.mul W hW, h'.mul W hW]
    ring
  res W W' hle hW a := by
    rw [h.res W W' hle hW, h'.res W W' hle hW]

theorem app_top_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (f : X ⟶ X) (hf : f ≫ p = p) (r : R) :
    (f.app ⊤).hom (constFn p ⊤ r) = resG X (le_top : f ⁻¹ᵁ ⊤ ≤ ⊤) (constFn p ⊤ r) := by
  have aux : ∀ q : X ⟶ Sp R, q = p → ∀ e e', q.appLE ⊤ (f ⁻¹ᵁ ⊤) e = p.appLE ⊤ (f ⁻¹ᵁ ⊤) e' := by
    rintro q rfl e e'
    rfl
  have key : ∀ e, p.appLE ⊤ ⊤ e ≫ f.app ⊤ =
      p.appLE ⊤ ⊤ e ≫ X.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ ⊤ ≤ ⊤)).op := by
    intro e
    rw [Scheme.Hom.appLE_map, Scheme.Hom.app_eq_appLE f, Scheme.Hom.appLE_comp_appLE]
    exact aux _ hf _ _
  unfold constFn
  exact congrArg (fun φ : Γ(Sp R, ⊤) ⟶ Γ(X, f ⁻¹ᵁ ⊤) => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (key _)

variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}

theorem ex_add_lattice (z l : Fin g → ℂ) (hl : l ∈ u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 hl, _root_.mul_one]

theorem fn_differentiableAt (m : A₀.left ⟶ X) (W : X.Opens) (a : Γ(X, W)) (z : Fin g → ℂ) (hz : z ∈ dom u m W) :
    DifferentiableAt ℂ (fn u m W a) z := by
  have hU := u.hol (m ⁻¹ᵁ W) ((m.app W).hom a)
  have hz' : z ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W)} := hz
  have heq : fn u m W a = fun z => valAt' (u.ex z).left (m ⁻¹ᵁ W) ((m.app W).hom a) := by
    funext w
    exact valAt'_comp_lemma (u.ex w).left m W a
  rw [heq]
  exact hU.2.differentiableAt (hU.1.mem_nhds hz')

theorem fderiv_fn_add_lattice (m : A₀.left ⟶ X) (W : X.Opens) (a : Γ(X, W)) (z l : Fin g → ℂ) (hl : l ∈ u.Λ) :
    fderiv ℂ (fn u m W a) (z + l) = fderiv ℂ (fn u m W a) z := by
  have hper : (fun w => fn u m W a (w + l)) = fn u m W a := by
    funext w
    unfold fn
    rw [ex_add_lattice u w l hl]
  rw [← fderiv_comp_add_right, hper]

theorem comm_of_endo : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D Θ s, KSRel u p m D Θ s → ∀ (f : X ⟶ X) (f₀ : P₀.A ⟶ P₀.A) (F : (Fin P₀.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ)), f ≫ p = p → f₀.left ≫ m = m ≫ f → (∀ z, u.ex (F z) = u.ex z ≫ f₀) → Comm Θ F := by
  intro P₀ u Hm χ hU R instR x₀ X p m hp hpb D Θ s hKS f f₀ F hfp hf₀ hF
  have hFdiff : Differentiable ℂ F := by
    have := (LinearMap.toContinuousLinearMap F).differentiable
    rwa [LinearMap.coe_toContinuousLinearMap'] at this

  have hpt : ∀ z, (u.ex z).left ≫ m ≫ f = (u.ex (F z)).left ≫ m := by
    intro z
    rw [hF z, Over.comp_left, Category.assoc, hf₀]

  have hex0 : u.ex 0 = 1 := (u.ker 0).2 (zero_mem _)
  have hone : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ P₀.A) ≫ f₀ = 1 := by
    have h0 := hF 0
    rw [map_zero, hex0] at h0
    exact h0.symm
  have hFl : ∀ l ∈ u.Λ, F l ∈ u.Λ := by
    intro l hl
    rw [← u.ker, hF, (u.ker l).2 hl, hone]
  have hexF : ∀ z, ∀ l ∈ u.Λ, u.ex (F (z + l)) = u.ex (F z) := by
    intro z l hl
    rw [map_add]
    exact ex_add_lattice u _ _ (hFl l hl)
  have hdom : ∀ W z, z ∈ dom u m (f ⁻¹ᵁ W) ↔ F z ∈ dom u m W := by
    intro W z
    show ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ (f ⁻¹ᵁ W) ↔ ⊤ ≤ ((u.ex (F z)).left ≫ m) ⁻¹ᵁ W
    rw [← hpt z]
    rfl
  have hfn : ∀ W a z, fn u m (f ⁻¹ᵁ W) ((f.app W).hom a) z = fn u m W a (F z) := by
    intro W a z
    show valAt' ((u.ex z).left ≫ m) (f ⁻¹ᵁ W) ((f.app W).hom a) = valAt' ((u.ex (F z)).left ≫ m) W a
    rw [← hpt z, ← Category.assoc, valAt'_comp_lemma ((u.ex z).left ≫ m) f W a]
  have hfd : ∀ W a z, F z ∈ dom u m W → fderiv ℂ (fn u m (f ⁻¹ᵁ W) ((f.app W).hom a)) z =
      (fderiv ℂ (fn u m W a) (F z)).comp (LinearMap.toContinuousLinearMap F) := by
    intro W a z hz
    have e : fn u m (f ⁻¹ᵁ W) ((f.app W).hom a) = fn u m W a ∘ (LinearMap.toContinuousLinearMap F) := by
      funext w
      exact hfn W a w
    rw [e]
    exact ((fn_differentiableAt u m W a (F z) hz).hasFDerivAt.comp z
      (LinearMap.toContinuousLinearMap F).hasFDerivAt).fderiv

  let d : (Fin P₀.g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ :=
    fun z W a => s (F z) W a - s z (f ⁻¹ᵁ W) ((f.app W).hom a)
  have hd : ∀ z, PtDer ((u.ex (F z)).left ≫ m) (d z) ∧ ∀ r, d z ⊤ (constFn p ⊤ r) = 0 := by
    intro z
    refine ⟨?_, ?_⟩
    · have h1 := ptDer_push _ f (s z) (hKS.der z)
      rw [Category.assoc, hpt z] at h1
      exact ptDer_sub _ _ _ (hKS.der (F z)) h1
    · intro r
      have htop : ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ (f ⁻¹ᵁ ⊤) := fun x _ => trivial
      show s (F z) ⊤ (constFn p ⊤ r) - s z (f ⁻¹ᵁ ⊤) ((f.app ⊤).hom (constFn p ⊤ r)) = 0
      rw [app_top_constFn p f hfp r, (hKS.der z).res ⊤ (f ⁻¹ᵁ ⊤) le_top htop, hKS.base, hKS.base, sub_self]
  have hdhol : ∀ W a, DifferentiableOn ℂ (fun z => d z W a) {z ∈ Set.univ | F z ∈ dom u m W} := by
    intro W a
    have h1 : DifferentiableOn ℂ (fun z => s (F z) W a) {z ∈ Set.univ | F z ∈ dom u m W} :=
      (hKS.hol W a).comp hFdiff.differentiableOn (fun z hz => hz.2)
    have h2 : DifferentiableOn ℂ (fun z => s z (f ⁻¹ᵁ W) ((f.app W).hom a)) {z ∈ Set.univ | F z ∈ dom u m W} :=
      (hKS.hol (f ⁻¹ᵁ W) ((f.app W).hom a)).mono (fun z hz => (hdom W z).2 hz.2)
    exact h1.sub h2
  obtain ⟨w, hwd, hw⟩ := GlobalTheory.T.exists_differentiableOn_verticalVectorField P₀ u Hm χ hU R x₀ X p m hp hpb P₀.g Set.univ F d isOpen_univ hFdiff
    (fun z _ => hd z) hdhol

  have hper : ∀ z, ∀ l ∈ u.Λ,
      w (z + l) = w z + (Θ.mulVec (star (F l)) - F (Θ.mulVec (star l))) := by
    intro z l hl
    have hFl' := hFl l hl
    have hpt' : PtDer ((u.ex (F z)).left ≫ m) (d (z + l)) ∧ ∀ r, d (z + l) ⊤ (constFn p ⊤ r) = 0 := by
      rw [← hexF z l hl]
      exact hd (z + l)
    obtain ⟨w0, -, huniq⟩ := GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hU R x₀ X p m hp hpb (F z) (d (z + l)) hpt'.1 hpt'.2
    refine (huniq _ ?_).trans (huniq _ ?_).symm
    · intro W a hz
      have hz' : F (z + l) ∈ dom u m W := by
        show ⊤ ≤ ((u.ex (F (z + l))).left ≫ m) ⁻¹ᵁ W
        rw [hexF z l hl]
        exact hz
      rw [hw (z + l) (Set.mem_univ _) W a hz', map_add, fderiv_fn_add_lattice u m W a (F z) (F l) hFl']
    · intro W a hz
      have hzf : z ∈ dom u m (f ⁻¹ᵁ W) := (hdom W z).2 hz
      have e1 := hKS.per ⟨F l, hFl'⟩ W a (F z) hz
      have e2 := hKS.per ⟨l, hl⟩ (f ⁻¹ᵁ W) ((f.app W).hom a) z hzf
      have hd0 := hw z (Set.mem_univ _) W a hz
      show s (F (z + l)) W a - s (z + l) (f ⁻¹ᵁ W) ((f.app W).hom a) = _
      rw [map_add, e1, e2, hfd W a z hz]
      show _ = fderiv ℂ (fn u m W a) (F z) (w z + (Θ.mulVec (star (F l)) - F (Θ.mulVec (star l))))
      rw [ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap', map_add, map_sub, ← hd0]
      ring

  have hc_add : ∀ v v' : Fin P₀.g → ℂ,
      Θ.mulVec (star (F (v + v'))) - F (Θ.mulVec (star (v + v'))) =
        (Θ.mulVec (star (F v)) - F (Θ.mulVec (star v))) + (Θ.mulVec (star (F v')) - F (Θ.mulVec (star v'))) := by
    intro v v'
    rw [map_add, star_add, star_add, Matrix.mulVec_add, Matrix.mulVec_add, map_add]
    abel
  have hc_smul : ∀ (a : ℂ) (v : Fin P₀.g → ℂ),
      Θ.mulVec (star (F (a • v))) - F (Θ.mulVec (star (a • v))) =
        star a • (Θ.mulVec (star (F v)) - F (Θ.mulVec (star v))) := by
    intro a v
    rw [map_smul, star_smul, star_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, map_smul, smul_sub]
  let cA : (Fin P₀.g → ℂ) →+ (Fin P₀.g → ℂ) :=
    AddMonoidHom.mk' (fun v => Θ.mulVec (star (F v)) - F (Θ.mulVec (star v))) hc_add
  have hexp : ∀ v : Fin P₀.g → ℂ, Θ.mulVec (star (F v)) - F (Θ.mulVec (star v)) =
      ∑ j, star (v j) • cA (fun k => if j = k then 1 else 0) := by
    intro v
    have h1 : cA v = ∑ j, cA (v j • fun k => if j = k then 1 else 0) := by
      conv_lhs => rw [pi_eq_sum_univ v]
      exact map_sum cA _ _
    refine h1.trans (Finset.sum_congr rfl fun j _ => ?_)
    exact hc_smul (v j) _

  have hwdiff : Differentiable ℂ w := differentiableOn_univ.1 hwd
  have hzero : ∀ i j, cA (fun k => if j = k then 1 else 0) i = 0 := by
    intro i j
    have hperi : ∀ (l : u.Λ) (z : Fin P₀.g → ℂ), w (z + l) i =
        w z i + (fun j => cA (fun k => if j = k then 1 else 0) i) ⬝ᵥ star (l : Fin P₀.g → ℂ) := by
      intro l z
      rw [hper z l l.2, Pi.add_apply, hexp (l : Fin P₀.g → ℂ)]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Pi.star_apply]
      congr 1
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hI := GlobalTheory.T.entire_antilinear_lattice_periods_const P₀.g u.Λ u.discrete u.full (fun z => w z i) _ (differentiable_pi.1 hwdiff i) hperi
    exact congrFun hI.1 j
  intro z
  have hz := hexp z
  have hz0 : Θ.mulVec (star (F z)) - F (Θ.mulVec (star z)) = 0 := by
    rw [hz]
    funext i
    simp [hzero]
  exact (sub_eq_zero.1 hz0).symm

end GlobalTheory.KS.Endo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormPsiPullLocalRingsOfIntegers
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.PsiNormPull

theorem valF_eq_valR' {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valF x U f = valR x U f := by
  rfl

theorem toStk_map_valR {A F : Type} [CommRing A] [Field F] (ψ : A →+* F) {X : Scheme.{0}} (x : Sp A ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (z : Sp F) (a : Γ(X, U)ˣ) :
    toStk z (ψ (valR x U a.val)) = (gm (spMap ψ ≫ x) z U a).val := by
  obtain ⟨h', e⟩ := CrdCalc.valR_spMap ψ x U h
  rw [← e, ← valF_eq_valR']
  exact toStk_valF _ U z (h' trivial) a

theorem norm_eq_one_of_isUnit {A F : Type} [CommRing A] [NormedField F] (ψ : A →+* F) (hψ : ∀ a, ‖ψ a‖ ≤ 1)
    {a : A} (ha : IsUnit a) : ‖ψ a‖ = 1 := by
  obtain ⟨u, rfl⟩ := ha
  have e : ‖ψ u.val‖ * ‖ψ (u⁻¹).val‖ = 1 := by rw [← norm_mul, ← map_mul, u.mul_inv, map_one, norm_one]
  refine le_antisymm (hψ _) ?_
  calc (1 : ℝ) = ‖ψ u.val‖ * ‖ψ (u⁻¹).val‖ := e.symm
    _ ≤ ‖ψ u.val‖ * 1 := mul_le_mul_of_nonneg_left (hψ _) (norm_nonneg _)
    _ = _ := _root_.mul_one _

theorem norm_psi_pull : ∀ (p : ℕ) [Fact p.Prime] (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'] [Algebra (FractionRing V) (PadicAlgCl p)] [Algebra (FractionRing V') (PadicAlgCl p)] (φ : V →+* V'), (∀ v : V, algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V _ v) = algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ (φ v))) → (∀ v : V', ‖algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ v)‖ ≤ 1) → ∀ (D : DegPre V) (D' : DegPre V') (hD : IsPullDeg φ D D') (χ : D'.X) (j : D.P.L.ι) (j' : D'.P.L.ι), ⊤ ≤ (D.c (hD.xe χ)).left ⁻¹ᵁ D.P.L.U j → ⊤ ≤ (D'.c χ).left ⁻¹ᵁ D'.P.L.U j' → ‖algebraMap (FractionRing V') (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing V'))) _ ((D'.psi χ).s fun _ => j').val)‖ = ‖algebraMap (FractionRing V) (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing V))) _ ((D.psi (hD.xe χ)).s fun _ => j).val)‖ := by
  intro p _ V V' _ _ _ _ _ _ _ _ φ hφ hn D D' hD χ j j' hj hj'
  let F := PadicAlgCl p
  let ψ' : V' →+* F := (algebraMap (FractionRing V') F).comp (algebraMap V' (FractionRing V'))
  have hsq : jFK (R := V') F ≫ jK V' ≫ spMap φ = jFK (R := V) F ≫ jK V := by
    refine ((congrArg (jFK (R := V') F ≫ ·) (spMap_comp φ _).symm).trans (spMap_comp _ _).symm).trans
      ((congrArg spMap ?_).trans (spMap_comp _ _))
    exact RingHom.ext fun v => (hφ v).symm
  have z : Sp F := (default : PrimeSpectrum F)
  let Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  have hΦ : ⊤ ≤ ((D'.c χ).left ≫ Φ) ⁻¹ᵁ D.P.L.U j := by
    rw [show (D'.c χ).left ≫ Φ = _ from hD.c_pr χ]
    exact fun y _ => hj (Set.mem_univ ((specOf φ) y))
  let U := (D.P.L.pull Φ).U (fun _ => j) ⊓ D'.P.L.U j'
  have hU : ⊤ ≤ (D'.c χ).left ⁻¹ᵁ U := fun y _ => ⟨mem_pull.2 (hΦ (Set.mem_univ y)), hj' (Set.mem_univ y)⟩
  have m' : ∀ y, D'.xK χ y ∈ D'.P.L.U j' := fun y => hj' (Set.mem_univ (jK V' y))
  have m : ∀ y, D.xK (hD.xe χ) y ∈ D.P.L.U j := fun y => hj (Set.mem_univ (jK V y))
  have e := pmaps_psi hD F hsq χ _ (𝟙 _) z (fun _ => j) (fun _ => j')
    (fun _ => hΦ (Set.mem_univ (jK V' (jFK (R := V') F z)))) (fun _ => m' _)
  have g₁ := gm_pullGen D.P.L (fun _ : PUnit => D.xK (hD.xe χ)) (fun _ => -1) (D.psi (hD.xe χ)) (jFK (R := V) F)
    (𝟙 _ ≫ 𝟙 _) z (fun _ => j) (Set.mem_iInter.2 fun _ => m _)
  have g₂ := gm_pullGen D'.P.L (fun _ : PUnit => D'.xK χ) (fun _ => -1) (D'.psi χ) (jFK (R := V') F)
    (𝟙 _) z (fun _ => j') (Set.mem_iInter.2 fun _ => m' _)
  rw [Fintype.prod_unique] at e
  replace e := g₁.symm.trans (e.trans (congrArg₂ (· * ·) (zpow_neg_one _) g₂))
  rw [eq_inv_mul_iff_mul_eq] at e
  simp only [Category.id_comp] at e
  have a := toStk_map_valR (algebraMap (FractionRing V) F) (𝟙 _)
    (LB.wchart D.P.L (fun _ : PUnit => D.xK (hD.xe χ)) fun _ => j) (fun y _ => Set.mem_iInter.2 fun _ => m y) z
    ((D.psi (hD.xe χ)).s fun _ => j)
  have a' := toStk_map_valR (algebraMap (FractionRing V') F) (𝟙 _)
    (LB.wchart D'.P.L (fun _ : PUnit => D'.xK χ) fun _ => j') (fun y _ => Set.mem_iInter.2 fun _ => m' y) z
    ((D'.psi χ).s fun _ => j')
  rw [Category.comp_id, ← valF_eq_valR'] at a a'
  have b := toStk_map_valR ψ' (D'.c χ).left U hU z (hD.w.s (fun _ => j, j'))
  have hpt : spMap ψ' ≫ (D'.c χ).left = jFK (R := V') F ≫ D'.xK χ :=
    (congrArg (· ≫ (D'.c χ).left) (spMap_comp _ _)).trans (Category.assoc _ _ _)
  have b' : toStk z (ψ' (valR (D'.c χ).left U (hD.w.s (fun _ => j, j')).val)) =
      (gw hD.w (jFK (R := V') F ≫ D'.xK χ) z j j').val := by
    rw [← hpt]; exact b
  have hu : IsUnit (valR (D'.c χ).left U (hD.w.s (fun _ => j, j')).val) := by
    exact (congrArg IsUnit (CrdCalc.valR_eq (R := V') (D'.c χ).left U hU _)).mpr ((Units.isUnit _).map _)
  have key := (toStk z).injective (a'.trans ((congrArg Units.val e).symm.trans
    ((Units.val_mul _ _).trans ((congrArg₂ (· * ·) b' a).symm.trans (map_mul _ _ _).symm))))
  refine (congrArg norm key).trans ?_
  rw [norm_mul, norm_eq_one_of_isUnit ψ' hn hu, _root_.one_mul]
  rfl

end GlobalTheory.ZH.PsiNormPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PadicIntermediateFieldIntRingCompleteDvr
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem lift_mem_valuationSubring_iff {K L : Type*} [Field K] [Field L] (A : ValuationSubring L) (i : K →+* L)
    (h : Function.Injective (i.comp (A.comap i).subtype)) (x : FractionRing (A.comap i)) :
    IsFractionRing.lift (A := A.comap i) (K := FractionRing (A.comap i)) h x ∈ A ↔
      x ∈ Set.range (algebraMap (A.comap i) (FractionRing (A.comap i))) := by
  let f := FractionRing.algEquiv (A.comap i) K
  have hf : IsFractionRing.lift (A := A.comap i) (K := FractionRing (A.comap i)) h =
      i.comp f.toRingEquiv.toRingHom := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (A.comap i)) (RingHom.ext fun a => ?_)
    refine (IsFractionRing.lift_algebraMap h a).trans ?_
    exact congrArg i (f.commutes a).symm
  rw [hf]
  refine ⟨fun hx => ⟨⟨f x, hx⟩, f.injective (f.commutes _)⟩, ?_⟩
  rintro ⟨v, rfl⟩
  rw [← hf, IsFractionRing.lift_algebraMap]
  exact v.2

theorem intRing_complete_dvr : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → IsDiscreteValuationRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ∧ IsAdicComplete (IsLocalRing.maximalIdeal (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ∧ ∀ x : FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K), ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K))) := by
  intro p _ K hK
  have hmem : ∀ x : K, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := fun x => mem_OO_iff _
  let e : integralClosure ℤ_[p] K ≃+* GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K :=
    { toFun := fun x => ⟨x.1, (hmem _).2 ((mem_integralClosure_padicInt_iff K _).1 x.2)⟩
      invFun := fun x => ⟨x.1, (mem_integralClosure_padicInt_iff K _).2 ((hmem _).1 x.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  have hc := CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[p] (integralClosure ℤ_[p] K)
  refine ⟨IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, ?_, fun x => ?_⟩
  · have := (IsAdicComplete.congr_ringEquiv (IsLocalRing.maximalIdeal _) e).2 hc
    rwa [IsLocalRing.map_ringEquiv_maximalIdeal] at this
  · rw [← mem_OO_iff]
    exact lift_mem_valuationSubring_iff (OO p) (algebraMap K (PadicAlgCl p))
      (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing_injective K) x

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsOfGeometric
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem torsionSection_eq_labelled_of_isDomain : ∀ (R : Type) [CommRing R] [IsDomain R] (P : PolAV (Sp R)) (M : ℕ) (I : Type) (pt : I → (baseOver (Sp R) ⟶ P.A)), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (z : Over.mk x ⟶ P.A), z ^ M = 1 → ∃ a, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R)) ≫ pt a = z) → ∀ y : baseOver (Sp R) ⟶ P.A, y ^ M = 1 → ∃ a, pt a = y := by
  intro R _ _ P M I pt h y hy
  let K := AlgebraicClosure (FractionRing R)
  let j : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hj : Function.Injective j :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  have hdom : IsDominant (Geo.Tor.spMap j) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)⟩
  have hprop : IsProper P.A.hom := P.isAb.proper
  obtain ⟨a, ha⟩ := h K (Geo.Tor.spMap j)
    ((Over.homMk (Geo.Tor.spMap j) (by simp) : Over.mk (Geo.Tor.spMap j) ⟶ baseOver (Sp R)) ≫ y)
    (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])
  exact ⟨a, Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp R) P.A.hom
    ((Over.w (pt a)).trans (Over.w y).symm) (Geo.Tor.spMap j) (congrArg Over.Hom.left ha))⟩

end GlobalTheory
end

