import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

structure GenWeil (G : Over X) [GrpObj G] (L : LB G.left) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (n : ℕ)
    (e : (Over.mk ξ ⟶ G) → (Over.mk ξ ⟶ G) → Ωˣ) : Prop where
  finite : Finite {x : Over.mk ξ ⟶ G // x ^ n = 1}
  mul_left : ∀ x x' g, x ^ n = 1 → x' ^ n = 1 → g ^ n = 1 → e (x * x') g = e x g * e x' g
  mul_right : ∀ x g g', x ^ n = 1 → g ^ n = 1 → g' ^ n = 1 → e x (g * g') = e x g * e x g'
  perfect : ∀ χ : (Over.mk ξ ⟶ G) → Ωˣ, (∀ g g', g ^ n = 1 → g' ^ n = 1 → χ (g * g') = χ g * χ g') →
    ∃ x, x ^ n = 1 ∧ ∀ g, g ^ n = 1 → χ g = e x g
  nondeg : ∀ g, g ^ n = 1 → (∀ x, x ^ n = 1 → e x g = 1) → g = 1
  weil : ∀ x g, x ^ n = 1 → g ^ n = 1 → ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k)
    (xk gk : Over.mk (spMap i ≫ ξ) ⟶ G) (c : kˣ), xk.left = spMap i ≫ x.left → gk.left = spMap i ≫ g.left →
      (Out.WeilIs G L n xk gk (unitOn c) ↔ (c : k) = i (e x g))

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HtWSpanSingleton
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HtLatCheck

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
variable (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
  (σ : O →+* Ω)

theorem secVal_one {B : Type} [CommRing B] {Z : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Z) (W : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ W) : secVal x W h 1 = 1 := by
  simp [secVal]

theorem fullTorsion_one : FullTorsion G ξ 1 := by
  intro k _ i g hg
  rw [pow_one] at hg
  subst hg
  refine ⟨1, ?_⟩
  have h := MonObj.comp_one (M := G) (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ ξ) ⟶ Over.mk ξ)
  rw [← h]; rfl

theorem isHTAt_add_nsmul {x : Over.mk ξ ⟶ G} {q : Cpt ξ} {w w' : Module.Dual Ω E}
    (hw : M.IsHTAt L n x q w) (hw' : w' ∈ M.omLat q) : M.IsHTAt L n x q (w + n • w') := by
  obtain ⟨h1, W, f, hW, hv, hd⟩ := hw
  refine ⟨(M.omLat q).add_mem h1 ((M.omLat q).toAddSubmonoid.nsmul_mem hw' n), W, f, hW, hv, fun e v he h => ?_⟩
  obtain ⟨r, hr, hre⟩ := hd e v he h
  refine ⟨r + w' e, (regAt ξ q).add_mem hr (hw' e (Submodule.subset_span ⟨v, he⟩)), ?_⟩
  simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, hre]; ring

theorem isHTAt_one_zero (q : Cpt ξ)
    (h1 : ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (g : Over.mk (spMap i ≫ ξ) ⟶ G) (c : kˣ),
      Out.WeilIs G L n 1 g (unitOn c) → c = 1) : M.IsHTAt L n 1 q 0 := by
  refine ⟨Submodule.zero_mem _, ⊤, 1, trivial, fun k _ _ i xk g c h hx _ hc => ?_, fun e v _ h => ⟨0, (regAt ξ q).zero_mem, ?_⟩⟩
  · have hx1 : xk = 1 := by
      have h := MonObj.comp_one (M := G) (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ ξ) ⟶ Over.mk ξ)
      ext1
      rw [hx, ← h]; rfl
    subst hx1
    rw [secVal_one, h1 k i g c hc]; rfl
  · rw [secVal_one]; simp only [TrivSqZeroExt.snd_one, LinearMap.zero_apply, mul_zero, add_zero]
    exact (RingHom.map_zero (genMap ξ q)).symm

theorem nsmul_mem_htOm (q : Cpt ξ)
    (h1 : ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (g : Over.mk (spMap i ≫ ξ) ⟶ G) (c : kˣ),
      Out.WeilIs G L n 1 g (unitOn c) → c = 1) {w : Module.Dual Ω E} (hw : w ∈ M.omLat q) :
    n • w ∈ M.htOm L n q :=
  Submodule.subset_span ⟨1, one_pow _, by
    simpa using isHTAt_add_nsmul M L n (isHTAt_one_zero M L n q h1) hw⟩

theorem mem_htW_iff (𝔡 : Ideal O) (q : Cpt ξ) (e : E) :
    e ∈ M.htW L n ρ σ 𝔡 q ↔ e ∈ eigSp ρ σ ∧ ∀ d ∈ 𝔡, σ d • e ∈ M.htDual L n ρ σ q := by
  refine ⟨fun he => ⟨M.mem_eigSp_of_mem_htW L n ρ σ 𝔡 he, ?_⟩, fun h => Submodule.subset_span h⟩
  induction he using Submodule.span_induction with
  | mem x hx => exact hx.2
  | zero => intro d _; simp
  | add x y _ _ hx hy => intro d hd; rw [smul_add]; exact Submodule.add_mem _ (hx d hd) (hy d hd)
  | smul c x _ hx =>
    intro d hd
    have : σ d • (c • x) = c • (σ d • x) := by
      show σ d • ((c : Ω) • x) = (c : Ω) • (σ d • x)
      exact smul_comm _ _ _
    rw [this]; exact Submodule.smul_mem _ c (hx d hd)

theorem htW_span_singleton (d : O) (hd : σ d ≠ 0) (q : Cpt ξ) (hσ : ∀ a, σ a ∈ regAt ξ q) :
    M.htW L n ρ σ (Ideal.span {d}) q = (M.htDual L n ρ σ).scale (σ d)⁻¹ q := by
  ext e
  rw [mem_htW_iff]
  constructor
  · rintro ⟨-, h⟩
    refine Submodule.mem_map.2 ⟨σ d • e, h d (Ideal.mem_span_singleton_self d), ?_⟩
    simp [smul_smul, inv_mul_cancel₀ hd]
  · intro h
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 h
    have hue := M.mem_eigSp_of_mem_htDual L n ρ σ hu
    refine ⟨(eigSp ρ σ).smul_mem _ hue, fun a ha => ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    have : σ (b * d) • ((σ d)⁻¹ • u) = (⟨σ b, hσ b⟩ : regAt ξ q) • u := by
      show _ = σ b • u
      rw [smul_smul, map_mul, mul_inv_cancel_right₀ hd]
    show σ (b * d) • ((σ d)⁻¹ • u) ∈ _
    rw [this]; exact Submodule.smul_mem _ _ hu

theorem htDual_bounded (q : Cpt ξ) (hn : ∀ w ∈ M.omLat q, n • w ∈ M.htOm L n q) {e : E}
    (he : e ∈ M.htDual L n ρ σ q) {w : Module.Dual Ω E} (hw : w ∈ M.omLat q) : w (n • e) ∈ regAt ξ q := by
  have := ((M.mem_htDual_iff L n ρ σ q e).1 he).2 _ (hn w hw)
  simpa using this

end GlobalTheory.CompanionTheory.Ar.HtLatCheck
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NonemptyLinearEquivOfPiFinPowFinite
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar.BT

structure TorsTower (p : ℕ) {O : Type} [CommRing O] [IsDomain O] {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] where

  Γ : ∀ n, QFGroup O (LevGrp La p n)

  i : ∀ n, (Γ n).G.left ⟶ G.left
  tors : ∀ n, (Γ n).IsTorsionAlong G y (p ^ n) (i n)
  compat : ∀ n (a : La), ((Γ n).pt (lev p n a)).left ≫ i n = ((Γ (n + 1)).pt (lev p (n + 1) (p • a))).left ≫ i (n + 1)

namespace TorsTower

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] {S : Scheme.{0}} {G : Over S} [GrpObj G]
  {y : Spec (CommRingCat.of O) ⟶ S} {La : Type} [AddCommGroup La] (X : TorsTower p G y La)

def IsDer {L : Type} [AddCommGroup L] [Module O L] (M : LieModel G y L) (n : ℕ)
    (f : LevGrp La p n → O) (w : Module.Dual O L) : Prop :=
  ∃ s : Γ((X.Γ n).G.left, ⊤), (X.Γ n).HasValues s f ∧ ∀ e : L,
    ∃ v : Spec (CommRingCat.of (DualNumber (O ⧸ Ideal.span {((p ^ n : ℕ) : O)}))) ⟶ (X.Γ n).G.left,
      v ≫ (X.Γ n).G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (O ⧸ Ideal.span {((p ^ n : ℕ) : O)})
        (DualNumber (O ⧸ Ideal.span {((p ^ n : ℕ) : O)}))).comp (Ideal.Quotient.mk _))) ∧
      v ≫ X.i n = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {((p ^ n : ℕ) : O)})))) ≫
        (M.pt e).left ∧
      valAt v ⊤ le_top s = TrivSqZeroExt.inl (Ideal.Quotient.mk _ (f 1)) +
        TrivSqZeroExt.inr (Ideal.Quotient.mk (Ideal.span {((p ^ n : ℕ) : O)}) (w e))

def Induces (u : G ⟶ G) (φ : La →+ La) : Prop :=
  ∀ n (a : La), ((X.Γ n).pt (lev p n (φ a))).left ≫ X.i n = ((X.Γ n).pt (lev p n a)).left ≫ X.i n ≫ u.left

def PairingRegular (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ) : Prop :=
  ∀ n, ∃ s : Γ(((X.Γ n).G ⊗ (X.Γ n).G).left, ⊤), ∀ a b : La,
    valAt (lift ((X.Γ n).pt (lev p n a)) ((X.Γ n).pt (lev p n b))).left ⊤ le_top s =
      algebraMap O (FractionRing O) ((ζ n ^ B a b : Oˣ) : O)

end TorsTower

end GlobalTheory.CompanionTheory.Ar.HT
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwTan
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}

def TwTan {g : HostAut H} {Φ : Xo.X ⟶ Xo.X} (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ) (Y : Model Xo c β)
    (Y' : Model Xo c β') {T : Scheme.{0}} (u₁ : T ⟶ Y.t.G.left) (u₂ : T ⟶ Y'.t.G.left) : Prop :=
  ∃ (u : T ⟶ Y.oF.t.G.left) (u' : T ⟶ Y'.oF.t.G.left), u ≫ Y.m.φ = u₁ ∧ u' ≫ Y'.m.φ = u₂ ∧
    u' ≫ Y'.m0.toSABMap.φ = u ≫ (twistMap Y.m0.toSABMap g).φ ≫ n.φ ∧
    u' ≫ Y'.oF.t.G.hom ≫ pullback.snd _ _ = u ≫ Y.oF.t.G.hom ≫ pullback.snd _ _

end GlobalTheory.CompanionTheory.Ar
end
end

