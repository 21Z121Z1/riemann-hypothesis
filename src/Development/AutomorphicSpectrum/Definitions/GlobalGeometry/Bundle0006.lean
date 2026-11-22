import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StdSmoothMvPolynomial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GaIsHTFormOver
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HtLatModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem htLat_le_omLat (M : LieModel G ξ E) (N : ℕ) (p : Cpt ξ) : M.htLat N p ≤ M.omLat p := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨_, T, _, Γ, i, L, _, _, M₀, j, χ, w₀, -, hj, -, hw⟩ e he
  refine Submodule.span_induction (p := fun e _ => w e ∈ regAt ξ p) ?_ ?_ ?_ ?_ he
  · rintro e ⟨v, hv, hev⟩
    obtain ⟨l, rfl⟩ := M₀.onto v hv
    have : e = j l := M.inj (Over.OverMorphism.ext (hev.trans (hj l).symm))
    rw [this, hw]
    exact ⟨_, rfl⟩
  · simp
  · intro a b _ _ ha hb
    simpa using add_mem ha hb
  · intro c a _ ha
    have : w (c • a) = (c : Ω) * w a := by
      rw [Subring.smul_def, map_smul, smul_eq_mul]
    rw [this]
    exact mul_mem c.2 ha

def triv (R : Type) [CommRing R] [IsDomain R] : BT.QFGroup R Unit where
  G := 𝟙_ _
  flat := inferInstanceAs (Flat (𝟙 _))
  quasiFinite := inferInstanceAs (LocallyQuasiFinite (𝟙 _))
  separated := inferInstanceAs (IsSeparated (𝟙 _))
  quasiCompact := inferInstanceAs (QuasiCompact (𝟙 _))
  finPres := inferInstanceAs (LocallyOfFinitePresentation (𝟙 _))
  pt := 1
  pt_inj _ _ _ _ _ := rfl
  pt_onto g hg := by
    refine ⟨(), IsLocalRing.closedPoint (FractionRing R), ?_⟩
    have h : ((1 : Unit →* (BT.genPt R ⟶ 𝟙_ (Over (Spec (CommRingCat.of R))))) ()).left = (BT.genPt R).hom := by
      have := Over.w ((1 : Unit →* (BT.genPt R ⟶ 𝟙_ (Over (Spec (CommRingCat.of R))))) ())
      simpa using this
    rw [h]
    apply PrimeSpectrum.ext
    refine Eq.trans ?_ (show g.asIdeal = ⊥ from hg).symm
    change Ideal.comap (algebraMap R (FractionRing R)) (IsLocalRing.maximalIdeal (FractionRing R)) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)]
  gen_reduced := by
    have : IsIso (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := inferInstanceAs (IsIso (𝟙 _))
    have : IsReduced (BT.genPt R).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (FractionRing R))))
    exact isReduced_of_isOpenImmersion (pullback.snd _ (BT.genPt R).hom)

theorem triv_torsion {R : Type} [CommRing R] [IsDomain R] (x : Spec (CommRingCat.of R) ⟶ X) (N : ℕ)
    (h : ∀ (Y : Over (Spec (CommRingCat.of R))) (g : Over.mk (Y.hom ≫ x) ⟶ G), g ^ N = 1 → g = 1) :
    (triv R).IsTorsionAlong G x N (1 : Over.mk x ⟶ G).left := by
  have key : ∀ (Y : Over (Spec (CommRingCat.of R))) (y : Y ⟶ (triv R).G),
      y.left ≫ (1 : Over.mk x ⟶ G).left = (1 : Over.mk (Y.hom ≫ x) ⟶ G).left := by
    intro Y y
    have hy : y.left = Y.hom := (Category.comp_id _).symm.trans (Over.w y)
    have := MonObj.comp_one (M := G) (Over.homMk Y.hom rfl : Over.mk (Y.hom ≫ x) ⟶ Over.mk x)
    rw [hy]
    exact congrArg (fun q => q.left) this
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Over.w (1 : Over.mk x ⟶ G)).trans (Category.id_comp _).symm
  · intro Y y z y₀ z₀ hy hz
    rw [key] at hy hz ⊢
    rw [Over.OverMorphism.ext hy, Over.OverMorphism.ext hz, _root_.mul_one]
  · intro Y y z _
    exact toUnit_unique _ _
  · intro Y g
    constructor
    · intro hg
      exact ⟨toUnit _, by rw [key, h Y g hg]⟩
    · rintro ⟨y, hy⟩
      rw [key] at hy
      rw [← Over.OverMorphism.ext hy, one_pow]

theorem ga_torsion {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ X) (N : ℕ) (hN : IsUnit (N : R))
    (Y : Over (Spec (CommRingCat.of R))) (g : Over.mk (Y.hom ≫ x) ⟶ LieInh.gaObj X) (hg : g ^ N = 1) : g = 1 := by
  let φ : (Over.mk (Y.hom ≫ x) ⟶ LieInh.gaObj X) →* Multiplicative Γ(Y.left, ⊤) :=
    ⟨⟨LieInh.gaEquiv _, LieInh.gaEquiv_one⟩, LieInh.gaEquiv_mul⟩
  apply (LieInh.gaEquiv _).injective
  change φ g = φ 1
  have h1 : φ g ^ N = 1 := by rw [← map_pow, hg, map_one]
  have h2 : (N : Γ(Y.left, ⊤)) * (φ g).toAdd = 0 := by
    have := congrArg Multiplicative.toAdd h1
    simpa [nsmul_eq_mul] using this
  have h3 : IsUnit (N : Γ(Y.left, ⊤)) := by
    have := hN.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ Y.hom.appTop).hom
    simpa using this
  rw [map_one]
  exact h3.mul_right_eq_zero.1 h2

theorem ga_isHTFormOver {R : Type} [CommRing R] [IsDomain R] (x : Spec (CommRingCat.of R) ⟶ X) (k : R →+* Ω)
    (hk : Spec.map (CommRingCat.ofHom k) ≫ x = ξ) (N : ℕ) (hN : IsUnit (N : R)) :
    (LieInh.gaLie ξ).IsHTFormOver N x k LinearMap.id := by
  have hs : Subsingleton (R ⧸ Ideal.span {(N : R)}) :=
    Ideal.Quotient.subsingleton_iff.2 (Ideal.span_singleton_eq_top.2 hN)
  have hs' : Subsingleton (DualNumber (R ⧸ Ideal.span {(N : R)})) :=
    ⟨fun a b => TrivSqZeroExt.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
  have he : IsEmpty (Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)})))) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum _))
  refine ⟨inferInstance, Unit, inferInstance, triv R, _, R, inferInstance, inferInstance, LieInh.gaLie x, k, 1,
    LinearMap.id, triv_torsion x N (ga_torsion x N hN), fun e => ?_, ⟨1, fun t => ?_, fun e => ?_⟩, fun _ => rfl⟩
  · symm
    refine (LieInh.map_gaPt (dualMap k) _ (Spec.map (CommRingCat.ofHom (algebraMap Ω (DualNumber Ω))) ≫ ξ) ?_ _).trans ?_
    · rw [← hk, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
      congr 2
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    · have : dualMap k (TrivSqZeroExt.inr e) = TrivSqZeroExt.inr (k e) := by ext <;> simp [dualMap]
      rw [this]
      rfl
  · simp [BT.valAt]
  · exact ⟨isInitialOfIsEmpty.to _, isInitialOfIsEmpty.hom_ext _ _, isInitialOfIsEmpty.hom_ext _ _,
      Subsingleton.elim _ _⟩

theorem ga_id_mem_htLat (p : Cpt ξ) [IsDomain (X.presheaf.stalk p.1)] (N : ℕ)
    (hN : IsUnit (N : X.presheaf.stalk p.1)) :
    (LinearMap.id : Module.Dual Ω Ω) ∈ (LieInh.gaLie ξ).htLat N p := by
  refine Submodule.subset_span (ga_isHTFormOver (R := X.presheaf.stalk p.1) _ _ ?_ N hN)
  change Spec.map (X.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo ξ) ≫ _ = _
  rw [Spec.map_comp_assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ

theorem ga_htLat_ne_bot [IsIntegral X] (p : Cpt ξ) (N : ℕ) (hN : IsUnit (N : X.presheaf.stalk p.1)) :
    (LieInh.gaLie ξ).htLat N p ≠ ⊥ := fun h => by
  have := ga_id_mem_htLat p N hN
  rw [h, Submodule.mem_bot] at this
  exact one_ne_zero (LinearMap.congr_fun this (1 : Ω))

theorem isHT_add_nsmul {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : BT.QFGroup R T)
    {x : Spec (CommRingCat.of R) ⟶ X} (i : Γ.G.left ⟶ G.left) {L : Type} [AddCommGroup L] [Module R L]
    (M : LieModel G x L) (N : ℕ) (χ : T →* Rˣ) (w w' : Module.Dual R L) (h : Γ.IsHT i M N χ w) :
    Γ.IsHT i M N χ (w + (N : R) • w') := by
  obtain ⟨s, hs, h⟩ := h
  refine ⟨s, hs, fun e => ?_⟩
  obtain ⟨v, h1, h2, h3⟩ := h e
  refine ⟨v, h1, h2, h3.trans ?_⟩
  congr 2
  rw [Ideal.Quotient.eq]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, sub_add_cancel_left, neg_mem_iff]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

end GlobalTheory.CompanionTheory.Ar.HtLatModel
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFullLevelAt
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.XR

open AlgebraicGeometry CategoryTheory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {Ω : Type} [Field Ω]

abbrev TateIsoAt (D : Datum H) (t : SAB H X) {k : Type} [Field k] (x : Sp k ⟶ X) : Type :=
  TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))

def IsFullLevelAt (D : Datum H) (t : SAB H X) (ξ : Sp Ω ⟶ X) (N : ℕ) (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)) :
    Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k), ∃ I : TateIsoAt D t (spMap i ≫ ξ),
    (I.ζ N : k) = i z ∧ ∀ a, (I.ev N a).left = spMap i ≫ (ev a).left

end GlobalTheory.CompanionTheory.Ar.XR
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

def secVal {B : Type} [CommRing B] {Z : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Z) (W : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (f : Γ(Z, W)) : B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((x.appLE W ⊤ h).hom f)

def FullTorsion (G : Over X) [GrpObj G] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (n : ℕ) : Prop :=
  ∀ (k : Type) [Field k] (i : Ω →+* k) (g : Over.mk (spMap i ≫ ξ) ⟶ G), g ^ n = 1 →
    ∃ x : Over.mk ξ ⟶ G, g.left = spMap i ≫ x.left

namespace LieModel

def IsHTAt (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) (x : Over.mk ξ ⟶ G) (q : Cpt ξ)
    (w : Module.Dual Ω E) : Prop :=
  w ∈ M.omLat q ∧ ∃ (W : G.left.Opens) (f : Γ(G.left, W)), (η[G]).left q.1 ∈ W ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (xk g : Over.mk (spMap i ≫ ξ) ⟶ G) (c : kˣ)
      (h : ⊤ ≤ g.left ⁻¹ᵁ W), xk.left = spMap i ≫ x.left → g ^ n = 1 →
        Out.WeilIs G L n xk g (unitOn c) → secVal (B := k) g.left W h f = c) ∧
    ∀ e v, M.Extends q e v → ∀ h : ⊤ ≤ v.left ⁻¹ᵁ W, ∃ r ∈ regAt ξ q,
      w e = genMap ξ q (secVal (B := DualNumber (X.presheaf.stalk q.1)) v.left W h f).snd + n * r

def htOm (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) : Lat ξ (Module.Dual Ω E) := fun q =>
  Submodule.span (regAt ξ q) {w | ∃ x : Over.mk ξ ⟶ G, x ^ n = 1 ∧ M.IsHTAt L n x q w}

def htOmEig (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
    (σ : O →+* Ω) : Lat ξ (Module.Dual Ω (eigSp ρ σ)) :=
  (M.htOm L n).map (eigSp ρ σ).subtype.dualMap

def htDual (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
    (σ : O →+* Ω) : Lat ξ E := fun q =>
  Submodule.span (regAt ξ q) {e | e ∈ eigSp ρ σ ∧ ∀ w ∈ M.htOm L n q, w e ∈ regAt ξ q}

def htW (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
    (σ : O →+* Ω) (𝔡 : Ideal O) : Lat ξ E := fun q =>
  Submodule.span (regAt ξ q) {e | e ∈ eigSp ρ σ ∧ ∀ d ∈ 𝔡, σ d • e ∈ M.htDual L n ρ σ q}

variable (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
  (σ : O →+* Ω)

theorem htOm_le (q : Cpt ξ) : M.htOm L n q ≤ M.omLat q :=
  Submodule.span_le.2 fun _ ⟨_, _, h⟩ => h.1

theorem mem_htDual_iff (q : Cpt ξ) (e : E) :
    e ∈ M.htDual L n ρ σ q ↔ e ∈ eigSp ρ σ ∧ ∀ w ∈ M.htOm L n q, w e ∈ regAt ξ q := by
  constructor
  · intro he
    induction he using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨(eigSp ρ σ).zero_mem, fun w _ => by simpa using (regAt ξ q).zero_mem⟩
    | add x y _ _ hx hy =>
      exact ⟨(eigSp ρ σ).add_mem hx.1 hy.1, fun w hw => by
        simpa using (regAt ξ q).add_mem (hx.2 w hw) (hy.2 w hw)⟩
    | smul c x _ hx =>
      refine ⟨(eigSp ρ σ).smul_mem (c : Ω) hx.1, fun w hw => ?_⟩
      have : w (c • x) = (c : Ω) * w x := by
        show w ((c : Ω) • x) = _
        rw [map_smul, smul_eq_mul]
      rw [this]
      exact (regAt ξ q).mul_mem c.2 (hx.2 w hw)
  · exact fun h => Submodule.subset_span h

theorem mem_eigSp_of_mem_htDual {q : Cpt ξ} {e : E} (he : e ∈ M.htDual L n ρ σ q) : e ∈ eigSp ρ σ :=
  ((M.mem_htDual_iff L n ρ σ q e).1 he).1

theorem mem_htDual (q : Cpt ξ) (e : eigSp ρ σ) :
    (e : E) ∈ M.htDual L n ρ σ q ↔ ∀ u ∈ M.htOmEig L n ρ σ q, u e ∈ regAt ξ q := by
  rw [mem_htDual_iff]
  constructor
  · rintro ⟨-, h⟩ u hu
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hu
    exact h w hw
  · intro h
    refine ⟨e.2, fun w hw => ?_⟩
    exact h _ (Submodule.mem_map.2 ⟨w, hw, rfl⟩)

theorem eigLat_le_htDual (q : Cpt ξ) : M.eigLat ρ σ q ≤ M.htDual L n ρ σ q :=
  fun e he => Submodule.subset_span ⟨he.2, fun w hw => (M.htOm_le L n q hw) e he.1⟩

theorem mem_eigSp_of_mem_htW (𝔡 : Ideal O) {q : Cpt ξ} {e : E} (he : e ∈ M.htW L n ρ σ 𝔡 q) :
    e ∈ eigSp ρ σ := by
  induction he using Submodule.span_induction with
  | mem x hx => exact hx.1
  | zero => exact (eigSp ρ σ).zero_mem
  | add x y _ _ hx hy => exact (eigSp ρ σ).add_mem hx hy
  | smul c x _ hx => exact (eigSp ρ σ).smul_mem (c : Ω) hx

example (q : Cpt ξ) : (0 : Module.Dual Ω (eigSp ρ σ)) ∈ M.htOmEig L n ρ σ q := Submodule.zero_mem _

end LieModel

open Classical in

def Lat.patch (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) : Lat ξ E := fun q =>
  if ∃ p ∈ S, InFibre ξ p q then ⨅ p ∈ S, ⨅ _ : InFibre ξ p q, Lp p q else L₀ q

theorem Lat.patch_empty (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) : Lat.patch ∅ L₀ Lp = L₀ := by
  funext q; simp [Lat.patch]

theorem Lat.patch_of_not (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) {q : Cpt ξ}
    (hq : ∀ p ∈ S, ¬ InFibre ξ p q) : Lat.patch S L₀ Lp q = L₀ q := by
  simp only [Lat.patch]; rw [if_neg]; rintro ⟨p, hp, h⟩; exact hq p hp h

theorem Lat.patch_of_unique (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) {q : Cpt ξ} {p : ℕ} (hp : p ∈ S)
    (hq : InFibre ξ p q) (hu : ∀ p' ∈ S, InFibre ξ p' q → p' = p) : Lat.patch S L₀ Lp q = Lp p q := by
  simp only [Lat.patch]; rw [if_pos ⟨p, hp, hq⟩]
  refine le_antisymm (iInf₂_le_of_le p hp (iInf_le _ hq)) (le_iInf₂ fun p' hp' => le_iInf fun h => ?_)
  rw [hu p' hp' h]

end GlobalTheory.CompanionTheory.Ar
end
end

