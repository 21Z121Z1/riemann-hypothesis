import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

abbrev LevelMod (Dw : Datum H) (l : Level H) : Type :=
  Dw.La ⧸ (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La))

abbrev LevelAut (Dw : Datum H) (l : Level H) : Type := LevelMod Dw l ≃ₗ[𝓞 E] LevelMod Dw l

def IsRigCubIso {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (ν : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull ν.φ)) : Prop :=
  w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec t'.G) (fun _ => 1)) t'.PP.rig
      (ν.cm.rigPull t.PP.L t.PP.rig) ∧
    LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (ν.cm.thetaPull t.PP.L t.cub.t)

def MovesLevel (Xo : Moduli Dw l) (g : LevelAut Dw l) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) : Prop :=
  ρ ≫ Xo.s = Xo.s ∧
    (∀ a b : Dw.La, Submodule.Quotient.mk b = g (Submodule.Quotient.mk a) →
      (Xo.univ.eta b).left ≫ ν.φ = ρ ≫ (Xo.univ.eta a).left) ∧
    ∀ a : Dw.La, (Xo.univ.etaA a).left ≫ ν.φ = ρ ≫ (Xo.univ.etaA a).left

variable {Xo : Moduli Dw l} {c : Coeff l}

def Carries {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.φ))
    {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) : Prop :=
  y'.x = y.x ≫ ρ ∧
    (∀ τ i, y'.u τ i = y.u τ i ≫ ν.φ) ∧
    ∃ pm : Gx y.x ⟶ Gx y'.x,
      pm ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = (snd (Over.mk y.x) Xo.univ.t.G).left ≫ ν.φ ∧
      pm ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = (fst (Over.mk y.x) Xo.univ.t.G).left ∧
      ∀ (i i' : Fin 1 → Xo.univ.t.PP.L.ι) (V : (Gx y.x).Opens)
        (h : V ≤ (PPx y.x).U i) (h' : V ≤ pm ⁻¹ᵁ (PPx y'.x).U i')
        (hw : V ≤ (snd (Over.mk y.x) Xo.univ.t.G).left ⁻¹ᵁ
          (LB.div (Xo.univ.t.PP.L.pull ν.φ) Xo.univ.t.PP.L).U (fun _ => i' 0, i 0)),
        (pm.appLE _ V h').hom (y'.s.f i') =
          ((snd (Over.mk y.x) Xo.univ.t.G).left.appLE _ V hw).hom (w.s (fun _ => i' 0, i 0)).val *
            resG (Gx y.x) h (y.s.f i)

def LevelMove (g : LevelAut Dw l) {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) : Prop :=
  ∃ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.φ)),
    MovesLevel Xo g ρ ν ∧ IsRigCubIso ν w ∧ Carries ν w y y'

abbrev RelFam (Xo : Moduli Dw l) (c : Coeff l) (G : Type) : Type 1 :=
  G → ∀ (S : Type) [CommRing S] [Algebra c.F S], FrPt Xo c S → FrPt Xo c S → Prop

section Laws

variable {G : Type} [Group G] (R : RelFam Xo c G)

def Total : Prop :=
  ∀ (g : G) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃ y', R g S y y'

def Functional : Prop :=
  ∀ (g : G) (S : Type) [CommRing S] [Algebra c.F S] (y y₁ y₂ : FrPt Xo c S), R g S y y₁ → R g S y y₂ → y₁ = y₂

def Unital : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), R 1 S y y

def Multiplicative' : Prop :=
  ∀ (g h : G) (S : Type) [CommRing S] [Algebra c.F S] (y y' y'' : FrPt Xo c S),
    R g S y y' → R h S y' y'' → R (g * h) S y y''

def Natural : Prop :=
  ∀ (g : G) (S S' : Type) [CommRing S] [Algebra c.F S] [CommRing S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S')
    (y y' : FrPt Xo c S) (z z' : FrPt Xo c S'), FrMap φ y z → R g S y y' → R g S' z z' → FrMap φ y' z'

def Triangular : Prop :=
  ∀ (g : G) (S : Type) [CommRing S] [Algebra c.F S] (t : Ix Dw → Sˣ) (y y' z z' : FrPt Xo c S),
    FrBor t y z → R g S y y' → R g S z z' → FrBor t y' z'

def ActionLaws : Prop :=
  Total R ∧ Functional R ∧ Unital R ∧ Multiplicative' R ∧ Natural R ∧ Triangular R

variable {R}

theorem ActionLaws.comap (h : ActionLaws R) {G' : Type} [Group G'] (f : G' →* G) :
    ActionLaws (fun g => R (f g) : RelFam Xo c G') := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun g => h1 (f g), fun g => h2 (f g), fun S _ _ y => ?_, fun g k S _ _ y y' y'' a b => ?_,
    fun g => h5 (f g), fun g => h6 (f g)⟩
  · show R (f 1) S y y
    rw [map_one]; exact h3 S y
  · show R (f (g * k)) S y y''
    rw [map_mul]; exact h4 _ _ S y y' y'' a b

theorem ActionLaws.exists_mulAction (h : ActionLaws R) (S : Type) [CommRing S] [Algebra c.F S] :
    ∃ _ : MulAction Gᵐᵒᵖ (FrPt Xo c S), ∀ (g : G) (y y' : FrPt Xo c S), R g S y y' ↔ y' = MulOpposite.op g • y := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := h
  choose a ha using fun g => h1 g S
  refine ⟨{ smul := fun g y => a g.unop y
            one_smul := fun y => h2 1 S y _ _ (ha 1 y) (h3 S y)
            mul_smul := fun g k y => h2 _ S y _ _ (ha _ y) (h4 _ _ S _ _ _ (ha k.unop y) (ha g.unop _)) },
    fun g y y' => ⟨fun r => h2 g S y _ _ r (ha g y), fun e => e ▸ ha g y⟩⟩

example : ActionLaws (fun _ _ _ _ y y' => y' = y : RelFam Xo c G) :=
  ⟨fun _ _ _ _ y => ⟨y, rfl⟩, fun _ _ _ _ _ _ _ a b => a.trans b.symm, fun _ _ _ _ => rfl,
    fun _ _ _ _ _ _ _ _ a b => b.trans a, fun _ _ _ _ _ _ _ _ _ _ _ _ m a b => by subst a b; exact m,
    fun _ _ _ _ _ _ _ _ _ m a b => by subst a b; exact m⟩

end Laws

def levelRel (Xo : Moduli Dw l) (c : Coeff l) : RelFam Xo c (LevelAut Dw l) :=
  fun g _ _ _ y y' => LevelMove g y y'

example (g : LevelAut Dw l) {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S} (h : LevelMove g y y') :
    ∃ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), MovesLevel Xo g ρ ν ∧ y'.x = y.x ≫ ρ := by
  obtain ⟨ρ, ν, w, h1, -, h2⟩ := h
  exact ⟨ρ, ν, h1, h2.1⟩

def LevelActionOver (Xo : Moduli Dw l) (c : Coeff l) : Prop := ActionLaws (levelRel Xo c)

end General

def PrincipalLevelAction : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l), l.A = 1 → LevelActionOver Xo c

variable {D : D7}

def LevelActionAt (T : Core D) (j : ℕ) : Prop :=
  LevelActionOver (T.Q.Xo j) T.Q.c ∧ ∀ c' : Coeff T.Q.l, T.Q.c.F ≤ c'.F → LevelActionOver (T.Q.Xo j) c'

def LevelActionSt (D : D7) : Prop :=
  ∀ T : Core D, T.Q.Pins → ∀ j, InR D j → LevelActionAt T j

theorem levelActionSt_of_principal (h : PrincipalLevelAction) (D : D7) : LevelActionSt D :=
  fun _ hp _ _ => ⟨h _ _ _ _ _ _ hp.2.1.2, fun _ _ => h _ _ _ _ _ _ hp.2.1.2⟩

theorem LevelActionAt.matrixGroup {T : Core D} {j : ℕ} (h : LevelActionAt T j)
    (f : G0g D.nd →* LevelAut (T.Q.Dw j) T.Q.l) :
    ActionLaws (fun g => levelRel (T.Q.Xo j) T.Q.c (f g) : RelFam (T.Q.Xo j) T.Q.c (G0g D.nd)) ∧
      ∀ c' : Coeff T.Q.l, T.Q.c.F ≤ c'.F →
        ActionLaws (fun g => levelRel (T.Q.Xo j) c' (f g) : RelFam (T.Q.Xo j) c' (G0g D.nd)) :=
  ⟨ActionLaws.comap h.1 f, fun c' hc => ActionLaws.comap (h.2 c' hc) f⟩

end GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.RayContainment
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RayContainment

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def conjI (H : Host E) (I : Ideal (𝓞 E)) : Ideal (𝓞 E) := I.map (H.bar : 𝓞 E →+* 𝓞 E)

def modulus (H : Host E) (Q : Finset (Ideal (𝓞 E))) : Ideal (𝓞 E) := ∏ P ∈ Q, P * conjI H P

def primeUnder (Q : Finset (Ideal (𝓞 E))) : ℕ := ∏ q ∈ Q.image Ideal.absNorm, q

def IsPlaceSet (H : Host E) (Q : Finset (Ideal (𝓞 E))) : Prop :=
  ∀ P ∈ Q, P.IsMaximal ∧ (Ideal.absNorm P).Prime ∧ Odd (Ideal.absNorm P) ∧
    ((Ideal.absNorm P : ℕ) : 𝓞 E) ∉ P ^ 2 ∧ conjI H P ∉ Q

def IsTwist (H : Host E) (Q : Finset (Ideal (𝓞 E))) {K : Type} [Field K] (xi : Ideal (𝓞 E) →*₀ K) : Prop :=
  (∀ 𝔞 : Ideal (𝓞 E), 𝔞 ⊔ modulus H Q ≠ ⊤ → xi 𝔞 = 0) ∧
  (∀ a : 𝓞 E, a ≠ 0 → a - 1 ∈ modulus H Q → xi (Ideal.span {a}) = 1) ∧
  ∀ 𝔟 : Ideal (𝓞 (maximalRealSubfield E)), 𝔟 ≠ ⊥ →
    𝔟.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ⊔ modulus H Q = ⊤ →
      xi (𝔟.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))) = 1

def ContainsRay (L : Type) [Field L] [NumberField L] (d m : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra K L),
    Module.finrank ℚ K = 2 ∧ (∃ x : K, x ^ 2 = -(d : K)) ∧
    ∀ 𝔄 : Ideal (𝓞 L), 𝔄 ≠ ⊥ → 𝔄 ⊔ Ideal.span {(m : 𝓞 L)} = ⊤ →
      ∃ a : 𝓞 K, a - 1 ∈ Ideal.span {(m : 𝓞 K)} ∧ Ideal.relNorm (𝓞 K) 𝔄 = Ideal.span {a}

variable {H : Host E} {Dw : Datum H} {l : Level H}

def TupleGuard (c : Coeff l) (Q : Finset (Ideal (𝓞 E))) (xi : Ideal (𝓞 E) →*₀ c.F) : Prop :=
  IsPlaceSet H Q ∧ IsTwist H Q xi ∧ Nat.Coprime (primeUnder Q) l.M ∧
    zeta (Nat.lcm (l.M * primeUnder Q) l.A) ∈ c.F ∧ ContainsRay c.F H.d (l.M * primeUnder Q)

def IsHalf (H : Host E) (N : ℕ) (I : Ideal (𝓞 E)) : Prop :=
  I = Ideal.span {a | a ∈ I ∧ a ∈ Algebra.adjoin ℤ {H.w0}} ∧
    I * conjI H I = Ideal.span {(N : 𝓞 E)} ∧ I ⊔ conjI H I = ⊤

def indexIdeal (D : Datum H) (N : Submodule (𝓞 E) D.La) : Ideal (𝓞 E) :=
  Ideal.span {a | ∃ (ω : D.La [⋀^Fin (D.p + D.q)]→ₗ[𝓞 E] 𝓞 E) (x : Fin (D.p + D.q) → D.La),
    (∀ i, x i ∈ N) ∧ a = ω x}

def DetIdeal (D D' : Datum H) (l₂ : Level H) (t : D.La →ₗ[𝓞 E] D'.La) (𝔣 𝔠 : Ideal (𝓞 E)) : Prop :=
  𝔠 ≠ ⊥ ∧ 𝔠 ⊔ 𝔣 = ⊤ ∧ ∃ (n : ℕ) (ψ : D'.La →ₗ[𝓞 E] D.La),
    0 < n ∧ Nat.Coprime n l₂.M ∧
    (∀ x y, D.EF (ψ x) (ψ y) = (n : ℤ) ^ 2 * D'.EF x y) ∧
    (∀ a ∈ Mfr l₂ • (⊤ : Submodule (𝓞 E) D.La), D.ModN l₂.M (ψ (t a) - n • a)) ∧
    indexIdeal D (LinearMap.range ψ) * conjI H 𝔠 = Ideal.span {(n : 𝓞 E) ^ (D.p + D.q)} * 𝔠

variable {Xo : Moduli Dw l} {c : Coeff l}

def embCov {n : ℕ} (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) : d.c₂.F →+* ℂ :=
  σ.comp (d.eF.symm : d.c₂.F →+* c.F)

def IsCover {n : ℕ} (d : DeltaDat Xo c n) (N : ℕ) (I : Ideal (𝓞 E)) : Prop :=
  d.pd = N ∧ d.I = I ∧ d.l₂.M = l.M * N ∧ d.l₂.Mb = l.Mb * I ∧ d.l₂.A = l.A ∧
  (∃ jK : KA l →+* KA d.l₂, (∀ x, ((jK x : KA d.l₂) : ℂ) = ((x : KA l) : ℂ)) ∧
    d.r ≫ Xo.s = d.Xo₂.s ≫ spMap jK) ∧
  d.EtaOK ∧
  (∃ rF : d.Xo₂.XF d.c₂ ⟶ Xo.XF c,
    rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ d.r ∧
    rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion d.hF.ge).toRingHom ∧
    IsFinite rF ∧ Etale rF ∧ Surjective rF) ∧
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ y : FrPt Xo c k, ∃ y₂ : FrPt d.Xo₂ d.c₂ k, FrOver d y₂ y

def IsXiDet {n : ℕ} (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (𝔣 : Ideal (𝓞 E)) (xi : Ideal (𝓞 E) →*₀ c.F) : Prop :=
  d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 ∧
  (∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H Dw.p Dw.q ty ∧
    Nonempty (FamilyUnif d.Xo₂ ((embCov d σ).comp (IntermediateField.inclusion d.c₂.le).toRingHom) ty)) ∧
  ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H Dw.p Dw.q ty →
    ∀ (U : FamilyUnif d.Xo₂ ((embCov d σ).comp (IntermediateField.inclusion d.c₂.le).toRingHom) ty) (i : Fin U.n),
      (∃ 𝔠, DetIdeal Dw (U.Di i) d.l₂ (U.t i) 𝔣 𝔠) ∧
      ∀ 𝔠, DetIdeal Dw (U.Di i) d.l₂ (U.t i) 𝔣 𝔠 →
        ∀ P, IsPeriod (U.Di i) ty P → ∀ y : FrPt d.Xo₂ d.c₂ (CAt (embCov d σ)), y.x = U.u i P →
          toC (evR d.Xo₂ d.c₂ d.cδ y) = σ (xi 𝔠)

def IsPinnedCover₂ [StarRing (𝓞 E)] {n : ℕ} (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (Q : Finset (Ideal (𝓞 E)))
    (xi : Ideal (𝓞 E) →*₀ c.F) (I : Ideal (𝓞 E)) : Prop :=
  IsCover d (primeUnder Q) I ∧ IsNab d.Xo₂ d.c₂ d.nab₂ ∧ IsXiDet d σ (modulus H Q) xi ∧ d.φδ = fun _ => 1

def CoversExist : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (n : ℕ) (Tup : Type) (Q : Tup → Finset (Ideal (𝓞 E)))
    (xi : Tup → (Ideal (𝓞 E) →*₀ c.F)),
    (∀ a : 𝓞 E, star a = H.bar a) → Odd (Dw.p + Dw.q) → GoodEmb c σ → (∀ t, TupleGuard c (Q t) (xi t)) →
      (∀ t, ∃ I, IsHalf H (primeUnder (Q t)) I) ∧
      ∀ I : Tup → Ideal (𝓞 E), (∀ t, IsHalf H (primeUnder (Q t)) (I t)) →
        ∃ dδ : Tup → DeltaDat Xo c n, ∀ t, IsPinnedCover₂ (dδ t) σ (Q t) (xi t) (I t)

open Classical in

example (H : Host E) (K : Type) [Field K] :
    IsPlaceSet H ∅ ∧ IsTwist H ∅ (1 : Ideal (𝓞 E) →*₀ K) ∧ IsHalf H (primeUnder (∅ : Finset (Ideal (𝓞 E)))) ⊤ := by
  refine ⟨fun P hP => by simp at hP, ⟨fun 𝔞 h => ?_, fun a ha _ => ?_, fun 𝔟 hb _ => ?_⟩, ?_, ?_, by simp⟩
  · simp [modulus] at h
  · apply MonoidWithZeroHom.one_apply_of_ne_zero
    simpa using ha
  · apply MonoidWithZeroHom.one_apply_of_ne_zero
    intro h
    exact hb ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  · symm
    rw [Ideal.eq_top_iff_one]
    exact Ideal.subset_span ⟨trivial, one_mem _⟩
  · simp [conjI, primeUnder, Ideal.map_top]

end GlobalTheory.IndefiniteRowSideFullHecke.RayContainment
end
end

