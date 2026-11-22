import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLieLieModel
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorusModel

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem charVal_eq {A : Type} [CommRing A] {a : Sp A ⟶ S} (t : Over.mk a ⟶ splitTorus S X) (χ : X) :
    charVal t χ = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      (GlobalTheory.splitTorusPointsEquiv S X (Over.mk a) t (Multiplicative.ofAdd χ)).val := by
  unfold charVal
  set g : Sp A ⟶ Spec (torusRing ZU X) := t.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S) with hg
  have h : (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      = Spec.preimage g := by
    conv_lhs => rw [← Spec.map_preimage g]
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rw [← h]
  rfl

theorem charVal_mul {A : Type} [CommRing A] {a : Sp A ⟶ S} (t t' : Over.mk a ⟶ splitTorus S X) (χ : X) :
    charVal (t * t') χ = charVal t χ * charVal t' χ := by
  simp only [charVal_eq, map_mul, MonoidHom.mul_apply, Units.val_mul]

theorem charVal_one {A : Type} [CommRing A] {a : Sp A ⟶ S} (χ : X) :
    charVal (1 : Over.mk a ⟶ splitTorus S X) χ = 1 := by
  simp only [charVal_eq, map_one, MonoidHom.one_apply, Units.val_one]

theorem charVal_add {A : Type} [CommRing A] {a : Sp A ⟶ S} (t : Over.mk a ⟶ splitTorus S X) (χ χ' : X) :
    charVal t (χ + χ') = charVal t χ * charVal t χ' := by
  simp only [charVal_eq, ofAdd_add, map_mul, Units.val_mul]

theorem charVal_zero {A : Type} [CommRing A] {a : Sp A ⟶ S} (t : Over.mk a ⟶ splitTorus S X) :
    charVal t 0 = 1 := by
  simp only [charVal_eq, ofAdd_zero, map_one, Units.val_one]

theorem charVal_ext {A : Type} [CommRing A] {a : Sp A ⟶ S} {t t' : Over.mk a ⟶ splitTorus S X}
    (h : ∀ χ, charVal t χ = charVal t' χ) : t = t' := by
  apply (GlobalTheory.splitTorusPointsEquiv S X (Over.mk a)).injective
  ext χ
  have := h χ
  rw [charVal_eq, charVal_eq] at this
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective this

theorem exists_charVal {A : Type} [CommRing A] (a : Sp A ⟶ S) (u : Multiplicative X →* Aˣ) :
    ∃ t : Over.mk a ⟶ splitTorus S X, ∀ χ, charVal t χ = (u (Multiplicative.ofAdd χ)).val := by
  refine ⟨(GlobalTheory.splitTorusPointsEquiv S X (Over.mk a)).symm
    ((Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom).comp u), fun χ => ?_⟩
  rw [charVal_eq, MulEquiv.apply_symm_apply]
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply _

theorem charVal_comp {A B : Type} [CommRing A] [CommRing B] {a : Sp A ⟶ S} {b : Sp B ⟶ S} (g : A →+* B)
    (t : Over.mk a ⟶ splitTorus S X) (t' : Over.mk b ⟶ splitTorus S X)
    (h : t'.left = spMap g ≫ t.left) (χ : X) : charVal t' χ = g (charVal t χ) := by
  unfold charVal
  have e : (t'.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S) : Sp B ⟶ Spec (torusRing ZU X)) =
      Spec.map (CommRingCat.ofHom g) ≫
        (t.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S) : Sp A ⟶ Spec (torusRing ZU X)) := by
    rw [h]; exact Category.assoc _ _ _
  rw [e, Spec.preimage_comp, Spec.preimage_map]
  rfl

theorem left_eq_of_charVal {A B : Type} [CommRing A] [CommRing B] {a : Sp A ⟶ S} {b : Sp B ⟶ S} (g : A →+* B)
    (hg : spMap g ≫ a = b) (t : Over.mk a ⟶ splitTorus S X) (t' : Over.mk b ⟶ splitTorus S X)
    (h : ∀ χ, charVal t' χ = g (charVal t χ)) : t'.left = spMap g ≫ t.left := by
  let k : Over.mk b ⟶ Over.mk a := Over.homMk (spMap g) hg
  have : t' = k ≫ t := charVal_ext fun χ => by rw [h, charVal_comp g t (k ≫ t) rfl]
  rw [this]; rfl

def epsUnit {R : Type} [CommRing R] (δ : X →+ R) : Multiplicative X →* (DualNumber R)ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun χ => TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (δ χ.toAdd)
      map_one' := by ext <;> simp
      map_mul' := fun a b => by ext <;> simp [add_comm] }

def tanPt {R : Type} [CommRing R] (x : Sp R ⟶ S) (δ : X →+ R) : epsAt x ⟶ splitTorus S X :=
  (exists_charVal _ (epsUnit δ)).choose

theorem charVal_tanPt {R : Type} [CommRing R] (x : Sp R ⟶ S) (δ : X →+ R) (χ : X) :
    charVal (tanPt x δ) χ = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (δ χ) :=
  (exists_charVal _ (epsUnit δ)).choose_spec χ

theorem spMap_comp_eps {R A : Type} [CommRing R] [CommRing A] (x : Sp R ⟶ S) (g : DualNumber R →+* A)
    (f : R →+* A) (h : g.comp (algebraMap R (DualNumber R)) = f) :
    spMap g ≫ (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x) = spMap f ≫ x := by
  rw [← Category.assoc, ← Spec.map_comp, ← h]; rfl

theorem fst_eps {R : Type} [CommRing R] (x : Sp R ⟶ S) :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x) = x := by
  rw [spMap_comp_eps x _ (RingHom.id R) (by ext; simp)]
  simp [spMap]

def lieModel {R : Type} [CommRing R] (x : Sp R ⟶ S) : LieModel (splitTorus S X) x (X →+ R) where
  pt := tanPt x
  tan δ := (left_eq_of_charVal _ (fst_eps x) (tanPt x δ) 1 fun χ => by
    rw [charVal_one, charVal_tanPt]; simp).symm
  inj δ δ' h := by
    ext χ
    have := congrArg (fun t => (charVal t χ).snd) h
    simpa [charVal_tanPt] using this
  onto v hv := by
    have h1 : ∀ χ, (charVal v χ).fst = 1 := fun χ => by
      have := charVal_comp (TrivSqZeroExt.fstHom R R R).toRingHom v (1 : Over.mk x ⟶ splitTorus S X)
        (Eq.symm hv) χ
      rw [charVal_one] at this
      exact this.symm
    refine ⟨AddMonoidHom.mk' (fun χ => (charVal v χ).snd) fun a b => ?_, charVal_ext fun χ => ?_⟩
    · simp [charVal_add, TrivSqZeroExt.snd_mul, h1, add_comm]
    · rw [charVal_tanPt]; ext <;> simp [h1]
  add δ δ' := charVal_ext fun χ => by
    rw [charVal_mul, charVal_tanPt, charVal_tanPt, charVal_tanPt]
    ext <;> simp [add_comm]
  smul c δ := left_eq_of_charVal (epsMul c)
    (spMap_comp_eps x _ _ (by ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])) _ _ fun χ => by
      rw [charVal_tanPt, charVal_tanPt]
      ext <;> simp [epsMul, mul_comm]

theorem isCocharLie_lieModel {R : Type} [CommRing R] (x : Sp R ⟶ S) :
    IsCocharLie (lieModel (X := X) x) := charVal_tanPt x

theorem IsCocharLie.pt_eq {R : Type} [CommRing R] {x : Sp R ⟶ S} {M M' : LieModel (splitTorus S X) x (X →+ R)}
    (h : IsCocharLie M) (h' : IsCocharLie M') : M.pt = M'.pt :=
  funext fun δ => charVal_ext fun χ => (h δ χ).trans (h' δ χ).symm

theorem lifts_iff {R R' : Type} [CommRing R] [CommRing R'] (x : Sp R ⟶ S) (c : R →+* R') (δ : X →+ R)
    (δ' : X →+ R') :
    (lieModel x).Lifts c (𝟙 (splitTorus S X).left) δ (tanPt (spMap c ≫ x) δ') ↔ ∀ χ, δ' χ = c (δ χ) := by
  unfold LieModel.Lifts
  rw [Category.comp_id]
  constructor
  · intro h χ
    have := congrArg TrivSqZeroExt.snd (charVal_comp (dualMap c) (tanPt x δ) _ h χ)
    simpa [charVal_tanPt, dualMap] using this
  · intro h
    refine left_eq_of_charVal (dualMap c) ?_ (tanPt x δ) _ fun χ => ?_
    · rw [spMap_comp_eps x _ ((algebraMap R' (DualNumber R')).comp c)
        (by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]), ← Category.assoc, ← Spec.map_comp]
      rfl
    · rw [charVal_tanPt, charVal_tanPt]
      ext <;> simp [dualMap, h]

theorem killsOver_id_iff (Y : AddSubgroup X) {B : Type} [CommRing B] [Nontrivial B] (b : Sp B ⟶ S) :
    KillsOver (𝟙 (splitTorus S X)) Y b ↔ Y = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro χ _
    obtain ⟨t, ht⟩ := exists_charVal (X := X) (spMap (algebraMap B (AddMonoidAlgebra B (X ⧸ Y))) ≫ b)
      (MonoidHom.toHomUnits ((AddMonoidAlgebra.of B (X ⧸ Y)).comp
        (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Y))))
    have ht' : ∀ χ, charVal t χ = AddMonoidAlgebra.single (QuotientAddGroup.mk χ : X ⧸ Y) 1 := ht
    have h1 := h _ _ t fun y hy => by
      rw [ht', (QuotientAddGroup.eq_zero_iff y).2 hy]; rfl
    rw [Category.comp_id] at h1
    have h2 := ht' χ
    rw [h1, charVal_one, AddMonoidAlgebra.one_def] at h2
    exact (QuotientAddGroup.eq_zero_iff χ).1 (AddMonoidAlgebra.single_left_injective one_ne_zero h2).symm
  · rintro rfl A _ g t ht
    rw [Category.comp_id]
    exact charVal_ext fun χ => (ht χ trivial).trans (charVal_one χ).symm

theorem killsOver_sq {B : Type} [CommRing B] (b : Sp B ⟶ S) :
    KillsOver (𝟙 (splitTorus S X) * 𝟙 (splitTorus S X)) (nsmulAddMonoidHom (α := X) 2).range b := by
  intro A _ g t ht
  rw [MonObj.comp_mul, Category.comp_id]
  refine charVal_ext fun χ => ?_
  rw [charVal_mul, ← charVal_add, charVal_one]
  exact ht _ ⟨χ, two_nsmul χ⟩

theorem not_killsOver_mu_two (b : Sp (ZMod 2) ⟶ S) :
    ¬ KillsOver (𝟙 (splitTorus S ℤ)) (nsmulAddMonoidHom (α := ℤ) 2).range b := by
  rw [killsOver_id_iff]
  intro h
  obtain ⟨n, hn⟩ : (1 : ℤ) ∈ (nsmulAddMonoidHom (α := ℤ) 2).range := h ▸ trivial
  have : 2 * n = 1 := by simpa using hn
  omega

end GlobalTheory.CompanionTheory.Ar.TorusModel
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

structure IsEmbedded {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : Ideal (MRing ι))
    (U : X → Set X) (lam : X → X → (Σ k, ι k) → ℂ) : Prop where
  isOpen : ∀ x, IsOpen (U x)
  mem_U : ∀ x, x ∈ U x
  holo : ∀ x p, A.HoloOn (U x) fun y => lam x y p
  mem : ∀ x, ∀ y ∈ U x, lam x y ∈ mcPts P
  compat : ∀ x x', ∀ y ∈ U x ∩ U x', SameOrbit (lam x y) (lam x' y)
  surj : ∀ z ∈ mcPts P, ∃ x, SameOrbit (lam x x) z
  inj : ∀ x x', SameOrbit (lam x x) (lam x' x') → x = x'
  immersion : ∀ x, ∀ p : (k : K) → ι k, (∀ k, lam x x ⟨k, p k⟩ ≠ 0) → ∀ j, x ∈ (A.chart j).source →
    (fderiv ℂ (fun y => affCoord p (lam x ((A.chart j).symm y))) (A.chart j x)).ker = ⊥

def secOf {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (β : MRing ι) : R.X → R.X → ℂ :=
  fun x y => evC (R.lift x y) β

def IsSncModel {Ω : Type} [Field Ω] [Algebra ℚ Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)) : Prop :=
  ∀ c : (k : K) → ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (m : ℕ) (f a : Fin m → Ω),
    (∀ l, f l ∈ Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) ∧
    (∀ l, a l ∈ Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) ∧
    ∑ l, a l * f l = 1 ∧ ∀ l, f l ≠ 0 → ∀ S : Subalgebra ℚ Ω,
      S = Algebra.adjoin ℚ (insert (f l)⁻¹ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) →
      Algebra.Smooth ℚ S ∧ ∃ (z : Fin e → S) (n : ℕ), n ≤ e ∧
        LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) ∧
        Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ ∧
        ∀ q : Ideal S, q.IsPrime →
          ((∀ g ∈ J, ∀ s : S, (s : Ω) = aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g → s ∈ q) ↔
            ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)

def AlgOver {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) : Prop :=
  ∃ (K₀ : Type) (_ : Fintype K₀) (ι₀ : K₀ → Type) (_ : ∀ k, Fintype (ι₀ k)) (κ : K₀ → K)
    (v : (Σ k, ι₀ k) → Σ k, ι k) (U : S.X → Set S.X) (lam : S.X → S.X → (Σ k, ι₀ k) → ℂ) (β : MRing ι₀) (b : K₀ → ℕ),
    IsBlockMap κ v ∧ IsEmbedded S.A (imageZ v P) U lam ∧
    (∀ x, SameOrbit (lam (Re.π x) (Re.π x)) fun p => Re.R.lift x x (v p)) ∧
    IsMultiHomog β b ∧ β ∉ imageZ v P ∧ ∀ x ∈ bdry S.s, evC (lam x x) β = 0

section Same

variable {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]

def SameSing {D : ℕ} {σ₁ σ₂ : Type} {S₁ : AnSys D σ₁} {S₂ : AnSys D σ₂} {P₁ : Ideal (MRing ι₁)}
    {P₂ : Ideal (MRing ι₂)} (Re₁ : Realis S₁ P₁) (Re₂ : Realis S₂ P₂) (P : Ideal (MRing ι)) (κ₁ : K₁ → K)
    (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k) (β : MRing ι) (a₁ : σ₁) (a₂ : σ₂) :
    Prop :=
  ∃ f g : MRing ι, IsLineIso P (pullDeg κ₁ (Re₁.ref a₁).a) (pullDeg κ₂ (Re₂.ref a₂).a) f g ∧
    ∀ z ∈ mcPts P, evC z β ≠ 0 → ∀ (x₁ : Re₁.R.X) (x₂ : Re₂.R.X),
      SameOrbit (Re₁.R.lift x₁ x₁) (fun p => z (v₁ p)) → SameOrbit (Re₂.R.lift x₂ x₂) (fun p => z (v₂ p)) →
      Re₁.π x₁ ∉ bdry S₁.s → Re₂.π x₂ ∉ bdry S₂.s →
      ∀ u v : MRing ι, u * f - v * g ∈ P → evC z u ≠ 0 →
        Real.log (‖evC z v‖ / ‖evC z u‖ * (Re₂.ref a₂).h (fun p => z (v₂ p)) / (Re₁.ref a₁).h fun p => z (v₁ p)) =
          S₁.ph a₁ (Re₁.π x₁) - S₂.ph a₂ (Re₂.π x₂)

end Same

end GlobalTheory.CompanionTheory.Ar.Cmp
end
end

