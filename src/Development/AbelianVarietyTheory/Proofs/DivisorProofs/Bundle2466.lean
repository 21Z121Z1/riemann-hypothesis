import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2378
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerIsoDiagonalOfLPowerTorsionAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowerDiagonal

section General

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]

theorem isMonHom_of_points {X Y : C} [MonObj X] [MonObj Y] (f : X ⟶ Y)
    (h1 : ∀ T : C, (1 : T ⟶ X) ≫ f = 1)
    (hm : ∀ (T : C) (x y : T ⟶ X), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f where
  one_hom := by
    rw [MonObj.one_eq_one X, MonObj.one_eq_one Y]
    exact h1 _
  mul_hom := by
    rw [MonObj.mul_eq_mul X, MonObj.mul_eq_mul Y, hm, MonObj.comp_mul]
    simp

theorem exists_sections {G H : C} [MonObj G] [MonObj H] {n : Type} [DecidableEq n]
    (p : n → (G ⟶ H)) (hp : ∀ a, IsMonHom (p a))
    (hu : ∀ (T : C) (y : n → (T ⟶ H)), ∃! x : T ⟶ G, ∀ a, x ≫ p a = y a) :
    ∃ j : n → (H ⟶ G), (∀ b, IsMonHom (j b)) ∧ (∀ b, j b ≫ p b = 𝟙 H) ∧
      ∀ b c, c ≠ b → j b ≫ p c = 1 := by
  classical
  have hex := fun b => (hu H (fun c => if c = b then 𝟙 H else 1)).exists
  choose j hj using hex
  have key : ∀ {T : C} (x : T ⟶ H) (b c : n), x ≫ j b ≫ p c = if c = b then x else 1 := by
    intro T x b c
    rw [hj b c]
    split_ifs <;> simp
  have ext : ∀ {T : C} (x y : T ⟶ G), (∀ a, x ≫ p a = y ≫ p a) → x = y := fun {T} x y h =>
    (hu T fun a => y ≫ p a).unique h (fun _ => rfl)
  refine ⟨j, fun b => ?_, fun b => by simpa using key (𝟙 H) b b,
    fun b c hcb => by simpa [hcb] using key (𝟙 H) b c⟩
  apply isMonHom_of_points
  · intro T
    apply ext
    intro a
    haveI := hp a
    rw [Category.assoc, key, MonObj.one_comp]
    split_ifs <;> rfl
  · intro T x y
    apply ext
    intro a
    haveI := hp a
    simp only [Category.assoc, key, MonObj.mul_comp]
    split_ifs <;> simp

theorem hom_ext_sections {G H H' : C} [MonObj G] [MonObj H] [MonObj H']
    {n : Type} [Finite n] [DecidableEq n]
    (p : n → (G ⟶ H)) (hp : ∀ a, IsMonHom (p a))
    (hu : ∀ (T : C) (y : n → (T ⟶ H)), ∃! x : T ⟶ G, ∀ a, x ≫ p a = y a)
    (j : n → (H ⟶ G)) (h1 : ∀ b, j b ≫ p b = 𝟙 H) (h2 : ∀ b c, c ≠ b → j b ≫ p c = 1)
    (f g : G ⟶ H') [IsMonHom f] [IsMonHom g] (h : ∀ b, j b ≫ f = j b ≫ g) : f = g := by
  classical
  haveI := Fintype.ofFinite n
  have ext : ∀ {T : C} (x y : T ⟶ G), (∀ a, x ≫ p a = y ≫ p a) → x = y := fun {T} x y h =>
    (hu T fun a => y ≫ p a).unique h (fun _ => rfl)
  have hcomp : ∀ {K : C} [MonObj K] (k : G ⟶ K) [IsMonHom k] (l : List n),
      (l.map fun b => p b ≫ j b).prod ≫ k = (l.map fun b => p b ≫ j b ≫ k).prod := by
    intro K _ k _ l
    induction l with
    | nil => simp
    | cons b l ih => simp [MonObj.mul_comp, ih]
  have hlist : ∀ (c : n) (l : List n), l.Nodup →
      (l.map fun b => p b ≫ j b ≫ p c).prod = if c ∈ l then p c else 1 := by
    intro c l hl
    induction l with
    | nil => simp
    | cons b l ih =>
      rw [List.map_cons, List.prod_cons, ih (List.nodup_cons.mp hl).2]
      by_cases hbc : b = c
      · subst hbc
        have hnot : b ∉ l := (List.nodup_cons.mp hl).1
        simp [h1, hnot]
      · simp [h2 b c (Ne.symm hbc), Ne.symm hbc]
  have hs : (Finset.univ.toList.map fun b => p b ≫ j b).prod = 𝟙 G := by
    apply ext
    intro c
    haveI := hp c
    rw [hcomp (p c), hlist c _ (Finset.nodup_toList _)]
    simp
  calc f = (Finset.univ.toList.map fun b => p b ≫ j b).prod ≫ f := by rw [hs, Category.id_comp]
    _ = (Finset.univ.toList.map fun b => p b ≫ j b ≫ f).prod := hcomp f _
    _ = (Finset.univ.toList.map fun b => p b ≫ j b ≫ g).prod := by simp only [h]
    _ = (Finset.univ.toList.map fun b => p b ≫ j b).prod ≫ g := (hcomp g _).symm
    _ = g := by rw [hs, Category.id_comp]

end General

theorem exists_diagonal : ∀ (K : Type) [Field K] [IsAlgClosed K] (G₀ G₁ H₀ H₁ : Over (Sp K)) [GrpObj G₀] [GrpObj G₁] [GrpObj H₀] [GrpObj H₁] [IsCommMonObj H₀] [IsCommMonObj H₁], IsSemiAbelian H₀ → IsSemiAbelian H₁ → ∀ (l : ℕ), l.Prime → (l : K) ≠ 0 → ∀ (p₀ : Fin 8 → (G₀ ⟶ H₀)) (p₁ : Fin 8 → (G₁ ⟶ H₁)), (∀ a, IsMonHom (p₀ a)) → (∀ a, IsMonHom (p₁ a)) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ H₀)), ∃! x : T ⟶ G₀, ∀ a, x ≫ p₀ a = y a) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ H₁)), ∃! x : T ⟶ G₁, ∀ a, x ≫ p₁ a = y a) → ∀ (F : G₀ ⟶ G₁), IsMonHom F → IsIso F → (∀ (z z' : 𝟙_ (Over (Sp K)) ⟶ G₀), (∃ k : ℕ, z ^ (l ^ k) = 1) → (∃ k : ℕ, z' ^ (l ^ k) = 1) → ∀ a a', z ≫ p₀ a = z' ≫ p₀ a' → z ≫ F ≫ p₁ a = z' ≫ F ≫ p₁ a') → ∃ f₁ : H₀ ⟶ H₁, IsMonHom f₁ ∧ IsIso f₁ ∧ ∀ a, F ≫ p₁ a = p₀ a ≫ f₁ := by
  intro K _ _ G₀ G₁ H₀ H₁ _ _ _ _ _ _ hH₀ hH₁ l hl hlK p₀ p₁ hp₀ hp₁ hu₀ hu₁ F hF hFi htor
  classical
  obtain ⟨j₀, hj₀m, hj₀1, hj₀2⟩ := exists_sections p₀ hp₀ hu₀
  obtain ⟨j₁, hj₁m, hj₁1, hj₁2⟩ := exists_sections p₁ hp₁ hu₁
  haveI := hF
  haveI := hFi
  haveI := fun a => hp₀ a
  haveI := fun a => hp₁ a
  haveI := fun b => hj₀m b
  have hpj : ∀ b a : Fin 8, j₀ b ≫ p₀ a = if a = b then 𝟙 H₀ else 1 := by
    intro b a
    split_ifs with h
    · subst h; exact hj₀1 a
    · exact hj₀2 b a h
  have hpj₁ : ∀ b a : Fin 8, j₁ b ≫ p₁ a = if a = b then 𝟙 H₁ else 1 := by
    intro b a
    split_ifs with h
    · subst h; exact hj₁1 a
    · exact hj₁2 b a h

  have htors : ∀ (b : Fin 8) (y : 𝟙_ (Over (Sp K)) ⟶ H₀) (k : ℕ), y ^ (l ^ k) = 1 →
      ∃ k : ℕ, (y ≫ j₀ b) ^ (l ^ k) = 1 := by
    intro b y k hy
    haveI := hj₀m b
    exact ⟨k, by rw [← MonObj.pow_comp, hy, MonObj.one_comp]⟩

  have hoff : ∀ b a : Fin 8, a ≠ b → j₀ b ≫ F ≫ p₁ a = 1 := by
    intro b a hab
    haveI := hj₀m b
    haveI := hp₁ a
    refine GlobalTheory.TorsionDense.eq_one_of_torsion_comp_eq_one K H₀ H₁ hH₀ hH₁ l hl hlK _ inferInstance
      (fun _ _ y k hy => ?_)
    have := htor (y ≫ j₀ b) 1 (htors b y k hy) ⟨0, _root_.one_pow _⟩ a a
      (by rw [Category.assoc, hpj, if_neg hab, MonObj.comp_one, MonObj.one_comp])
    rw [MonObj.one_comp (F ≫ p₁ a)] at this
    simpa [Category.assoc] using this

  have hdiag : ∀ a : Fin 8, j₀ a ≫ F ≫ p₁ a = j₀ 0 ≫ F ≫ p₁ 0 := by
    intro a
    haveI := hj₀m a
    haveI := hj₀m 0
    haveI := hp₁ a
    haveI := hp₁ 0
    have hpt : ∀ (T : Over (Sp K)) (x : T ⟶ H₀),
        x ≫ ((j₀ a ≫ F ≫ p₁ a) * (j₀ 0 ≫ F ≫ p₁ 0)⁻¹) =
          (x ≫ j₀ a ≫ F ≫ p₁ a) * (x ≫ j₀ 0 ≫ F ≫ p₁ 0)⁻¹ := by
      intro T x
      rw [MonObj.comp_mul, GrpObj.comp_inv]
    have hmon : IsMonHom ((j₀ a ≫ F ≫ p₁ a) * (j₀ 0 ≫ F ≫ p₁ 0)⁻¹) := by
      apply isMonHom_of_points
      · intro T
        rw [hpt, MonObj.one_comp, MonObj.one_comp, _root_.inv_one, _root_.mul_one]
      · intro T x y
        rw [hpt, hpt, hpt, MonObj.mul_comp, MonObj.mul_comp, _root_.mul_inv, _root_.mul_mul_mul_comm]
    have h1 := GlobalTheory.TorsionDense.eq_one_of_torsion_comp_eq_one K H₀ H₁ hH₀ hH₁ l hl hlK _ hmon
      (fun _ _ y k hy => by
        have := htor (y ≫ j₀ a) (y ≫ j₀ 0) (htors a y k hy) (htors 0 y k hy) a 0
          (by rw [Category.assoc, Category.assoc, hpj, hpj, if_pos rfl, if_pos rfl])
        rw [hpt, _root_.mul_inv_eq_one]
        simpa [Category.assoc] using this)
    exact _root_.mul_inv_eq_one.mp h1
  let f₁ : H₀ ⟶ H₁ := j₀ 0 ≫ F ≫ p₁ 0
  haveI : IsMonHom f₁ := by
    haveI := hj₀m 0
    haveI := hp₁ 0
    dsimp [f₁]
    infer_instance
  have hcomm : ∀ a, F ≫ p₁ a = p₀ a ≫ f₁ := by
    intro a
    haveI := hp₁ a
    haveI := hp₀ a
    refine hom_ext_sections p₀ hp₀ hu₀ j₀ hj₀1 hj₀2 _ _ (fun b => ?_)
    rw [← Category.assoc (j₀ b) (p₀ a), hpj]
    split_ifs with hab
    · subst hab
      rw [Category.id_comp, hdiag]
    · rw [hoff b a hab, MonObj.one_comp]
  have hsec : j₀ 0 ≫ F = f₁ ≫ j₁ 0 := by
    refine (hu₁ H₀ fun a => (f₁ ≫ j₁ 0) ≫ p₁ a).unique (fun a => ?_) (fun _ => rfl)
    rw [Category.assoc, hcomm, ← Category.assoc, hpj, Category.assoc, hpj₁]
    split_ifs
    · simp
    · rw [MonObj.one_comp, MonObj.comp_one]
  refine ⟨f₁, inferInstance, ⟨⟨j₁ 0 ≫ inv F ≫ p₀ 0, ?_, ?_⟩⟩, hcomm⟩
  · rw [← Category.assoc, ← hsec, Category.assoc, IsIso.hom_inv_id_assoc, hj₀1]
  · rw [Category.assoc, Category.assoc, ← hcomm, IsIso.inv_hom_id_assoc, hj₁1]

end GlobalTheory.PowerDiagonal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsilonPartDeformationFormClassEqCoboundaryOfLif
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS.LiftTriv

section General

variable {R₁ R₂ R' : Type} [CommRing R₁] [CommRing R₂] [CommRing R'] {I₁ : Ideal R₁} {I₂ : Ideal R₂}
  {I' : Ideal R'} {X₁ X₂ X' : Scheme.{0}} {κ₁ : DividedPowers I₁} {κ₂ : DividedPowers I₂} {κ' : DividedPowers I'}
  {s₁ : X₁ ⟶ Sp R₁} {s₂ : X₂ ⟶ Sp R₂} {s' : X' ⟶ Sp R'} {σ₁ : R₁ →+* R'} {σ₂ : R₂ →+* R'}
  {p₁ : X' ⟶ X₁} {p₂ : X' ⟶ X₂}

def pv (h : IsMor κ₁ s₁ κ' s' σ₁ p₁) (f : Z1 (O κ₁ s₁)) {T T' : Thick κ' s'} (φ : T ⟶ T') : T'.B :=
  ev f (h.functor.map φ)

theorem exists_of_pull1_eq (h₁ : IsMor κ₁ s₁ κ' s' σ₁ p₁) (h₂ : IsMor κ₂ s₂ κ' s' σ₂ p₂) (f : Z1 (O κ₁ s₁))
    (g b : Z1 (O κ₂ s₂)) (r : R')
    (e : h₁.pull1 (H1.mk _ f) = h₂.pull1 (H1.mk _ g) + r • h₂.pull1 (H1.mk _ b)) :
    ∃ G : ∀ T : Thick κ' s', T.B, ∀ (T T' : Thick κ' s') (φ : T ⟶ T'),
      G T' - φ.φ (G T) = pv h₁ f φ - (pv h₂ g φ + algebraMap R' T'.B r * pv h₂ b φ) := by
  have e' : H1.mk (O κ' s') (h₁.coef.pullbackOneCocycle f) =
      H1.mk (O κ' s') (h₂.coef.pullbackOneCocycle g + r • h₂.coef.pullbackOneCocycle b) := by
    rw [map_add, map_smul]
    exact e
  obtain ⟨G, hG⟩ := H1.mk_eq_mk.1 e'
  refine ⟨G, fun T T' φ ↦ ?_⟩
  rw [← Algebra.smul_def]
  exact congrFun (congrFun (congrFun hG T) T') φ

theorem form_idLift {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (f : Form s)
    {T T' : Thick (dp0 R) s} (Φ : T ⟶ T') (y : Sp T.B ⟶ X) (hy : y ≫ s = spMap (algebraMap R T.B))
    (ey : spMap T.π ≫ y = T.x) (y' : Sp T'.B ⟶ X) (hy' : y' ≫ s = spMap (algebraMap R T'.B))
    (ey' : spMap T'.π ≫ y' = T'.x) (e : spMap (Φ.φ : T.B →+* T'.B) ≫ y = y') :
    ev f.1 Φ = ev f.1 (idLift T' y' hy' ey') - Φ.φ (ev f.1 (idLift T y hy ey)) := by
  let a : Thick.triv T.B y hy ⟶ Thick.triv T'.B y' hy' := Thick.trivHom Φ.φ e
  have k := Form.ev_sq f a (idLift T' y' hy' ey') (idLift T y hy ey) Φ rfl rfl fun _ ↦ rfl
  exact eq_sub_of_add_eq' k.symm

end General

section Eps

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

omit [GrpObj A] in

def epsHom {P Q : GPt A} (φ : P.Hom Q) : P.eps ⟶ Q.eps :=
  letI := P.eps.alg
  letI := Q.eps.alg
  { φ := { dualMap (φ.ρ : P.B →+* Q.B) with
      commutes' := fun r ↦ by
        change dualMap (φ.ρ : P.B →+* Q.B) (dualMap (algebraMap K P.B) r) = dualMap (algebraMap K Q.B) r
        ext <;> simp [dualMap] }
    φ₀ := (φ.ρ : P.B →+* Q.B)
    comm := fun c ↦ by
      change φ.ρ c.fst = (dualMap (φ.ρ : P.B →+* Q.B) c).fst
      simp [dualMap]
    dp := isDPMorphism_sqDP (SqExt.ofModule K P.B P.B).sq (SqExt.ofModule K Q.B Q.B).sq _ fun a ha ↦ by
      have ha' : a.fst = 0 := ha
      change (dualMap (φ.ρ : P.B →+* Q.B) a).fst = 0
      simp [dualMap, ha']
    pt := φ.pt }

def epsSec (P : GPt A) : P.triv ⟶ (constMor A).isMor.obj P.eps :=
  letI := ((constMor A).isMor.obj P.eps).alg
  Thick.trivHom
    { (TrivSqZeroExt.inlAlgHom K P.B P.B : P.B →+* DualNumber P.B) with
      commutes' := fun r ↦ by
        change TrivSqZeroExt.inl (algebraMap K P.B r) =
          dualMap (algebraMap K P.B) (algebraMap K (DualNumber K) r)
        ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl] }
    (by
      change spMap (RingHom.id P.B) ≫ P.x = P.x ≫ (𝟙 A : A ⟶ A).left
      simp [Cris.spMap_id])

def secVal (f : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) (P : GPt A) : DualNumber P.B := ev f (epsSec P)

theorem pv_const (f : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) {P Q : GPt A} (φ : P.Hom Q) :
    (pv (constMor A).isMor f (epsHom φ) : DualNumber Q.B) =
      TrivSqZeroExt.inl (ev f φ.triv : Q.B) + secVal f Q - dualMap (φ.ρ : P.B →+* Q.B) (secVal f P) := by
  have k := Cris.ev_sq f φ.triv (epsSec Q) (epsSec P) ((constMor A).isMor.functor.map (epsHom φ)) fun c ↦ by
    change (TrivSqZeroExt.inl (φ.ρ c) : DualNumber Q.B) = dualMap (φ.ρ : P.B →+* Q.B) (TrivSqZeroExt.inl c)
    ext <;> simp [dualMap]
  exact eq_sub_of_add_eq' (G := DualNumber Q.B) k.symm

variable {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left}

theorem pv_lift (h : IsGrpPullback A A' (DeRham.epsRed K) i) (ω' : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K))))
    {P Q : GPt A} (φ : P.Hom Q) {y : Sp (DualNumber P.B) ⟶ A'.left} {y' : Sp (DualNumber Q.B) ⟶ A'.left}
    (hy : IsLift i P y) (hy' : IsLift i Q y') (e : spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ y = y') :
    (pv (liftMor (epsDP K) h).isMor ω'.1 (epsHom φ) : DualNumber Q.B) =
      liftVal h ω'.1 hy' - dualMap (φ.ρ : P.B →+* Q.B) (liftVal h ω'.1 hy) := by
  exact form_idLift ω' ((liftMor (epsDP K) h).isMor.functor.map (epsHom φ)) y hy.1 hy.2 y' hy'.1 hy'.2 e

end Eps

theorem eps_part_eq_coboundary (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A]
    (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left)
    (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ω' : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K))))
    (ω : Form (A.hom ≫ 𝟙 (Sp K))) (b : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))))
    (hyp : (liftMor (epsDP K) h).isMor.pull1 (Form.cl _ ω') = (constMor A).isMor.pull1 (Form.cl _ ω) +
      (DualNumber.eps : DualNumber K) • (constMor A).isMor.pull1 (H1.mk _ b)) :
    ∃ G : PtFn (A.hom ≫ 𝟙 (Sp K)), ∀ (P Q : GPt A) (φ : P.Hom Q) (y : Sp (DualNumber P.B) ⟶ A'.left)
      (y' : Sp (DualNumber Q.B) ⟶ A'.left) (hy : IsLift i P y) (hy' : IsLift i Q y'),
      spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ y = y' →
      ev b φ.triv = ((liftVal h ω'.1 hy').snd + G Q) - φ.ρ ((liftVal h ω'.1 hy).snd + G P) := by
  obtain ⟨G₀, hG⟩ := exists_of_pull1_eq (liftMor (epsDP K) h).isMor (constMor A).isMor ω'.1 ω.1 b
    DualNumber.eps hyp
  let G₁ : ∀ P : GPt A, DualNumber P.B := fun P ↦ G₀ (Pt.eps P)
  refine ⟨fun P ↦ -(secVal ω.1 P).snd - (secVal b P).fst - (G₁ P).snd, fun P Q φ y y' hy hy' e ↦ ?_⟩
  have k : G₁ Q - dualMap (φ.ρ : P.B →+* Q.B) (G₁ P) =
      (pv (liftMor (epsDP K) h).isMor ω'.1 (epsHom φ) : DualNumber Q.B) -
        ((pv (constMor A).isMor ω.1 (epsHom φ) : DualNumber Q.B) +
          dualMap (algebraMap K Q.B) DualNumber.eps * (pv (constMor A).isMor b (epsHom φ) : DualNumber Q.B)) :=
    hG P.eps Q.eps (epsHom φ)
  rw [pv_lift h ω' φ hy hy' e, pv_const, pv_const] at k
  have k2 := congrArg TrivSqZeroExt.snd k
  simp [dualMap] at k2
  simp only [map_add, map_sub, map_neg]
  linear_combination k2

end GlobalTheory.CechKS.LiftTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfTorsionPointClassAtStalkEq
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem eq_of_valAt_eq : ∀ {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [IsSeparated G.hom]
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (P Q : Over.mk t ⟶ G)
    (PT QT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hQT : QT ≫ (torsion.ι G n).left = Q.left) (x : Sp K) (c : M) (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) c)
    (hcQ : GlobalTheory.TorsSpec.ValAt G n ℓ w (QT x) c), P = Q := by
  intro X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ K _ _ t P Q PT QT hPT hQT x c hcP hcQ
  haveI hEt : Etale (torsion G n).hom := GlobalTheory.GrpTangent.etale_torsion G hn
  have hιT : (torsion.ι G n).left ≫ G.hom = (torsion G n).hom := Over.w (torsion.ι G n)
  have hPt : PT ≫ (torsion G n).hom = t := by
    rw [← hιT, ← Category.assoc, hPT]; exact Over.w P
  have hQt : QT ≫ (torsion G n).hom = t := by
    rw [← hιT, ← Category.assoc, hQT]; exact Over.w Q
  obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  let pq : Sp K ⟶ pullback (torsion G n).hom (torsion G n).hom := pullback.lift PT QT (hPt.trans hQt.symm)
  let q := pq (IsLocalRing.closedPoint K)
  have hfq : (pullback.fst (torsion G n).hom (torsion G n).hom) q = PT (IsLocalRing.closedPoint K) := by
    show (pq ≫ pullback.fst (torsion G n).hom (torsion G n).hom) (IsLocalRing.closedPoint K) = _
    rw [pullback.lift_fst]
  have hsq : (pullback.snd (torsion G n).hom (torsion G n).hom) q = QT (IsLocalRing.closedPoint K) := by
    show (pq ≫ pullback.snd (torsion G n).hom (torsion G n).hom) (IsLocalRing.closedPoint K) = _
    rw [pullback.lift_snd]
  haveI hdom : IsDomain ((pullback (torsion G n).hom (torsion G n).hom).presheaf.stalk q) :=
    isDomain_stalk_of_etale (pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom) q
  let Wp := pullback (torsion G n).hom (torsion G n).hom
  let R : Type := Wp.presheaf.stalk q
  let Ω := AlgebraicClosure (FractionRing R)
  let φ : R →+* Ω := algebraMap R Ω
  have hφ : Function.Injective φ := by
    have e : φ = (algebraMap (FractionRing R) Ω).comp (algebraMap R (FractionRing R)) :=
      IsScalarTower.algebraMap_eq R (FractionRing R) Ω
    rw [e]
    exact (algebraMap (FractionRing R) Ω).injective.comp (IsFractionRing.injective R (FractionRing R))
  let ybar : Sp Ω ⟶ Spec (Wp.presheaf.stalk q) := Spec.map (CommRingCat.ofHom φ)
  haveI hyd : IsDominant ybar := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  let s0 : Sp Ω := IsLocalRing.closedPoint Ω
  have hgen : ∀ e, ybar s0 ⤳ e := by
    intro e
    have hr : Set.range ybar = {ybar s0} := Set.eq_singleton_iff_unique_mem.mpr
      ⟨⟨s0, rfl⟩, by rintro _ ⟨s, rfl⟩; rw [Subsingleton.elim s s0]⟩
    rw [specializes_iff_mem_closure, ← hr, ybar.denseRange.closure_range]
    trivial
  let f : Spec (Wp.presheaf.stalk q) ⟶ X' :=
    Wp.fromSpecStalk q ≫ pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom
  obtain ⟨w', hw'q, hw'ξ⟩ := Flat.generalizingMap (pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom)
    (genericPoint_specializes ((pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom) q))
  have hw'r : w' ∈ Set.range (Wp.fromSpecStalk q) := by rw [Scheme.range_fromSpecStalk]; exact hw'q
  obtain ⟨d, hd⟩ := hw'r
  have hξV : genericPoint X' ∈ Set.range ℓ := by
    rw [(genericPoint_spec X').mem_open_set_iff ℓ.isOpenEmbedding.isOpen_range]
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨ℓ v, trivial, v, rfl⟩
  have hsp : (ybar ≫ f) s0 ⤳ genericPoint X' := by
    have h1 := (hgen d).map f.continuous
    have e2 : f d = (pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom) w' := by
      rw [← hd]; rfl
    rw [show (ybar ≫ f) s0 = f (ybar s0) from rfl, ← hw'ξ, ← e2]
    exact h1
  have H : Set.range (ybar ≫ f) ⊆ Set.range ℓ := by
    rintro _ ⟨s, rfl⟩
    rw [Subsingleton.elim s s0]
    exact hsp.mem_open ℓ.isOpenEmbedding.isOpen_range hξV
  let z : Sp Ω ⟶ V := IsOpenImmersion.lift ℓ (ybar ≫ f) H
  have hz : z ≫ ℓ = ybar ≫ f := IsOpenImmersion.lift_fac _ _ _
  have hcP' : ValAt G n ℓ w ((pullback.fst (torsion G n).hom (torsion G n).hom) q) c := by rw [hfq]; exact hcP
  have hcQ' : ValAt G n ℓ w ((pullback.snd (torsion G n).hom (torsion G n).hom) q) c := by rw [hsq]; exact hcQ
  have k1 : Spec.map ((pullback.fst (torsion G n).hom (torsion G n).hom).stalkMap q) ≫
      (torsion G n).left.fromSpecStalk ((pullback.fst (torsion G n).hom (torsion G n).hom) q) =
      Wp.fromSpecStalk q ≫ pullback.fst (torsion G n).hom (torsion G n).hom := Scheme.SpecMap_stalkMap_fromSpecStalk _
  have k2 : Spec.map ((pullback.snd (torsion G n).hom (torsion G n).hom).stalkMap q) ≫
      (torsion G n).left.fromSpecStalk ((pullback.snd (torsion G n).hom (torsion G n).hom) q) =
      Wp.fromSpecStalk q ≫ pullback.snd (torsion G n).hom (torsion G n).hom := Scheme.SpecMap_stalkMap_fromSpecStalk _
  have h1 := hcP' Ω (ybar ≫ Spec.map ((pullback.fst (torsion G n).hom (torsion G n).hom).stalkMap q)) z (by
    rw [hz, Category.assoc, reassoc_of% k1])
  have h2 := hcQ' Ω (ybar ≫ Spec.map ((pullback.snd (torsion G n).hom (torsion G n).hom).stalkMap q)) z (by
    rw [hz, Category.assoc, reassoc_of% k2, ← pullback.condition])
  rw [Category.assoc, reassoc_of% k1] at h1
  rw [Category.assoc, reassoc_of% k2] at h2
  have hu : Wp.fromSpecStalk q ≫ pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left =
      Wp.fromSpecStalk q ≫ pullback.snd (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left := by
    refine ext_of_isDominant_of_isSeparated G.hom ?_ ybar (h1.trans h2.symm)
    simp only [Category.assoc, hιT, pullback.condition]
  have hpq : Spec.map (Scheme.stalkClosedPointTo pq) ≫ Wp.fromSpecStalk q = pq :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk pq
  apply Over.OverMorphism.ext
  rw [← hPT, ← hQT]
  calc PT ≫ (torsion.ι G n).left
      = pq ≫ pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left := by
        rw [← Category.assoc, pullback.lift_fst]
    _ = Spec.map (Scheme.stalkClosedPointTo pq) ≫ Wp.fromSpecStalk q ≫
          pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left := by
        rw [reassoc_of% hpq]
    _ = Spec.map (Scheme.stalkClosedPointTo pq) ≫ Wp.fromSpecStalk q ≫
          pullback.snd (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left := by
        rw [hu]
    _ = QT ≫ (torsion.ι G n).left := by
        rw [reassoc_of% hpq, ← Category.assoc, pullback.lift_snd]

end GlobalTheory.TorsSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeIntStalkOfArithBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.ZH.RatModel

theorem essFiniteType_int_stalk_of_arithBase {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω]
    [hA : ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z) :
    Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := by
  haveI : LocallyOfFiniteType M.s := M.lft
  let y : PrimeSpectrum o' := M.s x
  letI A : Algebra o' ((Sp o').presheaf.stalk (M.s x)) := StructureSheaf.stalkAlgebra _ y
  haveI : @IsLocalization.AtPrime o' _ ((Sp o').presheaf.stalk (M.s x)) _ A y.asIdeal _ :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := @algebraMap o' ((Sp o').presheaf.stalk (M.s x)) _ _ A
  have h₁ : (M.s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap M.s x
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  haveI : Algebra.FiniteType ℤ o' := hA.ft
  have h₀ : (algebraMap ℤ o').EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h := ((h₀.comp h₂).comp h₁)
  rw [← RingHom.essFiniteType_algebraMap]
  convert h
  exact RingHom.ext_int _ _

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenDefectDegenerationDataBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenDefect_degenerationData_baseChange : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (R₂ : Type) [CommRing R₂] [IsDomain R₂] (σ : R₁ →+* R₂) (D₁ : DegPre R₁) (D₂ : DegPre R₂) (β : D₂.P.A.left ⟶ D₁.P.A.left) (v : LB.Iso D₂.P.L (D₁.P.L.pull β)) (xe : D₂.X ≃+ D₁.X) (gam : FractionRing R₁ →+* FractionRing R₂), (∀ r, gam (algebraMap R₁ _ r) = algebraMap R₂ _ (σ r)) → IsGrpPullback D₂.P.A D₁.P.A (spMap σ) β → v.IsGen → (∀ x, (D₂.c x).left ≫ β = spMap σ ≫ (D₁.c (xe x)).left) → GlobalTheory.PsiRing.RigCmp σ D₁ D₂ β v → GlobalTheory.PsiRing.PsiCmp D₁ D₂ β v xe (spMap gam) → ∀ h : D₁.X → (FractionRing R₁)ˣ, EvenDefect D₁ h → EvenDefect D₂ fun χ => Units.map gam.toMonoidHom (h (xe χ)) := by
  first | exact @GlobalTheory.PolDeg.evenDefect_baseChange | exact GlobalTheory.PolDeg.evenDefect_baseChange | (intros; apply GlobalTheory.PolDeg.evenDefect_baseChange <;> assumption)
end

