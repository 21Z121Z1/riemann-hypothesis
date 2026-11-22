import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2528
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutomorphismActsOnDeeperLevelLabels
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GalAct

open MonObj in

theorem exists_mulEquiv_points {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {X : Scheme.{0}} (t : X ⟶ S') (g : X ⟶ S)
    (hg : t ≫ f = g) :
    ∃ e : (Over.mk t ⟶ G') ≃* (Over.mk g ⟶ G), ∀ z, (e z).left = z.left ≫ F := by
  subst hg
  let m : (Over.mk t ⟶ G') → (Over.mk (t ≫ f) ⟶ G) := fun z => Over.homMk (z.left ≫ F) (by
    have h : z.left ≫ G'.hom = t := Over.w z
    show (z.left ≫ F) ≫ G.hom = t ≫ f
    rw [Category.assoc, hF.1.w, ← Category.assoc, h])
  have hm : ∀ z, (m z).left = z.left ≫ F := fun _ => rfl
  have hmul : ∀ x y, m (x * y) = m x * m y := fun x y =>
    Over.OverMorphism.ext ((hm _).trans (hF.2 (Over.mk t) x y (m x) (m y) (hm x) (hm y)).symm)
  have hinj : Function.Injective m := fun x y h => by
    refine Over.OverMorphism.ext (hF.1.hom_ext ?_ ((Over.w x).trans (Over.w y).symm))
    rw [← hm, ← hm, h]
  have hsurj : Function.Surjective m := fun z =>
    ⟨Over.homMk (hF.1.lift z.left t (Over.w z)) (hF.1.lift_snd _ _ _),
      Over.OverMorphism.ext ((hm _).trans (hF.1.lift_fst _ _ _))⟩
  exact ⟨MulEquiv.ofBijective (MonoidHom.mk' m hmul) ⟨hinj, hsurj⟩, hm⟩

theorem epi_spMap_of_field {K L : Type} [Field K] [Field L] (f : K →+* L) : Epi (spMap f) := by
  have f₁ : Flat (spMap f) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField K) f
  have f₂ : Surjective (spMap f) := ⟨fun y => ⟨(default : PrimeSpectrum L), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem eq_id_of_frac {A K : Type} [CommRing A] [Field K] (φ : A →+* K) (h : ∀ x, ∃ a b, x = φ a / φ b)
    (u : Sp K ⟶ Sp K) (hu : u ≫ spMap φ = spMap φ) : u = 𝟙 _ := by
  obtain ⟨j, rfl⟩ := Spec.map_surjective u
  have e : CommRingCat.ofHom φ ≫ j = CommRingCat.ofHom φ := Spec.map_injective ((Spec.map_comp _ _).trans hu)
  have e' : ∀ a, j.hom (φ a) = φ a := fun a => congrArg (fun q => q.hom a) e
  have : j = 𝟙 _ := by
    ext x
    obtain ⟨a, b, rfl⟩ := h x
    exact (map_div₀ j.hom (φ a) (φ b)).trans (by rw [e', e']; rfl)
  rw [this, Spec.map_id]

open MonObj in

theorem exists_generic_labels {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real)
    {G : Over (Sp Ω)} [GrpObj G] {b : G.left ⟶ ρ.P.A.left} (hb : IsGrpPullback G ρ.P.A (spMap S.R.val.toRingHom) b) :
    ∃ w : S.Gam → (Over.mk (𝟙 (Sp Ω)) ⟶ G), (∀ x, (w x).left ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left) ∧
      (∀ x y, w (x + y) = w x * w y) ∧ Function.Injective w ∧ (∀ x, w x ^ (S.r * S.N) = 1) ∧
      ∀ z, z ^ (S.r * S.N) = 1 → ∃ a, w a = z := by
  obtain ⟨e, he⟩ := exists_mulEquiv_points hb (𝟙 _) (spMap S.R.val.toRingHom) (Category.id_comp _)
  let j : Over.mk (spMap S.R.val.toRingHom) ⟶ baseOver (Sp S.R) := Over.homMk (spMap S.R.val.toRingHom) (by simp)
  let k : Sp (AlgebraicClosure Ω) ⟶ Sp Ω := spMap (algebraMap Ω (AlgebraicClosure Ω))
  have : Epi k := epi_spMap_of_field _
  let k' : Over.mk (k ≫ spMap S.R.val.toRingHom) ⟶ Over.mk (spMap S.R.val.toRingHom) := Over.homMk k rfl
  let w : S.Gam → (Over.mk (𝟙 (Sp Ω)) ⟶ G) := fun x => e.symm (j ≫ ρ.pt x)
  have hw : ∀ x, e (w x) = j ≫ ρ.pt x := fun x => e.apply_symm_apply _
  have hadd : ∀ x y, w (x + y) = w x * w y := fun x y => by
    apply e.injective
    rw [map_mul, hw, hw, hw, ρ.pt_add, MonObj.comp_mul]
  let w' : Multiplicative S.Gam →* (Over.mk (𝟙 (Sp Ω)) ⟶ G) := MonoidHom.mk' (fun x => w x.toAdd) fun x y => hadd _ _
  have htor : ∀ x, w x ^ (S.r * S.N) = 1 := fun x => by
    have h0 : (S.r * S.N) • x = 0 := by
      funext i
      simp [nsmul_eq_mul]
    have h1 : (Multiplicative.ofAdd x) ^ (S.r * S.N) = 1 := by rw [← ofAdd_nsmul, h0, ofAdd_zero]
    exact (map_pow w' (Multiplicative.ofAdd x) _).symm.trans (by rw [h1, map_one])
  have key : ∀ z : Over.mk (𝟙 (Sp Ω)) ⟶ G, z ^ (S.r * S.N) = 1 → ∃! a, w a = z := fun z hz => by
    have h := ρ.pt_bij (AlgebraicClosure Ω) (k ≫ spMap S.R.val.toRingHom) (k' ≫ e z)
      ((map_pow (preHom k') (e z) _).symm.trans (by rw [← map_pow, hz, map_one, map_one]))
    refine (existsUnique_congr fun a => ?_).1 h
    constructor
    · intro ha
      apply e.injective
      rw [hw]
      refine Over.OverMorphism.ext ((cancel_epi k).1 ?_)
      exact (Category.assoc _ _ _).symm.trans (congrArg (fun q => q.left) ha)
    · rintro rfl
      rw [hw]
      exact Over.OverMorphism.ext (Category.assoc _ _ _)
  refine ⟨w, fun x => (he _).symm.trans (congrArg (fun q => q.left) (hw x)), hadd,
    fun x y h => (key _ (htor y)).unique h rfl, htor, fun z hz => (key z hz).exists⟩

open MonObj in

theorem exists_label_action {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real)
    {G : Over (Sp Ω)} [GrpObj G] {b : G.left ⟶ ρ.P.A.left} (hb : IsGrpPullback G ρ.P.A (spMap S.R.val.toRingHom) b)
    (σ : Ω →+* Ω) (hσ : Function.Surjective σ) {t : G.left ⟶ G.left} (ht : IsGrpPullback G G (spMap σ) t) :
    ∃ a : S.Gam ≃+ S.Gam, (∀ x (w w' : Sp Ω ⟶ G.left), w ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left →
      w' ≫ t = spMap σ ≫ w → w' ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt (a x)).left) ∧
      ∀ x (w : Sp Ω ⟶ G.left), w ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left → w ≫ t = spMap σ ≫ w → a x = x := by
  obtain ⟨p, hp, hadd, hinj, htor, hsurj⟩ := exists_generic_labels ρ hb
  obtain ⟨e, he⟩ := exists_mulEquiv_points ht (𝟙 _) (spMap σ) (Category.id_comp _)
  have : Epi (spMap σ) := epi_spMap_of_field _
  let s : Over.mk (spMap σ) ⟶ Over.mk (𝟙 (Sp Ω)) := Over.homMk (spMap σ) (Category.comp_id _)
  let τ : (Over.mk (𝟙 (Sp Ω)) ⟶ G) →* (Over.mk (𝟙 (Sp Ω)) ⟶ G) := e.symm.toMonoidHom.comp (preHom s)
  have hτ : ∀ z, (τ z).left ≫ t = spMap σ ≫ z.left := fun z =>
    (he _).symm.trans (congrArg (fun q => q.left) (e.apply_symm_apply (s ≫ z)))
  have τinj : Function.Injective τ := fun z z' h => by
    refine Over.OverMorphism.ext ((cancel_epi (spMap σ)).1 ?_)
    rw [← hτ, ← hτ, h]
  have hex : ∀ x, ∃ y, p y = τ (p x) := fun x => hsurj _ (by rw [← map_pow, htor, map_one])
  choose a ha using hex
  let a' : S.Gam →+ S.Gam := AddMonoidHom.mk' a fun x y => hinj (by rw [hadd, ha, ha, ha, hadd, map_mul])
  have ainj : Function.Injective a' := fun x y h => hinj (τinj (by
    rw [← ha, ← ha]; exact congrArg p h))
  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have abij : Function.Bijective a' := Finite.injective_iff_bijective.1 ainj
  have h₁ : ∀ x (w : Sp Ω ⟶ G.left), w ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left → w = (p x).left := fun x w h => by
    refine hb.1.hom_ext (h.trans (hp x).symm) (Eq.trans ?_ (Over.w (p x)).symm)
    refine eq_id_of_frac S.R.val.toRingHom (fun y => ?_) _ ?_
    · obtain ⟨c, hc, d, hd, rfl⟩ := S.frac y
      exact ⟨⟨c, hc⟩, ⟨d, hd⟩, rfl⟩
    · rw [Category.assoc, ← hb.1.w, ← Category.assoc, h, Category.assoc]
      exact (congrArg _ (Over.w (ρ.pt x))).trans (Category.comp_id _)
  have h₂ : ∀ x (w' : Sp Ω ⟶ G.left), w' ≫ t = spMap σ ≫ (p x).left → w' = (p (a x)).left := fun x w' h => by
    rw [ha]
    refine ht.1.hom_ext (h.trans (hτ _).symm) (Eq.trans ?_ (Over.w (τ (p x))).symm)
    refine eq_id_of_frac σ (fun y => ?_) _ ?_
    · obtain ⟨c, rfl⟩ := hσ y
      exact ⟨c, 1, by rw [map_one, div_one]⟩
    · rw [Category.assoc, ← ht.1.w, ← Category.assoc, h, Category.assoc]
      exact (congrArg _ (Over.w (p x))).trans (Category.comp_id _)
  refine ⟨AddEquiv.ofBijective a' abij, fun x w w' hw hw' => ?_, fun x w hw hw' => ?_⟩
  · rw [h₁ x w hw] at hw'
    rw [h₂ x w' hw']
    exact hp _
  · have e₁ := h₁ x w hw
    subst e₁
    exact hinj (Over.OverMorphism.ext (h₂ x _ hw').symm)

theorem exists_galLab : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁), ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a ∧ ∀ x, a (D.lab x) = D.lab x := by
  intro g n F W Z i X₁ _ _ _ _ _ _ _ ε₁ _ D σ
  obtain ⟨P₀, a₁, a₂, ε₀, h₁, h₂, l₁, l₂, hε, hpt⟩ := D.same
  have hs : spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp X₁.S.R.val.toRingHom) =
      spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp X₁.S.R.val.toRingHom) :=
    (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext fun y => σ.commutes _))
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : P₀.A.left ⟶ P₀.A.left, t ≫ a₁ = a₁ ∧
      t ≫ P₀.A.hom = P₀.A.hom ≫ spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) :=
    ⟨h₁.1.lift a₁ (P₀.A.hom ≫ spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) (by rw [Category.assoc, hs, h₁.1.w]),
      h₁.1.lift_fst _ _ _, h₁.1.lift_snd _ _ _⟩
  have ht : IsGrpPullback P₀.A P₀.A (spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) t := h₁.cancel (h₁.congr hs.symm ht₁.symm) ht₂
  have lt : LBIso (P₀.L.pull t) (X₁.ρ.P.L.pull a₁) :=
    l₁.chartPull (Geo.Tor.chartPullPull P₀.L t t rfl)
      (chartPullSame X₁.ρ.P.L (fun _ => a₁) (fun _ => a₁) _ t fun _ => ht₁.symm)
  obtain ⟨a, ha, ha'⟩ := exists_label_action D.X.ρ h₂ (σ : D.X.Ω₁ →+* D.X.Ω₁) σ.surjective ht
  refine ⟨a, ⟨P₀, a₂, t, ε₀, h₂, ht, l₂,
    LBIso.trans P₀.isLB (pull_isLB X₁.ρ.P.isLB _) (pull_isLB P₀.isLB _) l₁ lt.symm, fun E => ⟨(hε E).2, ?_⟩, ha⟩,
    fun x => ?_⟩
  · refine h₁.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, ht₁, (hε E).1, ← Category.assoc, ht₁]
    · rw [Category.assoc, Category.assoc, ht₂, Over.w (ε₀ E), ← Category.assoc, Over.w (ε₀ E), ht₂]
  · obtain ⟨w, hw₁, hw₂⟩ := hpt x
    refine ha' _ w hw₂ (h₁.1.hom_ext ?_ ?_)
    · rw [Category.assoc, Category.assoc, ht₁, hw₁, ← Category.assoc, hs]
    · have hw : w ≫ P₀.A.hom = 𝟙 _ := by
        refine eq_id_of_frac D.X.S.R.val.toRingHom (fun y => ?_) _ ?_
        · obtain ⟨c, hc, d, hd, rfl⟩ := D.X.S.frac y
          exact ⟨⟨c, hc⟩, ⟨d, hd⟩, rfl⟩
        · rw [Category.assoc, ← h₂.1.w, ← Category.assoc, hw₂, Category.assoc]
          exact (congrArg _ (Over.w (D.X.ρ.pt _))).trans (Category.comp_id _)
      rw [Category.assoc, Category.assoc, ht₂, hw, ← Category.assoc, hw, Category.id_comp, Category.comp_id]

end GlobalTheory.Poinc.GalAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisInvariantFunctionsFlatBaseChange
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.InvFun

open TensorProduct in

theorem alg_inv {R A R' B : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing B] [Algebra R A] [Algebra R R']
    [Algebra R B] [Algebra A B] [Algebra R' B] [IsScalarTower R A B] [IsScalarTower R R' B]
    [Algebra.IsPushout R A R' B] [Module.Flat R A] (hinj : Function.Injective (algebraMap R R'))
    {J : Type} [Finite J] (s : J → (R' →ₐ[R] R')) (hs : ∀ x : R', (∀ i, s i x = x) → x ∈ (algebraMap R R').range)
    (t : J → (B →+* B)) (htA : ∀ i a, t i (algebraMap A B a) = algebraMap A B a)
    (htR : ∀ i r, t i (algebraMap R' B r) = algebraMap R' B (s i r)) :
    Function.Injective (algebraMap A B) ∧ ∀ u : B, (∀ i, t i u = u) → u ∈ Set.range (algebraMap A B) := by
  classical
  cases nonempty_fintype J
  let e := Algebra.IsPushout.equiv R A R' B
  have he : ∀ (a : A) (r : R'), e (a ⊗ₜ r) = algebraMap A B a * algebraMap R' B r := fun a r =>
    Algebra.IsPushout.equiv_tmul R A R' B a r
  have hA : ∀ a : A, algebraMap A B a = e ((Algebra.linearMap R R').lTensor A (a ⊗ₜ 1)) := fun a => by
    simp [he]
  refine ⟨fun a b hab => ?_, fun u hu => ?_⟩
  · rw [hA, hA] at hab
    have h₁ := Module.Flat.lTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R R') hinj (e.injective hab)
    simpa using congrArg (TensorProduct.rid R A) h₁
  · let d : R' →ₗ[R] (J → R') := LinearMap.pi fun i => (s i).toLinearMap - LinearMap.id
    have hex : Function.Exact (Algebra.linearMap R R') d := by
      intro x
      constructor
      · intro hx
        exact hs x fun i => sub_eq_zero.1 (congrFun hx i)
      · rintro ⟨r, rfl⟩
        ext i
        simp [d]
    have hexA := Module.Flat.lTensor_exact A hex
    obtain ⟨w, rfl⟩ := e.surjective u
    have key : ∀ (w : A ⊗[R] R') (i : J), e (TensorProduct.piRight R R A (fun _ : J => R') (d.lTensor A w) i) =
        t i (e w) - e w := by
      intro w i
      induction w with
      | zero => simp
      | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]; ring
      | tmul a r => simp [d, he, htA, htR, mul_sub, tmul_sub]
    have h0 : d.lTensor A w = 0 := by
      apply (TensorProduct.piRight R R A (fun _ : J => R')).injective
      ext i
      apply e.injective
      rw [key, hu]
      simp
    obtain ⟨v, rfl⟩ := (hexA w).1 h0
    refine ⟨TensorProduct.rid R A v, ?_⟩
    rw [hA]
    congr 2
    exact (TensorProduct.rid R A).symm_apply_apply v

theorem app_comp_appLE {Y Y' : Scheme.{0}} {β : Y' ⟶ Y} {f : Y' ⟶ Y'} (hf : f ≫ β = β) (U : Y.Opens)
    (e : β ⁻¹ᵁ U ≤ f ⁻¹ᵁ (β ⁻¹ᵁ U)) : β.app U ≫ f.appLE (β ⁻¹ᵁ U) (β ⁻¹ᵁ U) e = β.app U := by
  refine (Scheme.Hom.comp_appLE f β U (β ⁻¹ᵁ U) e).symm.trans ?_
  rw [← Scheme.Hom.appLE_eq_app]
  simp only [hf]

theorem const_comp_appLE {R : CommRingCat.{0}} {Y : Scheme.{0}} {y : Y ⟶ Spec R} {f : Y ⟶ Y} {s : R ⟶ R}
    (hf : f ≫ y = y ≫ Spec.map s) (U : Y.Opens) (e : U ≤ f ⁻¹ᵁ U) :
    ((Scheme.ΓSpecIso R).inv ≫ y.appLE ⊤ U le_top) ≫ f.appLE U U e =
      s ≫ (Scheme.ΓSpecIso R).inv ≫ y.appLE ⊤ U le_top := by
  have e₁ : y.appLE ⊤ U le_top ≫ f.appLE U U e = (Spec.map s).appTop ≫ y.appLE ⊤ U le_top := by
    refine (Scheme.Hom.appLE_comp_appLE f y ⊤ U U le_top e).trans ?_
    simp only [hf]
    exact Scheme.Hom.comp_appLE y (Spec.map s) ⊤ U le_top
  rw [Category.assoc, e₁, Scheme.ΓSpecIso_inv_naturality_assoc]

theorem affine_inv {R R' : Type} [CommRing R] [CommRing R'] (ρ : R →+* R') (hρ : Function.Injective ρ) (hG : IsGal ρ)
    {Y Y' : Scheme.{0}} {y : Y ⟶ Sp R} {y' : Y' ⟶ Sp R'} {β : Y' ⟶ Y} [Flat y] (h : IsPullback β y' y (spMap ρ))
    (act : Gal ρ → (Y' ⟶ Y')) (hβ : ∀ σ, act σ ≫ β = β) (hy : ∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ))
    {U : Y.Opens} (hU : IsAffineOpen U) :
    Function.Injective (β.app U).hom ∧ ∀ u : Γ(Y', β ⁻¹ᵁ U),
      (∀ σ (h : β ⁻¹ᵁ U ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ U)), ((act σ).appLE _ _ h).hom u = u) → u ∈ Set.range (β.app U).hom := by
  have hp := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := β ⁻¹ᵁ U)
    le_top le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen h _ _ _
      (isAffineOpen_top _) (isAffineOpen_top _) hU)
  have hp' : IsPushout ((Scheme.ΓSpecIso (.of R)).inv ≫ y.appLE ⊤ U le_top)
      (CommRingCat.ofHom ρ) (β.app U)
      ((Scheme.ΓSpecIso (.of R')).inv ≫ y'.appLE ⊤ (β ⁻¹ᵁ U) le_top) := by
    refine hp.of_iso (Scheme.ΓSpecIso _) (.refl _) (Scheme.ΓSpecIso _) (.refl _) (by simp) ?_
      (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    exact Scheme.ΓSpecIso_naturality _
  have hfl : ((Scheme.ΓSpecIso (.of R)).inv ≫ y.appLE ⊤ U le_top).hom.Flat := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _))
      (y.flat_appLE (isAffineOpen_top _) hU le_top)
  have hle : ∀ σ, β ⁻¹ᵁ U ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ U) := fun σ => by
    rw [← Scheme.Hom.comp_preimage, hβ]
  algebraize [ρ, ((Scheme.ΓSpecIso (.of R)).inv ≫ y.appLE ⊤ U le_top).hom,
    (β.app U).hom,
    ((Scheme.ΓSpecIso (.of R')).inv ≫ y'.appLE ⊤ (β ⁻¹ᵁ U) le_top).hom,
    (((Scheme.ΓSpecIso (.of R)).inv ≫ y.appLE ⊤ U le_top) ≫ β.app U).hom]
  have : IsScalarTower R Γ(Y, U) Γ(Y', β ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
  have : IsScalarTower R R' Γ(Y', β ⁻¹ᵁ U) := .of_algebraMap_eq' congr($(hp'.w).hom)
  have : Algebra.IsPushout R Γ(Y, U) R' Γ(Y', β ⁻¹ᵁ U) :=
    CommRingCat.isPushout_iff_isPushout.mp hp'
  have := hG.1
  have H := alg_inv (R := R) (A := Γ(Y, U)) (R' := R') (B := Γ(Y', β ⁻¹ᵁ U)) hρ
    (fun σ : Gal ρ => (⟨Gal.hom σ, σ.2⟩ : R' →ₐ[R] R')) (fun x hx => hG.2 x fun σ hσ => hx ⟨σ, hσ⟩)
    (fun σ => ((act σ).appLE _ _ (hle σ)).hom) ?_ ?_
  · exact ⟨H.1, fun u hu => H.2 u fun σ => hu σ _⟩
  · intro σ a
    exact congr($(app_comp_appLE (hβ σ) U (hle σ)).hom a)
  · intro σ r
    exact congr($(const_comp_appLE (hy σ) (β ⁻¹ᵁ U) (hle σ)).hom r)

theorem app_res {Y Y' : Scheme.{0}} (β : Y' ⟶ Y) {U V : Y.Opens} (e : U ≤ V) (a : Γ(Y, V)) :
    (β.app U).hom ((Y.presheaf.map (homOfLE e).op).hom a) =
      (Y'.presheaf.map (homOfLE (β.preimage_mono e)).op).hom ((β.app V).hom a) :=
  congr($(β.naturality (homOfLE e).op).hom a)

theorem res_res {Y : Scheme.{0}} {U V W : Y.Opens} (e : U ≤ V) (e' : V ≤ W) (a : Γ(Y, W)) :
    (Y.presheaf.map (homOfLE e).op).hom ((Y.presheaf.map (homOfLE e').op).hom a) =
      (Y.presheaf.map (homOfLE (e.trans e')).op).hom a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem le_iSup_affine {Y : Scheme.{0}} (V : Y.Opens) :
    V ≤ ⨆ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ V}, U.1 := by
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUV⟩, hxU⟩

theorem injective_of_affine {Y Y' : Scheme.{0}} (β : Y' ⟶ Y)
    (H : ∀ U : Y.Opens, IsAffineOpen U → Function.Injective (β.app U).hom) (V : Y.Opens) :
    Function.Injective (β.app V).hom := by
  intro a b hab
  refine Y.sheaf.eq_of_locally_eq' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ V} => U.1) V
    (fun U => homOfLE U.2.2) (le_iSup_affine V) a b fun U => H U.1 U.2.1 ?_
  exact (app_res β U.2.2 a).trans ((congrArg _ hab).trans (app_res β U.2.2 b).symm)

theorem mem_range_of_affine {Y Y' : Scheme.{0}} (β : Y' ⟶ Y)
    (H : ∀ U : Y.Opens, Function.Injective (β.app U).hom) (V : Y.Opens) (u : Γ(Y', β ⁻¹ᵁ V))
    (hu : ∀ (U : Y.Opens) (_ : IsAffineOpen U) (e : U ≤ V),
      (Y'.presheaf.map (homOfLE (β.preimage_mono e)).op).hom u ∈ Set.range (β.app U).hom) :
    u ∈ Set.range (β.app V).hom := by
  choose a ha using fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ V} => hu U.1 U.2.1 U.2.2
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ V} => U.1) V
    (fun U => homOfLE U.2.2) (le_iSup_affine V) a (fun i j => H (i.1 ⊓ j.1) (by
      refine (app_res β inf_le_left (a i)).trans (Eq.trans ?_ (app_res β inf_le_right (a j)).symm)
      rw [ha, ha, res_res, res_res]))
  refine ⟨s, Y'.sheaf.eq_of_locally_eq' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ V} => β ⁻¹ᵁ U.1) (β ⁻¹ᵁ V)
    (fun U => homOfLE (β.preimage_mono U.2.2)) ?_ _ _ fun U => ?_⟩
  · rw [← β.preimage_iSup]
    exact β.preimage_mono (le_iSup_affine V)
  · exact (app_res β U.2.2 s).symm.trans ((congrArg _ (hs U)).trans (ha U))

theorem invariant_functions : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R']
    (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (Y Y' : Scheme.{0}) (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (β : Y' ⟶ Y), Flat y →
    IsPullback β y' y (spMap ρ) → ∀ (act : Gal ρ → (Y' ⟶ Y')), (∀ σ, act σ ≫ β = β) →
    (∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ)) → ∀ V : Y.Opens, Function.Injective (β.app V).hom ∧
    ∀ u : Γ(Y', β ⁻¹ᵁ V), (∀ σ (h : β ⁻¹ᵁ V ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ V)), ((act σ).appLE _ _ h).hom u = u) →
      u ∈ Set.range (β.app V).hom := by
  intro R _ _ R' _ _ _ ρ hF hG Y Y' y y' β _ h act hβ hy V
  have H := fun (U : Y.Opens) (hU : IsAffineOpen U) => affine_inv ρ hF.2.1 hG h act hβ hy hU
  have hinj := injective_of_affine β fun U hU => (H U hU).1
  refine ⟨hinj V, fun u hu => mem_range_of_affine β hinj V u fun U hU e => (H U hU).2 _ fun σ hσ => ?_⟩
  have hle : β ⁻¹ᵁ V ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, hβ]
  have e₁ : Y'.presheaf.map (homOfLE (β.preimage_mono e)).op ≫ (act σ).appLE _ _ hσ =
      (act σ).appLE _ _ hle ≫ Y'.presheaf.map (homOfLE (β.preimage_mono e)).op := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  exact (congr($(e₁).hom u)).trans (congrArg _ (hu σ hle))

end GlobalTheory.Mum.InvFun
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericUniformisedPullbackMumfordBundleMatching
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem genLam_pull_of_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (βW₂ : (G2 GW).left ⟶ (G2 G).left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), GlobalTheory.LN.CDvr W → Function.Injective φ → IsLocalHom φ → IsGrpPullback GW G (spMap φ) βW → Geo.Tor.IsSquare βW βW₂ → LBIso (abelian₂ GW UW.LG.L) (PP.pull βW₂) → ∃ (ga : FractionRing R →+* FractionRing W) (α : AW.A.left ⟶ A.A.left) (α₂ : (G2 AW.A).left ⟶ (G2 A.A).left), (∀ r, ga (algebraMap R _ r) = algebraMap W _ (φ r)) ∧ IsGrpPullback AW.A A.A (spMap ga) α ∧ Geo.Tor.IsSquare α α₂ ∧ LBIso (abelian₂ AW.A AW.L) ((abelian₂ A.A A.L).pull α₂) ∧ UW.gen.inv.left ≫ pullback.fst GW.hom (jK W) ≫ βW = α ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hExt W _ _ _ φ GW _ _ βW βW₂ DW AW UW hW hφ hφl hβ hsqW hPP
  let ga : FractionRing R →+* FractionRing W := IsFractionRing.map (K := FractionRing R) (L := FractionRing W) hφ
  have hga : ∀ r, ga (algebraMap R _ r) = algebraMap W _ (φ r) := fun r => by
    simp [ga, IsFractionRing.map, IsLocalization.map_eq]
  have hsq : jK W ≫ spMap φ = spMap ga ≫ jK R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [ga, IsFractionRing.map, IsLocalization.map_eq]
  let κW : pullback GW.hom (jK W) ⟶ pullback G.hom (jK R) :=
    pullback.lift (pullback.fst _ _ ≫ βW) (pullback.snd _ _ ≫ spMap ga) (by
      rw [Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition, Category.assoc, hsq, Category.assoc])
  have hκf : κW ≫ pullback.fst G.hom (jK R) = pullback.fst GW.hom (jK W) ≫ βW := pullback.lift_fst _ _ _
  have w : κW ≫ ((Over.pullback (jK R)).obj G).hom = ((Over.pullback (jK W)).obj GW).hom ≫ spMap ga :=
    pullback.lift_snd _ _ _
  have hκ : IsGrpPullback ((Over.pullback (jK W)).obj GW) ((Over.pullback (jK R)).obj G) (spMap ga) κW :=
    (isGrpPullback_pullback G (jK R)).cancel
      (((isGrpPullback_pullback GW (jK W)).comp hβ).congr hsq hκf.symm) w
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (jK W)).obj GW) := Functor.isCommMonObj_obj
  have : IsMonHom UW.gen.hom := UW.gen_hom
  have : IsMonHom gen.hom := hgen
  have : IsMonHom UW.gen.symm.hom := show IsMonHom UW.gen.inv by infer_instance
  have hu : IsGrpPullback AW.A ((Over.pullback (jK W)).obj GW) (𝟙 _) UW.gen.inv.left :=
    isGrpPullback_of_iso UW.gen.symm
  have hg : IsGrpPullback ((Over.pullback (jK R)).obj G) A.A (𝟙 _) gen.hom.left := isGrpPullback_of_iso gen
  have hα : IsGrpPullback AW.A A.A (spMap ga) (UW.gen.inv.left ≫ κW ≫ gen.hom.left) :=
    (hu.comp (hκ.comp hg)).congr (by simp) rfl
  obtain ⟨u₂, squ, Hu⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ hu
  obtain ⟨κ₂, sqκ, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ hκ
  obtain ⟨g₂, sqg, Hg⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ hg
  obtain ⟨fW₂, sqfW, HfW⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ (isGrpPullback_pullback GW (jK W))
  obtain ⟨fR₂, sqfR, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ (isGrpPullback_pullback G (jK R))
  have hLA : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have hLG : (UW.LG.L.pull (pullback.fst GW.hom (jK W))).IsLB := pull_isLB UW.LG.isLB _
  have hAg : (A.L.pull gen.hom.left).IsLB := pull_isLB A.isLB _

  have Z : LBIso (abelian₂ ((Over.pullback (jK R)).obj G) (A.L.pull gen.hom.left)) ((abelian₂ A.A A.L).pull g₂) := by
    have h := Hg A.L (A.L.pull gen.hom.left) _ (abelian₂ A.A A.L) (𝟙 _) A.isLB hAg hLA
      (PolBaseChange.lbIso_refl hAg)
      (LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) (PolBaseChange.lbIso_refl hLA))
    rwa [Category.comp_id] at h
  have Y : LBIso (PP.pull fR₂) ((abelian₂ A.A A.L).pull g₂) :=
    LBIso.trans (pull_isLB hExt.1 _) (DVR.linComb_isLB _ hAg _ _) (pull_isLB hLA _) (hExt.2 fR₂ sqfR).symm Z
  have e : fW₂ ≫ βW₂ = κ₂ ≫ fR₂ := by
    apply pullback.hom_ext
    · show (fW₂ ≫ βW₂) ≫ (fst G G).left = (κ₂ ≫ fR₂) ≫ (fst G G).left
      simp only [Category.assoc, hsqW.1, sqfR.1]
      rw [← Category.assoc fW₂, sqfW.1, reassoc_of% sqκ.1, hκf, Category.assoc]
    · show (fW₂ ≫ βW₂) ≫ (snd G G).left = (κ₂ ≫ fR₂) ≫ (snd G G).left
      simp only [Category.assoc, hsqW.2, sqfR.2]
      rw [← Category.assoc fW₂, sqfW.2, reassoc_of% sqκ.2, hκf, Category.assoc]
  have B1 : LBIso (abelian₂ ((Over.pullback (jK W)).obj GW) (UW.LG.L.pull (pullback.fst GW.hom (jK W))))
      (PP.pull (κ₂ ≫ fR₂)) := by
    have h := HfW UW.LG.L (UW.LG.L.pull (pullback.fst GW.hom (jK W))) _ PP βW₂ UW.LG.isLB hLG hExt.1
      (PolBaseChange.lbIso_refl hLG) hPP
    rwa [e] at h
  have B3 : LBIso (PP.pull (κ₂ ≫ fR₂)) ((abelian₂ A.A A.L).pull (κ₂ ≫ g₂)) :=
    LBIso.chartPull (chartPullSame PP _ (fun _ => fR₂) _ κ₂ fun _ => rfl)
      (chartPullSame (abelian₂ A.A A.L) _ (fun _ => g₂) _ κ₂ fun _ => rfl) Y
  have hLamW : LBIso (abelian₂ ((Over.pullback (jK W)).obj GW) (UW.LG.L.pull (pullback.fst GW.hom (jK W))))
      ((abelian₂ A.A A.L).pull (κ₂ ≫ g₂)) :=
    LBIso.trans (DVR.linComb_isLB _ hLG _ _) (pull_isLB hExt.1 _) (pull_isLB hLA _) B1 B3

  have hN : LBIso AW.L ((UW.LG.L.pull (pullback.fst GW.hom (jK W))).pull UW.gen.inv.left) := by
    have hext : LBIso (AW.L.pull UW.gen.hom.left) (UW.LG.L.pull (pullback.fst GW.hom (jK W))) := UW.ext
    have h1 : LBIso (AW.L.pull (𝟙 _)) ((UW.LG.L.pull (pullback.fst GW.hom (jK W))).pull UW.gen.inv.left) :=
      LBIso.chartPull (chartPullSame AW.L _ (fun _ => UW.gen.hom.left) _ UW.gen.inv.left fun _ => by
          rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left])
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) hext
    have h0 : LBIso AW.L (AW.L.pull (𝟙 _)) :=
      LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) (PolBaseChange.lbIso_refl AW.isLB)
    exact LBIso.trans AW.isLB (pull_isLB AW.isLB _) (pull_isLB hLG _) h0 h1
  refine ⟨ga, UW.gen.inv.left ≫ κW ≫ gen.hom.left, u₂ ≫ κ₂ ≫ g₂, hga, hα, ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [Category.assoc, sqg.1, reassoc_of% sqκ.1, reassoc_of% squ.1]
  · simp only [Category.assoc, sqg.2, reassoc_of% sqκ.2, reassoc_of% squ.2]
  · exact Hu _ AW.L _ (abelian₂ A.A A.L) (κ₂ ≫ g₂) hLG AW.isLB hLA hN hLamW
  · rw [Category.assoc, Category.assoc, ← Category.assoc gen.hom.left, ← Over.comp_left, Iso.hom_inv_id,
      Over.id_left, Category.id_comp, hκf]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedOfIsPullbackSurjectiveLft
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem geometricallyConnected_of_isPullback_of_surjective :
    ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → Surjective π →
    ∀ (G' : Over S) (G : Over (Sp R)) (β : G'.left ⟶ G.left), IsPullback β G'.hom G.hom π →
    GeometricallyConnected G'.hom → GeometricallyConnected G.hom := by
  intro R _ S π hlft hsurj G' G β hpb hG'
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  let jK : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  obtain ⟨t, ht⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective (Ω := AlgebraicClosure K) π (jK ≫ y)
  have hct : ConnectedSpace ↥(pullback G'.hom t) :=
    pullback_of_geometrically hG'.geometrically_connectedSpace _ t
  have hP : IsPullback (pullback.fst G'.hom t ≫ β) (pullback.snd G'.hom t) G.hom (t ≫ π) :=
    (IsPullback.of_hasPullback G'.hom t).paste_horiz hpb
  rw [← ht] at hP
  have hc' : ConnectedSpace ↥(pullback G.hom (jK ≫ y)) :=
    hP.isoPullback.hom.homeomorph.connectedSpace_iff.mp hct
  have hjK : Surjective jK := ⟨fun z ↦ by
    obtain ⟨w⟩ : Nonempty ↥(Spec (.of (AlgebraicClosure K))) := inferInstance
    exact ⟨w, Subsingleton.elim _ _⟩⟩
  have hc'' : ConnectedSpace ↥(pullback (pullback.snd G.hom y) jK) :=
    (pullbackLeftPullbackSndIso G.hom y jK).hom.homeomorph.connectedSpace_iff.mpr hc'
  exact (pullback.fst (pullback.snd G.hom y) jK).surjective.connectedSpace
    (pullback.fst (pullback.snd G.hom y) jK).continuous

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLocalRingEssFiniteTypeIntStatement
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelLocalRing_essFiniteType_int : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (x : M.Z), Algebra.EssFiniteType ℤ (M.O x) := by
  first | exact @GlobalTheory.Izumi.essFiniteType_int_O | exact GlobalTheory.Izumi.essFiniteType_int_O | (intros; apply GlobalTheory.Izumi.essFiniteType_int_O <;> assumption)
end

