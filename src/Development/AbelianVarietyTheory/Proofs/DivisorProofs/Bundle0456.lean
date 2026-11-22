import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0441
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationOfData
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechDR.FormExt

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def extMap {T T' : C} (φ : T ⟶ T') :
    TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R] →ₐ[R] TrivSqZeroExt (F.obj T') Ω[F.obj T'⁄R] :=
  { semiDiag (semiHom_mp F φ) with
    commutes' := fun r ↦ by
      change semiDiag (semiHom_mp F φ) (algebraMap R _ r) = algebraMap R _ r
      ext
      · rw [fst_semiDiag]; simp [TrivSqZeroExt.algebraMap_eq_inl', (semiHom_mp F φ).map_algebraMap]
      · rw [snd_semiDiag]; simp [TrivSqZeroExt.algebraMap_eq_inl'] }

theorem fst_extMap {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R]) :
    (extMap F φ c).fst = mp F φ c.fst := fst_semiDiag _ c

theorem snd_extMap {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R]) :
    (extMap F φ c).snd = p1 F φ c.snd := snd_semiDiag _ c

def omExt : C ⥤ CommAlgCat.{0} R where
  obj T := CommAlgCat.of R (TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R])
  map φ := CommAlgCat.ofHom (extMap F φ)
  map_id T := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext
    ((fst_extMap F _ c).trans (mp_id F T _)) ((snd_extMap F _ c).trans (oneFormsMapOfFunctorMorphism_id F _)))
  map_comp φ ψ := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext
    ((fst_extMap F _ c).trans ((mp_comp F φ ψ _).trans (by
      change _ = ((extMap F ψ) (extMap F φ c)).fst
      rw [fst_extMap, fst_extMap])))
    ((snd_extMap F _ c).trans ((oneFormsMapOfFunctorMorphism_comp F φ ψ _).trans (by
      change _ = ((extMap F ψ) (extMap F φ c)).snd
      rw [snd_extMap, snd_extMap]))))

end GlobalTheory.CechDR.FormExt

namespace GlobalTheory.CechDR.FormExt

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem isLocalization_of_data {T T' : C} (l : T ⟶ T') (b : F.obj T) (h1 : IsUnit (mp F l b))
    (h2 : ∀ y : F.obj T', ∃ (n : ℕ) (x : F.obj T), y * mp F l b ^ n = mp F l x)
    (h3 : ∀ x : F.obj T, mp F l x = 0 → ∃ n : ℕ, b ^ n * x = 0) :
    letI : Algebra (F.obj T) (F.obj T') := (mp F l : F.obj T →+* F.obj T').toAlgebra
    IsLocalization.Away b (F.obj T') := by
  letI : Algebra (F.obj T) (F.obj T') := (mp F l : F.obj T →+* F.obj T').toAlgebra
  refine ⟨?_, fun z ↦ ?_, fun {x y} e ↦ ?_⟩
  · rintro ⟨_, n, rfl⟩
    change IsUnit (mp F l (b ^ n))
    rw [map_pow]; exact h1.pow n
  · obtain ⟨n, x, e⟩ := h2 z
    refine ⟨(x, ⟨b ^ n, n, rfl⟩), ?_⟩
    change z * mp F l (b ^ n) = mp F l x
    rw [map_pow]; exact e
  · obtain ⟨n, hn⟩ := h3 (x - y) (by rw [map_sub]; exact sub_eq_zero.2 e)
    exact ⟨⟨b ^ n, n, rfl⟩, sub_eq_zero.1 (by rw [← mul_sub]; exact hn)⟩

theorem isUnit_mp_omExt_iff {T S : C} (u : T ⟶ S) (c : (omExt F).obj T) :
    IsUnit (mp (omExt F) u c) ↔ IsUnit (mp F u c.fst) :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst.trans (iff_of_eq (congrArg IsUnit (fst_extMap F u c)))

theorem surj_key {T T' : C} (l : T ⟶ T') (c : TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R])
    (y : TrivSqZeroExt (F.obj T') Ω[F.obj T'⁄R]) (a₀ : F.obj T) (η₀ : Ω[F.obj T⁄R]) (k₁ k₂ : ℕ)
    (ha : y.fst * mp F l (c.fst ^ k₁) = mp F l a₀) (hη : mp F l (c.fst ^ k₂) • y.snd = p1 F l η₀) :
    y * extMap F l c ^ (k₁ + k₂ + 1) = extMap F l (TrivSqZeroExt.inl (a₀ * c.fst ^ (k₂ + 1)) +
      TrivSqZeroExt.inr ((k₁ + k₂ + 1) • (a₀ * c.fst ^ k₂) • c.snd + c.fst ^ (k₁ + 1) • η₀)) := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, fst_extMap, fst_extMap]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, map_mul,
      map_pow] at ha ⊢
    linear_combination (mp F l c.fst) ^ (k₂ + 1) * ha
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, snd_extMap, fst_extMap, snd_extMap]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, map_add, map_nsmul,
      oneFormsMapOfFunctorMorphism_smul, map_mul, map_pow, op_smul_eq_smul, Nat.pred_succ] at ha hη ⊢
    rw [← hη, ← ha]
    module

theorem ker_key {T : C} (c x : TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R]) (m₁ m₂ : ℕ)
    (h₁ : c.fst ^ m₁ * x.fst = 0) (h₂ : c.fst ^ m₂ • x.snd = 0) : c ^ (m₁ + m₂ + 1) * x = 0 := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_zero]
    linear_combination c.fst ^ (m₂ + 1) * h₁
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_zero, op_smul_eq_smul, Nat.pred_succ]
    linear_combination (norm := module) c.fst ^ (m₁ + 1) • h₂ + h₁ • ((m₁ + m₂ + 1) • c.fst ^ m₂ • c.snd)

theorem hasLoc_omExt (H : Desc.HasLoc F) : Desc.HasLoc (omExt F) := by
  intro T c
  obtain ⟨T', l, h1, h2, h3, h4⟩ := H T c.fst
  letI : Algebra (F.obj T) (F.obj T') := (mp F l : F.obj T →+* F.obj T').toAlgebra
  haveI : IsScalarTower R (F.obj T) (F.obj T') :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((mp F l).commutes r).symm
  haveI := isLocalization_of_data F l c.fst h1 h2 h3
  have hp : ∀ ω, p1 F l ω = KaehlerDifferential.map R R (F.obj T) (F.obj T') ω :=
    SemiHom.oneFormMap_eq_kaehlerDifferential_map _ fun _ ↦ rfl
  have hs : ∀ (a : F.obj T) (η : Ω[F.obj T'⁄R]), a • η = mp F l a • η := fun a η ↦
    (algebraMap_smul (F.obj T') a η).symm
  refine ⟨T', l, (isUnit_mp_omExt_iff F l c).2 h1, fun y ↦ ?_, fun x hx ↦ ?_,
    fun S u hu ↦ h4 S u ((isUnit_mp_omExt_iff F u c).1 hu)⟩
  · obtain ⟨⟨a₀, _, k₁, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers c.fst) y.fst
    obtain ⟨⟨η₀, _, k₂, rfl⟩, hη⟩ := IsLocalizedModule.surj (Submonoid.powers c.fst)
      (KaehlerDifferential.map R R (F.obj T) (F.obj T')) y.snd
    change y.fst * mp F l (c.fst ^ k₁) = mp F l a₀ at ha
    change (c.fst ^ k₂) • y.snd = _ at hη
    rw [hs, ← hp] at hη
    refine ⟨k₁ + k₂ + 1, TrivSqZeroExt.inl (a₀ * c.fst ^ (k₂ + 1)) +
      TrivSqZeroExt.inr ((k₁ + k₂ + 1) • (a₀ * c.fst ^ k₂) • c.snd + c.fst ^ (k₁ + 1) • η₀), ?_⟩
    exact surj_key F l c y a₀ η₀ k₁ k₂ ha hη
  · have e1 : mp F l x.fst = 0 := (fst_extMap F l x).symm.trans (congrArg TrivSqZeroExt.fst hx)
    have e2 : KaehlerDifferential.map R R (F.obj T) (F.obj T') x.snd = 0 :=
      (hp _).symm.trans ((snd_extMap F l x).symm.trans (congrArg TrivSqZeroExt.snd hx))
    obtain ⟨m₁, h₁⟩ := h3 _ e1
    obtain ⟨⟨_, m₂, rfl⟩, h₂⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers c.fst)
      (f := KaehlerDifferential.map R R (F.obj T) (F.obj T')) (x₁ := x.snd) (x₂ := 0)
      (by rw [e2, map_zero])
    rw [smul_zero, Submonoid.smul_def] at h₂
    exact ⟨m₁ + m₂ + 1, ker_key F c x m₁ m₂ h₁ h₂⟩

end GlobalTheory.CechDR.FormExt

namespace GlobalTheory.CechDR.FormExt

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

theorem span_inl_eq_top {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    {S : C} {n : ℕ} {b : Fin n → F.obj S} (hb : Ideal.span (Set.range b) = ⊤) :
    Ideal.span (Set.range fun i ↦ (TrivSqZeroExt.inl (b i) : (omExt F).obj S)) = ⊤ := by
  have := congrArg (Ideal.map (TrivSqZeroExt.inlHom (F.obj S) Ω[F.obj S⁄R])) hb
  rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  exact this

theorem glue_one_forms : ∀ {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R') {C' : Type} [Category.{0} C'], [Quiver.IsThin C'] → ∀ (G : C' ⥤ AffOp X'), (∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S), IsUnit (mp (OAff s') u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : AffOp X'), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (OAff s').obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'), IsUnit (mp (OAff s') u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → (∀ (T : AffOp X') (s : ∀ t, (T ⟶ G.obj t) → Ω[(OAff s').obj (G.obj t)⁄R']), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = p1 (OAff s') (G.map a) (s t u)) → ∃ ω : Ω[(OAff s').obj T⁄R'], ∀ t u, p1 (OAff s') u ω = s t u) := by
  intro R' _ X' s' C' _ _ G hcov hdir T s hs
  have unit : ∀ {S S' : AffOp X'} (u : S ⟶ S') (b : (OAff s').obj S),
      IsUnit (mp (omExt (OAff s')) u (TrivSqZeroExt.inl b)) → IsUnit (mp (OAff s') u b) :=
    fun u b h ↦ ((isUnit_mp_omExt_iff (OAff s') u _).1 h)
  obtain ⟨x, hx⟩ := GlobalTheory.CatCoh.Desc.glue_comma_of_basis (omExt (OAff s')) G (hasLoc_omExt (OAff s') (hasLoc_OAff s'))
    (fun T ↦ by
      obtain ⟨n, b, hb, h⟩ := hcov T
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inl_eq_top (OAff s') hb,
        fun i S u hu ↦ h i S u (unit u _ hu)⟩)
    (fun t₁ t₂ S a₁ a₂ ↦ by
      obtain ⟨n, b, hb, h⟩ := hdir t₁ t₂ S a₁ a₂
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inl_eq_top (OAff s') hb,
        fun i S' u hu ↦ h i S' u (unit u _ hu)⟩)
    T (fun t u ↦ TrivSqZeroExt.inr (s t u)) (fun t t' u a ↦ by
      apply TrivSqZeroExt.ext
      · exact (TrivSqZeroExt.fst_inr _ _).trans (((fst_extMap (OAff s') (G.map a) _).trans
          (by rw [TrivSqZeroExt.fst_inr, map_zero])).symm)
      · exact ((TrivSqZeroExt.snd_inr _ _).trans (hs t t' u a)).trans
          ((snd_extMap (OAff s') (G.map a) _).trans (by rw [TrivSqZeroExt.snd_inr])).symm)
  exact ⟨x.snd, fun t u ↦ (snd_extMap (OAff s') u x).symm.trans
    ((congrArg TrivSqZeroExt.snd (hx t u)).trans (TrivSqZeroExt.snd_inr _ _))⟩

end GlobalTheory.CechDR.FormExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSheafProjBundleCochainPresheafEtale
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.CotSheaf

open CupSpec

variable {R : Type} [CommRing R] {q N : ℕ} {I : Cx R} {n : ℤ}

def fstHom {U W : Scheme.{0}} {E : Spc} {p : ℕ} (y : Sx (sch.obj U ⨯ E) p W) : W ⟶ U := y.map prod.fst

theorem fstHom_pair {U W : Scheme.{0}} {E : Spc} {p : ℕ} (v : W ⟶ U) (b : Sx E p W) :
    fstHom (sxPair (schSx v p) b) = v := sxPair_fst _ _

theorem fstHom_res {U W W' : Scheme.{0}} {E : Spc} {p : ℕ} (y : Sx (sch.obj U ⨯ E) p W) (w : W' ⟶ W) :
    fstHom (y.res w) = w ≫ fstHom y := by
  rw [fstHom, sxMap_res]; rfl

theorem fstHom_map {U Y W : Scheme.{0}} {E : Spc} {p : ℕ} (y : Sx (sch.obj Y ⨯ E) p W) (g : Y ⟶ U) :
    fstHom (y.map (prod.map (sch.map g) (𝟙 E))) = fstHom y ≫ g := by
  rw [fstHom, ← sxMap_comp, prod.map_fst, sxMap_comp]; rfl

theorem snd_map {U Y W : Scheme.{0}} {E : Spc} {p : ℕ} (y : Sx (sch.obj Y ⨯ E) p W) (g : Y ⟶ U) :
    (y.map (prod.map (sch.map g) (𝟙 E))).map prod.snd = y.map prod.snd := by
  rw [← sxMap_comp, prod.map_snd, Category.comp_id]

theorem sx_res_res {E : Spc} {p : ℕ} {U V W : Scheme.{0}} (x : Sx E p U) (f : V ⟶ U) (g : W ⟶ V) :
    (x.res f).res g = x.res (g ≫ f) := by
  change _ = (E.obj (op (SimplexCategory.mk p))).map (g ≫ f).op x
  rw [op_comp, FunctorToTypes.map_comp_apply]; rfl

theorem ev_res_pair {U W W' : Scheme.{0}} (α : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (y : Sx (sch.obj U ⨯ fibQ q N) p W) (w : W' ⟶ W) :
    Sec.res w (ev α p s h W y) =
      ev (I := I) (E := sch.obj W' ⨯ fibQ q N) (((cotPre R q N I n).map (w ≫ fstHom y).op).hom α) p s h W'
        (sxPair (schSx (𝟙 W') p) ((y.map prod.snd).res w)) := by
  rw [ev_res, cotPre_ev]
  congr 1
  apply sx_prod_ext
  · rw [sxPair_map, sxPair_fst, sxMap_res, schSx_map, Category.id_comp]
    rfl
  · rw [sxMap_res, sxPair_map, sxPair_snd]
    rfl

end GlobalTheory.EtC.CotSheaf

namespace GlobalTheory.EtC

open CupSpec CotSheaf

theorem cotPre_isSheaf (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (n : ℤ) :
    Presheaf.IsSheaf Scheme.etaleTopology.{0} (cotPre R q N I n) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R))), isSheaf_iff_isSheaf_of_type]
  have hI : ∀ s : ℤ, Presieve.IsSheaf Scheme.etaleTopology.{0} ((I.X s).obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    fun s => (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 (I.X s).cond)
  have sep : ∀ (s : ℤ) (W : Scheme.{0}) (T : Sieve W), T ∈ Scheme.etaleTopology.{0} W → ∀ t t' : Sec (I.X s) W,
      (∀ (W' : Scheme.{0}) (w : W' ⟶ W), T w → Sec.res w t = Sec.res w t') → t = t' :=
    fun s W T hT t t' ht => (hI s T hT).isSeparatedFor.ext fun _ w hw => ht _ w hw
  intro U S hS c hc
  rw [Presieve.compatible_iff_sieveCompatible] at hc
  have hC : ∀ {Y Z : Scheme.{0}} (f : Y ⟶ U) (g : Z ⟶ Y) (hf : S f),
      ((cotPre R q N I n).map g.op).hom (c f hf) = c (g ≫ f) (S.downward_closed hf g) := fun f g hf => (hc f g hf).symm

  have hcong : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {W : Scheme.{0}} (g g' : W ⟶ U) (hg : S g) (hg' : S g')
      (x x' : Sx (fibQ q N) p W), g = g' → x = x' →
      ev (I := I) (E := sch.obj W ⨯ fibQ q N) (c g hg) p s h W (sxPair (schSx (𝟙 W) p) x) =
        ev (I := I) (E := sch.obj W ⨯ fibQ q N) (c g' hg') p s h W (sxPair (schSx (𝟙 W) p) x') := by
    rintro p s h W g _ hg hg' x _ rfl rfl; rfl

  have hL : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {W W' : Scheme.{0}} (g : W ⟶ U) (hg : S g)
      (x : Sx (fibQ q N) p W) (t : W' ⟶ W),
      Sec.res t (ev (I := I) (E := sch.obj W ⨯ fibQ q N) (c g hg) p s h W (sxPair (schSx (𝟙 W) p) x)) =
        ev (I := I) (E := sch.obj W' ⨯ fibQ q N) (c (t ≫ g) (S.downward_closed hg t)) p s h W'
          (sxPair (schSx (𝟙 W') p) (x.res t)) := by
    intro p s h W W' g hg x t
    refine (ev_res_pair (c g hg) p s h _ t).trans ?_
    rw [fstHom_pair, Category.comp_id, hC, sxPair_snd]

  have hAm : ∀ γ : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n,
      (∀ {Y : Scheme.{0}} (g : Y ⟶ U) (hg : S g), ((cotPre R q N I n).map g.op).hom γ = c g hg) →
      ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {W W' : Scheme.{0}} (y : Sx (sch.obj U ⨯ fibQ q N) p W) (w : W' ⟶ W)
        (hw : S (w ≫ fstHom y)),
      Sec.res w (ev γ p s h W y) = ev (I := I) (E := sch.obj W' ⨯ fibQ q N) (c (w ≫ fstHom y) hw) p s h W'
          (sxPair (schSx (𝟙 W') p) ((y.map prod.snd).res w)) := by
    intro γ hγ p s h W W' y w hw
    refine (ev_res_pair γ p s h y w).trans ?_
    rw [hγ]

  have key : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (W : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) p W),
      ∃ t : Sec (I.X s) W, ∀ (W' : Scheme.{0}) (w : W' ⟶ W) (hw : S (w ≫ fstHom y)),
        Sec.res w t = ev (I := I) (E := sch.obj W' ⨯ fibQ q N) (c (w ≫ fstHom y) hw) p s h W'
          (sxPair (schSx (𝟙 W') p) ((y.map prod.snd).res w)) := by
    intro p s h W y
    let fam : Presieve.FamilyOfElements ((I.X s).obj ⋙ forget (ModuleCat.{1} (ULift.{1} R)))
        (S.pullback (fstHom y)).arrows := fun W' w hw =>
      ev (I := I) (E := sch.obj W' ⨯ fibQ q N) (c (w ≫ fstHom y) hw) p s h W'
          (sxPair (schSx (𝟙 W') p) ((y.map prod.snd).res w))
    have hfam : fam.Compatible := by
      rw [Presieve.compatible_iff_sieveCompatible]
      intro Y Z f g hf
      refine Eq.trans ?_ (hL p s h (f ≫ fstHom y) hf _ g).symm
      exact hcong _ _ _ _ _ _ _ _ _ (Category.assoc _ _ _) (sx_res_res _ _ _).symm
    obtain ⟨t, ht, -⟩ := hI s _ (Scheme.etaleTopology.{0}.pullback_stable (fstHom y) hS) fam hfam
    exact ⟨t, fun W' w hw => ht w hw⟩
  choose a ha using key
  have hnat : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (V W : Scheme.{0}) (g : V ⟶ W)
      (y : Sx (sch.obj U ⨯ fibQ q N) p W), Sec.res g (a p s h W y) = a p s h V (y.res g) := by
    intro p s h V W g y
    apply sep s V _ (Scheme.etaleTopology.{0}.pullback_stable (fstHom (y.res g)) hS)
    intro W' w hw
    have hw' : S ((w ≫ g) ≫ fstHom y) := by
      rw [fstHom_res] at hw; simpa [Category.assoc] using hw
    rw [secRes_res, ha p s h W y W' (w ≫ g) hw', ha p s h V (y.res g) W' w hw]
    refine hcong _ _ _ _ _ _ _ _ _ ?_ ?_
    · rw [fstHom_res, Category.assoc]
    · rw [sxMap_res, sx_res_res]
  obtain ⟨α, hα⟩ := ev_exists (R := R) (E := sch.obj U ⨯ fibQ q N) (I := I) (n := n) a hnat
  have hαam : ∀ {Y : Scheme.{0}} (g : Y ⟶ U) (hg : S g), ((cotPre R q N I n).map g.op).hom α = c g hg := by
    intro Y g hg
    apply ev_ext
    intro p s h W y
    rw [cotPre_ev, hα]
    apply sep s W _ (Scheme.etaleTopology.{0}.pullback_stable (fstHom (y.map (prod.map (sch.map g) (𝟙 _)))) hS)
    intro W' w hw
    rw [ha p s h W _ W' w hw]
    refine Eq.trans ?_ (ev_res_pair (c g hg) p s h y w).symm
    rw [hC, snd_map]
    refine hcong _ _ _ _ _ _ _ _ _ ?_ rfl
    rw [fstHom_map, Category.assoc]
  refine ⟨α, fun Y g hg => hαam g hg, fun β hβ => ?_⟩
  apply ev_ext
  intro p s h W y
  apply sep s W _ (Scheme.etaleTopology.{0}.pullback_stable (fstHom y) hS)
  intro W' w hw
  rw [hAm β (fun g hg => hβ g hg) p s h y w hw, hAm α (fun g hg => hαam g hg) p s h y w hw]

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitTwoMulRhoSubTr
section
noncomputable section

namespace GlobalTheory.UPel.HT.LieLin.RankIdeal

open NumberField

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

theorem sq_two_mul_rho_sub_tr (b : Base D R) :
    (2 * b.ρ - (D.tr : R)) ^ 2 = ((D.tr ^ 2 - 4 * D.nm : ℤ) : R) := by
  have h := b.ρ_root
  push_cast
  linear_combination 4 * h

theorem isUnit_two_mul_rho_sub_tr (b : Base D R) : IsUnit (2 * b.ρ - (D.tr : R)) := by
  have hp : (p).Prime := Fact.out
  set d : ℤ := D.tr ^ 2 - 4 * D.nm with hd
  have hc : d.natAbs.Coprime p := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => D.disc_p ?_)
    exact Int.natCast_dvd.2 h
  have hu := b.unit _ hc
  have hdu : IsUnit ((d : ℤ) : R) := by
    rcases Int.natAbs_eq d with h | h
    · rw [h, Int.cast_natCast]; exact hu
    · rw [h, Int.cast_neg, Int.cast_natCast]; exact hu.neg
  rw [← sq_two_mul_rho_sub_tr] at hdu
  exact (isUnit_pow_iff two_ne_zero).1 hdu

def uInv (b : Base D R) : R := ↑(isUnit_two_mul_rho_sub_tr b).unit⁻¹

theorem uInv_mul (b : Base D R) : uInv b * (2 * b.ρ - (D.tr : R)) = 1 :=
  (isUnit_two_mul_rho_sub_tr b).val_inv_mul

def comaxC (b : Base D R) (i j : Fin D.a) : 𝓞 D.F →₀ R :=
  if h : i ≠ j then
    Classical.choose (Finsupp.mem_span_range_iff_exists_finsupp.1
      ((b.comax i j h).symm ▸ Submodule.mem_top :
        (1 : R) ∈ Ideal.span (Set.range fun x => b.t i x - b.t j x)))
  else 0

theorem comaxC_spec (b : Base D R) {i j : Fin D.a} (h : i ≠ j) :
    ((comaxC b i j).sum fun x r => r * (b.t i x - b.t j x)) = 1 := by
  unfold comaxC
  rw [dif_pos h]
  exact Classical.choose_spec (Finsupp.mem_span_range_iff_exists_finsupp.1
      ((b.comax i j h).symm ▸ Submodule.mem_top :
        (1 : R) ∈ Ideal.span (Set.range fun x => b.t i x - b.t j x)))

variable {B : Type} [CommRing B] {n : ℕ}

def alphaMat (b : Base D R) (βB : R →+* B) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (i j : Fin D.a) :
    Matrix (Fin n) (Fin n) B :=
  (comaxC b i j).sum fun x r =>
    algebraMap B (Matrix (Fin n) (Fin n) B) (βB r) * (M x - algebraMap B (Matrix (Fin n) (Fin n) B) (βB (b.t j x)))

def projMat (b : Base D R) (βB : R →+* B) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (i : Fin D.a) :
    Matrix (Fin n) (Fin n) B :=
  (List.ofFn fun j => if j = i then 1 else alphaMat b βB M i j).prod *
    (algebraMap B (Matrix (Fin n) (Fin n) B) (βB (uInv b)) *
      (M D.ω - algebraMap B (Matrix (Fin n) (Fin n) B) (βB ((D.tr : R) - b.ρ))))

end GlobalTheory.UPel.HT.LieLin.RankIdeal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedMapsAgreeCohomologyTwoInstances
section
set_option autoImplicit false

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh.JoinedTwoProof

universe a b

theorem main : JoinedTwo.{a, b} := by
  intro C _ C' _ K K' m m' θ j c
  obtain ⟨⟨⟨z, w, η⟩, hc⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
  obtain ⟨h1, h2, h3, -⟩ := hc
  dsimp only at h1 h2 h3
  refine QuotientAddGroup.eq.2 ⟨(fun T T' φ ↦ m'.a0 T' (z _ _ _ (θ.app T) (m'.G.map φ) - z _ _ _ (m.G.map φ) (θ.app T')),
    fun T ↦ m'.a1 T (w _ _ (θ.app T))), ?_⟩
  refine Prod.ext (funext fun T ↦ funext fun T' ↦ funext fun T'' ↦ funext fun φ ↦ funext fun ψ ↦ ?_)
    (Prod.ext (funext fun T ↦ funext fun T' ↦ funext fun φ ↦ ?_) (funext fun T ↦ ?_))
  · change K'.M0.map ψ (m'.a0 T' (z _ _ _ (θ.app T) (m'.G.map φ) - z _ _ _ (m.G.map φ) (θ.app T'))) -
        m'.a0 T'' (z _ _ _ (θ.app T) (m'.G.map (φ ≫ ψ)) - z _ _ _ (m.G.map (φ ≫ ψ)) (θ.app T'')) +
        m'.a0 T'' (z _ _ _ (θ.app T') (m'.G.map ψ) - z _ _ _ (m.G.map ψ) (θ.app T'')) =
      -m.a0 T'' (z _ _ _ (m.G.map φ) (m.G.map ψ)) + m'.a0 T'' (z _ _ _ (m'.G.map φ) (m'.G.map ψ))
    have e1 := congrArg (m'.a0 T'') (h1 _ _ _ _ (m.G.map φ) (m.G.map ψ) (θ.app T''))
    have e2 := congrArg (m'.a0 T'') (h1 _ _ _ _ (m.G.map φ) (θ.app T') (m'.G.map ψ))
    have e3 := congrArg (m'.a0 T'') (h1 _ _ _ _ (θ.app T) (m'.G.map φ) (m'.G.map ψ))
    rw [θ.naturality ψ] at e1
    rw [θ.naturality φ] at e2
    rw [← m.G.map_comp] at e1
    rw [← m'.G.map_comp] at e3
    simp only [map_add, j.e0, m'.compDegreeZero_natural] at e1 e2 e3
    simp only [map_sub, m'.compDegreeZero_natural]
    linear_combination (norm := abel1) e1 - e2 + e3
  · change m'.a1 T' (w _ _ (θ.app T')) - K'.M1.map φ (m'.a1 T (w _ _ (θ.app T))) -
        K'.d0 T' (m'.a0 T' (z _ _ _ (θ.app T) (m'.G.map φ) - z _ _ _ (m.G.map φ) (θ.app T'))) =
      -m.a1 T' (w _ _ (m.G.map φ)) + m'.a1 T' (w _ _ (m'.G.map φ))
    have e := congrArg (m'.a1 T') ((h2 _ _ _ (m.G.map φ) (θ.app T')).symm.trans
      ((congrArg (w _ _) (θ.naturality φ)).trans (h2 _ _ _ (θ.app T) (m'.G.map φ))))
    simp only [map_add, j.e1, m'.compDegreeOne_natural, m'.comp_commutes_diffZero] at e
    simp only [map_sub]
    linear_combination (norm := abel1) e
  · change K'.d1 T (m'.a1 T (w _ _ (θ.app T))) = -m.a2 T (η _) + m'.a2 T (η _)
    rw [h3 _ _ (θ.app T), map_add, j.e2, m'.comp_commutes_diffOne]; abel

theorem joinedTwo_inst : JoinedTwo.{1,1} ∧ JoinedTwo.{1,0} ∧ JoinedTwo.{0,0} := ⟨main, main, main⟩

end GlobalTheory.CxCoh.JoinedTwoProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeHeightSpanRangeXMvPolynomial
section
open IsLocalRing

namespace GlobalTheory

theorem span_range_X_eq_ker_constantCoeff (k : Type) [Field k] (n : ℕ) :
    Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k)))
      = RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) k →+* k) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker]
  · intro p hp
    rw [RingHom.mem_ker] at hp
    have key : ∀ q : MvPolynomial (Fin n) k, q - MvPolynomial.C (MvPolynomial.constantCoeff q) ∈
        Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k))) := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq =>
        have := Ideal.add_mem _ hp hq
        convert this using 1
        simp only [map_add]; ring
      | mul_X p i _ =>
        simp only [map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero, sub_zero]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    simpa [hp] using key p

theorem le_height_span_range_X_mvPolynomial : ∀ (k : Type) [Field k] (n : ℕ), ((n : ℕ∞)) ≤ (Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k)))).height := by
  intro k _ n
  rw [span_range_X_eq_ker_constantCoeff]
  haveI : (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) k →+* k)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨MvPolynomial.C a, by simp⟩)
  have h := ReciprocityTheory.CA.height_maximal_mvPolynomial_field k n (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) k →+* k))
  exact h.2.ge

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelwiseEquivalenceIsEquivalenceStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelwiseEquivalence_isEquivalence : GlobalTheory.EtC.A3 := by
  first | (exact @GlobalTheory.EtC.levelwise_eqv) | (exact GlobalTheory.EtC.levelwise_eqv) | (intros; apply GlobalTheory.EtC.levelwise_eqv  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapTwoSidedMulHaarMatrixQuadraticExtStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_twoSided_mul_haar_matrix_quadraticExt : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (u : GL α E) (a : GL ν E), μ.map (fun x => (u : Matrix α α E) * x * (a : Matrix ν ν E)) = (distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det u)) ^ Fintype.card ν * distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det a)) ^ Fintype.card α)⁻¹ • μ := by
  first | exact @GlobalTheory.KSp.map_twoSided_haar | exact GlobalTheory.KSp.map_twoSided_haar | (intros; apply GlobalTheory.KSp.map_twoSided_haar <;> assumption)
end

