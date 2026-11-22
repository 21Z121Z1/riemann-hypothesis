import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open GlobalTheory.Cartier

namespace GlobalTheory.LogDR

section Algebra

abbrev abelian₂ (K : Type) [Field K] : Type := ExteriorAlgebra K Ω[K⁄ℤ]

variable {K : Type} [Field K]

abbrev dK (f : K) : Ω[K⁄ℤ] := KaehlerDifferential.D ℤ K f

variable (K) in

def extD : abelian₂ K →+ abelian₂ K := (CechDR.dDR ℤ K).toAddMonoidHom

theorem extD_apply (η : abelian₂ K) : extD K η = CechDR.dDR ℤ K η := rfl

def dlog (g : Kˣ) : Ω[K⁄ℤ] := ((g⁻¹ : Kˣ) : K) • dK (g : K)

def spanForms (M : Set K) (H : Set Ω[K⁄ℤ]) (a : ℕ) : AddSubgroup (abelian₂ K) :=
  AddSubgroup.closure
    {η | ∃ c ∈ M, ∃ v : Fin a → Ω[K⁄ℤ], (∀ i, v i ∈ H) ∧ η = c • ExteriorAlgebra.ιMulti K a v}

def frame {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n) : Ω[K⁄ℤ] :=
  if i ∈ J then dlog (x i) else dK (x i : K)

def logWedge {n : ℕ} (x : Fin n → Kˣ) (I : Finset (Fin n)) : abelian₂ K :=
  ((I.sort (· ≤ ·)).map fun i => ExteriorAlgebra.ι K (dlog (x i))).prod

def chartForms (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (a : ℕ) :
    AddSubgroup (abelian₂ K) :=
  spanForms {c | c * t ∈ A} (Set.range (frame x J)) a

def IsCoord {n : ℕ} (x : Fin n → Kˣ) : Prop :=
  LinearIndependent K (fun i => dK (x i : K)) ∧
    Submodule.span K (Set.range fun i => dK (x i : K)) = ⊤

structure AlgChart (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) : Prop where

  mem : ∀ i, (x i : K) ∈ A

  coord : IsCoord x

  deriv : ∀ f ∈ A, ∃ c : Fin n → K, (∀ i, c i ∈ A) ∧ dK f = ∑ i, c i • dK (x i : K)

  root : ∀ (S : Finset (Fin n)) (g : K) (m : ℕ), 0 < m →
    g ^ m / ∏ j ∈ S, (x j : K) ∈ A → g / ∏ j ∈ S, (x j : K) ∈ A

def IsCartierMap (p : ℕ) {n : ℕ} (x : Fin n → Kˣ) (γ : abelian₂ K →+* abelian₂ K) : Prop :=
  (∀ c : K, γ (algebraMap K (abelian₂ K) c) = algebraMap K (abelian₂ K) (c ^ p)) ∧
    ∀ i, γ (ExteriorAlgebra.ι K (dlog (x i))) = ExteriorAlgebra.ι K (dlog (x i))

def IsEulerContraction {n : ℕ} (x : Fin n → Kˣ) (i : Fin n) (θ : abelian₂ K →ₗ[K] abelian₂ K) : Prop :=
  θ 1 = 0 ∧ (∀ (v : Ω[K⁄ℤ]) (η : abelian₂ K),
    θ (ExteriorAlgebra.ι K v * η) = θ (ExteriorAlgebra.ι K v) * η - ExteriorAlgebra.ι K v * θ η) ∧
    ∀ j, θ (ExteriorAlgebra.ι K (dlog (x j))) = if j = i then 1 else 0

end Algebra

section Scheme

variable {X : Scheme.{0}} [IsIntegral X]

def locRing (y : X) : Subring X.functionField :=
  (algebraMap (X.presheaf.stalk y) X.functionField).range

theorem mem_locRing {y : X} {f : X.functionField} : f ∈ locRing y ↔ RegAt y f := Iff.rfl

def LogUnit (Z : Set X) (y : X) (g : X.functionFieldˣ) : Prop :=
  ∀ z : X, z ⤳ y → z ∉ Z → UnitAt z (g : X.functionField)

def logAt (Z : Set X) (G : CartierDiv X) (a : ℕ) (y : X) : AddSubgroup (abelian₂ X.functionField) :=
  spanForms {c | G.RegularAt y c} (dlog '' {g | LogUnit Z y g}) a

omit [IsIntegral X] in

def latSec {V : Type} [AddCommGroup V] (M : X → AddSubgroup V) (U : X.Opens) : AddSubgroup V :=
  ⨅ y ∈ U, M y

abbrev logSec (Z : Set X) (G : CartierDiv X) (a : ℕ) (U : X.Opens) :
    AddSubgroup (abelian₂ X.functionField) :=
  latSec (logAt Z G a) U

structure IsLogChart (Z : Set X) (U : X.Opens) {n : ℕ} (x : Fin n → X.functionFieldˣ)
    (J : Finset (Fin n)) : Prop where

  chart : ∀ y ∈ U, AlgChart (locRing y) x

  logUnit : ∀ y ∈ U, ∀ g : X.functionFieldˣ, LogUnit Z y g ↔
    ∃ (u : X.functionFieldˣ) (m : Fin n → ℤ), UnitAt y (u : X.functionField) ∧ g = u * ∏ j ∈ J, x j ^ m j

def IsSncOn {C : Type} (E : C → CartierDiv X) (U : X.Opens) {n : ℕ} (x : Fin n → X.functionFieldˣ)
    (J : Finset (Fin n)) : Prop :=
  ∃ e : C → Option (Fin n), (∀ c c' j, e c = some j → e c' = some j → c = c') ∧
    (∀ j, j ∈ J ↔ ∃ c, e c = some j) ∧
    ∀ c, ∀ y ∈ U, (E c).IsEqn y ((e c).elim 1 x)

def suppAll {C : Type} (E : C → CartierDiv X) : Set X := ⋃ c, ((E c).supp : Set X)

structure SncAtlas {C : Type} (E : C → CartierDiv X) (n : ℕ) (ι : Type) where

  U : ι → X.Opens

  x : ι → Fin n → X.functionFieldˣ

  J : ι → Finset (Fin n)

  affine : ∀ i, IsAffineOpen (U i)

  gen : ∀ i, genericPoint X ∈ U i

  cover : ⨆ i, U i = ⊤

  chart : ∀ i, IsLogChart (suppAll E) (U i) (x i) (J i)

  snc : ∀ i, IsSncOn E (U i) (x i) (J i)

structure LatModel {V : Type} [AddCommGroup V] [Module X.functionField V] (M : X → AddSubgroup V)
    (F : X.Modules) where

  val : ∀ U : X.Opens, genericPoint X ∈ U → (Γ(F, U) →+ V)

  inj : ∀ U h, Function.Injective (val U h)

  range : ∀ U h, (val U h).range = latSec M U

  res : ∀ (U W : X.Opens) (e : W ≤ U) (h : genericPoint X ∈ W) (s : Γ(F, U)),
    val W h (F.presheaf.map (homOfLE e).op s) = val U (e h) s

  smul : ∀ U h (r : Γ(X, U)) (s : Γ(F, U)), val U h (r • s) = fnOf U h r • val U h s

end Scheme

end GlobalTheory.LogDR
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasiRegularSeqOfIsFreeGen
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.AnForm.R (ds_stalkId_eq_map mem_support_iff_stalkId)
open ReciprocityTheory.AnForm.R.FinalTheorems (stalkId)
open GlobalTheory.LB GlobalTheory.CechPic GlobalTheory.TangentOrigin
open GlobalTheory.TopForm (le_preimage_inf)
open GlobalTheory.Adelic (cutIdeal ideal_cutIdeal mem_support_cutIdeal)
open H0

variable {k : Type} [CommRing k] {Y T : Scheme.{0}}

theorem exists_affine {U : Y.Opens} {y : Y} (hy : y ∈ U) :
    ∃ W : Y.affineOpens, y ∈ W.1 ∧ W.1 ≤ U :=
  let ⟨W, hW, h₁, h₂⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hy
  ⟨⟨W, hW⟩, h₁, h₂⟩

variable (I : Y.IdealSheafData)

theorem stalkId_pow (a : ℕ) (y : Y) : stalkId (I ^ a) y = stalkId I y ^ a := by
  obtain ⟨W, hW, -⟩ := exists_affine (U := ⊤) (y := y) trivial
  rw [ds_stalkId_eq_map _ W y hW, ds_stalkId_eq_map _ W y hW, ← Ideal.map_pow]
  rfl

theorem stalkId_eq_top {y : Y} (hy : y ∉ I.support) : stalkId I y = ⊤ :=
  not_not.1 fun h => hy ((mem_support_iff_stalkId I y).2 h)

theorem ι_mem_support (z : I.subscheme) : I.subschemeι z ∈ I.support :=
  I.range_subschemeι.le ⟨z, rfl⟩

variable {I} in

theorem exists_ι_eq {y : Y} (hy : y ∈ I.support) : ∃ z : I.subscheme, I.subschemeι z = y :=
  I.range_subschemeι.ge hy

theorem ker_stalkMap (z : I.subscheme) :
    RingHom.ker (I.subschemeι.stalkMap z).hom = stalkId I (I.subschemeι z) := by
  have key (W : Y.affineOpens) (hW : I.subschemeι z ∈ W.1) (a : Γ(Y, W.1)) :
      (I.subschemeι.stalkMap z).hom (ger _ hW a) =
        ger (U := I.subschemeι ⁻¹ᵁ W.1) z hW ((I.subschemeι.app W.1).hom a) :=
    Scheme.Hom.germ_stalkMap_apply _ _ z hW a
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨U, hU, a, rfl⟩ := Y.presheaf.germ_exist x
    have h₀ : ger (U := I.subschemeι ⁻¹ᵁ U) z hU ((I.subschemeι.app U).hom a) =
        ger (U := I.subschemeι ⁻¹ᵁ U) z hU 0 :=
      (Scheme.Hom.germ_stalkMap_apply _ _ z hU a).symm.trans (hx.trans (map_zero _).symm)
    obtain ⟨V, hV, i₁, i₂, e⟩ := I.subscheme.presheaf.germ_eq z hU hU _ _ h₀
    obtain ⟨V', hV', hVV⟩ := I.subschemeι.isClosedEmbedding.isInducing.isOpen_iff.1 V.2
    obtain ⟨W, hW, hle⟩ := exists_affine (U := U ⊓ ⟨V', hV'⟩) (y := I.subschemeι z)
      ⟨hU, hVV.ge hV⟩
    have hWV : I.subschemeι ⁻¹ᵁ W.1 ≤ V := fun w hw => hVV.le (hle hw).2
    have hm : resG Y (hle.trans inf_le_left) a ∈ I.ideal W := by
      rw [← I.ker_subschemeι_app W, RingHom.mem_ker, Scheme.Hom.app_eq_appLE, LB.appLE_resG,
        ← resG_app, ← resG_resG i₁.le hWV]
      exact (congrArg (resG _ hWV) (e.trans (map_zero _))).trans (map_zero _)
    rw [ds_stalkId_eq_map I W _ hW]
    exact ger_resG (hle.trans inf_le_left) _ hW a ▸ Ideal.mem_map_of_mem _ hm
  · obtain ⟨W, hW, -⟩ := exists_affine (U := ⊤) (y := I.subschemeι z) trivial
    rw [ds_stalkId_eq_map I W _ hW, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [← I.ker_subschemeι_app W, RingHom.mem_ker] at ha
    exact (key W hW a).trans ((congrArg _ ha).trans (map_zero _))

theorem mem_ideal_iff_ger (W : Y.affineOpens) (a : Γ(Y, W.1)) :
    a ∈ I.ideal W ↔ ∀ y hy, ger y hy a ∈ stalkId I y := by
  refine ⟨fun h y hy => ds_stalkId_eq_map I W y hy ▸ Ideal.mem_map_of_mem _ h, fun h => ?_⟩
  rw [← I.ker_subschemeι_app W, RingHom.mem_ker]
  refine fun_ext_ger fun z hz => ?_
  have := (ker_stalkMap I z).ge (h _ hz)
  exact (Scheme.Hom.germ_stalkMap_apply _ _ z hz a).symm.trans (this.trans (map_zero _).symm)

variable {L : LB Y} (hL : L.IsLB) {ι : Type} (s : ι → L.Sec)

abbrev secGer (j : L.ι) (y : Y) (hj : y ∈ L.U j) : ι → Y.presheaf.stalk y :=
  fun i => ger y hj ((s i).f j)

theorem stalkId_cutIdeal (j : L.ι) (y : Y) (hj : y ∈ L.U j) :
    stalkId (cutIdeal hL s) y = Ideal.span (Set.range (secGer s j y hj)) := by
  obtain ⟨W, hW, hle⟩ := exists_affine hj
  rw [ds_stalkId_eq_map _ W y hW, ideal_cutIdeal hL s W j hle, Ideal.map_span, ← Set.range_comp]
  exact congrArg (fun f => Ideal.span (Set.range f)) (funext fun i => ger_resG hle y hW _)

theorem vanishesAlong_cutIdeal (i : ι) : VanishesAlong (s i) (cutIdeal hL s).subschemeι :=
  fun j => fun_ext_ger fun z hz => by
    have : ger (U := L.U j) ((cutIdeal hL s).subschemeι z) hz ((s i).f j) ∈ RingHom.ker ((cutIdeal hL s).subschemeι.stalkMap z).hom := by
      rw [ker_stalkMap, stalkId_cutIdeal hL s j _ hz]
      exact Ideal.subset_span ⟨i, rfl⟩
    exact (Scheme.Hom.germ_stalkMap_apply _ _ z hz _).symm.trans (this.trans (map_zero _).symm)

theorem secGer_change (j j' : L.ι) (y : Y) (hj : y ∈ L.U j) (hj' : y ∈ L.U j') (i : ι) :
    secGer s j y hj i = tr L y j j' * secGer s j' y hj' i := by
  have e := congrArg (ger y (memInf hj hj')) (sec_rel (s i) j j' inf_le_left inf_le_right le_rfl)
  rwa [map_mul, ger_resG, ger_resG, ger_resG, ← val_tr] at e

section Etale

variable {p : Y ⟶ Sp k}

theorem formallyUnramified_quotient (h : FormallyUnramified (I.subschemeι ≫ p)) (W : Y.affineOpens) :
    ((Ideal.Quotient.mk (I.ideal W)).comp (algX p W.1)).FormallyUnramified := by
  have h₁ := HasRingHomProperty.appLE @FormallyUnramified (I.subschemeι ≫ p) h
    ⟨⊤, isAffineOpen_top _⟩ ⟨_, W.2.preimage I.subschemeι⟩ le_top
  have h₂ := RingHom.FormallyUnramified.respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv h₁
  let e : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ W.1) ≃+* Γ(Y, W.1) ⧸ I.ideal W :=
    (RingHom.quotientKerEquivOfSurjective (I.subschemeι_app_surjective W)).symm.trans
      (Ideal.quotEquivOfEq (I.ker_subschemeι_app W))
  have h₃ := RingHom.FormallyUnramified.respectsIso.1 _ e h₂
  have e₁ := Scheme.Hom.appLE_comp_appLE I.subschemeι p ⊤ W.1 (I.subschemeι ⁻¹ᵁ W.1) le_top le_rfl
  have e₂ (a : Γ(Y, W.1)) : e ((I.subschemeι.app W.1).hom a) = Ideal.Quotient.mk _ a := by
    rw [RingEquiv.trans_apply, ← RingHom.quotientKerEquivOfSurjective_apply_mk
      (I.subschemeι_app_surjective W), RingEquiv.symm_apply_apply]
    rfl
  rw [Scheme.Hom.appLE_eq_app] at e₁
  refine (congrArg RingHom.FormallyUnramified (RingHom.ext fun c => ?_)).mp h₃
  exact (congrArg e (congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))
    e₁).symm).trans (e₂ _)

variable {D : ℕ} [SmoothOfRelativeDimension D p] (K : CanonLB p D) (s : Fin D → L.Sec)

theorem isUnit_ger_jacFun (h : FormallyUnramified ((cutIdeal hL s).subschemeι ≫ p)) {y : Y}
    (hy : y ∈ (cutIdeal hL s).support) (i : K.bundle.ι) (j : L.ι)
    (hij : y ∈ K.bundle.U i ⊓ L.U j) : IsUnit (ger y hij (K.jacFun s i j)) := by
  obtain ⟨z, rfl⟩ := exists_ι_eq hy
  obtain ⟨W, hW, hle⟩ := exists_affine hij
  have hu := formallyUnramified_quotient _ h W
  rw [ideal_cutIdeal hL s W j (hle.trans inf_le_right)] at hu
  have := K.isUnit_map_jacobian i W.2 (hle.trans inf_le_left) _ hu
    (((cutIdeal hL s).subschemeι.stalkMap z).hom.comp (ger _ hW)) fun a => by
      rw [RingHom.comp_apply, ger_resG, ← RingHom.mem_ker, ker_stalkMap,
        stalkId_cutIdeal hL s j _ hij.2]
      exact Ideal.subset_span ⟨a, rfl⟩
  rw [← K.resG_jacFun s i j hle, RingHom.comp_apply, ger_resG] at this
  exact IsUnit.of_map _ _ this

theorem isQuasiRegularSeq_of_isFreeGen {A : Type} [CommRing A] {α : k →+* A} {D : ℕ}
    (h : α.IsStandardSmoothOfRelativeDimension D) (x : Fin D → A)
    (hx : TopForm.IsFreeGen A (TopForm.dForm α x)) : IsQuasiRegularSeq A x := by
  let := α.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension D k A := h
  cases subsingleton_or_nontrivial A with
  | inl _ => exact isQuasiRegularSeq_of_smul_top_eq_top (Subsingleton.elim _ _)
  | inr _ =>
    have := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth D (R := k) (S := A)
    have hr : Module.finrank A Ω[A⁄k] = D := Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := A) D)
    let b := Module.finBasisOfFinrankEq A Ω[A⁄k] hr
    let v : Fin D → Ω[A⁄k] := fun i => KaehlerDifferential.D k A (x i)
    have e := alternating_map_sum_smul_eq_det_smul (exteriorPower.ιMulti A D)
      (Matrix.of fun i j => b.repr (v i) j) b
    simp only [Matrix.of_apply, b.sum_repr] at e
    have hu := (TopForm.isFreeGen_ιMulti b).smul_iff.1 ((congrArg (TopForm.IsFreeGen A) e).mp hx)
    rw [← Matrix.det_transpose] at hu
    obtain ⟨h₁, h₂⟩ := (b.is_basis_iff_det (v := v)).2 hu
    let := (MvPolynomial.eval₂Hom α x).toAlgebra
    have : IsScalarTower k (MvPolynomial (Fin D) k) A :=
      IsScalarTower.of_algebraMap_eq fun r => (MvPolynomial.eval₂Hom_C α x r).symm
    have hX (i) : algebraMap (MvPolynomial (Fin D) k) A (MvPolynomial.X i) = x i :=
      MvPolynomial.eval₂Hom_X' α x i
    have := EtaleCoordJacobian.etale_of_basis k A (Fin D) (Module.Basis.mk h₁ h₂.ge)
      fun i => by rw [Module.Basis.mk_apply, hX]
    simpa only [hX] using (isQuasiRegularSeq_X (R := k) (Fin D)).of_flat A

omit K in

theorem isQuasiRegularSeq_secGer (h : FormallyUnramified ((cutIdeal hL s).subschemeι ≫ p)) {y : Y}
    (hy : y ∈ (cutIdeal hL s).support) (j : L.ι) (hj : y ∈ L.U j) :
    IsQuasiRegularSeq (Y.presheaf.stalk y) (secGer s j y hj) := by
  let K := CanonLB.all p D
  obtain ⟨i, hi⟩ := exists_chart K.isLB y
  have hb : y ∈ Y.basicOpen (K.jacFun s i j) :=
    (Y.mem_basicOpen _ y (memInf hi hj)).2 (isUnit_ger_jacFun hL K s h hy i j _)
  obtain ⟨⟨V, hV⟩, hx, hle⟩ := exists_affine hb
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨σ, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (σ : Set Γ(Y, V)), y ∈ Y.basicOpen (t : Γ(Y, V)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hV (t : Γ(Y, V))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, V))))
  have h₂ : (algX p (Y.basicOpen (t : Γ(Y, V)))).IsStandardSmoothOfRelativeDimension D := by
    rw [← TopForm.resG_comp_algX p (Y.basicOpen_le (t : Γ(Y, V)))]
    exact h₁
  have hW := IsAffineOpen.basicOpen hV (t : Γ(Y, V))
  have l₁ := (Y.basicOpen_le (t : Γ(Y, V))).trans hle
  have l₂ := l₁.trans (Y.basicOpen_le _)
  have hu : IsUnit (resG Y l₂ (K.jacFun s i j)) :=
    resG_resG (Y.basicOpen_le _) l₁ (K.jacFun s i j) ▸
      (Y.toRingedSpace.isUnit_res_basicOpen (K.jacFun s i j)).map (resG Y l₁)
  rw [K.resG_jacFun, K.isUnit_jacobian_iff i hW] at hu
  let := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hxt⟩ : Y.basicOpen (t : Γ(Y, V)))
  have := hW.isLocalization_stalk ⟨y, hxt⟩
  have hq := (isQuasiRegularSeq_of_isFreeGen h₂ _ hu.gen).of_isLocalization (Y.presheaf.stalk y)
    (hW.primeIdealOf ⟨y, hxt⟩).asIdeal.primeCompl
  exact (congrArg _ (funext fun a => ger_resG (l₂.trans inf_le_right) y hxt _)).mp hq

end Etale

end GlobalTheory.Vanishing
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
section
open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.WeilParts
open scoped TensorProduct Classical

namespace GlobalTheory.AdTh

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure IsPair (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) : Prop where
  weil : IsWeilDatumO ψ V W χV χW om
  inf : IsInfFam θ
  std : V.gram = 1
  even : Even V.rank
  sigV : V.SigOK
  sigW : W.SigOK
  expV : ∀ τ, ∃ a : ℤ, HasInfExp D χV τ a
  expW : ∀ τ, ∃ b : ℤ, HasInfExp D χW τ ((b : ℚ) + (W.rank : ℚ) / 2)
  unr : ∀ v ε, NonSplitAt D v ε → UnramAt ε χV ∧ UnramAt ε χW
  eta : ∃ η, IsEtaTilde D η

def MarkAd {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Level H) (W : HSp D) {r : ℕ} (hr : W.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (h : GA D W) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) : Prop :=
  ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat W h,
    finVec W (mk a ∘ Fin.cast hr) - (finHom W h).1.mulVec (finVec W (ι a)) = (l.M : ℕ) • w

def hatC {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (l : Level H)
    {n : ℕ} (φ : (Fin n → LevQc Dw l) → ℂ) (q : Fin n → LevQ Dw l) : ℂ :=
  ∑ᶠ x : Fin n → LevQc Dw l, φ x * Complex.exp (2 * Real.pi * Complex.I / (l.M : ℂ)) ^
    pairL (l := l) (fun b => qRep (x b)) (fun b => levRep (q b))

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

def SerOf (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : (R.MW i (sg0 D A)).Vec)
    (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ) : Prop :=
  (∀ k, ‖cc k‖ = 1) ∧ ‖ph‖ = 1 ∧
    ∀ (t : Tp) (h : O.Cl' t → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))),
      RepsR R i (tup t) h (O.bad t) J' (O.Lh t) (O.gam t) (O.vol t) →
      ∀ (y : (R.HV i (tup t)).H) (x : O.Cl' t → VsV D i O.c'.F), Place R i (tup t) h O.c0' y x →
      ∀ f ∈ sec (C.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank,
        IsThClsD (C.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ t) (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t) O.io x f →
        ∀ g : GA D (Wc D i), ph * R.thF i (tup t) y v₀ g =
          cc (O.dict g).1 * (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * O.mu g *
            rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) f (O.dict g).1 (O.dict g).2

theorem SerOf.norm {O : OMDat C R i Tp tup} {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
    {cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ} {ph : ℂ} (h : SerOf O κ v₀ cc ph) : ‖ph‖ = 1 := h.2.1

end

end GlobalTheory.AdTh
end

