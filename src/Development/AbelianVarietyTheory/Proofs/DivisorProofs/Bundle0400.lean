import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0385
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryTranslationInvariantPTorsion
section
set_option autoImplicit false

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

theorem lTensor_transl_comul (n : ℕ) (x : G.A (n + 1)) :
    (G.transl n).toLinearMap.lTensor (G.A (n + 1)) (comul (R := R) x) =
      TensorProduct.assoc R _ _ _ ((comul (R := R)).rTensor (G.A 1) (G.transl n x)) := by
  have h1 : (G.transl n).toLinearMap =
      (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1).lTensor _ ∘ₗ comul :=
    LinearMap.ext fun a => G.transl_apply n a
  have h2 : ∀ t : (G.A (n + 1) ⊗[R] G.A (n + 1)) ⊗[R] G.A (n + 1),
      ((G.resOne n : G.A (n + 1) →ₗ[R] G.A 1).lTensor _).lTensor _ (TensorProduct.assoc R _ _ _ t) =
        TensorProduct.assoc R _ _ _ ((G.resOne n : G.A (n + 1) →ₗ[R] G.A 1).lTensor _ t) := by
    intro t
    induction t with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul u c =>
      induction u with
      | zero => simp
      | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
      | tmul a b => simp
  rw [h1, LinearMap.lTensor_comp_apply, ← coassoc_apply, h2, transl_apply]
  congr 1
  generalize comul (R := R) x = t
  induction t with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => simp

theorem lTensor_transl_sub_cobOne (n : ℕ) (x : G.A (n + 1)) (b : G.A 1)
    (h : G.transl n x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) :
    ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).lTensor
      (G.A (n + 1)) (cobOne R (G.A (n + 1)) x) = 0 := by
  have h1 : ∀ t : G.A (n + 1) ⊗[R] G.A (n + 1), TensorProduct.assoc R _ _ _ (t ⊗ₜ (1 : G.A 1)) =
      ((TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).lTensor _ t := fun t => by
    induction t with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  have h2 : comul (R := R) (1 : G.A (n + 1)) = 1 ⊗ₜ 1 := by simp [Algebra.TensorProduct.one_def]
  have h3 : G.transl n 1 = 1 ⊗ₜ 1 := by rw [map_one, Algebra.TensorProduct.one_def]
  rw [LinearMap.lTensor_sub, LinearMap.sub_apply, cobOne_apply]
  simp only [map_sub, lTensor_transl_comul, h, map_add, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul, h1, h2, h3, AlgHom.toLinearMap_apply, LinearMap.flip_apply, mk_apply,
    assoc_tmul, tmul_add]
  abel

theorem cobOne_transl_invariant {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ)
    (x : G.A (n + 1)) (b : G.A 1) (h : G.transl n x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) :
    ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).rTensor
      (G.A (n + 1)) (cobOne R (G.A (n + 1)) x) = 0 ∧
    ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).lTensor
      (G.A (n + 1)) (cobOne R (G.A (n + 1)) x) = 0 := by
  have h2 := G.lTensor_transl_sub_cobOne n x b h
  refine ⟨?_, h2⟩
  rw [← (mem_symCocycles.1 (cobOne_mem x)).2, LinearMap.rTensor_comm, h2, map_zero]

end PDivGroup

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnGramDeterminantUnitLowerThreeStatement
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnGramDeterminant_unitLower_three : ∀ M : Matrix (Fin 3) (Fin 3) ℂ, (∀ i, M i i = 1) → (∀ i j : Fin 3, i < j → M i j = 0) → colGram M 1 = 1 + ‖M 1 0‖ ^ 2 + ‖M 2 0‖ ^ 2 ∧ colGram M 2 = 1 + ‖M 2 1‖ ^ 2 + ‖M 1 0 * M 2 1 - M 2 0‖ ^ 2 := by
  first | exact @GlobalTheory.IntBall.colGram_three_unitLower | exact GlobalTheory.IntBall.colGram_three_unitLower | (intros; apply GlobalTheory.IntBall.colGram_three_unitLower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOfSqZeroAgreePairs
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroAgree

open GlobalTheory.MulUnramified

variable {C C₀ : Type} [CommRing C] [CommRing C₀] (π : C →+* C₀)

lemma spMap_surjective (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0) :
    Function.Surjective (spMap π) := by
  intro (p : PrimeSpectrum C)
  change p ∈ Set.range (PrimeSpectrum.comap π)
  rw [range_comap_of_surjective _ _ hπ, PrimeSpectrum.mem_zeroLocus]
  intro a ha
  refine p.isPrime.mem_of_pow_mem 2 ?_
  have : a ^ 2 ∈ RingHom.ker π ^ 2 := Ideal.pow_mem_pow ha 2
  rw [hsq, Submodule.zero_eq_bot, Ideal.mem_bot] at this
  rw [this]
  exact zero_mem _

lemma preimage_eq_of_agree (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0)
    {X Y : Over (Sp C)} {f f' : X ⟶ Y}
    (h : ∀ (T₀ : Over (Sp C₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ X), y ≫ f = y ≫ f')
    (V : Y.left.Opens) : f.left ⁻¹ᵁ V = f'.left ⁻¹ᵁ V := by
  have hs : Surjective (spMap π) := ⟨spMap_surjective π hπ hsq⟩
  have hf : Surjective (pullback.fst X.hom (spMap π)) := inferInstance
  have e := congrArg (·.left) (h (Over.mk (pullback.snd X.hom (spMap π)))
    (Over.homMk (pullback.fst X.hom (spMap π)) pullback.condition))
  simp only [Over.comp_left, Over.homMk_left] at e
  exact preimage_eq _ hf.surj e V

noncomputable def alg (X : Over (Sp C)) (V : X.left.Opens) : C →+* Γ(X.left, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ X.hom.appLE ⊤ V le_top).hom

lemma fromSpec_over (X : Over (Sp C)) {V : X.left.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ X.hom = spMap (alg X V) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec X.hom (isAffineOpen_top (Spec (CommRingCat.of C))) hV
    (le_top : V ≤ X.hom ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h, alg, spMap, CommRingCat.ofHom_hom, Spec.map_comp]

lemma appLE_alg {X Y : Over (Sp C)} (f : X ⟶ Y) (V : Y.left.Opens) (V' : X.left.Opens)
    (hf : V' ≤ f.left ⁻¹ᵁ V) (c : C) : f.left.appLE V V' hf (alg Y V c) = alg X V' c := by
  simp only [alg, CommRingCat.hom_comp, RingHom.comp_apply]
  exact comp_appLE_apply f.left Y.hom (Over.w f) _ _ _ _ _ _ _

lemma sub_mem (hπ : Function.Surjective π) {X Y : Over (Sp C)} {f f' : X ⟶ Y}
    (h : ∀ (T₀ : Over (Sp C₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ X), y ≫ f = y ≫ f')
    {V : Y.left.Opens} (hV : IsAffineOpen V) {V' : X.left.Opens} (hV' : IsAffineOpen V')
    (hf : V' ≤ f.left ⁻¹ᵁ V) (hf' : V' ≤ f'.left ⁻¹ᵁ V) (s : Γ(Y.left, V)) :
    f.left.appLE V V' hf s - f'.left.appLE V V' hf' s ∈ (RingHom.ker π).map (alg X V') := by
  set J := (RingHom.ker π).map (alg X V')
  let q : Γ(X.left, V') →+* Γ(X.left, V') ⧸ J := Ideal.Quotient.mk J
  let ψ : C₀ →+* Γ(X.left, V') ⧸ J :=
    (Ideal.quotientMap J (alg X V') Ideal.le_comap_map).comp
      (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
  have hψ : ψ.comp π = q.comp (alg X V') := by
    ext c
    have e : (RingHom.quotientKerEquivOfSurjective hπ).symm (π c) = Ideal.Quotient.mk _ c :=
      (RingEquiv.symm_apply_eq _).mpr rfl
    simp only [ψ, q, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
      Ideal.quotientMap_mk]
  let y : Over.mk ((Over.mk (spMap ψ)).hom ≫ spMap π) ⟶ X :=
    Over.homMk (spMap q ≫ hV'.fromSpec) (by
      rw [Category.assoc, fromSpec_over]
      simp only [Over.mk_hom, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ])
  have e := congrArg (·.left) (h (Over.mk (spMap ψ)) y)
  simp only [y, Over.comp_left, Over.homMk_left, Category.assoc] at e
  rw [← hV.SpecMap_appLE_fromSpec f.left hV' hf, ← hV.SpecMap_appLE_fromSpec f'.left hV' hf',
    ← Category.assoc, ← Category.assoc, cancel_mono, spMap, ← Spec.map_comp, ← Spec.map_comp,
    Spec.map_inj] at e
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  exact congr($e s)

lemma eq_on_map {B R : Type} [CommRing B] [CommRing R] (I : Ideal C) (hI : I ^ 2 = 0)
    (φB : C →+* B) (φR : C →+* R) (β β' : B →+* R) (hβ : β.comp φB = φR) (hβ' : β'.comp φB = φR)
    (hd : ∀ b, β b - β' b ∈ I.map φR) {x : B} (hx : x ∈ I.map φB) : β x = β' x := by
  have hJ : I.map φR * I.map φR = ⊥ := by
    rw [← Ideal.map_mul, ← pow_two, hI, Submodule.zero_eq_bot, Ideal.map_bot]
  suffices β x = β' x ∧ β x ∈ I.map φR from this.1
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    rw [← RingHom.comp_apply β, hβ, ← RingHom.comp_apply β', hβ']
    exact ⟨rfl, Ideal.mem_map_of_mem _ hc⟩
  | zero => simp
  | add x y _ _ hx hy => exact ⟨by rw [map_add, map_add, hx.1, hy.1], by rw [map_add]; exact add_mem hx.2 hy.2⟩
  | smul a x _ hx =>
    refine ⟨?_, ?_⟩
    · rw [smul_eq_mul, map_mul, map_mul, ← hx.1, ← sub_eq_zero, ← sub_mul, ← Ideal.mem_bot, ← hJ]
      exact Ideal.mul_mem_mul (hd a) hx.2
    · rw [smul_eq_mul, map_mul]
      exact Ideal.mul_mem_left _ _ hx.2

end GlobalTheory.SqZeroAgree

namespace GlobalTheory

open MulUnramified SqZeroAgree in

theorem comp_eq_of_sqZero_agree : ∀ (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀),
    Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (K G : Over (Sp C)) (g g' : K ⟶ G),
    (∀ (T₀ : Over (Sp C₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ K), y ≫ g = y ≫ g') →
    ∀ (T : Over (Sp C)) (w w' : T ⟶ K),
    (∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ w = j ≫ w') →
    w' ≫ g = w' ≫ g' → w ≫ g = w ≫ g' := by
  intro C C₀ _ _ π hπ hsq K G g g' hg T w w' hw h'
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  refine Scheme.hom_ext_of_forall _ _ fun t ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, htV, -⟩ :=
    G.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g.left (w.left t))) isOpen_univ
  obtain ⟨_, ⟨V', hV', rfl⟩, htV', hV'V : V' ≤ g.left ⁻¹ᵁ V⟩ :=
    K.left.isBasis_affineOpens.exists_subset_of_mem_open (a := w.left t) (u := g.left ⁻¹ᵁ V) htV
      (TopologicalSpace.Opens.isOpen _)
  obtain ⟨_, ⟨W, hW, rfl⟩, htW, hWV' : W ≤ w.left ⁻¹ᵁ V'⟩ :=
    T.left.isBasis_affineOpens.exists_subset_of_mem_open (a := t) (u := w.left ⁻¹ᵁ V') htV'
      (TopologicalSpace.Opens.isOpen _)
  have hV'V₂ : V' ≤ g'.left ⁻¹ᵁ V := preimage_eq_of_agree π hπ hsq hg V ▸ hV'V
  have hWV'₂ : W ≤ w'.left ⁻¹ᵁ V' := preimage_eq_of_agree π hπ hsq hw V' ▸ hWV'
  refine ⟨W, htW, ?_⟩
  have key : ∀ s, w.left.appLE V' W hWV' (g.left.appLE V V' hV'V s) =
      w.left.appLE V' W hWV' (g'.left.appLE V V' hV'V₂ s) := by
    intro s
    have hx := sub_mem π hπ hg hV hV' hV'V hV'V₂ s
    have e := eq_on_map (RingHom.ker π) hsq (alg K V') (alg T W) (w.left.appLE V' W hWV').hom
      (w'.left.appLE V' W hWV'₂).hom (RingHom.ext (appLE_alg w V' W hWV'))
      (RingHom.ext (appLE_alg w' V' W hWV'₂)) (sub_mem π hπ hw hV' hW hWV' hWV'₂) hx
    have e' : w'.left.appLE V' W hWV'₂ (g.left.appLE V V' hV'V s) =
        w'.left.appLE V' W hWV'₂ (g'.left.appLE V V' hV'V₂ s) := by
      rw [comp_appLE_apply _ _ rfl _ _ _ _ _ (le_preimage_of_comp _ _ hV'V hWV'₂),
        comp_appLE_apply _ _ rfl _ _ _ _ _ (le_preimage_of_comp _ _ hV'V₂ hWV'₂)]
      have hh : w'.left ≫ g.left = w'.left ≫ g'.left := by rw [← Over.comp_left, h', Over.comp_left]
      rw [appLE_congr hh V W _ (le_preimage_of_comp _ _ hV'V₂ hWV'₂)]
    simp only [map_sub] at e
    rw [← sub_eq_zero, ← sub_eq_zero.mpr e, e', sub_self, sub_zero]
  have fin : (w.left ≫ g.left).appLE V W (le_preimage_of_comp _ _ hV'V hWV') =
      (w.left ≫ g'.left).appLE V W (le_preimage_of_comp _ _ hV'V₂ hWV') := by
    ext s
    rw [← comp_appLE_apply _ _ rfl _ _ _ hV'V hWV', ← comp_appLE_apply _ _ rfl _ _ _ hV'V₂ hWV']
    exact key s
  rw [← hW.isoSpec_hom_fromSpec, Category.assoc, Category.assoc,
    ← hV.SpecMap_appLE_fromSpec _ hW (le_preimage_of_comp _ _ hV'V hWV'), fin,
    hV.SpecMap_appLE_fromSpec _ hW]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotDComp
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

def invP (q : ℕ) : PSh where
  obj U := PLift (IsUnit (q : Γ(U.unop, ⊤)))
  map f := TypeCat.ofHom fun h => ⟨by simpa using h.down.map f.unop.appTop.hom⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def fibQ (q N : ℕ) : Spc := pullback (trivV N (disc.obj (invP q))) (PGL.pr N)

def lineQ (q N : ℕ) : fibQ q N ⟶ ofCat (glCat 1) := pullback.snd _ _ ≫ PGL.line N

variable (R : Type) [CommRing R]

def cotPre (q N : ℕ) (I : Cx R) (n : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of (ULift.{1} R) (Cochain ((chains R).obj (sch.obj U.unop ⨯ fibQ q N)) I n)
  map f := ModuleCat.ofHom
    { toFun := fun α => (Cochain.ofHom ((chains R).map (prod.map (sch.map f.unop) (𝟙 (fibQ q N))))).comp α (zero_add n)
      map_add' := fun α β => Cochain.comp_add _ _ _ _
      map_smul' := fun r α => Cochain.comp_smul _ _ _ _ }
  map_id U := by
    ext α : 2
    simp
  map_comp f g := by
    ext α : 2
    change (Cochain.ofHom ((chains R).map (prod.map (sch.map (g.unop ≫ f.unop)) (𝟙 (fibQ q N))))).comp α (zero_add n) =
      (Cochain.ofHom ((chains R).map (prod.map (sch.map g.unop) (𝟙 (fibQ q N))))).comp
        ((Cochain.ofHom ((chains R).map (prod.map (sch.map f.unop) (𝟙 (fibQ q N))))).comp α (zero_add n)) (zero_add n)
    rw [show prod.map (sch.map (g.unop ≫ f.unop)) (𝟙 (fibQ q N)) =
      prod.map (sch.map g.unop) (𝟙 (fibQ q N)) ≫ prod.map (sch.map f.unop) (𝟙 (fibQ q N)) by simp,
      Functor.map_comp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

def cotD (q N : ℕ) (I : Cx R) (n : ℤ) : cotPre R q N I n ⟶ cotPre R q N I (n + 1) where
  app U := ModuleCat.ofHom
    { toFun := fun α => δ n (n + 1) α
      map_add' := fun α β => δ_add _ _ _ _
      map_smul' := fun r α => δ_smul _ _ _ _ }
  naturality U U' f := by
    ext α : 2
    revert α
    intro (α : Cochain ((chains R).obj (sch.obj U.unop ⨯ fibQ q N)) I n)
    change δ n (n + 1) ((Cochain.ofHom ((chains R).map (prod.map (sch.map f.unop) (𝟙 (fibQ q N))))).comp α (zero_add n)) =
      (Cochain.ofHom ((chains R).map (prod.map (sch.map f.unop) (𝟙 (fibQ q N))))).comp (δ n (n + 1) α) (zero_add (n + 1))
    rw [δ_zero_cochain_comp _ _ _ rfl, δ_ofHom, Cochain.zero_comp, smul_zero, add_zero]

theorem cotD_comp (q N : ℕ) (I : Cx R) (n : ℤ) : cotD R q N I n ≫ cotD R q N I (n + 1) = 0 := by
  ext U : 2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  change δ (n + 1) (n + 1 + 1) (δ n (n + 1) α) = 0
  exact δ_δ _ _ _ _

def Jcx (q N : ℕ) (I : Cx R) : Cx R :=
  CochainComplex.of (fun n => (presheafToSheaf Scheme.etaleTopology.{0} _).obj (cotPre R q N I n))
    (fun n => (presheafToSheaf Scheme.etaleTopology.{0} _).map (cotD R q N I n))
    (fun n => by rw [← Functor.map_comp, cotD_comp, Functor.map_zero])

variable {R}

def Jsec {q N : ℕ} {I : Cx R} {n : ℤ} {U : Scheme.{0}} (c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n) :
    Sec ((Jcx R q N I).X n) U :=
  ((toSheafify Scheme.etaleTopology.{0} (cotPre R q N I n)).app (op U)).hom c

def twCast {q : ℕ} {i i' : ℤ} (h : i = i') {s : ℤ} {V : Scheme.{0}} (x : Sec ((res (ZMod q) (tw q i)).X s) V) :
    Sec ((res (ZMod q) (tw q i')).X s) V := h ▸ x

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossTZeroRight
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.PBFc
open GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ

variable {R : Type} [CommRing R]

abbrev BSx (X : SimplicialObject Spc) (a b : ℕ) (U : Scheme.{0}) : Type :=
  ((X.obj (op (SimplexCategory.mk a))).obj (op (SimplexCategory.mk b))).obj (op U)

abbrev BSx.res {X : SimplicialObject Spc} {a b : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (y : BSx X a b U) : BSx X a b V :=
  ((X.obj (op (SimplexCategory.mk a))).obj (op (SimplexCategory.mk b))).map g.op y

theorem biChains_isZero (X : SimplicialObject Spc) (c l : ℤ) (h : 0 < c ∨ 0 < l) :
    IsZero (((biChains R X).X c).X l) := by
  rcases h with h | h
  · exact (HomologicalComplex.eval _ _ l).map_isZero (HomologicalComplex.isZero_extend_X _ _ c (fun i hi => by
      change -((i : ℕ) : ℤ) = c at hi
      omega))
  · by_cases hc : c ≤ 0
    · obtain ⟨a, rfl⟩ : ∃ a : ℕ, c = -(a : ℤ) := ⟨(-c).toNat, by omega⟩
      refine IsZero.of_iso ?_ ((HomologicalComplex.eval _ _ l).mapIso
        (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := a) rfl))
      exact HomologicalComplex.isZero_extend_X _ _ l (fun i hi => by
        change -((i : ℕ) : ℤ) = l at hi
        omega)
    · exact (HomologicalComplex.eval _ _ l).map_isZero (HomologicalComplex.isZero_extend_X _ _ c (fun i hi => by
        change -((i : ℕ) : ℤ) = c at hi
        omega))

def evT {X : SimplicialObject Spc} {K : Cx R} {n : ℤ} (γ : Cochain (totChains R X) K n) (a b : ℕ) (s : ℤ)
    (h : -((a + b : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : BSx X a b U) : Sec (K.X s) U :=
  Sec.map ((biChainsXIso R X a b).inv ≫ (biChains R X).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ))
      (-((a + b : ℕ) : ℤ)) (by simp only [ComplexShape.π_def]; push_cast; ring) ≫ γ.v _ s h) (freeGen R _ U y)

theorem evT_ext {X : SimplicialObject Spc} {K : Cx R} {n : ℤ} (γ γ' : Cochain (totChains R X) K n)
    (h : ∀ a b s h U y, evT γ a b s h U y = evT γ' a b s h U y) : γ = γ' := by
  ext t s hs : 1
  apply HomologicalComplex₂.total.hom_ext
  intro c l hcl
  have hcl' : c + l = t := hcl
  by_cases hc : c ≤ 0 ∧ l ≤ 0
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, c = -(a : ℤ) := ⟨(-c).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, l = -(b : ℤ) := ⟨(-l).toNat, by omega⟩
    obtain rfl : t = -((a + b : ℕ) : ℤ) := by push_cast; omega
    rw [← cancel_epi (biChainsXIso R X a b).inv]
    exact free_ext _ _ fun U y => h a b s hs U y
  · exact (biChains_isZero X c l (by omega)).eq_of_src _ _

theorem evT_exists {X : SimplicialObject Spc} {K : Cx R} {n : ℤ}
    (f : ∀ (a b : ℕ) (s : ℤ), -((a + b : ℕ) : ℤ) + n = s → ∀ U : Scheme.{0}, BSx X a b U → Sec (K.X s) U)
    (hf : ∀ a b s h (V U : Scheme.{0}) (g : V ⟶ U) (y : BSx X a b U), Sec.res g (f a b s h U y) = f a b s h V (y.res g)) :
    ∃ γ : Cochain (totChains R X) K n, ∀ a b s h U y, evT γ a b s h U y = f a b s h U y := by
  have key : ∀ (c l s : ℤ) (hs : c + l + n = s), ∃ ψ : ((biChains R X).X c).X l ⟶ K.X s,
      ∀ (a b : ℕ) (hc : c = -(a : ℤ)) (hl : l = -(b : ℤ)) U y,
        Sec.map ((biChainsXIso R X a b).inv ≫ eqToHom (by rw [hc, hl]) ≫ ψ) (freeGen R _ U y) =
          f a b s (by push_cast; omega) U y := by
    intro c l s hs
    by_cases hc : c ≤ 0 ∧ l ≤ 0
    · obtain ⟨a, rfl⟩ : ∃ a : ℕ, c = -(a : ℤ) := ⟨(-c).toNat, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b : ℕ, l = -(b : ℤ) := ⟨(-l).toNat, by omega⟩
      obtain ⟨φ, hφ⟩ := free_exists (R := R) _ _ (f a b s (by push_cast; omega)) (fun V U g y => hf a b s _ V U g y)
      refine ⟨(biChainsXIso R X a b).hom ≫ φ, fun a' b' hc hl U y => ?_⟩
      obtain rfl : a' = a := by omega
      obtain rfl : b' = b := by omega
      rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
      exact hφ U y
    · exact ⟨0, fun a b hc' hl' => by omega⟩
  choose ψ hψ using key
  refine ⟨Cochain.mk fun t s h => (biChains R X).totalDesc fun c l hcl => ψ c l s (by
      have : c + l = t := hcl
      omega), fun a b s h U y => ?_⟩
  unfold evT
  rw [Cochain.mk_v, HomologicalComplex₂.ι_totalDesc]
  have := hψ (-(a : ℤ)) (-(b : ℤ)) s (by push_cast at h ⊢; omega) a b rfl rfl U y
  rw [eqToHom_refl, Category.id_comp] at this
  exact this

section Cross
variable {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N))

def baseS {a b : ℕ} {U : Scheme.{0}} (y : BSx (twX E V) a b U) : Sx E a U :=
  (show (E.obj (op (SimplexCategory.mk a))).obj (op U) × ((Fib N).obj (op (SimplexCategory.mk b))).obj (op U) from y).1

variable {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)

def vertS {a b : ℕ} {U : Scheme.{0}} (y : BSx (twX E V) a b U) : Sx B b U :=
  ((ℓ.app (op (SimplexCategory.mk a))).app (op (SimplexCategory.mk b))).app (op U) y

theorem baseS_res {a b : ℕ} {W U : Scheme.{0}} (g : W ⟶ U) (y : BSx (twX E V) a b U) :
    baseS V (y.res g) = (baseS V y).res g := rfl

theorem vertS_res {a b : ℕ} {W U : Scheme.{0}} (g : W ⟶ U) (y : BSx (twX E V) a b U) :
    vertS V ℓ (y.res g) = (vertS V ℓ y).res g :=
  ConcreteCategory.congr_hom (((ℓ.app (op (SimplexCategory.mk a))).app (op (SimplexCategory.mk b))).naturality g.op) y

variable {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n)
  (z : Cochain ((chains R).obj B) J m)

def crossVal (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + k = s) (U : Scheme.{0}) (y : BSx (twX E V) a b U) :
    Sec (K.X s) U :=
  (m * (a : ℤ)).negOnePow • μ.mul U (-(a : ℤ) + n) (-(b : ℤ) + m) s (by push_cast at h; omega)
    (ev α a _ rfl U (baseS V y)) (ev z b _ rfl U (vertS V ℓ y))

theorem crossVal_res (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + k = s) {W U : Scheme.{0}} (g : W ⟶ U)
    (y : BSx (twX E V) a b U) :
    Sec.res g (crossVal V ℓ μ hk α z a b s h U y) = crossVal V ℓ μ hk α z a b s h W (y.res g) := by
  unfold crossVal
  rw [Units.smul_def, Units.smul_def, Sec.res, map_zsmul, ← Sec.res, μ.nat, ev_res, ev_res, baseS_res, vertS_res]

def crossT : Cochain (totChains R (twX E V)) K k :=
  (evT_exists (crossVal V ℓ μ hk α z) (fun a b s h W U g y => crossVal_res V ℓ μ hk α z a b s h g y)).choose

theorem evT_crossT (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + k = s) (U : Scheme.{0}) (y : BSx (twX E V) a b U) :
    evT (crossT V ℓ μ hk α z) a b s h U y =
      (m * (a : ℤ)).negOnePow • μ.mul U (-(a : ℤ) + n) (-(b : ℤ) + m) s (by push_cast at h; omega)
        (ev α a _ rfl U (baseS V y)) (ev z b _ rfl U (vertS V ℓ y)) :=
  (evT_exists (crossVal V ℓ μ hk α z) (fun a b s h W U g y => crossVal_res V ℓ μ hk α z a b s h g y)).choose_spec a b s h U y

theorem evT_add {X : SimplicialObject Spc} {L : Cx R} {t : ℤ} (γ γ' : Cochain (totChains R X) L t) (a b : ℕ) (s : ℤ)
    (h : -((a + b : ℕ) : ℤ) + t = s) (U : Scheme.{0}) (y : BSx X a b U) :
    evT (γ + γ') a b s h U y = evT γ a b s h U y + evT γ' a b s h U y := by
  unfold evT
  rw [Cochain.add_v, Preadditive.comp_add, Preadditive.comp_add]
  exact map_add (mapHom _ _ (freeGen R _ U y)) _ _

theorem crossT_add_left (α' : Cochain ((chains R).obj E) I n) :
    crossT V ℓ μ hk (α + α') z = crossT V ℓ μ hk α z + crossT V ℓ μ hk α' z :=
  evT_ext _ _ fun a b s h U y => by
    rw [evT_add, evT_crossT, evT_crossT, evT_crossT, ev_add, map_add, LinearMap.add_apply, smul_add]

theorem evT_zero {X : SimplicialObject Spc} {L : Cx R} {t : ℤ} (a b : ℕ) (s : ℤ)
    (h : -((a + b : ℕ) : ℤ) + t = s) (U : Scheme.{0}) (y : BSx X a b U) :
    evT (0 : Cochain (totChains R X) L t) a b s h U y = 0 := by
  unfold evT
  rw [Cochain.zero_v, comp_zero, comp_zero]
  exact map_zero (mapHom _ _ (freeGen R _ U y))

theorem crossT_zero_right : crossT V ℓ μ hk α (0 : Cochain ((chains R).obj B) J m) = 0 :=
  evT_ext _ _ fun a b s h U y => by
    rw [evT_crossT, evT_zero, ev_zero, map_zero, smul_zero]

end Cross

def twPairI (q : ℕ) (i j : ℤ) : Pair (res (ZMod q) (tw q (i - j))) (res (ZMod q) (tw q j)) (res (ZMod q) (tw q i)) :=
  Eq.rec (motive := fun k _ => Pair (res (ZMod q) (tw q (i - j))) (res (ZMod q) (tw q j)) (res (ZMod q) (tw q k)))
    (twPair q (i - j) j) (sub_add_cancel i j)

def phi (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ)
    (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (n : ℤ) :
    (∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) →+
      Cochain (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n :=
  AddMonoidHom.mk' (fun α => ∑ j : Fin N, crossT V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _) (α j) (z j))
    (fun α α' => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => crossT_add_left V ℓ _ _ _ _ _)

theorem phi_apply (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ)
    (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (n : ℤ) (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) :
    phi q V ℓ i z n α = ∑ j : Fin N, crossT V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _) (α j) (z j) := rfl

end GlobalTheory.PBFc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DadjCombinationStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_D_eq_sum_smul_D_of_mem_adjoin : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (n : ℕ) (u : Fin n → F), ∀ v ∈ Algebra.adjoin k (Set.range u), ∃ c : Fin n → F, (∀ j, c j ∈ Algebra.adjoin k (Set.range u)) ∧ D k K (algebraMap F K v) = ∑ j, algebraMap F K (c j) • D k K (algebraMap F K (u j)) := by
  first | (exact @GlobalTheory.dadj_combination) | (exact GlobalTheory.dadj_combination) | (intros; apply GlobalTheory.dadj_combination  <;> assumption)
end

