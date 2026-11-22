import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0177
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0237
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0771
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0603
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0077
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0774
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonFactorRecCompatible
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.SatakeLaw

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def consEquiv (n : ℕ) : ((Fin 1 → ℂ) × (Fin n → ℂ)) ≃ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun v := Fin.cons (v.1 0) v.2
  invFun f := (fun _ => f 0, Fin.tail f)
  map_add' x y := funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp
  left_inv v := Prod.ext (funext fun i => by rw [Subsingleton.elim i 0]; simp) (funext fun j => by simp [Fin.tail])
  right_inv f := funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]

theorem diag_sum_iso {n : ℕ} (c : Fin (n + 1) → ℂˣ) :
    ((WDRep.diag h fun _ : Fin 1 => c 0).sum (WDRep.diag h fun i : Fin n => c i.succ)).Iso (WDRep.diag h c) := by
  refine ⟨consEquiv n, fun σ v => ?_, fun v => ?_⟩
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [consEquiv]
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [consEquiv]

theorem sumList_cons (x : WD h) (l : List (WD h)) : sumList (x :: l) = x.lpSum (sumList l) := rfl

theorem sumList_ofFn_diag : ∀ (n : ℕ) (c : Fin n → ℂˣ),
    sumList (List.ofFn fun i => WD.mk (WDRep.diag h fun _ : Fin 1 => c i)) = WD.mk (WDRep.diag h c)
  | 0, c => by
      rw [List.ofFn_zero]
      show WD.lpZero h = _
      unfold WD.lpZero
      congr 2
      funext i
      exact i.elim0
  | n + 1, c => by
      rw [List.ofFn_succ]
      rw [sumList_cons]
      rw [sumList_ofFn_diag n (fun i => c i.succ), WD.lpSum_mk]
      exact WD.sound (diag_sum_iso c)

end GlobalTheory.LocLanglands.SatakeLaw

namespace GlobalTheory.LocLanglands.SatakeLaw

theorem sat_of_lawsLit : LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing →
    GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ)
    (rc : IrrGL (w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (x : IrrGL (w.adicCompletion E)) (α : Fin x.1 → ℂˣ),
    HasSatake x.rep α → rc x = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  intro h1 h2 h3 h4 h5 h6 E Ω _ _ _ _ _ A w h a ha e rc H x α hα
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hL := GlobalTheory.T.spherical_satake_eq_langlandsQuotient_unramified h1 h2 h3 h4 h5 h6 (w.adicCompletion E) x α hα
  rw [Fin.univ_val_map] at hL
  rw [H.langlands _ x hL, segSum, List.map_ofFn, ← sumList_ofFn_diag]
  congr 1
  refine List.ofFn_inj.mpr (funext fun i => ?_)
  simp only [Function.comp_apply, Segment.single, Segment.first_ofFirst, Segment.len_ofFirst, Nat.cast_one, sub_self,
    zero_div, WD.lpTw_zero, Test.lpChar_lpSp_one, H.one]
  exact Test.lpOfChar_unrChar ha (α i) _

end GlobalTheory.LocLanglands.SatakeLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBijectiveOfIsSubquotient
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
open GlobalTheory.PRep GlobalTheory.SmGL

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.JacFactor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isIrreducible_comp_surj {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (f : G →* H) (hf : Function.Surjective f) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp f : Representation ℂ G V) := by
  let e : Subrepresentation (ρ.comp f : Representation ℂ G V) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        obtain ⟨x, rfl⟩ := hf g
        exact S.apply_mem_toSubmodule x hv⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (f g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  haveI : IsSimpleOrder (Subrepresentation ρ) := h
  exact e.isSimpleOrder

theorem isSubquotient_comp' {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (h : IsSubquotient σ ρ) (ψ : G' →* G) : IsSubquotient (σ.comp ψ) (ρ.comp ψ) := by
  obtain ⟨S, f, hf⟩ := h
  exact ⟨⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (ψ g) hv⟩,
    ⟨f.toLinearMap, fun g => f.isIntertwining' (ψ g)⟩, hf⟩

def piTensorBoolEquiv {R a b : Type} [CommRing R] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {X : Bool → Type} [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)]
    (F : ∀ j, Representation ℂ (GL (Two a b j) R) (X j)) :
    Representation.Equiv ((piTensor F).comp (leviTwo R a b).toMonoidHom :
      Representation ℂ (GL a R × GL b R) (⨂[ℂ] j, X j)) (extTensor (F false) (F true)) :=
  .mk (Exponents.boolTensorEquiv (X := X)) fun g => by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    show Exponents.boolTensorEquiv (X := X) (piTensor F (leviTwo R a b g) (PiTensorProduct.tprod ℂ x)) =
      extTensor (F false) (F true) g (Exponents.boolTensorEquiv (X := X) (PiTensorProduct.tprod ℂ x))
    rw [piTensor_tprod, Exponents.boolTensorEquiv_tprod, Exponents.boolTensorEquiv_tprod, extTensor_tmul]
    rfl

theorem exists_extTensor_of_isSubquotient_jac₂ (hGL : GlobalTheory.Published.GeometricLemma) {n : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (hπ : IsSmooth π)
    (hirr : π.IsIrreducible) {a b : ℕ} (h : a + b = n) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (GL (Fin a) k × GL (Fin b) k) Y) (hτ : τ.IsIrreducible)
    (hs : IsSubquotient τ (jac₂ (stdSum h) π)) :
    ∃ (W W' : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : AddCommGroup W') (_ : Module ℂ W')
      (σ : Representation ℂ (GL (Fin a) k) W) (ρ : Representation ℂ (GL (Fin b) k) W'),
      IsSmooth σ ∧ σ.IsIrreducible ∧ IsSmooth ρ ∧ ρ.IsIrreducible ∧ IsSubquotient τ (extTensor σ ρ) := by
  let L := leviTwo k (Fin a) (Fin b)
  let τ' : Representation ℂ (Levi k (Two (Fin a) (Fin b))) Y := τ.comp L.symm.toMonoidHom
  have hτ' : τ'.IsIrreducible := isIrreducible_comp_surj τ _ L.symm.surjective hτ
  have hj : (jac₂ (stdSum h) π).comp L.symm.toMonoidHom = jac (two (stdSum h)) π :=
    MonoidHom.ext fun g => by simp [jac₂, L]
  have hs' : IsSubquotient τ' (jac (two (stdSum h)) π) := hj ▸ isSubquotient_comp' hs L.symm.toMonoidHom
  obtain ⟨φ⟩ := LocGL.nonempty_equiv_multiProd_one hπ (JacTensor.oneBlock n) fun _ _ => rfl
  have hinj : Function.Injective (jacMap (two (stdSum h)) φ.toIntertwiningMap) := by
    refine Function.LeftInverse.injective (g := jacMap (two (stdSum h)) φ.symm.toIntertwiningMap) fun x => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show Submodule.Quotient.mk (φ.symm (φ v)) = _
    simp
  have h1 : IsSubquotient τ' (jac (two (stdSum h)) (multiProd (JacTensor.oneBlock n) fun _ : Fin 1 => π)) :=
    hs'.trans (.of_injective _ hinj)
  obtain ⟨bm, f, g, t, -, ht⟩ := exists_cell_of_isSubquotient (hGL k).1 (hGL k).2
    (m' := Two (Fin a) (Fin b)) (JacTensor.oneBlock n) (two (stdSum h)) (fun _ => hπ)
    (fun _ => hasFiniteLength_of_isIrreducible hirr) hτ' h1
  let F : ∀ j : Bool, Representation ℂ (GL (Two (Fin a) (Fin b) j) k) _ :=
    fun j => multiProd (g j) fun i => (t i j).ρ
  have h2 : IsSubquotient (τ'.comp L.toMonoidHom) ((piTensor F).comp L.toMonoidHom) :=
    isSubquotient_comp' ht L.toMonoidHom
  have h2' : IsSubquotient τ (τ'.comp L.toMonoidHom) :=
    .of_injective ⟨LinearMap.id, fun g => rfl⟩ Function.injective_id
  have h3 : IsSubquotient ((piTensor F).comp L.toMonoidHom) (extTensor (F false) (F true)) :=
    .of_injective (piTensorBoolEquiv F).toIntertwiningMap (piTensorBoolEquiv F).toLinearEquiv.injective
  exact ⟨_, _, _, _, _, _, F false, F true,
    isSmooth_parInd _ _, JacTensor.isIrreducible_multiProd_fin_one (g false) fun i => t i false,
    isSmooth_parInd _ _, JacTensor.isIrreducible_multiProd_fin_one (g true) fun i => t i true, h2'.trans (h2.trans h3)⟩

theorem isIrreducible_extTensor {R a b W W' : Type} [CommRing R] [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (σ : Representation ℂ (GL a R) W) (ρ : Representation ℂ (GL b R) W')
    (hσ : σ.IsIrreducible) (hρ : ρ.IsIrreducible)
    (hSσ : ∀ φ : W →ₗ[ℂ] W, (∀ g x, φ (σ g x) = σ g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id)
    (hSρ : ∀ φ : W' →ₗ[ℂ] W', (∀ g x, φ (ρ g x) = ρ g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id) :
    (extTensor σ ρ).IsIrreducible := by
  have h1 : (piTensor (Exponents.twoRep σ ρ)).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun j => by cases j <;> assumption)
      (fun j => by cases j <;> assumption)
  have h2 := isIrreducible_comp_surj _ (leviTwo R a b).toMonoidHom (leviTwo R a b).surjective h1
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv (piTensorBoolEquiv (Exponents.twoRep σ ρ)) h2

theorem nontrivial_of_isIrreducible {G Y : Type} [Group G] [AddCommGroup Y] [Module ℂ Y]
    {τ : Representation ℂ G Y} (hτ : τ.IsIrreducible) : Nontrivial Y := by
  haveI : IsSimpleOrder (Subrepresentation τ) := hτ
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply (bot_ne_top : (⊥ : Subrepresentation τ) ≠ ⊤)
  ext v
  exact ⟨fun _ => trivial, fun _ => Subsingleton.elim v 0⟩

theorem exists_bijective_of_isSubquotient {G Y X : Type} [Group G] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G Y} {χ : Representation ℂ G X}
    (hτ : τ.IsIrreducible) (hχ : χ.IsIrreducible) (h : IsSubquotient τ χ) :
    ∃ ψ : τ.IntertwiningMap χ, Function.Bijective ψ := by
  obtain ⟨S, f, hf⟩ := h
  haveI : IsSimpleOrder (Subrepresentation χ) := hχ
  haveI := nontrivial_of_isIrreducible hτ

  let T : Subrepresentation χ := ⟨(LinearMap.ker f.toLinearMap).map S.toSubmodule.subtype, by
    rintro g _ ⟨v, hv, rfl⟩
    refine ⟨S.toRepresentation g v, ?_, rfl⟩
    have hv' : f v = 0 := hv
    show f (S.toRepresentation g v) = 0
    have h' := LinearMap.congr_fun (f.isIntertwining' g) v
    simp only [LinearMap.comp_apply] at h'
    rw [show f (S.toRepresentation g v) = τ g (f v) from h', hv', map_zero]⟩
  have hinj : Function.Injective f := by
    rcases IsSimpleOrder.eq_bot_or_eq_top T with hT | hT
    · refine (injective_iff_map_eq_zero f).2 fun v hv => ?_
      have : (v : X) ∈ T.toSubmodule := ⟨v, hv, rfl⟩
      rw [hT] at this
      exact Subtype.ext this
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (0 : Y)
      obtain ⟨v, rfl⟩ := hf y
      have : (v : X) ∈ T.toSubmodule := by rw [hT]; trivial
      obtain ⟨w, hw, hwv⟩ := this
      rw [Subtype.ext hwv] at hw
      exact hy hw
  have hS : S = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top S with hS | hS
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (0 : Y)
      obtain ⟨v, rfl⟩ := hf y
      have h0 : S.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule hS
      have : (v : X) ∈ (⊥ : Submodule ℂ X) := h0 ▸ v.2
      have hv : v = 0 := Subtype.ext ((Submodule.mem_bot ℂ).1 this)
      rw [hv, map_zero] at hy
      exact hy rfl
    · exact hS
  let e : S.toSubmodule ≃ₗ[ℂ] Y := LinearEquiv.ofBijective f.toLinearMap ⟨hinj, hf⟩
  refine ⟨⟨S.toSubmodule.subtype ∘ₗ e.symm.toLinearMap, fun g => ?_⟩, ?_, ?_⟩
  · ext y
    obtain ⟨v, rfl⟩ := e.surjective y
    have h' := LinearMap.congr_fun (f.isIntertwining' g) v
    simp only [LinearMap.comp_apply] at h'
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      Submodule.subtype_apply]
    have : e.symm (τ g (e v)) = S.toRepresentation g v := by
      rw [LinearEquiv.symm_apply_eq]
      exact h'.symm
    rw [this]
    rfl
  · exact Subtype.val_injective.comp e.symm.injective
  · intro x
    have hx : x ∈ S.toSubmodule := by rw [hS]; trivial
    exact ⟨e ⟨x, hx⟩, by simp⟩

end GlobalTheory.JacFactor

theorem GlobalTheory.JacFactor.exists_extTensor_equiv_of_quotient_jac₂ : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.ZelevinskyPolynomialRing →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → ∀ (a b : ℕ) (h : a + b = n) (Y : Type) [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (GL (Fin a) k × GL (Fin b) k) Y), IsSmooth τ → τ.IsIrreducible →
    ∀ q : (jac₂ (stdSum h) π).IntertwiningMap τ, Function.Surjective q →
    ∃ (W W' : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : AddCommGroup W') (_ : Module ℂ W')
      (σ : Representation ℂ (GL (Fin a) k) W) (ρ : Representation ℂ (GL (Fin b) k) W'),
      IsSmooth σ ∧ σ.IsIrreducible ∧ IsSmooth ρ ∧ ρ.IsIrreducible ∧
      ∃ ψ : τ.IntertwiningMap (extTensor σ ρ), Function.Bijective ψ := by
  intro hBZ hGL _ k _ _ _ _ n V _ _ π hπ hirr a b h Y _ _ τ _ hτ q hq
  obtain ⟨W, W', i1, i2, i3, i4, σ, ρ, hσs, hσ, hρs, hρ, hsub⟩ :=
    GlobalTheory.JacFactor.exists_extTensor_of_isSubquotient_jac₂ hGL π hπ hirr h τ hτ
      (IsSubquotient.of_surjective q hq)
  have hSσ := GlobalTheory.SchurAdm.schur_admissible _ (GlobalTheory.SplitWeil.KO k (Fin a)) GlobalTheory.SplitFlip.isOpen_KO
    GlobalTheory.SplitFlip.isCompact_KO W σ hσ ((hBZ k).1 (Fin a) W σ hσs hσ)
  have hSρ := GlobalTheory.SchurAdm.schur_admissible _ (GlobalTheory.SplitWeil.KO k (Fin b)) GlobalTheory.SplitFlip.isOpen_KO
    GlobalTheory.SplitFlip.isCompact_KO W' ρ hρ ((hBZ k).1 (Fin b) W' ρ hρs hρ)
  obtain ⟨ψ, hψ⟩ := GlobalTheory.JacFactor.exists_bijective_of_isSubquotient hτ
    (GlobalTheory.JacFactor.isIrreducible_extTensor σ ρ hσ hρ hSσ hSρ) hsub
  exact ⟨W, W', i1, i2, i3, i4, σ, ρ, hσs, hσ, hρs, hρ, ψ, hψ⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRankinSelbergPlaceSetSupersetTotallyCoStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodRankinSelbergPlaceSet_superset_totallyComplex : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (T : Finset (HeightOneSpectrum (𝓞 E))), ∃ T' : Finset (HeightOneSpectrum (𝓞 E)), T ⊆ T' ∧ IsGood T' := by
  first | (exact @GlobalTheory.RSNonvan.exists_isGood_superset_all) | (exact GlobalTheory.RSNonvan.exists_isGood_superset_all) | (intros; apply GlobalTheory.RSNonvan.exists_isGood_superset_all  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleSmoothQuotient
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.SmGL.IrrQuot

theorem exists_irreducible_smooth_quotient : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V), IsSmooth ρ → HasFiniteLength ρ → Nontrivial V →
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y),
      IsSmooth τ ∧ τ.IsIrreducible ∧ ∃ q : ρ.IntertwiningMap τ, Function.Surjective q := by
  intro G V _ _ _ _ _ ρ hsm hfl hnt
  haveI : WellFoundedGT (Subrepresentation ρ) := ((hasFiniteLength_iff_wellFounded ρ).1 hfl).1
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hmem : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← h] at hmem
    exact hx ((Submodule.mem_bot ℂ).1 hmem)
  obtain ⟨M, hM, -⟩ := (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subrepresentation ρ)).resolve_left hbt
  let W : Submodule ℂ V := M.toSubmodule
  have hW : ∀ g : G, W ≤ W.comap (ρ g) := fun g v hv => M.apply_mem_toSubmodule g hv
  let τ : Representation ℂ G (V ⧸ W) := ρ.quotient W hW
  have hτ : ∀ (g : G) (v : V), τ g (W.mkQ v) = W.mkQ (ρ g v) := fun g v => rfl
  let q : ρ.IntertwiningMap τ := ⟨W.mkQ, fun g => by ext v; rfl⟩
  have hq : Function.Surjective q := Submodule.mkQ_surjective W
  refine ⟨V ⧸ W, inferInstance, inferInstance, τ, ?_, ?_, q, hq⟩
  ·
    intro x
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W x
    let stab : (u : Type) → [AddCommGroup u] → [Module ℂ u] → (σ : Representation ℂ G u) → u → Subgroup G :=
      fun u _ _ σ y =>
        { carrier := {g | σ g y = y}
          mul_mem' := by
            intro a b ha hb
            simp only [Set.mem_setOf_eq] at ha hb ⊢
            rw [map_mul, Module.End.mul_apply, hb, ha]
          one_mem' := by simp
          inv_mem' := by
            intro a ha
            simp only [Set.mem_setOf_eq] at ha ⊢
            conv_lhs => rw [← ha]
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    have hle : stab V ρ v ≤ stab (V ⧸ W) τ (W.mkQ v) := by
      intro g hg
      change τ g (W.mkQ v) = W.mkQ v
      rw [hτ]
      exact congrArg W.mkQ hg
    exact Subgroup.isOpen_mono hle (hsm v)
  ·
    have hMtop : M ≠ ⊤ := hM.1
    refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
    · intro h
      apply hMtop
      apply Subrepresentation.toSubmodule_injective
      apply eq_top_iff.2
      intro v _
      have hmem : W.mkQ v ∈ (⊤ : Subrepresentation τ).toSubmodule := Submodule.mem_top
      rw [← h] at hmem
      exact (Submodule.Quotient.mk_eq_zero W).1 ((Submodule.mem_bot ℂ).1 hmem)
    · intro S
      let T : Subrepresentation ρ := ⟨S.toSubmodule.comap W.mkQ, fun g v hv => by
        change W.mkQ (ρ g v) ∈ S.toSubmodule
        rw [← hτ]
        exact S.apply_mem_toSubmodule g hv⟩
      have hMT : M ≤ T := by
        intro v hv
        change W.mkQ v ∈ S.toSubmodule
        rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).2 hv]
        exact S.toSubmodule.zero_mem
      rcases hM.le_iff.1 hMT with h | h
      · right
        apply Subrepresentation.toSubmodule_injective
        apply eq_top_iff.2
        intro x _
        obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W x
        have hvT : v ∈ T.toSubmodule := by rw [h]; exact Submodule.mem_top
        exact hvT
      · left
        apply Subrepresentation.toSubmodule_injective
        apply eq_bot_iff.2
        intro x hx
        obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W x
        have hvT : v ∈ T.toSubmodule := hx
        rw [h] at hvT
        exact (Submodule.mem_bot ℂ).2 (by rw [Submodule.mkQ_apply]; exact (Submodule.Quotient.mk_eq_zero W).2 hvT)

end GlobalTheory.SmGL.IrrQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsFinIdem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.PartsSpanProof

theorem exists_isFinIdem {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (h : IsPrimeIdem P e f) :
    ∃ v, IsFinIdem D v f := by
  rcases h with ⟨⟨⟨-, -, v, ε, hv, he⟩, -⟩, rfl⟩ | ⟨rfl, ⟨v, ε, hv, rfl⟩, -⟩
  · exact ⟨v, ε, hv, he⟩
  · exact ⟨v, ε, hv, rfl⟩

theorem exists_lift {H X : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X] (e : H →ₗ[ℂ] X)
    (he : Function.Injective e) (L : X →ₗ[ℂ] X) (hL : ∀ x, L (e x) ∈ LinearMap.range e) :
    ∃ h : Module.End ℂ H, ∀ x, e (h x) = L (e x) := by
  refine ⟨(LinearEquiv.ofInjective e he).symm.toLinearMap ∘ₗ (L ∘ₗ e).codRestrict _ hL, fun x => ?_⟩
  exact congrArg Subtype.val ((LinearEquiv.ofInjective e he).apply_symm_apply ⟨L (e x), hL x⟩)

theorem dualLab_dualLab (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab, List.map_reverse, List.map_map]

set_option maxHeartbeats 2000000 in

theorem partsSpan : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i S, PartsSpan R i S := by
  intro hC D G _ _ Pl0 T A Ks _ _ _ R F hL hF i S
  have hLP := GlobalTheory.LevelProduct.levProd_of_laws D G Pl0 T A Ks R F hL hF i
  have hS := (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hC R).2.2 i
  obtain ⟨inj, hr, hip⟩ := hL.models.HW i (sg0 D A)
  have hmem : ∀ x, (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := fun x => hr ▸ LinearMap.mem_range_self _ x
  have hlv := fun x v => ((GlobalTheory.MultMem.mem_mult_iff ..).1 (hmem x)).lev v
  let ι := {x : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D (Wc D i)) //
    Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) S
      x.1 x.2.1 x.2.2}
  have keep : ∀ x : ι, ∀ U ∈ R.Wall i (sg0 D A), heckeOn (R.MW i (sg0 D A)) x.1.2.2 U ∈ R.Wall i (sg0 D A) := by
    rintro ⟨⟨P, d, B⟩, e, f, ϖ, α, -, hP, -, -, -, -, -, hα, -, hB, hc⟩ U hU
    obtain ⟨v, hv⟩ := exists_isFinIdem hP
    exact GlobalTheory.LocalHeckeLevel.heckeOn_mem_wall hLP v f hv α hα B hB hc U hU
  have hex : ∀ x : ι, ∃ h : Module.End ℂ (R.HW i (sg0 D A)).H, ∀ y,
      (R.HW i (sg0 D A)).e (h y) = heckeOn (R.MW i (sg0 D A)) x.1.2.2 ((R.HW i (sg0 D A)).e y) :=
    fun x => exists_lift _ inj _ fun y => hr ▸ keep x _ (hmem y)
  choose op hop using hex
  have hcomm : Formalism.L2.Col.PairComm op := fun x x' => by
    refine LinearMap.ext fun y => inj ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hop, hop, hop, hop]
    exact MultilinearMap.ext fun v => GlobalTheory.SphericalOps.comm_heckeLin (J := levW R i)
      (GlobalTheory.HeckeAdjoint.realUnif D _) x.2 x'.2 (hlv y v)
  have hadj : ∀ x : ι, ∃ x', op x' = LinearMap.adjoint (op x) := by
    intro x
    obtain ⟨B', hB', -⟩ := GlobalTheory.SphericalOps.exists_dual (J := levW R i) (GlobalTheory.HeckeAdjoint.realUnif D x.1.1) x.2
    let x' : ι := ⟨(x.1.1, dualLab x.1.2.1, B'), hB'⟩
    refine ⟨x', ?_⟩
    rw [LinearMap.eq_adjoint_iff]
    intro a b
    rw [hip, hip, hop, hop]
    unfold ipAt
    congr 1
    exact GlobalTheory.HeckeAdjoint.ipM_heckeOn_dualLab D (Wc D i) _ R.θ (R.MW i (sg0 D A)) (levW R i) _ S (R.νW i) (R.fdW i)
      hL.models.inf (hL.models.νW i).1.1 (hL.models.νW i).2 hS x.1.1 (dualLab x.1.2.1) B' x.1.2.2 hB'
      (by rw [dualLab_dualLab]; exact x.2) _ (hmem a) _ (hmem b) (keep x' _ (hmem a)) (keep x _ (hmem b))
  obtain ⟨h1, h2, -⟩ := GlobalTheory.normalFamily_orthogonal_decomposition op hcomm hadj
  classical
  unfold PartsSpan
  refine eq_top_iff.2 (h2 ▸ iSup_le fun y => ?_)
  refine le_iSup_of_le (fun P d => if h : ∃ B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) S P d B then y ⟨(P, d, h.choose), h.choose_spec⟩ else 0) ?_
  intro x hx
  rw [h1, Submodule.mem_iInf] at hx
  show (R.HW i (sg0 D A)).e x ∈ partFull _ _ _ _ _ _
  unfold partFull
  refine Submodule.mem_inf.2 ⟨hmem x, ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]
  intro P d B hB
  have hE : ∃ B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) S P d B := ⟨B, hB⟩
  rw [dif_pos hE]
  have e1 := Module.End.mem_eigenspace_iff.1 (hx ⟨(P, d, hE.choose), hE.choose_spec⟩)
  have e2 := congrArg (R.HW i (sg0 D A)).e e1
  rw [hop, map_smul] at e2
  rw [← e2]
  exact MultilinearMap.ext fun v => GlobalTheory.SphericalOps.labelUnique (J := levW R i) (GlobalTheory.HeckeAdjoint.realUnif D)
    P d B _ hB hE.choose_spec _ (hlv x v)

end GlobalTheory.PartsSpanProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalCompatibilityAllStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_global_compatibility_all : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → GlobalTheory.HubX.LgcG D := by
  first | exact @GlobalTheory.HubX.lgcG_of_adm | exact GlobalTheory.HubX.lgcG_of_adm | (intros; apply GlobalTheory.HubX.lgcG_of_adm <;> assumption)
end

