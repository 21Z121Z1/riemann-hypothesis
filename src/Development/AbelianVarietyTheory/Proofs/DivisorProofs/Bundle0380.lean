import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0351
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0313
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0130
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0143
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0300
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0346
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateInCell
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem finite_det_line_zero {F E : Type} [Field F] [Field E] [Algebra F E] {ν : Type} [Fintype ν] [DecidableEq ν]
    (A B : Matrix ν ν E) (r₀ : F) (h : (A + algebraMap F E r₀ • B).det ≠ 0) :
    {r : F | (A + algebraMap F E r • B).det = 0}.Finite := by
  set M : Matrix ν ν (Polynomial E) := A.map Polynomial.C + (Polynomial.X : Polynomial E) • B.map Polynomial.C with hM
  have hev : ∀ x : E, M.det.eval x = (A + x • B).det := by
    intro x
    have h1 := RingHom.map_det (Polynomial.evalRingHom x) M
    rw [Polynomial.coe_evalRingHom] at h1
    rw [h1]
    congr 1
    ext i j
    simp [hM]
    ring
  have hp : M.det ≠ 0 := by
    intro h0
    apply h
    rw [← hev, h0, Polynomial.eval_zero]
  have hfin := Polynomial.finite_setOfPred_isRoot hp
  refine (hfin.preimage (f := algebraMap F E) (algebraMap F E).injective.injOn).subset ?_
  intro r hr
  change M.det.eval _ = 0
  rw [hev]
  exact hr

theorem exists_herm_transversal (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E)
    (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (s : Finset (UG c (stdJ ν E))) :
    ∃ t : Matrix ν ν E, (t.map c)ᵀ = t ∧ ∀ g ∈ s, ((mat c g).toBlocks₂₁ + (mat c g).toBlocks₂₂ * t).det ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by ext i j; simp, by simp⟩
  | insert g s _ ih =>
    obtain ⟨t₀, ht₀, h₀⟩ := ih
    obtain ⟨t₁, ht₁, h₁⟩ := GlobalTheory.T.exists_hermitian_splitUnitary_lowerBlock_invertible F E c δ hE ν g
    have key : ∀ k ∈ insert g s, {r : F | (((mat c k).toBlocks₂₁ + (mat c k).toBlocks₂₂ * t₀) +
        algebraMap F E r • ((mat c k).toBlocks₂₂ * (t₁ - t₀))).det = 0}.Finite := by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · refine finite_det_line_zero _ _ 1 ?_
        rw [map_one, one_smul, add_assoc, ← Matrix.mul_add, add_sub_cancel]
        exact h₁
      · refine finite_det_line_zero _ _ 0 ?_
        rw [map_zero, zero_smul, add_zero]
        exact h₀ k hk
    have hfin := Set.Finite.biUnion (insert g s).finite_toSet key
    obtain ⟨r, hr⟩ := hfin.exists_notMem
    refine ⟨t₀ + algebraMap F E r • (t₁ - t₀), ?_, ?_⟩
    · ext i j
      have e₀ : c (t₀ j i) = t₀ i j := congrFun (congrFun ht₀ i) j
      have e₁ : c (t₁ j i) = t₁ i j := congrFun (congrFun ht₁ i) j
      simp [e₀, e₁]
    · intro k hk h0
      apply hr
      refine Set.mem_biUnion (Finset.mem_coe.mpr hk) ?_
      rw [Matrix.mul_add, Matrix.mul_smul, ← add_assoc] at h0
      exact h0

theorem exists_translate_inCell : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (s : Finset (UG c (stdJ ν E))),
    ∃ u : UG c (stdJ ν E), ∀ g ∈ s, InCell c (g * u) := by
  intro F _ _ E _ _ c δ hE ν _ _ s
  obtain ⟨t, ht, h⟩ := exists_herm_transversal F E c δ hE ν s
  let u : UG c (stdJ ν E) :=
    ⟨⟨fromBlocks 1 0 t 1, fromBlocks 1 0 (-t) 1, by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩, by
      rw [mem_UG_iff]
      have h0 : (0 : Matrix ν ν E).map c = 0 := Matrix.map_zero _ (map_zero c)
      have h1 : (1 : Matrix ν ν E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
      simp [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, h0, h1, ht]⟩
  refine ⟨u, fun g hg => (GlobalTheory.T.inCell_iff_det_lower_left_block_ne_zero F E c δ hE ν _).mpr ?_⟩
  have e : mat c (g * u) = mat c g * fromBlocks 1 0 t 1 := rfl
  rw [e, ← fromBlocks_toBlocks (mat c g), fromBlocks_multiply, toBlocks_fromBlocks₂₁, Matrix.mul_one]
  exact h g hg

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitEqOfStableLattices
section
open Polynomial Matrix GlobalTheory.LatOrb

noncomputable section

namespace GlobalTheory.LatOrb.Stab

theorem polyStable {O K : Type} [CommRing O] [Field K] [Algebra O K] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) (M : Submodule O (Fin n → K))
    (hM : ∀ v ∈ M, γ *ᵥ v ∈ M) (r : O[X]) :
    ∀ v ∈ M, aeval γ (r.map (algebraMap O K)) *ᵥ v ∈ M := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq =>
    intro v hv
    rw [Polynomial.map_add, map_add, Matrix.add_mulVec]
    exact M.add_mem (hp v hv) (hq v hv)
  | monomial k a =>
    intro v hv
    have hpow : ∀ v ∈ M, (γ ^ k) *ᵥ v ∈ M := by
      induction k with
      | zero => intro v hv; simpa using hv
      | succ k ih =>
        intro v hv
        rw [pow_succ, ← Matrix.mulVec_mulVec]
        exact ih _ (hM v hv)
    rw [Polynomial.map_monomial, aeval_monomial, ← Matrix.mulVec_mulVec,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec,
      algebraMap_smul]
    exact M.smul_mem a (hpow v hv)

end GlobalTheory.LatOrb.Stab

namespace GlobalTheory.LatOrb.Stab

theorem exists_unit_eq_matLat : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ M₁ M₂ : Submodule O (Fin n → K), IsLatV O M₁ → IsLatV O M₂ →
    (∀ v ∈ M₁, γ *ᵥ v ∈ M₁) → (∀ v ∈ M₂, γ *ᵥ v ∈ M₂) →
    ∃ p : K[X], IsUnit (aeval γ p) ∧ M₂ = matLat O (aeval γ p) M₁ := by
  intro O K _ _ _ _ _ _ _ n P₀ hcop γ hchar M₁ M₂ hL₁ hL₂ hs₁ hs₂
  have hsep : γ.charpoly.Separable := by rw [hchar]; exact Polynomial.Separable.map hcop
  obtain ⟨v₀, hv₀⟩ := GlobalTheory.T.exists_cyclicVector_of_separable_charpoly' n γ hsep
  obtain ⟨A, hA⟩ : ∃ A : Subalgebra K (Matrix (Fin n) (Fin n) K), A = Algebra.adjoin K {γ} :=
    ⟨_, rfl⟩
  have memA : ∀ a : Matrix (Fin n) (Fin n) K, a ∈ A ↔ ∃ p : K[X], aeval γ p = a := by
    intro a; rw [hA, Algebra.adjoin_singleton_eq_range_aeval]; rfl
  have commA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    obtain ⟨p, rfl⟩ := (memA a).1 ha
    obtain ⟨q, rfl⟩ := (memA b).1 hb
    rw [← map_mul, ← map_mul, mul_comm]
  letI : CommRing A := { A.toRing with mul_comm := fun x y => Subtype.ext (commA _ x.2 _ y.2) }
  haveI : Module.Finite K A := inferInstance
  haveI : IsReduced A := by
    refine ⟨fun a ⟨m, hm⟩ => ?_⟩
    obtain ⟨f, hf⟩ := (memA a).1 a.2
    have h0 : aeval γ (f ^ m) = 0 := by
      rw [map_pow, hf]
      exact congrArg Subtype.val hm
    have hsq : Squarefree (minpoly K γ) :=
      (hsep.of_dvd (Matrix.minpoly_dvd_charpoly γ)).squarefree
    have h1 : minpoly K γ ∣ f := hsq.isRadical m f (minpoly.dvd K γ h0)
    apply Subtype.ext
    rw [← hf]
    exact (minpoly.dvd_iff).1 h1

  let φ : A →ₗ[K] (Fin n → K) :=
    { toFun := fun a => (a : Matrix (Fin n) (Fin n) K) *ᵥ v₀
      map_add' := fun a b => by simp [Matrix.add_mulVec]
      map_smul' := fun c a => by simp [Matrix.smul_mulVec] }
  have hφ : ∀ a : A, φ a = (a : Matrix (Fin n) (Fin n) K) *ᵥ v₀ := fun _ => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    rw [hφ] at ha
    apply Subtype.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro u
    obtain ⟨p, rfl⟩ := hv₀ u
    obtain ⟨q, hq⟩ := (memA a).1 a.2
    change (a : Matrix (Fin n) (Fin n) K) *ᵥ (aeval γ p *ᵥ v₀) = (0 : Matrix (Fin n) (Fin n) K) *ᵥ _
    rw [Matrix.mulVec_mulVec, ← hq, ← map_mul, mul_comm, map_mul, hq, ← Matrix.mulVec_mulVec, ha,
      Matrix.mulVec_zero, Matrix.zero_mulVec]
  have hsurj : Function.Surjective φ := by
    intro u
    obtain ⟨p, rfl⟩ := hv₀ u
    exact ⟨⟨aeval γ p, (memA _).2 ⟨p, rfl⟩⟩, rfl⟩
  let e : A ≃ₗ[K] (Fin n → K) := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : ∀ a : A, e a = (a : Matrix (Fin n) (Fin n) K) *ᵥ v₀ := fun _ => rfl
  let eO : A ≃ₗ[O] (Fin n → K) := e.restrictScalars O
  let J : Submodule O (Fin n → K) → Submodule O A := fun M => M.map (eO.symm : (Fin n → K) →ₗ[O] A)
  have memJ : ∀ M y, y ∈ J M ↔ (y : Matrix (Fin n) (Fin n) K) *ᵥ v₀ ∈ M := by
    intro M y
    simp only [J, Submodule.mem_map_equiv]
    rfl
  have latJ : ∀ M, IsLatV O M → GlobalTheory.UnitLemma.IsLat O K (J M) := by
    intro M hM
    refine ⟨hM.1.map _, ?_⟩
    have hcoe : ((J M : Submodule O A) : Set A) = (e.symm : (Fin n → K) →ₗ[K] A) '' (M : Set _) := by
      ext y; simp [J, Submodule.mem_map]; rfl
    rw [hcoe, Submodule.span_image, hM.2, Submodule.map_top, LinearEquiv.range]
  have stJ : ∀ M, (∀ v ∈ M, γ *ᵥ v ∈ M) →
      ∀ a ∈ integralClosure O A, ∀ y ∈ J M, a * y ∈ J M := by
    intro M hM a ha y hy
    have hint : IsIntegral O (a : Matrix (Fin n) (Fin n) K) :=
      (ha : IsIntegral O a).map (A.val.restrictScalars O)
    obtain ⟨p, hp⟩ := (memA _).1 a.2
    rw [← hp] at hint
    obtain ⟨r, hr⟩ := GlobalTheory.T.integral_aeval_eq_aeval_map_of_coprime_charpoly n P₀ hcop γ hchar p hint
    rw [memJ] at hy ⊢
    change ((a : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K)) *ᵥ v₀ ∈ M
    rw [← Matrix.mulVec_mulVec, ← hp, hr]
    exact polyStable γ M hM r _ hy
  haveI : IsPrincipalIdealRing (integralClosure O A) :=
    GlobalTheory.UnitLemma.PrincipalLatDVR.isPrincipalIdealRing_integralClosure (E := K)
  set Λ : Submodule O A := Subalgebra.toSubmodule (integralClosure O A)

  have back : ∀ M (c : Aˣ), J M = GlobalTheory.UnitLemma.mulLat O (c : A) Λ →
      M = matLat O ((c : A) : Matrix (Fin n) (Fin n) K) (Λ.map (eO : A →ₗ[O] (Fin n → K))) := by
    intro M c hc
    ext v
    obtain ⟨y, rfl⟩ := hsurj v
    rw [mem_matLat]
    have h1 : φ y ∈ M ↔ y ∈ J M := by rw [memJ]; rfl
    rw [h1, hc]
    simp only [GlobalTheory.UnitLemma.mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨eO l, ⟨l, hl, rfl⟩, ?_⟩
      change ((c : A) : Matrix (Fin n) (Fin n) K) *ᵥ ((l : Matrix (Fin n) (Fin n) K) *ᵥ v₀) =
        (((c : A) * l : A) : Matrix (Fin n) (Fin n) K) *ᵥ v₀
      rw [Matrix.mulVec_mulVec]; rfl
    · rintro ⟨_, ⟨l, hl, rfl⟩, hv⟩
      refine ⟨l, hl, hinj ?_⟩
      rw [← hv]
      change (((c : A) * l : A) : Matrix (Fin n) (Fin n) K) *ᵥ v₀ =
        ((c : A) : Matrix (Fin n) (Fin n) K) *ᵥ ((l : Matrix (Fin n) (Fin n) K) *ᵥ v₀)
      rw [Matrix.mulVec_mulVec]; rfl
  obtain ⟨a₁, h₁⟩ :=
    GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_of_isPrincipalIdealRing (E := K) (J M₁) (latJ M₁ hL₁) (stJ M₁ hs₁)
  obtain ⟨a₂, h₂⟩ :=
    GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_of_isPrincipalIdealRing (E := K) (J M₂) (latJ M₂ hL₂) (stJ M₂ hs₂)
  obtain ⟨p, hp⟩ := (memA _).1 ((a₂ * a₁⁻¹ : Aˣ) : A).2
  refine ⟨p, ?_, ?_⟩
  · rw [hp]; exact (Units.isUnit (a₂ * a₁⁻¹)).map A.val
  · rw [back M₂ a₂ h₂, back M₁ a₁ h₁, ← matLat_mul, hp]
    congr 1
    change ((a₂ : A) : Matrix (Fin n) (Fin n) K) = (((a₂ * a₁⁻¹ : Aˣ) : A) * (a₁ : A) : A).1
    rw [← Units.val_mul, inv_mul_cancel_right]

end GlobalTheory.LatOrb.Stab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodActionModelOfIsColimitFiltered
section
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.TorsorColim

theorem exists_common_under {K : Type} [SmallCategory K] [IsFiltered K] {I : Type} [Finite I]
    (k : K) (l : I → K) (f : ∀ i, k ⟶ l i) :
    ∃ (m : K) (p : k ⟶ m) (r : ∀ i, l i ⟶ m), ∀ i, f i ≫ r i = p := by
  classical
  letI := Fintype.ofFinite I
  obtain ⟨c'⟩ := IsFiltered.cocone_nonempty (WidePushoutShape.wideSpan k l f)
  exact ⟨c'.pt, c'.ι.app none, fun i => c'.ι.app (some i), fun i => c'.w (.init i)⟩

theorem exists_stage_eq {K : Type} [SmallCategory K] [IsFiltered K] {I : Type} [Finite I]
    {R S : CommRingCat.{0}} (E : K ⥤ CommRingCat.{0}) (α : (Functor.const _).obj R ⟶ E)
    (φ : R ⟶ S) (c : Cocone E) (hc : IsColimit c) (hφ : φ.hom.EssFiniteType) {k : K}
    (a b : I → (S ⟶ E.obj k)) (ha : ∀ i, φ ≫ a i = α.app k) (hb : ∀ i, φ ≫ b i = α.app k)
    (hab : ∀ i, a i ≫ c.ι.app k = b i ≫ c.ι.app k) :
    ∃ (m : K) (p : k ⟶ m), ∀ i, a i ≫ E.map p = b i ≫ E.map p := by
  choose l f₁ f₂ h using fun i => RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit R E α φ c hc
    hφ (a i) (ha i) (b i) (hb i) (hab i)
  obtain ⟨m, p, r, hr⟩ := exists_common_under k (fun i => IsFiltered.coeq (f₁ i) (f₂ i))
    (fun i => f₁ i ≫ IsFiltered.coeqHom (f₁ i) (f₂ i))
  refine ⟨m, p, fun i => ?_⟩
  have h2 : (f₂ i ≫ IsFiltered.coeqHom (f₁ i) (f₂ i)) ≫ r i = p := by
    rw [← IsFiltered.coeq_condition]; exact hr i
  conv_lhs => rw [← hr i]
  conv_rhs => rw [← h2]
  simp only [E.map_comp, Category.assoc]
  rw [reassoc_of% (h i)]

theorem exists_stage_factor {K : Type} [SmallCategory K] [IsFiltered K] {I : Type} [Finite I]
    {R S : CommRingCat.{0}} (E : K ⥤ CommRingCat.{0}) (α : (Functor.const _).obj R ⟶ E)
    (φ : R ⟶ S) (c : Cocone E) (hc : IsColimit c) (hφ : φ.hom.FinitePresentation)
    (a : I → (S ⟶ c.pt)) (ha : ∀ i k, φ ≫ a i = α.app k ≫ c.ι.app k) :
    ∃ (m : K) (s : I → (S ⟶ E.obj m)), ∀ i, φ ≫ s i = α.app m ∧ s i ≫ c.ι.app m = a i := by
  classical
  choose l s h₁ h₂ using fun i => RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit R E α φ c
    hc hφ (a i) (ha i)
  letI := Fintype.ofFinite I
  obtain ⟨m, hm⟩ := IsFiltered.sup_objs_exists (Finset.univ.image l)
  have r : ∀ i, l i ⟶ m := fun i => (hm (Finset.mem_image_of_mem l (Finset.mem_univ i))).some
  refine ⟨m, fun i => s i ≫ E.map (r i), fun i => ⟨?_, ?_⟩⟩
  · rw [reassoc_of% (h₁ i), ← α.naturality]
    exact Category.id_comp _
  · rw [Category.assoc, c.w, ← h₂]

theorem exists_stage_action {K : Type} [SmallCategory K] [IsFiltered K] {G : Type} [Monoid G]
    [Finite G] {R S : CommRingCat.{0}} (P E : K ⥤ CommRingCat.{0})
    (β : ∀ k, R ⟶ P.obj k) (φ : R ⟶ S) (hφ : φ.hom.FinitePresentation)
    (u : P ⟶ E) (v : (Functor.const _).obj S ⟶ E)
    (hpo : ∀ k, IsPushout φ (β k) (v.app k) (u.app k))
    (c : Cocone E) (hc : IsColimit c) (τ : G → (c.pt ⟶ c.pt)) (τ1 : τ 1 = 𝟙 _)
    (τm : ∀ g h, τ (g * h) = τ h ≫ τ g)
    (τu : ∀ g k, u.app k ≫ c.ι.app k ≫ τ g = u.app k ≫ c.ι.app k) :
    ∃ (m : K) (σ : G → (E.obj m ⟶ E.obj m)), σ 1 = 𝟙 _ ∧ (∀ g h, σ (g * h) = σ h ≫ σ g) ∧
      (∀ g, u.app m ≫ σ g = u.app m) ∧ ∀ g, σ g ≫ c.ι.app m = c.ι.app m ≫ τ g := by
  let α : (Functor.const K).obj R ⟶ E := (Functor.const K).map φ ≫ v
  let w : ∀ k, S ⟶ E.obj k := fun k => v.app k
  let ι : ∀ k, E.obj k ⟶ c.pt := fun k => c.ι.app k
  have hα : ∀ k, α.app k = φ ≫ w k := fun k => rfl
  have hι : ∀ {k l} (f : k ⟶ l), E.map f ≫ ι l = ι k := fun f => c.w f
  have hw : ∀ {k l} (f : k ⟶ l), w k ≫ E.map f = w l := fun f =>
    (v.naturality f).symm.trans (Category.id_comp _)
  have hpo' : ∀ k, IsPushout φ (β k) (w k) (u.app k) := hpo
  have τu' : ∀ g k, u.app k ≫ ι k ≫ τ g = u.app k ≫ ι k := τu
  have k₀ : K := IsFiltered.nonempty.some
  have hwι : ∀ k, w k ≫ ι k = w k₀ ≫ ι k₀ := fun k => by
    rw [← hι (IsFiltered.leftToMax k k₀), ← hι (IsFiltered.rightToMax k k₀), reassoc_of% hw,
      reassoc_of% hw]
  obtain ⟨k, s, hs⟩ := exists_stage_factor E α φ c hc hφ (fun g : G => w k₀ ≫ ι k₀ ≫ τ g)
    (fun g k => by
      change φ ≫ w k₀ ≫ ι k₀ ≫ τ g = (φ ≫ w k) ≫ ι k
      rw [← reassoc_of% (hwι k), (hpo' k).w, reassoc_of% (hpo' k).w, τu', Category.assoc])
  have hs1 : ∀ g, φ ≫ s g = φ ≫ w k := fun g => (hs g).1
  have hs2 : ∀ g, s g ≫ ι k = w k₀ ≫ ι k₀ ≫ τ g := fun g => (hs g).2
  let σ : ∀ {l} (_ : k ⟶ l), G → (E.obj l ⟶ E.obj l) := fun {l} f g =>
    (hpo' l).desc (s g ≫ E.map f) (u.app l) (by
      rw [reassoc_of% hs1, hw, (hpo' l).w])
  have σw : ∀ {l} (f : k ⟶ l) g, w l ≫ σ f g = s g ≫ E.map f := fun f g => (hpo' _).inl_desc _ _ _
  have σu : ∀ {l} (f : k ⟶ l) g, u.app l ≫ σ f g = u.app l := fun f g => (hpo' _).inr_desc _ _ _
  have σι : ∀ {l} (f : k ⟶ l) g, σ f g ≫ ι l = ι l ≫ τ g := fun {l} f g => by
    apply (hpo' l).hom_ext
    · rw [reassoc_of% σw, hι, hs2, reassoc_of% (hwι l)]
    · rw [reassoc_of% σu, τu']
  have σmap : ∀ {l} (f : k ⟶ l) g, σ (𝟙 k) g ≫ E.map f = E.map f ≫ σ f g := fun {l} f g => by
    apply (hpo' k).hom_ext
    · rw [reassoc_of% σw, reassoc_of% hw, σw, E.map_id, Category.id_comp]
    · rw [reassoc_of% σu, ← u.naturality_assoc, σu, u.naturality]
  obtain ⟨m, p, hp⟩ := exists_stage_eq (I := Option (G × G)) E α φ c hc
    (RingHom.FiniteType.essFiniteType (RingHom.FiniteType.of_finitePresentation hφ)) (k := k)
    (fun i => i.elim (s 1) (fun x => s (x.1 * x.2)))
    (fun i => i.elim (w k) (fun x => s x.2 ≫ σ (𝟙 k) x.1))
    (by
      rintro (_ | x)
      · exact hs1 _
      · exact hs1 _)
    (by
      rintro (_ | x)
      · rfl
      · change φ ≫ s x.2 ≫ σ (𝟙 k) x.1 = φ ≫ w k
        rw [reassoc_of% hs1, σw, E.map_id, Category.comp_id, hs1])
    (by
      rintro (_ | x)
      · change s 1 ≫ ι k = w k ≫ ι k
        rw [hs2, τ1, Category.comp_id, hwι k]
      · change s (x.1 * x.2) ≫ ι k = (s x.2 ≫ σ (𝟙 k) x.1) ≫ ι k
        rw [Category.assoc, σι, reassoc_of% hs2, hs2, τm])
  refine ⟨m, σ p, ?_, fun g h => ?_, σu p, σι p⟩
  · apply (hpo' m).hom_ext
    · rw [σw, Category.comp_id, ← hw p]
      exact hp none
    · rw [σu, Category.comp_id]
  · apply (hpo' m).hom_ext
    · rw [σw, reassoc_of% σw, ← σmap, ← Category.assoc]
      exact hp (some (g, h))
    · rw [σu, reassoc_of% σu, σu]

theorem finitePresentation_of_isPushout {R S R' S' : CommRingCat.{0}} {φ : R ⟶ S} {β : R ⟶ R'}
    {v : S ⟶ S'} {u : R' ⟶ S'} (h : IsPushout φ β v u) (hφ : φ.hom.FinitePresentation) :
    u.hom.FinitePresentation := by
  algebraize [φ.hom, β.hom, v.hom, u.hom, v.hom.comp φ.hom]
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  have : Algebra.IsPushout R S R' S' := CommRingCat.isPushout_iff_isPushout.1 h
  exact RingHom.finitePresentation_isStableUnderBaseChange R S R' S' hφ

theorem exists_algEquiv_of_isPushout {R C B D : Type} [CommRing R] [CommRing C] [CommRing B]
    [CommRing D] [Algebra R C] [Algebra R B] [Algebra C D] (ι : B →+* D)
    (h : IsPushout (CommRingCat.ofHom (algebraMap R C)) (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom (algebraMap C D)) (CommRingCat.ofHom ι)) :
    ∃ e : C ⊗[R] B ≃ₐ[C] D, ∀ x y, e (x ⊗ₜ y) = algebraMap C D x * ι y := by
  algebraize [ι, (algebraMap C D).comp (algebraMap R C)]
  have : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  have : Algebra.IsPushout R C B D := CommRingCat.isPushout_iff_isPushout.1 h
  exact ⟨Algebra.IsPushout.equiv R C B D, fun x y => Algebra.IsPushout.equiv_tmul R C B D x y⟩

theorem exists_action_model_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A] (D : Type) [CommRing D] [Algebra c.pt D]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[c.pt] D)),
    letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
    Nonempty (c.pt ⊗[F.obj j] A ≃ₐ[c.pt] D) →
    ∃ (k : J) (B : Type) (_ : CommRing B) (_ : Algebra (F.obj k) B)
      (_ : Algebra.FinitePresentation (F.obj k) B)
      (actB : Multiplicative (ZMod q) →* (B ≃ₐ[F.obj k] B)),
      letI : Algebra (F.obj k) c.pt := (c.ι.app k).hom.toAlgebra;
      ∃ e : c.pt ⊗[F.obj k] B ≃ₐ[c.pt] D, ∀ (g : Multiplicative (ZMod q)) (x : c.pt ⊗[F.obj k] B),
        e (GlobalTheory.TorsorColim.bcAct c.pt actB g x) = act g (e x) := by
  intro J _ _ F c hc q hq j A _ _ _ D _ _ act
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  rintro ⟨e₀⟩
  haveI : NeZero q := ⟨hq.ne'⟩
  let φ : F.obj j ⟶ CommRingCat.of A := CommRingCat.ofHom (algebraMap (F.obj j) A)
  have hφ : φ.hom.FinitePresentation := RingHom.finitePresentation_algebraMap.2 inferInstance
  let g₀ : c.pt ⟶ CommRingCat.of D := CommRingCat.ofHom (algebraMap c.pt D)
  let h₀ : CommRingCat.of A ⟶ CommRingCat.of D :=
    CommRingCat.ofHom (e₀.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := F.obj j) (A := c.pt) (B := A)).toRingHom)
  let ιc : ∀ k, F.obj k ⟶ c.pt := fun k => c.ι.app k
  have hsq : IsPushout φ (ιc j) h₀ g₀ := by
    refine (CommRingCat.isPushout_tensorProduct (F.obj j) c.pt A).flip.of_iso (Iso.refl _)
      (Iso.refl _) (Iso.refl _) e₀.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · ext x
      exact e₀.commutes x
  obtain ⟨E, ι, u, v, ⟨hE⟩, hk⟩ :=
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J F c hc j _ _ φ h₀ g₀ hsq
  let τ : Multiplicative (ZMod q) → (CommRingCat.of D ⟶ CommRingCat.of D) := fun g =>
    CommRingCat.ofHom (act g).toRingEquiv.toRingHom
  have hτ : ∀ g, g₀ ≫ τ g = g₀ := fun g => by
    ext x
    exact (act g).commutes x
  let ι' : ∀ k, E.obj k ⟶ CommRingCat.of D := fun k => ι.app k
  let u' : ∀ k : Under j, F.obj k.right ⟶ E.obj k := fun k => u.app k
  let v' : ∀ k : Under j, CommRingCat.of A ⟶ E.obj k := fun k => v.app k
  have hu : ∀ k, u' k ≫ ι' k = ιc k.right ≫ g₀ := fun k => (hk k).2.2
  have hv : ∀ k, v' k ≫ ι' k = h₀ := fun k => (hk k).2.1
  have hpo : ∀ k : Under j, IsPushout φ (F.map k.hom) (v' k) (u' k) := fun k => (hk k).1
  obtain ⟨m, σ, σ1, σm, σu, σι⟩ := exists_stage_action (Under.forget j ⋙ F) E
    (fun k => F.map k.hom) φ hφ u v hpo (Cocone.mk _ ι) hE τ
    (by
      ext x
      change act 1 x = x
      simp)
    (fun g h => by
      ext x
      change act (g * h) x = act g (act h x)
      simp)
    (fun g k => by
      change u' k ≫ ι' k ≫ τ g = u' k ≫ ι' k
      rw [reassoc_of% hu, hτ, hu])
  letI : Algebra (F.obj m.right) (E.obj m) := (u' m).hom.toAlgebra
  letI : Algebra (F.obj m.right) c.pt := (c.ι.app m.right).hom.toAlgebra
  let σ' : Multiplicative (ZMod q) →* (E.obj m →ₐ[F.obj m.right] E.obj m) :=
    { toFun := fun g => ⟨(σ g).hom, fun x => congr(($(σu g)).hom x)⟩
      map_one' := AlgHom.ext fun x => congr(($σ1).hom x)
      map_mul' := fun g h => AlgHom.ext fun x => congr(($(σm g h)).hom x) }
  have hsq' : IsPushout (u' m) (ιc m.right) (ι' m) g₀ := by
    have hcw : F.map m.hom ≫ ιc m.right = ιc j := c.w m.hom
    refine IsPushout.of_top ?_ (hu m) (hpo m)
    rw [hv]
    exact hcw ▸ hsq
  obtain ⟨e, he⟩ := exists_algEquiv_of_isPushout (R := F.obj m.right) (C := c.pt) (B := E.obj m)
    (D := D) (ι' m).hom hsq'.flip
  refine ⟨m.right, E.obj m, inferInstance, inferInstance,
    finitePresentation_of_isPushout (hpo m) hφ,
    (AlgEquiv.algHomUnitsEquiv _ _).toMonoidHom.comp σ'.toHomUnits, e, fun g x => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s b =>
    rw [bcAct_tmul, he, he, map_mul, AlgEquiv.commutes]
    congr 1
    exact congr(($(σι g)).hom b)

end GlobalTheory.TorsorColim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpGContinuousInv
section
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory

theorem expG_continuous_inv : ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ), inG ε Z →
    Continuous (fun t : ℝ => expG ε Z t) ∧
      ∀ t : ℝ, toM (expG ε Z t)⁻¹ = NormedSpace.exp (-((t : ℂ) • Z)) := by
  intro n ε Z hZ
  refine ⟨(Formalism.REAL.group_exponential_facts n ε Z hZ).2.2.1, fun t => ?_⟩
  have hmul : toM (expG ε Z t) * NormedSpace.exp (-((t : ℂ) • Z)) = 1 := by
    rw [Formalism.REAL.toM_expG ε Z t hZ]
    have h := Formalism.REAL.one_parameter_subgroup_holds n Z t (-t)
    have e : ((-t : ℝ) : ℂ) • Z = -((t : ℂ) • Z) := by push_cast; rw [neg_smul]
    rw [e, add_neg_cancel] at h
    simpa using h.symm
  exact Units.inv_eq_of_mul_eq_one_right hmul

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsuppMapDomainEqZeroAtFilteredStageStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsupp_mapDomain_eq_zero_at_filtered_stage : ∀ (Λ : Type 1) [AddCommGroup Λ] (J : Type) [SmallCategory J] [IsFiltered J] (P : J ⥤ Type) (Q : Type) (ι : ∀ j, P.obj j → Q), (∀ (j k : J) (f : j ⟶ k) (x : P.obj j), ι k (P.map f x) = ι j x) → (∀ j (x y : P.obj j), ι j x = ι j y → ∃ (k : J) (f : j ⟶ k), P.map f x = P.map f y) → ∀ j (x : P.obj j →₀ Λ), Finsupp.mapDomain (ι j) x = 0 → ∃ (k : J) (f : j ⟶ k), Finsupp.mapDomain (P.map f) x = 0 := by
  first | (exact @GlobalTheory.finsupp_mapDomain_eq_zero_at_stage) | (exact GlobalTheory.finsupp_mapDomain_eq_zero_at_stage) | (intros; apply GlobalTheory.finsupp_mapDomain_eq_zero_at_stage  <;> assumption)
end

