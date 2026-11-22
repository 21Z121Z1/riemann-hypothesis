import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0032
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0050
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0042
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0048
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0030
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0056
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1595
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1849
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1594
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1497
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1785
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1746
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PetEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieEigenLatticeLeSpanCmHomImages
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory.FlatCM.HomLat.LieSpan

section Over

variable {S S' : Scheme.{0}} {s : S' ⟶ S} {G B : Over S} {G' B' : Over S'} [GrpObj B] [GrpObj B'] [IsCommMonObj B]
  [IsCommMonObj B'] {φ : G'.left ⟶ G.left} {m : B'.left ⟶ B.left}

theorem one_over (w : φ ≫ G.hom = G'.hom ≫ s) (hm : IsGrpPullback B' B s m) :
    (1 : G' ⟶ B').left ≫ m = φ ≫ (1 : G ⟶ B).left := by
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hm G'.hom (G'.hom ≫ s) rfl
  let φ₀ : Over.mk (G'.hom ≫ s) ⟶ G := Over.homMk φ w
  have h1 := he 1
  rw [map_one, ← comp_one φ₀] at h1
  exact h1.symm

theorem prod_over (w : φ ≫ G.hom = G'.hom ≫ s) (hm : IsGrpPullback B' B s m) {I : Type} (t : Finset I)
    {x' : I → (G' ⟶ B')} {x : I → (G ⟶ B)} (h : ∀ i, (x' i).left ≫ m = φ ≫ (x i).left) :
    (∏ i ∈ t, x' i).left ≫ m = φ ≫ (∏ i ∈ t, x i).left := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using one_over w hm
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact FamDesc.exists_mul w hm (h a) ih

end Over

section Rel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R R' : Type} [CommRing R] [CommRing R']
  {j : R →+* R'} {A B : PAT H (Sp R)} {A' B' : PAT H (Sp R')} (mA : SABMap A'.t A.t (spMap j))
  (mB : SABMap B'.t B.t (spMap j))

theorem exists_linear_over {f : A.t.G ⟶ B.t.G} (hf : Serre.IsLinearHom A.t.act B.t.act f) :
    ∃ f' : A'.t.G ⟶ B'.t.G, Serre.IsLinearHom A'.t.act B'.t.act f' ∧ f'.left ≫ mB.φ = mA.φ ≫ f.left := by
  haveI := hf.isMonHom
  obtain ⟨f', hm, e⟩ := PairingFibre.exists_hom mA.cart mB.cart f
  refine ⟨f', ⟨hm, fun c => ?_⟩, e⟩
  apply Over.OverMorphism.ext
  apply mB.cart.1.hom_ext
  · have hc := congrArg CommaMorphism.left (hf.comm c)
    simp only [Over.comp_left] at hc ⊢
    rw [Category.assoc, e, ← Category.assoc, mA.act c, Category.assoc, hc, Category.assoc, mB.act c,
      ← Category.assoc, ← Category.assoc, e]
  · simp only [Over.comp_left, Category.assoc, Over.w]

theorem comb_over {n : ℕ} {f : Fin n → (A.t.G ⟶ B.t.G)} {f' : Fin n → (A'.t.G ⟶ B'.t.G)}
    (h : ∀ i, (f' i).left ≫ mB.φ = mA.φ ≫ (f i).left) (x : Fin n → 𝓞 E) :
    (∏ i, (A'.t.act.act (x i) ≫ f' i)).left ≫ mB.φ = mA.φ ≫ (∏ i, (A.t.act.act (x i) ≫ f i)).left := by
  refine prod_over mA.cart.1.w mB.cart _ fun i => ?_
  rw [Over.comp_left, Over.comp_left, Category.assoc, h, ← Category.assoc, mA.act, Category.assoc]

theorem rel_descend (hj : Function.Injective j) {n : ℕ} {f : Fin n → (A.t.G ⟶ B.t.G)}
    {f' : Fin n → (A'.t.G ⟶ B'.t.G)} (h : ∀ i, (f' i).left ≫ mB.φ = mA.φ ≫ (f i).left) (x : Fin n → 𝓞 E)
    (hx : ∏ i, (A'.t.act.act (x i) ≫ f' i) = 1) : ∏ i, (A.t.act.act (x i) ≫ f i) = 1 := by
  have : IsSchemeTheoreticallyDominant (spMap j) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom j) hj
  have : QuasiCompact (spMap j) := inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom j)))
  have := A.ab.smooth
  have : Flat A.t.G.hom := inferInstance
  have : IsSeparated B.t.G.hom := B.t.semi.separated
  refine ExtUnique.over_hom_ext_of_isPullback mA.cart.1 ?_
  rw [← comb_over mA mB h x, hx]
  exact one_over mA.cart.1.w mB.cart

theorem exists_pow_eq {n : ℕ} {f : A.t.G ⟶ B.t.G} {φ : Fin n → (A.t.G ⟶ B.t.G)}
    (hf : Serre.IsLinearHom A.t.act B.t.act f) (hφ : ∀ a, Serre.IsLinearHom A.t.act B.t.act (φ a)) {x₀ : 𝓞 E}
    (h₀ : x₀ ≠ 0) {x : Fin n → 𝓞 E} (h : (A.t.act.act x₀ ≫ f) * ∏ a, (A.t.act.act (x a) ≫ φ a) = 1) :
    ∃ N : ℕ, 0 < N ∧ ∃ y : Fin n → 𝓞 E, f ^ N = ∏ a, (A.t.act.act (y a) ≫ φ a) := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {x₀}))
  have hN : Ideal.absNorm (Ideal.span {x₀}) ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  refine ⟨_, Nat.pos_of_ne_zero hN, fun a => -(z * x a), ?_⟩
  let F : Serre.Pts B.t.act A.t.G := Serre.Pts.mk _ f
  let Φ : Fin n → Serre.Pts B.t.act A.t.G := fun a => Serre.Pts.mk _ (φ a)
  have h1 : x₀ • F + ∑ a, x a • Φ a = 0 := by
    apply Serre.Pts.ext
    rw [Serre.Pts.hom_add, Serre.Pts.hom_sum, Serre.Pts.hom_zero, ← h, hf.comm]
    simp only [Serre.Pts.hom_smul, (hφ _).comm, F, Φ, Serre.Pts.hom_mk]
  have h2 : Ideal.absNorm (Ideal.span {x₀}) • F = ∑ a, (-(z * x a)) • Φ a := by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← hz, mul_smul, eq_neg_of_add_eq_zero_left h1, smul_neg, Finset.smul_sum,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [neg_smul, mul_smul]
  have h3 := congrArg Serre.Pts.hom h2
  rw [Serre.Pts.hom_sum] at h3
  simp only [Serre.Pts.hom_smul, ← (hφ _).comm, Φ, Serre.Pts.hom_mk] at h3
  exact h3

end Rel

section Diff

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {A B : PAT H (Sp (𝓞 K))} {FA : GenFib A.pol} {FB : GenFib B.pol}

open IntCoord in

theorem smul_diff_eq {p : ℕ} {φ : Fin p → (A.t.G ⟶ B.t.G)}
    {MP : Fin p → ((Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))} (hMP : ∀ a, FA.IsDiffOf FB (φ a) (MP a))
    {f : A.t.G ⟶ B.t.G} {M : (Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)} (hM : FA.IsDiffOf FB f M) {n : ℕ}
    {x : Fin p → 𝓞 E} (hfn : f ^ n = ∏ a, (A.t.act.act (x a) ≫ φ a)) {τ : 𝓞 E →+* 𝓞 K} {e : Fin FA.P₀.g → K}
    (he : e ∈ FA.eigLat A.t.act τ) : n • M e = ∑ a, ((τ (x a) : 𝓞 K) : K) • MP a e := by
  obtain ⟨u, hu, heig⟩ := ((integral_tangent_coordinates K _ FA).2.2.2.2.2 _ _ τ e).1 he
  have hd := hM u e hu
  have hs : ∀ a, FB.IsCoord (u ≫ (A.t.act.act (x a) ≫ φ a)) (MP a (τ (x a) • e)) := by
    intro a
    rw [← Category.assoc]
    exact hMP a _ _ (isCoord_smul FA hu (heig (x a)))
  have hprod : ∀ s : Finset (Fin p), FB.IsCoord (u ≫ ∏ a ∈ s, (A.t.act.act (x a) ≫ φ a))
      (∑ a ∈ s, MP a (τ (x a) • e)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.sum_empty, comp_one]
      exact isCoord_one FB
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, comp_mul]
      exact isCoord_mul FB (hs a) ih
  have hpow : ∀ m : ℕ, FB.IsCoord ((u ≫ f) ^ m) (m • M e) := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero, zero_smul]
      exact isCoord_one FB
    | succ m ih =>
      rw [pow_succ, succ_nsmul]
      exact isCoord_mul FB ih hd
  have h1 := hpow n
  rw [← comp_pow, hfn] at h1
  rw [((integral_tangent_coordinates K _ FB).1 _ h1.1).unique h1 (hprod Finset.univ)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← algebraMap_smul K (τ (x a)) e, map_smul]

end Diff

theorem exists_rel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
    {ρ : 𝓞 K} {A B : PAT H (Sp (𝓞 K))} {p q : ℕ} (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) (hA : HasType H A.t.act ρ 1 0)
    (hB : HasType H B.t.act ρ p q) {n : ℕ} (hn : p + q < n) {ψ : Fin n → (A.t.G ⟶ B.t.G)}
    (hψ : ∀ i, Serre.IsLinearHom A.t.act B.t.act (ψ i)) :
    ∃ x : Fin n → 𝓞 E, x ≠ 0 ∧ ∏ i, (A.t.act.act (x i) ≫ ψ i) = 1 := by
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  let β : 𝓞 K →+* ℂ := σ.comp (algebraMap (𝓞 K) K)
  have hβ : Function.Injective β := σ.injective.comp (IsFractionRing.injective (𝓞 K) K)
  obtain ⟨A', mA, -⟩ := PAT.exists_pullback E H _ _ (spMap β) A
  obtain ⟨B', mB, -⟩ := PAT.exists_pullback E H _ _ (spMap β) B
  choose ψ' hψ' e using fun i => exists_linear_over mA mB (hψ i)
  obtain ⟨x, hx, h⟩ := GlobalTheory.T.exists_integer_relation_linear_homs_cm_signature_type E H (β ρ) A' B' p q (by rw [← map_pow, hρ, map_neg, map_natCast])
    ((hasType_baseChange E H _ _ β _ _ mA ρ 1 0).1 hβ hA) ((hasType_baseChange E H _ _ β _ _ mB ρ p q).1 hβ hB)
    n hn ψ' hψ'
  exact ⟨x, hx, rel_descend mA mB hβ e x h⟩

theorem eigLat_le_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0), ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ∀ τE : E →+* K, (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
          FB.eigLat X.B.t.act τ ≤ Submodule.span (𝓞 K)
            {w | ∃ c ∈ GlobalTheory.FlatCM.HomLat.lat X, ∃ e ∈ FP.eigLat (X.A true).t.act τ, w = ∑ a, τE (c a) • MP a e} := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X FP FB MP hMP τ _ τE hτE w hw
  obtain ⟨K', _, _, j, ω, C, A', B', mA, mB, DA, DB, hA, hB, rA, -, ⟨tA⟩, ⟨tB⟩⟩ :=
    GlobalTheory.T.exists_finiteExtension_principalTriples_tensorLattice E H K ρ (X.A true) X.B 1 p X.ρ_sq X.typeP X.typeB
  obtain ⟨n, f', g', hf', hg', hfg⟩ := GlobalTheory.T.cmTensor_retract_of_cmDatum_rank_one E H _ ω C A' B' DA DB hA hB rA tA tB
  have hj : Function.Injective (RingOfIntegers.mapRingHom j) := fun a b h => by
    apply RingOfIntegers.ext
    apply j.injective
    exact congrArg (fun x : 𝓞 K' => (x : K')) h
  have hφ : ∀ a, Serre.IsLinearHom (X.A true).t.act X.B.t.act (phiP X a) := fun a => X.lin (Sum.inl a)
  choose φ' hφ' eφ using fun a => exists_linear_over mA mB (hφ a)
  have key : ∀ i, ∃ f : (X.A true).t.G ⟶ X.B.t.G, Serre.IsLinearHom (X.A true).t.act X.B.t.act f ∧
      (f' i).left ≫ mB.φ = mA.φ ≫ f.left ∧ ∃ N : ℕ, 0 < N ∧ ∃ y : Fin p → 𝓞 E,
        f ^ N = ∏ a, ((X.A true).t.act.act (y a) ≫ phiP X a) := fun i => by
    obtain ⟨x, hx, h⟩ := exists_rel (ρ := RingOfIntegers.mapRingHom j ρ) (A := A') (B := B') (p := p) (q := 0)
      (by rw [← map_pow, X.ρ_sq, map_neg, map_natCast])
      ((hasType_baseChange E H _ _ _ _ _ mA ρ 1 0).1 hj X.typeP)
      ((hasType_baseChange E H _ _ _ _ _ mB ρ p 0).1 hj X.typeB) (Nat.lt_succ_self p)
      (ψ := Fin.cons (f' i) φ') (Fin.cases (hf' i) hφ')
    rw [Fin.prod_univ_succ] at h
    simp only [Fin.cons_zero, Fin.cons_succ] at h
    have h₀ : x 0 ≠ 0 := fun h₀ => by
      haveI := (hf' i).isMonHom
      rw [h₀, Serre.act_zero, MonObj.one_comp, _root_.one_mul] at h
      have hs := GlobalTheory.T.cmObjHomOfType_linearIndependent E H K ρ σ₁ p 0 X _ (rel_descend mA mB hj eφ _ h)
      exact hx (funext (Fin.cases h₀ fun a => congrFun hs a))
    obtain ⟨N, hN, y, hy⟩ := exists_pow_eq (hf' i) hφ' h₀ h
    obtain ⟨f, hf, e₁, e₂⟩ := GlobalTheory.T.eq_pow_of_baseChange_eq_pow_principalAbelianCMTriple E H K K' j (X.A true) X.B A' B' mA mB _ (f' i) N hN (isLinearHom_prod X y) (hf' i)
      (by rw [hy]; exact comb_over mA mB eφ y)
    exact ⟨f, hf, e₂, N, hN, y, e₁⟩
  choose f hf ef N hN y hy using key
  choose M hM using fun i =>
    (DiffCoord.existsUnique_isDiffOf K _ FP _ FB (f i) (hf i).isMonHom).1.exists
  refine GlobalTheory.T.mem_of_mem_span_ringOfIntegers_map_numberField K K' j _ _ w (Submodule.span_mono (Set.image_mono ?_)
    (GlobalTheory.T.eigenLattice_image_le_span_after_baseChange E H K K' j (X.A true) X.B A' B' mA mB n f f' g' hf hf' hg' ef hfg FP FB M hM τ w hw))
  rintro _ ⟨i, e, he, rfl⟩
  have hE : (N i : E) ≠ 0 := Nat.cast_ne_zero.2 (hN i).ne'
  have hK : (N i : K) ≠ 0 := Nat.cast_ne_zero.2 (hN i).ne'
  refine Submodule.subset_span ⟨fun a => (y i a : E) / N i,
    Submodule.subset_span ⟨N i, hN i, y i, fun a => by field_simp, f i, hf i, hy i⟩, e, he, ?_⟩
  refine smul_right_injective _ hK ?_
  show (N i : K) • M i e = (N i : K) • _
  rw [Nat.cast_smul_eq_nsmul, smul_diff_eq hMP (hM i) (hy i) he, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, map_div₀, hτE, map_natCast, mul_div_cancel₀ _ hK]

end GlobalTheory.FlatCM.HomLat.LieSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqComponentTensorEqConstMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.AdelicPush

open GlobalTheory.AdelicU

theorem lintegral_tens_eq_const_mul : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (r : (κ → AF F) → ℂ),
    @Measurable _ _ (borel _) _ r →
    (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → r (x + z) = r x) →
    ∀ μA : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μA →
    ∀ μ : @MeasureTheory.Measure (κ → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ K : Set (κ → Fv F v), IsCompact K → (interior K).Nonempty →
    ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ 0 →
    ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ ⊤ →
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ φ : (κ → Fv F v) → ℂ, Continuous φ → HasCompactSupport φ →
      ∫⁻ x, ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r x‖ₑ ^ 2 ∂μA = C * ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ _ v r hr hinv μA hμA μ hμ K hK hKi hK0 hKt
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mV : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  have hcont : Continuous (evFin F v) := by
    change Continuous fun a => _
    exact (PI.LevelKSplit.W.Cont.continuous_evalV v).comp continuous_snd
  let evK : (κ → AF F) → (κ → Fv F v) := fun x i => evFin F v (x i)
  have hevKm : Measurable evK := (continuous_pi fun i => hcont.comp (continuous_apply i)).measurable
  let ρ : (κ → AF F) → ENNReal := fun x => ‖r x‖ₑ ^ 2
  have hρ : Measurable ρ := hr.enorm.pow_const 2
  let ν : Measure (κ → Fv F v) := (μA.withDensity ρ).map evK
  have hνA : ∀ A, MeasurableSet A → ν A = ∫⁻ x, A.indicator 1 (evK x) * ρ x ∂μA := by
    intro A hA
    rw [Measure.map_apply hevKm hA, withDensity_apply _ (hevKm hA), ← lintegral_indicator (hevKm hA)]
    refine lintegral_congr fun x => ?_
    by_cases h : evK x ∈ A <;> simp [Set.indicator, h]
  haveI : ν.IsAddLeftInvariant := by
    constructor
    intro y
    ext A hA
    rw [Measure.map_apply (measurable_const_add y) hA, hνA _ hA, hνA _ (measurable_const_add y hA)]
    let z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
    have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v (y i) u hu
    have hev : ∀ x, evK (x + z) = y + evK x := fun x => funext fun i => by
      simp [evK, z, GlobalTheory.LatVac.evFin_liftV, add_comm]
    rw [← lintegral_add_right_eq_self (fun x => A.indicator 1 (evK x) * ρ x) z]
    refine lintegral_congr fun x => ?_
    simp only [hev, ρ, hinv x z hz]
    by_cases h : y + evK x ∈ A <;> simp [Set.indicator, h]
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  haveI : ν.IsAddHaarMeasure := Measure.isAddHaarMeasure_of_isCompact_nonempty_interior ν K hK hKi
    (by rw [hνA K hKm]; exact hK0) (by rw [hνA K hKm]; exact hKt)
  have hsc : ∀ s : Set (κ → Fv F v), IsCompact (closure s) →
      ν s = (Measure.addHaarScalarFactor ν μ : ENNReal) * μ s := fun s hs => by
    rw [Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure ν μ hs, ENNReal.smul_def, smul_eq_mul]
  refine ⟨(Measure.addHaarScalarFactor ν μ : ENNReal), ?_, ENNReal.coe_ne_top, ?_⟩
  · intro h0
    have := hsc K (by rw [hK.isClosed.closure_eq]; exact hK)
    rw [h0, zero_mul, hνA K hKm] at this
    exact hK0 this
  intro φ hφ hφc
  set C : ENNReal := (Measure.addHaarScalarFactor ν μ : ENNReal)
  let T := tsupport φ
  have hrest : ν.restrict T = C • μ.restrict T := by
    ext s hs
    rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
    exact hsc _ (hφc.isCompact.of_isClosed_subset isClosed_closure
      (closure_minimal Set.inter_subset_right (isClosed_tsupport φ)))
  have hf : Measurable fun y => ‖φ y‖ₑ ^ 2 := hφ.measurable.enorm.pow_const 2
  have hsupp : Function.support (fun y => ‖φ y‖ₑ ^ 2) ⊆ T := by
    intro y hy
    by_contra h
    exact hy (by simp [image_eq_zero_of_notMem_tsupport h])
  calc ∫⁻ x, ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r x‖ₑ ^ 2 ∂μA
      = ∫⁻ x, (ρ * fun x => (fun y => ‖φ y‖ₑ ^ 2) (evK x)) x ∂μA := by
        refine lintegral_congr fun x => ?_
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.mul_apply, ρ, evK, enorm_mul, mul_pow, mul_comm]
    _ = ∫⁻ x, (fun y => ‖φ y‖ₑ ^ 2) (evK x) ∂(μA.withDensity ρ) :=
        (lintegral_withDensity_eq_lintegral_mul _ hρ (hf.comp hevKm)).symm
    _ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂ν := (lintegral_map hf hevKm).symm
    _ = ∫⁻ y in T, ‖φ y‖ₑ ^ 2 ∂ν := (setLIntegral_eq_of_support_subset hsupp).symm
    _ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂(C • μ.restrict T) := by rw [hrest]
    _ = C * ∫⁻ y in T, ‖φ y‖ₑ ^ 2 ∂μ := lintegral_smul_measure _ _
    _ = C * ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by rw [setLIntegral_eq_of_support_subset hsupp]

end GlobalTheory.AdelicPush

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableCompInfGLProd
section
noncomputable section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Petersson Formalism.L2.Host
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped ComplexConjugate

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem measurable_chart_prod {φ : GA E a → ℂ} (hφ : Continuous φ) :
    Measurable fun p : GA E a × Lie E a => chart φ p.1 p.2 := by
  classical
  have e : (fun p : GA E a × Lie E a => chart φ p.1 p.2) =
      (Set.univ ×ˢ invSet E a).piecewise (fun p : GA E a × Lie E a => chart φ p.1 p.2) (fun _ => 0) := by
    funext p
    by_cases hp : p ∈ Set.univ ×ˢ invSet E a
    · rw [Set.piecewise_eq_of_mem _ _ _ hp]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hp]
      have hp' : ¬ IsUnit (Matrix.of p.2) := fun h => hp ⟨trivial, h⟩
      exact dif_neg hp'
  rw [e]
  exact (GlobalTheory.ConstTermSmooth.continuousOn_chart hφ).measurable_piecewise continuousOn_const
    (isOpen_univ.prod isOpen_invSet).measurableSet

theorem measurable_comp_infGL_prod {F : GA E a → ℂ} (hF : Continuous F) {X : Type} [MeasurableSpace X]
    {γ : X → GL (Fin a) (Cinf E)} (hγ : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) :
    Measurable fun p : GA E a × X => F (p.1 * infGL E a (γ p.2)) := by
  have h : Measurable fun x => toL (γ x).val := hγ
  have e : (fun p : GA E a × X => F (p.1 * infGL E a (γ p.2))) =
      (fun p : GA E a × Lie E a => chart F p.1 p.2) ∘ fun p : GA E a × X => (p.1, toL (γ p.2).val) :=
    funext fun p => (chart_val F p.1 (γ p.2)).symm
  rw [e]
  exact (measurable_chart_prod hF).comp (measurable_fst.prodMk (h.comp measurable_snd))

theorem IsRapidInf.integrable_norm {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) : Integrable (fun x => ‖k x‖) ν := by
  simpa using hk.2.2 0

theorem kerInf_mem_bddForms {ω : HChar E} {F : GA E a → ℂ} (h : F ∈ bddForms E a ω) {X : Type} [MeasurableSpace X]
    {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    kerInf ν k γ F ∈ bddForms E a ω := by
  obtain ⟨C, hC⟩ := h.2.2.2
  have hki := hk.integrable_norm
  have hm := measurable_comp_infGL_prod h.1 hk.2.1
  refine ⟨?_, fun γ' g => ?_, fun z g => ?_, ∫ x, ‖k x‖ * C ∂ν, fun g => ?_⟩
  · refine continuous_of_dominated (bound := fun x => ‖k x‖ * C)
      (fun g => (hk.1.mul (hm.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
      (fun g => .of_forall fun x => ?_) (hki.mul_const C)
      (.of_forall fun x => continuous_const.mul (h.1.comp (continuous_mul_const _)))
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  · simp only [kerInf, mul_assoc, h.2.1]
  · rw [kerInf, kerInf, ← integral_const_mul]
    congr 1; funext x; rw [mul_assoc, h.2.2.1]; ring
  · exact norm_integral_le_of_norm_le (hki.mul_const C)
      (.of_forall fun x => (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)))

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure]

theorem pet_kerInf_left {ω : HChar E} (hω : ω.IsUnitary) {F ψ : GA E a → ℂ} (h : F ∈ bddForms E a ω)
    (h' : ψ ∈ bddForms E a ω) {X : Type} [MeasurableSpace X] (ν : Measure X) [SFinite ν] {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    pet (latticeGL E a) μ (kerInf ν k γ F) ψ =
      ∫ x, k x * pet (latticeGL E a) μ (fun g => F (g * infGL E a (γ x))) ψ ∂ν := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have hD := isFundamentalDomain_stdDom (latticeGL E a) μ
  haveI : IsFiniteMeasure (μ.restrict (stdDom (latticeGL E a))) :=
    ⟨by rw [Measure.restrict_apply_univ, ← quotMeasure_univ hD]; exact measure_lt_top _ _⟩
  obtain ⟨C, hC⟩ := h.2.2.2
  obtain ⟨D, hD'⟩ := h'.2.2.2
  have hki := hk.integrable_norm
  have hm := measurable_comp_infGL_prod h.1 hk.2.1
  have hi : Integrable (fun p : GA E a × X => k p.2 * F (p.1 * infGL E a (γ p.2)) * conj (ψ p.1))
      ((μ.restrict (stdDom (latticeGL E a))).prod ν) := by
    refine ((integrable_const (C * D)).mul_prod hki).mono'
      (((hk.1.comp measurable_snd).mul hm).mul
        ((Complex.continuous_conj.comp h'.1).measurable.comp measurable_fst)).aestronglyMeasurable
      (.of_forall fun p => ?_)
    rw [norm_mul, norm_mul, mul_assoc, Complex.norm_conj, mul_comm]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hD' _) (norm_nonneg _)
      ((norm_nonneg _).trans (hC 1))) (norm_nonneg _)
  rw [(pet_eq_setIntegral hω (kerInf_mem_bddForms h hk) h' hD).2]
  simp only [kerInf, ← integral_mul_const]
  rw [integral_integral_swap hi]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [(pet_eq_setIntegral hω (mul_right_mem_bddForms h _) h' hD).2, ← integral_const_mul, mul_assoc]

theorem rspan_central {π : CuspSub E a} {ω : HChar E} (hπ : π.HasCentChar ω) {F : GA E a → ℂ} (hF : F ∈ rspan π)
    (z : Ideles E) (g : GA E a) :
    F (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * F g := by
  have hc := CuspSub.hasCentral_iff.2 hπ
  let S : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | ∀ (z : Ideles E) g, F (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * F g}
      add_mem' := fun {F F'} hF hF' z g => by simp only [Pi.add_apply, hF z g, hF' z g, mul_add]
      zero_mem' := fun z g => by simp
      smul_mem' := fun c F hF z g => by simp only [Pi.smul_apply, smul_eq_mul, hF z g]; ring }
  refine rspan_le (S := S) (fun φ hφ z g => hc.apply hφ z g) (fun F hF h z g => ?_)
    (fun F hF X _ ν _ k γ _ z g => ?_) hF z g
  · change F (GeneralLinearGroup.scalar (Fin a) z * g * h) = _ * F (g * h)
    rw [mul_assoc]; exact hF z _
  · change ∫ x, k x * F (GeneralLinearGroup.scalar (Fin a) z * g * infGL E a (γ x)) ∂ν =
      _ * ∫ x, k x * F (g * infGL E a (γ x)) ∂ν
    rw [← integral_const_mul]
    congr 1; funext x; rw [mul_assoc, hF z]; ring

theorem pet_rt_eq_zero {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (hπ : π.HasCentChar ω) {ψ : GA E a → ℂ}
    (hψ : ψ ∈ bddForms E a ω) (h0 : ∀ φ ∈ π.V, pet (latticeGL E a) μ φ.1 ψ = 0) {φ : Sm E a} (hφ : φ ∈ π.V)
    (h : GA E a) : pet (latticeGL E a) μ (fun g => φ.1 (g * h)) ψ = 0 := by
  have hb : ∀ φ ∈ π.V, φ.1 ∈ bddForms E a ω := fun φ hφ =>
    mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ
  rw [← infGL_mul_finGL h]
  have e : (fun g => φ.1 (g * (infGL E a (GeneralLinearGroup.map (pInf E) h) *
      finGL E a (GeneralLinearGroup.map (pFin E) h)))) =
      fun g => (finRep E a (GeneralLinearGroup.map (pFin E) h) φ).1 (g * infGL E a (GeneralLinearGroup.map (pInf E) h)) := by
    funext g
    change _ = φ.1 (g * infGL E a _ * finGL E a _)
    rw [mul_assoc]
  rw [e]
  exact GlobalTheory.KeepOrth.pet_translate_eq_zero μ hω hψ hb (fun X => π.stable (.lie X)) (fun φ hφ => (π.cusp φ hφ).1) h0
    (π.stable (.fin _) φ hφ) _

theorem rspan_bdd_pet_eq_zero {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (hπ : π.HasCentChar ω)
    {ψ : GA E a → ℂ} (hψ : ψ ∈ bddForms E a ω) (h0 : ∀ φ ∈ π.V, pet (latticeGL E a) μ φ.1 ψ = 0)
    {F : GA E a → ℂ} (hF : F ∈ rspan π) :
    F ∈ bddForms E a ω ∧ ∀ h : GA E a, pet (latticeGL E a) μ F (fun g => ψ (g * h)) = 0 := by
  have hψh : ∀ h : GA E a, (fun g => ψ (g * h)) ∈ bddForms E a ω := mul_right_mem_bddForms hψ
  let S : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | F ∈ bddForms E a ω ∧ ∀ h : GA E a, pet (latticeGL E a) μ F (fun g => ψ (g * h)) = 0}
      add_mem' := fun {F F'} hF hF' => ⟨add_mem hF.1 hF'.1, fun h => by
        rw [pet_add_left μ hω hF.1 hF'.1 (hψh h), hF.2 h, hF'.2 h, add_zero]⟩
      zero_mem' := ⟨zero_mem _, fun h => by simp [pet, descend]⟩
      smul_mem' := fun c F hF => ⟨Submodule.smul_mem _ c hF.1, fun h => by
        rw [pet_smul_left, hF.2 h, mul_zero]⟩ }
  have htr : ∀ F ∈ S, ∀ h' : GA E a, (fun g => F (g * h')) ∈ S := fun F hF h' =>
    ⟨mul_right_mem_bddForms hF.1 h', fun h => by
      rw [pet_mul_right_left μ hω hF.1 (hψh h) h']
      have := hF.2 (h'⁻¹ * h)
      simp only [mul_assoc] at this ⊢
      exact this⟩
  refine rspan_le (S := S) (fun φ hφ => ⟨mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ,
    fun h => ?_⟩) htr (fun F hF X _ ν _ k γ hk => ⟨kerInf_mem_bddForms hF.1 hk, fun h => ?_⟩) hF
  · have hb := mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ
    have e := pet_mul_right_left μ hω hb hψ h⁻¹
    rw [inv_inv] at e
    rw [← e]
    exact pet_rt_eq_zero μ hω hπ hψ h0 hφ h⁻¹
  · rw [pet_kerInf_left μ hω hF.1 (hψh h) ν hk]
    exact integral_eq_zero_of_ae (.of_forall fun x => mul_eq_zero_of_right _ ((htr F hF _).2 h))

example {π : CuspSub E a} {ω : HChar E} (hπ : π.HasCentChar ω) {φ : Sm E a} (hφ : φ ∈ π.V) (z : Ideles E) (g : GA E a) :
    φ.1 (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g :=
  rspan_central hπ (mem_rspan hφ) z g

end GlobalTheory.JSW
end
end

