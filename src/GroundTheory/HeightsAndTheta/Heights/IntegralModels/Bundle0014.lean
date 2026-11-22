import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PGlueModulesStar
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0011

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PGlueTwo
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace GlueTwo

lemma pullbackCompIso_symm_trans {A B C Z : Scheme.{0}} {t : A ⟶ B} {s : B ⟶ C} {ι : C ⟶ Z}
    {j : B ⟶ Z} {u : A ⟶ C} {w : A ⟶ Z} (e : s ≫ ι = j) (eg : t ≫ s = u) (ek : t ≫ j = w)
    (e' : u ≫ ι = w) {E : Z.Modules} {F : B.Modules} (a : (Scheme.Modules.pullback j).obj E ≅ F) :
    pullbackCompIso eg ((pullbackCompIso e (Iso.refl ((Scheme.Modules.pullback ι).obj E))).symm ≪≫ a) =
      (pullbackCompIso e' (Iso.refl ((Scheme.Modules.pullback ι).obj E))).symm ≪≫
        pullbackCompIso ek a := by
  rw [pullbackCompIso_comp' t e eg ek e' (Iso.refl ((Scheme.Modules.pullback ι).obj E)),
    pullbackCompIso_eq_refl_trans eg
      ((pullbackCompIso e (Iso.refl ((Scheme.Modules.pullback ι).obj E))).symm ≪≫ a),
    pullbackCompIso_eq_refl_trans ek a, Functor.mapIso_trans, Functor.mapIso_symm]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.symm_self_id_assoc]

set_option backward.isDefEq.respectTransparency false in

theorem proof : GlueTwo.Statement := by
  intro X O₁ O₂ O O₁₂ h₁ h₂ _ k₁ k₂ hk F₁ F₂ ψ
  obtain rfl : O₁ ⊓ O₂ = O₁₂ := le_antisymm hk (le_inf k₁ k₂)
  let I := GlueModulesStar.index O₂ (fun _ : Unit => O₁) F₂ (fun _ => F₁) (fun _ => ψ)
  have h0 : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction O₂.ι).homEquiv _ _).symm
      (Multiequalizer.ι I none)) :=
    GlueModulesStar.isIso_homEquiv_symm O₂.ι _ (fun W =>
      GlueModulesStar.isIso_ι_none_app O₂ (fun _ : Unit => O₁) F₂ (fun _ => F₁) (fun _ => ψ) _
        (O₂.ι_image_le W))
  have hi : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction O₁.ι).homEquiv _ _).symm
      (Multiequalizer.ι I (some ()))) :=
    GlueModulesStar.isIso_homEquiv_symm O₁.ι _ (fun W =>
      GlueModulesStar.isIso_ι_some_app O₂ (fun _ : Unit => O₁) F₂ (fun _ => F₁) (fun _ => ψ)
        (fun i j hij => absurd (Subsingleton.elim i j) hij) () _ (O₁.ι_image_le W))
  let a₂ := asIso (((Scheme.Modules.pullbackPushforwardAdjunction O₂.ι).homEquiv _ _).symm
    (Multiequalizer.ι I none))
  let a₁ := asIso (((Scheme.Modules.pullbackPushforwardAdjunction O₁.ι).homEquiv _ _).symm
    (Multiequalizer.ι I (some ())))
  have hc : pullbackCompIso (X.homOfLE_ι k₂) a₂ = pullbackCompIso (X.homOfLE_ι k₁) a₁ ≪≫ ψ := by
    ext1
    apply ((Scheme.Modules.pullbackPushforwardAdjunction (O₁ ⊓ O₂).ι).homEquiv _ _).injective
    have e1 := GlueModulesStar.homEquiv_pullbackCompIso (X.homOfLE_ι k₂) a₂ (𝟙 _)
    have e2 := GlueModulesStar.homEquiv_pullbackCompIso (X.homOfLE_ι k₁) a₁ ψ.hom
    rw [Category.comp_id] at e1
    rw [Iso.trans_hom, e1, e2]
    simp only [a₁, a₂, asIso_hom, Equiv.apply_symm_apply]
    exact Multiequalizer.condition I ()
  refine ⟨(Scheme.Modules.pullback O.ι).obj (multiequalizer I),
    (pullbackCompIso (X.homOfLE_ι h₁) (Iso.refl _)).symm ≪≫ a₁,
    (pullbackCompIso (X.homOfLE_ι h₂) (Iso.refl _)).symm ≪≫ a₂, ?_⟩
  rw [pullbackCompIso_symm_trans (X.homOfLE_ι h₂) (X.homOfLE_homOfLE k₂ h₂) (X.homOfLE_ι k₂)
      (X.homOfLE_ι _),
    pullbackCompIso_symm_trans (X.homOfLE_ι h₁) (X.homOfLE_homOfLE k₁ h₁) (X.homOfLE_ι k₁)
      (X.homOfLE_ι _), hc, Iso.trans_assoc]

end GlueTwo

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PHeightOneSectionsLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace HeightOneSections

variable {X : Scheme.{0}} [IsIntegral X]

lemma genericPoint_mem {U : X.Opens} {x : X} (hx : x ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩

omit [IsIntegral X] in

lemma fromSpec_mem {V : X.Opens} (hV : IsAffineOpen V) (p : PrimeSpectrum Γ(X, V)) :
    hV.fromSpec p ∈ V := by
  have h : hV.fromSpec p ∈ Set.range hV.fromSpec := ⟨p, rfl⟩
  rwa [hV.range_fromSpec] at h

lemma isIntegrallyClosed_of_isAffineOpen (hN : IsNormalScheme X) {V : X.Opens}
    (hV : IsAffineOpen V) [Nonempty V] : IsIntegrallyClosed Γ(X, V) := by
  refine IsIntegrallyClosed.of_localization_maximal fun P _ hP => ?_
  have hy := fromSpec_mem hV ⟨P, hP.isPrime⟩
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf
    (⟨hV.fromSpec ⟨P, hP.isPrime⟩, hy⟩ : V)
  have : IsLocalization.AtPrime (X.presheaf.stalk (hV.fromSpec ⟨P, hP.isPrime⟩)) P :=
    hV.isLocalization_stalk' ⟨P, hP.isPrime⟩ hy
  have := hN (hV.fromSpec ⟨P, hP.isPrime⟩)
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv P.primeCompl (X.presheaf.stalk (hV.fromSpec ⟨P, hP.isPrime⟩))
      (Localization.AtPrime P)).toRingEquiv

def comb (E : X.Modules) {V : X.Opens} {n : ℕ} (s : Fin n → Γ(E, V)) (W : X.Opens) (h : W ≤ V)
    (r : Fin n → Γ(X, W)) : Γ(E, W) :=
  ∑ i, r i • (E.presheaf.map (homOfLE h).op).hom (s i)

omit [IsIntegral X] in

lemma germ_comb (E : X.Modules) {V : X.Opens} {n : ℕ} (s : Fin n → Γ(E, V)) (W : X.Opens)
    (h : W ≤ V) (r : Fin n → Γ(X, W)) (x : X) (hx : x ∈ W) :
    E.presheaf.germ W x hx (comb E s W h r) =
      ∑ i, X.presheaf.germ W x hx (r i) • E.presheaf.germ V x (h hx) (s i) := by
  rw [comb, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [BundlesAgree.germ_smul']
  congr 1
  exact TopCat.Presheaf.germ_res_apply E.presheaf (homOfLE h) x hx (s i)

omit [IsIntegral X] in

lemma comb_res (E : X.Modules) {V : X.Opens} {n : ℕ} (s : Fin n → Γ(E, V)) (W W' : X.Opens)
    (h : W ≤ V) (h' : W' ≤ W) (r : Fin n → Γ(X, W)) :
    E.presheaf.map (homOfLE h').op (comb E s W h r) =
      comb E s W' (h'.trans h) (fun i => X.presheaf.map (homOfLE h').op (r i)) := by
  rw [comb, comb, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.map_smul]
  congr 1
  show (E.presheaf.map (homOfLE h).op ≫ E.presheaf.map (homOfLE h').op) (s i) = _
  rw [← Functor.map_comp]
  rfl

omit [IsIntegral X] in

lemma germ_coeff_unique (E : X.Modules) {V : X.Opens} {n : ℕ} {s : Fin n → Γ(E, V)}
    (hs : IsBasisOn E V s) (x : X) (hxV : x ∈ V) {W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ V)
    (hx : x ∈ W) (hx' : x ∈ W') (r : Fin n → Γ(X, W)) (r' : Fin n → Γ(X, W'))
    (e : ∑ i, X.presheaf.germ W x hx (r i) • E.presheaf.germ V x hxV (s i) =
      ∑ i, X.presheaf.germ W' x hx' (r' i) • E.presheaf.germ V x hxV (s i)) (i : Fin n) :
    X.presheaf.germ W x hx (r i) = X.presheaf.germ W' x hx' (r' i) := by
  rw [← germ_comb E s W h r x hx, ← germ_comb E s W' h' r' x hx'] at e
  obtain ⟨W'', hx'', iU, iV, e'⟩ := E.presheaf.germ_eq x hx hx' _ _ e
  have hU : iU = homOfLE iU.le := rfl
  have hV : iV = homOfLE iV.le := rfl
  rw [hU, hV, comb_res, comb_res] at e'
  have := (hs W'' (iU.le.trans h)).1 e'
  have hi := congrFun this i
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf iU x hx'' (r i),
    ← TopCat.Presheaf.germ_res_apply X.presheaf iV x hx'' (r' i)]
  exact congrArg (X.presheaf.germ W'' x hx'') hi

theorem exists_section_of_isBasisOn (hHOI : HeightOneIntersection.Statement)
    [IsLocallyNoetherian X] (hN : IsNormalScheme X) (E : X.Modules) {V : X.Opens}
    (hV : IsAffineOpen V) (hη : genericPoint X ∈ V) {n : ℕ} {s : Fin n → Γ(E, V)}
    (hs : IsBasisOn E V s) (v : E.presheaf.stalk (genericPoint X))
    (hv : ∀ y : X, y ∈ V → ringKrullDim (X.presheaf.stalk y) = 1 → v ∈ genericImage E y) :
    ∃ σ : Γ(E, V), E.presheaf.germ V (genericPoint X) hη σ = v := by
  have : Nonempty V := ⟨⟨genericPoint X, hη⟩⟩
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have := isIntegrallyClosed_of_isAffineOpen hN hV
  have := functionField_isFractionRing_of_isAffineOpen X V hV

  obtain ⟨W0, hW0, t0, ht0⟩ := E.presheaf.exists_germ_eq v
  have hW1 : genericPoint X ∈ W0 ⊓ V := ⟨hW0, hη⟩
  obtain ⟨r, hr⟩ := (hs (W0 ⊓ V) inf_le_right).2
    ((E.presheaf.map (homOfLE (inf_le_left : W0 ⊓ V ≤ W0)).op).hom t0)
  have hvc : v = ∑ i, X.presheaf.germ (W0 ⊓ V) _ hW1 (r i) •
      E.presheaf.germ V (genericPoint X) hη (s i) := by
    rw [← germ_comb E s (W0 ⊓ V) inf_le_right r _ hW1]
    change v = E.presheaf.germ (W0 ⊓ V) _ hW1 (comb E s (W0 ⊓ V) inf_le_right r)
    rw [show comb E s (W0 ⊓ V) inf_le_right r = _ from hr, ← ht0]
    exact (TopCat.Presheaf.germ_res_apply E.presheaf _ _ hW1 t0).symm

  have hmem : ∀ i, X.presheaf.germ (W0 ⊓ V) _ hW1 (r i) ∈
      Subalgebra.toSubmodule (⊥ : Subalgebra Γ(X, V) X.functionField) := by
    intro i
    rw [hHOI Γ(X, V) X.functionField, Submodule.mem_iInf]
    intro p
    rw [Submodule.mem_iInf]
    intro hp1
    have hy := fromSpec_mem hV p
    let y := hV.fromSpec p
    let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hy⟩ : V)
    have hloc : IsLocalization.AtPrime (X.presheaf.stalk y) p.asIdeal :=
      hV.isLocalization_stalk' p hy
    have hdim : ringKrullDim (X.presheaf.stalk y) = 1 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal, hp1]
      rfl
    obtain ⟨w, hw⟩ := hv y hy hdim
    obtain ⟨W2, hW2, t, rfl⟩ := E.presheaf.exists_germ_eq w
    have hη3 : genericPoint X ∈ W2 ⊓ V := genericPoint_mem (show y ∈ W2 ⊓ V from ⟨hW2, hy⟩)
    obtain ⟨r', hr'⟩ := (hs (W2 ⊓ V) inf_le_right).2
      ((E.presheaf.map (homOfLE (inf_le_left : W2 ⊓ V ≤ W2)).op).hom t)
    have hvc' : v = ∑ i, X.presheaf.germ (W2 ⊓ V) _ hη3 (r' i) •
        E.presheaf.germ V (genericPoint X) hη (s i) := by
      rw [← germ_comb E s (W2 ⊓ V) inf_le_right r' _ hη3]
      change v = E.presheaf.germ (W2 ⊓ V) _ hη3 (comb E s (W2 ⊓ V) inf_le_right r')
      rw [show comb E s (W2 ⊓ V) inf_le_right r' = _ from hr', ← hw]
      rw [TopCat.Presheaf.germ_res_apply]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply E.presheaf hW2
        (genericPoint_specializes y) t
    have hc := germ_coeff_unique E hs _ hη inf_le_right inf_le_right hW1 hη3 r r'
      (hvc.symm.trans hvc') i
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj p.asIdeal.primeCompl
      (X.presheaf.germ (W2 ⊓ V) y ⟨hW2, hy⟩ (r' i))
    refine ⟨b, b.2, Algebra.mem_bot.mpr ⟨a, ?_⟩⟩
    have hab' := congrArg (X.presheaf.stalkSpecializes (genericPoint_specializes y)) hab
    rw [map_mul] at hab'
    have h1 : X.presheaf.stalkSpecializes (genericPoint_specializes y)
        (X.presheaf.germ (W2 ⊓ V) y ⟨hW2, hy⟩ (r' i)) = X.presheaf.germ (W2 ⊓ V) _ hη3 (r' i) :=
      TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    have h2 : ∀ c : Γ(X, V), X.presheaf.stalkSpecializes (genericPoint_specializes y)
        (algebraMap Γ(X, V) (X.presheaf.stalk y) c) = algebraMap Γ(X, V) X.functionField c :=
      fun c => TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    rw [h1, h2, h2, ← hc] at hab'
    rw [Algebra.smul_def, ← hab', mul_comm]
  choose a ha using fun i => Algebra.mem_bot.mp (hmem i)
  refine ⟨∑ i, a i • s i, ?_⟩
  rw [map_sum, hvc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [BundlesAgree.germ_smul', ← ha i]
  rfl

end HeightOneSections

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PLocSectionsInj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry Opposite

noncomputable section

lemma eq_zero_of_mul_of_coprime {B : Type*} [CommRing B] (p : ℕ) (hp : p.Prime) (e N' : ℕ) (u : ℤ)
    (hu : ¬ (p : ℤ) ∣ u) (hN' : IsUnit (N' : B)) (t : B)
    (h1 : ((p ^ e * N' : ℕ) : B) * t = 0) (h2 : (u : B) * t = 0) : t = 0 := by
  have hc : IsCoprime u ((p : ℤ) ^ e) :=
    ((Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.mpr hu).symm.pow_right
  obtain ⟨x, y, hxy⟩ := hc
  have hxy' := congrArg (Int.cast : ℤ → B) hxy
  push_cast at hxy' h1
  have h3 : (N' : B) * t = 0 := by
    linear_combination (-(N' : B) * t) * hxy' + (x : B) * (N' : B) * h2 + (y : B) * h1
  exact hN'.mul_right_eq_zero.mp h3

lemma eq_zero_of_coprime_mul_eq_zero {X : Scheme.{0}} (f : X ⟶ SpecZ) (p : ℕ) (hp : p.Prime) (k : ℤ)
    (hcov : ∀ x : X, ∃ (U : X.affineOpens) (N : ℕ), x ∈ (U : X.Opens) ∧ ((ordCompl[p] N : ℕ) : ℤ) ∣ k ∧
      ∀ (n : ℤ) (a : Γ(X, U)), n ≠ 0 → (n : Γ(X, U)) * a = 0 → (N : Γ(X, U)) * a = 0)
    {W : X.Opens} (hW : W ≤ invOpen f k) (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) (s : Γ(X, W))
    (hs : (u : Γ(X, W)) * s = 0) : s = 0 := by
  refine X.IsSheaf.section_ext fun x hx => ?_
  obtain ⟨U, N, hxU, hNk, hN⟩ := hcov x
  obtain ⟨a, haW, hxa⟩ := U.2.exists_basicOpen_le ⟨x, hx⟩ hxU
  refine ⟨X.basicOpen a, haW, hxa, ?_⟩
  have := U.2.isLocalization_basicOpen a
  set t := X.presheaf.map (homOfLE haW).op s with ht_def
  have ht : (u : Γ(X, X.basicOpen a)) * t = 0 := by
    rw [ht_def, ← map_intCast (X.presheaf.map (homOfLE haW).op).hom u, ← map_mul, hs, map_zero]
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (dvd_zero _)
  have hNt := torsion_bound_localization (Submonoid.powers a) hN u t hu0 ht
  have hk := isUnit_intCast_of_le_invOpen f k (haW.trans hW)
  obtain ⟨c, hc⟩ := hNk
  rw [hc, Int.cast_mul, Int.cast_natCast] at hk
  rw [map_zero]
  refine eq_zero_of_mul_of_coprime p hp (N.factorization p) (ordCompl[p] N) u hu
    (isUnit_of_mul_isUnit_left hk) t ?_ ht
  rwa [Nat.ordProj_mul_ordCompl_eq_self]

lemma exists_mul_eq_zero_of_pushout_inl {R A T : CommRingCat.{0}} (f : R ⟶ A) (g : R ⟶ T)
    (M : Submonoid R) (hT : @IsLocalization R _ M T _ g.hom.toAlgebra) (a : A)
    (ha : pushout.inl f g a = 0) : ∃ m ∈ M, f m * a = 0 := by
  algebraize [f.hom, g.hom]
  have e : _ = pushout.inl f g := (CommRingCat.isPushout_tensorProduct R T A).flip.inl_isoPushout_hom
  rw [← e, CommRingCat.comp_apply, ← map_zero
    (CommRingCat.isPushout_tensorProduct R T A).flip.isoPushout.hom.hom] at ha
  have ha' := (CommRingCat.isPushout_tensorProduct R T A).flip.isoPushout.commRingCatIsoToRingEquiv.injective ha
  have hL : IsLocalizedModule M (TensorProduct.mk R T A 1) :=
    (isLocalizedModule_iff_isBaseChange M T _).mpr (TensorProduct.isBaseChange R A T)
  obtain ⟨m, hm⟩ := (IsLocalizedModule.eq_zero_iff M (TensorProduct.mk R T A 1)).mp ha'
  exact ⟨m, m.2, hm⟩

lemma exists_coprime_mul_eq_zero {X : Scheme.{0}} (f : X ⟶ SpecZ) (p : Nat.Primes) {V : X.Opens}
    (hV : IsAffineOpen V) (s : Γ(X, V)) (hs : (baseChangeMap f (ZLoc p)).app V s = 0) :
    ∃ u : ℤ, ¬ ((p : ℕ) : ℤ) ∣ u ∧ (u : Γ(X, V)) * s = 0 := by
  set φ : Spec (CommRingCat.of (ZLoc p)) ⟶ SpecZ := Spec.map (CommRingCat.ofHom (Int.castRingHom _))
  have H : IsPullback (pullback.fst f φ) (pullback.snd f φ) f φ := IsPullback.of_hasPullback f φ
  have hiso := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := V)
    (UY := pullback.fst f φ ⁻¹ᵁ V) le_top (by simp) (by simp) (isAffineOpen_top _)
    (isAffineOpen_top _) hV
  have h0 : pushout.inl (f.appLE ⊤ V (by simp)) (φ.appLE ⊤ ⊤ le_top) s = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (pushoutSection H (US := ⊤) (UT := ⊤) (UX := V)
      (UY := pullback.fst f φ ⁻¹ᵁ V) le_top _ _)).1
    rw [map_zero, ← CommRingCat.comp_apply, pushout.inl_desc, ← Scheme.Hom.app_eq_appLE]
    exact hs
  let eR : ℤ ≃+* Γ(SpecZ, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv.symm
  let eT : ZLoc p ≃+* Γ(Spec (CommRingCat.of (ZLoc p)), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (ZLoc p))).commRingCatIsoToRingEquiv.symm
  have key : (φ.appLE ⊤ ⊤ le_top).hom =
      eT.toRingHom.comp ((algebraMap ℤ (ZLoc p)).comp eR.symm.toRingHom) := by
    have h := RingHom.ext_int ((φ.appLE ⊤ ⊤ le_top).hom.comp eR.toRingHom)
      (eT.toRingHom.comp (algebraMap ℤ (ZLoc p)))
    ext x
    have h' := RingHom.congr_fun h (eR.symm x)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply] at h' ⊢
    exact h'
  have hT : @IsLocalization _ _ ((Ideal.span {((p : ℕ) : ℤ)}).primeCompl.map eR) _ _
      (φ.appLE ⊤ ⊤ le_top).hom.toAlgebra := by
    rw [key]
    let : Algebra Γ(SpecZ, ⊤) (ZLoc p) := ((algebraMap ℤ (ZLoc p)).comp eR.symm.toRingHom).toAlgebra
    have h1 : IsLocalization ((Ideal.span {((p : ℕ) : ℤ)}).primeCompl.map eR) (ZLoc p) :=
      IsLocalization.isLocalization_of_base_ringEquiv _ _ eR
    exact (IsLocalization.isLocalization_iff_of_ringEquiv _ eT).mp h1
  obtain ⟨m, hm, hma⟩ := exists_mul_eq_zero_of_pushout_inl _ _ _ hT s h0
  obtain ⟨u, hu, rfl⟩ := Submonoid.mem_map.mp hm
  refine ⟨u, fun h => hu (Ideal.mem_span_singleton.mpr h), ?_⟩
  rw [← hma]
  congr 1
  exact (map_intCast ((f.appLE ⊤ V (by simp)).hom.comp eR.toRingHom) u).symm

theorem LocSectionsInj.proof : LocSectionsInj.Statement := by
  intro X f _ _ p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  choose N hNpos hN using fun U : X.affineOpens =>
    haveI := IsLocallyNoetherian.component_noetherian U
    exists_torsion_bound Γ(X, U)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => ((U : X.Opens) : Set X)) (fun U => (U : X.Opens).isOpen)
    (fun x _ => by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩)
  have hP : (∏ U ∈ t, N U) ≠ 0 := (Finset.prod_pos fun U _ => hNpos U).ne'
  refine ⟨ordCompl[(p : ℕ)] (∏ U ∈ t, N U), Nat.ordCompl_pos _ hP, Nat.not_dvd_ordCompl p.2 hP,
    fun k _ hmk W hW => ?_⟩
  have hcov : ∀ x : X, ∃ (U : X.affineOpens) (N' : ℕ), x ∈ (U : X.Opens) ∧
      ((ordCompl[(p : ℕ)] N' : ℕ) : ℤ) ∣ k ∧
      ∀ (n : ℤ) (a : Γ(X, U)), n ≠ 0 → (n : Γ(X, U)) * a = 0 → (N' : Γ(X, U)) * a = 0 := by
    intro x
    obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    have hd : ordCompl[(p : ℕ)] (N U) ∣ ordCompl[(p : ℕ)] (∏ U ∈ t, N U) :=
      Nat.ordCompl_dvd_ordCompl_of_dvd (Finset.dvd_prod_of_mem N hUt) _
    exact ⟨U, N U, hxU, dvd_trans (Int.natCast_dvd_natCast.mpr hd) hmk, hN U⟩
  rw [injective_iff_map_eq_zero ((baseChangeMap f (ZLoc p)).app W).hom]
  intro s hs
  refine X.IsSheaf.section_ext fun x hx => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
  have hVW' : V ≤ W := hVW
  refine ⟨V, hVW', hxV, ?_⟩
  obtain ⟨u, hu, hus⟩ := exists_coprime_mul_eq_zero f p hV (X.presheaf.map (homOfLE hVW').op s) (by
    rw [← ConcreteCategory.comp_apply, Scheme.Hom.naturality]
    simp [hs])
  rw [map_zero]
  exact eq_zero_of_coprime_mul_eq_zero f p p.2 k hcov (hVW'.trans hW) u hu _ hus

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadBundleNbhd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

variable {X : Scheme.{0}}

theorem SpreadsOn.toNbhd (f : X ⟶ SpecZ) (R : Type) [CommRing R] {E : (baseChange f R).Modules}
    {W : X.Opens} (hE : SpreadsOn f R E W) (htop : ⊤ ≤ baseChangeMap f R ⁻¹ᵁ W) :
    ∃ (hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι) (E' : (W : Scheme.{0}).Modules),
      IsVectorBundle E' ∧ Nonempty ((Scheme.Modules.pullback (toOpen f R W hW)).obj E' ≅ E) := by
  obtain ⟨E', hE', ⟨α⟩⟩ := hE
  have hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact htop (Set.mem_univ y)
  let U := baseChangeMap f R ⁻¹ᵁ W
  let u : baseChange f R ⟶ U := IsOpenImmersion.lift U.ι (𝟙 _) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact htop (Set.mem_univ y))
  have hu : u ≫ U.ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  have hcomp : u ≫ (baseChangeMap f R ∣_ W) = toOpen f R W hW := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hu,
      Category.id_comp, toOpen_ι]
  exact ⟨hW, E', hE', ⟨pullbackCompIso hcomp α ≪≫ (Scheme.Modules.pullbackComp u U.ι).app E ≪≫
    (Scheme.Modules.pullbackCongr hu).app E ≪≫ (Scheme.Modules.pullbackId _).app E⟩⟩

theorem spreadNbhd_of_isEmpty (f : X ⟶ SpecZ) (R : Type) [CommRing R] [IsEmpty (baseChange f R)]
    (E : (baseChange f R).Modules) :
    ∃ (W : X.Opens) (hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι)
      (E' : (W : Scheme.{0}).Modules), IsVectorBundle E' ∧
        Nonempty ((Scheme.Modules.pullback (toOpen f R W hW)).obj E' ≅ E) := by
  have hW : Set.range (baseChangeMap f R) ⊆ Set.range (⊥ : X.Opens).ι := by
    rintro _ ⟨y, rfl⟩
    exact isEmptyElim y
  have : IsEmpty ((⊥ : X.Opens) : Scheme.{0}) := ⟨fun x => x.2⟩
  let i : ((⊥ : X.Opens) : Scheme.{0}) ⟶ baseChange f R := isInitialOfIsEmpty.to _
  have hi : toOpen f R ⊥ hW ≫ i = 𝟙 _ := isInitialOfIsEmpty.hom_ext _ _
  exact ⟨⊥, hW, (Scheme.Modules.pullback i).obj E, fun x => isEmptyElim x,
    ⟨(Scheme.Modules.pullbackComp _ i).app E ≪≫ (Scheme.Modules.pullbackCongr hi).app E ≪≫
      (Scheme.Modules.pullbackId _).app E⟩⟩

theorem SpreadBundleNbhd.proof (h₁ : SpreadLocal.Statement) (h₂ : SpreadStep.Statement) :
    SpreadBundleNbhd.Statement := by
  intro X f _ _ p E hE
  classical
  rcases isEmpty_or_nonempty (baseChange f (ZLoc p)) with hX | hne
  · exact spreadNbhd_of_isEmpty f (ZLoc p) E
  obtain ⟨x₀⟩ := hne
  choose Wx hxW hWx using h₁ X f p E hE
  have hcov : Set.univ ⊆ ⋃ x, ((baseChangeMap f (ZLoc p) ⁻¹ᵁ Wx x :
      (baseChange f (ZLoc p)).Opens) : Set (baseChange f (ZLoc p))) :=
    fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩
  have hc : IsCompact (Set.univ : Set (baseChange f (ZLoc p))) := isCompact_univ
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover _ (fun x => (baseChangeMap f (ZLoc p) ⁻¹ᵁ Wx x).isOpen) hcov
  have key : ∀ s : Finset (baseChange f (ZLoc p)), ∃ W : X.Opens,
      (∀ x ∈ s, baseChangeMap f (ZLoc p) ⁻¹ᵁ Wx x ≤ baseChangeMap f (ZLoc p) ⁻¹ᵁ W) ∧
        SpreadsOn f (ZLoc p) E W := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨Wx x₀, fun x hx => absurd hx (Finset.notMem_empty x), hWx x₀⟩
    | insert a s ha ih =>
      obtain ⟨W, hW, hEW⟩ := ih
      obtain ⟨W', hW', hEW'⟩ := h₂ X f p E (Wx a) W (hWx a) hEW
      refine ⟨W', fun x hx => ?_, hEW'⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact le_sup_left.trans hW'
      · exact (hW x hx).trans (le_sup_right.trans hW')
  obtain ⟨W, hW, hEW⟩ := key t
  obtain ⟨hW', E', hE', hiso⟩ := hEW.toNbhd f (ZLoc p) (fun y _ => by
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact hW x hx hy)
  exact ⟨W, hW', E', hE', hiso⟩

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadHomInj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

theorem SpreadHomInj.proof (h₁ : GenericSectionsInj.Statement)
    (h₂ : PullbackFaithful.Statement.{0}) : SpreadHomInj.Statement := by
  intro X f _ _ a ha F G hF hG
  obtain ⟨m, hm, H⟩ := h₁ X f
  refine ⟨m, hm, fun n hn hmn ψ₁ ψ₂ e => ?_⟩
  have hk : IsUnit (((a : ℤ) * n : ℤ) : ℚ) := isUnit_intCast_rat _ (by positivity)
  have hG' : IsVectorBundle
      ((Scheme.Modules.pullback (X.homOfLE (invOpen_mul_le_left f a n))).obj G) :=
    hG.pullback_of_isOpenImmersion _
  refine h₂ _ _ (toInvOpen f ℚ ((a : ℤ) * n) hk)
    (H _ hk (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hmn) _)) _ _ hG' ψ₁ ψ₂ ?_
  unfold pullbackHomAlong at e
  rwa [cancel_epi, cancel_mono] at e

end GroundTheory.Heights₂.Heights.Model
end

