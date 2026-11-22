import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0094
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFacOfClosedPoint

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiRelOfExpT
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.PsiExpansion

theorem exists_sec_of_retract {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (m : Y ⟶ Y') (hm : h ≫ m = 𝟙 Y')
    (e : ∀ k, m ≫ φ' k = φ k) (s' : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain ⟨s, hs⟩ := exists_sec hL (φ' := φ) (ε' := ε) (fun U _ g => by simp only [e]) (H1.SectionArithmetic.pullSec s' m)
  refine ⟨s, fun Z r z J hJ => ?_⟩
  rw [hs Z _ z J hJ, H1.SectionArithmetic.sval_pullSec _ _ _ z hJ, Category.assoc, hm, Category.comp_id]

theorem snd_lift_unit {S : Scheme.{0}} (G : Over S) :
    (snd (𝟙_ _) G).left ≫ (lift (toUnit G) (𝟙 G)).left = 𝟙 (𝟙_ (Over S) ⊗ G).left := by
  have : snd (𝟙_ _) G ≫ lift (toUnit G) (𝟙 G) = 𝟙 _ := by
    refine CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) ?_
    rw [Category.assoc, lift_snd, Category.comp_id, Category.id_comp]
  exact congrArg CommaMorphism.left this

variable {R : Type} [CommRing R] [IsDomain R]

omit [IsDomain R] in

theorem exists_lift_of_retraction (F : Type) [Field F] [Algebra (FractionRing R) F] (g : F →+* FractionRing R)
    (hg : ∀ a, g (algebraMap (FractionRing R) F a) = a) {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) :
    ∃ κ' : T ⟶ TF (R := R) F, κ'.left ≫ jFK (R := R) F = κ.left := by
  let i : (TK R).left ⟶ Spec (CommRingCat.of F) := Spec.map (CommRingCat.ofHom g)
  have hi : i ≫ jFK (R := R) F = 𝟙 (TK R).left := by
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_id _))
    exact CommRingCat.hom_ext (RingHom.ext hg)
  have hκ : (κ.left ≫ i) ≫ jFK (R := R) F = κ.left := by
    rw [Category.assoc, hi, Category.comp_id]
  exact ⟨Over.homMk (κ.left ≫ i)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jK R) hκ).trans (Over.w κ))), hκ⟩

theorem exists_lift_frac {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) :
    ∃ κ' : T ⟶ TF (R := R) (FractionRing R), κ'.left ≫ jFK (R := R) (FractionRing R) = κ.left :=
  exists_lift_of_retraction (FractionRing R) (RingHom.id _) (fun _ => rfl) κ

omit [IsDomain R] in

theorem exists_sameG {G : Over (Spec (CommRingCat.of R))} {L : LB G.left} (hL : L.IsLB) {k : ℕ}
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd (𝟙_ _) G).left) (fun _ => (k : ℤ)))) :
    ∃ σ : H0 L k, SameG σ s :=
  exists_sec_of_retract hL _ _ (snd_lift_unit G)
    (fun _ => congrArg CommaMorphism.left (lift_snd (toUnit G) (𝟙 G))) s

theorem exists_sameB {D : DegPre R} {k : ℕ} (s : ∀ α, SecBT D (𝟙_ _) k α) : ∃ f : ∀ α, D.SecB k α, SameB f s := by
  have H : ∀ α, ∃ f : D.SecB k α, ∀ (Z : Scheme.{0}) (r : Z ⟶ _) (z : Z) (J), Good D.P.L z J →
      sval (s α) r z J = sval f (r ≫ (snd _ D.P.A).left) z J := fun α => by
    refine exists_sec_of_retract D.P.isLB _ _ (snd_lift_unit D.P.A) (fun i => ?_) (s α)
    fin_cases i
    · exact congrArg CommaMorphism.left (lift_snd (toUnit D.P.A) (𝟙 D.P.A))
    · refine congrArg CommaMorphism.left (show lift (toUnit D.P.A) (𝟙 D.P.A) ≫
        padd D.P.A (snd _ _) (toUnit _ ≫ D.c α) = padd D.P.A (𝟙 _) (toUnit _ ≫ D.c α) from ?_)
      simp only [padd, ← Category.assoc, comp_lift, lift_snd, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit D.P.A) (𝟙 D.P.A) ≫ toUnit _ ≫ D.c α = toUnit _ ≫ D.c α from ?_)
      rw [← Category.assoc, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit D.P.A) (𝟙 D.P.A) ≫ toUnit _ ≫ η[D.P.A] = toUnit _ ≫ η[D.P.A] from ?_)
      rw [← Category.assoc, comp_toUnit]
  choose f hf using H
  exact ⟨f, hf⟩

theorem psiRel_of_levelOneEq {D : DegPre R} {f₀ : ∀ α, D.SecB 1 α} {f : ∀ α, SecBT D (𝟙_ _) 1 α}
    (hs : SameB f₀ f) (h : PsiCompare.LevelOneEq D f₀) : PsiRel D (𝟙_ _) f := by
  intro χ T ρ κ y z J hJ
  obtain ⟨κ', hκ⟩ := exists_lift_frac κ
  have l : ∀ u : T ⟶ D.P.A, (lift ρ u).left ≫ (snd _ D.P.A).left = u.left := fun u =>
    congrArg CommaMorphism.left (lift_snd ρ u)
  have e := (h χ 0 rfl T κ' y z J hJ).trans (congrArg (fun q => sval (f₀ 0) (y * cT D T χ).left z J *
    (val (D.psi χ) q z J * rigV D z J).val) hκ)
  rw [hs χ _ _ z J hJ, hs 0 _ _ z J hJ, l, l]
  exact e.trans (mul_comm _ _)

theorem psiRel_of_expT : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (I : Ideal V), AdmBase V I → ∀ (D : DegData V I) (A : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U₀ : Unif I D A G), Under U U₀.toUnifPre → ∀ (σ : U.SecGT (𝟙_ _) 1) (f : ∀ α, SecBT D.toPre (𝟙_ _) 1 α), U.ExpT (𝟙_ _) 1 σ f → PsiRel D.toPre (𝟙_ _) f := by
  intro h₁ h₂ V _ _ _ I hV D A G _ _ U U₀ hU σ f hE
  obtain ⟨σ₁, hσ₁⟩ := exists_sameG U.P.L.isLB σ
  obtain ⟨f₀, hf₀⟩ := exists_sameB f
  have ht : H0 U.P.L.L 1 = H0 U₀.toUnifPre.LG.L 1 := by rw [hU.2.1]
  have hc : HEq (cast ht σ₁) σ₁ := cast_heq ht σ₁
  have H := ((PreForm.under_exists_and_expands h₁ h₂ V I D A G U.semi).2.2 U U₀.toUnifPre hU 1 σ f (cast ht σ₁) f₀
    (fun τ hτ z J hJ => by
      obtain rfl : τ = σ₁ := eq_of_heq (hτ.trans hc)
      rw [hσ₁ _ _ z J hJ, Category.id_comp])
    (fun α z J hJ => by rw [hf₀ α _ _ z J hJ, Category.id_comp])).1 hE
  exact psiRel_of_levelOneEq hf₀
    (PsiCompare.levelOneEq_of_expandsAt h₁.globalFns hV U₀.toUnifPre (U₀.expand 1 le_rfl) _ f₀ H)

end GlobalTheory.PsiExpansion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PureEqZeroOfVanishingOnTorsion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.PureZero

theorem lt_of_big {g N N' : ℕ} (h : Big g N N') (hg : 1 ≤ g) : N ^ g * g.factorial < N' := by
  have hs := h.sep
  have h4 : (4 : ℝ) ≤ N := by exact_mod_cast h.four
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have h1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ g := one_le_pow₀ (by norm_num)
  have h2 : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ ((g : ℝ) / 2 - 1) := by
    have : (2 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ ((g : ℝ) / 2 - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_neg_one] at this
    linarith
  have h3 : (1 / 2 : ℝ) ≤ (g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1) := by
    have : (1 : ℝ) ≤ (g : ℝ) * (3 / 2 : ℝ) ^ g := one_le_mul_of_one_le_of_one_le hg' h1
    nlinarith
  set C := (g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)
  have hM : (0 : ℝ) ≤ ((N ^ g * g.factorial : ℕ) : ℝ) := Nat.cast_nonneg _
  have h5 : (1 : ℝ) ≤ 2 * C * N := by nlinarith
  have : ((N ^ g * g.factorial : ℕ) : ℝ) < N' := by nlinarith
  exact_mod_cast this

theorem sec_eq_zero_of_dim_zero {K : Type} [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (hg : P.g = 0)
    {M : LB (Out.baseOver (Sp K) ⊗ P.A).left} (s : M.Sec)
    (hs : ¬ ⊤ ≤ (Out.ptSecT P.A (1 : Out.baseOver (Sp K) ⟶ P.A)).left ⁻¹ᵁ Out.nonzeroLocus s) (j : M.ι) :
    s.f j = 0 := by
  have := polAV_isIntegral_of_isAlgClosed K P
  have : Etale P.A.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 (hg ▸ P.smoothDim)
  let e : Sp K ⟶ P.A.left := (1 : Out.baseOver (Sp K) ⟶ P.A).left
  have := isOpenImmersion_of_section_of_etale P.A.hom e (Over.w _)
  have : IsDominant e := ⟨e.isOpenEmbedding.isOpen_range.dense ⟨_, (default : PrimeSpectrum K), rfl⟩⟩
  have : IsIso (snd (Out.baseOver (Sp K)) P.A).left :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 (Sp K)) P.A.hom))
  let z : Sp K ⟶ (Out.baseOver (Sp K) ⊗ P.A).left := (Out.ptSecT P.A (1 : Out.baseOver (Sp K) ⟶ P.A)).left
  have hz : z = e ≫ inv (snd (Out.baseOver (Sp K)) P.A).left := by
    rw [IsIso.eq_comp_inv]
    exact congrArg (·.left) (lift_snd (𝟙 _) (1 : Out.baseOver (Sp K) ⟶ P.A))
  have hd : IsDominant z := by rw [hz]; infer_instance
  have : IsReduced (Out.baseOver (Sp K) ⊗ P.A).left :=
    isReduced_of_isOpenImmersion (snd (Out.baseOver (Sp K)) P.A).left
  by_contra hne
  have hb : ((Out.baseOver (Sp K) ⊗ P.A).left.basicOpen (s.f j) : Set (Out.baseOver (Sp K) ⊗ P.A).left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h => hne ((basicOpen_eq_bot_iff _).1 (TopologicalSpace.Opens.ext h))
  obtain ⟨y, hy⟩ := hd.denseRange.exists_mem_open (TopologicalSpace.Opens.isOpen _) hb
  refine hs fun y' _ => ?_
  have : y' = y := Subsingleton.elim (α := PrimeSpectrum K) _ _
  subst this
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy⟩

theorem twist_eq_zero (h : Out.Laws) (h₂ : Out.Laws2) {K : Type} [Field K] [IsAlgClosed K]
    (P : Out.PolAV (Sp K)) {g N N' d : ℕ} (hB : Big g N N') (hN' : (N' : K) ≠ 0) (hg : P.g ≤ g) (hd : 1 ≤ d)
    (hd' : d ≤ N ^ g * g.factorial) (c : Out.baseOver (Sp K) ⟶ P.A)
    (s : LB.Sec (Out.twistLB P.A P.L (N * d) c))
    (hs : ∀ x : Out.baseOver (Sp K) ⟶ P.A, x ^ N' = 1 → ¬ ⊤ ≤ (Out.ptSecT P.A x).left ⁻¹ᵁ Out.nonzeroLocus s) :
    ∀ j, s.f j = 0 := by
  rcases Nat.eq_zero_or_pos P.g with h0 | h0
  · exact sec_eq_zero_of_dim_zero P h0 s (hs 1 (one_pow _))
  by_contra hne
  push Not at hne
  have hM1 : 1 ≤ N' := Nat.pos_of_ne_zero fun e => hN' (by rw [e, Nat.cast_zero])
  have hcard := (h.mulN (Sp K) P N' hM1).2.2.2.2 K (𝟙 _) hN'
  have h₄ := card_torsion_zeros_twist_le h h₂ K P N d N' c h0 hB.four hd hN' s hne
  have e : N' ^ (2 * P.g) = N' ^ 2 * N' ^ (2 * P.g - 2) := by rw [← pow_add]; congr 1; omega
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => and_iff_left_of_imp (hs x)), hcard, e] at h₄
  have h₅ := Nat.le_of_mul_le_mul_right h₄ (pow_pos hM1 _)
  have h₆ := lt_of_big hB (h0.trans_le hg)
  have h₇ : N ^ P.g * P.g.factorial ≤ N ^ g * g.factorial :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by have := hB.four; omega) hg) (Nat.factorial_le hg)
  have h₈ := Nat.mul_le_mul h₇ hd'
  nlinarith

theorem pure_eq_zero_of_vanishing_on_torsion :
    Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' d : ℕ) (π : Φ.Pol N), Big g N N' → (N' : k) ≠ 0 → π.PB.g ≤ g → 1 ≤ d → d ≤ N ^ g * g.factorial → ∀ (α : Φ.E.X) (φ : (Φ.H d).Sec), Φ.Pure α φ → (∀ x : Φ.Pt, x ^ N' = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ) → ∀ l, φ.f l = 0) := by
  intro h h₂ k _ _ Φ g N N' d π hB hN' hg hd hd' α φ hφ hx
  have hM1 : 1 ≤ N' := Nat.pos_of_ne_zero fun e => hN' (by rw [e, Nat.cast_zero])
  obtain ⟨s, hs0, hs⟩ := (GlobalTheory.T.pureWeightSection_to_twistedPolarisationPower k Φ N d π α (by have := hB.four; omega) hd).1 φ hφ
  refine hs0 (twist_eq_zero h h₂ π.PB hB hN' hg hd hd' _ s fun b hb => ?_)
  have := π.hom
  have hb' : (b ≫ π.β.inv) ^ N' = 1 := by
    rw [← cancel_mono π.β.hom, MonObj.pow_comp, MonObj.one_comp, Category.assoc, π.β.inv_hom_id,
      Category.comp_id, hb]
  obtain ⟨x, hx1, hxq⟩ := (TorsLift.points_lift k Φ.E Φ.G Φ.D N' hM1).2.1 _ hb'
  have e : x ≫ Φ.D.q ≫ π.β.hom = b := by
    rw [← Category.assoc, hxq, Category.assoc, π.β.inv_hom_id, Category.comp_id]
  rw [← e]
  exact fun hh => hx x hx1 ((hs x).2 hh)

end GlobalTheory.PureZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusIsAffineHomAndSplitsFinite
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem torus_isAffineHom_and_splits_finite : NaSt.{0} := by
  intro k _ T _ hT
  obtain ⟨Ω, _, _, X, _, _, _, e, he⟩ := hT.splits
  have hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :=
    Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :=
    ⟨fun x => ⟨(default : Spec (.of Ω)), Subsingleton.elim (α := Spec (.of k)) _ _⟩⟩
  have haff : IsAffineHom T.hom := by
    refine isAffineHom_of_isAffineHom_pullback_snd_of_fpqc _ _ _ T.hom _ hsurj hflat inferInstance ?_
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    have h : IsAffineHom (e.hom.left ≫ (splitTorus (Spec (.of Ω)) X).hom) := inferInstance
    rw [Over.w] at h
    exact h
  refine ⟨haff, ?_⟩
  obtain ⟨k', _, _, _, e', he'⟩ := IsoFinite.exists_finite_iso k Ω T (splitTorus (Spec (.of k)) X)
    haff inferInstance hT.finiteType inferInstance
    ⟨e ≪≫ (Diag.baseChangeIso _ X).symm,
      inferInstanceAs (IsMonHom (e.hom ≫ (Diag.baseChangeIso _ X).inv))⟩
  exact ⟨k', inferInstance, inferInstance, inferInstance, X, inferInstance, inferInstance, inferInstance,
    e' ≪≫ Diag.baseChangeIso _ X, inferInstanceAs (IsMonHom (e'.hom ≫ (Diag.baseChangeIso _ X).hom))⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnEqOfFineCharts
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section

namespace GlobalTheory.ZJ.TestNorm

open CubeGen

variable {p : ℕ} [Fact p.Prime] {X Y Z : Scheme.{0}}

abbrev z₀ (p : ℕ) [Fact p.Prime] : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)

def sn (p : ℕ) [Fact p.Prime] : (Sp (PadicAlgCl p)).presheaf.stalk (z₀ p) →* ℝ :=
  (normHom : PadicAlgCl p →*₀ ℝ).toMonoidHom.comp (ev (z₀ p)).toRingHom.toMonoidHom

def un (p : ℕ) [Fact p.Prime] : ((Sp (PadicAlgCl p)).presheaf.stalk (z₀ p))ˣ →* ℝ :=
  (sn p).comp (Units.coeHom _)

theorem sn_val (u : ((Sp (PadicAlgCl p)).presheaf.stalk (z₀ p))ˣ) : sn p u.val = un p u := rfl

theorem un_pos (u : ((Sp (PadicAlgCl p)).presheaf.stalk (z₀ p))ˣ) : 0 < un p u :=
  norm_pos_iff.2 (u.isUnit.map (ev (z₀ p))).ne_zero

theorem sn_gs (x : Sp (PadicAlgCl p) ⟶ X) {U : X.Opens} (h : x (z₀ p) ∈ U) (a : Γ(X, U)) :
    sn p (gs x (z₀ p) U a) = ‖valF x U a‖ := congrArg norm (ev_gs x _ h a)

theorem un_gm (x : Sp (PadicAlgCl p) ⟶ X) {U : X.Opens} (h : x (z₀ p) ∈ U) (a : Γ(X, U)ˣ) :
    un p (gm x (z₀ p) U a) = ‖valF x U a.val‖ := congrArg norm (ev_gm x _ h a)

theorem gs_comp (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens) (h : q (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ q) z U a = (r.stalkMap z).hom (gs q (r z) U a) := by
  rw [← gs_pull r q z U h, gs_stalkMap r z (q ⁻¹ᵁ U) h, gs_pull (𝟙 Y) q (r z) U h, Category.id_comp]

theorem gm_comp (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens) (h : q (r z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (r ≫ q) z U a = Units.map (r.stalkMap z).hom.toMonoidHom (gm q (r z) U a) := by
  refine Units.ext ?_
  rw [← gs_unit (r ≫ q) z U h, gs_comp r q z U h, gs_unit q (r z) U h]
  rfl

theorem mem_of_cPt (b : Sp (OO p) ⟶ X) {U : X.Opens} (h : b (cPt p) ∈ U) : ⊤ ≤ b ⁻¹ᵁ U :=
  fun y _ => (IsLocalRing.specializes_closedPoint y).mem_open (b ⁻¹ᵁ U).isOpen h

theorem gen_mem (b : Sp (OO p) ⟶ X) {U : X.Opens} (h : b (cPt p) ∈ U) : (gPt p ≫ b) (z₀ p) ∈ U :=
  mem_of_cPt b h (show gPt p (z₀ p) ∈ (⊤ : (Sp (OO p)).Opens) from trivial)

theorem isUnit_iff_norm (v : OO p) : IsUnit v ↔ ‖(v : PadicAlgCl p)‖ = 1 := by
  have le : ∀ u : OO p, ‖(u : PadicAlgCl p)‖ ≤ 1 := fun u =>
    (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 u.2
  constructor
  · intro h
    obtain ⟨u, hu⟩ := h.exists_right_inv
    have e : ‖(v : PadicAlgCl p)‖ * ‖(u : PadicAlgCl p)‖ = 1 := by
      rw [← norm_mul]
      exact (congrArg (fun t : OO p => ‖(t : PadicAlgCl p)‖) hu).trans norm_one
    have := le u
    have := le v
    have := norm_nonneg (v : PadicAlgCl p)
    nlinarith
  · intro h
    have h0 : (v : PadicAlgCl p) ≠ 0 := norm_pos_iff.1 (by rw [h]; exact one_pos)
    refine IsUnit.of_mul_eq_one ⟨(v : PadicAlgCl p)⁻¹,
      (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).2 (by rw [norm_inv, h, inv_one])⟩ ?_
    exact Subtype.ext (mul_inv_cancel₀ h0)

theorem sn_integral (b : Sp (OO p) ⟶ X) {U : X.Opens} (h : b (cPt p) ∈ U) (a : Γ(X, U)) :
    sn p (gs (gPt p ≫ b) (z₀ p) U a) ≤ 1 ∧
      (sn p (gs (gPt p ≫ b) (z₀ p) U a) = 1 ↔ b (cPt p) ∈ X.basicOpen a) := by
  have h' := mem_of_cPt b h
  have hg := gen_mem b h
  let v : OO p := (Scheme.ΓSpecIso (CommRingCat.of (OO p))).hom.hom ((b.appLE U ⊤ h').hom a)
  have e : valF (gPt p ≫ b) U a = (v : PadicAlgCl p) := by
    rw [valF, dif_pos ((top_le_iff_mem _ U _).2 hg)]
    have e₁ := Scheme.Hom.appLE_comp_appLE (gPt p) b U ⊤ ⊤ h' le_top
    have e₂ := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (OO p).subtype)
    have e₃ : (gPt p).appLE ⊤ ⊤ le_top = (gPt p).appTop := (Scheme.Hom.app_eq_appLE _).symm
    rw [← e₁, e₃]
    exact congrArg (fun q => q.hom ((b.appLE U ⊤ h').hom a)) e₂
  rw [sn_gs _ hg, e]
  refine ⟨(mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 v.2, (isUnit_iff_norm v).symm.trans ?_⟩
  have e₄ : (Sp (OO p)).basicOpen ((b.appLE U ⊤ h').hom a) = PrimeSpectrum.basicOpen v :=
    basicOpen_eq_of_affine' _
  have e₅ := Scheme.basicOpen_appLE b ⊤ U h' a
  have e₆ : cPt p ∈ (Sp (OO p)).basicOpen ((b.appLE U ⊤ h').hom a) ↔ b (cPt p) ∈ X.basicOpen a := by
    erw [e₅]
    exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  rw [← e₆, e₄]
  exact (IsLocalRing.notMem_maximalIdeal).symm

theorem un_integral (b : Sp (OO p) ⟶ X) {U : X.Opens} (h : b (cPt p) ∈ U) (a : Γ(X, U)ˣ) :
    un p (gm (gPt p ≫ b) (z₀ p) U a) = 1 := by
  rw [← sn_val, ← gs_unit _ _ _ (gen_mem b h)]
  refine (sn_integral b h a.val).2.2 ?_
  rw [Scheme.basicOpen_of_isUnit _ a.isUnit]
  exact h

theorem un_eq_of_charts {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {K : Type} [Field K]
    [Algebra V K] [IsFractionRing V K] {H HK : Scheme.{0}} {f : H ⟶ Sp V} [Smooth f] [GeometricallyIntegral f]
    {j : HK ⟶ H} {fK : HK ⟶ Sp K} (hK : IsPullback j fK f (spMap (algebraMap V K))) (e : Sp V ⟶ H)
    (he : e ≫ f = 𝟙 _) {α : Type} (U : α → H.Opens) (g : ∀ a b, Γ(H, U a ⊓ U b)ˣ) (r : ∀ a, Γ(HK, j ⁻¹ᵁ U a)ˣ)
    (hU : ∀ x, ∃ a, x ∈ U a)
    (hr : ∀ a a' x, j x ∈ U a → j x ∈ U a' →
      gm (𝟙 HK) x _ (r a) = gm j x _ (g a a') * gm (𝟙 HK) x _ (r a')) :
    ∃ u : Γ(Sp K, ⊤)ˣ, ∀ (c : Sp (OO p) ⟶ H) (cK : Sp (PadicAlgCl p) ⟶ HK), cK ≫ j = gPt p ≫ c → ∀ a,
      c (cPt p) ∈ U a → un p (gm cK (z₀ p) _ (r a)) = un p (gm (cK ≫ fK) (z₀ p) ⊤ u) := by
  have hs := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  let eK : Sp K ⟶ HK := hK.lift (spMap (algebraMap V K) ≫ e) (𝟙 _) (by simp [he])
  have h₁ : eK ≫ j = spMap (algebraMap V K) ≫ e := hK.lift_fst _ _ _
  have h₂ : eK ≫ fK = 𝟙 _ := hK.lift_snd _ _ _
  obtain ⟨a₀, ha₀⟩ := hU (e (IsLocalRing.closedPoint V))
  have hA : ⊤ ≤ e ⁻¹ᵁ U a₀ := fun y _ => (IsLocalRing.specializes_closedPoint y).mem_open (e ⁻¹ᵁ U a₀).isOpen ha₀
  have hA'' : ⊤ ≤ eK ⁻¹ᵁ (j ⁻¹ᵁ U a₀) := fun y _ => by
    show (eK ≫ j) y ∈ U a₀
    rw [h₁]
    exact hA (show spMap (algebraMap V K) y ∈ (⊤ : (Sp V).Opens) from trivial)
  let u : Γ(Sp K, ⊤)ˣ := res hA'' (pullU eK _ (r a₀))
  let r' : ∀ a, Γ(HK, j ⁻¹ᵁ U a)ˣ := fun a => r a * res (le_top : j ⁻¹ᵁ U a ≤ fK ⁻¹ᵁ ⊤) (pullU fK ⊤ u⁻¹)
  have v : ∀ (Z : Scheme.{0}) (q : Z ⟶ HK) (z : Z) a, j (q z) ∈ U a →
      gm q z _ (r' a) = gm q z _ (r a) * (gm (q ≫ fK) z ⊤ u)⁻¹ := fun Z q z a h =>
    (map_mul _ _ _).trans (congrArg (_ * ·) (((gm_res q z _ h _).trans (gm_pull q fK z ⊤ trivial _)).trans
      (map_inv _ _)))
  obtain ⟨s, ⟨hs₁, -, hs₂⟩, -⟩ := DvrModel.existsUnique_isUnit_appLE_eq hK hs (U := U) (g := fun a b => (g a b).val)
    (W := fun a => j ⁻¹ᵁ U a) (fun _ => rfl) hU (fun a b => (g a b).isUnit) (r := fun a => (r' a).val)
    (fun a b => fn_ext fun x hx => by
      refine (gs_res (𝟙 HK) x _ hx _).trans (Eq.trans ?_ ((gs_mul (𝟙 HK) x _ hx _ _).trans
        (congrArg₂ (· * ·) (gs_appLE j _ _ _ (𝟙 HK) x hx _) (gs_res (𝟙 HK) x _ hx _))).symm)
      rw [Category.id_comp, gs_unit (𝟙 HK) x _ hx.1, gs_unit (𝟙 HK) x _ hx.2, gs_unit j x (U a ⊓ U b) hx,
        v _ (𝟙 HK) x a hx.1, v _ (𝟙 HK) x b hx.2, hr a b x hx.1 hx.2, _root_.mul_assoc, Units.val_mul])
    (fun a => (r' a).isUnit) he h₁ (A := ⊤) trivial hA (A' := ⊤) rfl hA'' (u := 1) isUnit_one (by
      rw [map_one]
      refine fn_ext fun y hy => ?_
      refine Eq.trans ?_ (gs_appLE eK _ _ _ (𝟙 _) y hy _).symm
      rw [Category.id_comp, gs_unit eK y _ (hA'' hy), v _ eK y a₀ (hA'' hy), h₂]
      have : gm (𝟙 (Sp K)) y ⊤ u = gm eK y _ (r a₀) := by
        refine ((gm_res _ y _ hy _).trans (gm_pull (𝟙 _) eK y _ (hA'' hy) _)).trans ?_
        rw [Category.id_comp]
      rw [this, mul_inv_cancel, gs_eq _ y ⊤ hy, map_one, map_one, Units.val_one])
  refine ⟨u, fun c cK hc a ha => ?_⟩
  have hm : j (cK (z₀ p)) ∈ U a := by
    show (cK ≫ j) _ ∈ U a
    rw [hc]
    exact gen_mem c ha
  have e₁ : un p (gm cK (z₀ p) _ (r' a)) = 1 := by
    rw [← un_integral c ha (hs₁ a).unit, ← hc]
    refine congrArg (un p) (Units.ext ?_)
    rw [← gs_unit cK _ _ hm, ← gs_unit (cK ≫ j) _ _ hm, ← hs₂ a]
    exact gs_appLE j _ _ _ cK _ hm _
  rw [v _ cK _ a hm, map_mul, map_inv] at e₁
  exact (mul_inv_eq_one₀ (un_pos _).ne').1 e₁

theorem un_eq_of_fine_charts {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {K : Type} [Field K]
    [Algebra V K] [IsFractionRing V K] {H HK : Scheme.{0}} {f : H ⟶ Sp V} [Smooth f] [GeometricallyIntegral f]
    {j : HK ⟶ H} {fK : HK ⟶ Sp K} (hK : IsPullback j fK f (spMap (algebraMap V K))) (e : Sp V ⟶ H)
    (he : e ≫ f = 𝟙 _) {α κ : Type} (U : α → H.Opens) (g : ∀ a b, Γ(H, U a ⊓ U b)ˣ) (W : α → κ → HK.Opens)
    (r : ∀ a b, Γ(HK, W a b)ˣ) (hU : ∀ x, ∃ a, x ∈ U a) (hW : ∀ a x, j x ∈ U a ↔ ∃ b, x ∈ W a b)
    (hr : ∀ a b a' b' x, x ∈ W a b → x ∈ W a' b' →
      gm (𝟙 HK) x _ (r a b) = gm j x _ (g a a') * gm (𝟙 HK) x _ (r a' b'))
    {c c' : Sp (OO p) ⟶ H} {cK cK' : Sp (PadicAlgCl p) ⟶ HK} (hc : cK ≫ j = gPt p ≫ c) (hc' : cK' ≫ j = gPt p ≫ c')
    (h : c ≫ f = c' ≫ f) {a a' : α} {b b' : κ} (ha : c (cPt p) ∈ U a) (ha' : c' (cPt p) ∈ U a')
    (hb : cK (z₀ p) ∈ W a b) (hb' : cK' (z₀ p) ∈ W a' b') :
    un p (gm cK (z₀ p) _ (r a b)) = un p (gm cK' (z₀ p) _ (r a' b')) := by
  have le : ∀ a b, W a b ≤ j ⁻¹ᵁ U a := fun a b x hx => (hW a x).2 ⟨b, hx⟩
  choose R hR using fun a => glue_unit (j ⁻¹ᵁ U a) (W a) (le a)
    (fun x hx => TopologicalSpace.Opens.mem_iSup.2 ((hW a x).1 hx)) (r a) (fun b b' x hx => by
      rw [hr a b a b' x hx.1 hx.2, mul_eq_right.1 (hr a b a b x hx.1 hx.1).symm, _root_.one_mul])
  have v : ∀ (Z : Scheme.{0}) (q : Z ⟶ HK) (z : Z) a b, q z ∈ W a b → gm q z _ (r a b) = gm q z _ (R a) :=
    fun Z q z a b h => by rw [← hR a b, gm_res q z _ h]
  obtain ⟨u, hu⟩ := un_eq_of_charts (p := p) hK e he U g R hU fun a a' x hx hx' => by
    obtain ⟨b, hb⟩ := (hW a x).1 hx
    obtain ⟨b', hb'⟩ := (hW a' x).1 hx'
    rw [← v _ (𝟙 HK) x a b hb, ← v _ (𝟙 HK) x a' b' hb', hr a b a' b' x hb hb']
  have := DvrModel.isOpenImmersion_generic (IsPullback.of_id_snd (f := spMap (algebraMap V K)))
  rw [v _ _ _ _ _ hb, v _ _ _ _ _ hb', hu c cK hc a ha, hu c' cK' hc' a' ha']
  refine congrArg (fun q => un p (gm q (z₀ p) ⊤ u)) ?_
  rw [← cancel_mono (spMap (algebraMap V K)), Category.assoc, Category.assoc, ← hK.w, ← Category.assoc, hc,
    ← Category.assoc, hc', Category.assoc, Category.assoc, h]

theorem exists_norm_ext {L : LB X} (hL : L.IsLB) (x : Sp (PadicAlgCl p) ⟶ X) (S : L.ι → ℝ → Prop)
    (hS : ∀ j t, S j t → 0 < t ∧ x (z₀ p) ∈ L.U j)
    (hS' : ∀ j t j' t', S j t → S j' t' → un p (gm x (z₀ p) _ (L.g j j')) * t = t') :
    ∃ n : L.ι → ℝ, (∀ j, 0 < n j) ∧ (∀ j j', x (z₀ p) ∈ L.U j → x (z₀ p) ∈ L.U j' →
      un p (gm x (z₀ p) _ (L.g j j')) * n j = n j') ∧ ∀ j t, S j t → n j = t := by
  classical
  obtain ⟨i, t₀, h₀, hi, H⟩ : ∃ i t₀, 0 < t₀ ∧ x (z₀ p) ∈ L.U i ∧
      ∀ j t, S j t → un p (gm x (z₀ p) _ (L.g i j)) * t₀ = t := by
    by_cases h : ∃ j t, S j t
    · obtain ⟨i, t₀, h⟩ := h
      exact ⟨i, t₀, (hS _ _ h).1, (hS _ _ h).2, fun j t h' => hS' _ _ _ _ h h'⟩
    · obtain ⟨i, hi⟩ := exists_chart hL (x (z₀ p))
      exact ⟨i, 1, one_pos, hi, fun j t h' => absurd ⟨j, t, h'⟩ h⟩
  refine ⟨fun j => un p (gm x (z₀ p) _ (L.g i j)) * t₀, fun j => mul_pos (un_pos _) h₀, fun j j' hj hj' => ?_, H⟩
  rw [← _root_.mul_assoc, ← map_mul, _root_.mul_comm (gm x _ _ _), gm_cocycle hL x _ hi hj hj']

end GlobalTheory.ZJ.TestNorm
end
end

