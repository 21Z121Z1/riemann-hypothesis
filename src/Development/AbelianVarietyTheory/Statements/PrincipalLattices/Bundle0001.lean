import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.CmHostBarHalfIntegerGenerator
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0030
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0032
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

-- bundled from Development.AbelianVarietyTheory.Statements.PrincipalLattices.DimPosOfHasType
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.NumInh

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in

theorem exists_isDiffOf {P P' : Out.PolAV (Sp (𝓞 K))} (F : GenFib P) (F' : GenFib P') (f : P.A ⟶ P'.A) [IsMonHom f] :
    ∃ M, F.IsDiffOf F' f M := by
  obtain ⟨f₀, _, e⟩ := HomDescent.exists_isMonHom_pull F.fib.2.1 F'.fib.2.1 f
  have := F'.P₀.isAb.comm
  have tan : ∀ i, IsTangent (F.v i ≫ f₀) := fun i => HomLinear.isTangent_comp f₀ (F.basis.1 i)
  choose m hm using fun i => (F'.basis.2 _ (tan i)).exists
  refine ⟨Fintype.linearCombination K m, fun u c ⟨hu, w, hw, hc⟩ =>
    ⟨HomLinear.isTangent_comp f hu, w ≫ f₀, ?_, ?_⟩⟩
  · unfold IsVecOver at hw ⊢
    rw [Over.comp_left, Category.assoc, e, ← Category.assoc, hw, Over.comp_left, Category.assoc]
  · refine (LieComb.lieComb_algebra K F'.P₀.A _ F'.v F'.basis.1).2.2.1 _ m _ c _ hm ?_
    obtain ⟨y, hy, rfl⟩ := hc
    exact ⟨fun i => y i ≫ f₀, fun i => by rw [Over.comp_left, hy, Category.assoc]; rfl,
      (map_list_prod (IsMonHom.monoidHom f₀ (epsR K)) _).trans (by rw [List.map_ofFn]; rfl)⟩

theorem exists_key (hT : Out.SecTwistSt) {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P) :
    ∃ (rig : LB.Gen (F.P₀.L.pull (eSec F.P₀.A))) (th : F.P₀.L.Sec), rig.IsGen ∧
      ∀ s : Sp K, ∃ x : F.P₀.A.left, F.P₀.A.hom x = s ∧ x ∈ Out.nonzeroLocus th := by
  obtain ⟨rig, hr⟩ := F.P₀.rigid
  obtain ⟨b, hb⟩ := principalPolarisation_exists_unique_section hT F.P₀
  obtain ⟨a, -, hu⟩ := hb b
  refine ⟨rig, b, hr, KeyPow.exists_mem_nonzeroLocus _ b ?_⟩
  by_contra hn
  push Not at hn
  exact zero_ne_one ((hu 0 fun i => by rw [hn i, mul_zero]).trans (hu 1 fun i => by rw [hn i, mul_zero]).symm)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem dim_pos_of_lieMult {S : Scheme.{0}} {O k : Type} [CommRing O] [Field k] {G : Over S} [GrpObj G] {act : OAct O G}
    {t : Sp k ⟶ S} {τ : O →+* k} (h : LieMult act t τ 1) {g : ℕ} (hg : SmoothOfRelativeDimension g G.hom) : 1 ≤ g := by
  by_contra h0
  obtain rfl : g = 0 := by omega
  have : Etale G.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hg
  obtain ⟨v, hv, hu⟩ := h
  have hs : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) hs
  have hnil : IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro r hr s hs
    have hr' : r.fst = 0 := hr
    have hs' : s.fst = 0 := hs
    rw [Ideal.mem_bot]
    ext <;> simp [hr', hs']
  have key : ∀ c : k, (v 0).left = spMap (epsScale c) ≫ (v 0).left := fun c => by
    refine FormallyUnramified.hom_ext (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)
      (isNilpotent_ker_specMap _ hnil) G.hom ?_ ?_
    · rw [← Category.assoc, spMap_comp_spMap]
      congr 2
      ext a <;> simp [epsScale]
    · rw [Category.assoc, Over.w (v 0)]
      show spMap _ ≫ t = spMap _ ≫ spMap _ ≫ t
      rw [← Category.assoc, spMap_comp_spMap]
      congr 2
      ext a <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]
  have e : ∀ c : Fin 1 → k, ∃ u : Fin 1 → (epsPt t ⟶ G),
      (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (v i).left) ∧ v 0 = (List.ofFn u).prod := fun c =>
    ⟨v, fun i => by rw [Subsingleton.elim i 0]; exact key _, by simp⟩
  exact zero_ne_one (congrFun ((hu _ (hv 0)).unique (e 0) (e 1)) 0)

theorem exists_char (hs : Splits E K) {ρ : 𝓞 K} (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) : ∃ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ := by
  obtain ⟨τ⟩ : Nonempty (𝓞 E →+* 𝓞 K) := (Nat.card_pos_iff.1 (hs ▸ Module.finrank_pos)).1
  have e : τ H.rt ^ 2 = ρ ^ 2 := by rw [← map_pow, H.rt_sq, hρ]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 e with e | e
  · exact ⟨τ, e⟩
  · exact ⟨τ.comp H.bar.toRingHom, by
      show τ (H.bar H.rt) = ρ
      rw [Test.bar_rt, map_neg, e, neg_neg]⟩

theorem dim_pos_of_hasType (hs : Splits E K) {ρ : 𝓞 K} (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) (T : PAT H (Sp (𝓞 K))) {q : ℕ}
    (hT : HasType H T.t.act ρ 1 q) : 1 ≤ T.g := by
  obtain ⟨τ, hτ⟩ := exists_char hs hρ
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  exact dim_pos_of_lieMult ((hT ℂ (σ.comp (algebraMap (𝓞 K) K)) (σ.injective.comp RingOfIntegers.coe_injective)
    ((σ.comp (algebraMap (𝓞 K) K)).comp τ)).1 (by rw [RingHom.comp_apply, hτ])) T.dim

omit [IsCMField E] in

theorem exists_bound {I : Type} [Fintype I] (a : I → 𝓞 E) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ j (τ : E →+* ℂ), ‖τ (a j : E)‖ ≤ Λ ^ 2 := by
  have h0 : 0 ≤ ∑ x : I × (E →+* ℂ), ‖x.2 (a x.1 : E)‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨1 + ∑ x : I × (E →+* ℂ), ‖x.2 (a x.1 : E)‖, by linarith, fun j τ => ?_⟩
  have := Finset.single_le_sum (f := fun x : I × (E →+* ℂ) => ‖x.2 (a x.1 : E)‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ (j, τ))
  nlinarith

theorem exists_data (hU : ThetaUnifAV) (hL : Out.Laws) {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ₁ p q) :
    ∃ (FA : ∀ b, GenFib (X.A b).pol) (FB : GenFib X.B.pol) (hA : ∀ b, HermFam K (Fin (FA b).P₀.g → K))
      (hB : HermFam K (Fin FB.P₀.g → K))
      (M : ∀ j : Fin p ⊕ Fin q, (Fin (FA j.isLeft).P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)) (Λ : ℝ),
      (∀ b, 1 ≤ (FA b).P₀.g ∧ (FA b).IsHerm (hA b)) ∧ FB.IsHerm hB ∧ (∀ j, (FA j.isLeft).IsDiffOf FB (X.φ j) (M j)) ∧
      0 < Λ ∧ ∀ j (τ : E →+* ℂ), ‖τ (X.hh j : E)‖ ≤ Λ ^ 2 := by
  have FA := fun b => (GenFib.nonempty_of_baseChange hL.polBaseChange K (X.A b).pol).some
  obtain ⟨FB⟩ := GenFib.nonempty_of_baseChange hL.polBaseChange K X.B.pol
  choose hA hA' using fun b => (LieMetric.exists_unique_isHerm hU hL K _ (FA b)).1
  obtain ⟨hB, hB'⟩ := (LieMetric.exists_unique_isHerm hU hL K _ FB).1
  choose M hM using fun j : Fin p ⊕ Fin q =>
    @exists_isDiffOf K _ _ _ (FA j.isLeft) FB (X.φ j) (X.lin j).isMonHom
  obtain ⟨Λ, h₁, h₂⟩ := exists_bound X.hh
  refine ⟨FA, FB, hA, hB, M, Λ, fun b => ⟨(FA b).fib.1 ▸ ?_, hA' b⟩, hB', hM, h₁, h₂⟩
  cases b
  · exact dim_pos_of_hasType X.split (by rw [neg_sq, X.ρ_sq]) _ (Test.hasType_neg X.ρ_sq X.typeM)
  · exact dim_pos_of_hasType X.split X.ρ_sq _ X.typeP

end GlobalTheory.CM.NumInh
end
end

-- bundled from Development.AbelianVarietyTheory.Statements.PrincipalLattices.PhiNeOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.CM.ExStModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def zeroDatum (H : Host E) : Datum H where
  La := PUnit
  fin := inferInstance
  proj := inferInstance
  EF := 0
  alt _ := rfl
  unimod := ⟨fun _ _ _ => rfl, fun f => ⟨0, by ext x; rw [Subsingleton.elim x 0, map_zero, map_zero]⟩⟩
  adj _ _ _ := rfl
  p := 0
  q := 0
  rank := Module.finrank_zero_of_subsingleton
  dom := by
    have hs : Subsingleton (ℝ ⊗[ℤ] PUnit.{1}) := inferInstance
    refine ⟨0, fun x => Subsingleton.elim _ _, fun x y => by simp, fun x hx => absurd (Subsingleton.elim _ _) hx, ?_⟩
    intro a A t _ ht
    rw [Subsingleton.elim A 0, ht]
    simp

theorem unit_comp {S S' T : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (s : T ⟶ S')
    (s₀ : T ⟶ S) (h : s ≫ f = s₀) :
    (1 : Over.mk s ⟶ t'.G).left ≫ m.φ = (1 : Over.mk s₀ ⟶ t.G).left := by
  subst h
  have e1 : (1 : Over.mk s ⟶ t'.G).left = s ≫ eSec t'.G := by
    rw [Hom.one_def]; simp [eSec]
  have e2 : (1 : Over.mk (s ≫ f) ⟶ t.G).left = (s ≫ f) ≫ eSec t.G := by
    rw [Hom.one_def]; simp [eSec]
  have e3 := m.cm.e_comm
  rw [m.base] at e3
  rw [e1, e2]
  simp only [Category.assoc]
  exact congrArg (s ≫ ·) e3

theorem hh_real {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} {hP : IsPeriod D ty Pe}
    {p q : ℕ} (Z : CMLat hP p q) (j : Fin p ⊕ Fin q) (a : (Z.D₁ j.isLeft).La) : H.bar (Z.hh j) • a = Z.hh j • a := by
  have skew : ∀ (D : Datum H) (x y : D.La), D.EF x y = -D.EF y x := fun D x y => by
    have := D.alt (x + y)
    simp only [map_add, LinearMap.add_apply, D.alt] at this
    linarith
  apply (Z.D₁ j.isLeft).unimod.1
  ext b
  rw [skew, ← Datum.adj, ← Z.form, ← Z.form, ← skew]

theorem phi_ne_one (hS : CMExistsSt) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n)
    (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (Z : CMLat hP D.p D.q) :
    ∃ (K₁ : IntermediateField ℚ ℂ) (_ : NumberField K₁) (ρ : 𝓞 K₁) (X : CMObj H K₁ ρ (algebraMap K₁ ℂ) D.p D.q),
      X.hh = Z.hh ∧ ∀ j, Z.f j ≠ 0 → X.φ j ≠ 1 := by
  obtain ⟨K₁, hK, hk, ρ, X, y, t₀, m, m', gA, tyA, PA, e, F, -, -, hh, -, hy, -, hF, hx⟩ :=
    hS E H D l Xo g ty FU i Pe hP Z ⊥ inferInstance
  refine ⟨K₁, hK, ρ, X, hh, fun j hj h1 => hj ?_⟩
  have hmem : ∀ z, F j z ∈ Pe.range := fun z => by
    rw [← FU.ex_ker i Pe hP]
    have hc : spMap (algebraMap K₁ ℂ) ≫ spMap (algebraMap (𝓞 K₁) K₁) =
        spMap ((algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁)) := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]; rfl
    have := hx j z (1 : Over.mk (spMap (algebraMap K₁ ℂ)) ⟶ t₀.G).left (Over.w _) (by
      rw [unit_comp m' _ _ hc, h1]; simp)
    rw [unit_comp m _ _ hy] at this
    exact Over.OverMorphism.ext this.symm
  have hz : ∀ z, F j z = 0 := fun z => by
    haveI := hP.2.2.1
    have hcont : Continuous fun c : ℂ => (⟨F j (c • z), hmem _⟩ : Pe.range) := by
      refine Continuous.subtype_mk ?_ _
      simp only [map_smul]
      fun_prop
    have := PreconnectedSpace.constant inferInstance hcont (x := 1) (y := 0)
    simpa using this
  ext a
  apply hP.2.1
  rw [← hF, hz]; simp

theorem kForm_diag {D : Datum H} {ε : ℤˣ} {h : D.La → D.La → OK H} (hh : IsKForm D ε h) (x : D.La) :
    ((h x x : OK H) : 𝓞 E) = (((ε : ℤ) * D.EF (H.w0 • x) x : ℤ) : 𝓞 E) := by
  rw [hh, D.alt]; simp

end GlobalTheory.CM.ExStModel
end
end

