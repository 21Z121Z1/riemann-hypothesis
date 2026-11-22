import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0152
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0016
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingOfPolarisationFormLinComb

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFieldExtensionBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.relAmple_of_fieldExtension_baseChange : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A₀] [GrpObj A] (φ : A.left ⟶ A₀.left) (L₀ : LB A₀.left) (L : LB A.left), IsAbelianScheme A₀ → IsGrpPullback A A₀ (spMap i) φ → L₀.IsLB → L.IsLB → LBIso L (L₀.pull φ) → Out.RelAmple A L → Out.RelAmple A₀ L₀ := by
  first | exact @GlobalTheory.AmpleDescent.relAmple_of_fieldExtension | exact GlobalTheory.AmpleDescent.relAmple_of_fieldExtension | (intros; apply GlobalTheory.AmpleDescent.relAmple_of_fieldExtension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ShapeOfUniformisedThetaObjectStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shape_of_uniformised_theta_object : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (t : TObj g k J b (spMap em)) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ), (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → (∀ j i, ∃ y, ac j (lam i) = ∑ i', Mat j i' i • lam i' + k • y) → (∀ j, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j x)) ∧ ∀ y, y ≠ 0 → (hermForm Hm (F y) (F y)).re < κ * (hermForm Hm y y).re) → t.Shape Mat κ := by
  first | exact @GlobalTheory.ZM.shape_of_uniformised | exact GlobalTheory.ZM.shape_of_uniformised | (intros; apply GlobalTheory.ZM.shape_of_uniformised <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelDataPullbackOfLevelMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.SiegelDataPull

open GlobalTheory.SiegelPullComp

theorem isSquare_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {ψ : G''.left ⟶ G'.left} {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : Geo.Tor.IsSquare ψ ψ₂) (h : Geo.Tor.IsSquare φ φ₂) : Geo.Tor.IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc]
  · rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]

theorem siegData_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (O : Type) [CommRing O] (T T' : Scheme.{0}) (sT : T ⟶ Sp O) (f : T' ⟶ T) (t : SAB H T) (t' : SAB H T') (ν : SABMap t' t f) (lev : D.La → (𝟙_ (Over T) ⟶ t.G)) (lev' : D.La → (𝟙_ (Over T') ⟶ t'.G)) (g p N : ℕ) (Ag : SiegelFamily g p N) (z : ZP p N →+* O) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (w : T ⟶ pullback Ag.s (spMap z)), (∀ x, (lev' x).left ≫ ν.φ = f ≫ (lev x).left) → SiegData sT t lev Ag z bas w → SiegData (f ≫ sT) t' lev' Ag z bas (f ≫ w) := by
  intro E _ _ _ H D O _ T T' sT f t t' ν lev lev' g p N Ag z bas w hlev hw
  obtain ⟨o, φ, φ₂, hpb, hsq, hiso, hlv, hsnd, hSPB⟩ := hw
  obtain ⟨⟨o', ho'⟩, -⟩ := GlobalTheory.siegPre_pullback _ _ _ _ _ _ _ ((f ≫ sT) ≫ spMap z) f o
    (Category.assoc f sT (spMap z)).symm
  have hpbo := ho'
  obtain ⟨φ₁, φ₁₂, hpb₁, hsq₁, hiso₁, hlv₁⟩ := hpbo
  have hν : IsGrpPullback t'.G t.G f ν.φ := ν.cart
  have hc : IsGrpPullback o'.A t.G f (φ₁ ≫ φ) := (hpb₁.comp hpb).congr (Category.comp_id f) rfl
  obtain ⟨e, he, hel⟩ := grpPullback_iso hc hν
  haveI := he
  have hpb' : IsGrpPullback o'.A t'.G (𝟙 T') e.hom.left := isGrpPullback_of_iso e
  have hsq' := GlobalTheory.LamPull.exists_isSquare hpb'.1.w
  have hν₂ := GlobalTheory.LamPull.exists_isSquare hν.1.w
  have hΛ : (abelian₂ t.G t.PP.L).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ t.PP.isLB _ _
  have hΛ' : (abelian₂ t'.G t'.PP.L).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ t'.PP.isLB _ _
  have sA := isSquare_comp hsq₁ hsq
  have sB := isSquare_comp hsq' hν₂
  rw [hel] at sB
  have key := GlobalTheory.LamPull.isSquare_unique sA sB
  refine ⟨o', e.hom.left, _, hpb', hsq', ?_, ?_, ?_, ?_⟩
  · have h2 := GlobalTheory.SiegelPullComp.iso_pull φ₁₂ hiso
    have h3 := GlobalTheory.SiegelPullComp.iso_pull_pull hΛ φ₂ φ₁₂
    rw [key] at h3
    have h4 := (GlobalTheory.SiegelPullComp.iso_pull_pull hΛ (lift (pushPt hν.1.w (fst t'.G t'.G))
      (pushPt hν.1.w (snd t'.G t'.G))).left (lift (pushPt hpb'.1.w (fst o'.A o'.A))
      (pushPt hpb'.1.w (snd o'.A o'.A))).left).symm
    have h5 := GlobalTheory.SiegelPullComp.iso_pull (lift (pushPt hpb'.1.w (fst o'.A o'.A))
      (pushPt hpb'.1.w (snd o'.A o'.A))).left ((GlobalTheory.LamPull.lam_pull E H T T' t t' f).2 ν _ hν₂).symm
    have l0 := o'.isLB
    have l1 := pull_isLB o.isLB φ₁₂
    have l2 := pull_isLB (pull_isLB hΛ φ₂) φ₁₂
    refine LBIso.trans l0 l1 (pull_isLB hΛ' _) hiso₁ ?_
    refine LBIso.trans l1 l2 (pull_isLB hΛ' _) h2 ?_
    refine LBIso.trans l2 (pull_isLB hΛ _) (pull_isLB hΛ' _) h3 ?_
    refine LBIso.trans (pull_isLB hΛ _) (pull_isLB (pull_isLB hΛ _) _) (pull_isLB hΛ' _) h4 h5
  · intro u
    apply hν.1.hom_ext
    · rw [Category.assoc, hel, ← Category.assoc, hlv₁ u, Category.assoc, hlv u, hlev]
    · rw [Category.assoc, Over.w e.hom, Over.w (o'.lev u), Over.w (lev' (bas u))]
  · rw [Category.assoc, hsnd]
  · rw [Category.assoc f w (pullback.fst Ag.s (spMap z))]
    exact GlobalTheory.SiegelPullComp.pb_comp hSPB ho'

end GlobalTheory.SiegelDataPull

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelPre_pullback_principal_ringChange : ∀ (h k : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j ζ = ζ' → f ≫ s = s' ≫ spMap j → (∀ c : SiegPre h k ζ s, ∃ c' : SiegPre h k ζ' s', SiegPB c' c f) ∧ (∀ (c : SiegPre h k ζ s) (c' : SiegPre h k ζ' s'), SiegPB c' c f → c.Principal → c'.Principal) ∧ ∀ c' : SiegPre h k ζ' s', ∃ c₀ : SiegPre h k ζ (s' ≫ spMap j), SiegPB c' c₀ (𝟙 _) ∧ SiegPB c₀ c' (𝟙 _) := by
  first | exact @GlobalTheory.SiegelRingChange.siegPre_pull_ringChange | exact GlobalTheory.SiegelRingChange.siegPre_pull_ringChange | (intros; apply GlobalTheory.SiegelRingChange.siegPre_pull_ringChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaClosureComponentTrdegGe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM

namespace GlobalTheory.ZM.GenericTrdeg

theorem exists_hom_of_ker_eq {R K K' : Type} [CommRing R] [Field K] [Field K'] (φ : R →+* K) (θ : R →+* K')
    (hk : RingHom.ker θ = RingHom.ker φ) (hs : ∀ z : K, ∃ a b, z = φ a / φ b) :
    ∃ j : K →+* K', j.comp φ = θ := by
  letI : Algebra (R ⧸ RingHom.ker φ) K := (RingHom.kerLift φ).toAlgebra
  haveI : FaithfulSMul (R ⧸ RingHom.ker φ) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective φ)
  haveI : IsFractionRing (R ⧸ RingHom.ker φ) K := by
    refine IsFractionRing.of_field _ _ fun z => ?_
    obtain ⟨a, b, h⟩ := hs z
    exact ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b, h⟩
  let g : (R ⧸ RingHom.ker φ) →+* K' := Ideal.Quotient.lift _ θ (fun a ha => by rw [← hk] at ha; exact ha)
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hk]
    exact ha
  refine ⟨IsFractionRing.lift hg, ?_⟩
  ext a
  exact IsFractionRing.lift_algebraMap (K := K) hg (Ideal.Quotient.mk _ a)

theorem exists_local_domain {A K : Type} [CommRing A] [Field K] (e : A →+* K) (P : Ideal A) [P.IsPrime]
    (hP : P ≤ RingHom.ker e) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (ρ : A →+* R') (ψ : R' →+* K),
      RingHom.ker ρ = P ∧ ψ.comp ρ = e ∧ ∀ r, ψ r ≠ 0 → IsUnit r := by
  let e' : A ⧸ P →+* K := Ideal.Quotient.lift P e (fun a ha => hP ha)
  haveI : (RingHom.ker e').IsPrime := RingHom.ker_isPrime e'
  let R' := Localization.AtPrime (RingHom.ker e')
  have hu : ∀ y : (RingHom.ker e').primeCompl, IsUnit (e' y) := fun y =>
    isUnit_iff_ne_zero.2 y.2
  have hinj : Function.Injective (algebraMap (A ⧸ P) R') :=
    IsLocalization.injective R' (RingHom.ker e').primeCompl_le_nonZeroDivisors
  refine ⟨R', inferInstance, inferInstance, (algebraMap (A ⧸ P) R').comp (Ideal.Quotient.mk P),
    IsLocalization.lift hu, ?_, ?_, ?_⟩
  · ext a
    rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]
  · ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalization.lift_eq]
    rfl
  · intro r hr
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker e').primeCompl r
    rw [IsLocalization.AtPrime.isUnit_mk'_iff R' (RingHom.ker e')]
    intro ha
    apply hr
    rw [IsLocalization.lift_mk']
    rw [show e' a = 0 from ha, zero_mul]

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap f' ≫ spMap f = spMap (f'.comp f) := by
  unfold spMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_inj {R R' : Type} [CommRing R] [CommRing R'] {f f' : R →+* R'} (h : spMap f = spMap f') : f = f' := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

theorem exists_factor {X : Scheme.{0}} {R R' K : Type} [CommRing R] [CommRing R'] [Field K] (x : Sp R ⟶ X)
    [IsOpenImmersion x] (x' : Sp R' ⟶ X) (φ : R →+* K) (ψ : R' →+* K) (hψ : ∀ r, ψ r ≠ 0 → IsUnit r)
    (h : spMap ψ ≫ x' = spMap φ ≫ x) : ∃ χ : R →+* R', spMap χ ≫ x = x' ∧ ψ.comp χ = φ := by
  have hr : Set.range x' ⊆ Set.range x := by
    rintro _ ⟨q, rfl⟩
    let pt : Sp K := (⊥ : PrimeSpectrum K)
    have hsp : q ⤳ spMap ψ pt := by
      refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
      intro r hr
      change ψ r ∈ (⊥ : Ideal K)
      by_contra hne
      exact q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hr (hψ r hne))
    have hmem : x' (spMap ψ pt) ∈ Set.range x := by
      rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    exact (hsp.map x'.continuous).mem_open x.isOpenEmbedding.isOpen_range hmem
  have hχ : spMap (Spec.preimage (IsOpenImmersion.lift x x' hr)).hom ≫ x = x' := by
    unfold spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]
  refine ⟨_, hχ, spMap_inj ?_⟩
  rw [← cancel_mono x, ← spMap_comp, Category.assoc, hχ, h]

theorem exists_algebraicIndependent : Out.Laws → Out.Laws2 → ∀ (n : ℕ), ∀ (g N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ) (F : ThetaFam n em C), ArBase em → GoodClass em C Mat κ w w' d → ∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ F.MM), IsOpenImmersion x → x ≫ F.s = spMap (algebraMap o R) → ∀ (K : Type) [Field K] [Algebra o K] (φ : R →ₐ[o] K), RingHom.ker φ ∈ minimalPrimes R → (∀ z : K, ∃ a b, z = φ a / φ b) → ∃ y : Fin d → K, AlgebraicIndependent o y := by
  intro hL hL2 n g N' J Mat κ w w' o _ b em C d F hA hG R _ _ x hx hxs K _ _ φ hmin hsurj
  have hη : (spMap φ.toRingHom ≫ x) ≫ F.s = spMap (algebraMap o K) := by
    rw [Category.assoc, hxs, spMap_comp]
    congr 1
    exact φ.comp_algebraMap
  obtain ⟨v, hv, hvI⟩ := F.loc K (algebraMap o K) _ hη
  let e : MvPolynomial (Ix g (N' ^ 2)) o →+* K := MvPolynomial.eval₂Hom (algebraMap o K) v
  have hN : N' ≠ 0 := by
    rintro rfl
    have := b.unit.map (algebraMap o K)
    simp at this
  obtain ⟨c₁, hc₁⟩ := hvI.2 ⊥ Ideal.isPrime_bot 0
  set a₁ := 0 + (N' / n) • c₁ with ha₁
  have hva₁ : v a₁ ≠ 0 := hc₁
  obtain ⟨P, a₀, a, hP, hIP, hPp, -, hind⟩ := GlobalTheory.ThetaPrime.exists_prime_independent_ratios hL hL2 g N' J Mat κ w w' o b em C d hA hG
    (RingHom.ker e) a₁ hN (RingHom.ker_isPrime e) (fun G hG => hvI.1 G hG)
    (by simpa [e, RingHom.mem_ker] using hva₁)
  obtain ⟨R', _, _, ρ, ψ, hρ, hψρ, hψ⟩ := exists_local_domain e P hPp
  let β' : o →+* R' := ρ.comp MvPolynomial.C
  let v' : Ix g (N' ^ 2) → R' := fun i => ρ (MvPolynomial.X i)
  have hev : MvPolynomial.eval₂Hom β' v' = ρ := by
    apply MvPolynomial.ringHom_ext <;> intro i <;> simp [β', v']
  have hψv : (fun i => ψ (v' i)) = v := by
    funext i
    have := RingHom.congr_fun hψρ (MvPolynomial.X i)
    simpa [e] using this
  have hψβ : ψ.comp β' = algebraMap o K := by
    ext i
    have := RingHom.congr_fun hψρ (MvPolynomial.C i)
    simpa [e, β'] using this
  have hI' : InMM n N' (thIdeal em C) β' v' := by
    refine ⟨fun G hG => ?_, fun q hq i => ?_⟩
    · have : ρ G = 0 := by rw [← RingHom.mem_ker, hρ]; exact hIP hG
      rw [← hev] at this
      exact this
    · obtain ⟨c, hc⟩ := hvI.2 ⊥ Ideal.isPrime_bot i
      refine ⟨c, fun hm => hq.ne_top (Ideal.eq_top_of_isUnit_mem _ hm (hψ _ ?_))⟩
      rw [congrFun hψv]
      exact hc
  obtain ⟨x', ⟨hx's, hx'v⟩, -⟩ := F.pts R' β' v' hI'
  have hcl : spMap ψ ≫ x' = spMap φ.toRingHom ≫ x := by
    refine (F.pts K (algebraMap o K) v hvI).unique ⟨?_, ?_⟩ ⟨hη, hv⟩
    · rw [Category.assoc, hx's, spMap_comp, hψβ]
    · have := GlobalTheory.hasTh_baseChange hL2 o g N' J b _ _ F.univ R' K ψ x' v' hx'v
      rwa [hψv] at this
  obtain ⟨χ, hχx, hψχ⟩ := exists_factor x x' φ.toRingHom ψ hψ hcl
  let K' := FractionRing R'
  let lam : R' →+* K' := algebraMap R' K'
  have hlam : Function.Injective lam := IsFractionRing.injective R' K'
  have hker : RingHom.ker (lam.comp χ) = RingHom.ker φ.toRingHom := by
    have hle : RingHom.ker (lam.comp χ) ≤ RingHom.ker φ.toRingHom := by
      intro r hr
      rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _ hlam] at hr
      rw [RingHom.mem_ker, ← hψχ, RingHom.comp_apply, hr, map_zero]
    exact le_antisymm hle (hmin.2 ⟨RingHom.ker_isPrime _, bot_le⟩ hle)
  obtain ⟨j, hj⟩ := exists_hom_of_ker_eq φ.toRingHom (lam.comp χ) hker hsurj
  have hpt : spMap j ≫ spMap φ.toRingHom ≫ x = spMap lam ≫ x' := by
    rw [← Category.assoc, spMap_comp, hj, ← spMap_comp, Category.assoc, hχx]
  have h1 := GlobalTheory.hasTh_baseChange hL2 o g N' J b _ _ F.univ K K' j _ v hv
  have h2 := GlobalTheory.hasTh_baseChange hL2 o g N' J b _ _ F.univ R' K' lam _ v' hx'v
  rw [hpt] at h1
  obtain ⟨u, hu⟩ := GlobalTheory.hasTh_unique_unit hL hL2 o g N' J b _ _ F.univ K' _ _ _ h1 h2
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨a₁, rfl⟩)
      (isUnit_iff_ne_zero.2 ((map_ne_zero j).2 hva₁)))
  have hjβ : j.comp (algebraMap o K) = lam.comp β' := by
    apply spMap_inj
    rw [← spMap_comp, ← hη, ← Category.assoc, hpt, Category.assoc, hx's, spMap_comp]
  have hkP : RingHom.ker (MvPolynomial.eval₂Hom (lam.comp β') (fun i => lam (v' i))) = P := by
    rw [← MvPolynomial.comp_eval₂Hom, hev, ← hρ]
    ext G
    rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _ hlam, RingHom.mem_ker]
  refine ⟨fun i => v (a i) / v a₀, algebraicIndependent_iff.2 fun G hG => hind K' _ _ hkP G ?_⟩
  have h3 := congrArg j hG
  rw [MvPolynomial.aeval_def, MvPolynomial.hom_eval₂, hjβ, map_zero] at h3
  rw [← h3]
  congr 1
  funext i
  rw [hu, hu, mul_div_mul_left _ _ u.ne_zero, map_div₀]

end GlobalTheory.ZM.GenericTrdeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealPrimeAvoidingVariableStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_ideal_prime_avoiding_variable : Out.Laws → Out.Laws2 → ∀ (g N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (p : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (a₁ : Ix g (N' ^ 2)), N' ≠ 0 → p.IsPrime → thIdeal em C ≤ p → MvPolynomial.X a₁ ∉ p → ∃ (P : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (a₀ : Ix g (N' ^ 2)) (a : Fin d → Ix g (N' ^ 2)), P.IsPrime ∧ thIdeal em C ≤ P ∧ P ≤ p ∧ MvPolynomial.X a₀ ∉ P ∧ ∀ (K : Type) [Field K] (β : o →+* K) (v : Ix g (N' ^ 2) → K), RingHom.ker (MvPolynomial.eval₂Hom β v) = P → ∀ G : MvPolynomial (Fin d) o, MvPolynomial.eval₂ β (fun i => v (a i) / v a₀) G = 0 → G = 0 := by
  first | exact @GlobalTheory.ThetaPrime.exists_prime_independent_ratios | exact GlobalTheory.ThetaPrime.exists_prime_independent_ratios | (intros; apply GlobalTheory.ThetaPrime.exists_prime_independent_ratios <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaObjectConstantFamilyDualNumbersIsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS

namespace GlobalTheory.KS
private theorem k_ne_zero_lemma {o : Type} [CommRing o] {k : ℕ} (b : TBase o k) (s₀ : Sp ℂ ⟶ Sp o) :
    k ≠ 0 := by
  rintro rfl
  have h0 : (0 : o) = 1 := isUnit_zero_iff.mp (by simpa using b.unit)
  haveI : Subsingleton o := subsingleton_of_zero_eq_one h0
  obtain ⟨x⟩ := (inferInstance : Nonempty (PrimeSpectrum ℂ))
  exact (s₀.base x).isPrime.ne_top (Subsingleton.elim _ _)

theorem tMap_of_isConst : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (s₀ : Sp ℂ ⟶ Sp o) (s' : Sp (DualNumber ℂ) ⟶ Sp o) (t₀ : TObj g k J b s₀) (t' : TObj g k J b s') (ρ : t'.A.left ⟶ t₀.A.left) (j : t₀.A.left ⟶ t'.A.left), IsConst t'.A t₀.A ρ j → (IsGrpPullback t₀.A t'.A (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j ∧ LBIso t₀.L (t'.L.pull j) ∧ (∀ i, (t₀.pt i).left ≫ j = (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ (t'.pt i).left) ∧ ∀ jj, (t₀.act jj).left ≫ j = j ≫ (t'.act jj).left) → TMap t' t₀ (spMap (algebraMap ℂ (DualNumber ℂ))) := by
  intro hL hL2 hT o _ g k J b s₀ s' t₀ t' ρ j hc ⟨hpb, hlb, hpt, hact⟩
  have hk : k ≠ 0 := k_ne_zero_lemma b s₀
  refine ⟨ρ, hc.1, ?_, ?_, ?_⟩
  · obtain ⟨u, Hm, χ, hu, -⟩ := GlobalTheory.KSInh.exists_goodU_ksRel hT t₀.pol
    exact GlobalTheory.SymRigid.lbIso_pull_of_isConst hL t₀.pol u Hm χ hu t'.A ρ j hc t'.L t'.isLB t'.sym hlb
  · intro i
    exact GlobalTheory.T.torsionSection_constantFamily_dualNumbers hL t₀.pol t'.A ρ j hc k (t'.pt i) (t₀.pt i) hk (t'.torsion i) (t₀.torsion i) (hpt i).symm
  · intro jj
    exact GlobalTheory.T.endo_constant_family_dualNumbers_eq_baseChange hL hL2 t₀.pol t'.A ρ j hc (t'.act jj) (t₀.act jj) t'.ab (t'.hom jj) (t₀.hom jj) (hact jj).symm
end GlobalTheory.KS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaSectionsVeryAmplePeriodic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

noncomputable section
namespace GlobalTheory.EmbVA

theorem act_unique (hL : Out.SymLiftSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) (k : ℕ) (z : ℤ)
    (hz : z = k) (ho : Odd k) (hu : IsUnit (k : Γ(S, ⊤))) {T : Over S} (x : T ⟶ P.A) (hx : x ^ k = 1)
    {θ θ' : Out.ThetaGrp P.A P.L z T} (h : Out.SymLift P.A P.L z k x θ) (h' : Out.SymLift P.A P.L z k x θ')
    {s s₁ s₂ : LB.Sec (Out.LPow P.A P.L z T)} (a₁ : Out.IsActOf P.A P.L z θ s s₁)
    (a₂ : Out.IsActOf P.A P.L z θ' s s₂) (j) : s₁.f j = s₂.f j := by
  subst hz
  have hc := (hL S P k ho hu T x hx).2 θ θ' h h'
  refine sec_ext_val P.isLB (s := s₁) (s' := s₂) (fun y J hJ => ?_) j
  have e₁ := GlobalTheory.ThetaPowOrder.act_sval a₁ (𝟙 _) y hJ
  have e₂ := GlobalTheory.ThetaPowOrder.act_sval a₂ (𝟙 _) y hJ
  have e₃ := val_corr hJ hc (𝟙 _)
  have e₄ : θ.pt = θ'.pt := h.pt_eq.trans h'.pt_eq.symm
  refine e₁.trans (Eq.trans ?_ e₂.symm)
  exact congrArg₂ (fun u (p : T ⟶ P.A) => Units.val u * sval (L := P.L) s (𝟙 _ ≫ (Out.translT P.A p).left) y J) e₃ e₄

theorem lbIso_pow {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (n : ℕ) (z : ℤ) (hz : z = n) :
    LBIso (LB.LinComb L (K := Fin 1) (fun _ => f) (fun _ => z)) ((lbPow L n).pull f) := by
  subst hz
  refine LBIso.chartPull (h := f) (A := lbPow L n) (B := lbPow L n) ?_ (chartPullPull _ f f rfl)
    ⟨_, idIso_isGen (LB.isLB_linComb hL _ _)⟩
  have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => f) j ≤
      f ⁻¹ᵁ LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => j 0) :=
    fun j y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0
  refine ⟨fun j _ => j 0, le, fun y j j' hj hj' => ?_⟩
  refine (gm_linComb L _ _ (𝟙 Y) y j j' hj hj').trans (Eq.trans ?_
    (gm_linComb L (fun _ : PUnit => 𝟙 X) (fun _ => (n : ℤ)) f y _ _ (le j hj) (le j' hj')).symm)
  rw [Fin.prod_univ_one, Fintype.prod_unique, Category.id_comp, Category.comp_id]

theorem linComb_pow {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {r : ℕ} (y : Fin r → (T ⟶ A))
    (a : Fin r → ℕ) (n : ℕ) : Out.linComb y a ^ n = ∏ i, y i ^ (a i * n) := by
  rw [Out.linComb, List.prod_ofFn, ← Finset.prod_pow]
  simp only [pow_mul]

end GlobalTheory.EmbVA

namespace GlobalTheory

open EmbVA in

theorem embSec_veryAmple_periodic : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g (N' ^ 2) J b (spMap β)) (m : ℕ) σ, Odd N' → m ∣ N' → 2 ≤ m → t.Emb m (Over.mk (𝟙 (Sp K))) σ → IsIso (snd (Over.mk (𝟙 (Sp K))) t.A).left ∧ (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 (Sp K)))).IsLB ∧ VAmp (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ ∧ LBIso (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 (Sp K)))) ((lbPow t.L (m ^ 2)).pull (snd (Over.mk (𝟙 (Sp K))) t.A).left) ∧ (∀ a a' : Ix g (N' ^ 2), (∀ i, (a i).val ≡ (a' i).val [MOD m ^ 2]) → ∀ j, (σ a).f j = (σ a').f j) ∧ TorsBasis t.A (N' ^ 2) t.pt ∧ ∀ x : Out.baseOver (Sp K) ⟶ t.A, x ^ N' = 1 → ∃ h, t.lab h ^ N' = x := by
  intro hL hL2 o _ g N' J b K _ _ β t m σ hN hm h2 hE
  haveI := t.ab.comm
  have hN0 : N' ≠ 0 := by rintro rfl; simp at hN
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero _ hN0⟩
  have hid : (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) = 𝟙 _ := rfl
  have hbij : ∀ y : Out.baseOver (Sp K) ⟶ t.A, y ^ (N' ^ 2) = 1 →
      ∃! c : Fin (2 * g) → ZMod (N' ^ 2), Out.linComb t.pt (fun i => (c i).val) = y := fun y hy => by
    have := t.bij K (𝟙 _) y hy
    simpa only [hid, Category.id_comp] using this
  refine ⟨?_, LB.isLB_linComb t.isLB _ _, ?_, lbIso_pow t.isLB _ _ _ (by push_cast; rfl), ?_, ⟨Nat.pos_of_neZero _, t.torsion, hbij⟩, ?_⟩
  · show IsIso (pullback.snd (𝟙 (Sp K)) t.A.hom)
    infer_instance
  · refine GlobalTheory.T.isVeryAmpleSectionSystem_of_projectiveCoordinates K _ _ _ _ _ _ (GlobalTheory.T.projCoordRepresentation_geometric_fibre_spanning hL hL2 _ t.pol K (𝟙 _) _ _ σ (by nlinarith) ?_)
    exact GlobalTheory.EmbSpan.emb_span_eq_top hL hL2 o g N' J b _ _ t m K (𝟙 _) σ hN hm h2 hE
  · intro a a' haa j
    obtain ⟨th, s1, α, U, -, -, -, hU, hact⟩ := hE
    obtain ⟨c, rfl⟩ := hm
    have hm0 : 0 < m := by omega
    have hc : m * c / m = c := Nat.mul_div_cancel_left c hm0
    have hlab : t.lab a ^ (c ^ 2) = t.lab a' ^ (c ^ 2) := by
      rw [TObj.lab, TObj.lab, linComb_pow, linComb_pow]
      refine Finset.prod_congr rfl fun i _ => ?_
      refine pow_eq_pow_of_modEq ?_ (t.torsion i)
      exact ((haa i).mul_right' _).of_dvd (dvd_of_eq (mul_pow m c 2))
    have htor : (t.lab a ^ (c ^ 2)) ^ (m ^ 2) = 1 := by
      rw [← pow_mul, TObj.lab, linComb_pow]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [show (a i).val * (c ^ 2 * m ^ 2) = (m * c) ^ 2 * (a i).val by ring, pow_mul, t.torsion, one_pow]
    have hu : IsUnit ((m ^ 2 : ℕ) : Γ(Sp K, ⊤)) := by
      have h1 := (b.unit.map β).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      rw [map_natCast, map_natCast, mul_pow, Nat.cast_mul] at h1
      exact isUnit_of_mul_isUnit_left h1
    have h₁ := hU a
    have h₂ := hU a'
    simp only [Over.mk_hom, hid, Category.id_comp, hc] at h₁ h₂
    rw [← hlab] at h₂
    exact act_unique hL.symLift t.pol (m ^ 2) _ (by push_cast; rfl) (Odd.of_dvd_nat hN (Dvd.intro c rfl)).pow hu _ htor
      h₁ h₂ (hact a) (hact a') j
  · intro x hx
    obtain ⟨h1, -, h3, -⟩ := hL.mulN _ t.pol N' (Nat.pos_of_ne_zero hN0)
    obtain ⟨d, hd⟩ := TwistTranslate.exists_root t.pol (𝟙 (Sp K)) N' x
    have hd' : (show Out.baseOver (Sp K) ⟶ t.A from d) ^ N' = x := hd
    obtain ⟨h, hh, -⟩ := hbij d ((congrArg (fun n => (show Out.baseOver (Sp K) ⟶ t.A from d) ^ n) (pow_two N')).trans (by rw [pow_mul, hd', hx]))
    exact ⟨h, (congrArg (· ^ N') hh).trans hd'⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuativeLiftGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ValuativeGeneric

theorem isProper_of_lift_generic_of_finiteType : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (X Y : Scheme.{0}) (f : X ⟶ Y) (sY : Y ⟶ Sp O), IsQProjOver (f ≫ sY) → IsSeparated sY → LocallyOfFiniteType sY → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (x : Sp K ⟶ X) (y : Sp V ⟶ Y), Set.range x ⊆ genericPoints X → x ≫ f = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) → IsProper f := by
  intro O _ _ X Y f sY hq hs hl h
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  exact isProper_of_lift_generic O X Y f sY hs hq
    fun V K _ _ _ _ _ _ _ x y hx hy => h V K x y hx hy

end GlobalTheory.ValuativeGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingOfPolarisationFormLinCombStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_of_polarisationForm_linComb : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (I : Type) [Fintype I] (φ : I → (P.A ⟶ P.A)) (ε : I → ℤ) (s : P.A ⟶ P.A) (k : ℕ) (x y : Out.baseOver (Sp K) ⟶ P.A) (c : I → Kˣ), (k : K) ≠ 0 → (∀ i, IsMonHom (φ i)) → FormIs P (LB.LinComb P.L (fun i => (φ i).left) ε) s → x ^ k = 1 → y ^ k = 1 → (∀ i, Out.WeilIs P.A P.L k (x ≫ φ i) (y ≫ φ i) (unitOn (c i))) → Out.WeilIs P.A P.L k x (y ≫ s) (unitOn (∏ i, c i ^ ε i)) := by
  first | exact @GlobalTheory.weilIs_of_formIs_linComb | exact GlobalTheory.weilIs_of_formIs_linComb | (intros; apply GlobalTheory.weilIs_of_formIs_linComb <;> assumption)
end

