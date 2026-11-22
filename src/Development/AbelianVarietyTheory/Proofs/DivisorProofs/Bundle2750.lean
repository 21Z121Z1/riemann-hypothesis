import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2649
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0700
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0386
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2517
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2634
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatMulIntegralMemCmLatticePrimeToStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nat_mul_integral_mem_cmLattice_prime_to : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (c : Ideal (OF E)) (y : (Af E)ˣ) (R : ℕ), l.Prime → OneOver l y → 0 < R → (R : OF E) ∈ c → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ x : E, IsIntegral ℤ x → ((M * R : ℕ) : E) * x ∈ lattice c y := by
  first | exact @GlobalTheory.HilbFam.LatDen.nat_mul_integral_mem_lattice | exact GlobalTheory.HilbFam.LatDen.nat_mul_integral_mem_lattice | (intros; apply GlobalTheory.HilbFam.LatDen.nat_mul_integral_mem_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearOpenEmbeddingCompOfSumMapComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DescFix

set_option backward.isDefEq.respectTransparency false

theorem smooth_of_comp_mono {W X G : Scheme.{0}} (m : W ⟶ X) (e : X ⟶ G) [Mono e] [hs : Smooth (m ≫ e)] : Smooth m := by
  have : IsPullback (𝟙 W) m (m ≫ e) e := IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  exact MorphismProperty.of_isPullback (P := @Smooth) this hs

theorem smooth_mul {T : Scheme.{0}} (G : Over T) [GrpObj G] [Smooth G.hom] : Smooth (μ[G]).left := by
  let σ : G ⊗ G ≅ G ⊗ G :=
    { hom := lift (fst G G * snd G G) (snd G G)
      inv := lift (fst G G * (snd G G)⁻¹) (snd G G)
      hom_inv_id := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.comp_mul, GrpObj.comp_inv]
      inv_hom_id := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.comp_mul, GrpObj.comp_inv] }
  have h : μ[G] = σ.hom ≫ fst G G := by
    simp [σ, Hom.mul_def]
  have h₁ : Smooth (fst G G).left := inferInstanceAs (Smooth (pullback.fst G.hom G.hom))
  have h₂ : IsIso σ.hom.left := inferInstanceAs (IsIso ((Over.forget T).mapIso σ).hom)
  rw [h, Over.comp_left]
  infer_instance

theorem isPreirreducible_fibre {X T : Scheme.{0}} (f : X ⟶ T) [Smooth f] [GeometricallyConnected f] (t : T) :
    IsPreirreducible (f ⁻¹' {t}) := by
  have : IrreducibleSpace (f.fiber t) :=
    GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace (T.residueField t) (f.fiber t) (f.fiberToSpecResidueField t)
      (inferInstanceAs (Smooth (pullback.snd _ _))) inferInstance
  rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
  exact (PreirreducibleSpace.isPreirreducible_univ).image _ (f.fiberι t).continuous.continuousOn

theorem eq_of_smooth_comp {W X T Y : Scheme.{0}} (p : X ⟶ T) [Smooth p] (hp : ∀ t : T, IsPreirreducible (p ⁻¹' {t}))
    (m : W ⟶ X) [Smooth m] [Surjective (m ≫ p)] (q : Y ⟶ T) [IsSeparated q] (f g : X ⟶ Y) (hfg : f ≫ q = g ≫ q)
    (h : m ≫ f = m ≫ g) : f = g := by
  let P : X.Opens := ⟨Set.range m, m.isOpenMap.isOpen_range⟩
  refine GlobalTheory.T.hom_ext_of_agree_on_fibreDense_open_smooth X T Y p q P (fun x => ?_) f g hfg ?_
  · obtain ⟨w, hw⟩ := (m ≫ p).surjective (p x)
    have := subset_closure_inter_of_isPreirreducible_of_isOpen (hp (p x)) P.2 ⟨m w, by simpa using hw, w, rfl⟩
    rw [Set.inter_comm] at this
    exact this rfl
  · let l : W ⟶ P.toScheme := IsOpenImmersion.lift P.ι m (by simp [P])
    have hl : l ≫ P.ι = m := IsOpenImmersion.lift_fac _ _ _
    have : Smooth (l ≫ P.ι) := by rw [hl]; infer_instance
    have : Smooth l := smooth_of_comp_mono l P.ι
    have : Surjective l := ⟨fun y => by
      obtain ⟨w, hw⟩ := y.2
      refine ⟨w, P.ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hl]
      exact hw⟩
    have : Epi l := Flat.epi_of_flat_of_surjective l
    rw [← cancel_epi l, ← Category.assoc, ← Category.assoc, hl, h]

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

theorem isOpenImmersion_emb (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    IsOpenImmersion (Desc.emb N p hp).left := by
  have h₁ : IsPullback (Desc.toS N p hp) (pullback.snd N.U.hom (pullback.fst π π ≫ π)) (pullback.snd N.U.hom π) p := by
    refine IsPullback.of_right (h₁₂ := pullback.fst N.U.hom π) (h₂₂ := π) (v₁₃ := N.U.hom) ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback _ _)
    rw [hp, Desc.toS, pullback.lift_fst]
    exact IsPullback.of_hasPullback _ _
  have h₂ : IsPullback (Desc.toS N p hp) (Desc.embL N p hp) N.u (pullback.fst G.hom p) := by
    refine IsPullback.of_bot (v₂₁ := pullback.snd G.hom p) (v₂₂ := G.hom) (h₃₁ := p) ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback _ _)
    rw [N.u_over, Desc.embL, pullback.lift_snd]
    exact h₁
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₂ N.isOpen

theorem surjective_of_closedFibre [GrpObj G] [Surjective π] (N : Near π G) (V : (N.U ⊗ N.U).left.Opens)
    (hV : ∀ z : (N.U ⊗ N.U).left, (N.U ⊗ N.U).hom z = closedPoint R → z ∈ V) :
    Surjective (V.ι ≫ (N.U ⊗ N.U).hom) := by
  have := N.smooth
  have : Smooth (N.U ⊗ N.U).hom := inferInstanceAs (Smooth (pullback.fst N.U.hom N.U.hom ≫ N.U.hom))
  obtain ⟨s, hs⟩ := π.surjective (closedPoint R)
  have he : (η[G]).left ≫ G.hom = 𝟙 S := Over.w η[G]
  have he' : G.hom ((η[G]).left s) = s := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  obtain ⟨x, hx⟩ := N.all ((η[G]).left s) (by rw [he', hs])
  have h₁ : N.U.hom (pullback.fst N.U.hom π x) = closedPoint R := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ← N.u_over, Scheme.Hom.comp_apply, hx, he', hs]
  let z : (N.U ⊗ N.U).left := (lift (𝟙 N.U) (𝟙 N.U)).left (pullback.fst N.U.hom π x)
  have hz : (N.U ⊗ N.U).hom z = closedPoint R := by
    rw [← h₁, ← Scheme.Hom.comp_apply, Over.w]
  let O : TopologicalSpace.Opens (PrimeSpectrum R) :=
    ⟨Set.range (V.ι ≫ (N.U ⊗ N.U).hom), (V.ι ≫ (N.U ⊗ N.U).hom).isOpenMap.isOpen_range⟩
  have hO : O = ⊤ := (closedPoint_mem_iff O).1 ⟨⟨z, hV z hz⟩, hz⟩
  exact ⟨fun t => (hO.ge (Set.mem_univ t) : t ∈ O)⟩

def toSq (N : Near π G) : (Desc.UT N ⊗ Desc.UT N).left ⟶ (N.U ⊗ N.U).left :=
  pullback.lift ((fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst N.U.hom (pullback.fst π π ≫ π))
    ((snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst N.U.hom (pullback.fst π π ≫ π)) (by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc _ _ (_ ≫ π)]
      exact congrArg (· ≫ _) ((Over.w (fst (Desc.UT N) (Desc.UT N))).trans (Over.w (snd (Desc.UT N) (Desc.UT N))).symm))

theorem toSq_fst (N : Near π G) : toSq N ≫ (fst N.U N.U).left =
    (fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst N.U.hom (pullback.fst π π ≫ π) := pullback.lift_fst _ _ _

theorem toSq_snd (N : Near π G) : toSq N ≫ (snd N.U N.U).left =
    (snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst N.U.hom (pullback.fst π π ≫ π) := pullback.lift_snd _ _ _

theorem toSq_hom (N : Near π G) : toSq N ≫ (N.U ⊗ N.U).hom =
    (Desc.UT N ⊗ Desc.UT N).hom ≫ pullback.fst π π ≫ π := by
  rw [← Over.w (fst N.U N.U), ← Category.assoc, toSq_fst, Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ _) (Over.w (fst (Desc.UT N) (Desc.UT N)))

theorem surjective_preimage (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) [Surjective (V.ι ≫ (N.U ⊗ N.U).hom)] :
    Surjective ((toSq N ⁻¹ᵁ V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom) := by
  let a := V.ι ≫ (N.U ⊗ N.U).hom
  let b := pullback.fst π π ≫ π
  let Z : Over (pullback π π) := Over.mk (pullback.snd a b)
  let k₁ : Z ⟶ Desc.UT N := Over.homMk (pullback.lift (pullback.fst a b ≫ V.ι ≫ (fst N.U N.U).left) (pullback.snd a b) (by
    rw [Category.assoc, Category.assoc, Over.w]; exact pullback.condition)) (pullback.lift_snd _ _ _)
  let k₂ : Z ⟶ Desc.UT N := Over.homMk (pullback.lift (pullback.fst a b ≫ V.ι ≫ (snd N.U N.U).left) (pullback.snd a b) (by
    rw [Category.assoc, Category.assoc, Over.w]; exact pullback.condition)) (pullback.lift_snd _ _ _)
  let k : pullback a b ⟶ (Desc.UT N ⊗ Desc.UT N).left := (lift k₁ k₂).left
  have hk : k ≫ toSq N = pullback.fst a b ≫ V.ι := by
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans ((congrArg (k ≫ ·) (toSq_fst N)).trans ?_)
      have : k ≫ (fst (Desc.UT N) (Desc.UT N)).left = k₁.left := congrArg (·.left) (lift_fst k₁ k₂)
      rw [← Category.assoc, this]
      exact (pullback.lift_fst _ _ _).trans (Category.assoc _ _ _).symm
    · refine (Category.assoc _ _ _).trans ((congrArg (k ≫ ·) (toSq_snd N)).trans ?_)
      have : k ≫ (snd (Desc.UT N) (Desc.UT N)).left = k₂.left := congrArg (·.left) (lift_snd k₁ k₂)
      rw [← Category.assoc, this]
      exact (pullback.lift_fst _ _ _).trans (Category.assoc _ _ _).symm
  have hk' : k ≫ (Desc.UT N ⊗ Desc.UT N).hom = pullback.snd a b := Over.w (lift k₁ k₂)
  refine ⟨fun t => ?_⟩
  obtain ⟨z, hz⟩ := (pullback.snd a b).surjective t
  refine ⟨⟨k z, ?_⟩, ?_⟩
  · show toSq N (k z) ∈ V
    rw [← Scheme.Hom.comp_apply, hk]
    exact (pullback.fst a b z).2
  · rw [← hz, ← hk']
    rfl

theorem exists_factor [GrpObj G] [Surjective π] (N : Near π G) (hN : N.Law) :
    ∃ (W : (Desc.UT N ⊗ Desc.UT N).left.Opens) (m : W.toScheme ⟶ (Desc.UT N).left),
      Surjective (W.ι ≫ (Desc.UT N ⊗ Desc.UT N).hom) ∧
      ∀ (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π),
        m ≫ (Desc.emb N p hp).left = W.ι ≫ (Desc.sum N p hp).left := by
  obtain ⟨V, m, hV, hm, law⟩ := hN
  have := surjective_of_closedFibre N V hV
  let W := toSq N ⁻¹ᵁ V
  let v : W.toScheme ⟶ V.toScheme := toSq N ∣_ V
  have hv : v ≫ V.ι = W.ι ≫ toSq N := morphismRestrict_ι _ _
  let τ : W.toScheme ⟶ pullback π π := W.ι ≫ (Desc.UT N ⊗ Desc.UT N).hom
  let m' : W.toScheme ⟶ pullback N.U.hom (pullback.fst π π ≫ π) := pullback.lift (v ≫ m) τ (by
    rw [Category.assoc, hm, ← Category.assoc, hv, Category.assoc, toSq_hom, Category.assoc])
  refine ⟨W, m', surjective_preimage N V, fun p hp => ?_⟩
  let J : Over.mk τ ⟶ Desc.UT N ⊗ Desc.UT N := Over.homMk W.ι rfl
  have lift₀ : ∀ x : Over.mk τ ⟶ (Over.pullback p).obj G,
      ∃ x₀ : Over.mk (τ ≫ p) ⟶ G, x₀.left = x.left ≫ pullback.fst G.hom p := fun x =>
    ⟨Over.homMk (x.left ≫ pullback.fst G.hom p) ((Category.assoc _ _ _).trans
      ((congrArg (x.left ≫ ·) pullback.condition).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (Over.w x))))), rfl⟩
  have pt : ∀ (c : Over.mk τ ⟶ Desc.UT N), N.Pt (τ ≫ p) (c.left ≫ pullback.fst N.U.hom (pullback.fst π π ≫ π))
      ((c ≫ Desc.emb N p hp).left ≫ pullback.fst G.hom p) := fun c =>
    ⟨c.left ≫ Desc.toS N p hp,
      (Category.assoc _ _ _).trans (congrArg (c.left ≫ ·) (pullback.lift_fst _ _ _)),
      (Category.assoc _ _ _).trans ((congrArg (c.left ≫ ·) (pullback.lift_snd _ _ _)).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (Over.w c)))),
      (Category.assoc _ _ _).trans (((Category.assoc _ _ _).trans
        (congrArg (c.left ≫ ·) (pullback.lift_fst _ _ _))).symm)⟩
  obtain ⟨x₀, hx₀⟩ := lift₀ ((J ≫ fst _ _) ≫ Desc.emb N p hp)
  obtain ⟨y₀, hy₀⟩ := lift₀ ((J ≫ snd _ _) ≫ Desc.emb N p hp)
  have hx := pt (J ≫ fst _ _)
  have hy := pt (J ≫ snd _ _)
  rw [← hx₀] at hx
  rw [← hy₀] at hy
  have ex : v ≫ V.ι ≫ (fst N.U N.U).left = (J ≫ fst _ _).left ≫ pullback.fst N.U.hom (pullback.fst π π ≫ π) := by
    rw [← Category.assoc, hv, Category.assoc, toSq_fst]
    exact (Category.assoc _ _ _).symm
  have ey : v ≫ V.ι ≫ (snd N.U N.U).left = (J ≫ snd _ _).left ≫ pullback.fst N.U.hom (pullback.fst π π ≫ π) := by
    rw [← Category.assoc, hv, Category.assoc, toSq_snd]
    exact (Category.assoc _ _ _).symm
  rw [← ex] at hx
  rw [← ey] at hy
  obtain ⟨x₁, h₁, h₂, h₃⟩ := law _ v (τ ≫ p) x₀ y₀ hx hy
  have hmul := (isGrpPullback_pullback G p).2 (Over.mk τ) _ _ x₀ y₀ hx₀ hy₀
  have hsum : ((J ≫ fst _ _) ≫ Desc.emb N p hp) * ((J ≫ snd _ _) ≫ Desc.emb N p hp) = J ≫ Desc.sum N p hp := by
    rw [Desc.sum, MonObj.comp_mul, Category.assoc, Category.assoc]
  rw [hsum] at hmul
  have e₁ : x₁ = m' ≫ Desc.toS N p hp := by
    apply pullback.hom_ext
    · rw [h₁, Category.assoc, Desc.toS, pullback.lift_fst, pullback.lift_fst]
    · rw [h₂, Category.assoc m', Desc.toS, pullback.lift_snd, ← Category.assoc m', pullback.lift_snd]
  apply pullback.hom_ext
  · refine (Category.assoc _ _ _).trans ((congrArg (m' ≫ ·) (pullback.lift_fst _ _ _)).trans ?_)
    rw [← Category.assoc, ← e₁, h₃]
    exact hmul
  · refine (Category.assoc _ _ _).trans ((congrArg (m' ≫ ·) (pullback.lift_snd _ _ _)).trans ?_)
    refine (pullback.lift_snd _ _ _).trans ?_
    exact ((Category.assoc _ _ _).trans (congrArg (W.ι ≫ ·) (Over.w (Desc.sum N p hp)))).symm

theorem emb_comp_of_sum_comp : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∀ (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (hp' : p' ≫ π = pullback.fst π π ≫ π), ∀ φ : (Over.pullback p).obj G' ⟶ (Over.pullback p').obj G', Desc.sum N p hp ≫ φ = Desc.sum N p' hp' → Desc.emb N p hp ≫ φ = Desc.emb N p' hp' := by
  intro R _ _ _ _ S π _ hπ _ G _ _ hG N hN p p' hp hp' φ hφ
  obtain ⟨W, m, hW, hm⟩ := exists_factor N hN
  have := hG.smooth
  have := hG.separated
  have := hG.geomConnected
  have := N.smooth
  have he := isOpenImmersion_emb N p hp
  have s₁ : Smooth ((Over.pullback p).obj G).hom := inferInstanceAs (Smooth (pullback.snd G.hom p))
  have c₁ : GeometricallyConnected ((Over.pullback p).obj G).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd G.hom p))
  have s₂ : IsSeparated ((Over.pullback p').obj G).hom := inferInstanceAs (IsSeparated (pullback.snd G.hom p'))
  have s₃ : Smooth (Desc.UT N).hom := inferInstanceAs (Smooth (pullback.snd _ _))
  have s₄ : Smooth (Desc.sum N p hp).left := by
    have h : Desc.sum N p hp = (Desc.emb N p hp ⊗ₘ Desc.emb N p hp) ≫ μ[(Over.pullback p).obj G] := by
      rw [Desc.sum, Hom.mul_def, lift_fst_comp_snd_comp]
    have := smooth_mul ((Over.pullback p).obj G)
    have : IsOpenImmersion (Desc.emb N p hp ⊗ₘ Desc.emb N p hp).left := by
      rw [Over.tensorHom_left]
      infer_instance
    rw [h, Over.comp_left]
    infer_instance
  have s₅ : Smooth (m ≫ (Desc.emb N p hp).left) := by
    rw [hm]; infer_instance
  have s₆ : Smooth m := smooth_of_comp_mono m (Desc.emb N p hp).left
  have s₇ : Surjective (m ≫ (Desc.UT N).hom) := by
    rw [← Over.w (Desc.emb N p hp), ← Category.assoc, hm, Category.assoc, Over.w]
    exact hW
  have hirr : ∀ t, IsPreirreducible ((Desc.UT N).hom ⁻¹' {t}) := fun t => by
    have := (isPreirreducible_fibre ((Over.pullback p).obj G).hom t).preimage
      (Desc.emb N p hp).left.isOpenEmbedding
    rw [← Over.w (Desc.emb N p hp)]
    exact this
  ext1
  refine eq_of_smooth_comp (Desc.UT N).hom hirr m ((Over.pullback p').obj G).hom _ _
    ((Over.w _).trans (Over.w _).symm) ?_
  rw [Over.comp_left, ← Category.assoc, hm, hm, Category.assoc, ← Over.comp_left, hφ]

end GlobalTheory.Mum.DescFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearOpenPullbackToSelfProductSurjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.Desc

theorem surjective_U_hom {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} (hπ : Surjective π)
    {G' : Over S} [GrpObj G'] (N : Near π G') : Surjective N.U.hom := by
  have := N.smooth
  obtain ⟨s, hs⟩ := π.surjective (closedPoint R)
  let e : S ⟶ G'.left := (1 : Over.mk (𝟙 S) ⟶ G').left
  have he : e ≫ G'.hom = 𝟙 S := Over.w (1 : Over.mk (𝟙 S) ⟶ G')
  have hes : G'.hom (e s) = s := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  obtain ⟨z, hz⟩ : e s ∈ Set.range N.u := N.all _ (by rw [hes]; exact hs)
  have hzs : pullback.snd N.U.hom π z = s := by
    rw [← N.u_over, Scheme.Hom.comp_apply, hz, hes]
  have hc : closedPoint R ∈ Set.range N.U.hom := ⟨pullback.fst N.U.hom π z, by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hzs, hs]⟩
  exact ⟨fun x => (Flat.generalizingMap N.U.hom).stableUnderGeneralization_range
    (IsLocalRing.specializes_closedPoint x) hc⟩

theorem surjective_UT_hom : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), Surjective π →
    ∀ (G' : Over S) [GrpObj G'] (N : Near π G'), Surjective (Desc.UT N).hom := by
  intro R _ _ S π hπ G' _ N
  have := surjective_U_hom hπ N
  exact inferInstanceAs (Surjective (pullback.snd N.U.hom (pullback.fst π π ≫ π)))

end GlobalTheory.Mum.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefCombinationOfPartialIndicatorsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_combination_of_partial_indicators : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {d : ℕ}, IsArithVar p d → ∀ (T : Type) [Fintype T] (N : ℕ) (M : T × Fin N → HermLB p) (l : ℕ), (∀ τ : T, ∀ i : ℕ, i < N → NefOver (ArInt.comb M fun x => if x.1 = τ ∧ x.2.val < i then -1 else 0) l) → (∀ τ : T, NefOver (ArInt.comb M fun x => if x.1 = τ then 1 else 0) l ∧ NefOver (ArInt.comb M fun x => if x.1 = τ then -1 else 0) l) → ∀ n : T → Fin N → ℤ, (∀ τ, Antitone (n τ)) → NefOver (ArInt.comb M fun x => -n x.1 x.2) l := by
  first | exact @GlobalTheory.HtNefAbel.nefOver_comb_of_antitone | exact GlobalTheory.HtNefAbel.nefOver_comb_of_antitone | (intros; apply GlobalTheory.HtNefAbel.nefOver_comb_of_antitone <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefHermitianBundlePullbackStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VertForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_hermitian_bundle_pullback : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (l : ℕ), l.Prime → NefOver L l → NefOver (L.pull π hπ) l := by
  first | exact @GlobalTheory.VertForm.nefOver_pull | exact GlobalTheory.VertForm.nefOver_pull | (intros; apply GlobalTheory.VertForm.nefOver_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOfSurjectivePullbackNefStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VertForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_of_surjective_pullback_nef : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), Function.Surjective π → ∀ (L : HermLB p) (l : ℕ), l.Prime → NefOver (L.pull π hπ) l → NefOver L l := by
  first | exact @GlobalTheory.NefDescent.nefOver_of_pull | exact GlobalTheory.NefDescent.nefOver_of_pull | (intros; apply GlobalTheory.NefDescent.nefOver_of_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefShiftOfGeneratedAtCharZeroPoints
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefOfGen

theorem card_pos_of_isAlgPt {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) {x : X} (hx : IsAlgPt x) : (0 : ℝ) < Nat.card (X.residueField x →+* ℂ) := by
  obtain ⟨hc, hd⟩ := hx
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint x
  have hr : Set.range i = closure {i (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hr] at hd
  have hbij : Function.Bijective (i.residueFieldMap (genericPoint Z)).hom := by
    refine ⟨RingHom.injective _, fun u => ?_⟩
    obtain ⟨u, rfl⟩ := Z.residue_surjective _ u
    obtain ⟨u, rfl⟩ := i.stalkMap_surjective _ u
    exact ⟨X.residue _ u, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i _) u⟩
  have hc' : CharZero (Z.residueField (genericPoint Z)) := (RingHom.charZero_iff hbij.1).1 hc
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hcΓ hd
  have := GlobalTheory.SmallSecHeight.numberField hZ hc'
  rw [GlobalTheory.HtSelfInter.card_ringHom_eq]
  exact_mod_cast Nat.card_pos

theorem nef_of_gen : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (m N : ℕ) (s : Fin N → (M.pow m).B.Sec), 1 ≤ m → (∀ x : X, CharZero (X.residueField x) → ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i)) → M.SemiPos D → NefFib M → ∃ t : ℝ, 0 ≤ t ∧ (M.shift (fun _ => t) fun _ => rfl).IsNef D := by
  intro hA k _ X _ p D hX M m N s hm hs hsp hf
  have hc : ∀ i, ∃ c : ℝ, s i ∈ ((M.shift (fun _ => -c) fun _ => rfl).pow m).smallSec :=
    fun i => GlobalTheory.AmpleHtLow.small_of_shift k X p D hX M m hm (s i)
  choose c hc using hc
  obtain ⟨h, H⟩ := (hA.arExists k X p D hX).1 M
  refine ⟨-(-(∑ i, |c i|)), ?_, GlobalTheory.HtSelfInter.isNef_shift hX hsp hf fun x hx => ?_⟩
  · rw [neg_neg]
    exact Finset.sum_nonneg fun j _ => abs_nonneg (c j)
  obtain ⟨i, hi⟩ := hs x hx.1
  have hN := card_pos_of_isAlgPt hX hx
  have hb : IsPtHt M x (h x / Nat.card (X.residueField x →+* ℂ)) :=
    ⟨h, H, (div_mul_cancel₀ _ hN.ne').symm⟩
  refine ⟨_, hb, ?_⟩
  have h1 := GlobalTheory.SmallSecHeight.le_ptHt k X p D hX M m (c i) _ x (s i) hm (hc i) hi hx hb
  have h2 : -(∑ j, |c j|) ≤ c i :=
    (neg_le_neg (Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i))).trans (neg_abs_le _)
  exact h2.trans h1

end GlobalTheory.NefOfGen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoetherianSubringPrimeContractionOrDvrStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noetherian_subring_prime_contraction_or_dvr : ∀ (R : Type) [CommRing R] (R₁ : Subring R) [IsNoetherianRing R₁] (p : PrimeSpectrum R₁), p ∈ Set.range (PrimeSpectrum.comap R₁.subtype) ∨ ∃ (Q : PrimeSpectrum R) (k : Type) (_ : Field k) (i : R₁ →+* k) (j : k →+* Q.asIdeal.ResidueField) (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ρ : R₁ →+* V) (e : k →+* FractionRing V), j.comp i = (algebraMap R Q.asIdeal.ResidueField).comp R₁.subtype ∧ e.comp i = (algebraMap V (FractionRing V)).comp ρ ∧ p ∈ Set.range (PrimeSpectrum.comap ρ) := by
  first | exact @GlobalTheory.PrimeReach.prime_contraction_or_dvr | exact GlobalTheory.PrimeReach.prime_contraction_or_dvr | (intros; apply GlobalTheory.PrimeReach.prime_contraction_or_dvr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegId
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegUniqAny

open GlobalTheory.ArcPull GlobalTheory.ArcQ GlobalTheory.PullDegUniq
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem nonempty_isPullDeg_id {φ : R →+* R'} {D : DegPre R} {D₁ D₂ : DegPre R'} (h₁ : IsPullDeg φ D D₁)
    (h₂ : IsPullDeg φ D D₂) : Nonempty (IsPullDeg (RingHom.id R') D₁ D₂) := by
  have hβ : Function.Injective (RingHom.id R') := Function.injective_id
  have h : IsPullDeg ((RingHom.id R').comp φ) D D₂ := (RingHom.id_comp φ).symm ▸ h₂
  have p₁ : IsGrpPullback D₁.P.A D.P.A (spMap φ) (proj h₁) := pull_grp h₁
  have sc : spMap (RingHom.id R') ≫ spMap φ = spMap ((RingHom.id R').comp φ) := (spMap_comp φ _).symm
  have p : IsGrpPullback D₂.P.A D.P.A (spMap (RingHom.id R') ≫ spMap φ) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D₂.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧
      Φ ≫ D₁.P.A.hom = D₂.P.A.hom ≫ spMap (RingHom.id R') :=
    ⟨p₁.1.lift (proj h) (D₂.P.A.hom ≫ spMap (RingHom.id R')) (p.1.w.trans (Category.assoc _ _ _).symm),
      p₁.1.lift_fst _ _ _, p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D₂.P.A D₁.P.A (spMap (RingHom.id R')) Φ :=
    IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := FieldPull.exists_cancel_of_eq e₁ D.P.isLB D₁.P.isLB D₂.P.isLB h₁.w h.w
    ((isGen_iff _).1 h₁.w_gen) ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (FieldPull.pmaps_rig h₁)
    (FieldPull.pmaps_rig h)
  let xe : D₂.X ≃+ D₁.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D₂.c x).left ≫ Φ = spMap (RingHom.id R') ≫ (D₁.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨ψW⟩ := nonempty_psiOn_pull h₁
  obtain ⟨s, hs⟩ := exists_generic_section h₁
  obtain ⟨hD, -⟩ := DvrDeg.exists_isPullDeg_of_val hβ D₁ D₂ ψW s hs gp w hw hr xe hc (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D.P.isLB z
    have sβ : jK R' ≫ spMap (RingHom.id R') = genMap hβ ≫ jK R' :=
      (Category.id_comp _).symm.trans (fracMap_sq hβ)
    have v := PsiEvenPull.psi_pull h x (𝟙 _) z hJ₀ hJ
    have v₁ := PsiEvenPull.psi_pull h₁ (xe x) (genMap hβ) z hJ₀ hJ₁
    have ag : val (h₁.psiW.psi (h.xe x)) (genMap hβ ≫ h₁.g) z J₀ = val (h.psiW.psi (h.xe x)) (𝟙 _ ≫ h.g) z J₀ :=
      ArcSpecialise.psiOn_agree h₁.psiW h.psiW _ _ _ (by
        rw [Category.assoc, h₁.g_comm, Category.assoc, h.g_comm, Category.id_comp, ← Category.assoc, ← sβ,
          Category.assoc]
        exact congrArg (jK R' ≫ ·) sc) hJ₀
    have hx : D₂.xK x ≫ Φ = genMap hβ ≫ D₁.xK (xe x) := by
      show (jK R' ≫ (D₂.c x).left) ≫ Φ = genMap hβ ≫ jK R' ≫ (D₁.c (xe x)).left
      rw [Category.assoc, hc, ← Category.assoc, sβ, Category.assoc]
    change _ = (om h₁.w z J₀ J₁ (genMap hβ ≫ D₁.xK (xe x)))⁻¹ * _ at v₁
    change _ = (om h.w z J₀ J (𝟙 _ ≫ D₂.xK x))⁻¹ * _ at v
    rw [hxe, ag, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  exact ⟨hD⟩

end GlobalTheory.PullDegUniqAny

namespace GlobalTheory.Mum

theorem isPullDeg_unique_any : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D₁ D₂ : DegPre R'), Nonempty (IsPullDeg φ D D₁) → Nonempty (IsPullDeg φ D D₂) → Nonempty (IsPullDeg (RingHom.id R') D₁ D₂) :=
  fun _ _ _ _ _ _ _ _ _ _ ⟨h₁⟩ ⟨h₂⟩ => GlobalTheory.PullDegUniqAny.nonempty_isPullDeg_id h₁ h₂

end GlobalTheory.Mum
end
end

