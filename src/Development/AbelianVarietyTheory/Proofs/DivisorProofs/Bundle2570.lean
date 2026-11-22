import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2521
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2455

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreFieldPointsInjectiveProjectiveMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ClosedFibreInj

theorem spMap_epi {K L : Type} [Field K] [Field L] (f : K →+* L) : Epi (spMap f) := by
  letI := f.toAlgebra
  haveI : Flat (spMap f) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (show Module.Flat K L from inferInstance)
  haveI : Surjective (spMap f) := ⟨fun z => ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem point_lift (Ω : Type) [Field Ω] (X Y : Scheme.{0}) (g : Y ⟶ X) (hg : Surjective g) (x : Sp Ω ⟶ X) :
    ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω') (y : Sp Ω' ⟶ Y), y ≫ g = spMap io ≫ x := by
  haveI := hg
  obtain ⟨w⟩ : Nonempty ↥(Sp Ω) := inferInstance
  obtain ⟨z, -⟩ := (pullback.fst x g).surjective w
  refine ⟨(pullback x g).residueField z, inferInstance,
    (Spec.preimage ((pullback x g).fromSpecResidueField z ≫ pullback.fst x g)).hom,
    (pullback x g).fromSpecResidueField z ≫ pullback.snd x g, ?_⟩
  rw [Category.assoc, ← pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ x) (Spec.map_preimage _).symm

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem closedFibre_inj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → Surjective M.π → ∀ (Ω : Type) [Field Ω] (κ : ResidueField R →+* Ω) (a a' : Sp Ω ⟶ N.U.left), a ≫ N.U.hom = spMap (κ.comp (residue R)) → a' ≫ N.U.hom = spMap (κ.comp (residue R)) → a ≫ fU = a' ≫ fU → a = a' := by
  intro R _ _ _ M G' _ E N fU l hl hlf hπ Ω _ κ a a' ha ha' hf
  haveI := N.isOpen
  haveI := E.imm
  obtain ⟨Ω', _, io, s, hs⟩ := point_lift Ω (Sp R) M.S M.π hπ (spMap (κ.comp (residue R)))
  have hs' : s ≫ M.π = spMap ((io.comp κ).comp (residue R)) := by
    rw [hs, ← spMap_comp, RingHom.comp_assoc]
  obtain ⟨Ω'', _, io', e, l', -, hl'1, hl'2⟩ := E.fib Ω' s (io.comp κ) hs'

  have pt : ∀ (b : Sp Ω ⟶ N.U.left) (hb : b ≫ N.U.hom = spMap (κ.comp (residue R))),
      ∃ x : Sp Ω'' ⟶ pullback G'.hom (spMap io' ≫ s),
        x ≫ pullback.fst _ _ = spMap io' ≫ pullback.lift (spMap io ≫ b) s (by rw [Category.assoc, hb, hs]) ≫ N.u ∧
        x ≫ pullback.snd _ _ = 𝟙 _ ∧
        x ≫ e.hom.left ≫ pullback.fst _ _ ≫ E.j = spMap io' ≫ spMap io ≫ b ≫ fU := by
    intro b hb
    have hc : (spMap io ≫ b) ≫ N.U.hom = s ≫ M.π := by rw [Category.assoc, hb, hs]
    set p := pullback.lift (spMap io ≫ b) s hc with hp
    refine ⟨pullback.lift (spMap io' ≫ p ≫ N.u) (𝟙 _) (by
      rw [Category.id_comp, Category.assoc, Category.assoc, N.u_over, hp, pullback.lift_snd]), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _, ?_⟩
    have h1 : pullback.lift (spMap io' ≫ p ≫ N.u) (𝟙 _) (by
        rw [Category.id_comp, Category.assoc, Category.assoc, N.u_over, hp, pullback.lift_snd]) ≫ l' =
        spMap io' ≫ p ≫ l := by
      rw [← cancel_mono E.H.ι, Category.assoc, hl'1, pullback.lift_fst, Category.assoc, Category.assoc, hl]
    rw [← hl'2, ← Category.assoc, h1, Category.assoc, Category.assoc, hlf, ← Category.assoc p, hp,
      pullback.lift_fst, Category.assoc]
  obtain ⟨x, hx1, hx2, hx3⟩ := pt a ha
  obtain ⟨x', hx1', hx2', hx3'⟩ := pt a' ha'
  have hj : x ≫ e.hom.left ≫ pullback.fst _ _ = x' ≫ e.hom.left ≫ pullback.fst _ _ := by
    rw [← cancel_mono E.j, Category.assoc, Category.assoc, Category.assoc, Category.assoc, hx3, hx3', hf]
  have hsec : ∀ y : Sp Ω'' ⟶ pullback G'.hom (spMap io' ≫ s), y ≫ pullback.snd _ _ = 𝟙 _ →
      y ≫ e.hom.left ≫ pullback.snd _ _ = 𝟙 _ := by
    intro y hy
    have hw := Over.w e.hom
    simp only [Over.pullback_obj_hom] at hw
    rw [hw, hy]
  have he : x ≫ e.hom.left = x' ≫ e.hom.left :=
    pullback.hom_ext (by simpa using hj) (by rw [Category.assoc, Category.assoc, hsec x hx2, hsec x' hx2'])
  have hxx : x = x' := by
    have := congrArg (· ≫ e.inv.left) he
    simpa [← Over.comp_left] using this
  subst hxx
  rw [hx1'] at hx1
  simp only [← Category.assoc, cancel_mono] at hx1
  have h2 := congrArg (· ≫ pullback.fst N.U.hom M.π) hx1
  simp only [Category.assoc, pullback.lift_fst] at h2
  haveI := spMap_epi io'
  haveI := spMap_epi io
  rw [cancel_epi, cancel_epi] at h2
  exact h2.symm

end GlobalTheory.Mum.ClosedFibreInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionOfBaseChangeFieldExt
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ClosedImmFieldDescent

set_option backward.isDefEq.respectTransparency.types false

theorem isClosedImmersion_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@IsClosedImmersion : MorphismProperty Scheme.{0})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := GlobalTheory.isAffineHom_descendsAlong_fpqc.{0}
  have hP : HasAffineProperty @IsClosedImmersion (affineAnd fun f ↦ Function.Surjective f) :=
    IsClosedImmersion.hasAffineProperty
  have H₂ : ∀ {R S : CommRingCat.{0}} {f : R ⟶ S}, (@Surjective ⊓ @Flat) (Spec.map f) →
      RingHom.FaithfullyFlat f.hom := by
    intro R S f ⟨hf₁, hf₂⟩
    rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    refine ⟨?_, (Spec.map f).surjective⟩
    rwa [HasRingHomProperty.Spec_iff (P := @Flat)] at hf₂
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ ?_ ?_
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  intro R S Y φ g h hf
  have : IsAffine Y := by
    have : IsAffineHom g := MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := @IsAffineHom) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨h, inferInstance⟩
      (HasAffineProperty.affineAnd_le_isAffineHom @IsClosedImmersion hP _ hf)
    exact isAffine_of_isAffineHom g
  wlog hY : ∃ S, Y = Spec S generalizing Y
  · rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) Y.isoSpec.inv]
    have heq : pullback.fst (Spec.map φ) (Y.isoSpec.inv ≫ g) =
        pullback.map _ _ _ _ (𝟙 _) (Y.isoSpec.inv) (𝟙 _) (by simp) (by simp) ≫
          pullback.fst (Spec.map φ) g := (pullback.lift_fst _ _ _).symm
    refine this _ ?_ inferInstance ⟨_, rfl⟩
    rwa [heq, MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)]
  obtain ⟨Y, rfl⟩ := hY
  apply of_pullback_fst_Spec_of_codescendsAlong _ _ RingHom.FaithfullyFlat.codescendsAlong_surjective H₂ _ h hf
  intro R' S' f'
  exact HasAffineProperty.SpecMap_iff_of_affineAnd hP RingHom.surjective_respectsIso f'

theorem isPullback_baseChange_step {R k Ω : Type} [CommRing R] [Field k] [Field Ω] [Algebra R k]
    [Algebra k Ω] [Algebra R Ω] [IsScalarTower R k Ω] {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R)) :
    IsPullback (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))
      (pullback.map c (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) c (Spec.map (CommRingCat.ofHom (algebraMap R k)))
        (𝟙 C) (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (𝟙 _) (by simp)
        (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
      (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R k)))) := by
  have e : Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R k)) =
      Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  refine IsPullback.of_bot ?_ (pullback.lift_snd _ _ _).symm (IsPullback.of_hasPullback c _).flip
  have h0 := (IsPullback.of_hasPullback c (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).flip
  rw [pullback.lift_fst, Category.comp_id, e]
  exact h0

theorem fpqc_specMap_field (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) := by
  refine ⟨⟨⟨fun x ↦ ?_⟩, ?_⟩, inferInstance⟩
  · obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of Ω)) := inferInstanceAs (Nonempty (PrimeSpectrum Ω))
    exact ⟨y, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩
  · rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance

theorem isClosedImmersion_of_baseChange_extension :
    ∀ (R k Ω : Type) [CommRing R] [Field k] [Field Ω] [Algebra R k] [Algebra k Ω] [Algebra R Ω] [IsScalarTower R k Ω] (V W : Over (Spec (CommRingCat.of R))) (f : V ⟶ W), IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map f).left → IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map f).left := by
  intro R k Ω _ _ _ _ _ _ _ V W f hΩ
  have hd := isClosedImmersion_descendsAlong_fpqc
  have e : (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R k))) = (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let vX := pullback.map V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) V.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (𝟙 _) (by simp) (by rw [Category.comp_id, e])
  let vY := pullback.map W.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) W.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (𝟙 _) (by simp) (by rw [Category.comp_id, e])
  have sX : IsPullback (pullback.snd V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) vX (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (pullback.snd V.hom (Spec.map (CommRingCat.ofHom (algebraMap R k)))) :=
    isPullback_baseChange_step (k := k) (Ω := Ω) V.hom
  have sY : IsPullback (pullback.snd W.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) vY (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (pullback.snd W.hom (Spec.map (CommRingCat.ofHom (algebraMap R k)))) :=
    isPullback_baseChange_step (k := k) (Ω := Ω) W.hom
  let φk := ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map f).left
  let φΩ := ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map f).left
  have hk2 : φk ≫ pullback.snd W.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) = pullback.snd V.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) := by simp only [φk, Over.pullback_map_left, pullback.lift_fst, pullback.lift_snd, Category.comp_id, Category.assoc]
  have hk1 : φk ≫ pullback.fst W.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) = pullback.fst V.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) ≫ f.left := by simp only [φk, Over.pullback_map_left, pullback.lift_fst, pullback.lift_snd, Category.comp_id, Category.assoc]
  have hΩ2 : φΩ ≫ pullback.snd W.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) = pullback.snd V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) := by simp only [φΩ, Over.pullback_map_left, pullback.lift_fst, pullback.lift_snd, Category.comp_id, Category.assoc]
  have hΩ1 : φΩ ≫ pullback.fst W.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) = pullback.fst V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≫ f.left := by simp only [φΩ, Over.pullback_map_left, pullback.lift_fst, pullback.lift_snd, Category.comp_id, Category.assoc]
  have comm : φΩ ≫ vY = vX ≫ φk := by
    apply pullback.hom_ext
    · simp only [vX, vY, Category.assoc, hk1, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
      exact hΩ1
    · simp only [vX, vY, Category.assoc, hk2, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
      rw [← Category.assoc, hΩ2]
  have sq : IsPullback φΩ vX vY φk := by
    refine IsPullback.of_right ?_ comm sY
    rw [hΩ2, hk2]
    exact sX
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsClosedImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq
    (MorphismProperty.of_isPullback (P := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sY (fpqc_specMap_field k Ω)) hΩ

end GlobalTheory.ClosedImmFieldDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetReductionGood
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel.HalfFormUnit

theorem conj_mem_orderC {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)} {x : E} (hx : x ∈ orderC c) :
    IsCMField.complexConj E x ∈ orderC c := by
  obtain ⟨a, b, hb, rfl⟩ := mem_orderC.1 hx
  refine mem_orderC.2 ⟨a, IsCMField.ringOfIntegersComplexConj E b, ?_, ?_⟩
  · have : c.map (algebraMap (OF E) (𝓞 E)) ≤
        (c.map (algebraMap (OF E) (𝓞 E))).comap (IsCMField.ringOfIntegersComplexConj E) := by
      rw [Ideal.map_le_iff_le_comap]
      intro z hz
      rw [Ideal.mem_comap, Ideal.mem_comap, AlgEquiv.commutes]
      exact Ideal.mem_map_of_mem _ hz
    exact this hb
  · rw [map_add]
    congr 1
    exact (IsCMField.complexConj E).commutes (a : FR E)

theorem span_bcMap {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [Algebra R R'] {A : Over (Sp R)} [GrpObj A]
    {A' : Over (Sp R')} [GrpObj A'] {φ : A'.left ⟶ A.left}
    {m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' (algebraMap R R') (spMap (algebraMap R R')) φ} (hm : m.IsBC)
    [Module.Finite R (primDR A)] [Module.Projective R (primDR A)] (lam : HdR A' →ₗ[R'] R')
    (h : ∀ x, lam (hm.bcMap x) = 0) : lam = 0 := by
  haveI : Module.Free R (primDR A) := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis R (primDR A)
  refine LinearMap.ext fun y ↦ ?_
  have : y = ∑ k, y (m.pull (b k)) • hm.bcMap (b.coord k) := by
    refine LinearMap.ext fun c ↦ ?_
    obtain ⟨z, rfl⟩ := hm.2 c
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x c =>
      rw [liftSemi_tmul, map_smul, map_smul]
      congr 1
      rw [LinearMap.sum_apply]
      conv_lhs => rw [← b.sum_repr c, map_sum, map_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [LinearMap.smul_apply, hm.corr_iff.2 rfl c, LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
      rfl
  rw [this, map_sum]
  simp [h]

open ReciprocityTheory.ChartRestriction.G.Chart (isTan_iff) in

theorem exists_coord {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ)) {L : LB X.A.left}
    (u : HolUnif X.A L (Module.finrank ℚ F)) :
    ∃ D : X.Lie →ₗ[ℂ] (Fin (Module.finrank ℚ F) → ℂ), Function.Surjective D ∧ ∀ v w, u.IsDiff w v.hom ↔ D v = w := by
  obtain ⟨h1, h2⟩ := GlobalTheory.TorusTransfer.tangent_bijective u X.dim
  choose D hD hu using fun v : X.Lie ↦ h1 v.hom v.isTangent
  refine ⟨{ toFun := D, map_add' := fun v v' ↦ ?_, map_smul' := fun c v ↦ ?_ }, fun w ↦ ?_,
    fun v w ↦ ⟨fun h ↦ (hu v w h).symm, fun h ↦ h ▸ hD v⟩⟩
  · refine (hu _ _ ?_).symm
    have := GlobalTheory.UnifLieBasis.isDiff_add u ((isTan_iff _).2 v.isTangent) ((isTan_iff _).2 v'.isTangent) (hD v) (hD v')
    rw [Serre.Lie.hom_add]
    exact this
  · refine (hu _ _ ?_).symm
    have := GlobalTheory.UnifLieBasis.isDiff_smul u ((isTan_iff _).2 v.isTangent) (hD v) c
    convert this using 1
    all_goals rfl
  · obtain ⟨v, ⟨hv, hw⟩, -⟩ := h2 w
    exact ⟨Serre.Lie.mk X.rm v hv, (hu (Serre.Lie.mk X.rm v hv) w hw).symm⟩

theorem periodGen_eigen (P : GlobalTheory.Published.AbelianDeRham) {E : Type} [Field E] [NumberField E] {I : Type} {φ : I → E →+* ℂ}
    {𝔠 : FracId (FR E)} {R : Subring ℂ} [IsLocalRing R] {X₀ : Obj (FR E) 𝔠 (Sp R)} {X : Obj (FR E) 𝔠 (Sp ℂ)} {L : Set E}
    {U : Unif φ L 0 X} {p : X.A.left ⟶ X₀.A.left} (hp : X.IsPullBy X₀ (spMap R.subtype) p) (hL : LieExact X₀.A)
    {i : I} {e : X₀.Lie →ₗ[R] R} {a : ℂ} (ha : a ≠ 0) (he : IsPeriodGen X₀ U p i e a) :
    (∃ x, e (hL.toLie X₀.rm x) ≠ 0) ∧
    ∀ (β : X₀.A ⟶ X₀.A) [IsMonHom β] (α : X.A ⟶ X.A) [IsMonHom α] (c : Fin (Module.finrank ℚ (FR E)) → ℂ),
      α.left ≫ p = p ≫ β.left → (∀ w, U.u.ex (fun j ↦ c j * w j) = U.u.ex w ≫ α) → ∀ x,
      (e (hL.toLie X₀.rm (push (dp0 R) (𝟙 _) β x)) : ℂ) = c (U.e.symm i) * e (hL.toLie X₀.rm x) := by
  have hφ : IsGrpPullback X.A X₀.A (spMap (algebraMap R ℂ)) p := hp.grp
  obtain ⟨hm, -⟩ := P.2.2.1 R X₀.A _ X₀.ab X₀.dim ℂ X.A p hφ
  have hL' := (P.2.1 ℂ X.A _ X.ab X.dim).1
  obtain ⟨hfin, hproj, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim P.1 X₀.ab X₀.dim
  obtain ⟨D, hDs, hD⟩ := exists_coord X U.u
  have key : ∀ x y, (GlobalTheory.Published.AbelianDeRham.bcMor hφ).Corr x y →
      (e (hL.toLie X₀.rm x) : ℂ) = a * D (hL'.toLie X.rm y) (U.e.symm i) := fun x y hxy ↦
    he _ _ _ (Obj.lieCorr_of_isLieImage P R.subtype hp (GlobalTheory.Published.AbelianDeRham.bcMor hφ) hxy
      ((hL.toLie_eq_iff _).1 rfl) ((hL'.toLie_eq_iff _).1 rfl)) ((hD _ _).2 rfl)
  refine ⟨?_, fun β _ α _ c hαβ hα x ↦ ?_⟩
  · by_contra h0
    push_neg at h0
    have := span_bcMap hm (LinearMap.proj (U.e.symm i) ∘ₗ D ∘ₗ hL'.toLie X.rm) fun x ↦ by
      have h1 := key x _ (hm.corr_iff.2 rfl)
      rw [h0] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left ha
    obtain ⟨v, hv⟩ := hDs fun _ ↦ 1
    obtain ⟨y, rfl⟩ := hL'.toLie_surjective X.rm v
    have h2 := LinearMap.congr_fun this y
    simp [hv] at h2
  · have hx := hm.corr_iff.2 (rfl : hm.bcMap x = _)
    rw [key _ _ hx, key _ _ (GrpMor.Corr.push (GlobalTheory.Published.AbelianDeRham.bcMor hφ) β α hαβ.symm hx),
      hL'.toLie_push hL' X.rm X.rm]
    let M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
      { toFun := fun w j => c j * w j
        map_add' := fun w w' => by funext j; simp [mul_add]
        map_smul' := fun r w => by funext j; simp; ring }
    have h3 := GlobalTheory.UnifLieBasis.isDiff_comp U.u α (LinearMap.toContinuousLinearMap M) hα
      (hL'.toLie X.rm (hm.bcMap x)).isTangent ((hD _ _).2 rfl)
    rw [(hD (Serre.Lie.map X.rm X.rm α (hL'.toLie X.rm (hm.bcMap x))) _).1 h3]
    change a * (c _ * _) = _
    ring

theorem mem_eigLat {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)} {R K : Type} [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] {H : Type*} [AddCommGroup H] [Module R H] {H' : Type} [AddCommGroup H'] [Module R H']
    (eH : H ≃ₗ[R] H') (ρ : orderC c →+* Module.End R H) (σ : E →+* K) (h : H) {r : R} (hr : r ≠ 0)
    (hh : ∀ a : orderC c, ∃ s : R, algebraMap R K s = σ a * algebraMap R K r ∧ r • ρ a h = s • h) :
    eH h ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp ρ) σ := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK, Submodule.mem_comap, Submodule.restrictScalars_mem,
    Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  intro a
  obtain ⟨s, h2, h1⟩ := hh a
  have hr0 : algebraMap R K r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hr
  refine smul_right_injective _ hr0 ?_
  have h3 : LinearMap.baseChange K ((eH.conjRingEquiv.toRingHom.comp ρ) a) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H' (eH h)) =
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H' (eH (ρ a h)) := by
    simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK]
  dsimp only
  rw [h3, smul_smul, mul_comm, ← h2, algebraMap_smul, algebraMap_smul, ← map_smul, ← map_smul, h1, map_smul, map_smul]

theorem exists_factor {R : Type} [CommRing R] [IsDomain R] {H M : Type*} [AddCommGroup H] [Module R H] [AddCommGroup M]
    [Module R M] (π : H →ₗ[R] M) (hπ : Function.Surjective π) (f : H →ₗ[R] R) (e : M →ₗ[R] R) {s : R} (hs : s ≠ 0)
    (h : ∀ x, s * f x = e (π x)) : ∃ ℓ : M →ₗ[R] R, ∀ x, ℓ (π x) = f x := by
  have hker : LinearMap.ker π ≤ LinearMap.ker f := fun x hx ↦ by
    have := h x
    rw [LinearMap.mem_ker.1 hx, map_zero] at this
    exact (mul_eq_zero.1 this).resolve_left hs
  refine ⟨(LinearMap.ker π).liftQ _ hker ∘ₗ (π.quotKerEquivOfSurjective hπ).symm.toLinearMap, fun x ↦ ?_⟩
  simp

set_option maxHeartbeats 800000 in

theorem halfForm_eq_unit_mul : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i) →
    ∀ (hL : LieExact X₀.A) (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (c₀ : 𝔠.elt) (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)),
      (c₀ : FR E) ≠ 0 → IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) ((2 : R) • ψ₀) → Function.Bijective ψ₀ →
      (∀ a b : orderC (condQ 𝔣 Q), (b : E) = IsCMField.complexConj E a → ∀ h h' : HdR X₀.A,
        ψ₀ (act (dp0 R) (𝟙 _) cm a h) h' = ψ₀ h (act (dp0 R) (𝟙 _) cm b h')) →
      (Submodule.map eH.toLinearMap (Fil X₀.A)).baseChange (FractionRing R) =
        ⨆ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) →
      ∀ i (g : Fin n → R), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) = Submodule.span R {g} →
        ∃ r : Rˣ, ∀ x, ψ₀ (eH.symm g) x = (r : R) * e i (hL.toLie X₀.rm x) := by
  intro _ P _ E _ _ _ _ I _ d φ _ 𝔣 _ l _ Q _ _ y _ lam 𝔠 R _ _ X₀ X U p cm hp _ hcm j hj φK hφK e a he hL n eH c₀ ψ₀ _ _
    hψ hadj _ i g hg
  obtain ⟨ha, hper, huniq⟩ := he i
  obtain ⟨⟨x₀, hx₀⟩, heig⟩ := periodGen_eigen P hp hL ha hper
  obtain ⟨h, hh⟩ := hψ.2 (e i ∘ₗ hL.toLie X₀.rm)
  have hh' : ∀ x, ψ₀ h x = e i (hL.toLie X₀.rm x) := fun x ↦ LinearMap.congr_fun hh x
  have heig' : ∀ (b : orderC (condQ 𝔣 Q)) x,
      (e i (hL.toLie X₀.rm (act (dp0 R) (𝟙 _) cm b x)) : ℂ) = φ i b * e i (hL.toLie X₀.rm x) := fun b x ↦ by
    obtain ⟨α, hα, h1, h2⟩ := hcm b
    haveI := cm.hom b
    have := heig (cm.act b) α (fun j ↦ φ (U.e j) (b : E)) h1 h2 x
    rwa [Equiv.apply_symm_apply] at this
  have hmem : eH h ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm))
      (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) := by
    refine mem_eigLat eH _ _ h hx₀ fun c ↦ ?_
    let b : orderC (condQ 𝔣 Q) := ⟨_, conj_mem_orderC c.2⟩
    refine ⟨e i (hL.toLie X₀.rm (act (dp0 R) (𝟙 _) cm b x₀)), j.injective ?_, hψ.1 (LinearMap.ext fun x ↦ ?_)⟩
    · rw [map_mul, hj, hj, heig', ← hφK i]
      rfl
    · rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, hadj c b rfl, hh', hh']
      apply Subtype.ext
      simp only [smul_eq_mul, Subring.coe_mul]
      rw [heig', heig']
      ring
  rw [hg] at hmem
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 hmem
  have hsg : ∀ x, s * ψ₀ (eH.symm g) x = e i (hL.toLie X₀.rm x) := fun x ↦ by
    have h1 : h = s • eH.symm g := by rw [← LinearEquiv.map_smul, hs, eH.symm_apply_apply]
    rw [← hh', h1, LinearMap.map_smul₂, smul_eq_mul]
  have hs0 : s ≠ 0 := fun h0 ↦ hx₀ (by rw [← hsg, h0, zero_mul])
  obtain ⟨ℓ, hℓ⟩ := exists_factor (hL.toLie X₀.rm) (hL.toLie_surjective X₀.rm) (ψ₀ (eH.symm g)) (e i) hs0 hsg
  have hs0' : (s : ℂ) ≠ 0 := fun h0 ↦ hs0 (Subtype.ext h0)
  obtain ⟨t, ht⟩ := huniq ℓ (a i / s) fun v v' W h1 h2 ↦ by
    have h3 := hper v v' W h1 h2
    obtain ⟨x, rfl⟩ := hL.toLie_surjective X₀.rm v
    rw [← hsg, Subring.coe_mul] at h3
    rw [hℓ, div_mul_eq_mul_div, ← h3, mul_div_cancel_left₀ _ hs0']
  have hst : t * s = 1 := by
    have := hsg x₀
    rw [← hℓ, ht, LinearMap.smul_apply, smul_eq_mul, ← _root_.mul_assoc] at this
    rw [mul_comm]
    exact mul_right_cancel₀ hx₀ (this.trans (_root_.one_mul _).symm)
  refine ⟨Units.mkOfMulEqOne t s hst, fun x ↦ ?_⟩
  rw [← hℓ, ht]
  rfl

end GlobalTheory.LatModel.HalfFormUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmDeRhamEigenspaceCorankLeTwoStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_de_rham_eigenspace_corank_le_two : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
      (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X), IsCMType φ →
    ∀ (i : I) (b₀ : 𝓞 (FR E)), (∀ j : I, φ j ((b₀ : FR E) : E) = φ i ((b₀ : FR E) : E) → j = i) →
      Module.rank ℂ (HdR X.A ⧸ LinearMap.range (act (dp0 ℂ) (𝟙 _) X.rm b₀ - φ i ((b₀ : FR E) : E) • 1)) ≤ 2 ∧
      Disjoint (LinearMap.ker (act (dp0 ℂ) (𝟙 _) X.rm b₀ - φ i ((b₀ : FR E) : E) • 1))
        (LinearMap.range (act (dp0 ℂ) (𝟙 _) X.rm b₀ - φ i ((b₀ : FR E) : E) • 1)) := by
  first | exact @GlobalTheory.RealMultEigen.rank_coker_le_two | exact GlobalTheory.RealMultEigen.rank_coker_le_two | (intros; apply GlobalTheory.RealMultEigen.rank_coker_le_two <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeImageDiscreteStatement
section
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_lattice_image_discrete : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (L : Submodule (OF E) E), (∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) →
    ∀ (Λ : Submodule ℤ (Fin n → ℂ)), (∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ φ (e j) x) → DiscreteTopology Λ := by
  first | exact @GlobalTheory.CMLatticeDiscrete.cmLattice_discrete | exact GlobalTheory.CMLatticeDiscrete.cmLattice_discrete | (intros; apply GlobalTheory.CMLatticeDiscrete.cmLattice_discrete <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeImageSpansRealStatement
section
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_lattice_image_spans_real : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (L : Submodule (OF E) E), (∃ N : ℕ, 0 < N ∧ ∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ L) →
    ∀ (Λ : Submodule ℤ (Fin n → ℂ)), (∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ φ (e j) x) →
      Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ := by
  first | exact @GlobalTheory.CMSpan.span_real_eq_top | exact GlobalTheory.CMSpan.span_real_eq_top | (intros; apply GlobalTheory.CMSpan.span_real_eq_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodMatrixExistsStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_period_matrix_exists : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ e : Fin (Module.finrank ℚ (FR E)) ≃ I,
      ∃ M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ), Function.Surjective M ∧
        ∀ z, (∀ j, ∃ a b : ℤ, z j = a + b * io δ) → ∃ x ∈ lattice c y, M z = fun j ↦ φ (e j) x := by
  first | exact @GlobalTheory.LatModel.surj_lattice | exact GlobalTheory.LatModel.surj_lattice | (intros; apply GlobalTheory.LatModel.surj_lattice <;> assumption)
end

