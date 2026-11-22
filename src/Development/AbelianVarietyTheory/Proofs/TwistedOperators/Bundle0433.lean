import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0003
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0034
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0426
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesSUIff

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteEtaleAlgebraPullbackAffine
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.HeckeEx

theorem exists_finiteEtale_algebra_pullback : ∀ (X Y : Scheme.{0}) (π : Y ⟶ X), IsFinite π → Etale π → ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (h : Sp B ⟶ Y), Module.Finite R B ∧ Algebra.Etale R B ∧ h ≫ π = spMap (algebraMap R B) ≫ x ∧ (Surjective π → Function.Surjective (PrimeSpectrum.comap (algebraMap R B))) ∧ ∀ (Ω : Type) [CommRing Ω] (φ : R →+* Ω) (w : Sp Ω ⟶ Y), w ≫ π = spMap φ ≫ x → ∃! χ : B →+* Ω, χ.comp (algebraMap R B) = φ ∧ spMap χ ≫ h = w := by
  intro X Y π hfin het R _ x
  haveI : IsAffine (pullback π x) := isAffine_of_isAffineHom (pullback.snd π x)
  obtain ⟨S, e, -⟩ : ∃ (S : CommRingCat.{0}) (_ : Spec S ≅ pullback π x), True :=
    ⟨_, (pullback π x).isoSpec.symm, trivial⟩
  obtain ⟨f, hf⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := S)
    (e.hom ≫ pullback.snd π x)
  letI : Algebra R S := f.hom.toAlgebra
  have hsp : spMap (algebraMap R S) = e.hom ≫ pullback.snd π x := hf
  refine ⟨S, inferInstance, inferInstance, e.hom ≫ pullback.fst π x, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : IsFinite (Spec.map f) := by rw [hf]; infer_instance
    exact (IsFinite.SpecMap_iff f).1 h1
  · have h1 : Etale (Spec.map f) := by rw [hf]; infer_instance
    exact RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1 h1)
  · rw [hsp, Category.assoc, Category.assoc, pullback.condition]
  · intro hs
    have h1 : Surjective (Spec.map f) := by rw [hf]; infer_instance
    exact h1.surj
  · intro Ω _ φ w hw
    obtain ⟨g, hg⟩ := Spec.map_surjective (R := S) (S := CommRingCat.of Ω)
      (pullback.lift w (spMap φ) hw ≫ e.inv)
    have key : ∀ χ : S →+* Ω, χ.comp (algebraMap R S) = φ ↔
        spMap χ ≫ e.hom ≫ pullback.snd π x = spMap φ := by
      intro χ
      rw [← hsp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      constructor
      · intro h; rw [h]
      · intro h
        exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
    have hg' : spMap g.hom = pullback.lift w (spMap φ) hw ≫ e.inv := hg
    refine ⟨g.hom, ⟨(key _).2 ?_, ?_⟩, ?_⟩
    · rw [hg', Category.assoc, e.inv_hom_id_assoc, pullback.lift_snd]
    · rw [hg', Category.assoc, e.inv_hom_id_assoc, pullback.lift_fst]
    · rintro χ ⟨h1, h2⟩
      have h3 : spMap χ = spMap g.hom := by
        rw [hg', Iso.eq_comp_inv]
        refine pullback.hom_ext ?_ ?_
        · rw [pullback.lift_fst, Category.assoc]; exact h2
        · rw [pullback.lift_snd, Category.assoc]; exact (key _).1 h1
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h3)

end GlobalTheory.HeckeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFunctionOfSmoothLocalDescentReduced
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.SmoothLocalDescent

theorem eq_of_forall_geom {R : Type} [CommRing R] [_root_.IsReduced R] (a b : R)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ : R →+* k), χ a = χ b) : a = b := by
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  have := h (AlgebraicClosure J.ResidueField)
    ((algebraMap J.ResidueField _).comp (algebraMap R J.ResidueField))
  rw [← sub_eq_zero, ← map_sub, RingHom.comp_apply, map_eq_zero,
    Ideal.algebraMap_residueField_eq_zero] at this
  exact this

theorem exists_factor_pi {J : Type} [Fintype J] [DecidableEq J] (A : J → Type)
    [∀ i, CommRing (A i)] {k : Type} [CommRing k] [IsDomain k] (χ : (∀ i, A i) →+* k) :
    ∃ (i : J) (ψ : A i →+* k), ∀ x, χ x = ψ (x i) := by
  first
  | exact @_root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection
  | exact _root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection
  | (apply _root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection <;> assumption)
  | (intros; apply _root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection ..)

open scoped TensorProduct in

theorem exists_lift_geom (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Module.FaithfullyFlat R S] (k : Type) [Field k] [IsAlgClosed k]
    (χ : R →+* k) : ∃ χ' : S →+* k, χ'.comp (algebraMap R S) = χ := by
  letI : Algebra R k := χ.toAlgebra
  haveI : Nontrivial (k ⊗[R] S) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[R] S)
  letI : Field ((k ⊗[R] S) ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (k ⊗[R] S) := inferInstance
  haveI : Module.Finite k ((k ⊗[R] S) ⧸ m) := finite_of_finite_type_of_isJacobsonRing k _
  let g : ((k ⊗[R] S) ⧸ m) →ₐ[k] k := IsAlgClosed.lift
  refine ⟨g.toRingHom.comp ((Ideal.Quotient.mk m).comp
    (Algebra.TensorProduct.includeRight (R := R) (A := k) (B := S)).toRingHom), ?_⟩
  ext x
  have e : (1 : k) ⊗ₜ[R] algebraMap R S x = algebraMap k (k ⊗[R] S) (χ x) := by
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, _root_.mul_one]
    rfl
  change g (Ideal.Quotient.mk m ((1 : k) ⊗ₜ[R] algebraMap R S x)) = χ x
  rw [e]
  exact g.commutes (χ x)

open scoped TensorProduct in

theorem exists_preimage_of_geom (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [_root_.IsReduced R] [Algebra.Smooth R S] [Module.FaithfullyFlat R S] (w : S)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ₁ χ₂ : S →+* k),
      χ₁.comp (algebraMap R S) = χ₂.comp (algebraMap R S) → χ₁ w = χ₂ w) :
    ∃ u : R, algebraMap R S u = w := by
  haveI := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced R S
  haveI := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced S (S ⊗[R] S)
  have key : w ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] w := by
    refine eq_of_forall_geom _ _ fun k _ _ χ => ?_
    refine h k (χ.comp Algebra.TensorProduct.includeLeftRingHom)
      (χ.comp (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom) ?_
    ext x
    change χ (algebraMap R S x ⊗ₜ[R] (1 : S)) = χ ((1 : S) ⊗ₜ[R] algebraMap R S x)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  exact (Algebra.IsEffective.of_faithfullyFlat R S w).1 (by
    rw [Algebra.TensorProduct.includeLeftSubRight_apply, key, sub_self])

end GlobalTheory.SmoothLocalDescent

namespace GlobalTheory.SmoothLocalDescent

theorem exists_of_finite_cover (K B : Type) [CommRing K] [CommRing B] [Algebra K B]
    [_root_.IsReduced B]
    (F : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω], (B →ₐ[K] Ω) → Ω)
    {J : Type} [Fintype J] [DecidableEq J] (A : J → Type) [∀ i, CommRing (A i)]
    [∀ i, Algebra B (A i)] [∀ i, Algebra K (A i)] [∀ i, IsScalarTower K B (A i)]
    [∀ i, Algebra.Smooth B (A i)] (a : ∀ i, A i)
    (hcov : ∀ q : PrimeSpectrum B, ∃ i, q ∈ Set.range (PrimeSpectrum.comap (algebraMap B (A i))))
    (hval : ∀ i (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ' : A i →ₐ[K] Ω),
      χ' (a i) = F Ω (χ'.comp (IsScalarTower.toAlgHom K B (A i)))) :
    ∃ b : B, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ : B →ₐ[K] Ω), χ b = F Ω χ := by
  haveI : Algebra.Smooth B (∀ i, A i) := ⟨inferInstance, inferInstance⟩
  haveI : Module.Flat B (∀ i, A i) := inferInstance
  haveI : Module.FaithfullyFlat B (∀ i, A i) := by
    refine Module.FaithfullyFlat.of_comap_surjective fun p => ?_
    obtain ⟨i, Q, hQ⟩ := hcov p
    refine ⟨PrimeSpectrum.comap (Pi.evalRingHom A i) Q, ?_⟩
    rw [← hQ]
    rfl

  have key : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ' : (∀ i, A i) →+* Ω),
      (∀ x : K, χ' (algebraMap B (∀ i, A i) (algebraMap K B x)) = algebraMap K Ω x) →
      ∃ ρ : B →ₐ[K] Ω, (∀ y, ρ y = χ' (algebraMap B (∀ i, A i) y)) ∧ χ' a = F Ω ρ := by
    intro Ω _ _ _ χ' hK
    obtain ⟨i, ψ, hψ⟩ := exists_factor_pi A χ'
    have hB : ∀ y, ψ (algebraMap B (A i) y) = χ' (algebraMap B (∀ i, A i) y) := fun y => by
      rw [hψ]; rfl
    have hc : ∀ x : K, ψ (algebraMap K (A i) x) = algebraMap K Ω x := fun x => by
      rw [IsScalarTower.algebraMap_apply K B (A i), hB, hK]
    let ψa : A i →ₐ[K] Ω := { ψ with commutes' := hc }
    refine ⟨ψa.comp (IsScalarTower.toAlgHom K B (A i)), fun y => hB y, ?_⟩
    rw [hψ]
    exact hval i Ω ψa
  obtain ⟨b, hb⟩ := exists_preimage_of_geom B (∀ i, A i) a fun k _ _ χ₁ χ₂ h12 => by
    letI : Algebra K k := (χ₁.comp ((algebraMap B (∀ i, A i)).comp (algebraMap K B))).toAlgebra
    have h12' : ∀ y, χ₁ (algebraMap B (∀ i, A i) y) = χ₂ (algebraMap B (∀ i, A i) y) :=
      fun y => RingHom.congr_fun h12 y
    obtain ⟨ρ₁, hρ₁, e₁⟩ := key k χ₁ fun x => rfl
    obtain ⟨ρ₂, hρ₂, e₂⟩ := key k χ₂ fun x => (h12' _).symm
    have : ρ₁ = ρ₂ := AlgHom.ext fun y => by rw [hρ₁, hρ₂, h12']
    rw [e₁, e₂, this]
  refine ⟨b, fun Ω _ _ _ χ => ?_⟩
  obtain ⟨χ', hχ'⟩ := exists_lift_geom B (∀ i, A i) Ω χ.toRingHom
  have hχ'y : ∀ y, χ' (algebraMap B (∀ i, A i) y) = χ y := fun y => RingHom.congr_fun hχ' y
  obtain ⟨ρ, hρ, e⟩ := key Ω χ' fun x => by rw [hχ'y]; exact χ.commutes x
  have : ρ = χ := AlgHom.ext fun y => by rw [hρ, hχ'y]
  rw [← this, ← e, ← hb, hρ]

end GlobalTheory.SmoothLocalDescent

namespace GlobalTheory.SmoothLocalDescent

theorem exists_of_smooth_locally : ∀ (K B : Type) [CommRing K] [CommRing B] [Algebra K B] [IsReduced B] (F : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω], (B →ₐ[K] Ω) → Ω), (∀ q : PrimeSpectrum B, ∃ (B' : Type) (_ : CommRing B') (_ : Algebra B B') (_ : Algebra K B') (_ : IsScalarTower K B B') (b' : B'), Algebra.Smooth B B' ∧ q ∈ Set.range (PrimeSpectrum.comap (algebraMap B B')) ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ' : B' →ₐ[K] Ω), χ' b' = F Ω (χ'.comp (IsScalarTower.toAlgHom K B B'))) → ∃ b : B, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ : B →ₐ[K] Ω), χ b = F Ω χ := by
  intro K B _ _ _ _ F h
  choose B' iR iB iK iT b' hsm hq hval using h
  letI : ∀ q, CommRing (B' q) := iR
  letI : ∀ q, Algebra B (B' q) := iB
  letI : ∀ q, Algebra K (B' q) := iK
  haveI : ∀ q, IsScalarTower K B (B' q) := iT
  haveI : ∀ q, Algebra.Smooth B (B' q) := hsm
  let U : PrimeSpectrum B → Set (PrimeSpectrum B) := fun q =>
    Set.range (PrimeSpectrum.comap (algebraMap B (B' q)))
  have hopen : ∀ q, IsOpen (U q) := fun q => by
    have := PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
      (R := B) (S := B' q) _ isOpen_univ
    rwa [Set.image_univ] at this
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hopen
    (fun q _ => Set.mem_iUnion.2 ⟨q, hq q⟩)
  classical
  exact exists_of_finite_cover K B F (J := t) (fun i => B' i.1) (fun i => b' i.1)
    (fun q => by
      obtain ⟨i, hi, hqi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ q))
      exact ⟨⟨i, hi⟩, hqi⟩)
    (fun i => hval i.1)

end GlobalTheory.SmoothLocalDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsRigIsoOfBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

noncomputable section

namespace GlobalTheory.RigIsoDescent

section General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A}

theorem exists_isRigIso_of_gen {Y : Scheme.{0}} {x x' : Y ⟶ S} {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left}
    {k : ℤ} (hΨ : IsPointed A Ψ) (t : LB.Gen (isoLB A L Ψ k)) (ht : t.IsGen) : ∃ β, IsRigIso A L Ψ k β := by
  obtain ⟨β, hβ, hc⟩ := DVR.exists_normalized_to L.isLB _ _ t ht (fst (Over.mk x) A).left
    (ptSecT A (1 : Over.mk x ⟶ A)).left ThetaReal.NormMul.ptSec_fst _ _
    (LB.mulGen L.L (Y := Y) _ _ _ _ (rigT A L.L L.rig (Over.mk x) k) (rigT A L.L L.rig (Over.mk x') (-1)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (ThetaReal.NormMul.rigT_isGen L.rigGen _) (ThetaReal.NormMul.rigT_isGen L.rigGen _))
    (by
      rw [DVR.fsum_sumElim, DVR.fsum, DVR.fsum, DVR.fsum, Fin.sum_univ_two, Fin.sum_univ_one, Fin.sum_univ_one]
      refine congrArg₂ (· + ·) (congrArg (Finsupp.single · k) ThetaReal.NormMul.ptSec_snd)
        (congrArg (Finsupp.single · (-1 : ℤ)) ?_)
      refine (Category.assoc _ _ _).symm.trans ?_
      rw [hΨ.2]
      exact ThetaReal.NormMul.ptSec_snd)
  exact ⟨β, hΨ, hβ, hc⟩

theorem exists_gen_of_field (hA : IsAbelianScheme A) {K K' : Type} [Field K] [Field K'] (φ : K →+* K')
    {x x' : Sp K ⟶ S} {w w' : Sp K' ⟶ S} {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left}
    {Ψ' : (Over.mk w ⊗ A).left ⟶ (Over.mk w' ⊗ A).left} {k : ℤ} (hw : w = spMap φ ≫ x)
    (π : (Over.mk w ⊗ A).left ⟶ (Over.mk x ⊗ A).left)
    (h₁ : π ≫ (fst (Over.mk x) A).left = (fst (Over.mk w) A).left ≫ spMap φ)
    (h₂ : π ≫ (snd (Over.mk x) A).left = (snd (Over.mk w) A).left)
    (h₃ : π ≫ Ψ ≫ (snd (Over.mk x') A).left = Ψ' ≫ (snd (Over.mk w') A).left)
    (t : LB.Gen (isoLB A L Ψ' k)) (ht : t.IsGen) : ∃ u : LB.Gen (isoLB A L Ψ k), u.IsGen := by
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected
  let p : (Over.mk x ⊗ A).left ⟶ Sp K := (fst (Over.mk x) A).left
  have H₀ : IsPullback (snd (Over.mk x) A).left p A.hom x := (IsPullback.of_hasPullback x A.hom).flip
  have H₁ : IsPullback (snd (Over.mk w) A).left (fst (Over.mk w) A).left A.hom w :=
    (IsPullback.of_hasPullback w A.hom).flip
  have : IsProper p := MorphismProperty.of_isPullback (P := @IsProper) H₀ inferInstance
  have : GeometricallyIntegral p := MorphismProperty.of_isPullback (P := @GeometricallyIntegral) H₀ inferInstance
  have H : IsPullback π (fst (Over.mk w) A).left p (spMap φ) :=
    IsPullback.of_right (by rw [h₂, ← hw]; exact H₁) h₁ H₀
  obtain ⟨c, hc⟩ := gen_chartPull (chartPullOut L.L (isoφ A Ψ) ![k, -1] π (isoφ A Ψ') fun i => by
    fin_cases i
    exacts [h₂.symm, h₃.symm]) t ht
  exact FieldTriv.exists_gen_of_isPullback φ p π _ H (LB.isLB_linComb L.isLB _ _) c hc

end General

theorem eSec_fst {B B' : Scheme.{0}} (u : B' ⟶ B) (A : Over B) [GrpObj A] :
    eSec ((Over.pullback u).obj A) ≫ pullback.fst A.hom u = u ≫ eSec A := by
  rw [eSec, eSec, Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
    ← pullback.condition_assoc]
  exact (pullback.lift_fst _ _ _).trans (by simp)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem ptSec_swap {K : Type} [CommRing K] (x : Sp K ⟶ Xo.X) :
    (ptSecT Xo.univ.t.G (1 : Over.mk x ⟶ Xo.univ.t.G)).left ≫ (swap x).hom = eSec (Fib Xo x) := by
  refine pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (swap_hom_fst x)).trans
      (ThetaReal.NormMul.ptSec_snd.trans (eSec_fst x _).symm))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (swap_hom_snd x)).trans
      (ThetaReal.NormMul.ptSec_fst.trans (Over.w η[Fib Xo x]).symm))

theorem isPointed_of_isMonHom {K : Type} [CommRing K] {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x')
    (hf : IsMonHom f) : IsPointed Xo.univ.t.G (conj x x' f.left) := by
  refine ⟨(over_iff _).2 (Over.w f), ?_⟩
  have e : eSec (Fib Xo x) ≫ f.left = eSec (Fib Xo x') := congrArg (fun q => q.left) hf.one_hom
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (ptSec_swap x)).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans ?_)))
  exact (Iso.comp_inv_eq _).2 (ptSec_swap x').symm

theorem exists_isRigIso_of_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo w ⟶ Fib Xo w') (k : ℤ), IsBC φ f g → IsMonHom f → (∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj w w' g.left) k β) → ∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) k β := by
  rintro E _ _ _ H Dw l Xo K L _ _ φ x x' w w' f g k ⟨hw, hw', hbc⟩ hf ⟨β, -, hβ, -⟩
  have mk : ∀ {y : Sp K ⟶ Xo.X} {v : Sp L ⟶ Xo.X}, v = spMap φ ≫ y →
      ∃ π : pullback Xo.univ.t.G.hom v ⟶ pullback Xo.univ.t.G.hom y,
        π ≫ pullback.fst _ _ = pullback.fst _ _ ∧ π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ := fun h =>
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap φ) (by rw [Category.assoc, ← h, pullback.condition]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨π, a₁, a₂⟩ := mk hw
  obtain ⟨π', b₁, b₂⟩ := mk hw'
  have e := hbc π π' a₁ a₂ b₁ b₂
  have hp := isPointed_of_isMonHom f hf
  obtain ⟨u, hu⟩ := exists_gen_of_field (L := Xo.univ.t.PP) (Ψ := conj x x' f.left) (UnivPol.pol Xo).isAb φ hw
    ((swap w).hom ≫ π ≫ (swap x).inv)
    (by rw [Category.assoc, Category.assoc, swap_inv_fst, a₂, swap_hom_snd_assoc])
    (by rw [Category.assoc, Category.assoc, swap_inv_snd, a₁, swap_hom_fst])
    (by
      simp only [conj_apply, Category.assoc, Iso.inv_hom_id_assoc, swap_inv_snd]
      rw [← reassoc_of% e, b₁]) β hβ
  exact exists_isRigIso_of_gen hp u hu

end GlobalTheory.RigIsoDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalIsometryOfTraceSimilitudeSq
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.TraceSimilitude

theorem trace_natSq_mul {E : Type} [Field E] [NumberField E] (N : ℕ) (x : E) :
    Algebra.trace ℚ E ((N : E) ^ 2 * x) = (N : ℚ) ^ 2 * Algebra.trace ℚ E x := by
  have h : ((N : E) ^ 2) = algebraMap ℚ E ((N : ℚ) ^ 2) := by simp
  rw [h, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem exists_gl_of_trace_similitude : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ), 0 < N → (∀ τ : E →+* ℂ, ‖τ X.ξ0‖ = ‖τ X'.ξ0‖) → ∀ (gam : X.Λ →ₗ[𝓞 E] X'.Λ), (∀ u v : X.Λ, Algebra.trace ℚ E (-X'.ξ0 * herm X'.Gm (gam u : Fin r → E) (gam v : Fin r → E)) = (N : ℚ) ^ 2 * Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (u : Fin r → E) (v : Fin r → E))) → (∀ w : X'.Λ, ∃ v, gam v = (N ^ 2) • w) → ∃ (a : GL (Fin r) E) (ε : E), (ε = 1 ∨ ε = -1) ∧ X'.ξ0 = ε * X.ξ0 ∧ (∀ v : X.Λ, (N : E) • ((a : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E)) = (gam v : Fin r → E)) ∧ (∀ w ∈ X'.Λ, (N : E) • (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) ∈ X.Λ) ∧ ∀ u v, herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = ε * herm X.Gm u v := by
  classical
  intro E _ _ _ r X X' N hN hn gam htr hsurj
  have hs : Submodule.span E (Set.range X.Λ.subtype) = ⊤ := by
    rw [← X.Λ_span]; congr 1; exact Subtype.range_coe
  have hs' : Submodule.span E (Set.range X'.Λ.subtype) = ⊤ := by
    rw [← X'.Λ_span]; congr 1; exact Subtype.range_coe
  obtain ⟨A, hA⟩ := FrameFibre.exists_matrix X.Λ.subtype X.Λ.injective_subtype hs
    (X'.Λ.subtype ∘ₗ gam)
  have hA' : ∀ v : X.Λ, A *ᵥ (v : Fin r → E) = (gam v : Fin r → E) := hA
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hcoe : ∀ w : X'.Λ, (((N ^ 2) • w : X'.Λ) : Fin r → E) = ((N : E) ^ 2) • (w : Fin r → E) := by
    intro w
    rw [Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul E]
    push_cast; rfl
  have hsurjA : Function.Surjective (Matrix.toLin' A) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs', Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    obtain ⟨v, hv⟩ := hsurj w
    refine ⟨((N : E) ^ 2)⁻¹ • (v : Fin r → E), ?_⟩
    rw [map_smul, Matrix.toLin'_apply, hA', hv, hcoe, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hN0), one_smul]
    rfl
  have hU : IsUnit A := Matrix.mulVec_surjective_iff_isUnit.1 hsurjA
  set U := hU.unit with hUdef
  have hUA : (U : Matrix (Fin r) (Fin r) E) = A := hU.unit_spec
  let a : GL (Fin r) E :=
    ⟨(N : E)⁻¹ • A, (N : E) • ((U⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E),
      by rw [smul_mul_smul_comm, inv_mul_cancel₀ hN0, one_smul, ← hUA, U.mul_inv],
      by rw [smul_mul_smul_comm, mul_inv_cancel₀ hN0, one_smul, ← hUA, U.inv_mul]⟩
  have ha : (a : Matrix (Fin r) (Fin r) E) = (N : E)⁻¹ • A := rfl
  have hai : ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) =
      (N : E) • ((U⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := rfl
  obtain ⟨ε, hε, hξ⟩ : ∃ ε : E, (ε = 1 ∨ ε = -1) ∧ X'.ξ0 = ε * X.ξ0 := by
    rcases TraceIsometry.eq_or_eq_neg_of_norm_eq X.ξ0_im X'.ξ0_im hn with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, _root_.one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_mul]⟩
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> ring
  have h1 : cc (1 : E) = 1 := map_one (IsCMField.complexConj E)
  have key : ∀ u v : X.Λ, herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E)) =
      (N : E) ^ 2 * ε * herm X.Gm u v := by
    intro u v
    have h0 : -X'.ξ0 * herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E)) -
        (N : E) ^ 2 * (-X.ξ0 * herm X.Gm u v) = 0 := by
      refine FrameFibre.eq_zero_of_trace _ fun b => ?_
      have h2 := htr (b • u) v
      have h3 : ((b • u : X.Λ) : Fin r → E) = (b : E) • (u : Fin r → E) := rfl
      have h4 := FrameFibre.herm_smul_smul X'.Gm (b : E) 1 (A *ᵥ (u : Fin r → E))
        (A *ᵥ (v : Fin r → E))
      have h5 := FrameFibre.herm_smul_smul X.Gm (b : E) 1 (u : Fin r → E) (v : Fin r → E)
      rw [one_smul, h1, _root_.mul_one] at h4 h5
      rw [← hA', ← hA', h3, Matrix.mulVec_smul, h4, h5] at h2
      have e1 : (b : E) * (-X'.ξ0 * herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E))) =
          -X'.ξ0 * ((b : E) * herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E))) := by ring
      have e2 : (b : E) * ((N : E) ^ 2 * (-X.ξ0 * herm X.Gm u v)) =
          (N : E) ^ 2 * (-X.ξ0 * ((b : E) * herm X.Gm u v)) := by ring
      rw [mul_sub, map_sub, e1, e2, trace_natSq_mul, h2, sub_self]
    rw [hξ] at h0
    apply mul_left_cancel₀ X.ξ0_ne
    linear_combination (-ε) * h0 -
      (X.ξ0 * herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E))) * hε2
  have keyA : ∀ x y : Fin r → E, herm X'.Gm (A *ᵥ x) (A *ᵥ y) = (N : E) ^ 2 * ε * herm X.Gm x y := by
    intro x y
    obtain ⟨c, v, hc, hv⟩ := FrameFibre.exists_smul_eq X.Λ.subtype hs x
    obtain ⟨d, w, hd, hw⟩ := FrameFibre.exists_smul_eq X.Λ.subtype hs y
    have h2 := key v w
    rw [Submodule.subtype_apply] at hv hw
    rw [← hv, ← hw, Matrix.mulVec_smul, Matrix.mulVec_smul, FrameFibre.herm_smul_smul,
      FrameFibre.herm_smul_smul] at h2
    have hc' : (c : E) ≠ 0 := by simpa using hc
    have hd' : cc (d : E) ≠ 0 := (map_ne_zero (IsCMField.complexConj E)).2 (by simpa using hd)
    apply mul_left_cancel₀ (mul_ne_zero hc' hd')
    linear_combination h2
  refine ⟨a, ε, hε, hξ, fun v => ?_, fun w hw => ?_, fun x y => ?_⟩
  · rw [ha, Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hN0, one_smul, hA']
  · obtain ⟨v, hv⟩ := hsurj ⟨w, hw⟩
    have h3 : (U : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E) = (N : E) ^ 2 • w := by
      rw [hUA, hA', hv, hcoe]
    have h2 : ((U⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((N : E) ^ 2 • w) = v := by
      rw [← h3, Matrix.mulVec_mulVec, U.inv_mul, Matrix.one_mulVec]
    rw [hai, Matrix.smul_mulVec, smul_smul, ← pow_two, ← Matrix.mulVec_smul, h2]
    exact v.2
  · have hcc : cc ((N : E)⁻¹) = (N : E)⁻¹ :=
      (map_inv₀ (IsCMField.complexConj E) _).trans (by rw [map_natCast])
    rw [ha, Matrix.smul_mulVec, Matrix.smul_mulVec, FrameFibre.herm_smul_smul, hcc,
      keyA]
    field_simp

end GlobalTheory.TraceSimilitude
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalPointThetaGeneratorNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaNZ

theorem exists_ratPt_sv_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x₁ : Sp Ω ⟶ Xo.X} {s : LB.Sec (PPx x₁)}, IsThGen x₁ s → ∃ w : Sp Ω ⟶ Gx x₁, w ≫ (fst (Over.mk x₁) Xo.univ.t.G).left = 𝟙 _ ∧ ∀ (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s w z J ≠ 0 := by
  intro E _ _ _ H Dw l Xo Ω _ _ x₁ s hs
  have hnz := GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo Ω x₁ s hs
  obtain ⟨q, i, -, hqi⟩ := hnz (IsLocalRing.closedPoint Ω)
  have := Xo.univ.t.semi.smooth
  have : Smooth (fst (Over.mk x₁) Xo.univ.t.G).left := by
    show Smooth (pullback.fst x₁ Xo.univ.t.G.hom)
    infer_instance
  have : JacobsonSpace ↥(Over.mk x₁).left := inferInstanceAs (JacobsonSpace (PrimeSpectrum Ω))
  have : JacobsonSpace ↥(Gx x₁) := LocallyOfFiniteType.jacobsonSpace (fst (Over.mk x₁) Xo.univ.t.G).left
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints ⟨q, hqi⟩
    ((Gx x₁).basicOpen (s.f i)).isOpen.isLocallyClosed
  have hyc' : IsClosed ({y} : Set (Gx x₁)) := hyc
  refine ⟨pointOfClosedPoint (fst (Over.mk x₁) Xo.univ.t.G).left y hyc',
    pointOfClosedPoint_comp _ y hyc', fun z J hJ => ?_⟩
  set w := pointOfClosedPoint (fst (Over.mk x₁) Xo.univ.t.G).left y hyc'
  have hwz : w z = y := pointOfClosedPoint_apply _ y hyc' z
  let φ : Fin 1 → (Gx x₁ ⟶ Xo.univ.t.G.left) := fun _ => (snd (Over.mk x₁) Xo.univ.t.G).left
  have hi : w z ∈ LB.wchart Xo.univ.t.PP.L φ i := by
    rw [hwz]; exact Scheme.basicOpen_le _ _ hy
  have hj := hJ.mem φ w
  show sval s w z J ≠ 0
  rw [sval_of s w z J (fun k => J (w ≫ φ k)) (fun k => rfl), sec_trans s w z hj hi]
  have hU : IsUnit (gs w z (LB.wchart Xo.univ.t.PP.L φ i) (s.f i)) := by
    have hb : z ∈ (Sp Ω).basicOpen ((w.app _).hom (s.f i)) := by
      rw [← Scheme.preimage_basicOpen]
      show w z ∈ (Gx x₁).basicOpen (s.f i)
      rw [hwz]; exact hy
    convert ((Sp Ω).mem_basicOpen _ z hi).1 hb using 1
    exact gs_eq w z _ hi _
  exact ((Units.isUnit _).mul hU).ne_zero

end GlobalTheory.ThetaNZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltration
section
namespace GlobalTheory

theorem geometricLemma_of_filtration :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemmaFiltration →
      GlobalTheory.Published.GeometricLemma := by
  intro hB hF k _ _ _ _
  exact ⟨hF k, GlobalTheory.T.geometricLemma_cell_semisimplification_GL hB k⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HarishChandraCharactersOfInputsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harish_chandra_characters_of_inputs : GlobalTheory.Published.IrreducibleUnitaryAdmissible → GlobalTheory.Published.KFiniteCoefficientsAnalytic → GlobalTheory.Published.DiscreteSeriesSU → GlobalTheory.Published.CharacterRegularityFiniteLength → GlobalTheory.Published.DiscreteSeriesCharacterSU → GlobalTheory.Published.WeylIntegrationSum → GlobalTheory.Published.InducedCharacterVanishing → GlobalTheory.Published.InducedAdmissibleFiniteLength → GlobalTheory.Published.HarishChandraCharacters := by
  first | exact @GlobalTheory.HarishChandraCharacterSU.harishChandraCharacters_SU_of_hypotheses | exact GlobalTheory.HarishChandraCharacterSU.harishChandraCharacters_SU_of_hypotheses | (intros; apply GlobalTheory.HarishChandraCharacterSU.harishChandraCharacters_SU_of_hypotheses <;> assumption)
end

