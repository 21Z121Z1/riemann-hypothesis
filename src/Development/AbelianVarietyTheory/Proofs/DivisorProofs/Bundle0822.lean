import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0800
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0801
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0814
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquidistributedIdealClassesOfHilbertClassFieldJ
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
open GlobalTheory.Published
open scoped IntermediateField

noncomputable section

namespace GlobalTheory.EquidistJ

theorem card_ext_mul_finrank (L M : IntermediateField ℚ ℂ) (hML : M ≤ L) [FiniteDimensional ℚ L] (σ : ℂ ≃+* ℂ) :
    Nat.card {τ : L →+* ℂ // ∀ x : L, (x : ℂ) ∈ M → τ x = σ x} * Module.finrank ℚ M = Module.finrank ℚ L := by
  let E := IntermediateField.extendScalars hML
  have hEL : Module.finrank ℚ E = Module.finrank ℚ L := rfl
  have hEpos : 0 < Module.finrank ℚ E := by rw [hEL]; exact Module.finrank_pos
  haveI : FiniteDimensional ℚ E := Module.finite_of_finrank_pos hEpos
  haveI : FiniteDimensional M E := FiniteDimensional.right ℚ M E
  let ι : L →+* E :=
    { toFun := fun x => ⟨x.1, x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  let ι' : E →+* L :=
    { toFun := fun x => ⟨x.1, x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  let e : {τ : L →+* ℂ // ∀ x : L, (x : ℂ) ∈ M → τ x = σ x} ≃ (E →ₐ[M] ℂ) :=
    { toFun := fun τ =>
        { toRingHom := σ.symm.toRingHom.comp (τ.1.comp ι')
          commutes' := fun m => by
            change σ.symm (τ.1 ⟨m.1, hML m.2⟩) = m.1
            rw [τ.2 ⟨m.1, hML m.2⟩ m.2]
            exact σ.symm_apply_apply _ }
      invFun := fun f => ⟨σ.toRingHom.comp (f.toRingHom.comp ι), fun x hx => by
          change σ (f ⟨x.1, x.2⟩) = σ x.1
          congr 1
          exact f.commutes ⟨x.1, hx⟩⟩
      left_inv := fun τ => Subtype.ext (RingHom.ext fun x => by
          change σ (σ.symm (τ.1 ⟨x.1, x.2⟩)) = τ.1 x
          rw [σ.apply_symm_apply])
      right_inv := fun f => AlgHom.ext fun x => by
          change σ.symm (σ (f ⟨x.1, x.2⟩)) = f x
          rw [σ.symm_apply_apply] }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, AlgHom.card M E ℂ, mul_comm,
    Module.finrank_mul_finrank ℚ M E, hEL]

theorem equidistributed_of_hilbertClassFieldJ : ∀ (hH : GlobalTheory.Published.HilbertClassFieldJ) {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (φK : K →+* ℂ) (ΛK : PeriodPair) (hΛ : IsLatOf φK 1 ΛK) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h𝔞 : ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∃ Λ : PeriodPair, IsLatOf φK (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) Λ ∧ jLat Λ = σ (jLat ΛK)), Equidistributed φK (jLat ΛK) 𝔞 := by
  intro hH K _ _ _ h2 φK ΛK hΛ 𝔞 h𝔞
  letI : Algebra K ℂ := φK.toAlgebra
  have hj : ∀ Λ : PeriodPair, jLat Λ = (latticeCurve Λ).j := fun Λ => by rw [latticeCurve_j_eq]; rfl
  have hlat : ∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : PeriodPair),
      IsLatOf φK (𝔟 : FractionalIdeal (𝓞 K)⁰ K) Λ → IsIdealLattice 𝔟 Λ := fun _ _ h => h
  obtain ⟨-, hfin, hcl, -, hrange⟩ := hH K h2 ΛK (hlat 1 ΛK hΛ)
  set H : IntermediateField K ℂ := K⟮(latticeCurve ΛK).j⟯ with hHdef
  have hpos : 0 < Module.finrank K H := hfin ▸ Fintype.card_pos
  haveI : FiniteDimensional K H := Module.finite_of_finrank_pos hpos
  have hj0 : (latticeCurve ΛK).j ∈ H := IntermediateField.mem_adjoin_simple_self K _
  have hj0' : jLat ΛK ∈ H := by rw [hj]; exact hj0
  have halg : IsAlgebraic ℚ (jLat ΛK) := by
    rw [hj]
    exact (IntermediateField.isAlgebraic_iff.1
      (Algebra.IsAlgebraic.isAlgebraic (⟨_, hj0⟩ : H))).restrictScalars ℚ
  have hclass : ∀ σ σ' : ℂ ≃+* ℂ, Fixes φK σ → Fixes φK σ' →
      (ClassGroup.mk K (𝔞 σ) = ClassGroup.mk K (𝔞 σ') ↔ σ (jLat ΛK) = σ' (jLat ΛK)) := by
    intro σ σ' hσ hσ'
    obtain ⟨Λ, hl, hjl⟩ := h𝔞 σ hσ
    obtain ⟨Λ', hl', hjl'⟩ := h𝔞 σ' hσ'
    rw [← hjl, ← hjl', hj, hj]
    exact (hcl _ _ Λ Λ' (hlat _ _ hl) (hlat _ _ hl')).symm
  refine ⟨halg, hclass, ?_⟩
  intro L hLf hLg hKL hjL C
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective C
  obtain ⟨Lb, hLb⟩ := exists_isIdealLattice h2 (FractionalIdeal.mk0 K I)
  have hinv : (latticeCurve Lb).j ∈ idealInvariants K := ⟨_, Lb, hLb, rfl⟩
  rw [← hrange] at hinv
  obtain ⟨g, hg⟩ := hinv
  haveI : NumberField H := NumberField.of_module_finite K H
  haveI : Countable H := (Module.finBasis ℚ H).equivFun.injective.countable
  obtain ⟨σC, hσC⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq H.val.toRingHom
    (H.val.toRingHom.comp g.toAlgHom.toRingHom)
  have hfixC : Fixes φK σC := fun x => by
    have := hσC (algebraMap K H x)
    exact (by simpa using this : σC (algebraMap K ℂ x) = algebraMap K ℂ x)
  have hσCj : σC (jLat ΛK) = jLat Lb := by
    have := hσC (IntermediateField.AdjoinSimple.gen K (latticeCurve ΛK).j)
    rw [hj, hj]
    simpa [hg] using this
  have hclC : ClassGroup.mk K (𝔞 σC) = ClassGroup.mk0 I := by
    obtain ⟨Λ, hl, hjl⟩ := h𝔞 σC hfixC
    rw [← ClassGroup.mk_mk0 K]
    refine (hcl _ _ Λ Lb (hlat _ _ hl) hLb).1 ?_
    rw [← hj, hjl, hσCj, hj]
  let L' : IntermediateField K ℂ := L.toSubfield.toIntermediateField hKL
  have hHL : H ≤ L' := IntermediateField.adjoin_simple_le_iff.2 (by rw [← hj]; exact hjL)
  haveI : FiniteDimensional ℚ L := hLf
  haveI : Countable L := (Module.finBasis ℚ L).equivFun.injective.countable
  have hcount := card_ext_mul_finrank L (H.restrictScalars ℚ) (fun x hx => hHL hx) σC
  have hM : Module.finrank ℚ (H.restrictScalars ℚ) = Module.finrank ℚ K * Module.finrank K H := by
    rw [Module.finrank_mul_finrank ℚ K H]
    rfl
  rw [hM, h2, hfin] at hcount
  have hiff : ∀ τ : L →+* ℂ, (∃ σ : ℂ ≃+* ℂ, Fixes φK σ ∧ (∀ x : L, σ (x : ℂ) = τ x) ∧
      ClassGroup.mk K (𝔞 σ) = ClassGroup.mk0 I) ↔ ∀ x : L, (x : ℂ) ∈ H.restrictScalars ℚ → τ x = σC x := by
    intro τ
    constructor
    · rintro ⟨σ, hσ, hστ, hcσ⟩ x hx
      have e : σ (jLat ΛK) = σC (jLat ΛK) := (hclass σ σC hσ hfixC).1 (hcσ.trans hclC.symm)
      rw [hj] at e
      let a : H →ₐ[K] ℂ := ((AlgEquiv.ofRingEquiv (f := σ) hσ).toAlgHom).comp H.val
      let b : H →ₐ[K] ℂ := ((AlgEquiv.ofRingEquiv (f := σC) hfixC).toAlgHom).comp H.val
      have hab : a = b := by
        refine IntermediateField.algHom_ext_of_eq_adjoin K rfl ?_
        rintro y rfl
        exact e
      rw [← hστ x]
      exact DFunLike.congr_fun hab ⟨x, hx⟩
    · intro hτ
      obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq L.val.toRingHom τ
      have hσf : Fixes φK σ := fun x => by
        have h1 := hσ ⟨φK x, hKL x⟩
        have h2 := hτ ⟨φK x, hKL x⟩ (H.algebraMap_mem x)
        have h3 := hfixC x
        exact h1.trans (h2.trans h3)
      refine ⟨σ, hσf, fun x => hσ x, ?_⟩
      refine ((hclass σ σC hσf hfixC).2 ?_).trans hclC
      have h1 := hσ ⟨jLat ΛK, hjL⟩
      have h2 := hτ ⟨jLat ΛK, hjL⟩ hj0'
      exact h1.trans h2
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  linarith

end GlobalTheory.EquidistJ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenProductSectionsIsoStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_open_product_sections_iso : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (U : X.left.affineOpens) (V : Y.left.affineOpens), ∃ (W : (X ⊗ Y).left.affineOpens) (h₁ : W.1 ≤ (fst X Y).left ⁻¹ᵁ U.1) (h₂ : W.1 ≤ (snd X Y).left ⁻¹ᵁ V.1) (i₁ : Sec X.hom U.1 →ₐ[R] Sec (X ⊗ Y).hom W.1) (i₂ : Sec Y.hom V.1 →ₐ[R] Sec (X ⊗ Y).hom W.1), W.1 = (fst X Y).left ⁻¹ᵁ U.1 ⊓ (snd X Y).left ⁻¹ᵁ V.1 ∧ (∀ b, i₁ b = ((fst X Y).left.appLE U.1 W.1 h₁).hom b) ∧ (∀ b, i₂ b = ((snd X Y).left.appLE V.1 W.1 h₂).hom b) ∧ Function.Bijective (Algebra.TensorProduct.productMap i₁ i₂) := by
  first | exact @GlobalTheory.functions_on_product_of_affine_opens | exact GlobalTheory.functions_on_product_of_affine_opens | (intros; apply GlobalTheory.functions_on_product_of_affine_opens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineSpaceMorphismOfCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
noncomputable section

namespace GlobalTheory.HomFixPoint

theorem exists_affine_hom (Rg : Type) [CommRing Rg] (T : Scheme.{0}) (n : ℕ) (t : T ⟶ Sp Rg)
    (x : Fin n → Γ(T, ⊤)) :
    ∃ g : T ⟶ Sp (MvPolynomial (Fin n) Rg), g ≫ affπ Rg n = t ∧ ∀ i, coord g i = x i := by
  let φ : MvPolynomial (Fin n) Rg →+* Γ(T, ⊤) :=
    MvPolynomial.eval₂Hom (t.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of Rg)).inv.hom) x
  have key : ∀ p, (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv p) = φ p := by
    intro p
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply
      (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
      Scheme.toSpecΓ_appTop]
    simp
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_, ?_⟩
  · apply ext_of_isAffine
    refine (Iso.cancel_iso_inv_left (Scheme.ΓSpecIso (CommRingCat.of Rg)) _ _).1 ?_
    ext r
    have n2 : (affπ Rg n).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) =
        (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv (MvPolynomial.C r) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, n2, key]
    simp [φ]
  · intro i
    unfold coord
    rw [key]
    simp [φ]

end GlobalTheory.HomFixPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmCurveTorsionTransportSecondPeriod
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.LatVal.CurveTransport

open GlobalTheory.EllipticCM GlobalTheory.ConjPoint WeierstrassCurve
open GlobalTheory.Idele
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsLatOf IsInvIdealOf)

variable {K : Type} [Field K] [NumberField K]

theorem isLatOf_iff {ι : K →+* ℂ} {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {Λ : PeriodPair} :
    IsLatOf ι 𝔞 Λ ↔ ∀ z, z ∈ Λ.lattice ↔ ∃ x ∈ 𝔞, ι x = z := by
  rw [IsLatOf, Set.ext_iff]
  rfl

theorem isInvIdealOf_inv_smul_one (t : (Af K)ˣ) :
    IsInvIdealOf t (t⁻¹ • (1 : FractionalIdeal (𝓞 K)⁰ K)) := by
  intro x
  rw [← algebraMap_mem_adelicIdeal (GlobalTheory.Idele.smul_ne_zero _ (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0)), ← mem_adelicIdeal_one_iff,
    ← mul_mem_adelicIdeal_smul t⁻¹ 1 ((t : Af K) * algebraMap K _ x), Units.inv_mul_cancel_left]

theorem mulEquiv_inv_mk (t : (Af K)ˣ) {x x' : K}
    (h : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v (((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x) v) ≤ 1) :
    mulEquiv t⁻¹ (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0) rfl
      (Submodule.Quotient.mk x) = Submodule.Quotient.mk x' := by
  rw [mulEquiv_mk_eq_mk_iff_adelic]
  have e : ((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) x - algebraMap K (Af K) x' =
      ((t⁻¹ : (Af K)ˣ) : Af K) * -((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x) := by
    rw [mul_neg, mul_sub, Units.inv_mul_cancel_left]
    ring
  rw [e, mul_mem_adelicIdeal_smul]
  exact neg_mem (mem_adelicIdeal_one_iff.2 h)

theorem exists_curve_torsTransport : ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K],
    Module.finrank ℚ K = 2 → ∀ (ι : K →+* ℂ) (Λ₀ : PeriodPair) (Ω₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 1 Λ₀ →
    Ω₀ ≠ 0 → letI : Algebra K ℂ := ι.toAlgebra;
    ∃ (X : WeierstrassCurve ℂ) (_ : X.IsElliptic)
      (ξ : (ℂ ⧸ GlobalTheory.EllipticCM.idealSub (1 : FractionalIdeal (𝓞 K)⁰ K)) ≃+ X.toAffine.Point),
      GlobalTheory.EllipticCM.IsAnalyticIso ξ ∧ ∀ (σ : ℂ ≃ₐ[K] ℂ) (t : (Af K)ˣ),
        GlobalTheory.EllipticCM.Transports σ t one_ne_zero ξ →
        ∃ (Λ₁ : PeriodPair) (Ω₁ : ℂ), TorsTransport ι σ.toRingEquiv t Λ₀ Λ₁ Ω₀ Ω₁ := by
  intro K _ _ _ _ ι Λ₀ Ω₀ hΛ₀ hΩ₀
  letI : Algebra K ℂ := ι.toAlgebra
  have hAlg : ∀ y : K, algebraMap K ℂ y = ι y := fun _ => rfl
  have hsubIff : ∀ {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {Λ : PeriodPair},
      (IsLatOf ι 𝔞 Λ ↔ ∀ z, z ∈ idealSub 𝔞 ↔ z ∈ Λ.lattice) := fun {𝔞 Λ} => by
    rw [isLatOf_iff]
    exact forall_congr' fun z => by rw [mem_idealSub]; exact Iff.comm
  let M := GlobalTheory.scalePeriods Λ₀ Ω₀ hΩ₀
  have hM : GlobalTheory.IsHomothetic Ω₀ Λ₀ M := GlobalTheory.isHomothetic_scalePeriods Λ₀ Ω₀ hΩ₀
  have hsub : ∀ z, z ∈ idealSub (1 : FractionalIdeal (𝓞 K)⁰ K) ↔ Ω₀ * z ∈ M.lattice := fun z => by
    rw [hM z]; exact hsubIff.1 hΛ₀ z
  obtain ⟨ξ, hξ, hξz⟩ := exists_isAnalyticIso (X := latticeCurve M) (C := 1) (one_smul _ _) hΩ₀ hsub
  refine ⟨latticeCurve M, inferInstance, ξ, hξ, fun σ t ht => ?_⟩
  obtain ⟨η, ⟨hη, hηx⟩, -⟩ := ht
  obtain ⟨L', g2, g3⟩ := GlobalTheory.CMRam.exists_conj_lattice σ.toRingEquiv M
  have h' : (1 : VariableChange ℂ) • (latticeCurve M).map (σ : ℂ →+* ℂ) = latticeCurve L' := by
    rw [one_smul]
    simp [latticeCurve, WeierstrassCurve.map, g2, g3, map_ofNat]
  obtain ⟨α, hα0, hα, hηα⟩ := hη.exists_mul h'
  let Λ₁ := GlobalTheory.scalePeriods L' α⁻¹ (inv_ne_zero hα0)
  have hΛ₁ : GlobalTheory.IsHomothetic α⁻¹ L' Λ₁ := GlobalTheory.isHomothetic_scalePeriods L' α⁻¹ (inv_ne_zero hα0)
  have hΛ₁' : GlobalTheory.IsHomothetic α Λ₁ L' := fun z => by
    rw [← hΛ₁ (α * z), ← mul_assoc, inv_mul_cancel₀ hα0, one_mul]
  have hlat1 : IsLatOf ι (t⁻¹ • 1) Λ₁ := hsubIff.2 fun z => by rw [hα, hΛ₁' z]
  refine ⟨Λ₁, α, hΩ₀, hα0, fun x => σ.commutes x, hΛ₀, ⟨_, isInvIdealOf_inv_smul_one t, hlat1⟩, ?_, ?_, ?_⟩
  · rw [div_eq_inv_mul, ← hM.g₂_eq, ← g2, hΛ₁'.g₂_eq, div_eq_inv_mul]
  · rw [div_eq_inv_mul, ← hM.g₃_eq, ← g3, hΛ₁'.g₃_eq, div_eq_inv_mul]
  · intro x x' hx hint
    have e := hηx (Submodule.Quotient.mk x)
    rw [mulEquiv_inv_mk t hint, torsionIncl_mk, torsionIncl_mk, hξz, hηα, hAlg, hAlg] at e
    have hxM : Ω₀ * ι x ∉ M.lattice := fun h => hx ((hM _).1 h)
    rw [latticePoint_of_notMem M hxM] at e
    have hx' : α * ι x' ∉ L'.lattice := by
      intro h
      rw [latticePoint_of_mem L' h, map_zero, variableChangePoint_some] at e
      exact Affine.Point.some_ne_zero _ e
    rw [latticePoint_of_notMem L' hx', variableChangePoint_some, variableChangePoint_some] at e
    change Affine.Point.some _ _ _ = _ at e
    rw [Affine.Point.some.injEq] at e
    simp [VariableChange.one_def] at e
    obtain ⟨e1, e2⟩ := e
    refine ⟨?_, ?_⟩
    · rw [div_eq_inv_mul, ← hM.weierstrassP_mul, div_eq_inv_mul, ← hΛ₁'.weierstrassP_mul]
      exact e1
    · rw [div_eq_inv_mul, ← hM.derivWeierstrassP_mul, div_eq_inv_mul, ← hΛ₁'.derivWeierstrassP_mul]
      rw [map_ofNat σ 2, div_left_inj' two_ne_zero] at e2
      exact e2

end GlobalTheory.LatVal.CurveTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonHermitianGramDetTwoVectorsNeStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_hermitianGramDetTwoVectors_ne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ w : Fin M → E, gram2E σ J x w ≠ 0 ∧ gram2E σ J w y ≠ 0 := by
  first | exact @GlobalTheory.exists_common_hermitianGramDetTwoVectors_ne' | exact GlobalTheory.exists_common_hermitianGramDetTwoVectors_ne' | (intros; apply GlobalTheory.exists_common_hermitianGramDetTwoVectors_ne' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjKernelMul
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

open GlobalTheory.ConjPoint PeriodPair in

theorem exists_conj_kernel_mul : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∀ σ : ℂ ≃+* ℂ, (∀ x ∈ F, σ x = x) → ∃ c : ℕ, ¬ p ∣ c ∧ ∀ k : ℕ, GlobalTheory.ConjPoint.IsConj L L σ ((k : ℂ) * t) ((k : ℂ) * ((c : ℂ) * t)) := by
  intro p F L t hp h4 h3 hD σ hσ
  have h₂ : L.g₂ = σ L.g₂ := (hσ _ hD.g₂_mem).symm
  have h₃ : L.g₃ = σ L.g₃ := (hσ _ hD.g₃_mem).symm
  obtain ⟨s, -, hc⟩ := exists_conjEquiv h₂ h₃
  obtain ⟨t', ht'⟩ := latticePoint_surjective L (s (latticePoint L t))
  have hct : IsConj L L σ t t' := (hc _ _).2 ht'.symm
  have ht'n : t' ∉ L.lattice := by
    rcases hct with h | h
    · exact (hD.notMem h.1).elim
    · exact h.2.1

  have hsq : (σ (sqrtNegNat p)) ^ 2 = (sqrtNegNat p) ^ 2 := by
    rw [← map_pow, sqrtNegNat_sq, map_neg, map_natCast]
  have hm := IsConj.mul h₂ h₃ hD.mul hct
  have hker : σ (sqrtNegNat p) * t' ∈ L.lattice := by
    rcases hm with h | h
    · exact h.2
    · exact (h.1 hD.ker).elim
  have hker' : sqrtNegNat p * t' ∈ L.lattice := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with e | e
    · rwa [e] at hker
    · rw [e, neg_mul] at hker
      simpa using neg_mem hker
  obtain ⟨-, hz, -⟩ := GlobalTheory.T.sqrtNegPrime_kernel_cyclic p F L t hp h4 h3 hD
  obtain ⟨c, hcp, hcl⟩ := hz t' hker'
  refine ⟨c, fun hdvd => ?_, fun k => ?_⟩
  · have hc0 : c = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hcp
    subst hc0
    exact ht'n (by simpa using hcl)
  · have hk := IsConj.mul h₂ h₃ (α := (k : ℂ))
      (fun l hl => by rw [← nsmul_eq_mul]; exact nsmul_mem hl k) hct
    rw [map_natCast] at hk
    have h0 : IsConj L L σ 0 ((k : ℂ) * ((c : ℂ) * t) - (k : ℂ) * t') := by
      left
      refine ⟨zero_mem _, ?_⟩
      have : (k : ℂ) * ((c : ℂ) * t) - (k : ℂ) * t' = -((k : ℂ) * (t' - (c : ℂ) * t)) := by ring
      rw [this, ← nsmul_eq_mul]
      exact neg_mem (nsmul_mem hcl k)
    have := IsConj.add h₂ h₃ hk h0
    simpa using this

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousBijectiveAbelianizationOfAlgEqui
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

namespace GlobalTheory.HeckeGal

theorem continuous_galHom_of_fix {k F k' F' : Type*} [Field k] [Field F] [Algebra k F] [Field k'] [Field F']
    [Algebra k' F'] [Algebra.IsIntegral k F] (φ : (F ≃ₐ[k] F) →* (F' ≃ₐ[k'] F'))
    (h : ∀ y : F', ∃ x : F, ∀ σ : F ≃ₐ[k] F, σ x = x → φ σ y = y) : Continuous φ := by
  first
  | exact @_root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix
  | exact _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix
  | (apply _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix <;> assumption)
  | (intros; apply _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix ..)

theorem exists_topAbelianization_mulEquiv {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : G ≃* H) (hφ : IsHomeomorph φ) :
    ∃ ψ : TopologicalAbelianization G ≃* TopologicalAbelianization H, IsHomeomorph ψ ∧
      ∀ g : G, ψ (QuotientGroup.mk g) = QuotientGroup.mk (φ g) := by
  have hc : (commutator G).map (φ : G →* H) = commutator H := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ φ.surjective]
  have hmap : (Subgroup.topologicalClosure (commutator G)).map (φ : G →* H) =
      Subgroup.topologicalClosure (commutator H) := by
    apply SetLike.coe_injective
    rw [Subgroup.coe_map, Subgroup.topologicalClosure_coe, Subgroup.topologicalClosure_coe, ← hc, Subgroup.coe_map]
    exact (hφ.homeomorph φ).image_closure _
  let ψ := QuotientGroup.congr _ _ φ hmap
  have h1 : Continuous ψ :=
    (QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff).2
      (QuotientGroup.continuous_mk.comp hφ.continuous)
  have hs : Continuous φ.symm :=
    (φ.toEquiv.toHomeomorphOfContinuousOpen hφ.continuous hφ.isOpenMap).symm.continuous
  have h2 : Continuous ψ.symm :=
    (QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff).2
      (QuotientGroup.continuous_mk.comp hs)
  exact ⟨ψ, (Homeomorph.mk ψ.toEquiv h1 h2).isHomeomorph, fun g => rfl⟩

theorem exists_abMap_of_algEquiv : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω]
    (e : Ω ≃ₐ[K] AlgebraicClosure K), ∃ φ : GlobalTheory.HeckeGal.Gab K Ω →* Field.absoluteGaloisGroupAbelianization K,
      Continuous φ ∧ Function.Bijective φ ∧
      ∀ σ : Formalism.ConjugateSelfDual.G K Ω, φ (GlobalTheory.HeckeGal.toAb K Ω σ) = Neutral.B1.toAb K ((e.symm.trans σ).trans e) := by
  intro K _ _ Ω _ _ e
  haveI hint : Algebra.IsIntegral K Ω :=
    ⟨fun x => (isIntegral_algEquiv e).1 (Algebra.IsIntegral.isIntegral (e x))⟩
  let φ : (Ω ≃ₐ[K] Ω) ≃* Field.absoluteGaloisGroup K := AlgEquiv.autCongr e
  have h1 : Continuous φ.toMonoidHom :=
    continuous_galHom_of_fix φ.toMonoidHom fun y => ⟨e.symm y, fun σ hσ => by
      show e (σ (e.symm y)) = y
      rw [hσ, AlgEquiv.apply_symm_apply]⟩
  have h2 : Continuous φ.symm.toMonoidHom :=
    continuous_galHom_of_fix φ.symm.toMonoidHom fun y => ⟨e y, fun τ hτ => by
      show e.symm (τ (e y)) = y
      rw [hτ, AlgEquiv.symm_apply_apply]⟩
  have hφ : IsHomeomorph φ := (Homeomorph.mk φ.toEquiv h1 h2).isHomeomorph
  obtain ⟨ψ, hψ, hψg⟩ := exists_topAbelianization_mulEquiv φ hφ
  refine ⟨ψ.toMonoidHom, hψ.continuous, ψ.bijective, fun σ => ?_⟩
  exact hψg σ

end GlobalTheory.HeckeGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetDecoSetLatticeReps
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory

namespace DecoLatticeClasses

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

noncomputable def unitEquiv (γ : Matrix (Fin n) (Fin n) E) (h : γ * γ.conjTranspose = 1) :
    Sp E n ≃ₗ[E] Sp E n :=
  LinearEquiv.ofLinear (Matrix.mulVecLin γ.conjTranspose) (Matrix.mulVecLin γ)
    (by rw [← Matrix.mulVecLin_mul, mul_eq_one_comm.1 h, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, h, Matrix.mulVecLin_one])

theorem unitEquiv_mem (γ : Matrix (Fin n) (Fin n) E) (h : γ * γ.conjTranspose = 1) :
    unitEquiv γ h ∈ UF E n := by
  intro x y
  change star (γ.conjTranspose.mulVec x) ⬝ᵥ (γ.conjTranspose.mulVec y) = star x ⬝ᵥ y
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

theorem mem_one_iff [NumberField E] (a : E) :
    a ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ a := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨r, rfl⟩
    exact r.isIntegral_coe
  · intro h
    exact ⟨⟨a, h⟩, rfl⟩

end DecoLatticeClasses

open DecoLatticeClasses in

theorem exists_finset_decoSet_lattice_reps :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing E],
    (∀ x : E, star x = IsCMField.complexConj E x) → ∀ n : ℕ,
    ∃ Rs : Finset (Submodule (𝓞 E) (Sp E n)),
      (Rs.card : ℝ) ≤ (3 * ((Module.finrank ℚ E : ℝ) ^ 2 * (n : ℝ) ^ 4 *
        (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ^ 2)) ^
          (3 * Module.finrank ℚ E * n ^ 2) ∧
      ∀ (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (d : DecoSet E n ST SG),
        ∃ g : UF E n, ((g, (1 : GLG E n SG)) • d).1.N ∈ Rs := by
  intro E _ _ _ _ hs n
  obtain ⟨R, hR, H⟩ := GlobalTheory.exists_finset_selfDual_classes_rootDiscr E n
  refine ⟨R, hR, fun ST SG d => ?_⟩
  have hu : Formalism.HermitianLatticesTheory.dual (hStd E n) d.1.N = d.1.N := d.2.uni
  obtain ⟨L₀, hL₀, γ, hγ, hm⟩ := H d.1.N d.2.lat.fg d.2.lat.span_eq_top (fun y => by
    conv_lhs => rw [← hu, mem_dual]
    simp only [mem_one_iff, hStd_apply, hs])
  have hγ' : γ * γ.conjTranspose = 1 := by
    rw [← hγ]
    congr 1
    ext i j
    simp [Matrix.conjTranspose_apply, hs]
  refine ⟨⟨unitEquiv γ hγ', unitEquiv_mem γ hγ'⟩, ?_⟩
  have e : Formalism.HermitianLatticesTheory.gmap (unitEquiv γ hγ') d.1.N = L₀ := by
    ext x
    rw [mem_gmap, hm]
    rfl
  rw [← e] at hL₀
  exact hL₀

end GlobalTheory
end

