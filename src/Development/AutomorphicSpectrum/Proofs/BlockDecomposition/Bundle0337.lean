import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.RedMk
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0324
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0275
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0270
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0267
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0266
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0326
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import GroundTheory.AutomorphicForms.Bundle0020
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0327

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfSize
section
noncomputable section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.WedgeSupport

theorem nF_nonneg' {K ι κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K) : 0 ≤ nF A :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem sz_nonneg' {K ι κ : Type} [NormedField K] (g : Matrix ι κ K) : 0 ≤ sz g :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem map_mul_eq_one {R S ι κ : Type} [CommRing R] [CommRing S] [Fintype ι] [DecidableEq κ] (f : R →+* S)
    {A : Matrix ι κ R} {Y : Matrix κ ι R} (h : Y * A = 1) : Y.map f * A.map f = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero f) (map_one f)]

theorem one_le_sz_pow_mul_nF (hF : MulF) {K ι κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] {A : Matrix ι κ K} {Y : Matrix κ ι K} (h : Y * A = 1) :
    1 ≤ sz Y ^ Fintype.card κ * nF A := by
  have h1 := (hF K ι κ κ A).1 Y
  rw [h, (hF K κ κ κ 1).2.2 1, det_one, norm_one] at h1
  exact h1

theorem nF_le_sz_pow (hF : MulF) {K ι κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι κ K) : nF A ≤ sz A ^ Fintype.card κ := by
  have h1 := (hF K κ ι κ (1 : Matrix κ κ K)).1 A
  rw [Matrix.mul_one, (hF K κ κ κ 1).2.2 1, det_one, norm_one, mul_one] at h1
  exact h1

theorem nF_ne_zero_of_left_inv (hF : MulF) {K ι κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] {A : Matrix ι κ K} {Y : Matrix κ ι K} (h : Y * A = 1) : nF A ≠ 0 := by
  intro h0
  have h1 := one_le_sz_pow_mul_nF hF h
  rw [h0, mul_zero] at h1
  linarith

theorem nF_eq_one_of_sz_le (hF : MulF) {K ι κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] {A : Matrix ι κ K} {Y : Matrix κ ι K} (h : Y * A = 1) (hY : sz Y ≤ 1) (hA : sz A ≤ 1) :
    nF A = 1 := by
  apply le_antisymm
  · exact (nF_le_sz_pow hF A).trans (pow_le_one₀ (sz_nonneg' A) hA)
  · have h1 := one_le_sz_pow_mul_nF hF h
    have h2 : sz Y ^ Fintype.card κ ≤ 1 := pow_le_one₀ (sz_nonneg' Y) hY
    nlinarith [nF_nonneg' A]

theorem nI_ne_zero_of_left_inv (hI : MulI) {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {A : Matrix ι κ ℂ} {Y : Matrix κ ι ℂ} (h : Y * A = 1) : nI A ≠ 0 := by
  intro h0
  have h1 := (hI ι κ κ A).1 Y
  rw [h, (hI κ κ κ 1).2.2 1, det_one, norm_one, h0, mul_zero] at h1
  norm_num at h1

theorem finSupp_of_mul : MulF → MulI → SzFin → FinSupp := by
  intro hF hI hS E _ _ _ ι κ _ _ _ _ A Y h
  refine ⟨fun v => nI_ne_zero_of_left_inv hI (map_mul_eq_one (cV v) h),
    fun w => nF_ne_zero_of_left_inv hF (map_mul_eq_one (cW w) h), ?_⟩
  refine ((hS E κ ι Y).union (hS E ι κ A)).subset fun w hw => ?_
  by_contra hn
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hn
  exact hw (nF_eq_one_of_sz_le hF (map_mul_eq_one (cW w) h) hn.1 hn.2)

end GlobalTheory.CompanionTheory.WedgeSupport

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatThickeningQuotient
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsQ

namespace GlobalTheory.CompanionTheory.FlatThick

open TensorProduct in
set_option backward.isDefEq.respectTransparency true in

theorem flat_quotientMap {P B : Type} [CommRing P] [CommRing B] [Algebra P B] [Module.Flat P B] (I₀ : Ideal P) :
    (Ideal.quotientMap (I₀.map (algebraMap P B)) (algebraMap P B) Ideal.le_comap_map :
      P ⧸ I₀ →+* B ⧸ I₀.map (algebraMap P B)).Flat := by
  have f3 : (algebraMap (P ⧸ I₀) ((P ⧸ I₀) ⊗[P] B)).Flat := RingHom.flat_algebraMap_iff.2 inferInstance
  let e₂ : (B ⧸ I₀.map (algebraMap P B)) ≃+* (P ⧸ I₀) ⊗[P] B :=
      (((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I₀).toRingEquiv).trans
        (Algebra.TensorProduct.comm P B (P ⧸ I₀)).toRingEquiv)
  have f5 : (e₂.symm.toRingHom).Flat := RingHom.Flat.of_bijective e₂.symm.bijective
  have f4 := RingHom.Flat.comp f3 f5
  convert f4 using 1
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
  refine e₂.injective ?_
  have : e₂ (Ideal.Quotient.mk _ (algebraMap P B r)) = algebraMap (P ⧸ I₀) ((P ⧸ I₀) ⊗[P] B) (Ideal.Quotient.mk _ r) := by
    change Algebra.TensorProduct.comm P B (P ⧸ I₀) (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I₀ (Ideal.Quotient.mk _ (algebraMap P B r))) = _
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
    simp [Algebra.TensorProduct.algebraMap_apply]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    rfl
  simpa using this

theorem flat_of_surjective_ker {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (f : A →+* B) (hf : f.Flat)
    (π : A →+* A') (hπ : Function.Surjective π) (a : A) (hker : RingHom.ker π = Ideal.span {a})
    (g : A' →+* B ⧸ Ideal.span {f a}) (hg : ∀ r, g (π r) = Ideal.Quotient.mk _ (f r)) : g.Flat := by
  letI : Algebra A B := f.toAlgebra
  haveI : Module.Flat A B := hf
  have hJ : (Ideal.span {a}).map (algebraMap A B) = Ideal.span {f a} := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  let e₁ : (A ⧸ Ideal.span {a}) ≃+* A' :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hπ)
  let e₂ : (B ⧸ (Ideal.span {a}).map (algebraMap A B)) ≃+* (B ⧸ Ideal.span {f a}) := Ideal.quotEquivOfEq hJ
  have h0 := flat_quotientMap (P := A) (B := B) (Ideal.span {a})
  have h1 : (e₁.symm.toRingHom).Flat := RingHom.Flat.of_bijective e₁.symm.bijective
  have h2 : (e₂.toRingHom).Flat := RingHom.Flat.of_bijective e₂.bijective
  have h3 := RingHom.Flat.comp (RingHom.Flat.comp h1 h0) h2
  convert h3 using 1
  refine RingHom.ext fun x => ?_
  obtain ⟨r, rfl⟩ := hπ x
  have hr : e₁.symm (π r) = Ideal.Quotient.mk _ r := by
    rw [RingEquiv.symm_apply_eq]; rfl
  change g (π r) = e₂ (Ideal.quotientMap _ (algebraMap A B) Ideal.le_comap_map (e₁.symm (π r)))
  rw [hr, hg]
  rfl

theorem flatT_qT (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] (O : Type) [CommRing O]
    (F : B.Fn O) (ρ : O →+* k) (n : ℕ) (hn : n ≠ 0) (T : Thick (Wc.L l F ρ (n + 1))) (hT : FlatT T) :
    FlatT (qT hn T) := by
  refine flat_of_surjective_ker T.i hT (Wc.red l k n) ?_ (Ideal.Quotient.mk _ ((l : WittVector l k) ^ n)) ?_ (qi T)
    (qi_red T)
  · intro x
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ w, red_mk' w⟩
  · ext x
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, red_mk', Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
      Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨Ideal.Quotient.mk _ c, (map_mul _ _ _)⟩
    · rintro ⟨c, hc⟩
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hc
      obtain ⟨d, hd⟩ := hc
      refine ⟨c + (l : WittVector l k) * d, ?_⟩
      rw [mul_add, ← mul_assoc, ← pow_succ, ← hd]
      ring

end GlobalTheory.CompanionTheory.FlatThick

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafAddLeSup
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem imageSubobject_add_le {C : Type*} [Category C] [Preadditive C] [HasImages C]
    [HasBinaryCoproducts C] {A B : C} (f g : A ⟶ B) :
    imageSubobject (f + g) ≤ imageSubobject f ⊔ imageSubobject g := by
  have key : ∀ h : A ⟶ B, (imageSubobject h).Factors h := fun h => by
    have := Subobject.factors_comp_arrow (P := imageSubobject h) (factorThruImageSubobject h)
    rwa [imageSubobject_arrow_comp] at this
  have h := Subobject.factors_add f g
    (Subobject.factors_of_le f le_sup_left (key f)) (Subobject.factors_of_le g le_sup_right (key g))
  exact imageSubobject_le (f + g) _ (Subobject.factorThru_arrow _ _ h)

theorem sectionHom_add {X : Scheme.{0}} {F : X.Modules} (b c : Γ(F, ⊤)) :
    GlobalTheory.QCoh.sectionHom (b + c) = GlobalTheory.QCoh.sectionHom b + GlobalTheory.QCoh.sectionHom c := by
  ext V a
  change GlobalTheory.QCoh.structureModuleSectionsEquiv V a • GlobalTheory.Twist.resM F (le_top : V ≤ ⊤) (b + c) =
    GlobalTheory.QCoh.structureModuleSectionsEquiv V a • GlobalTheory.Twist.resM F (le_top : V ≤ ⊤) b +
      GlobalTheory.QCoh.structureModuleSectionsEquiv V a • GlobalTheory.Twist.resM F (le_top : V ≤ ⊤) c
  rw [map_add, smul_add]

theorem genHom_add {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules}
    (n : ℤ) (b c : Γ(GlobalTheory.twistZ P H n, ⊤)) :
    genHom hH n (b + c) = genHom hH n b + genHom hH n c := by
  have h : GlobalTheory.Twist.map (GlobalTheory.lbZPow H (-n)) (GlobalTheory.QCoh.sectionHom (b + c)) =
      GlobalTheory.Twist.map (GlobalTheory.lbZPow H (-n)) (GlobalTheory.QCoh.sectionHom b) +
        GlobalTheory.Twist.map (GlobalTheory.lbZPow H (-n)) (GlobalTheory.QCoh.sectionHom c) := by
    rw [sectionHom_add]
    exact (GlobalTheory.twistFunctor (GlobalTheory.lbZPow H (-n))).map_add
  simp only [genHom, h, Preadditive.add_comp]

theorem genSub_add_le {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules}
    (n : ℤ) (b c : Γ(GlobalTheory.twistZ P H n, ⊤)) :
    genSub hH n (b + c) ≤ genSub hH n b ⊔ genSub hH n c := by
  unfold genSub
  simp only [genHom_add]
  exact imageSubobject_add_le _ _

end GlobalTheory.CompanionTheory.GE.TwGen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafLeOfTwistedSectionMem
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem sectionHom_app_comp {X : Scheme.{0}} {F G : X.Modules} (φ : F ⟶ G) (s : Γ(F, ⊤)) :
    GlobalTheory.QCoh.sectionHom (φ.app ⊤ s) = GlobalTheory.QCoh.sectionHom s ≫ φ := by
  ext V a
  change (GlobalTheory.QCoh.sectionHom (φ.app ⊤ s)).app V a = φ.app V ((GlobalTheory.QCoh.sectionHom s).app V a)
  rw [GlobalTheory.QCoh.sectionHom_app, GlobalTheory.QCoh.sectionHom_app, Scheme.Modules.Hom.app_smul,
    GlobalTheory.Twist.app_resM]

theorem twistZZeroIso_inv_naturality {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB)
    {F G : X.Modules} (u : F ⟶ G) :
    (GlobalTheory.Twist.twistZZeroIso F hH).inv ≫ u =
      GlobalTheory.Twist.map (GlobalTheory.lbZPow H 0) u ≫ (GlobalTheory.Twist.twistZZeroIso G hH).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine GlobalTheory.Twist.zhom_ext fun V t i => ?_
  change GlobalTheory.Twist.zcoord ((GlobalTheory.Twist.twistZZeroIso G hH).hom.app V (u.app V t)) i =
    GlobalTheory.Twist.zcoord ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H 0) u).app V
      ((GlobalTheory.Twist.twistZZeroIso F hH).hom.app V t)) i
  rw [GlobalTheory.Twist.zcoord_twistZZeroIso_hom_app, GlobalTheory.Twist.zcoord_map_app,
    GlobalTheory.Twist.zcoord_twistZZeroIso_hom_app, GlobalTheory.Twist.app_resM]

theorem genHom_map_app {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB)
    {F G : X.Modules} (u : F ⟶ G) (n : ℤ) (b : Γ(GlobalTheory.twistZ F H n, ⊤)) :
    genHom hH n ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) u).app ⊤ b) = genHom hH n b ≫ u := by
  simp only [genHom, Category.assoc, twistZZeroIso_inv_naturality hH u]
  rw [sectionHom_app_comp]
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (GlobalTheory.Twist.twistZAddIso_naturality_assoc hH
    (add_neg_cancel n) u (GlobalTheory.Twist.twistZZeroIso G hH).inv))
  exact Category.assoc (GlobalTheory.Twist.map (GlobalTheory.lbZPow H (-n)) (GlobalTheory.QCoh.sectionHom b))
    (GlobalTheory.Twist.map (GlobalTheory.lbZPow H (-n)) (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) u))
    ((GlobalTheory.Twist.twistZAddIso G hH (add_neg_cancel n)).hom ≫ (GlobalTheory.Twist.twistZZeroIso G hH).inv)

theorem genSub_le : ∀ {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules}
    (S : Subobject P) (n : ℤ) (b : Γ(GlobalTheory.twistZ P H n, ⊤)), b ∈ twSecs H n S → genSub hH n b ≤ S := by
  rintro X H hH P S n _ ⟨b', rfl⟩
  exact imageSubobject_le _ (genHom hH n b') (genHom_map_app hH S.arrow n b').symm

end GlobalTheory.CompanionTheory.GE.TwGen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafQuasicoherent
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem isQuasicoherent_imageSubobject {X : Scheme.{0}} {A B : X.Modules}
    (hA : A.IsQuasicoherent) (hB : B.IsQuasicoherent) (f : A ⟶ B) :
    (imageSubobject f : X.Modules).IsQuasicoherent := by
  haveI := hA
  haveI := hB
  have hK : (kernel (cokernel.π f)).IsQuasicoherent := inferInstance
  exact GlobalTheory.QCoh.isQuasicoherent_of_iso
    (Abelian.imageIsoImage f ≪≫ (imageSubobjectIso f).symm)

theorem isQuasicoherent_genSub : ∀ {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB)
    {P : X.Modules}, P.IsQuasicoherent → ∀ (n : ℤ) (b : Γ(GlobalTheory.twistZ P H n, ⊤)),
    (genSub hH n b : X.Modules).IsQuasicoherent := by
  intro X H hH P hP n b
  have hO : (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsQuasicoherent := inferInstance
  have hS : (GlobalTheory.twistZ (SheafOfModules.unit X.ringCatSheaf) H (-n)).IsQuasicoherent :=
    GlobalTheory.Twist.isQuasicoherent_twist (F := SheafOfModules.unit X.ringCatSheaf)
      (GlobalTheory.Twist.isLB_lbZPow hH (-n))
  exact isQuasicoherent_imageSubobject hS hP _

end GlobalTheory.CompanionTheory.GE.TwGen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedClosedSystemCoherent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

lemma isCoherent_lvl {A : Type} [CommRing A] [IsNoetherianRing A] {I : Ideal A} {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsLocallyNoetherian X] {P : X.Modules} (hP : IsCoherent P)
    {S : ℕ → Subobject P} (hS : ClosedSys I P S) (e : ℕ) :
    IsCoherent (lvl S e : X.Modules) := by
  cases e with
  | zero =>
    have : IsIso (lvl S 0).arrow := by
      rw [lvl_zero]
      exact (Subobject.isIso_arrow_iff_eq_top _).2 rfl
    exact IsCoherent.of_iso (asIso (lvl S 0).arrow).symm hP
  | succ e => exact GlobalTheory.T.coherent_subobject_coherent hP (S e) (hS.qcoh e)

theorem isCoherent_gr : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsLocallyNoetherian X] {P : X.Modules}, IsCoherent P →
    ∀ (S : ℕ → Subobject P) (hS : ClosedSys I P S) (e : ℕ), IsCoherent (gr (anti hS) e) := by
  intro A _ _ I X _ _ P hP S hS e
  have := (isCoherent_lvl hP hS (e + 1)).1
  exact isCoherent_cokernel (incl (anti hS) e) (isCoherent_lvl hP hS e)

end GlobalTheory.CompanionTheory.GE.Step
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedPiecesGeneratedByIdealGenerators
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

def liftSub {X : Scheme.{0}} {P : X.Modules} {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e)
    (e : ℕ) (V : X.Opens) (W : Submodule Γ(X, V) Γ(gr hS e, V)) : Submodule Γ(X, V) Γ(P, V) where
  carrier := {t | ∃ x : Γ((lvl S e : X.Modules), V),
    (lvl S e).arrow.app V x = t ∧ (grπ hS e).app V x ∈ W}
  add_mem' := by
    rintro _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
    exact ⟨x + y, map_add _ _ _, by rw [map_add]; exact W.add_mem hx hy⟩
  zero_mem' := ⟨0, map_zero _, by rw [map_zero]; exact W.zero_mem⟩
  smul_mem' := by
    rintro c _ ⟨x, rfl, hx⟩
    exact ⟨c • x, Scheme.Modules.Hom.app_smul _ _ _,
      by rw [Scheme.Modules.Hom.app_smul]; exact W.smul_mem c hx⟩

lemma incl_arrow_app {X : Scheme.{0}} {P : X.Modules} {S : ℕ → Subobject P}
    (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) (V : X.Opens) (y : Γ((lvl S (e + 1) : X.Modules), V)) :
    (lvl S e).arrow.app V ((incl hS e).app V y) = (lvl S (e + 1)).arrow.app V y := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, incl_arrow]

lemma incl_grπ_app {X : Scheme.{0}} {P : X.Modules} {S : ℕ → Subobject P}
    (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) (V : X.Opens) (y : Γ((lvl S (e + 1) : X.Modules), V)) :
    (grπ hS e).app V ((incl hS e).app V y) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, incl_grπ]
  rfl

lemma pow_smul_le_secs_lvl {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] {P : X.Modules} (hP : P.IsQuasicoherent) {S : ℕ → Subobject P}
    (hS : ClosedSys I P S) (e : ℕ) (U : X.affineOpens) {n : Γ(P, U)}
    (hn : n ∈ (Ideal.map (toFunctions (A := A) (U : X.Opens)) (I ^ e) • ⊤ :
      Submodule Γ(X, U) Γ(P, U))) : n ∈ secs (lvl S e) (U : X.Opens) := by
  cases e with
  | zero =>
    have : IsIso (lvl S 0).arrow := by
      change IsIso (⊤ : Subobject P).arrow
      infer_instance
    refine ⟨(inv (lvl S 0).arrow).app (U : X.Opens) n, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, IsIso.inv_hom_id]
    simp
  | succ e =>
    have h1 : n ∈ secs (powSub I P (e + 1)) (U : X.Opens) := by
      rw [GlobalTheory.T.ideal_power_subobject_sections I P hP (e + 1) U U.2]
      exact hn
    exact (GlobalTheory.T.subobject_le_iff_affine_sections _ _).1 (hS.pow_le e) U h1

theorem span_grT_eq_top {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] {P : X.Modules} (hP : P.IsQuasicoherent) (S : ℕ → Subobject P)
    (hS : ClosedSys I P S) {k : ℕ} (g : Fin k → A) (hg : Ideal.span (Set.range g) = I)
    (hr : ∀ i, MapsDown S (toFunctions (X := X) (A := A) ⊤ (g i))) (e : ℕ) (U : X.affineOpens) :
    Submodule.span Γ(X, U) (⋃ i, Set.range ((grT (anti hS) (hr i) e).app U)) = ⊤ := by
  set W := Submodule.span Γ(X, U) (⋃ i, Set.range ((grT (anti hS) (hr i) e).app U)) with hW
  have hgen : ∀ i, ∀ n ∈ (Ideal.map (toFunctions (A := A) (U : X.Opens)) (I ^ e) • ⊤ :
      Submodule Γ(X, U) Γ(P, U)),
      toFunctions (A := A) (U : X.Opens) (g i) • n ∈ liftSub (anti hS) (e + 1) (U : X.Opens) W := by
    intro i n hn
    obtain ⟨v, rfl⟩ := pow_smul_le_secs_lvl I hP hS e U hn
    refine ⟨(mulLvl (hr i) e).app (U : X.Opens) v, ?_, ?_⟩
    · rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, mulLvl_arrow,
        Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, GroundTheory.Arith.SchemeCoh.smulHom_app_apply]
      congr 1
      exact restrictTop_restrict (homOfLE le_top) _
    · refine Submodule.subset_span (Set.mem_iUnion.2 ⟨i, (grπ (anti hS) e).app (U : X.Opens) v, ?_⟩)
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, grπ_grT,
        Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  have hle : (Ideal.map (toFunctions (A := A) (U : X.Opens)) (I ^ (e + 1)) • ⊤ :
      Submodule Γ(X, U) Γ(P, U)) ≤ liftSub (anti hS) (e + 1) (U : X.Opens) W := by
    rw [pow_succ', Ideal.map_mul, Submodule.mul_smul, Submodule.smul_le]
    intro r hr' n hn
    rw [← hg, Ideal.map_span] at hr'
    induction hr' using Submodule.span_induction with
    | mem x h =>
      obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := h
      exact hgen i n hn
    | zero => rw [zero_smul]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [add_smul]; exact Submodule.add_mem _ ha hb
    | smul a b _ hb => rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ a hb
  haveI : ((lvl S (e + 1 + 1) : Subobject P) : X.Modules).IsQuasicoherent := hS.qcoh (e + 1)
  haveI : ((lvl S (e + 1) : Subobject P) : X.Modules).IsQuasicoherent := hS.qcoh e
  have hsur : Function.Surjective ((grπ (anti hS) (e + 1)).app (U : X.Opens)) :=
    surjective_cokernel_π_app (incl (anti hS) (e + 1)) U.2
  rw [eq_top_iff]
  intro s _
  obtain ⟨x, rfl⟩ := hsur s
  have hq : ((powSub I P (e + 1) : Subobject P) : X.Modules).IsQuasicoherent :=
    haveI := hP
    (closedSys_pow I P).qcoh e
  have hx : (lvl S (e + 1)).arrow.app (U : X.Opens) x ∈
      secs (S (e + 1) ⊔ powSub I P (e + 1)) (U : X.Opens) := by
    rw [← hS.succ e]
    exact ⟨x, rfl⟩
  rw [(GlobalTheory.T.quasicoherent_sup_sections hP _ _ (hS.qcoh (e + 1)) hq).2 U U.2] at hx
  obtain ⟨_, ⟨y, rfl⟩, t, ht, hxy⟩ := hx
  rw [GlobalTheory.T.ideal_power_subobject_sections I P hP (e + 1) U U.2] at ht
  obtain ⟨x', hx't, hx'W⟩ := hle ht
  have hdec : x = (incl (anti hS) (e + 1)).app (U : X.Opens) y + x' := by
    apply injective_app_of_mono (lvl S (e + 1)).arrow (U : X.Opens)
    rw [map_add, hx't, hxy]
    exact congrArg (· + t) (incl_arrow_app (anti hS) (e + 1) (U : X.Opens) y).symm
  have hz : ∀ z : Γ((lvl S (e + 1 + 1) : X.Modules), (U : X.Opens)),
      (grπ (anti hS) (e + 1)).app (U : X.Opens)
        ((incl (anti hS) (e + 1)).app (U : X.Opens) z + x') =
      (grπ (anti hS) (e + 1)).app (U : X.Opens) x' := fun z => by
    rw [map_add, incl_grπ_app, zero_add]
  rw [hdec]
  exact Eq.mpr (congrArg (· ∈ W) (hz y)) hx'W

end GlobalTheory.CompanionTheory.GE.Step
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GrothendieckExistenceClosedProjStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grothendieck_existence_closed_proj : GEClosedProj := by
  first | exact @GlobalTheory.CompanionTheory.GE.geClosedProj | exact GlobalTheory.CompanionTheory.GE.geClosedProj | (intros; apply GlobalTheory.CompanionTheory.GE.geClosedProj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedTwoCharactersNotScalarStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_two_characters_not_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (W W' : Subrepresentation (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))), IsCompl W W' → W ≠ ⊥ → W' ≠ ⊥ → ¬ (∀ φ ψ : (jac (two (stdSum (rfl : a + b = a + b))) (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  first | exact @GlobalTheory.CompanionTheory.SplitFrob.not_dichotomy_det | exact GlobalTheory.CompanionTheory.SplitFrob.not_dichotomy_det | (intros; apply GlobalTheory.CompanionTheory.SplitFrob.not_dichotomy_det <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothCompContinuous
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.SmoothBridge

theorem isSmooth_comp {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (ψ : H →* G) (hψ : Continuous ψ) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (hρ : GlobalTheory.PRep.IsSmooth ρ) : GroundTheory.Automorphic.IsSmooth (ρ.comp ψ) := by
  intro v
  have h := (hρ v).preimage hψ
  exact h

end GlobalTheory.CompanionTheory.SmoothBridge
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethIsoProperSmoothStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slant_of_hodge_kuenneth : TopRes → SiteLaws → (∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q'), ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q ⊤) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂) → Slant := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.slant_of_kun | exact GlobalTheory.CompanionTheory.KunGlue.slant_of_kun | (intros; apply GlobalTheory.CompanionTheory.KunGlue.slant_of_kun <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductLocalCoordsStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kuenneth_product_local_coords : SiteLaws → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q') (V : X.Opens) (V' : X'.Opens) (d d' : ℕ), Nonempty (Coord q V d) → Nonempty (Coord q' V' d') → ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') T → inU q V ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') T → inU q' V' ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q V) (inU q' V') (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V')) h₁ h₂ := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.Aff.kun_aff | exact GlobalTheory.CompanionTheory.KunGlue.Aff.kun_aff | (intros; apply GlobalTheory.CompanionTheory.KunGlue.Aff.kun_aff <;> assumption)
end

