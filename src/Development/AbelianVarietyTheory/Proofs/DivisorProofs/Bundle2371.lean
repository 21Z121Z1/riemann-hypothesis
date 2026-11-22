import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2349
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1587
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiholomorphicLiftSystem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime]

theorem Datum.algebraMap_injective (D : Datum p) (hm : D.m = 1) :
    Function.Injective (algebraMap (𝓞 D.F) D.O) := by
  haveI := D.freeO
  haveI := D.finO
  haveI : Nontrivial D.O := by
    apply Module.nontrivial_of_finrank_pos (R := ℤ)
    rw [D.rankO, hm]; simpa using Module.finrank_pos (R := ℚ) (M := D.F)
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  have hF : (a : D.F) ≠ 0 := by exact_mod_cast ha0
  obtain ⟨y, hy0, hyint⟩ := IsAlgebraic.exists_integral_multiple
    (a.2.isAlgebraic.inv)
  set b : 𝓞 D.F := ⟨_, hyint⟩
  have hab : a * b = (y : 𝓞 D.F) := by
    apply RingOfIntegers.coe_injective
    simp only [map_mul, map_intCast]
    show (a : D.F) * ((y : ℤ) • (a : D.F)⁻¹) = _
    rw [zsmul_eq_mul]
    field_simp
  have h1 : algebraMap (𝓞 D.F) D.O (y : 𝓞 D.F) = 0 := by rw [← hab, map_mul, ha, zero_mul]
  rw [map_intCast] at h1
  have : (y : ℤ) • (1 : D.O) = 0 := by rw [zsmul_eq_mul, _root_.mul_one, h1]
  rcases smul_eq_zero.mp this with h | h
  · exact hy0 h
  · exact one_ne_zero h

theorem Datum.exists_zsmul_eq_algebraMap (D : Datum p) (hm : D.m = 1) (x : D.O) :
    ∃ e : ℤ, e ≠ 0 ∧ ∃ a : 𝓞 D.F, e • x = algebraMap (𝓞 D.F) D.O a := by
  haveI := D.freeO
  haveI := D.finO
  let f : 𝓞 D.F →ₗ[ℤ] D.O := (algebraMap (𝓞 D.F) D.O).toAddMonoidHom.toIntLinearMap
  have hf : Function.Injective f := D.algebraMap_injective hm
  let M := LinearMap.range f
  have h1 := rank_quotient_add_rank_of_isDomain M
  rw [rank_range_of_injective f hf, ← Module.finrank_eq_rank (R := ℤ) (M := 𝓞 D.F),
    ← Module.finrank_eq_rank (R := ℤ) (M := D.O), RingOfIntegers.rank, D.rankO, hm, one_pow,
    _root_.one_mul] at h1
  obtain ⟨k, hk⟩ := Cardinal.lt_aleph0.mp (Module.rank_lt_aleph0 (R := ℤ) (M := D.O ⧸ M))
  rw [hk] at h1
  norm_cast at h1
  have h0 : Module.rank ℤ (D.O ⧸ M) = 0 := by rw [hk]; norm_cast; omega
  obtain ⟨e, he, hex⟩ := (rank_eq_zero_iff.mp h0) (Submodule.Quotient.mk x)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hex
  obtain ⟨a, ha⟩ := hex
  exact ⟨e, he, a, ha.symm⟩

theorem Datum.algebraMap_surjective_of_m_eq_one :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.m = 1 → Function.Surjective (algebraMap (𝓞 D.F) D.O) := by
  intro p _ D hm x
  haveI := D.freeO
  haveI := D.finO
  obtain ⟨e, he, a, ha⟩ := D.exists_zsmul_eq_algebraMap hm x
  haveI : Algebra.IsIntegral ℤ D.O := Algebra.IsIntegral.of_finite ℤ D.O
  obtain ⟨P, hPm, hP⟩ := Algebra.IsIntegral.isIntegral (R := ℤ) x
  have h1 : Polynomial.aeval (algebraMap ℤ D.O e * x) (P.scaleRoots e) = 0 :=
    Polynomial.scaleRoots_aeval_eq_zero (by rwa [Polynomial.aeval_def])
  rw [← Algebra.smul_def, ha, Polynomial.aeval_algebraMap_apply] at h1
  have h2 : Polynomial.aeval a (P.scaleRoots e) = 0 :=
    D.algebraMap_injective hm (by rw [h1, map_zero])
  have he' : (e : D.F) ≠ 0 := by exact_mod_cast he
  have h4 : Polynomial.aeval (a : D.F) (P.scaleRoots e) = 0 := by
    have := congrArg (algebraMap (𝓞 D.F) D.F) h2
    rwa [← Polynomial.aeval_algebraMap_apply, map_zero] at this
  have h3 : Polynomial.eval₂ (algebraMap ℤ D.F) ((a : D.F) / e) P = 0 := by
    have := Polynomial.scaleRoots_eval₂_mul (p := P) (algebraMap ℤ D.F) ((a : D.F) / e) e
    rw [show algebraMap ℤ D.F e * ((a : D.F) / e) = (a : D.F) by
      rw [algebraMap_int_eq, eq_intCast]; field_simp] at this
    rw [← Polynomial.aeval_def, h4] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ (by simpa using he'))
  have hint : IsIntegral ℤ ((a : D.F) / e) := ⟨P, hPm, h3⟩
  obtain ⟨a', ha'⟩ : ∃ a' : 𝓞 D.F, (a' : D.F) = (a : D.F) / e := ⟨⟨_, hint⟩, rfl⟩
  refine ⟨a', ?_⟩
  have hae : a = e • a' := by
    apply RingOfIntegers.coe_injective
    rw [zsmul_eq_mul, map_mul, map_intCast]
    change (a : D.F) = (e : D.F) * (a' : D.F)
    rw [ha']
    field_simp
  apply smul_right_injective D.O he
  change e • algebraMap (𝓞 D.F) D.O a' = e • x
  rw [ha, ← map_zsmul, ← hae]

end GlobalTheory.UPel.HT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLiftSemiMOm
section
set_option autoImplicit false

noncomputable section

open TensorProduct GlobalTheory.CechDR GlobalTheory.DeRham

namespace GlobalTheory.FormsBaseChange

theorem bijective_liftSemi_iff {R R' B B' M N : Type} [CommRing R] [CommRing R'] [CommRing B]
    [CommRing B'] [Algebra R R'] [Algebra R B] [Algebra R' B'] [Algebra B B'] [Algebra R B']
    [IsScalarTower R B B'] [IsScalarTower R R' B'] [Algebra.IsPushout R R' B B']
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
    [AddCommGroup N] [Module B N] [Module B' N] [Module R' N] [IsScalarTower B B' N]
    [IsScalarTower R' B' N] (φ : M →ₗ[B] N) (g : M →ₛₗ[algebraMap R R'] N) (e : ∀ x, g x = φ x) :
    Function.Bijective (liftSemi g) ↔ IsBaseChange B' φ := by
  have hc : (liftSemi g : R' ⊗[R] M → N) =
      φ.liftBaseChange B' ∘ (Algebra.IsPushout.cancelBaseChange R R' B B' M).symm := by
    funext z
    induction z with
    | zero => simp
    | add x y hx hy => simp only [Function.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
    | tmul s m => simp [e]
  rw [hc, Function.Bijective.of_comp_iff _ (LinearEquiv.bijective _)]
  constructor
  · intro H
    exact IsBaseChange.of_equiv (LinearEquiv.ofBijective _ H) fun x ↦ by simp
  · intro H
    have : (φ.liftBaseChange B' : B' ⊗[B] M → N) = H.equiv := by
      funext z
      induction z with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul s m => simp
    rw [this]
    exact H.equiv.bijective

theorem bijective_liftSemi_mOm (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (B B' : Type)
    [CommRing B] [CommRing B'] [Algebra R B] [Algebra R' B'] (α : B →+* B')
    (h : SemiHom (algebraMap R R') α) (f : B →ₛₗ[algebraMap R R'] B') (hf : ∀ b, f b = α b)
    (h0 : Function.Bijective (liftSemi f)) (h1 : Function.Bijective (liftSemi h.m1)) (j : ℕ) :
    Function.Bijective (liftSemi (h.mOm j)) := by
  letI : Algebra B B' := α.toAlgebra
  letI : Algebra R B' := ((algebraMap R' B').comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' B' := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R B B' := .of_algebraMap_eq fun r ↦ (h.map_algebraMap r).symm
  haveI : Algebra.IsPushout R R' B B' :=
    ⟨IsBaseChange.of_equiv (LinearEquiv.ofBijective _ h0) fun x ↦ by
      change liftSemi f (1 ⊗ₜ x) = α x
      rw [liftSemi_tmul, one_smul, hf]⟩
  let φ : Ω[B⁄R] →ₗ[B] Ω[B'⁄R'] :=
    { toFun := h.m1
      map_add' := map_add _
      map_smul' := fun b x ↦ by
        rw [h.oneFormMap_smul_semilinear, RingHom.id_apply, ← algebraMap_smul B' b]; rfl }
  have hφ : IsBaseChange B' φ := (bijective_liftSemi_iff φ h.m1 fun _ ↦ rfl).1 h1
  refine (bijective_liftSemi_iff _ (h.mOm j) ?_).2 (GlobalTheory.TopForm.isBaseChange_exteriorPower hφ j)
  let ψ : Om R B j →ₗ[B] Om R' B' j :=
    { toFun := h.mOm j
      map_add' := map_add _
      map_smul' := fun b x ↦ by
        rw [h.mOm_smul, RingHom.id_apply, ← algebraMap_smul B' b]; rfl }
  suffices H : ψ = _ from fun x ↦ LinearMap.congr_fun H x
  apply exteriorPower.linearMap_ext
  ext1 v
  simp only [LinearMap.compAlternatingMap_apply, exteriorPowerMapOver_ιMulti]
  refine Subtype.ext ?_
  change h.mDR (exteriorPower.ιMulti B j v : DR R B) = _
  rw [exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
    ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext k
  exact h.mDR_ι _

end GlobalTheory.FormsBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLiftSemiSecPull
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechDR

theorem bijective_liftSemi_secPull : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X), IsPullback φ s' s (spMap (algebraMap R R')) → ∀ p : Pair φ, p.1.1.1 = φ ⁻¹ᵁ p.1.2.1 → ∀ f : Sec s p.1.2.1 →ₛₗ[algebraMap R R'] Sec s' p.1.1.1, (∀ b, f b = secPull s s' p b) → Function.Bijective (liftSemi f) := by
  intro R R' _ _ _ X X' s s' φ H p hp f hf
  have hUY : p.1.1.1 = φ ⁻¹ᵁ p.1.2.1 ⊓ s' ⁻¹ᵁ ⊤ := by rw [hp]; simp
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := p.1.2.1) (UY := p.1.1.1) le_top le_top hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) p.1.2.2)
  have po' : IsPushout (CommRingCat.ofHom (algebraMap R (Sec s p.1.2.1))) (CommRingCat.ofHom (algebraMap R R'))
      (CommRingCat.ofHom (secPull s s' p)) (CommRingCat.ofHom (algebraMap R' (Sec s' p.1.1.1))) := by
    refine po.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of R')) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (Category.comp_id _).trans ((Scheme.ΓSpecIso (.of R)).hom_inv_id_assoc _).symm
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans ((Scheme.ΓSpecIso (.of R')).hom_inv_id_assoc _).symm
  letI : Algebra (Sec s p.1.2.1) (Sec s' p.1.1.1) := (secPull s s' p).toAlgebra
  letI : Algebra R (Sec s' p.1.1.1) := ((algebraMap R' (Sec s' p.1.1.1)).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' (Sec s' p.1.1.1) := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R (Sec s p.1.2.1) (Sec s' p.1.1.1) :=
    .of_algebraMap_eq fun r => (congrArg (fun q => q.hom r) po'.w).symm
  have h : Algebra.IsPushout R R' (Sec s p.1.2.1) (Sec s' p.1.1.1) :=
    (CommRingCat.isPushout_iff_isPushout.mp po').symm
  have e : ⇑(liftSemi f) = ⇑h.out.equiv := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul c v => rw [liftSemi_tmul, h.out.equiv_tmul, hf]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [e]
  exact h.out.equiv.bijective

end GlobalTheory.CechDR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BorelWeilFlagModelDetInverseIsAmpleLocal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

noncomputable section

namespace GlobalTheory.FlagPlucker

open GlobalTheory.FlagMod Formalism.L2.Pj in

theorem isAmpleLB_LL_flagModel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagModel Y) (z : Y.X), ∃ V : Y.X.Opens, z ∈ V ∧ IsAffineOpen V ∧ IsAmpleLB ((X.F.LL (fun ix => ix.elim 0 fun p => (Dw.mult p.1 : ℤ) - ((p.2 : ℕ) : ℤ))).pull (X.π ⁻¹ᵁ V).ι) := by
  intro E _ _ _ H Dw l Xo c Y X z
  have hprop : IsProper X.π := X.proper
  by_cases hz : z ∈ Set.range X.π.base
  · obtain ⟨y, rfl⟩ := hz
    obtain ⟨k0, hk0⟩ := TopologicalSpace.Opens.mem_iSup.1 (X.F.cover.ge (Set.mem_univ y))
    have hzM : X.π y ∈ (X.F.M k0).U := X.F.le k0 hk0
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVM⟩ := Y.X.isBasis_affineOpens.exists_subset_of_mem_open
      (show X.π y ∈ ((X.F.M k0).U : Set Y.X) from hzM) (X.F.M k0).U.isOpen
    refine ⟨V, hzV, hV, ?_⟩
    have hg : ⊤ ≤ ((X.π ⁻¹ᵁ V).ι ≫ X.π) ⁻¹ᵁ (X.F.M k0).toMChart.U := fun p _ => hVM (by
      show X.π ((X.π ⁻¹ᵁ V).ι p) ∈ V
      have : (X.π ⁻¹ᵁ V).ι p ∈ X.π ⁻¹ᵁ V := by
        have h := Scheme.Opens.range_ι (X.π ⁻¹ᵁ V)
        exact (h.le ⟨p, rfl⟩ : _)
      exact this)
    have hf : IsProper ((X.π ∣_ V) ≫ hV.isoSpec.hom) := inferInstance
    choose t ht using fun (p : Σ σ : E →+* ℂ, Fin (Dw.mult σ)) (q : Fin (plkNum (X.F.M k0).toMChart p.2 + 1)) =>
      GlobalTheory.T.pluckerMinors_sections_inverseDetFlagBundle X.F (X.F.M k0).toMChart (X.π ⁻¹ᵁ V).ι hg p.1 p.2 q
    have hnz : ∀ p, ⨆ q, nonzeroLocus (t p q) = ⊤ := fun p =>
      GlobalTheory.T.sections_of_pulled_back_line_bundles_on_frames X.F (X.F.M k0).toMChart (X.π ⁻¹ᵁ V).ι hg p.1 p.2 (t p) (ht p)
    refine isAmpleLB_of_finite_fibres Γ(Y.X, V) _ ((X.π ∣_ V) ≫ hV.isoSpec.hom) hf (Σ σ : E →+* ℂ, Fin (Dw.mult σ))
      (fun p => (X.F.LL (ind p.1 p.2)).pull (X.π ⁻¹ᵁ V).ι) (fun p => LB.isLB_pull (X.F.isLB_LL _) _)
      (fun p => plkNum (X.F.M k0).toMChart p.2) t hnz ?_ (fun _ => 1) (fun _ => le_rfl) _
      (LB.isLB_pull (X.F.isLB_LL _) _) ?_
    · intro K _ _ a
      have hfin := X.fin K (a ≫ (X.π ⁻¹ᵁ V).ι)
      refine (hfin.preimage (f := fun a' : Sp K ⟶ _ => a' ≫ (X.π ⁻¹ᵁ V).ι)
        fun b _ b' _ e => (cancel_mono _).1 e).subset ?_
      rintro a' ⟨h1, h2⟩
      have e : (X.π ⁻¹ᵁ V).ι ≫ X.π = ((X.π ∣_ V) ≫ hV.isoSpec.hom) ≫ hV.fromSpec := by
        rw [← hV.isoSpec_inv_ι, Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι]
      have hx : a ≫ (X.π ⁻¹ᵁ V).ι ≫ X.π = a' ≫ (X.π ⁻¹ᵁ V).ι ≫ X.π := by
        rw [e]
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ hV.fromSpec) h1.symm).trans (Category.assoc _ _ _))
      exact GlobalTheory.T.lieFlag_eq_of_pluckerPoints_eq_field_points X.F (X.F.M k0).toMChart (X.π ⁻¹ᵁ V).ι hg (fun σ m => t ⟨σ, m⟩)
        (fun σ m => ht ⟨σ, m⟩) (fun σ m => hnz ⟨σ, m⟩) _ K a a' hx (fun σ m => (h2 ⟨σ, m⟩).symm)
    · have he : (fun ix : Ix Dw => ix.elim 0 fun p => (Dw.mult p.1 : ℤ) - ((p.2 : ℕ) : ℤ)) =
          ∑ p : Σ σ : E →+* ℂ, Fin (Dw.mult σ), ind p.1 p.2 := by
        funext ix
        rcases ix with _ | ⟨σ, i⟩
        · simp [ind]
        · rw [Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single σ]
          · simp only [ind, Option.elim, true_and]
            rw [Finset.sum_boole]
            have : (Finset.univ.filter fun m : Fin (Dw.mult σ) => (i : ℕ) ≤ m) = Finset.Ici i := by
              ext m; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici, Fin.le_def]
            simp only [this, Fin.card_Ici]
            push_cast [Nat.cast_sub i.2.le]
            ring
          · intro σ' _ h
            refine Finset.sum_eq_zero fun m _ => ?_
            simp [ind, Ne.symm h]
          · simp
      have h2 : ∀ p : Σ σ : E →+* ℂ, Fin (Dw.mult σ),
          1 • CechPic.cls ((X.F.LL (ind p.1 p.2)).pull (X.π ⁻¹ᵁ V).ι) (LB.isLB_pull (X.F.isLB_LL _) _) =
            CechPic.pull (X.π ⁻¹ᵁ V).ι (CechPic.cls (X.F.LL (ind p.1 p.2)) (X.F.isLB_LL _)) :=
        fun p => one_smul _ _
      rw [CechPic.cls_pull (X.F.isLB_LL _), Finset.sum_congr rfl fun p _ => h2 p, ← map_sum,
        ← GlobalTheory.T.cechPicardClass_gradedTensorBundle_finset_sum X.F Finset.univ (fun p : Σ σ : E →+* ℂ, Fin (Dw.mult σ) => ind p.1 p.2)]
      congr 2
      exact congrArg _ he
  · have hcl : IsClosed (Set.range X.π.base) := X.π.isClosedMap.isClosed_range
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVc⟩ := Y.X.isBasis_affineOpens.exists_subset_of_mem_open
      (show z ∈ (Set.range X.π.base)ᶜ from hz) hcl.isOpen_compl
    refine ⟨V, hzV, hV, ?_⟩
    haveI : IsEmpty (X.π ⁻¹ᵁ V).toScheme := ⟨fun p => hVc p.2 ⟨p.1, rfl⟩⟩
    haveI : IsAffine (X.π ⁻¹ᵁ V).toScheme := isAffine_of_isEmpty
    exact isAmpleLB_of_isAffine (LB.isLB_pull (X.F.isLB_LL _) _)

end GlobalTheory.FlagPlucker

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleNonzeroPeriod
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KerFin

theorem gbig_comb {Q1 Q2 Q : GlobalTheory.SqTop.GP} (h1 : GlobalTheory.SqTop.GBig Q1) (h2 : GlobalTheory.SqTop.GBig Q2)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q1 G μ₀ C x b → Q2 G μ₀ C x b → Q G μ₀ C x b) : GlobalTheory.SqTop.GBig Q := by
  obtain ⟨A1, h1⟩ := h1
  obtain ⟨A2, h2⟩ := h2
  refine ⟨max A1 A2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, h1⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, h2⟩ := h2 ε CF (le_of_max_le_right hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hL G => h G μ₀ C _ _
    (h1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ₀ hL G)
    (h2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ₀ hL G)⟩

theorem bottom_kernel : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω₀ : ℂ, Ω₀ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
            GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
            ∀ T, X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g y = Ω₀ * u * starRingEnd ℂ (P.term x h T) := by
  intro hPr hTI hLM hInp hBS
  refine gbig_comb (GlobalTheory.T.bottom_triangle_archimedean_constant hPr hTI hLM hInp hBS) GlobalTheory.BotWeights.weights_const ?_
  intro D T Lc sc G μ₀ C x b q2 q3 W hW i j A A' WW X δ t0 hX hβ
  obtain ⟨r, rc, κ, hr, hrc, hκ, H2⟩ := q2 W hW i j A A' WW X δ t0 hX hβ
  obtain ⟨n₀, H3⟩ := q3 i j δ t0
  obtain ⟨Ω, hΩ, H1⟩ := GlobalTheory.T.bottomTriple_thetaKernel_minors_eq_const_conjJet G W hW i j A A' WW X hX r rc hr hrc n₀
  refine ⟨Ω * starRingEnd ℂ κ, mul_ne_zero hΩ ((map_ne_zero _).2 hκ), fun s Q P P' hB => ?_⟩
  obtain ⟨u, hu0, huQ, huU, hEq⟩ := H2 s Q P P' hB
  refine ⟨u, hu0, huQ, huU, fun ea ed h g x y hg hy Tu => ?_⟩
  have hne : κ * starRingEnd ℂ u ≠ 0 := mul_ne_zero hκ ((map_ne_zero _).2 hu0)
  rw [H1 P.a P.d P.n ea ed (H3 s Q P P' hB) s g y hg.1 hy.1 Tu, hEq ea ed h g x y hg hy,
    GlobalTheory.FunObj.NormUniq.applyAt0_smul _ hne]
  simp only [GlobalTheory.NormSum.Pair.term, map_mul, Complex.conj_conj]
  ring

end GlobalTheory.KerFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryComponentStalkRegularBoundaryIdealProdPaStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_componentStalk_regular_boundaryIdeal_prod_params : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1), x ∉ (j₀ TF.Y Z).opensRange → IsRegularLocalRing ((X₀ TF.Y Z).presheaf.stalk x) ∧ ∃ (n : ℕ) (f : Fin n → (X₀ TF.Y Z).presheaf.stalk x) (J : Finset (Fin n)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp ((X₀ TF.Y Z).presheaf.stalk x) n f ∧ J.Nonempty ∧ Ideal.map (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx) ((Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl).ideal U) = Ideal.span {∏ i ∈ J, f i} := by
  first | exact @GlobalTheory.LogKSDiv.boundary_germ_snc | exact GlobalTheory.LogKSDiv.boundary_germ_snc | (intros; apply GlobalTheory.LogKSDiv.boundary_germ_snc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamComparisonBijectiveCupSmooth
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.SmoothLift

theorem isIso_spMap_mk_bot (R : Type) [CommRing R] : IsIso (spMap (Ideal.Quotient.mk (⊥ : Ideal R))) := by
  let e : R ≃+* R ⧸ (⊥ : Ideal R) := RingEquiv.ofBijective (Ideal.Quotient.mk ⊥)
    ⟨fun a b h ↦ by simpa [sub_eq_zero] using Ideal.Quotient.eq.1 h, Ideal.Quotient.mk_surjective⟩
  have : IsIso (spMap e.toRingHom) := inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
  exact this

def ofSmooth (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (hs : Smooth s) (hsep : IsSeparated s)
    (hqc : QuasiCompact s) : Data where
  R := R
  I := ⊥
  κ := dp0 R
  nil := isDPNilpotent_bot R
  X := X
  X₀ := X
  s := s
  t := s
  i := 𝟙 X
  smooth := hs
  sep := hsep
  qc := hqc
  red := by
    haveI := isIso_spMap_mk_bot R
    refine ⟨s ≫ inv (spMap (Ideal.Quotient.mk (⊥ : Ideal R))), ?_, by simp⟩
    exact IsPullback.of_horiz_isIso ⟨by simp⟩

end GlobalTheory.SmoothLift

namespace GlobalTheory.CechDR

open GlobalTheory.SmoothLift

theorem cechDeRham_comparison_bijective_cup_smooth (hP : GlobalTheory.Published.CrystallineSmoothLift) : ∀ (R : Type) [CommRing R] (X : Scheme.{0})
    (s : X ⟶ Sp R), Smooth s → IsSeparated s → QuasiCompact s → Function.Bijective (cmp1 s) ∧
    ∃ e : SecondDeRham s ≃ₗ[R] HH2 s, ∀ a b : FirstDeRham s, e (cup _ a b) = cupHH s (cmp1 s a) (cmp1 s b) := by
  intro R _ X s hs hsep hqc
  obtain ⟨e₁, e₂, hcup, hcmp, -⟩ := hP
  let D := ofSmooth R X s hs hsep hqc
  have key : ∀ c : FirstDeRham s, e₁ D c = cmp1 s c := fun c ↦ by
    have h1 := hcmp D (IsMor.id (dp0 R) s) c
    have h2 : (IsMor.id (dp0 R) s).pull1 c = c := IsMor.pullCohomologyOne_id _ c
    exact (congrArg (e₁ D) h2).symm.trans h1
  refine ⟨?_, e₂ D, fun a b ↦ ?_⟩
  · have hf : (cmp1 s : FirstDeRham s → HH1 s) = e₁ D := funext fun c ↦ (key c).symm
    rw [hf]; exact (e₁ D).bijective
  · rw [← key, ← key]; exact hcup D a b

end GlobalTheory.CechDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardEqZeroOfTrivialOnDisjointCoverStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechPicard_eq_zero_of_trivial_on_disjoint_cover : ∀ {Y : Scheme.{0}} {κ : Type} [Finite κ] {Z : κ → Scheme.{0}} (f : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (f i)], (⨆ i, (f i).opensRange = ⊤) → (Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) → ∀ d : Pic Y, (∀ i, GlobalTheory.CechPic.pull (f i) d = 0) → d = 0 := by
  first | exact @GlobalTheory.PicDisj.eq_zero_of_pull_eq_zero | exact GlobalTheory.PicDisj.eq_zero_of_pull_eq_zero | (intros; apply GlobalTheory.PicDisj.eq_zero_of_pull_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardEqZeroOfTwoOpenCoverUnitsSplitStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechPicard_eq_zero_of_twoOpen_cover_units_split : ∀ (Z : Scheme.{0}) (O O' : Z.Opens), O ⊔ O' = ⊤ → (∀ F : Γ(Z, O ⊓ O')ˣ, ∃ (u : Γ(Z, O)ˣ) (u' : Γ(Z, O')ˣ), F = res (inf_le_left : O ⊓ O' ≤ O) u * res (inf_le_right : O ⊓ O' ≤ O') u') → ∀ c : Pic Z, GlobalTheory.CechPic.pull O.ι c = 0 → GlobalTheory.CechPic.pull O'.ι c = 0 → c = 0 := by
  first | exact @GlobalTheory.CechPic.eq_zero_of_pull_eq_zero_of_units_split | exact GlobalTheory.CechPic.eq_zero_of_pull_eq_zero_of_units_split | (intros; apply GlobalTheory.CechPic.eq_zero_of_pull_eq_zero_of_units_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardExtendOfLocallyTrivialNormalCodimTwoStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechPicard_extend_of_locally_trivial_normal_codimTwo : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ W : X.Opens, (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ W) → ∀ c : Pic W.toScheme, (∀ x : X, ∃ N : X.Opens, x ∈ N ∧ GlobalTheory.CechPic.pull (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) c = 0) → ∃ c' : Pic X, GlobalTheory.CechPic.pull W.ι c' = c := by
  first | exact @GlobalTheory.extend_class_of_locally_trivial | exact GlobalTheory.extend_class_of_locally_trivial | (intros; apply GlobalTheory.extend_class_of_locally_trivial <;> assumption)
end

