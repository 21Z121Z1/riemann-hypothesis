import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0061
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsInvariantSectionMemBasicOpenIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverTargetOfIsGaloisCover
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExistsIffTopExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0067
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2194
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv
section
noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)} {A : Atlas Y p}

theorem uvec_cv (b : A.B) (w : Pm Dw.mult) (z : Let Dw.mult) (r : Fin (A.N + 1)) :
    uvec (A.cv b) w z r = ((A.A b).map (cC A b) * uC A b w z.1) r z.2 := by
  obtain ⟨τ, j⟩ := z
  simp only [uvec, cellVec, Atlas.cv, uC, cellMat, cC, Matrix.mul_apply, Matrix.map_apply, Matrix.submatrix_apply,
    Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, map_sum, map_mul, id,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => ?_
  ring

variable {Z : Scheme.{0}} {κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)} [∀ b w, IsOpenImmersion (κ b w)]
  {S : Type} [CommRing S]

theorem eq_spMap_ev (k : A.B × Pm Dw.mult) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) :
    spMap ((ev z _ hz).comp (cellθ κ k).toRingHom) ≫ κ k.1 k.2 = z := by
  rw [← spMap_comp', Category.assoc, spMap_cellθ, spMap_ev]

end GlobalTheory.FlagMod.FieldFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfIsPartOfBasisBalFormsOfMem
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM

namespace GlobalTheory.PolFan

theorem eq_zero_of_linearIndependent_int_rat {Y ι : Type} [Fintype ι] {f : ι → Y → ℤ}
    (hf : LinearIndependent ℤ f) (q : ι → ℚ) (hq : ∀ y, ∑ i, q i * (f i y : ℚ) = 0) : q = 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
  have hb' : ∀ i, ∃ r : ℤ, (r : ℚ) = ((b : ℤ) : ℚ) * q i := fun i => by
    obtain ⟨r, hr⟩ := hb i
    exact ⟨r, by simpa [Algebra.smul_def] using hr⟩
  choose n hn using hb'
  have h0 : n = 0 := by
    rw [Fintype.linearIndependent_iff] at hf
    funext i
    refine hf n ?_ i
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have : ((∑ i, n i * f i y : ℤ) : ℚ) = ((b : ℤ) : ℚ) * ∑ i, q i * (f i y : ℚ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hn i]; ring
    rw [hq y, mul_zero] at this
    exact_mod_cast this
  funext i
  have hbne : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero b
  have h := hn i
  rw [h0] at h
  simp only [Pi.zero_apply, Int.cast_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hbne

theorem eq_zero_of_linearIndependent_int {Y ι : Type} [Fintype ι] {f : ι → Y → ℤ}
    (hf : LinearIndependent ℤ f) (k : Type) [Field k] [CharZero k] (a : ι → k)
    (ha : ∀ y, ∑ i, a i * (f i y : k) = 0) : a = 0 := by
  classical
  let B := Module.Basis.ofVectorSpace ℚ k
  have key : ∀ j, (fun i => B.coord j (a i)) = 0 := fun j =>
    eq_zero_of_linearIndependent_int_rat hf _ fun y => by
      have h := congrArg (B.coord j) (ha y)
      rw [map_sum, map_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm (a i), ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]
  funext i
  apply B.repr.injective
  ext j
  have := congrFun (key j) i
  simpa [Module.Basis.coord_apply] using this

end GlobalTheory.PolFan

namespace GlobalTheory.PolFan

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfRestrictionsVanishStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open MeasureTheory Formalism.L2.Theta Formalism.BasicNotions.TH ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Topology TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_restrictions_vanish : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ σ : Y.d.c₂.F →+* ℂ, GoodEmb Y.d.c₂ σ → ∀ (G : WTZ D.host.E) (x : Y.V G), (∀ k, ∀ z ∈ ((Y.U σ).X k).dom, rdU (Y.U σ) (x : Rul Y.d.Xo₂ Y.d.c₂) k z = 0) → x = 0 := by
  first | exact @GlobalTheory.IntWtRead.cuspW_eq_zero_of_reading | exact GlobalTheory.IntWtRead.cuspW_eq_zero_of_reading | (intros; apply GlobalTheory.IntWtRead.cuspW_eq_zero_of_reading <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantNormalProjectiveCompactification
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

noncomputable section
namespace GlobalTheory.EqModel

theorem isProjOver_pi_const {R : Type} [CommRing R] (κ : Type) [Finite κ] (A : Over (Sp R))
    (h : IsProjOver A.hom) : IsProjOver (∏ᶜ fun _ : κ => A).hom := by
  let n := Nat.card κ
  let e : κ ≃ Fin n := Finite.equivFin κ
  let I₁ : (∏ᶜ fun _ : κ => A) ≅ ∏ᶜ fun _ : Fin n => A := (Pi.reindex e.symm (fun _ : κ => A)).symm
  let I₂ : (∏ᶜ fun _ : Fin n => A) ≅ ReciprocityTheory.ChartRestriction.G.Out.powObj A n :=
    (limit.isLimit _).conePointUniqueUpToIso (ReciprocityTheory.ChartRestriction.G.Out.powIsLimit A n)
  have : IsIso (I₁ ≪≫ I₂).hom.left := ((Over.forget _).mapIso (I₁ ≪≫ I₂)).isIso_hom
  have hp := Models.FamInh.isProjOver_powObj A h n
  have e' := ProjSpace.isProjOver_comp_of_isClosedImmersion (I₁ ≪≫ I₂).hom.left hp
  rwa [Over.w] at e'

theorem isOpenImmersion_toNormalization {V P X : Scheme.{0}} (c : V ⟶ P) (p : P ⟶ X) [IsSeparated p]
    (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact c] [QuasiSeparated c] (h : c ≫ p = j) :
    IsOpenImmersion c.toNormalization := by
  first
  | (rename_i h_5 h_7 h_8 h_9; revert V P X c p h_5 j h_7 h_8 h_9 h; exact @_root_.GlobalTheory.NormalizationOpenImmersion.main)
  | exact @_root_.GlobalTheory.NormalizationOpenImmersion.main
  | exact _root_.GlobalTheory.NormalizationOpenImmersion.main
  | (apply _root_.GlobalTheory.NormalizationOpenImmersion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormalizationOpenImmersion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormalizationOpenImmersion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormalizationOpenImmersion.main ..)

theorem isQProjOver_of_isProjOver' {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : IsQProjOver f := by
  obtain ⟨N, i, _, e⟩ := h
  exact ⟨N, i, inferInstance, inferInstance, e⟩

theorem exists_projective_quotient {F : Type} [Field F] {X : Scheme.{0}} (s : X ⟶ Sp F) {Γ : Type}
    [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (hs : IsProjOver s) (hρ : ∀ g, (ρ g).hom ≫ s = s) :
    ∃ (W : Scheme.{0}) (q : X ⟶ W) (sW : W ⟶ Sp F), IsAffineQuotient ρ q ∧ q ≫ sW = s ∧
      IsProjOver sW ∧ IsFinite q ∧ Surjective q := by
  have := OrbitsInAffineOpens.of_isQProjOver (isQProjOver_of_isProjOver' hs) ρ
  obtain ⟨W, q, hq⟩ := QuotientGluing.exists_isAffineQuotient ρ
  have hqs := hq.comp_desc s hρ
  have : IsProper s := ((isProjOver_iff_isProper_and_exists_isAmpleLB s).1 hs).1
  have : IsProper (q ≫ hq.desc s hρ) := by rw [hqs]; infer_instance
  have : LocallyOfFiniteType (q ≫ hq.desc s hρ) := by rw [hqs]; infer_instance
  have : IsProper (hq.desc s hρ) := hq.isProper _
  obtain ⟨L, hL⟩ := GaloisQuotient.exists_isAmpleLB_of_isAffineQuotient hq
    (isQProjOver_of_isProjOver' hs)
  exact ⟨W, q, hq.desc s hρ, hq, hqs, hL.isProjOver _, hq.isFinite (hq.desc s hρ), hq.surjective⟩

theorem exists_equivariant_model : ∀ (F : Type) [Field F] [NumberField F] (X V : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Sp F) (j : V ⟶ X) [IsOpenImmersion j] (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut V), IsProjOver sX → Nonempty V → GlobalTheory.IsNormalScheme V → (∀ γ, (ρ γ).hom ≫ j ≫ sX = j ≫ sX) → ∃ (X' W : Scheme.{0}) (φ : X' ⟶ X) (ℓ : V ⟶ X') (ρ' : Γ →* Aut X') (q : X' ⟶ W) (sW : W ⟶ Sp F) (_ : IsIntegral X'), GlobalTheory.IsNormalScheme X' ∧ IsProjOver (φ ≫ sX) ∧ IsOpenImmersion ℓ ∧ ℓ ≫ φ = j ∧ (∀ γ, (ρ γ).hom ≫ ℓ = ℓ ≫ (ρ' γ).hom) ∧ IsAffineQuotient ρ' q ∧ q ≫ sW = φ ≫ sX ∧ IsProjOver sW ∧ IsIntegral W ∧ IsFinite q ∧ Surjective q := by
  intro F _ _ X V _ sX j _ Γ _ _ ρ hX hne hN hρ
  classical
  let A : Over (Sp F) := Over.mk sX
  let P : Over (Sp F) := ∏ᶜ fun _ : Γ => A
  let B : Over (Sp F) := Over.mk (j ≫ sX)
  let c : B ⟶ P := Pi.lift fun γ => Over.homMk ((ρ γ).hom ≫ j) (by simpa [A, B] using hρ γ)
  have hcπ (γ : Γ) : c.left ≫ (Pi.π (fun _ : Γ => A) γ).left = (ρ γ).hom ≫ j := by
    rw [← Over.comp_left, Pi.lift_π]; rfl

  let σ₀ (g : Γ) : P ⟶ P := Pi.lift fun γ => Pi.π (fun _ : Γ => A) (γ * g)
  have hσπ (g γ : Γ) : σ₀ g ≫ Pi.π (fun _ : Γ => A) γ = Pi.π (fun _ : Γ => A) (γ * g) :=
    Pi.lift_π _ _
  have hσ (g h : Γ) : σ₀ g ≫ σ₀ h = σ₀ (h * g) :=
    Pi.hom_ext _ _ fun γ => by rw [Category.assoc, hσπ, hσπ, hσπ, mul_assoc]
  have hσ1 : σ₀ 1 = 𝟙 P := Pi.hom_ext _ _ fun γ => by rw [hσπ, mul_one, Category.id_comp]
  let σI (g : Γ) : P.left ≅ P.left :=
    { hom := (σ₀ g).left, inv := (σ₀ g⁻¹).left,
      hom_inv_id := by rw [← Over.comp_left, hσ, inv_mul_cancel, hσ1]; rfl,
      inv_hom_id := by rw [← Over.comp_left, hσ, mul_inv_cancel, hσ1]; rfl }
  let σ : Γ →* Aut P.left := MonoidHom.mk' σI fun g h => Iso.ext (by
    change (σ₀ (g * h)).left = (σ₀ h).left ≫ (σ₀ g).left
    rw [← Over.comp_left, hσ])
  have hσP (g : Γ) : (σ g).hom ≫ P.hom = P.hom := Over.w (σ₀ g)
  have hρmul (g γ : Γ) : (ρ (γ * g)).hom = (ρ g).hom ≫ (ρ γ).hom := by rw [map_mul]; rfl
  have H (g : Γ) : (ρ g).hom ≫ c.left = c.left ≫ (σ g).hom := by
    have e : (Over.homMk (ρ g).hom (by simpa [B] using hρ g) : B ⟶ B) ≫ c = c ≫ σ₀ g :=
      Pi.hom_ext _ _ fun γ => by
        rw [Category.assoc, Category.assoc, hσπ]
        ext1
        simp only [Over.comp_left, hcπ, Over.homMk_left, hρmul, Category.assoc]
    exact congrArg CommaMorphism.left e

  have : IsProper sX := ((isProjOver_iff_isProper_and_exists_isAmpleLB sX).1 hX).1
  have hP : IsProjOver P.hom := isProjOver_pi_const Γ A hX
  have : IsProper P.hom := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hP).1
  have hcP : c.left ≫ P.hom = j ≫ sX := Over.w c
  have hc1 : c.left ≫ (Pi.π (fun _ : Γ => A) 1).left = j := by rw [hcπ, map_one]; rfl
  have : IsSeparated (c.left ≫ P.hom) := by rw [hcP]; infer_instance
  have : QuasiSeparated c.left := .of_comp c.left P.hom
  have : IsSeparated (Pi.π (fun _ : Γ => A) 1).left := by
    have : IsSeparated ((Pi.π (fun _ : Γ => A) 1).left ≫ sX) := Over.w (Pi.π (fun _ : Γ => A) 1) ▸ inferInstance
    exact .of_comp _ sX
  have : IsIntegral V := isIntegral_of_isOpenImmersion j
  have : IsIntegral B.left := ‹IsIntegral V›
  have : GlobalTheory.IsNormalScheme B.left := hN
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := {}
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (j ≫ sX)
  have : CompactSpace V := ⟨by
    rw [j.isOpenEmbedding.isInducing.isCompact_iff, Set.image_univ]
    exact NoetherianSpace.isCompact _⟩
  have : IsNoetherian V := {}
  have : QuasiCompact (c.left ≫ (Pi.π (fun _ : Γ => A) 1).left) := by
    rw [hc1]
    exact quasiCompact_of_noetherianSpace_source j
  have : QuasiCompact c.left := .of_comp c.left (Pi.π (fun _ : Γ => A) 1).left
  have : LocallyOfFiniteType (c.left ≫ P.hom) := by rw [hcP]; infer_instance
  have : LocallyOfFiniteType c.left := locallyOfFiniteType_of_comp c.left P.hom

  have hfin : IsFinite c.left.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType c.left P.hom fun x _ =>
      charZero_of_injective_ringHom
        ((Scheme.ΓSpecIso (.of F)).inv ≫ (j ≫ sX).appTop ≫ V.Γevaluation x).hom.injective
  let φ : c.left.normalization ⟶ X := c.left.fromNormalization ≫ (Pi.π (fun _ : Γ => A) 1).left
  have hφ : φ ≫ sX = c.left.fromNormalization ≫ P.hom := by
    simp only [φ, Category.assoc]
    congr 1
    exact Over.w (Pi.π (fun _ : Γ => A) 1)
  have hproj : IsProjOver (φ ≫ sX) := hφ ▸ isProjOver_comp_of_isFinite _ hP
  have hnorm : GlobalTheory.IsNormalScheme c.left.normalization :=
    IsNormalScheme.normalization_of_isIntegral c.left
  let ρ' := normalizationAction c.left ρ σ H
  have hρ' (g : Γ) : (ρ' g).hom ≫ φ ≫ sX = φ ≫ sX := by
    rw [hφ, normalizationAction_fromNormalization_assoc, hσP]
  obtain ⟨W, q, sW, hq, hqs, hW, hqf, hqs'⟩ := exists_projective_quotient (φ ≫ sX) ρ' hproj hρ'
  refine ⟨c.left.normalization, W, φ, c.left.toNormalization, ρ', q, sW, inferInstance, hnorm, hproj,
    isOpenImmersion_toNormalization c.left (Pi.π (fun _ : Γ => A) 1).left j hc1, ?_,
    fun g => (toNormalization_normalizationAction c.left ρ σ H g).symm, hq, hqs, hW, hq.isIntegral,
    hqf, hqs'⟩
  simp only [φ, Scheme.Hom.toNormalization_fromNormalization_assoc, hc1]

end GlobalTheory.EqModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExOfHodgeWt
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeLin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def offCM (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) : ℤ :=
  if τ (H.rt : E) = H.rt0 then 0 else if conjEmb τ (H.rt : E) = H.rt0 then 1 else 0

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exOf_hodgeWt (Dw : Datum H) :
    GlobalTheory.AllWt.exOf Dw (hodgeWt Dw) 0 = fun ix => ix.elim 0 fun x => offCM H x.1 := by
  funext ix
  rcases ix with _ | ⟨τ, i⟩
  · rfl
  · simp only [GlobalTheory.AllWt.exOf, exZ, GlobalTheory.AllWt.wtOf, Option.elim, offCM, hodgeWt, CompHt.barWt]
    by_cases h : τ (H.rt : E) = H.rt0
    · simp only [dif_pos h, if_pos h]
      split_ifs <;> omega
    · have hm : Dw.mult τ = Dw.q := by simp [Datum.mult, h]
      have hi : (i : ℕ) < Dw.q := lt_of_lt_of_eq i.2 hm
      simp only [dif_neg h, if_neg h]
      by_cases h' : conjEmb τ (H.rt : E) = H.rt0
      · simp only [dif_pos h', if_pos h', dif_pos hi]
        split_ifs <;> omega
      · simp only [dif_neg h', if_neg h']

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def DetEqns (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)]
    (φ₀ : c.F →+* (X₀ TF.Y Z).functionField)
    (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from
      (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι))
    (a : (E →+* ℂ) → ℤ) (D : CartierDiv (X₀ TF.Y Z)) : Prop :=
  ∀ x : X₀ TF.Y Z, ∃ (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x)
    (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from
      (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι))
    (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField)
    (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ),
    (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ ∧
    (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) ∧
    (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from
      (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)
      (fun k => spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k)
      (A τ i) (f₀.v τ i)) ∧
    D.IsEqn x (∏ τ, d τ ^ (-a τ))

section Eqv

def EqvLin {X Y : Scheme.{0}} (t : SAB H Y) (p : X ⟶ Y) {Γ : Type} [Group Γ] (ρ' : Γ →* Aut X) (G' : Over X)
    [GrpObj G'] (ψ : G'.left ⟶ t.G.left) (act' : OAct (𝓞 E) G') (m : Γ → (G'.left ⟶ G'.left)) : Prop :=
  IsGrpPullback G' t.G p ψ ∧ (∀ a, (act'.act a).left ≫ ψ = ψ ≫ (t.act.act a).left) ∧
    (∀ γ, IsGrpPullback G' G' (ρ' γ).hom (m γ)) ∧ (∀ γ a, (act'.act a).left ≫ m γ = m γ ≫ (act'.act a).left) ∧
    (∀ γ₁ γ₂, m (γ₁ * γ₂) = m γ₂ ≫ m γ₁) ∧
    ∀ γ (x : X), X.fromSpecResidueField x ≫ (ρ' γ).hom = X.fromSpecResidueField x →
      ∀ (T : Scheme.{0}) (w : T ⟶ G'.left) (v : T ⟶ Spec (X.residueField x)),
        w ≫ G'.hom = v ≫ X.fromSpecResidueField x → w ≫ m γ = w

end Eqv

end GlobalTheory.HodgeLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactAtOfOneMeasure
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions

set_option synthInstance.maxHeartbeats 400000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.CovTop.MeasRd

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem sgAt_mk_eq {K : Type} [Field K] (σ₀ σ : K →+* ℂ) :
    sgAt σ₀ (InfinitePlace.mk σ) = σ ∨ sgAt σ₀ (InfinitePlace.mk σ) = (starRingEnd ℂ).comp σ := by
  have hc : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
    RingHom.ext fun a => ComplexEmbedding.conjugate_coe_eq σ a
  unfold sgAt
  split_ifs with h
  · rcases InfinitePlace.mk_eq_iff.1 h with h1 | h1
    · exact Or.inl h1.symm
    · right; rw [← h1, hc]
  · rcases InfinitePlace.embedding_mk_eq σ with h1 | h1
    · exact Or.inl h1
    · right; rw [h1, hc]

theorem phiC_congr {T : CoreJ D} {j : ℕ} {σ₁ σ₂ : T.Q.c.F →+* ℂ} (e : σ₁ = σ₂) {W : Formalism.BasicNotions.TH.HSp D}
    (h₁ : T.V j σ₁ = W) (h₂ : T.V j σ₂ = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    phiC T h₁ a f = phiC T h₂ a f := by
  subst e; rfl

end GlobalTheory.CovTop.MeasRd

namespace GlobalTheory.CovTop.MeasRd

open GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes in

theorem exactAt_of_rows {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (hp : p.Rows) (hM : OneMeasure D) (i : Fin D.R.m) : ExactAt p i := by
  intro σ f
  have hTau : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hk : p.κ = kapTop D := KapIs.eq (κ := p.κ) p.fw.kap hTau
  have ha : wtA (p.κ i) = wtA (kapTop D i) := by rw [hk]
  have hn : (p.κ i).n = (kapTop D i).n := by rw [hk]
  have hG : Gk p i = GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i := by unfold Gk GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW; rw [hk]
  obtain ⟨-, hd, h2⟩ := hM _ p.R.toRealDat.toLevCh _ p.charW.base.lev i p.R.toRealDat.triv
  have hmod := p.charW.base.models
  obtain ⟨h0, ht, he, -⟩ := h2 _ _ (hmod.νW i)
  obtain ⟨s, hs_def⟩ : ∃ s, s = sgAt D.what₂.embLL (InfinitePlace.mk σ) := ⟨_, rfl⟩
  have hs := sgAt_mk_eq D.what₂.embLL σ
  rw [← hs_def] at hs
  show ‖(p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) _‖ = _
  rw [← hs_def]

  have hgd : goodOf p.T.Q.c (res p.T s) = goodOf p.T.Q.c (res p.T σ) := by
    rcases hs with h | h
    · rw [h]
    · rw [h]; exact GlobalTheory.CompHt.goodOf_conj (c := p.T.Q.c) (res p.T σ)
  have hgood := goodEmb_goodOf p.T.Q.c (res p.T s)
  have hV : p.T.V ((i : ℕ) + 1) (gd p.T s) = Wc D i := p.fw.laws.spaceW _ (inR i) _ hgood
  obtain ⟨-, hrange, hip⟩ := hmod.HW i s
  by_cases hf0 : f = 0
  · subst hf0
    have hy : ((p.fw.e i 0 : (p.R.toRealDat.FW i).WK) : Fin (p.R.toRealDat.nW i) → D.what₂.LL) = 0 := by
      rw [map_zero]; rfl
    have hz := petW_smul (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i)
      (σ.comp (algebraMap p.T.Q.c.F D.what₂.LL)) 0 0
    rw [map_zero, norm_zero, zero_mul, zero_smul] at hz
    rw [hy, map_zero, norm_zero, ZeroMemClass.coe_zero, hz, mul_zero]
  set y : Fin (p.R.toRealDat.nW i) → D.what₂.LL := ((p.fw.e i f : (p.R.toRealDat.FW i).WK) : Fin (p.R.toRealDat.nW i) → D.what₂.LL)
    with hy
  have hy0 : y ≠ 0 := fun h => hf0 ((p.fw.e i).map_eq_zero_iff.1 (Subtype.ext h))
  set x := (p.R.toRealDat.FW i).j s y with hx_def
  have hx : (p.R.toRealDat.HW i s).e x ∈ p.R.toRealDat.Wall i s := hrange ▸ LinearMap.mem_range_self _ x
  set f' := rdU (p.T.U ((i : ℕ) + 1) (gd p.T s)) (f : p.T.R ((i : ℕ) + 1)) with hf'_def
  have hf' : f' ∈ scalarForms p.T i (gd p.T s) := by
    have := ((mem_cusp _ _ _ _ _ _).1 f.2).2 _ hgood
    show f' ∈ holSub _ (modelWt _ (wtZ (wtA (kapTop D i)) (kapTop D i).n))
    rw [modelWt_wtZ, ← ha, ← hn]
    exact this
  have hc : Corr p.T i s hV ((p.R.toRealDat.HW i s).e x) f' := by
    by_cases hgs : GoodEmb p.T.Q.c (res p.T s)
    · have hgd' : gd p.T s = res p.T s := by show goodOf _ _ = _; rw [goodOf, if_pos hgs]
      have hV' : p.T.V ((i : ℕ) + 1) (res p.T s) = Wc D i := p.fw.laws.spaceW _ (inR i) _ hgs
      have hpre : ∃ j' : (Fin (p.R.toRealDat.nW i) → D.what₂.LL) →ₛₗ[s] (p.R.toRealDat.HW i s).H,
          ∀ g : p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n,
            ((p.R.toRealDat.HW i s).e (j' ((p.fw.e i g : (p.R.toRealDat.FW i).WK) :
              Fin (p.R.toRealDat.nW i) → D.what₂.LL))) (p.v₀ i s) =
              hV' ▸ p.T.phiJ ((i : ℕ) + 1) (res p.T s) (wtA (p.κ i)) (g : p.T.R ((i : ℕ) + 1)) := by
        by_contra hne
        have hj0 := p.fw.ev0 i s hgs hV' hne
        have hli := (hp.prim.unif i s).1 1 (fun _ => y) (linearIndependent_unique_iff.2 hy0)
        rw [hj0] at hli
        exact hli.ne_zero 0 (LinearMap.zero_apply _)
      refine Or.inl ⟨hgs, p.v₀ i s, (p.fw.hv₀ i s).1, ?_⟩
      rw [hf'_def, adFun_rdU]
      refine (p.fw.ev i s hgs hV' hpre f).trans ?_
      show phiC p.T hV' (wtA (p.κ i)) _ = _
      generalize (f : p.T.R ((i : ℕ) + 1)) = F0
      rw [ha]
      exact phiC_congr hgd'.symm _ _ _ _
    · have hgd' : gd p.T s = resC p.T s := by show goodOf _ _ = _; rw [goodOf, if_neg hgs]
      have hVc : p.T.V ((i : ℕ) + 1) (resC p.T s) = Wc D i := p.fw.laws.spaceW _ (inR i) _ (good_resC p.T hgs)
      obtain ⟨v, hv, hvf⟩ := (p.bar i s hgs hVc).1 (hp.jEvBar i s hgs hVc)
      refine Or.inr ⟨hgs, v, hv, ?_⟩
      rw [hf'_def, adFun_rdU]
      refine (hvf f).trans (funext fun g => ?_)
      show starRingEnd ℂ (phiC p.T hVc (wtA (p.κ i)) _ g) = _
      generalize (f : p.T.R ((i : ℕ) + 1)) = F0
      rw [ha, phiC_congr hgd' hV hVc]
  have e := (he p.T p.fw.laws p.fw.alg_eq p.R.toRealDat.θ hmod.inf s (p.R.toRealDat.MW i s) hV _ hx f' hf' hc).2
  rw [← hip, inner_self_eq_norm_sq_to_K] at e
  have e' : ‖x‖ ^ 2 = ratio D i (p.R.toRealDat.νW i) (p.R.toRealDat.fdW i) * probSq p.T i (gd p.T s) f' := by
    have : (((‖x‖ ^ 2 : ℝ)) : ℂ) = _ := (Complex.ofReal_pow _ _).trans e
    exact_mod_cast this
  rw [hf'_def, probSq_rdU] at e'
  unfold petW
  rw [← hgd, hG, ← Real.sqrt_sq (norm_nonneg x), e', Real.sqrt_mul' _ (sq_nonneg _),
    Real.sqrt_sq (petAt_nonneg _ _ _ _ _ _ _)]
  rfl

end GlobalTheory.CovTop.MeasRd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormIndependentTranslatesStatement
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspForm_independent_translates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], IndependentTranslates E := by
  first | exact @GlobalTheory.TranslatesDet.independentTranslates | exact GlobalTheory.TranslatesDet.independentTranslates | (intros; apply GlobalTheory.TranslatesDet.independentTranslates <;> assumption)
end

