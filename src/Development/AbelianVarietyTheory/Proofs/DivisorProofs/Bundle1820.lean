import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1790
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomFamilyOfPureTypeComplexTriple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInversePreservingAdelicLatticeAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0162
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1787
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
import Formalism.PolynomialDimension.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDeterminantLineTwoHermitianLattices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1781
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1786
import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0482
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1500
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerRelationLinearHomsCmSignatureType
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.PureHom

open PureTriple

theorem exists_prod_act_comp_eq_one_of_pure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : ℂ) (A B : PAT H (Sp ℂ)) (p q : ℕ), ρ ^ 2 = -(H.d : ℂ) →
    HasType H A.t.act ρ 1 0 → HasType H B.t.act ρ p q → ∀ (n : ℕ), p + q < n → ∀ ψ : Fin n → (A.t.G ⟶ B.t.G),
    (∀ i, Serre.IsLinearHom A.t.act B.t.act (ψ i)) →
    ∃ x : Fin n → 𝓞 E, x ≠ 0 ∧ ∏ i, (A.t.act.act (x i) ≫ ψ i) = 1 := by
  intro E _ _ _ H ρ A B p q hρ hA hB n hn ψ hψ
  have hT : ThetaUnifAV := thetaUnifAV_all
  have hL : Out.Laws := abelianSchemeLaws_all.1
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := Spec.map_id _
  have hdA := hA ℂ (RingHom.id ℂ) Function.injective_id
  have hdB := hB ℂ (RingHom.id ℂ) Function.injective_id
  rw [hid] at hdA hdB
  simp only [RingHom.id_apply] at hdA hdB
  have hsq : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ^ 2 = -(H.d : ℂ) := fun τ => by
    rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  have key : ∀ (T : PAT H (Sp ℂ)) (a b : ℕ), (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = ρ → LieMult T.t.act (𝟙 (Sp ℂ)) τ a) ∧
      (τ H.rt ≠ ρ → LieMult T.t.act (𝟙 (Sp ℂ)) τ b)) → ∃ a' b' : ℕ, a' + b' = a + b ∧
      ∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ a') ∧
        (τ H.rt ≠ H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ b') := by
    intro T a b hd
    by_cases h0 : ρ = H.rt0
    · exact ⟨a, b, rfl, h0 ▸ hd⟩
    · have h1 := (sq_eq_sq_iff_eq_or_eq_neg.1 (hρ.trans H.sqrt_neg_disc_sq.symm)).resolve_left h0
      have h2 : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ≠ H.rt0 → τ H.rt = ρ := fun τ h =>
        ((sq_eq_sq_iff_eq_or_eq_neg.1 ((hsq τ).trans H.sqrt_neg_disc_sq.symm)).resolve_left h).trans h1.symm
      exact ⟨b, a, add_comm b a, fun τ => ⟨fun h => (hd τ).2 fun h' => h0 (h'.symm.trans h),
        fun h => (hd τ).1 (h2 τ h)⟩⟩
  obtain ⟨pA, qA, hpqA, hdetA⟩ := key A 1 0 hdA
  obtain ⟨pB, qB, hpqB, hdetB⟩ := key B p q hdB
  obtain ⟨gA, tyA, htyA⟩ := AllClasses.exists_isTypeFn H pA qA
  obtain ⟨gB, tyB, htyB⟩ := AllClasses.exists_isTypeFn H pB qB
  obtain ⟨uA, HA, χA, -, hAH, -⟩ := PureType.exists_isThetaUnif hT A.pol
  obtain ⟨uB, HB, χB, -, hBH, -⟩ := PureType.exists_isThetaUnif hT B.pol
  obtain ⟨DA, PeA, FA, hpA, hqA, hPA, hFA, -, hactA⟩ := exists_datum_period hT hL A htyA hdetA uA hAH
  obtain ⟨DB, PeB, FB, hpB, hqB, hPB, hFB, -, hactB⟩ := exists_datum_period hT hL B htyB hdetB uB hBH
  obtain ⟨-, -, -, -, -, hA2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT A.pol _ uA HA χA hAH
  obtain ⟨-, -, -, -, hB1, hB2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT B.pol _ uB HB χB hBH
  choose Ψ hΨ hΨΛ using fun i => (HomLinear.exists_linear_of_isMonHom A.t.G B.t.G A.ab B.ab _ _ _ _ uA uB hB1 hB2
    (ψ i) (hψ i).isMonHom).imp fun _ h => And.intro h.1 h.2.1
  let GA : 𝓞 E → (Fin A.pol.g → ℂ) →ₗ[ℂ] (Fin A.pol.g → ℂ) := fun s =>
    FA.toLinearMap ∘ₗ diagMul tyA (s : E) ∘ₗ FA.symm.toLinearMap
  let GB : 𝓞 E → (Fin B.pol.g → ℂ) →ₗ[ℂ] (Fin B.pol.g → ℂ) := fun s =>
    FB.toLinearMap ∘ₗ diagMul tyB (s : E) ∘ₗ FB.symm.toLinearMap
  have hGA : ∀ s z, uA.ex (GA s z) = uA.ex z ≫ A.t.act.act s := fun s z => by
    have e := hactA s (FA.symm z)
    rw [FA.apply_symm_apply] at e
    exact e
  have hGB : ∀ s z, uB.ex (GB s z) = uB.ex z ≫ B.t.act.act s := fun s z => by
    have e := hactB s (FB.symm z)
    rw [FB.apply_symm_apply] at e
    exact e
  have hGPA : ∀ s a, GA s (FA (PeA a)) = FA (PeA (s • a)) := fun s a => by
    simp only [GA, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    congr 1
    funext k
    simp only [diagMul, LinearMap.coe_mk, AddHom.coe_mk, hPA.1]
  have hGPB : ∀ s b, GB s (FB (PeB b)) = FB (PeB (s • b)) := fun s b => by
    simp only [GB, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    congr 1
    funext k
    simp only [diagMul, LinearMap.coe_mk, AddHom.coe_mk, hPB.1]
  have hGAc : ∀ r s z, GA r (GA s z) = GA s (GA r z) := fun r s z => by
    simp only [GA, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    congr 1
    funext k
    simp only [diagMul, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  have hGBinj : ∀ r : 𝓞 E, r ≠ 0 → ∀ z, GB r z = 0 → z = 0 := fun r hr z hz => by
    have hr' : (r : E) ≠ 0 := by exact_mod_cast hr
    have e : diagMul tyB (r : E) (FB.symm z) = 0 := by
      have := congrArg FB.symm hz
      simpa [GB] using this
    have e' : FB.symm z = 0 := funext fun k => by
      have := congrFun e k
      simp only [diagMul, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, mul_eq_zero] at this
      exact this.resolve_left ((map_ne_zero (tyB k)).2 hr')
    simpa using congrArg FB e'
  have hcomm : ∀ i s z, Ψ i (GA s z) = GB s (Ψ i z) := by
    intro i s z
    haveI := (hψ i).isMonHom
    haveI := A.t.act.hom s
    have e := linear_lift_unique uA uB hA2 hB1 (A.t.act.act s ≫ ψ i) (F := Ψ i ∘ₗ GA s) (F' := GB s ∘ₗ Ψ i)
      (fun z => by rw [LinearMap.comp_apply, hΨ, hGA, Category.assoc])
      (fun z => by rw [LinearMap.comp_apply, hGB, hΨ, (hψ i).comm, Category.assoc])
    exact LinearMap.congr_fun e z
  have := DA.fin
  have := DA.proj
  have := DB.fin
  have := DB.proj
  have hrkA : Module.finrank (𝓞 E) DA.La = 1 := by rw [DA.rank, hpA, hqA, hpqA]
  haveI : Nontrivial DA.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [hrkA]; exact one_pos)
  obtain ⟨a, ha⟩ := exists_ne (0 : DA.La)
  have hb : ∀ i, ∃ b : DB.La, Ψ i (FA (PeA a)) = FB (PeB b) := fun i => by
    have hm : Ψ i (FA (PeA a)) ∈ uB.Λ := hΨΛ i _ ((hFA _).2 ⟨a, rfl⟩)
    obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.1 ((hFB (FB.symm _)).1 (by rwa [FB.apply_symm_apply]))
    exact ⟨b, by rw [hb, FB.apply_symm_apply]⟩
  choose b hb using hb
  have hrkB : Module.finrank (𝓞 E) DB.La = p + q := by rw [DB.rank, hpB, hqB, hpqB]
  have hni : ¬ LinearIndependent (𝓞 E) b := fun hi => by
    have := hi.fintype_card_le_finrank
    rw [Fintype.card_fin, hrkB] at this
    omega
  obtain ⟨x, hx, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hni
  refine ⟨x, fun h => hi₀ (by rw [h]; rfl), ?_⟩
  let Θ : (Fin A.pol.g → ℂ) →ₗ[ℂ] (Fin B.pol.g → ℂ) := ∑ i, Ψ i ∘ₗ GA (x i)
  have hΘ : ∀ z, Θ z = ∑ i, Ψ i (GA (x i) z) := fun z => by
    simp only [Θ, LinearMap.sum_apply, LinearMap.comp_apply]
  have hΘa : Θ (FA (PeA a)) = 0 := by
    rw [hΘ]
    calc ∑ i, Ψ i (GA (x i) (FA (PeA a))) = ∑ i, FB (PeB (x i • b i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hcomm, hb, hGPB]
      _ = 0 := by rw [← map_sum, ← map_sum, hx, map_zero, map_zero]
  have hΘc : ∀ s z, Θ (GA s z) = GB s (Θ z) := fun s z => by
    rw [hΘ, hΘ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hGAc, hcomm]
  have hΘl : ∀ a', Θ (FA (PeA a')) = 0 := fun a' => by
    obtain ⟨r, s, hr, e⟩ := CMLat.exists_smul_eq_smul hrkA ha a'
    refine hGBinj r hr _ ?_
    rw [← hΘc, hGPA, e, ← hGPA, hΘc, hΘa, map_zero]
  have hΘ0 : Θ.restrictScalars ℝ = 0 := by
    refine LinearMap.ext_on uA.full fun z hz => ?_
    obtain ⟨a', ha'⟩ := AddMonoidHom.mem_range.1 ((hFA (FA.symm z)).1 (by rwa [FA.apply_symm_apply]))
    have ez : z = FA (PeA a') := by rw [ha', FA.apply_symm_apply]
    rw [ez]
    exact hΘl a'
  have hΘz : ∀ z, Θ z = 0 := fun z => LinearMap.congr_fun hΘ0 z
  have hs : Smooth A.t.G.hom := A.ab.smooth
  have hp : IsProper B.t.G.hom := B.ab.proper
  have hr : IsReduced A.t.G.left := isReduced_of_smooth_complex _ A.t.G.hom hs
  refine ComplexPoints.over_hom_ext_of_complexPoints fun y => ?_
  obtain ⟨z, rfl⟩ := uA.ex_onto y
  have hpr : ∀ s : Finset (Fin n), uA.ex z ≫ ∏ i ∈ s, (A.t.act.act (x i) ≫ ψ i) =
      uB.ex (∑ i ∈ s, Ψ i (GA (x i) z)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty, comp_one]; exact ((uB.ker 0).2 uB.Λ.zero_mem).symm
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, comp_mul, ih, uB.ex_add, hΨ, hGA, Category.assoc]
  rw [hpr, ← hΘ, hΘz, comp_one]
  exact (uB.ker 0).2 uB.Λ.zero_mem

end GlobalTheory.CM.PureHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInversePreservingAdelicLatticeAtPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inverse_preserving_adelicLatticeAtPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d),
    W.L.IsLattice E → ∀ (v : Pl F) (p : ℕ), (p : 𝓞 F) ∈ v.asIdeal → ∀ c : AF F, IsUnit c →
    ∀ M : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) (M - c • (1 : Matrix (Fin d) (Fin d) (AE F E))) →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, ∃ y ∈ GlobalTheory.InertSph.latAt W v, ∃ y' ∈ GlobalTheory.InertSph.latAt W v, z = M *ᵥ y + p • y') →
    ∃ M' : Matrix (Fin d) (Fin d) (AE F E), M * M' = 1 ∧ M' * M = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, M' *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  first | exact @GlobalTheory.InertSph.exists_inv_keeps_latAt | exact GlobalTheory.InertSph.exists_inv_keeps_latAt | (intros; apply GlobalTheory.InertSph.exists_inv_keeps_latAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryPosDefHermitianSameRank
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BottomIsom

theorem hasSignature_map_star {n p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature M p q) :
    Formalism.UG.HasSignature (M.map (starRingEnd ℂ)) p q := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨e, Matrix.GeneralLinearGroup.map (starRingEnd ℂ) P, ?_⟩
  have := congrArg (fun A => Matrix.map A (starRingEnd ℂ)) hP
  simp only [Matrix.map_mul] at this
  have hJ : (Formalism.UG.Jpq p q : Matrix _ _ ℂ).map (starRingEnd ℂ) = Formalism.UG.Jpq p q := by
    ext (a | a) (b | b) <;> simp [Formalism.UG.Jpq, Matrix.one_apply, apply_ite]
  rw [hJ] at this
  exact this

theorem hasSignature_all {D : D7} {V : HSp D} (h : NegIdx V 0) (σ : D.host.E →+* ℂ) :
    Formalism.UG.HasSignature (V.gram.map σ) V.rank 0 := by
  obtain ⟨τ, hσ | hσ⟩ := GlobalTheory.DefiniteMult.exists_tauE_or_conj D σ
  · subst hσ
    simpa [gramAt] using h τ
  · subst hσ
    have h1 := hasSignature_map_star (by simpa [gramAt] using h τ)
    rw [Matrix.map_map] at h1
    exact h1

def posResign {D : D7} (V : HSp D) : HSp D := { V with sig := fun _ => (V.rank, 0) }

theorem posResign_sigOK {D : D7} {V : HSp D} (h : NegIdx V 0) : (posResign V).SigOK := fun σ =>
  hasSignature_all h σ

theorem isoMat_of_posDef : ∀ {D : D7} {V V' : HSp D}, V.rank = V'.rank → NegIdx V 0 → NegIdx V' 0 →
    Nonempty (GlobalTheory.Mem.Isom.IsoMat V V') := by
  intro D V V' hr h h'
  obtain ⟨φ, hφ⟩ := GlobalTheory.LandherrSignature.exists_isometry_host D (posResign V) (posResign V')
    (posResign_sigOK h) (posResign_sigOK h') hr (fun _ => by simp [posResign, hr])
  exact ⟨GlobalTheory.Mem.Isom.IsoMat.ofEquiv φ hφ⟩

end GlobalTheory.BottomIsom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalBasisLatticeOfInverseAdelicMatrixFamiStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localBasis_lattice_of_inverse_adelicMatrixFamily : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (A : HeightOneSpectrum (𝓞 K) → Matrix (Fin n) (Fin n) K), IsAdelic A → ∀ P : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ P.asIdeal ∧ GlobalTheory.PtDeg.LocBasis P (locLat A) (fun j => (s : K) • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K))) := by
  first | exact @GlobalTheory.LocMatBasis.exists_locBasis_inv | exact GlobalTheory.LocMatBasis.exists_locBasis_inv | (intros; apply GlobalTheory.LocMatBasis.exists_locBasis_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorOfNonzeroIdeal
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

open IsDedekindDomain HeightOneSpectrum WithZero

theorem locGen_val_eq (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F) :
    Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) = v.intValuation d := by
  have h := valuedAdicCompletion_eq_valuation' (K := F) v (d : F)
  rw [← valuation_of_algebraMap (K := F) v d]
  exact h

theorem ideal_localGenerator : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), I ≠ ⊥ → ∃ z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v, z ≠ 0 ∧ (¬ I ≤ v.asIdeal → z = 1) ∧ (∀ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) ≤ Valued.v z) ∧ ∃ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) = Valued.v z := by
  intro F _ _ I v hI
  by_cases hv : I ≤ v.asIdeal
  · classical
    have hex : ∃ n : ℕ, ∃ d ∈ I, v.intValuation d = exp (-(n : ℤ)) := by
      obtain ⟨d, hdI, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      exact ⟨_, d, hdI, v.intValuation_if_neg hd0⟩
    obtain ⟨d0, hd0I, hd0v⟩ := Nat.find_spec hex
    refine ⟨algebraMap F _ (d0 : F), ?_, fun h => absurd hv h, ?_, d0, hd0I, rfl⟩
    · intro h
      have h2 := locGen_val_eq F v d0
      rw [h, map_zero, hd0v] at h2
      exact exp_ne_zero h2.symm
    · intro d hd
      rw [locGen_val_eq, locGen_val_eq, hd0v]
      by_cases hd0 : d = 0
      · simp [hd0]
      · have hk := v.intValuation_if_neg hd0
        rw [hk, exp_le_exp, neg_le_neg_iff, Int.ofNat_le]
        exact Nat.find_min' hex ⟨d, hd, hk⟩
  · obtain ⟨d, hdI, hdv⟩ := Set.not_subset.mp hv
    refine ⟨1, one_ne_zero, fun _ => rfl, ?_, d, hdI, ?_⟩
    · intro e _
      rw [locGen_val_eq, map_one]
      exact v.intValuation_le_one e
    · rw [locGen_val_eq, map_one]
      exact intValuation_eq_one_iff.mpr hdv

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaxLevelUnitaryCongrModIdeal
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.FunObj.SqNum GlobalTheory.NormSum

noncomputable section

namespace GlobalTheory.MaxLevelLift

theorem exists_intG_cong : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (N : ℕ)
    (g : Matrix (Fin N) (Fin N) (𝓞 D.host.E)), IsUnit (g.map (Ideal.Quotient.mk 𝔪)).det →
      ∃ k : GA D N, k ∈ intG D N ∧ ∀ i j : Fin N,
        ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j - inc D ((g i j : 𝓞 D.host.E) : D.host.E) ∈ hatId D 𝔪 := by
  intro D 𝔪 _ hcop N g hg
  have hcc : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun z => GlobalTheory.NormSum.UnramHecke.conj_conj D z
  have e : D.host.conj • D.host.conj • 𝔪 = 𝔪 := by rw [smul_smul, hcc, one_smul]
  have hdet : (g.map (Ideal.Quotient.mk 𝔪)).det = Ideal.Quotient.mk 𝔪 g.det :=
    ((Ideal.Quotient.mk 𝔪).map_det g).symm
  rw [hdet] at hg
  obtain ⟨v, hv⟩ := hg.exists_right_inv
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective v
  rw [← map_mul, ← map_one (Ideal.Quotient.mk 𝔪), Ideal.Quotient.eq] at hv
  have key : inc D ((g.det * u : 𝓞 D.host.E) : D.host.E) - 1 ∈ hatId D (D.host.conj • D.host.conj • 𝔪) := by
    rw [e]
    exact AddSubgroup.subset_closure ⟨g.det * u - 1, hv, 1, one_mem _, by simp⟩
  obtain ⟨f, hf, w, hw, hff, hfs, hfw, h1f⟩ :=
    GlobalTheory.BotPairSmall.IdemChoice.exists_idem_of_limit GlobalTheory.AlgIntIdem.idem D (D.host.conj • 𝔪)
      (by rw [e, sup_comm]; exact hcop) _ _ key
  rw [e] at h1f
  obtain ⟨k, hk, hkc⟩ := GlobalTheory.GlueUnitary.glue_unitary D 𝔪 N g f w hf hw hff hfs hfw h1f
  refine ⟨k⁻¹, inv_mem hk, fun i j => ?_⟩
  have := neg_mem (hkc i j)
  rwa [Matrix.sub_apply, neg_sub, Matrix.map_apply] at this

end GlobalTheory.MaxLevelLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMeasY
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TupExt

open Formalism.IndefR.Lev Formalism.IndefR.Cx

scoped macro "obt " p:Lean.Parser.Tactic.rcasesPatMed " := " e:term : tactic => `(tactic| (have x := $e; obtain $p := x))

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem exists_measY (t : T) (j : ℕ) : ∃ (μ : Measure (GA D (Yc D j))) (𝓕 : Set (GA D (Yc D j))),
    (j + 1 < D.R.m → IsMeasFD (Yc D j) (lev D.sp.cm (Yc D j).gram (R.βY j) (R.datYt t j R.triv)) μ 𝓕) ∧
    (j = D.R.m - 1 → IsMeasDef (Yc D j) (lev D.sp.cm (Yc D j).gram (R.βY j) (R.datYt t j R.triv)) μ 𝓕) := by
  have hLev := GlobalTheory.Mem.LevelOK.levOK_all D
  by_cases hj : j = D.R.m - 1
  · subst hj
    obtain ⟨μ, 𝓕, hμ⟩ := measDef_exists (Formalism.IndefR.Eqv.measLevDefExists_holds D) (Formalism.IndefR.Eqv.fundDomExists_holds D)
      (Yc D (D.R.m - 1)) _ (D.sp.Y_sig _) (GlobalTheory.Mem.EasyInputs.spOK D).1
      (hLev _ (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv)).1
    exact ⟨μ, 𝓕, fun h2 => absurd h2 (by omega), fun _ => hμ⟩
  · obtain ⟨μ, 𝓕, hμ⟩ := Formalism.IndefR.Eqv.measFDExists_holds D (Yc D j) (D.sp.Y_sig _) _ (hLev _ (R.βY j) (R.datYt t j R.triv)).1
    exact ⟨μ, 𝓕, fun _ => hμ, fun h' => absurd h' hj⟩

theorem exists_measX (t : T) : ∃ μ 𝓕, IsMeasDef D.sp.X' (lev D.sp.cm D.sp.X'.gram R.βX (R.datXt t)) μ 𝓕 :=
  measDef_exists (Formalism.IndefR.Eqv.measLevDefExists_holds D) (Formalism.IndefR.Eqv.fundDomExists_holds D) D.sp.X' _ D.sp.X'_sig
    (GlobalTheory.Mem.EasyInputs.spOK D).2 (GlobalTheory.Mem.LevelOK.levOK_all D _ R.βX (R.datXt t)).1

theorem exists_measV (hv : ∀ i, (Vc D i).IsPosDef) (i : Fin D.R.m) (t : T) :
    ∃ μ 𝓕, IsMeasDef (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t)) μ 𝓕 :=
  measDef_exists (Formalism.IndefR.Eqv.measLevDefExists_holds D) (Formalism.IndefR.Eqv.fundDomExists_holds D) (Vc D i) _ (D.sp.V_sig _)
    (fun τ => Or.inl (hv i τ)) (GlobalTheory.Mem.LevelOK.levOK_all D _ (R.βV i) (R.datVt i t)).1

set_option maxHeartbeats 1000000 in

theorem exists_modX (t : T) : ∃ (H : HMod (Bridge.Gf D.sp.X' → R.cX.W)) (j : A.fam.amb.FR t →ₛₗ[D.what₂.embLL] H.H),
    H.Is (Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv _ R.βX (R.datXt t)).J (levEnv _ R.βX (R.datXt t)).χ)
      (Bridge.adInner (Bridge.ratF D.sp.X') (levEnv _ R.βX (R.datXt t)).J (R.B.R t).pres.y) ∧ ∀ x, H.e (j x) = R.B.jR t x := by
  have herm : Formalism.IndefR.PeterssonHilbertSpace.IsHermPos (Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv _ R.βX (R.datXt t)).J
      (levEnv _ R.βX (R.datXt t)).χ) (Bridge.adInner (Bridge.ratF D.sp.X') (levEnv _ R.βX (R.datXt t)).J (R.B.R t).pres.y) :=
    hermPos_of_ipOn (Bridge.adInner_ipOn (W := R.cX.W) (R.B.R t).pres.reps (fun c => by
      exact ne_of_eq_of_ne ((R.B.R t).pres.card_stab c) (Nat.pos_iff_ne_zero.mp (by apply Formalism.L2.DIV.CSD.wt_pos))))
  refine (hMod_of_herm herm).elim fun H hH => ?_
  have x := hMod_lift hH (R.B.jR t) (fun x => by exact (R.B.R t).pres.extMem_holds x)
  refine x.elim fun j hj => ⟨H, j, hH, ?_⟩
  exact (hj)

set_option maxHeartbeats 1000000 in

theorem exists_modV (i : Fin D.R.m) (t : T) :
    ∃ (H : HMod (Bridge.Gf (Vc D i) → (R.cV i).W)) (j : A.fam.amb.FL i t →ₛₗ[D.what₂.embLL] H.H),
    H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
        (levEnv _ (R.βV i) (R.datVt i t)).χ)
      (Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y) ∧
    ∀ x, H.e (j x) = R.B.jL i t x := by
  have herm : Formalism.IndefR.PeterssonHilbertSpace.IsHermPos (Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
      (levEnv _ (R.βV i) (R.datVt i t)).χ)
      (Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y) :=
    hermPos_of_ipOn (Bridge.adInner_ipOn (W := (R.cV i).W) (R.B.L i t).pres.reps (fun c => by
      exact ne_of_eq_of_ne ((R.B.L i t).pres.card_stab c) (Nat.pos_iff_ne_zero.mp (by apply Formalism.L2.DIV.CSD.wt_pos))))
  refine (hMod_of_herm herm).elim fun H hH => ?_
  have x := hMod_lift hH (R.B.jL i t) (fun x => by exact (R.B.L i t).pres.extMem_holds x)
  refine x.elim fun j hj => ⟨H, j, hH, ?_⟩
  exact (hj)

variable {R}

open Classical in
theorem idem_of_is {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (t : T) :
    Disjoint L.Pg (L.Q t) ∧ ∃ e : AE D, IsIdemSum e (L.Pg ∪ L.Q t) :=
  ⟨(GlobalTheory.ChainEquiv.places_sep L μ0 hL t).2, GlobalTheory.CentralShift.exists_idemSum _ fun _ hP _ hP' =>
    GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL t (Finset.mem_union.1 hP) (Finset.mem_union.1 hP')⟩

theorem sd_of_frame {V : HSp D} {β Λ N} (h : IsSDFrame V β Λ N) : IsSelfDualC V Λ ∧ IsFrame β Λ := by
  obtain ⟨c, hc⟩ := h
  exact ⟨GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hc, hc.1⟩

theorem exists_kerY (hL : R.toLevCh.Is A.μ0) (hψ : IsStdChar D R.ψ (-1)) (t : T) (k : ℕ)
    (hv : k + 1 < D.R.m → IsVacO R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) (R.ΛY k) (R.ΛY (k + 1)) (R.vac k)) :
    ∃ ω v, k + 1 < D.R.m → IsWeilDatumO R.ψ (Yc D k) (Yc D (k + 1)) (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 ω ∧
      IsStepVecOf R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) (R.ΛY k) (R.ΛY (k + 1))
        (R.βY k) (R.βY (k + 1)) (R.datYt t k R.triv) (R.chi (k + 1)) (R.Q t) (R.xiR t) (R.vac k) v := by
  by_cases hk : k + 1 < D.R.m
  · have hs := (GlobalTheory.HeckeCharacterRestriction.splitFacts hL t).1 k hk
    obtain ⟨ω, hω⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D R.ψ hψ (Yc D k) (Yc D (k + 1)) _ _
      (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    have s1 := sd_of_frame (hL.βY k (by omega))
    have s2 := sd_of_frame (hL.βY (k + 1) hk)
    obtain ⟨v, hv'⟩ := GlobalTheory.PlaceDatum.stepVecExists D R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) (R.ΛY k)
      (R.ΛY (k + 1)) (R.βY k) (R.βY (k + 1)) (R.datYt t k R.triv) (R.chi (k + 1)) (R.Q t) (R.xiR t) s1.1 s2.1 s1.2 s2.2
      (idem_of_is hL t).1 (idem_of_is hL t).2 (R.vac k) (hv hk)
    exact ⟨ω, v, fun _ => ⟨hω, hv'⟩⟩
  · exact ⟨1, 0, fun h => absurd h hk⟩

theorem exists_kerX (hL : R.toLevCh.Is A.μ0) (hψ : IsStdChar D R.ψ (-1)) (t : T)
    (hv : IsVacO R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (R.MY (D.R.m - 1))) (cart R.MX) (R.ΛY (D.R.m - 1)) R.ΛX R.vacX) :
    ∃ ω v, IsWeilDatumO R.ψ (Yc D (D.R.m - 1)) D.sp.X' (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).2 ω ∧
      IsStepVecOf R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (R.MY (D.R.m - 1))) (cart R.MX) (R.ΛY (D.R.m - 1)) R.ΛX
        (R.βY (D.R.m - 1)) R.βX (R.datYt t (D.R.m - 1) R.triv) (R.chi D.R.m) (R.Q t) (R.xiR t) R.vacX v := by
  have hm : D.R.m - 1 < D.R.m := Nat.sub_lt (lt_of_lt_of_le two_pos D.R.two_le_m) one_pos
  have hs := (GlobalTheory.HeckeCharacterRestriction.splitFacts hL t).2.1
  obtain ⟨ω, hω⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D R.ψ hψ (Yc D (D.R.m - 1)) D.sp.X' _ _
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  have s1 := sd_of_frame (hL.βY _ hm)
  have s2 := sd_of_frame hL.βX
  obtain ⟨v, hv'⟩ := GlobalTheory.PlaceDatum.stepVecExists D R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (R.MY (D.R.m - 1))) (cart R.MX)
    (R.ΛY (D.R.m - 1)) R.ΛX (R.βY (D.R.m - 1)) R.βX (R.datYt t (D.R.m - 1) R.triv) (R.chi D.R.m) (R.Q t) (R.xiR t) s1.1 s2.1 s1.2 s2.2
    (idem_of_is hL t).1 (idem_of_is hL t).2 R.vacX hv
  exact ⟨ω, v, hω, hv'⟩

theorem exists_kerP (hL : R.toLevCh.Is A.μ0) (hψ : IsStdChar D R.ψ (-1)) (i : Fin D.R.m) (t : T)
    (hv : IsVacO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.vacP i)) :
    ∃ ω v, IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 ω ∧
      IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
        R.Pg (R.Q t) (R.xiR t) (R.vacP i) v := by
  have hs := (GlobalTheory.HeckeCharacterRestriction.splitFacts hL t).2.2 i
  obtain ⟨ω, hω⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D R.ψ hψ (Vc D i) (Wc D i) _ _
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  have s1 := sd_of_frame (hL.βV i)
  have s2 := sd_of_frame (hL.βW i)
  obtain ⟨v, hv'⟩ := GlobalTheory.PlaceVec.thPVecExists D R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i)
    (R.βV i) (R.βW i) R.Pg (R.Q t) (R.xiR t) s1.1 s2.1 s1.2 s2.2 (idem_of_is hL t).1 (idem_of_is hL t).2 (R.vacP i) hv
  exact ⟨ω, v, hω, hv'⟩

end GlobalTheory.TupExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightSlabSubsetUnipotentLeviCompactStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heightSlab_subset_unipotent_levi_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ b, IsFlowJ σ J X Y b → ∃ C : Set (GAd σ J), IsCompact C ∧ ∀ g, Real.exp (-1) ≤ h g → h g ≤ 1 → ∃ u ∈ unipRad σ J X, ∃ m ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∃ y ∈ C, g = u * m * y := by
  first | exact @GlobalTheory.ResidueEisenstein.slab_subset | exact GlobalTheory.ResidueEisenstein.slab_subset | (intros; apply GlobalTheory.ResidueEisenstein.slab_subset <;> assumption)
end

