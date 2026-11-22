import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfiniteScalarBounds
import Formalism.LocalToGlobal.ExponentGrids.ExponentGridsProofs.NormaliserValuationBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0087
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2153
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2154
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackCartierDivisorBundleEq
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

namespace GlobalTheory.Cartier.PullPres

theorem fnOf_app {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q]
    {U : W.Opens} (h : genericPoint X ∈ q ⁻¹ᵁ U) (a : Γ(W, U)) :
    fnOf (q ⁻¹ᵁ U) h ((q.app U).hom a) =
      functionFieldMap q (fnOf U (gen_mem (x := q (genericPoint X)) h) a) := by
  rw [← algebraMap_germ h, ← algebraMap_germ (show q (genericPoint X) ∈ U from h),
    functionFieldMap_algebraMap, Scheme.Hom.germ_stalkMap_apply]

theorem fnOf_res_pullU {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q]
    {U : W.Opens} {V : X.Opens} (le : V ≤ q ⁻¹ᵁ U) (hV : genericPoint X ∈ V) (u : Γ(W, U)ˣ) :
    fnOf V hV (res le (pullU q U u)).val =
      functionFieldMap q (fnOf U (gen_mem (x := q (genericPoint X)) (le hV)) u.val) :=
  (fnOf_resG le hV _).trans (fnOf_app q (le hV) _)

theorem presents_pull {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q]
    (D : CartierDiv X) (E : CartierDiv W)
    (hDE : ∀ y b, E.IsEqn y b → ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b)) :
    Presents D ((toLB E).pull q) fun J => Units.map (functionFieldMap q).toMonoidHom (J PUnit.unit).1.2 := by
  refine ⟨pull_isLB (isLB_toLB E) q, fun J K h => ?_, fun J x hx => hDE _ _ ((J PUnit.unit).2.2 _ (mem_pull.1 hx)) x rfl⟩
  have le : ((toLB E).pull q).U J ⊓ ((toLB E).pull q).U K ≤
      q ⁻¹ᵁ ((toLB E).U (J PUnit.unit) ⊓ (toLB E).U (K PUnit.unit)) :=
    fun y hy => ⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩
  have hg : ((toLB E).pull q).g J K = res le (pullU q _ ((toLB E).g (J PUnit.unit) (K PUnit.unit))) := by
    simp only [LB.pull, LB.LinComb, Fintype.prod_unique, zpow_one]
    rfl
  rw [hg, fnOf_res_pullU, fnOf_toLB_g]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_div₀]
  exact (div_mul_cancel₀ _ ((map_ne_zero _).2 (Units.ne_zero _))).symm

theorem pull_cls_toLB : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q]
    (D : CartierDiv X) (E : CartierDiv W),
    (∀ y b, E.IsEqn y b → ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b)) →
    CechPic.pull q (cls (toLB E) (isLB_toLB E)) = cls (toLB D) (isLB_toLB D) := by
  intro X W _ _ q _ D E hDE
  rw [← cls_pull (isLB_toLB E) q (pull_isLB (isLB_toLB E) q), ← (presents_pull q D E hDE).toPic_eq,
    toPic_apply]

end GlobalTheory.Cartier.PullPres
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPullbackLineBundleTransitionEqAppLE
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem chartPull_g_appLE : ∀ (Y Y' : Scheme.{0}) (A' : LB Y') (A : LB Y) (h : Y' ⟶ Y) (cp : ChartPull A' A h) (i j : A'.ι), ((A'.g i j : Γ(Y', A'.U i ⊓ A'.U j)ˣ) : Γ(Y', A'.U i ⊓ A'.U j)) = (h.appLE (A.U (cp.idx i) ⊓ A.U (cp.idx j)) (A'.U i ⊓ A'.U j) (le_inf (inf_le_left.trans (cp.le i)) (inf_le_right.trans (cp.le j)))).hom ((A.g (cp.idx i) (cp.idx j) : Γ(Y, A.U (cp.idx i) ⊓ A.U (cp.idx j))ˣ) : Γ(Y, A.U (cp.idx i) ⊓ A.U (cp.idx j))) := by
  intro Y Y' A' A h cp i j
  have e : A'.U i ⊓ A'.U j ≤ h ⁻¹ᵁ (A.U (cp.idx i) ⊓ A.U (cp.idx j)) :=
    le_inf (inf_le_left.trans (cp.le i)) (inf_le_right.trans (cp.le j))
  apply TopCat.Presheaf.section_ext Y'.sheaf (A'.U i ⊓ A'.U j)
  intro y hy
  have h1 := congrArg Units.val (cp.g y i j hy.1 hy.2)
  rw [gm_val _ y _ hy, gm_val h y _ (e hy)] at h1
  refine h1.trans ?_
  show _ = (Y'.presheaf.germ _ y hy).hom ((Y'.presheaf.map (homOfLE e).op).hom ((h.app _).hom _))
  exact (TopCat.Presheaf.germ_res_apply Y'.presheaf _ y hy _).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartStatementHolds
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LineNorm

namespace GlobalTheory.FlatModel

theorem exists_affine_normal_domain {X : Scheme.{0}} [GlobalTheory.IsNormalScheme X] [IsLocallyNoetherian X] (V : X.Opens) {z : X}
    (hz : z ∈ V) : ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : IsDomain Γ(X, U)),
      z ∈ U ∧ U ≤ V ∧ IsIntegrallyClosed Γ(X, U) := by
  have hC : IsOpen (irreducibleComponent z) :=
    GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents z)
  obtain ⟨U, hU, hzU, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := z)
    (U := V ⊓ ⟨irreducibleComponent z, hC⟩) ⟨hz, mem_irreducibleComponent⟩
  have hpre : IsPreirreducible (U : Set X) := (isIrreducible_irreducibleComponent (x := z)).2.open_subset U.2
    fun q hq => (hle hq).2
  have hirr : IsIrreducible (U : Set X) := ⟨⟨z, hzU⟩, hpre⟩
  have : IrreducibleSpace U.toScheme := Subtype.irreducibleSpace hirr
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : IsIntegral U.toScheme := GlobalTheory.IsNormalScheme.isIntegral_of_irreducibleSpace _
  have : Nonempty (Spec Γ(X, U)) := ⟨hU.isoSpec.hom ⟨z, hzU⟩⟩
  have : IsIntegral (Spec Γ(X, U)) := isIntegral_of_isOpenImmersion hU.isoSpec.inv
  have hd : IsDomain Γ(X, U) := (affine_isIntegral_iff _).1 this
  exact ⟨U, hU, hd, hzU, fun q hq => (hle hq).1,
    (GlobalTheory.IsNormalScheme.spec_iff_of_isDomain _).1 (GlobalTheory.IsNormalScheme.spec_of_isAffineOpen hU)⟩

theorem chartSt : ChartSt := by
  intro E _ _ _ H Dw l' Xo' c' W Y p hp hW x
  have hN : GlobalTheory.IsNormalScheme Y.X := (GlobalTheory.isNormalScheme_iff _).2 Y.normal
  have := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff c' hp.ne_zero hW
  have : IsProper Y.s := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  obtain ⟨V, g, e, hxV, he⟩ := exists_affine_isTanBasis E H Y.X Y.t Y.X (𝟙 _) x
  obtain ⟨U, hU, hd, hxU, hle, hic⟩ := exists_affine_normal_domain V.1 hxV
  obtain ⟨ρ, eρ⟩ : ∃ ρ : Γ(Y.X, V.1) →+* Γ(Y.X, U), spMap ρ ≫ V.2.fromSpec = hU.fromSpec :=
    ⟨(Y.X.presheaf.map (homOfLE hle).op).hom, V.2.map_fromSpec hU _⟩
  have hb := isTanBasis_bc he ρ
  rw [Category.comp_id, eρ] at hb
  refine ⟨Γ(Y.X, U), inferInstance, hd, hic, hU.fromSpec, g, _, inferInstance, ?_, hb⟩
  rw [hU.range_fromSpec]
  exact hxU

end GlobalTheory.FlatModel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEllipticCurveIsPureHodgeEndomorphismBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmEllipticCurve_isPureHodgeEndomorphismBaseChange : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Type) [CommRing S] (ω : S) (C : GlobalTheory.CM.Ell H S ω), IsPureBC C.P.A (C.act.act (GlobalTheory.CM.wK H)) (1 - ω) ω := by
  first | exact @GlobalTheory.PureLift.isPureBC_ell | exact GlobalTheory.PureLift.isPureBC_ell | (intros; apply GlobalTheory.PureLift.isPureBC_ell <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeFromConjugateComplement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

namespace GlobalTheory.MassLink

theorem sqrt_d_pos' (D : D7) : 0 < Real.sqrt D.host.d :=
  Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero D.host.hyp.2.1.ne_zero))

theorem tauE_injective' (D : D7) : Function.Injective (TH.tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((Formalism.BasicNotions.factEmb D.R D.host).1.1 h))

theorem conj_tauE_ne' (D : D7) (ρ ρ' : D.what₂.Tau) :
    ComplexEmbedding.conjugate (TH.tauE D ρ) ≠ TH.tauE D ρ' := by
  intro h
  have e := DFunLike.congr_fun h D.host.sqrtMinusD
  rw [ComplexEmbedding.conjugate_coe_eq, Formalism.L2.Theta.tauE_sqrtMinusD, Formalism.L2.Theta.tauE_sqrtMinusD] at e
  have e2 := congrArg Complex.im e
  simp at e2
  have := sqrt_d_pos' D
  linarith

theorem tauE_surj' (D : D7) (φ : D.host.E →+* ℂ)
    (h : φ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ)) : ∃ ρ, TH.tauE D ρ = φ := by
  obtain ⟨g, rfl⟩ := (Formalism.BasicNotions.factEmb D.R D.host).1.2 φ
  exact ⟨D.eTau.symm ⟨g, ((Formalism.BasicNotions.factEmb D.R D.host).2 g).1 h⟩, by unfold TH.tauE; rw [Equiv.apply_symm_apply]⟩

theorem tauE_or' (D : D7) (φ : D.host.E →+* ℂ) :
    ∃ ρ, TH.tauE D ρ = φ ∨ TH.tauE D ρ = ComplexEmbedding.conjugate φ := by
  have h0 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hs : D.host.sqrtMinusD * D.host.sqrtMinusD = -(D.host.d : D.host.E) := by
    apply D.host.φ₀.injective
    rw [map_mul, h0, map_neg, map_natCast, mul_mul_mul_comm, Complex.I_mul_I, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  have h1 : φ D.host.sqrtMinusD * φ D.host.sqrtMinusD =
      (Complex.I * (Real.sqrt D.host.d : ℂ)) * (Complex.I * (Real.sqrt D.host.d : ℂ)) := by
    rw [← map_mul, hs, ← h0, ← map_mul, hs, map_neg, map_neg, map_natCast, map_natCast]
  rcases mul_self_eq_mul_self_iff.1 h1 with h | h
  · obtain ⟨ρ, e⟩ := tauE_surj' D φ h
    exact ⟨ρ, Or.inl e⟩
  · obtain ⟨ρ, e⟩ := tauE_surj' D (ComplexEmbedding.conjugate φ) (by
      rw [ComplexEmbedding.conjugate_coe_eq, h, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring)
    exact ⟨ρ, Or.inr e⟩

open Classical in

theorem psi_cmType_equiv : ∀ D : D7, letI : IsCMField D.host.E := D.host.isCMField_hostE;
    (∀ τ : D.host.E →+* ℂ, τ ∈ GlobalTheory.MassLink.psi D ↔ ComplexEmbedding.conjugate τ ∉ GlobalTheory.MassLink.psi D) ∧
    ∃ eΨ : D.what₂.Tau ≃ GlobalTheory.MassLink.psi D, ∀ ρ, ((eΨ ρ : GlobalTheory.MassLink.psi D) : D.host.E →+* ℂ) = TH.tauE D ρ := by
  intro D
  have mem : ∀ φ : D.host.E →+* ℂ, φ ∈ psi D ↔ ∃ ρ, TH.tauE D ρ = φ := fun φ => by
    simp [psi]
  refine ⟨fun τ => ?_, ?_⟩
  · rw [mem, mem]
    constructor
    · rintro ⟨ρ, rfl⟩ ⟨ρ', h⟩
      exact conj_tauE_ne' D ρ ρ' h.symm
    · intro h
      obtain ⟨ρ, h1 | h1⟩ := tauE_or' D τ
      · exact ⟨ρ, h1⟩
      · exact absurd ⟨ρ, h1⟩ h
  · refine ⟨(Equiv.ofInjective _ (tauE_injective' D)).trans (Equiv.setCongr ?_), fun ρ => rfl⟩
    ext φ
    simp [psi]

end GlobalTheory.MassLink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffValuationLossFinsetSumAndInvPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.LossSum

theorem lossLe_sum_and_pow : ∀ {D : D7} (w : PlL D),
    (∀ {ι : Type} (s : Finset ι) (z : ι → ℂ) (a : ℝ), (∀ i ∈ s, LossLe w (z i) a) → LossLe w (∑ i ∈ s, z i) a) ∧
    ∀ q M : ℕ, 0 < q → LossLe w ((((q : ℝ)⁻¹ ^ M : ℝ)) : ℂ) ((M : ℝ) * (vw w ((q : ℕ) : D.what₂.LL) : ℝ)) := by
  intro D w
  refine ⟨?_, ?_⟩
  · intro ι s z a h
    classical
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp, Or.inl rfl⟩
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      obtain ⟨y1, e1, h1⟩ := h j (Finset.mem_insert_self _ _)
      obtain ⟨y2, e2, h2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      refine ⟨y1 + y2, by rw [map_add, e1, e2], ?_⟩
      by_cases hy1 : y1 = 0
      · subst hy1; simpa using h2
      by_cases hy2 : y2 = 0
      · subst hy2; simpa using h1
      have h1' := h1.resolve_left hy1
      have h2' := h2.resolve_left hy2
      by_cases h3 : y1 + y2 = 0
      · exact Or.inl h3
      right
      have h4 := Formalism.AtG.ValuationJets.vw_add w y1 y2 hy1 hy2 h3
      have h5 : ((min (vw w y1) (vw w y2) : ℤ) : ℝ) ≤ (vw w (y1 + y2) : ℝ) := by exact_mod_cast h4
      push_cast at h5
      exact le_trans (le_min h1' h2') h5
  · intro q M hq
    refine ⟨((q : D.what₂.LL)⁻¹) ^ M, by push_cast; simp, Or.inr ?_⟩
    have hq0 : ((q : D.what₂.LL)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast hq.ne')
    rw [GlobalTheory.ScalAA.vw_pow' w hq0, GlobalTheory.ScalAA.vw_inv']
    push_cast; ring_nf; rfl

end GlobalTheory.LossSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientBoundTupleStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_bound_tuple : GlobalTheory.BigOn.Exp.TupLe.TraceSt := by
  first | exact @GlobalTheory.BigOn.Exp.TupLe.traceSt | exact GlobalTheory.BigOn.Exp.TupLe.traceSt | (intros; apply GlobalTheory.BigOn.Exp.TupLe.traceSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonStatementHolds
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem cmpSt_holds : CmpSt := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle _hov p _ _ T T' i iF hi io y₀ k y hy k' kO hkO hk' yT yyT hT hr
  letI := H.starRing
  letI := io.toAlgebra
  have hxeq := GlobalTheory.CompHt.IsHTFrame.x_eq hy
  obtain ⟨hTest, kO₀, P, ψ₀, z, hP, -, hch⟩ := hy
  obtain ⟨hkO₀, G, t', m₁, m₂, π₀, φ₀, hπ₀, hact₀, hφ₀, hgen₀, hψ₀, hL⟩ := hP
  have tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g →
      ∀ m : SABMap s' s f, ∃ m' : SABMap s' s g, m'.φ = m.φ := by
    intro S S' s s' f g h m
    subst h
    exact ⟨m, rfl⟩

  have hkk : kO₀ = kO.comp i := RingHom.ext fun a => P.integers.hom_inj (by
    rw [hkO₀ a, RingHom.comp_apply, hkO (i a), hi, hk']; rfl)
  have hkk' : k'.comp iF = k.toRingHom := RingHom.ext fun a => hk' a
  have hii : (algebraMap T'.V T'.Fr).comp i = iF.comp (algebraMap T.V T.Fr) := RingHom.ext hi
  have hOO : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO = k'.comp (algebraMap T'.V T'.Fr) := RingHom.ext hkO
  have hx' : yyT ≫ r ≫ pullback.fst _ _ = spMap iF ≫ y₀.1.x := by
    rw [← Category.assoc, hr, Category.assoc]
    congr 1
    exact pullback.lift_fst _ _ _

  obtain ⟨G', ⟨a⟩⟩ := exists_sab (spMap i) G
  obtain ⟨Yt', ⟨b⟩⟩ := exists_sab yT Y.t
  obtain ⟨t₂, ⟨q⟩⟩ := exists_sab yyT Y.oF.t
  obtain ⟨t₁, ⟨c₁⟩⟩ := exists_sab (spMap (algebraMap T'.V T'.Fr)) G'
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν q
  obtain ⟨e₂, he₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m q
  obtain ⟨e₂', he₂'⟩ := tr (show yyT ≫ Y.jQ ≫ pullback.fst _ _ = spMap (algebraMap T'.V T'.Fr) ≫ yT from hT.symm) e₂
  obtain ⟨n₂, hn₂⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ b e₂'
  obtain ⟨e₁, he₁⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ a c₁
  obtain ⟨e₁', he₁'⟩ := tr (show spMap (algebraMap T'.V T'.Fr) ≫ spMap i = spMap iF ≫ spMap (algebraMap T.V T.Fr) by
    rw [spMap_spMap, spMap_spMap, hii]) e₁
  obtain ⟨d, hd⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m₂ e₁'
  obtain ⟨m₁', hm₁'⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₁ d
  obtain ⟨m₁'', hm₁''⟩ := tr hx'.symm m₁'
  obtain ⟨κ, nn, hκ, hnn⟩ := GlobalTheory.sab_extensions_iso E H Dw l Xo T'.V T'.Fr _ G' Yt' t₁ t₂ m₁'' c₁ n₁ n₂

  have w₁ : π₀ ≫ G.G.hom = (P.G.hom ≫ spMap kO) ≫ spMap i := by
    rw [hπ₀.1.w, Category.assoc, spMap_spMap, hkk]
  let π₁ : P.G.left ⟶ G'.G.left := a.cart.1.lift π₀ (P.G.hom ≫ spMap kO) w₁
  have hπ₁a : π₁ ≫ a.φ = π₀ := a.cart.1.lift_fst _ _ _
  have hπ₁s : π₁ ≫ G'.G.hom = P.G.hom ≫ spMap kO := a.cart.1.lift_snd _ _ _
  have hπ₁ : IsGrpPullback P.G G'.G (spMap kO) π₁ :=
    a.cart.cancel (hπ₀.congr (by rw [spMap_spMap, hkk]) hπ₁a.symm) hπ₁s

  have w₂ : φ₀ ≫ t'.G.hom = (P.A.A.hom ≫ spMap k') ≫ spMap iF := by
    rw [hφ₀.1.w, Category.assoc, spMap_spMap, hkk']
  let ψ₁ : P.A.A.left ⟶ t₁.G.left := d.cart.1.lift φ₀ (P.A.A.hom ≫ spMap k') w₂
  have hψ₁d : ψ₁ ≫ d.φ = φ₀ := d.cart.1.lift_fst _ _ _
  have hψ₁s : ψ₁ ≫ t₁.G.hom = P.A.A.hom ≫ spMap k' := d.cart.1.lift_snd _ _ _
  have hψ₁ : IsGrpPullback P.A.A t₁.G (spMap k') ψ₁ :=
    d.cart.cancel (hφ₀.congr (by rw [spMap_spMap, hkk']) hψ₁d.symm) hψ₁s
  have key : ψ₁ ≫ c₁.φ = P.gen ≫ π₁ := by
    apply a.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, hπ₁a, ← he₁, ← he₁', hd, ← Category.assoc, hψ₁d, hgen₀]
    · rw [Category.assoc, Category.assoc, hπ₁s, c₁.cart.1.w, ← Category.assoc, hψ₁s, ← Category.assoc,
        P.gen_pull.1.w, Category.assoc, Category.assoc, spMap_spMap, spMap_spMap, hOO]
  refine ⟨P, π₁ ≫ nn.φ ≫ b.φ, ψ₁ ≫ κ.φ ≫ q.φ, ?_⟩
  have hψν : (ψ₁ ≫ κ.φ ≫ q.φ) ≫ ν.φ = ψ₀ := by
    rw [Category.assoc, Category.assoc, ← hn₁, hκ, hm₁'', hm₁', ← Category.assoc, hψ₁d, hψ₀]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hTest, ?_, z, by rw [hψν]; exact hch⟩
  · rw [← Category.assoc, spMap_spMap, hOO, ← spMap_spMap, Category.assoc, hT, Category.assoc]
  · exact ((hπ₁.comp nn.cart).comp b.cart).congr (by rw [Category.comp_id]) (by rw [Category.assoc])
  · intro a₀
    have h1 : (P.oG.act a₀).left ≫ π₁ = π₁ ≫ (G'.act.act a₀).left := by
      apply a.cart.1.hom_ext
      · rw [Category.assoc, Category.assoc, hπ₁a, hact₀, a.act, ← Category.assoc, hπ₁a]
      · rw [Category.assoc, Category.assoc, hπ₁s, Over.w, hπ₁s, ← Category.assoc, Over.w]
    simp only [Category.assoc, reassoc_of% h1, reassoc_of% (nn.act a₀), b.act a₀]
  · exact ((hψ₁.comp κ.cart).comp q.cart).congr (by rw [Category.comp_id]) (by rw [Category.assoc])
  · have h2 : q.φ ≫ Y.m.φ = n₂.φ ≫ b.φ := by rw [← he₂, ← he₂', hn₂]
    rw [Category.assoc, Category.assoc, h2, ← Category.assoc κ.φ, ← hnn]
    simp only [Category.assoc]
    rw [reassoc_of% key]
  · exact LBIso.trans P.A.isLB (pull_isLB Xo.univ.t.PP.isLB _) (pull_isLB Y.oF.t.PP.isLB _) hL
      (GlobalTheory.LN.GenericPoint.lbIso_pull (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap ν) _ hψν.symm).symm
  · apply pullback.hom_ext
    · rw [ptF, pullback.lift_fst, hxeq, Category.assoc, Category.assoc, hx', ← Category.assoc, spMap_spMap, hkk']
    · rw [ptF, pullback.lift_snd]
      simp only [Category.assoc]
      rw [reassoc_of% hr, ← Category.assoc, spMap_spMap, hkk', ptF, pullback.lift_snd, spMap_spMap]
      congr 1
      exact (RingHom.ext fun x => k.commutes x).symm

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCubeAbelianPointThetaFaceEqPartialSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubHol

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

def pt3 (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) : Sp ℂ ⟶ (G3 D.P.A).left :=
  (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left

def wI (x y z : Fin g → ℂ) (I : thK) : Fin g → ℂ := ∑ a ∈ I.down, ![x, y, z] a

abbrev cubW (D : DegPre R) (j : thK → D.P.L.ι) : (G3 D.P.A).left.Opens :=
  LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j

theorem psum_eA (ν : NumOf D ℂ N) (d : AB N.toNumB g) {n : ℕ} (w : Fin n → Fin g → ℂ) (I : Finset (Fin n)) :
    psum D.P.A (fun k => ν.eA (d.ex (w k))) I = ν.eA (d.ex (∑ i ∈ I, w i)) := by
  have e0 : ν.eA (d.ex 0) = 1 := by
    have h := d.ex_add 0 0
    rw [add_zero] at h
    have h1 : d.ex 0 = 1 := left_eq_mul.mp h
    rw [h1, map_one]
  have hl : ∀ l : List (Fin n),
      l.foldr (fun k acc => padd D.P.A (ν.eA (d.ex (w k))) acc) (pzero D.P.A _) = ν.eA (d.ex (l.map w).sum) := by
    intro l
    induction l with
    | nil =>
      rw [List.foldr_nil, List.map_nil, List.sum_nil, e0, CategoryTheory.Hom.one_def]
      rfl
    | cons k l ih =>
      rw [List.foldr_cons, ih, List.map_cons, List.sum_cons, d.ex_add, map_mul, padd, CategoryTheory.Hom.mul_def]
  have hI : ((List.finRange n).filter (· ∈ I)).toFinset = I := by
    ext i
    simp
  unfold psum
  rw [hl, ← List.sum_toFinset w ((List.nodup_finRange n).filter _), hI]

theorem complexCubeAbelianPoint_thetaFace_eq_partialSum (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) (I : thK) :
    pt3 ν d x y z ≫ thφ D.P.A (x3 D.P.A) I = (ν.eA (d.ex (wI x y z I))).left := by
  have e := psum_hom (preHom (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z))))) (x3 D.P.A) I.down
  have e' : psum D.P.A (fun i => preHom (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))) (x3 D.P.A i))
      I.down = psum D.P.A (fun k => ν.eA (d.ex (![x, y, z] k))) I.down :=
    congrArg (fun q => psum D.P.A q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x3])
  rw [e', psum_eA] at e
  rw [pt3, thφ, ← Over.comp_left]
  exact congrArg (fun q => q.left) e

end GlobalTheory.MBLow.Cl.CubHol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationComponentsCovolumeEq
section
open NumberField

namespace GlobalTheory.EqCovol

theorem covol_eq_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k k' : U.Comp, GlobalTheory.TrueCx.covol (U.X k) = GlobalTheory.TrueCx.covol (U.X k') := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hG hp hq k k'
  obtain ⟨Y, hΨ, hp0, -, -, -, hL, hS, hc⟩ := GlobalTheory.T.exists_fullLevelGroup_data_same_covolume E H Dw l Xo c σ r U hσ hU hG hp hq k
  obtain ⟨Y', hΨ', hp0', -, -, -, hL', hS', hc'⟩ := GlobalTheory.T.exists_fullLevelGroup_data_same_covolume E H Dw l Xo c σ r U hσ hU hG hp hq k'
  obtain ⟨hr, hk, -⟩ := hU
  have hY : ∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0 := fun τ => hΨ ▸ (hk k).2 τ
  have hY' : ∀ τ : E →+* ℂ, τ ∈ Y'.Ψ ↔ τ (H.rt : E) = H.rt0 := fun τ => hΨ' ▸ (hk k').2 τ
  have eΨ : Y'.Ψ = Y.Ψ := Finset.ext fun τ => (hY' τ).trans (hY τ).symm
  have ep : Y'.p0 = Y.p0 := by rw [hp0, hp0', (hk k).1, (hk k').1]
  have h1 : 1 ≤ Y.p0 := by rw [hp0, (hk k).1]; exact hq
  have h2 : Y.p0 < r := by rw [hp0, (hk k).1, hr]; omega
  obtain ⟨Z, hZΨ, hZG, hZξ, hZp, hZL, hZS, hZc⟩ := GlobalTheory.T.exists_transport_selfDual_data_one_hermitianSpace E H l r Y Y' hY eΨ ep h1 h2 hL' hS hS'
  rw [hc, hc', ← hZc]
  exact GlobalTheory.T.covolume_eq_selfDual_lattices_same_hermitian_space E H l r Y Z hG hY hZΨ hZG hZξ hZp h1 h2 hL hZL hS hZS

end GlobalTheory.EqCovol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCoverStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexUniformizationLaws_of_goodDeepCover : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → Laws Y.U (xiR D) := by
  first | exact @GlobalTheory.LawsDeep.laws_deep | exact GlobalTheory.LawsDeep.laws_deep | (intros; apply GlobalTheory.LawsDeep.laws_deep <;> assumption)
end

