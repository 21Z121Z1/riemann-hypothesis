import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1662
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0050
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.Bundle0001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1658
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1664
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitsHolds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFundamentalDomainTsumRationalTranslatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_fundamentalDomain_tsum_rationalTranslates : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AF F) := borel _
    ∀ (μ : MeasureTheory.Measure (κ → AF F)), μ.IsAddHaarMeasure →
    ∀ 𝓕₁ : Set (κ → AF F), MeasureTheory.IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) 𝓕₁ μ → μ 𝓕₁ ≠ ⊤ →
    ∀ h : (κ → AF F) → ℂ, Continuous h →
      (∃ B : ℝ, ∀ x : κ → AF F, Summable (fun η : κ → F => ‖h ((fun i => algebraMap F (AF F) (η i)) + x)‖) ∧
        ∑' η : κ → F, ‖h ((fun i => algebraMap F (AF F) (η i)) + x)‖ ≤ B) →
      ∫ x in 𝓕₁, ∑' η : κ → F, h ((fun i => algebraMap F (AF F) (η i)) + x) ∂μ = ∫ u, h u ∂μ := by
  first | exact @GlobalTheory.ThetaUnfoldInt.integral_fundamentalDomain_tsum | exact GlobalTheory.ThetaUnfoldInt.integral_fundamentalDomain_tsum | (intros; apply GlobalTheory.ThetaUnfoldInt.integral_fundamentalDomain_tsum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRatPairFundamentalDomainAdelicIteratedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_ratPairFundamentalDomain_adelic_iterated : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AF F) := borel _
    letI : MeasurableSpace ((κ → AF F) × (κ → AF F)) := borel _
    ∀ (μ : MeasureTheory.Measure (κ → AF F)), μ.IsAddHaarMeasure →
    ∀ (lam : MeasureTheory.Measure ((κ → AF F) × (κ → AF F))), lam.IsAddHaarMeasure →
    ∀ 𝓖 : Set ((κ → AF F) × (κ → AF F)),
      MeasureTheory.IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) 𝓖 lam →
    ∀ 𝓕₁ : Set (κ → AF F), MeasureTheory.IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) 𝓕₁ μ → μ 𝓕₁ ≠ ⊤ →
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ G : (κ → AF F) × (κ → AF F) → ℂ, Measurable G →
      (∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w, G (γ + w) = G w) → (∃ B : ℝ, ∀ w, ‖G w‖ ≤ B) →
      ∫ w in 𝓖, G w ∂lam = c₁ * ∫ x in 𝓕₁, ∫ y in 𝓕₁, G (x, y) ∂μ ∂μ := by
  first | exact @GlobalTheory.PeriodicIteratedIntegral.integral_ratPair_fundamentalDomain_eq_iterated | exact GlobalTheory.PeriodicIteratedIntegral.integral_ratPair_fundamentalDomain_eq_iterated | (intros; apply GlobalTheory.PeriodicIteratedIntegral.integral_ratPair_fundamentalDomain_eq_iterated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrepAveragesFinDimSmoothOfKTypesAndPolyAverages
section
noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

variable {n : ℕ}

def typesIn (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : GlobalTheory.PsCo.Pc1.Mat n → (H →L[ℂ] H)) (A : Set (Fin n → ℝ)) : Submodule ℂ H :=
  ⨆ μ : A, (sSup {S : Submodule ℂ H | S ≤ ⊤ ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H)

theorem typesIn_kStable (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : GlobalTheory.PsCo.Pc1.Mat n → (H →L[ℂ] H)) (A : Set (Fin n → ℝ)) : Formalism.MainNotions.S.IsKStableOn ε σ (typesIn ε σ A) := by
  intro g hg v hv
  unfold typesIn at hv ⊢
  refine Submodule.iSup_induction _ (motive := fun v => σ g v ∈ _) hv (fun μ y hy => ?_) (by simp) ?_
  · rw [sSup_eq_iSup] at hy
    refine Submodule.iSup_induction _ (motive := fun z => σ g z ∈ _) hy (fun S w hw => ?_) (by simp) ?_
    · refine Submodule.iSup_induction _ (motive := fun w => σ g w ∈ _) hw (fun hS u hu => ?_) (by simp) ?_
      · exact Submodule.mem_iSup_of_mem μ (Submodule.mem_sSup_of_mem hS (hS.2.2.1 g hg u hu))
      · intro a b ha hb; rw [map_add]; exact add_mem ha hb
    · intro a b ha hb; rw [map_add]; exact add_mem ha hb
  · intro a b ha hb; rw [map_add]; exact add_mem ha hb

theorem typesIn_fd (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.PsCo.Pc1.Mat n → (H →L[ℂ] H)) (hσ : IsURepOn (UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) {A : Set (Fin n → ℝ)} (hA : A.Finite) :
    FiniteDimensional ℂ (typesIn ε σ A) := by
  have hσ' : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ := by
    rw [mir_isURepOn_iff, mir_UJset_eq]; exact hσ
  have hadm := GlobalTheory.PsCo.TrAdm.isAdmissibleSub_top n ε H σ hσ' hirr
  haveI : Finite A := hA.to_subtype
  have : ∀ μ : A,
      FiniteDimensional ℂ (sSup {S : Submodule ℂ H | S ≤ ⊤ ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H) :=
    fun μ => hadm μ
  exact Submodule.finiteDimensional_iSup _

theorem irrepAveragesFinDimSmooth_of_kTypes_and_polyAverages : SumTypes → PolyAvg → RangeFD := by
  intro hST hPA n ε H _ _ _ σ hσ hirr d
  obtain ⟨A, hAf, hA⟩ := hPA n ε d
  set M := typesIn ε σ A with hMdef
  have hMf : FiniteDimensional ℂ M := typesIn_fd ε σ hσ hirr hAf
  have hMK : Formalism.MainNotions.S.IsKStableOn ε σ M := typesIn_kStable ε σ A
  have hσ' : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ := by
    rw [mir_isURepOn_iff, mir_UJset_eq]; exact hσ
  have hMD : M ≤ smD ε σ := fun v hv => CompanionTheory.D.gk.HC.mem_smD_of_isKFin hσ' hirr ⟨M, hMf, hv, hMK⟩
  refine ⟨M.comap (smD ε σ).subtype, ?_, ?_, ?_⟩
  · exact Module.Finite.of_injective
      ((smD ε σ).subtype.restrict (p := M.comap (smD ε σ).subtype) (q := M) fun x hx => hx)
      (fun x y h => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h)))
  · intro k hk x hx
    show σ k (x : H) ∈ M
    exact hMK k (by rw [mir_Kset_eq]; exact hk) x hx
  · intro P hP u
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hMD]
    obtain ⟨S, hSf, hSK, hSP, hSA⟩ := hA H σ hσ u
    refine (hST n ε H σ hσ S hSf hSK).trans (sSup_le fun S' hS' => ?_) (hSP P hP)
    obtain ⟨hS'S, μ, hμ⟩ := hS'
    obtain ⟨v, hv, hv0, hvw⟩ := hμ.2.2.2.1
    have hμA : μ ∈ A := hSA μ v (hS'S hv) hv0 hvw
    exact le_iSup_of_le (⟨μ, hμA⟩ : A) (le_sSup ⟨le_top, hμ⟩)

end GlobalTheory.PsCo.PcEF

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem rangeFD_closed : RangeFD := irrepAveragesFinDimSmooth_of_kTypes_and_polyAverages @GlobalTheory.PsCo.PcEF.finDimStable_isSumOfKTypes @GlobalTheory.PsCo.PcEF.polyAverages_finiteWeightStableSubspace

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFlatAbelianSchemeHomOfQuasiInverse
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsogFiniteFlat

open GlobalTheory.UnramifiedEndFlat GlobalTheory.FiniteEndFlat

theorem apply_genericPoint_of_comp {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) (g : Y ⟶ X) [LocallyQuasiFinite g]
    (h : g (f (genericPoint X)) = genericPoint X) : f (genericPoint X) = genericPoint Y := by
  have hs := strictMono_of_locallyQuasiFinite g
  have h1 : genericPoint Y ⤳ f (genericPoint X) := genericPoint_specializes _
  have h2 : g (genericPoint Y) ⤳ genericPoint X := by
    rw [← h]; exact h1.map g.continuous
  have h3 : g (genericPoint Y) = genericPoint X :=
    (h2.antisymm (genericPoint_specializes _)).eq
  by_contra hne
  have hlt : f (genericPoint X) < genericPoint Y := lt_of_le_not_ge h1 fun h' =>
    hne (h1.antisymm (show f (genericPoint X) ⤳ genericPoint Y from h')).eq.symm
  have := hs hlt
  rw [h3, h] at this
  exact lt_irrefl _ this

theorem flat_of_isFinite_grpHom (K : Type) [Field K] [IsAlgClosed K]
    (G G' : Over (Spec (CommRingCat.of K))) [GrpObj G] [GrpObj G'] [IsIntegral G.left] [IsIntegral G'.left]
    [LocallyOfFiniteType G.hom] [LocallyOfFiniteType G'.hom] (φ : G ⟶ G') (φ' : G' ⟶ G)
    [IsMonHom φ] [IsMonHom φ'] [IsFinite φ.left] [IsFinite φ'.left] :
    Flat φ.left := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  let o : G.left := η[G].left (IsLocalRing.closedPoint K)
  have hfo : (φ.left ≫ φ'.left) o = o := by
    have : η[G] ≫ (φ ≫ φ') = η[G] := IsMonHom.one_hom (φ ≫ φ')
    rw [← Over.comp_left]
    exact congr(($this).left (IsLocalRing.closedPoint K))
  have hξ0 := apply_genericPoint (φ.left ≫ φ'.left) hfo
  have hξ : φ.left (genericPoint G.left) = genericPoint G'.left :=
    apply_genericPoint_of_comp φ.left φ'.left (by simpa using hξ0)
  obtain ⟨W, hW, H⟩ := exists_open_flat φ.left hξ
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hW W.2.isLocallyClosed
  refine flat_of_closedPoints _ fun x hx => ?_
  let x' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2
  let y' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨y, hyc⟩).2
  let α := GrpObj.mulRight (A := G) (y'⁻¹ * x')
  let β := GrpObj.mulRight (A := G') ((y'⁻¹ * x') ≫ φ)
  have hαβ : α.hom ≫ φ = φ ≫ β.hom := by
    simp only [α, β]
    generalize y'⁻¹ * x' = z
    simp [comp_lift_assoc]
  have hα : y' ≫ α.hom = x' := by
    have : y' ≫ α.hom = y' * (y'⁻¹ * x') := by
      simp [α, comp_lift_assoc, Hom.mul_def]
    rw [this, mul_inv_cancel_left]
  have hα' : α.hom.left y = x := by
    have h := congr(($hα).left (IsLocalRing.closedPoint K))
    rw [← pointOfClosedPoint_apply G.hom x hx (IsLocalRing.closedPoint K),
      ← pointOfClosedPoint_apply G.hom y hyc (IsLocalRing.closedPoint K)]
    exact h
  have : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).map α.hom))
  have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  have h1 : ((φ.left ≫ β.hom.left).stalkMap y).hom.Flat := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (Flat.stalkMap β.hom.left _).comp (H y hy)
  rw [← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp] at h1
  rw [← hα']
  exact (RingHom.Flat.respectsIso.cancel_right_isIso
    (φ.left.stalkMap (α.hom.left y)) (α.hom.left.stalkMap y)).mp h1

end GlobalTheory.IsogFiniteFlat

namespace GlobalTheory.IsogFiniteFlat

theorem isFinite_and_flat_of_quasiInverse : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A A' : Over S) [GrpObj A]
    [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'], IsAbelianScheme A → IsAbelianScheme A' →
    ∀ (ψ : A ⟶ A') (ψ' : A' ⟶ A) (c : ℕ), c ≠ 0 → IsMonHom ψ → IsMonHom ψ' → ψ ≫ ψ' = (𝟙 A) ^ c →
      ψ' ≫ ψ = (𝟙 A') ^ c → IsFinite ψ.left ∧ Flat ψ.left := by
  intro S _ A A' _ _ _ _ hA hA' ψ ψ' c hc _ _ h1 h2
  have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.2 hc
  obtain ⟨hfA, -⟩ := GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul S A hA c hc1
  obtain ⟨hfA', -⟩ := GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul S A' hA' c hc1
  have := hA.proper
  have := hA.smooth
  have := hA'.proper
  have := hA'.smooth
  haveI : IsSeparated (ψ'.left ≫ A.hom) := by rw [Over.w]; infer_instance
  haveI : IsSeparated ψ'.left := IsSeparated.of_comp _ A.hom
  haveI : IsSeparated (ψ.left ≫ A'.hom) := by rw [Over.w]; infer_instance
  haveI : IsSeparated ψ.left := IsSeparated.of_comp _ A'.hom
  haveI : IsFinite (ψ.left ≫ ψ'.left) := by rw [← Over.comp_left, h1]; exact hfA
  haveI : IsFinite (ψ'.left ≫ ψ.left) := by rw [← Over.comp_left, h2]; exact hfA'
  have hf : IsFinite ψ.left := IsFinite.of_comp _ ψ'.left
  have hf' : IsFinite ψ'.left := IsFinite.of_comp _ ψ.left
  refine ⟨hf, GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres S A A' ψ inferInstance inferInstance hf
    fun K _ _ t => ?_⟩
  have hB := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A hA
  have hB' := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A' hA'
  have := hB.smooth
  have := hB'.smooth
  have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _
    ((Over.pullback t).obj A).hom hB.smooth hB.geomConnected
  have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _
    ((Over.pullback t).obj A').hom hB'.smooth hB'.geomConnected
  have : IsIntegral ((Over.pullback t).obj A).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton ((Over.pullback t).obj A).hom
  have : IsIntegral ((Over.pullback t).obj A').left :=
    GeometricallyIntegral.isIntegral_of_subsingleton ((Over.pullback t).obj A').hom
  haveI : IsFinite ((Over.pullback t).map ψ).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t ψ) hf
  haveI : IsFinite ((Over.pullback t).map ψ').left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t ψ') hf'
  exact flat_of_isFinite_grpHom K _ _ ((Over.pullback t).map ψ) ((Over.pullback t).map ψ')

end GlobalTheory.IsogFiniteFlat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormDbar
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
open Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.CxForm

theorem dbarAt_congr {n : ℕ} {γ δ : V n → Alt n} {v : V n} (h : γ =ᶠ[𝓝 v] δ) :
    dbarAt γ v = dbarAt δ v := by
  unfold dbarAt coefwise
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  have hS : (fun x => (bas n).repr (γ x) S) =ᶠ[𝓝 v] fun x => (bas n).repr (δ x) S := h.mono fun x hx => congrArg (fun y => (bas n).repr y S) hx
  show GlobalTheory.dbar _ v (coordVec a) • _ = GlobalTheory.dbar _ v (coordVec a) • _
  rw [GlobalTheory.dbar_congr hS]

theorem dbarAt_eq_sum {n : ℕ} (β : V n → Alt n) (w : V n) :
    dbarAt β w = ∑ S, (∑ b, GlobalTheory.dbar (fun y => (bas n).repr (β y) S) w (coordVec b) • dzb b) * bas n S := by
  simp only [dbarAt, coefwise, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  exact Finset.sum_comm

theorem dbarAt_pull_comp {n m : ℕ} {φ : V n → V m} {U : Set (V n)} (hU : IsOpen U)
    (hφ : DifferentiableOn ℂ φ U) {v : V n} (hv : v ∈ U) {β : V m → Alt m}
    (hβ : ∀ S, DifferentiableAt ℝ (fun w => (bas m).repr (β w) S) (φ v)) :
    dbarAt (fun x => pull (fderiv ℂ φ x) (β (φ x))) v = pull (fderiv ℂ φ v) (dbarAt β (φ v)) := by
  have hφv : DifferentiableAt ℂ φ v := hφ.differentiableAt (hU.mem_nhds hv)
  have e1 : (fun x => pull (fderiv ℂ φ x) (β (φ x))) =
      fun x => ∑ S, (fun S y => (bas m).repr (β (φ y)) S) S x • (fun S y => pull (fderiv ℂ φ y) (bas m S)) S x := by
    funext x
    conv_lhs => rw [← (bas m).sum_repr (β (φ x)), map_sum]
    exact Finset.sum_congr rfl fun S _ => map_smul _ _ _
  rw [e1, GlobalTheory.T.dbar_sum_leibniz (c := fun S y => (bas m).repr (β (φ y)) S) (F := fun S y => pull (fderiv ℂ φ y) (bas m S)) (fun S => (hβ S).comp v (hφv.restrictScalars ℝ))
    (fun S T => GlobalTheory.T.differentiableAt_pullback_form hU hφ hv _ T)]
  simp only [GlobalTheory.T.dbar_pullback_holomorphic_zero hU hφ hv, smul_zero, add_zero]
  rw [dbarAt_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [GlobalTheory.T.dbar_comp_holomorphic hφv (hβ S), map_mul]

theorem isForm_dbar {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (α : A.Fld)
    (h : A.IsForm α) : A.IsForm (A.dbar α) := by
  have hloc : ∀ i, ∀ v ∈ (A.e i).target, A.loc (A.dbar α) i v = dbarAt (A.loc α i) v := by
    intro i v hv
    rw [HolAtlas.loc, dif_pos hv]
    show dbarAt (A.loc α i) ((A.e i) ((A.e i).symm v)) = _
    rw [(A.e i).right_inv hv]
  refine ⟨fun i S => ?_, fun x x' hxx' => ?_⟩
  · exact (GlobalTheory.T.contDiffOn_dbar_coefficients (A.e i).open_target (h.smooth i) S).congr fun v hv => by rw [hloc i v hv]
  · have hU : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
      x.ch.isOpen_inter_preimage_symm x'.ch.open_source
    have hφ : DifferentiableOn ℂ (x'.ch ∘ x.ch.symm) (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
      A.holo x.1.1 x'.1.1
    have e : x.ch.symm (x.ch x.pt) = x'.pt := (x.ch.left_inv x.2).trans hxx'
    have hv0 : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source := by
      refine ⟨x.ch.map_source x.2, ?_⟩
      show x.ch.symm (x.ch x.pt) ∈ x'.ch.source
      rw [e]
      exact x'.2
    have hφv0 : (x'.ch ∘ x.ch.symm) x.crd = x'.crd := by
      show x'.ch (x.ch.symm (x.ch x.pt)) = x'.ch x'.pt
      rw [e]
    have key : ∀ v ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source,
        A.loc α x.1.1 v = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) v) (A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) v)) := by
      intro v hv
      rw [HolAtlas.loc, dif_pos hv.1]
      have := h.compat ⟨(x.1.1, x.ch.symm v), x.ch.map_target hv.1⟩ ⟨(x'.1.1, x.ch.symm v), hv.2⟩ rfl
      have e2 : x.ch (x.ch.symm v) = v := x.ch.right_inv hv.1
      simp only [HolAtlas.Pt.crd, HolAtlas.Pt.ch, HolAtlas.Pt.pt] at this
      rw [this, e2]
      exact congrArg _ (HolAtlas.loc_crd A α ⟨(x'.1.1, x.ch.symm v), hv.2⟩).symm
    show dbarAt (A.loc α x.1.1) x.crd = pull _ (dbarAt (A.loc α x'.1.1) x'.crd)
    rw [dbarAt_congr (Filter.eventuallyEq_of_mem (hU.mem_nhds hv0) key),
      dbarAt_pull_comp hU hφ hv0 (β := A.loc α x'.1.1) (fun S => ?_), hφv0]
    rw [hφv0]
    exact ((h.smooth x'.1.1 S).contDiffAt (x'.ch.open_target.mem_nhds (x'.ch.map_source x'.2))).differentiableAt
      (by simp)

end GlobalTheory.CxForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFunctionFieldOfOneVariableOfGenericPointOfCurv
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc IntermediateField

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Nef.CurveFF

theorem isFF_of_trdeg_eq_one {k F : Type} [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F]
    (h : Algebra.trdeg k F = 1) : IsFF k F := by
  have hna : ¬ Algebra.IsAlgebraic k F := fun ha => by
    rw [trdeg_eq_zero_iff.mpr ha] at h; exact zero_ne_one h
  obtain ⟨x, hx⟩ : ∃ x : F, Transcendental k x := by
    by_contra hc
    push_neg at hc
    exact hna ⟨fun x => by simpa [Transcendental] using hc x⟩
  exact ⟨x, hx, finiteDimensional_adjoin_of_trdeg_le_one h.le x hx⟩

theorem isFF_of_stalk (k K : Type) [Field k] [Field K] [Algebra k K] (C : Scheme.{0}) [IsIntegral C]
    [Algebra k Γ(C, ⊤)] (hp : IsProjOver (strHom k C)) (hd : topologicalKrullDim C = 1)
    (y : C) (hy : y = genericPoint C) (ψ : C.presheaf.stalk y ⟶ CommRingCat.of K)
    (hψ : Function.Surjective ψ.hom)
    (hc : Spec.map ψ ≫ C.fromSpecStalk y ≫ strHom k C = spMap (algebraMap k K)) : IsFF k K := by
  subst hy
  let φ : k →+* C.functionField := (Spec.preimage (C.fromSpecStalk (genericPoint C) ≫ strHom k C)).hom
  have hφ : C.fromSpecStalk (genericPoint C) ≫ strHom k C = spMap φ := (Spec.map_preimage _).symm
  letI : Algebra k C.functionField := φ.toAlgebra
  have htr : Algebra.trdeg k C.functionField = 1 := by
    have := FunctionFieldTrdeg.trdeg_functionField_eq k C (strHom k C) 1 hp (by simpa using hd) φ hφ
    simpa using this
  have hfg : (⊤ : IntermediateField k C.functionField).FG :=
    FGFun.fg_functionField k C (strHom k C) hp k C.functionField φ (𝟙 _) (RingHom.id _) (by simp [hφ])
  haveI : Algebra.EssFiniteType k C.functionField := IntermediateField.fg_top_iff.mp hfg
  let ψ' : C.functionField →+* K := ψ.hom
  have hinj : Function.Injective ψ' := ψ'.injective
  have hcomm : ∀ c : k, ψ' (φ c) = algebraMap k K c := by
    rw [hφ] at hc
    have h1 : Spec.map (CommRingCat.ofHom φ ≫ ψ) = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
      rw [Spec.map_comp]; exact hc
    have h2 := Spec.map_injective h1
    intro c
    exact congrArg (fun f => f.hom c) h2
  let e : C.functionField ≃ₐ[k] K :=
    AlgEquiv.ofBijective { ψ' with commutes' := hcomm } ⟨hinj, hψ⟩
  haveI : Algebra.EssFiniteType k K := (Algebra.EssFiniteType.iff_of_algEquiv e).mp inferInstance
  exact isFF_of_trdeg_eq_one (e.trdeg_eq ▸ htr)

theorem isFF_of_isGenOver : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  IsFF k K := by
  intro k K _ _ _ _ _ C _ x hx
  obtain ⟨⟨hs, hp, hg⟩, ⟨hdom, hpre⟩, hxs⟩ := hx
  haveI : IsIntegral C := LieSemineg.isIntegral_curve hs hg
  let p : Sp K := IsLocalRing.closedPoint (CommRingCat.of K)
  haveI : Nonempty C := ⟨x p⟩
  have hd : topologicalKrullDim C = 1 := LieSemineg.dim_curve hs
  have hgen : x p = genericPoint C := by
    have hr : Set.range x = {x p} := by
      ext w
      constructor
      · rintro ⟨v, rfl⟩
        rw [Set.mem_singleton_iff, Subsingleton.elim v p]
      · rintro rfl
        exact ⟨p, rfl⟩
    refine ((genericPoint_spec C).eq ?_).symm
    rw [isGenericPoint_def, ← hr]
    exact x.denseRange.closure_range
  have hsurj : Function.Surjective (Scheme.stalkClosedPointTo x).hom := by
    unfold Scheme.stalkClosedPointTo
    exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (.of K)).hom).2.comp
      (x.stalkMap_surjective _)
  refine isFF_of_stalk k K C hp hd _ hgen (Scheme.stalkClosedPointTo x) hsurj ?_
  rw [← Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hxs]

end GlobalTheory.Nef.CurveFF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionDoublingThetaTensorCMStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunction_doublingThetaTensor_CM : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ → Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ →
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) := by
  first | exact @GlobalTheory.DblTargetThetaF.main | exact GlobalTheory.DblTargetThetaF.main | (intros; apply GlobalTheory.DblTargetThetaF.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointlyEpiSectionsGenerateStatement
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jointly_epi_sections_generate : ∀ (T : Scheme.{0}) (L Q : T.Modules) (N : ℕ) (s : Fin (N + 1) → (L ⟶ Q)), IsVB L 1 → IsVB Q 1 → JointEpi s → Gen s := by
  first | exact @GlobalTheory.LineQuot.gen_of_jointEpi | exact GlobalTheory.LineQuot.gen_of_jointEpi | (intros; apply GlobalTheory.LineQuot.gen_of_jointEpi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitsHoldsStatement
section
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_units_holds : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → LocalUnits O := by
  first | exact @GlobalTheory.LocalUnit.localUnits | exact GlobalTheory.LocalUnit.localUnits | (intros; apply GlobalTheory.LocalUnit.localUnits <;> assumption)
end

