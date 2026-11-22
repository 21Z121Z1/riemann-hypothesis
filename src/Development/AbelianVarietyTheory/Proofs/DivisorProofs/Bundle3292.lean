import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3279
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2832
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2116
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2166
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1214
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3161
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3280
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3283
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2618
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1031
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussPropertyCodimOneChartHeightOnePrime
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryCentralizerOfCommutePadicPointsSpliStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical
theorem _root_.GlobalTheory.T.exists_unitaryCentralizer_of_commute_padicPoints_split : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G β = β → ∀ (y₀ : grp G β) (c : Gr G 1), c * toP1 G β y₀ = toP1 G β y₀ * c → ∃ z : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ, InT G ℚ_[p] β (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) z ∧ psiP G z = c := by
  first | exact @GlobalTheory.TorCls.centraliser_at_p | exact GlobalTheory.TorCls.centraliser_at_p | (intros; apply GlobalTheory.TorCls.centraliser_at_p <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendRegularThetaSectionAnyFractionField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ExtFrac

theorem thList_pull_of_eq {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left)
    (ρ : LB.Gen (L.pull (eSec G))) (hL : L.IsLB) (hρ : ρ.IsGen) {m N : ℕ} {K K' : Type} [Field K] [Field K']
    (i : K →+* K') {x : Sp K ⟶ S} {x' : Sp K' ⟶ S} (h : spMap i ≫ x = x') {θ : SecAt G L x}
    {pt : Fin N → (Over.mk x ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m x θ pt c) :
    ∃ pt' : Fin N → (Over.mk x' ⟶ G),
      ThList G L ρ m x' (VVRank.pullS G _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x) θ) pt'
        (fun a => i (c a)) := by
  subst h
  obtain ⟨pt', -, H'⟩ := ThPull.thList_pull S G L ρ hL hρ m N K K' i x θ pt c H
  exact ⟨pt', H'⟩

theorem ext_any_frac : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (χ : Sp R ⟶ S) (θ : SecAt t.G t.PP.L (spMap (algebraMap R K) ≫ χ)) (pt : Fin N → (Over.mk (spMap (algebraMap R K) ≫ χ) ⟶ t.G)) (c : Fin N → R), Odd m → 3 ≤ m → IsUnit (m : R) → PolFib t.G t.PP.L g (spMap (algebraMap R K) ≫ χ) → ThList t.G t.PP.L t.PP.rig m _ θ pt (fun a => algebraMap R K (c a)) → (∃ a, IsUnit (c a)) → ∃ σ : SecAt t.G t.PP.L χ, SecM.ofSec t.G (SecAt.pull t.G t.PP.L σ (algebraMap R K)) = SecM.ofSec t.G θ ∧ ∀ s : Sp R, ∃ z : (Over.mk χ ⊗ t.G).left, (fst (Over.mk χ) t.G).left z = s ∧ z ∈ nonzeroLocus σ := by
  intro E _ _ _ H S t g m N R _ _ _ _ _ K _ _ _ χ θ pt c hm h3 hu hP hT hc
  let φ : FractionRing R ≃ₐ[R] K := FractionRing.algEquiv R K
  let i : K →+* FractionRing R := φ.symm.toRingEquiv.toRingHom
  let j : FractionRing R →+* K := φ.toRingEquiv.toRingHom
  have hi : ∀ r, i (algebraMap R K r) = algebraMap R (FractionRing R) r := fun r => φ.symm.commutes r
  have hi' : i.comp (algebraMap R K) = algebraMap R (FractionRing R) := RingHom.ext hi
  have hj' : j.comp (algebraMap R (FractionRing R)) = algebraMap R K := RingHom.ext fun r => φ.commutes r
  have hji : j.comp i = RingHom.id K := RingHom.ext fun r => φ.apply_symm_apply r
  have e₁ : spMap i ≫ spMap (algebraMap R K) ≫ χ = spMap (algebraMap R (FractionRing R)) ≫ χ := by
    rw [← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, hi']
  have e₂ : spMap j ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap (algebraMap R K) ≫ χ := by
    rw [← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, hj']
  have hp : IsGrpPullback t.G t.G (𝟙 _) (𝟙 t.G.left) :=
    @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl t.G) (inferInstanceAs (IsMonHom (𝟙 t.G)))
  have hLL : LBIso t.PP.L (t.PP.L.pull (𝟙 _)) :=
    (GlobalTheory.PolBaseChange.lbIso_refl t.PP.isLB).chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl)
  have hP' := (FibMove.polFib_move S S t.G t.PP.L t.G t.PP.L (𝟙 _) (𝟙 _) t.PP.isLB t.PP.isLB hp hLL g K _).2 _ i hP
  rw [e₁] at hP'
  obtain ⟨pt', hT'⟩ := thList_pull_of_eq t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen i e₁ hT
  simp only [hi] at hT'
  obtain ⟨σ, hσ, hz⟩ := GlobalTheory.T.fibreSection_extends_nonzero_of_integral_thetaConstants E H S t g m N R χ _ pt' c hm h3 hu hP' hT' hc
  refine ⟨σ, ?_, hz⟩
  let β : Over.mk (spMap (algebraMap R K) ≫ χ) ⟶ Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) :=
    Over.homMk (spMap j) e₂
  have q := congrArg (VVRank.pullM t.G t.PP.L _ β) hσ
  have a₁ : β ≫ (Over.homMk (spMap (algebraMap R (FractionRing R))) rfl :
      Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) = Over.homMk (spMap (algebraMap R K)) rfl := by
    ext
    change spMap j ≫ spMap (algebraMap R (FractionRing R)) = spMap (algebraMap R K)
    rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, hj']
  have a₂ : β ≫ (Over.homMk (spMap i) e₁ : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶
      Over.mk (spMap (algebraMap R K) ≫ χ)) = 𝟙 _ := by
    ext
    change spMap j ≫ spMap i = 𝟙 _
    rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, hji]
    exact Spec.map_id _
  have b₁ := VVRank.pullM_comp t.G t.PP.isLB ((1 : ℕ) : ℤ) β (Over.homMk (spMap (algebraMap R (FractionRing R))) rfl :
      Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) (SecM.ofSec t.G σ)
  have b₂ := VVRank.pullM_comp t.G t.PP.isLB ((1 : ℕ) : ℤ) β (Over.homMk (spMap i) e₁ :
      Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk (spMap (algebraMap R K) ≫ χ)) (SecM.ofSec t.G θ)
  rw [a₁] at b₁
  rw [a₂, VVRank.pullM_id t.G t.PP.isLB] at b₂
  exact b₁.symm.trans (q.trans b₂)

end GlobalTheory.UMin.ExtFrac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitenessInputsRealDataThree
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn

namespace GlobalTheory.LowRow

theorem lamLow_closing : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → GlobalTheory.Published.DoublingMethod → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ) (b C CH : ℝ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i) → (∀ j, Sizes D j b) → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → (∀ j, (R.num F C CH).l6 j ≤ (F.Zsc (R.toCx3 F).zs).l6m j) → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → StdV D → ((R.toCx3 F).data F.cr true).L6 (R.num F C CH) := by
  intro hCusp hWS hSWC hDM hUD hBZ hFD D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O s b C CH
    hOk hSep hChar hEx hPrim hPhs hStd fw hBar hIo hPins hOne hTie hSizes hLow hNum hPar hStdV
  have hAd : AdelC R.toRealDat F.lv2 :=
    GlobalTheory.T.finiteness_inputs_real_data hCusp hWS hSWC hDM hUD hBZ hFD R.toRealDat F.lv2 hPar hStdV
  have hCore := (GlobalTheory.T.splitPart_baseLinks_of_primitiveRows R F s hOk hSep hChar hEx hPrim hPhs).1
  have hPT : PrimeToHost R.toRealDat A3.A.μ0 :=
    GlobalTheory.T.badPlacesPrimeToHost_baseTuple R.toRealDat F.lv2 (GlobalTheory.Core5.of_core hCore)
  exact GlobalTheory.T.liftEigenvalueLowerBound_of_weakCharacterisation GlobalTheory.T.conjugatesOfRationalThetaLift_from_characterisation T R F κ v₀ O s b C CH hOk hSep hChar hEx hPrim hPhs hStd fw hBar
    hIo hPins hOne hTie hSizes hLow hNum hAd hPT

end GlobalTheory.LowRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSpanPowPDivGroupLevelLe
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

open Coalgebra Bialgebra WithConv

namespace GlobalTheory.SpanPow

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K]

def annPowIdeal (h : (p : K) = 0) (G : PDivGroup p K) (r : ℕ) : Ideal (G.dual.A r) where
  carrier := {χ | ∀ a : G.A r, (show CartierDual K (G.A r) from χ) (a ^ p ^ r) = 0}
  add_mem' {χ ψ} hχ hψ a := by
    have e1 := hχ a
    have e2 := hψ a
    change (χ.ofConv + ψ.ofConv) (a ^ p ^ r) = 0
    rw [LinearMap.add_apply]
    change χ.ofConv (a ^ p ^ r) = 0 at e1
    change ψ.ofConv (a ^ p ^ r) = 0 at e2
    rw [e1, e2, add_zero]
  zero_mem' a := rfl
  smul_mem' c χ hχ a := by
    change (show CartierDual K (G.A r) from c * χ) (a ^ p ^ r) = 0
    rw [CartierDual.mul_apply, ← Bialgebra.comulAlgHom_apply, map_pow, Bialgebra.comulAlgHom_apply]
    rcases subsingleton_or_nontrivial (G.A r ⊗[K] G.A r) with hs | hn
    · rw [Subsingleton.elim ((comul (R := K) a) ^ p ^ r) 0, map_zero]
    · haveI : CharP (G.A r ⊗[K] G.A r) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 (by
        rw [← map_natCast (algebraMap K (G.A r ⊗[K] G.A r)), h, map_zero])
      haveI : ExpChar (G.A r ⊗[K] G.A r) p := ExpChar.prime (Fact.out : p.Prime)
      have rep := Coalgebra.Repr.arbitrary K a
      rw [← rep.eq, sum_pow_char_pow, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Algebra.TensorProduct.tmul_pow, CartierDual.pair_tmul_tmul]
      have e := hχ (rep.right i)
      change χ.ofConv _ = 0 at e
      rw [e, mul_zero]

theorem frobKerIdeal_le_annPowIdeal (h : (p : K) = 0) (G : PDivGroup p K) (r : ℕ) :
    frobKerIdeal (p ^ r) K (G.dual.A r) ≤ annPowIdeal h G r := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨χ, hχ, rfl⟩ a
  have h1 := GlobalTheory.T.cartierDual_primePow_conv_pairing p K h G r r χ a
  have hχ' : χ.ofConv 1 = 0 := hχ
  change (χ ^ p ^ r).ofConv (a ^ p ^ r) = 0
  change (χ ^ p ^ r).ofConv (a ^ p ^ r) = χ.ofConv (mulBy K (G.A r) (p ^ r) a) ^ p ^ r at h1
  rw [h1, G.mulBy_pow_self r a, Algebra.algebraMap_eq_smul_one, map_smul, hχ', smul_zero,
    zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]

end GlobalTheory.SpanPow

open GlobalTheory.SpanPow in
theorem GlobalTheory.finrank_span_pow_le : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), ∀ r : ℕ, Module.finrank K (Submodule.span K (Set.range fun a : G.A r => a ^ p ^ r)) ≤ (p ^ r) ^ Module.finrank K G.dual.omega := by
  intro p _ K _ h G r
  set S := Submodule.span K (Set.range fun a : G.A r => a ^ p ^ r) with hS
  let D := G.dual.A r
  let ev : D →ₗ[K] Module.Dual K S := S.subtype.dualMap ∘ₗ (CartierDual.toDual K (G.A r)).toLinearMap
  have hev : Function.Surjective ev :=
    (LinearMap.dualMap_surjective_of_injective S.injective_subtype).comp
      (CartierDual.toDual K (G.A r)).surjective
  let J := frobKerIdeal (p ^ r) K D
  have hle : J.restrictScalars K ≤ LinearMap.ker ev := by
    intro χ hχ
    have hT := frobKerIdeal_le_annPowIdeal h G r hχ
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun s => ?_
    obtain ⟨s, hs⟩ := s
    change χ.ofConv s = 0
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact hT a
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  let φ : (D ⧸ J) →ₗ[K] Module.Dual K S :=
    (J.restrictScalars K).liftQ ev hle ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv K J).symm.toLinearMap
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := hev y
    refine ⟨Ideal.Quotient.mk J x, ?_⟩
    rfl
  have h1 : Module.finrank K S ≤ Module.finrank K (D ⧸ J) := by
    have := LinearMap.finrank_range_le φ
    rw [LinearMap.range_eq_top.2 hφ, finrank_top, Subspace.dual_finrank_eq] at this
    exact this
  have h2 := GlobalTheory.T.finrank_frobeniusKernelQuotient_le_pow_cotangent (p ^ r) K D (pow_pos (Fact.out : p.Prime).pos r)
  have hfin := (GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual p K h G.dual).1
  have h3 : Module.finrank K (Cot K D) ≤ Module.finrank K G.dual.omega := by
    have := LinearMap.finrank_range_le (G.dual.omegaLevel r)
    rwa [LinearMap.range_eq_top.2 (G.dual.omegaLevel_surjective r), finrank_top] at this
  exact h1.trans (h2.trans (Nat.pow_le_pow_right (pow_pos (Fact.out : p.Prime).pos r) h3))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDivisorIntegralPushforward
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem finsum_weighted_regroup_along_fibres {A B : Type} (π : A → B) (m : A → ℤ) (n : B → ℤ) (d : A → ℕ) (g : A → ℝ) (h : B → ℝ)
    (P : B → Prop) (hm : (Function.support m).Finite) (hn : (Function.support n).Finite)
    (hP : ∀ z, n z ≠ 0 → P z) (hs : ∀ z, P z → ∑ᶠ (w : A) (_ : π w = z), m w * (d w : ℤ) = n z)
    (h₁ : ∀ w, m w ≠ 0 → P (π w) → g w = d w * h (π w)) (h₀ : ∀ w, m w ≠ 0 → ¬ P (π w) → g w = 0) :
    ∑ᶠ w, (m w : ℝ) * g w = ∑ᶠ z, (n z : ℝ) * h z := by
  classical
  set S := hm.toFinset with hS
  set T := hn.toFinset ∪ S.image π with hT
  have hmS : ∀ w, m w ≠ 0 ↔ w ∈ S := fun w => by simp [hS]
  rw [finsum_eq_sum_of_support_subset (s := S) _ (fun w hw => by
      have : m w ≠ 0 := fun h0 => hw (by simp [h0])
      exact Finset.mem_coe.2 ((hmS w).1 this)),
    finsum_eq_sum_of_support_subset (s := T) _ (fun z hz => by
      have : n z ≠ 0 := fun h0 => hz (by simp [h0])
      simp [hT, this]),
    ← Finset.sum_fiberwise_of_maps_to (s := S) (t := T) (g := π) (fun w hw => by
      simp only [hT, Finset.mem_union]; exact Or.inr (Finset.mem_image_of_mem _ hw))]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : P z
  · have e : ∑ᶠ (w : A) (_ : π w = z), m w * (d w : ℤ) = ∑ w ∈ S.filter (fun w => π w = z), m w * (d w : ℤ) := by
      refine finsum_mem_eq_sum_of_inter_support_eq (s := {w | π w = z}) _ ?_
      ext w
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.mem_support, Finset.coe_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨(hmS w).1 (left_ne_zero_of_mul h2), h1⟩, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1.2, h2⟩
    rw [← hs z hz, e]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun w hw => ?_
    obtain ⟨hw', rfl⟩ := Finset.mem_filter.1 hw
    rw [h₁ w ((hmS w).2 hw') hz, mul_assoc]
  · have e : n z = 0 := by
      by_contra h'
      exact hz (hP z h')
    rw [e, Int.cast_zero, zero_mul]
    refine Finset.sum_eq_zero fun w hw => ?_
    obtain ⟨hw', rfl⟩ := Finset.mem_filter.1 hw
    rw [h₀ w ((hmS w).2 hw') hz, mul_zero]

theorem finsum_cycInt_push : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → IsProjOver q → topologicalKrullDim Y = (e + 1 : ℕ) → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ (Δ : CartierDiv X) (Δ' : CartierDiv Y), (∀ z : X, Order.coheight z = 1 → ∑ᶠ (w : Y) (_ : π w = z), Δ'.mult w * (π.residueDegree w : ℤ) = Δ.mult z) → ∀ (L : Fin e → MLine p σ) (f : CxPts p σ → ℝ), Measurable f → ∑ᶠ w, (Δ'.mult w : ℝ) * cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L f z := by
  intro F _ X Y _ _ _ _ p q σ e hp hX hq hY π hπ _ Δ Δ' hΔ L f hf
  have hc : ∀ {Z : Scheme.{0}} {s : Z ⟶ Sp F}, IsProjOver s → CompactSpace Z := by
    rintro Z _ ⟨m, i, hi, rfl⟩
    have := isProper_str F m
    have : IsProper (i ≫ PSpace.str F m) := inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str F m)
  haveI := hc hp
  haveI := hc hq
  have key := fun (w : Y) (hw : Δ'.mult w ≠ 0) => GlobalTheory.T.mixedChernIntegral_pointClosure_pullback F X Y p q σ hp hq π hπ e L f hf w
    ((GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F Y q e hq hY w).1 (CartierDiv.coheight_eq_one_of_mult_ne_zero (D := Δ') hw))
  exact finsum_weighted_regroup_along_fibres π Δ'.mult Δ.mult (fun w => π.residueDegree w) _ _ (fun z => Order.coheight z = 1)
    Δ'.finite_support_mult Δ.finite_support_mult
    (fun z hz => CartierDiv.coheight_eq_one_of_mult_ne_zero (D := Δ) hz) hΔ
    (fun w hw h => (key w hw).1 ((GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F X p e hp hX _).1 h))
    (fun w hw h => (key w hw).2 fun h' => h ((GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F X p e hp hX _).2 h'))

end GlobalTheory.Mix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleDimPlusOne
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false

noncomputable section

open Limits GlobalTheory.QCoh

namespace GlobalTheory.FlagLineDim

theorem exists_local_section (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules)
    (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a))
    (hE : ∀ a, GlobalTheory.VB.IsVB (E a) (r a)) (hfl : IsFlagBundle π E r fl) (b : B) :
    ∃ (V : B.Opens) (g : V.toScheme ⟶ Y), b ∈ V ∧ g ≫ π = V.ι := by
  choose U e hb he using fun a => hE a b
  let V : B.Opens := Finset.univ.inf U
  have hle : ∀ a, V ≤ U a := fun a => Finset.inf_le (Finset.mem_univ a)
  have hbV : b ∈ V := by
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_finset_inf]
    simpa using hb
  have hfr (a : ι) := (isFrame_restrict_iff V.ι _).2 ((he a).res ((V.ι_image_le ⊤).trans (hle a)))
  let φ : ∀ a, freeModule V.toScheme (Fin (r a)) ≅ (Scheme.Modules.pullback V.ι).obj (E a) := fun a =>
    (isFrame_freeFrame _ _).iso (hfr a) ≪≫ (Scheme.Modules.restrictFunctorIsoPullback V.ι).app (E a)
  obtain ⟨g', ⟨w, -⟩, -⟩ := hfl V.toScheme V.ι (fun a => (GlobalTheory.FlagSurj.freeFlag V.toScheme (r a)).ofIso (φ a))
  exact ⟨V, g', hbV, w⟩

theorem isLocallyNoetherian_base (B Y : Scheme.{0}) [IsLocallyNoetherian Y] (π : Y ⟶ B) (ι : Type) [Fintype ι]
    (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a))
    (hE : ∀ a, GlobalTheory.VB.IsVB (E a) (r a)) (hfl : IsFlagBundle π E r fl) : IsLocallyNoetherian B := by
  choose V g hbV hg using exists_local_section B Y π ι E r fl hE hfl
  let S : {U : B.affineOpens // ∃ b, (U : B.Opens) ≤ V b} → B.affineOpens := fun U => U.1
  refine isLocallyNoetherian_of_affine_cover (S := S) ?_ ?_
  · refine top_le_iff.1 fun b _ => ?_
    obtain ⟨U, hU, hbU, hUV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp B.isBasis_affineOpens (hbV b)
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨⟨⟨U, hU⟩, b, hUV⟩, hbU⟩
  · rintro ⟨U, b, hUV⟩
    let s : (U : B.Opens).toScheme ⟶ Y := B.homOfLE hUV ≫ g b
    have hs : s ≫ π = (U : B.Opens).ι := by
      simp only [s, Category.assoc, hg, Scheme.homOfLE_ι]
    haveI : LocallyOfFiniteType (s ≫ π) := by rw [hs]; infer_instance
    haveI : LocallyOfFiniteType s := locallyOfFiniteType_of_comp s π
    haveI : IsLocallyNoetherian (U : B.Opens).toScheme := LocallyOfFiniteType.isLocallyNoetherian s
    haveI : IsAffine (U : B.Opens).toScheme := U.2
    have := IsLocallyNoetherian.component_noetherian (X := (U : B.Opens).toScheme) ⟨⊤, isAffineOpen_top _⟩
    exact isNoetherianRing_of_ringEquiv _ ((U : B.Opens).topIso).commRingCatIsoToRingEquiv

theorem iSup_add_one_le {ι : Type} [Nonempty ι] (f : ι → WithBot ℕ∞) (hf : ∀ i, f i ≠ ⊥) (c : WithBot ℕ∞)
    (h : ∀ i, f i + 1 ≤ c) : (⨆ i, f i) + 1 ≤ c := by
  choose g hg using fun i => WithBot.ne_bot_iff_exists.mp (hf i)
  obtain rfl : f = fun i => ((g i : ℕ∞) : WithBot ℕ∞) := funext fun i => (hg i).symm
  rw [← WithBot.coe_iSup (OrderTop.bddAbove _), ← WithBot.coe_one, ← WithBot.coe_add, ENat.iSup_add,
    WithBot.coe_iSup (OrderTop.bddAbove _)]
  exact iSup_le fun i => by simpa using h i

end GlobalTheory.FlagLineDim

namespace GlobalTheory.FlagLineDim

theorem topologicalKrullDim_eq_add_one : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (Y Y₁ : Scheme.{0}) (p : Y ⟶ Sp k) (ρ : Y ⟶ Y₁) (E₁ : Y₁.Modules)
    (fl₁ : Vert.Flag ((Scheme.Modules.pullback ρ).obj E₁) 2), IsProjOver p → GlobalTheory.VB.IsVB E₁ 2 →
    IsFlagBundle ρ (fun _ : Unit => E₁) (fun _ => 2) (fun _ => fl₁) → topologicalKrullDim Y = topologicalKrullDim Y₁ + 1 := by
  intro k _ _ Y Y₁ p ρ E₁ fl₁ hp hE hfl
  haveI : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hp
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : IsLocallyNoetherian Y₁ := isLocallyNoetherian_base Y₁ Y ρ Unit (fun _ => E₁) (fun _ => 2) (fun _ => fl₁)
    (fun _ => hE) hfl
  have hsm := GlobalTheory.T.flag_bundle_smooth_relative_dimension Y₁ Y ρ Unit (fun _ => E₁) (fun _ => 2) (fun _ => fl₁) (fun _ => hE) hfl
  have h1 : (∑ _a : Unit, 2 * (2 - 1) / 2) = 1 := by decide
  rw [h1] at hsm
  haveI : SmoothOfRelativeDimension 1 ρ := hsm
  haveI : Smooth ρ := SmoothOfRelativeDimension.smooth 1 ρ
  have hsurj := GlobalTheory.FlagSurj.isFlagBundle_surjective Y₁ Y ρ Unit (fun _ => E₁) (fun _ => 2) (fun _ => fl₁)
    (fun _ => hE) hfl
  rw [GlobalTheory.SmoothDimTotal.topologicalKrullDim_eq_iSup_stalk, GlobalTheory.SmoothDimTotal.topologicalKrullDim_eq_iSup_stalk]
  simp_rw [GlobalTheory.SmoothDimTotal.ringKrullDim_stalk_eq_add Y₁ Y ρ]
  rcases isEmpty_or_nonempty Y₁ with hY₁ | hY₁
  · haveI : IsEmpty Y := ⟨fun y => hY₁.false (ρ y)⟩
    simp [iSup_of_empty]
  apply le_antisymm
  · refine iSup_le fun y => add_le_add (le_iSup (fun b : Y₁ => ringKrullDim (Y₁.presheaf.stalk b)) (ρ y)) ?_
    simpa using GlobalTheory.SmoothDimTotal.fib_le Y₁ Y ρ 1 y
  · refine iSup_add_one_le _ (fun b => ?_) _ fun b => ?_
    · exact ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial
    · obtain ⟨y₀, rfl⟩ := hsurj b
      obtain ⟨y, hy, hge⟩ := GlobalTheory.SmoothDimTotal.fib_ge Y₁ Y ρ 1 y₀
      rw [← hy]
      exact le_iSup_of_le y (add_le_add le_rfl (by simpa using hge))

end GlobalTheory.FlagLineDim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineCurvatureStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_hermitian_line_curvature : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    (hY.atlas σ).IsForm (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) ∧ (hY.atlas σ).ddc (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) = evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) ((X 4 - X 0) * (X 3 - X 0)) := by
  first | exact @GlobalTheory.LineForm.ddc_omF_sub_pull | exact GlobalTheory.LineForm.ddc_omF_sub_pull | (intros; apply GlobalTheory.LineForm.ddc_omF_sub_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineIntegralFormulaStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_hermitian_line_integral_formula : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ → ∀ ε : ℤˣ,
      Measure.map v ((hY.atlas σ).part (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 0 - X 3) * pullF hB hY σ π w φ) ε) =
        (hB.atlas σ).part φ (-ε) Set.univ • volume.restrict (Set.Icc (0 : ℝ) 1) := by
  first | exact @GlobalTheory.FibCos.map_part | exact GlobalTheory.FibCos.map_part | (intros; apply GlobalTheory.FibCos.map_part <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineLimitStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_hermitian_line_limit : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ K : MvPolynomial (Fin 5) ℝ, Filter.Tendsto (fun t : ℝ => (hY.atlas σ).integral ((hY.atlas σ).fn (fun y => t / (1 - v y + t) ^ 2) *
      ((hY.atlas σ).ddc ((hY.atlas σ).fn (fun y => 1 - v y)) + ((hY.atlas σ).fn (fun y => 1 - v y)) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 4 - X 0)) * (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (K) * (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB)))))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  first | exact @GlobalTheory.LineMeet.tendsto_integral_conc | exact GlobalTheory.LineMeet.tendsto_integral_conc | (intros; apply GlobalTheory.LineMeet.tendsto_integral_conc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleUniversallyOpen
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits

namespace GlobalTheory

theorem flagBundle_universallyOpen : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → UniversallyOpen π := by
  intro B Y π ι _ E r fl hE hF
  haveI := GlobalTheory.T.flag_bundle_smooth_relative_dimension B Y π ι E r fl hE hF
  haveI : Smooth π := SmoothOfRelativeDimension.smooth (∑ a, r a * (r a - 1) / 2) π
  infer_instance

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussPropertyCodimOneChartHeightOnePrimeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussProperty_codimOne_chart_heightOnePrime : ∀ (σ : Setup) (x : Sp σ.R) (z : (σ.C x).G.left), Vert (σ.C x).G.hom (σ.ρ x σ.f) z → GaussAt (GlobalTheory.Desc.cst (σ.C x).G.hom) ((σ.C x).G.hom z).asIdeal (σ.θ x) (σ.W (spMap (σ.ρ x) ((σ.C x).G.hom z))) (regSet z) ∧ (σ.θ x) ⁻¹' (regSet z) = σ.W (spMap (σ.ρ x) ((σ.C x).G.hom z)) := by
  first | exact @GlobalTheory.Desc.GaussPt.gaussAt_vert | exact GlobalTheory.Desc.GaussPt.gaussAt_vert | (intros; apply GlobalTheory.Desc.GaussPt.gaussAt_vert <;> assumption)
end

