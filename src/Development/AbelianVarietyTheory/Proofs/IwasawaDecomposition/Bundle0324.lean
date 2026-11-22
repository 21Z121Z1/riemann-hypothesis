import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0312
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0305
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0306
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenSubgroupFiniteSubset
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SmallSub

theorem eq_zero_of_pow_mul {K : Type} [NormedField K] {C : Set K} (hC : IsCompact C) {c x : K} (hc : ‖c‖ < 1)
    (h : ∀ n : ℕ, ∃ u ∈ C, x = c ^ n * u) : x = 0 := by
  obtain ⟨B, hB⟩ := hC.isBounded.exists_norm_le
  have ht : Filter.Tendsto (fun n : ℕ => ‖c‖ ^ n * B) Filter.atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg c) hc).mul_const B
  refine norm_le_zero_iff.1 (ge_of_tendsto' ht fun n => ?_)
  obtain ⟨u, hu, rfl⟩ := h n
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (hB u hu) (by positivity)

theorem finiteAdele_eq_zero (F : Type) [Field F] [NumberField F] {C : Set (Af F)} (hC : IsCompact C) {x : Af F}
    (h : ∀ M : ℕ, 0 < M → ∃ u ∈ C, x = M • u) : x = 0 := by
  refine Subtype.ext (funext fun v => ?_)
  change evalV F v x = 0
  have hv : Continuous (evalV F v) := RestrictedProduct.continuous_eval v
  have h1 := (NumberField.FinitePlace.norm_lt_one_iff_mem F v _).2 (Ideal.absNorm_mem v.asIdeal)
  rw [map_natCast, map_natCast] at h1
  have h0 : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero fun e => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
  refine eq_zero_of_pow_mul (hC.image hv) h1 fun n => ?_
  obtain ⟨u, hu, rfl⟩ := h _ (pow_pos h0 n)
  exact ⟨_, ⟨u, hu, rfl⟩, by rw [map_nsmul, nsmul_eq_mul, Nat.cast_pow]⟩

theorem tensor_eq_zero (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {C : Set (Af F ⊗[F] E)} (hC : IsCompact C) {x : Af F ⊗[F] E}
    (h : ∀ M : ℕ, 0 < M → ∃ u ∈ C, x = M • u) : x = 0 := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  let b := Algebra.TensorProduct.basis (Af F) (Module.finBasis F E)
  refine b.ext_elem fun i => ?_
  have hc : Continuous (b.coord i) := IsModuleTopology.continuous_of_linearMap _
  rw [map_zero, Finsupp.zero_apply]
  change b.coord i x = 0
  refine finiteAdele_eq_zero F (hC.image hc) fun M hM => ?_
  obtain ⟨u, hu, rfl⟩ := h M hM
  exact ⟨_, ⟨u, hu, rfl⟩, map_nsmul _ _ _⟩

theorem mem_GinfC_of_cong {D : D7} (V : HSp D) (k : GA D V)
    (h : ∀ n : ℕ, GlobalTheory.Ker.CongK V (GlobalTheory.SW.stdL D.host.E V.rank) n.factorial k) : k ∈ GinfC V := by
  obtain ⟨C, hC, hLC⟩ := GlobalTheory.StabCompact.exists_compact_latHat D.host.F D.host.E (GlobalTheory.SW.stdL D.host.E V.rank)
    (Submodule.fg_span (Set.finite_range _))
  refine Units.ext ?_
  change GlobalTheory.Ker.fmt V k = 1
  ext i j
  have h1 : (1 : Af D.host.F) ∈ intAf D.host.F := fun w => by rw [map_one]; exact one_mem _
  have hy : (Pi.single j 1 : Fin V.rank → GlobalTheory.Ker.AfE D) ∈ GlobalTheory.Ker.hatV (D := D) (GlobalTheory.SW.stdL D.host.E V.rank) := by
    refine AddSubgroup.subset_closure ⟨1, h1, Pi.single j 1, Submodule.subset_span ⟨j, rfl⟩, ?_⟩
    funext a
    by_cases e : a = j
    · subst e
      simp only [Pi.single_eq_same]
      rfl
    · simp [Pi.single_eq_of_ne e]
  have key : (GlobalTheory.Ker.fmt V k *ᵥ Pi.single j 1 - (Pi.single j 1 : Fin V.rank → GlobalTheory.Ker.AfE D)) i = 0 := by
    refine tensor_eq_zero D.host.F D.host.E (hC.image (continuous_apply i)) fun M hM => ?_
    obtain ⟨u, hu, e⟩ := (h M).2 _ hy
    obtain ⟨c, hc⟩ := Nat.dvd_factorial hM le_rfl
    refine ⟨_, ⟨c • u, hLC _ (nsmul_mem hu c), rfl⟩, ?_⟩
    rw [e, hc, mul_smul]
    rfl
  rw [Pi.sub_apply, sub_eq_zero, Matrix.mulVec_single_one] at key
  rw [Matrix.one_apply, ← Pi.single_apply]
  exact key

theorem exists_open_subgroup_finite_subset : ∀ (D : D7) (V : HSp D), ∀ N ∈ 𝓝 (1 : GA D V), ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ N := by
  intro D V N hN
  obtain ⟨i0, -, -, i3, -, -, hK⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  have hL : (GlobalTheory.SW.stdL D.host.E V.rank).FG ∧ Submodule.span D.host.E
      (GlobalTheory.SW.stdL D.host.E V.rank : Set (Fin V.rank → D.host.E)) = ⊤ := by
    refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
    rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin V.rank)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    apply Submodule.subset_span
    exact ⟨a, by simp⟩
  choose K hK1 hK2 hK3 _ using fun n : ℕ => hK _ n.factorial hL n.factorial_pos
  have hanti : Antitone fun n => (K n : Set (GA D V)) ∩ GfC V := by
    intro m n hmn k hk
    refine ⟨(hK1 m k).2 ⟨((hK1 n k).1 hk.1).1, fun u hu => ?_⟩, hk.2⟩
    obtain ⟨w, hw, e⟩ := ((hK1 n k).1 hk.1).2 u hu
    obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hmn
    exact ⟨c • w, nsmul_mem hw c, by rw [e, hc, mul_smul]⟩
  obtain ⟨n, hn⟩ := exists_subset_nhds_of_isCompact' (U := N) hanti.directed_ge hK3 (fun n => (hK3 n).isClosed)
    (fun x hx => by
      rw [Set.mem_iInter] at hx
      rwa [GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V (hx 0).2 (mem_GinfC_of_cong V x fun n => (hK1 n x).1 (hx n).1)])
  exact ⟨K n, hK2 n, fun k hk hf => hn ⟨hk, hf⟩⟩

end GlobalTheory.Mem.SmallSub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreimagePositiveResidueDegree
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory

set_option backward.isDefEq.respectTransparency.types false in

theorem exists_residueDegree_pos_of_mem_range (W Z : Scheme.{0}) (g : W ⟶ Z) [QuasiCompact g]
    [LocallyOfFiniteType g] (z : Z) (hz : z ∈ Set.range g) :
    ∃ w, g w = z ∧ 0 < g.residueDegree w := by
  obtain ⟨w₀, hw₀⟩ := hz
  let F := g.fiber z
  have hne : (Set.univ : Set F).Nonempty := ⟨(g.fiberHomeo z).symm ⟨w₀, hw₀⟩, trivial⟩
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton isClosed_univ hne
  have h₁ : LocallyOfFiniteType (F.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  have h₂ : LocallyOfFiniteType (g.fiberToSpecResidueField z) := by
    exact MorphismProperty.pullback_snd _ _ inferInstance
  let h : F ⟶ Z := g.fiberι z ≫ g
  have e : h x = z := by
    have := (g.range_fiberι z).le ⟨x, rfl⟩
    simpa [h] using this
  let β : Z.residueField z ⟶ F.residueField x := (Z.residueFieldCongr e.symm).hom ≫ h.residueFieldMap x
  have hβ : Spec.map β = F.fromSpecResidueField x ≫ g.fiberToSpecResidueField z := by
    rw [← cancel_mono (Z.fromSpecResidueField z)]
    simp only [β, Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    simp [h, Scheme.Hom.fiber_fac]
  have hβft : β.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map β) := hβ ▸ inferInstance
    exact HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) |>.mp this
  have hβf : β.hom.Finite := by
    letI := β.hom.toAlgebra
    haveI : Algebra.FiniteType (Z.residueField z) (F.residueField x) := hβft
    exact finite_of_finite_type_of_isJacobsonRing _ _
  have hhf : (h.residueFieldMap x).hom.Finite := by
    have : h.residueFieldMap x = (Z.residueFieldCongr e.symm).inv ≫ β := by simp [β]
    rw [this, CommRingCat.hom_comp]
    exact hβf.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Z.residueFieldCongr e.symm).inv).2)
  refine ⟨g.fiberι z x, e, ?_⟩
  rw [show h.residueFieldMap x = g.residueFieldMap (g.fiberι z x) ≫ (g.fiberι z).residueFieldMap x
    from Scheme.residueFieldMap_comp _ _ _] at hhf
  letI := (g.residueFieldMap (g.fiberι z x)).hom.toAlgebra
  letI := ((g.fiberι z).residueFieldMap x).hom.toAlgebra
  letI := (g.residueFieldMap (g.fiberι z x) ≫ (g.fiberι z).residueFieldMap x).hom.toAlgebra
  haveI : IsScalarTower (Z.residueField (g (g.fiberι z x))) (W.residueField (g.fiberι z x))
      (F.residueField x) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite (Z.residueField (g (g.fiberι z x))) (F.residueField x) := hhf
  let φ := IsScalarTower.toAlgHom (Z.residueField (g (g.fiberι z x)))
    (W.residueField (g.fiberι z x)) (F.residueField x)
  haveI : Module.Finite (Z.residueField (g (g.fiberι z x))) (W.residueField (g.fiberι z x)) :=
    Module.Finite.of_injective φ.toLinearMap φ.toRingHom.injective
  exact Module.finrank_pos

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrincipalLevelFormOfFaceLevelMultiplicity
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.MultLevelP

theorem multT_mono {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (hJ : J' ⊆ J) (hχ : ∀ k ∈ J', χ' k = χ k) :
    MultT θ M J χ ≤ MultT θ M J' χ' := by
  unfold MultT Mult
  exact Submodule.map_mono (Submodule.span_mono fun T hT =>
    ⟨hT.aut, hT.cusp, fun v k hk g => by rw [hχ k hk]; exact hT.lev v k (hJ hk) g, hT.equiv, hT.cont⟩)

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}

theorem levS_flag1_sub (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) : levS V β (flag1L L) ⊆ levS V β L := by
  rintro κ ⟨hκ, hp, hr⟩
  have e : Formalism.L2.DIV.rTup β L (finE V κ) = 1 := Subgroup.mem_bot.1 hr
  refine ⟨hκ, hp, ?_⟩
  show Formalism.L2.DIV.rTup β L (finE V κ) ∈ L.P.H
  rw [e]
  exact L.P.H.one_mem

theorem levChi_flag1 (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {κ : GA D V} (hκ : κ ∈ levS V β (flag1L L)) :
    levChi V β (flag1L L) κ = levChi V β L κ := by
  obtain ⟨-, -, hr⟩ := hκ
  have e : Formalism.L2.DIV.rTup β L (finE V κ) = 1 := Subgroup.mem_bot.1 hr
  have h1 : Formalism.L2.DIV.rTup β L (finE V κ) ∈ L.P.H := e ▸ L.P.H.one_mem
  have h := levFn_withP (β := β) (L := L) L.P (finE V κ)
  change Formalism.L2.DIV.levFn β L (finE V κ) = _ at h
  have e1 : (⟨_, h1⟩ : L.P.H) = 1 := Subtype.ext e
  unfold levChi
  rw [levFn_flag1, h, Formalism.L2.DIV.extendOne_of_mem _ h1, e1, map_one, one_mul]

end GlobalTheory.MultLevelP

set_option maxHeartbeats 1600000 in

theorem GlobalTheory.MultLevelP.exists_form_of_mult : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (Tm : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)), Tm ∈ Mult.MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) → ∃ Fn ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ, (∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), Fn (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Fn h) ∧ R.cX.toMap R.prX Fn = Tm := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB b t Tm hTm
  have hθ := hB.models.inf
  have hc := hB.models.cX
  have hpr := hB.models.prX
  have hp := GlobalTheory.DefiniteMult.allPlus_parB (V := D.sp.X') _ (Nat.sub_le _ _) R.MX
  have hT0 : Tm ∈ MultT R.θ R.MX (levS _ R.βX (flag1L (datXP R t (R.levR F b))))
      (levChi _ R.βX (flag1L (datXP R t (R.levR F b)))) :=
    GlobalTheory.MultLevelP.multT_mono R.θ R.MX (GlobalTheory.MultLevelP.levS_flag1_sub (β := R.βX) (datXP R t (R.levR F b)))
      (fun k hk => GlobalTheory.MultLevelP.levChi_flag1 (datXP R t (R.levR F b)) hk) hTm
  have e : flag1L (datXP R t (R.levR F b)) = flag1L (R.datXt t) := rfl
  have hT1 : Tm ∈ MultT R.θ R.MX (levS _ R.βX (flag1L (R.datXt t))) (levChi _ R.βX (flag1L (R.datXt t))) := by
    rw [← e]; exact hT0
  have X := GlobalTheory.DefiniteMult.exists_form (D := D) (V := D.sp.X') (M := R.MX) (θ := R.θ) (c := R.cX) (pr := R.prX) (β := R.βX) (L := R.datXt t) hθ hp hc hpr hT1
  obtain ⟨Fn, hFn, hmap⟩ := X
  refine ⟨Fn, hFn, ?_, hmap⟩
  rintro ⟨q, hqQ⟩ hq h
  obtain ⟨κ, hκκ⟩ := GlobalTheory.DefiniteMult.exists_fin_lift (D := D) D.sp.X' q
  have hκ := hκκ.1
  have hκq := hκκ.2
  obtain ⟨g, hg⟩ := (finHom D.sp.X').rangeRestrict_surjective h
  subst hg
  have hqQ' : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q := by rw [hκq]; exact hqQ
  have eQ : (⟨_, hqQ'⟩ : (levEnv D.sp.X' R.βX (R.datXt t)).Q) = ⟨q, hqQ⟩ := Subtype.ext hκq
  have hq' : (R.B.R t).act_tie.red ⟨_, hqQ'⟩ ∈ (F.lvl b).P :=
    (congrArg (fun x => (R.B.R t).act_tie.red x ∈ (F.lvl b).P) eQ).mpr hq
  have key : ∀ (x y : (levEnv D.sp.X' R.βX (R.datXt t)).Q), x = y → ∀ (hx : (R.B.R t).act_tie.red x ∈ (F.lvl b).P)
      (hy : (R.B.R t).act_tie.red y ∈ (F.lvl b).P),
      ((levEnv D.sp.X' R.βX (R.datXt t)).ch x : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hx⟩ : D.what₂.LLˣ) : D.what₂.LL) =
        ((levEnv D.sp.X' R.βX (R.datXt t)).ch y : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hy⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
    rintro x _ rfl hx hy
    rfl
  have hbr := GlobalTheory.T.mem_level_group_face_level_iff_flag_group D G Pl0 T A Ks R F hB.grp.red_R b t κ hκ
  have hκS : κ ∈ levS _ R.βX (datXP R t (R.levR F b)) := hbr.1.2 ⟨hqQ', hq'⟩
  have hχ := hbr.2 hqQ' hq'
  have hM := (mem_multT _ _ _ _ _).1 hTm
  have hlev : ∀ x g', Tm x (g' * κ) = levChi _ R.βX (datXP R t (R.levR F b)) κ * Tm x g' := by
    intro x g'
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have := (GlobalTheory.mult_value_left_cont_level R.θ R.MX _ _ _ hM v).2.2 κ hκS g'
      rw [map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]
      exact congrArg (r * ·) this
    | add x y hx hy => rw [map_add, Pi.add_apply, Pi.add_apply, hx, hy, mul_add]
  have hb := (GlobalTheory.DefiniteMult.pair_bijective hθ hp hc hpr).1
  have hext : R.cX.ext Fn (g * κ) = levChi _ R.βX (datXP R t (R.levR F b)) κ • R.cX.ext Fn g := by
    refine hb (LinearMap.ext fun x => ?_)
    have a1 : R.prX (R.cX.ext Fn (g * κ)) x = Tm x (g * κ) := congrFun (LinearMap.congr_fun hmap x) (g * κ)
    have a2 : R.prX (R.cX.ext Fn g) x = Tm x g := congrFun (LinearMap.congr_fun hmap x) g
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, a1, a2, hlev]
  change R.cX.ρ (g * κ)⁻¹ (Fn ((finHom D.sp.X').rangeRestrict (g * κ))) =
    levChi _ R.βX (datXP R t (R.levR F b)) κ • R.cX.ρ g⁻¹ (Fn ((finHom D.sp.X').rangeRestrict g)) at hext
  rw [GlobalTheory.DefiniteMult.rho_right_inv R.cX.ρ g (hc.1 _ (inv_mem hκ)), map_mul] at hext
  have inj : Function.Injective (R.cX.ρ g⁻¹) := fun a a' haa => by
    have := congrArg (R.cX.ρ g) haa
    rwa [GlobalTheory.DefiniteEnd.rho_inv_cancel, GlobalTheory.DefiniteEnd.rho_inv_cancel] at this
  calc Fn ((finHom D.sp.X').rangeRestrict g * q) = Fn ((finHom D.sp.X').rangeRestrict g * (finHom D.sp.X').rangeRestrict κ) :=
      congrArg (fun x => Fn ((finHom D.sp.X').rangeRestrict g * x)) hκq.symm
    _ = levChi _ R.βX (datXP R t (R.levR F b)) κ • Fn ((finHom D.sp.X').rangeRestrict g) :=
      inj (hext.trans ((R.cX.ρ g⁻¹).map_smul _ _).symm)
    _ = _ := congrArg (fun c : ℂ => c • Fn ((finHom D.sp.X').rangeRestrict g)) (hχ.trans (key _ _ eQ hq' hq))

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAtStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_weight_definiteUnitary_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AU E n) (τ : E →+* ℂ), ∃! lam : DomWeight n, π.HasWt τ lam := by
  first | exact @GlobalTheory.DefU.AU.existsUnique_hasWt | exact GlobalTheory.DefU.AU.existsUnique_hasWt | (intros; apply GlobalTheory.DefU.AU.existsUnique_hasWt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilOfFixesStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weil_of_fixes' : ∀ (E K Ω : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra E K] [IsScalarTower E K Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A w) (h' : IsPlaceOver A W) (σ : Weil h), (∀ x : K, (σ : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x) → ∃ τ : Weil h', ∀ z : Ω, (σ : G E Ω) z = (τ : G K Ω) z := by
  first | exact @GlobalTheory.WeilSurj.exists_weil_of_fixes | exact GlobalTheory.WeilSurj.exists_weil_of_fixes | (intros; apply GlobalTheory.WeilSurj.exists_weil_of_fixes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZeroOfInvOfNotRegularNormalStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zero_of_inv_of_not_regular_normal : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ (x : X) (f : X.functionField), ¬ RegAt x f → ∃ z : X, z ⤳ x ∧ ZeroAt z f⁻¹ := by
  first | exact @GlobalTheory.NormalPole.exists_zeroAt_inv | exact GlobalTheory.NormalPole.exists_zeroAt_inv | (intros; apply GlobalTheory.NormalPole.exists_zeroAt_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteImageOfIsOpenStabilizerStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_image_of_isOpen_stabilizer_alt : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V), IsOpen {g : G | ρ g v = v} → ∀ S : Set G, IsCompact S → ((fun g => ρ g v) '' S).Finite := by
  first | exact @GlobalTheory.finite_image_of_isOpen_stabilizer | exact GlobalTheory.finite_image_of_isOpen_stabilizer | (intros; apply GlobalTheory.finite_image_of_isOpen_stabilizer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteNonemptyOffCharts
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjOrigin

open ProjSpace

theorem chartι_mem_chart_iff (R : Type) [CommRing R] (N : ℕ) (i : Fin (N + 1)) (j : {j // j ≠ i})
    (p : Sp (MvPolynomial {j // j ≠ i} R)) :
    chartι R N i p ∈ chart R N j.1 ↔ (X j : MvPolynomial {j // j ≠ i} R) ∉ p.asIdeal := by
  have h := Proj.awayι_preimage_basicOpen (grading R N) (X_mem R N i) one_pos (X_mem R N j.1) one_pos
  have e : awayToPoly R N i (HomogeneousLocalization.Away.isLocalizationElem (X_mem R N i) (X_mem R N j.1))
      = X j := by
    refine (awayToPoly_mk R N i _ _ _).trans ?_
    rw [pow_one, dehom_X_of_ne]
  rw [← e]
  exact (congrArg (spMap (awayToPoly R N i) p ∈ ·) h).to_iff

def origin {R K : Type} [CommRing R] [Field K] (N : ℕ) (φ : R →+* K) : Sp K ⟶ PSpace R N :=
  spMap (eval₂Hom φ fun _ : {j : Fin (N + 1) // j ≠ 0} => 0) ≫ chartι R N 0

end GlobalTheory.ProjOrigin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankComapOfLeRange
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ.RowIso

theorem finrank_eq_of_semi {σ : ℂ →+* ℂ} (hσ : Function.Bijective σ) {E F : Type} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (f : E →ₛₗ[σ] F) (hf : Function.Bijective f) :
    Module.finrank ℂ E = Module.finrank ℂ F := by
  unfold Module.finrank
  congr 1
  exact rank_eq_of_equiv_equiv σ (AddEquiv.ofBijective f.toAddMonoidHom hf) hσ (fun r m => f.map_smulₛₗ r m)

theorem finrank_twSub (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V : Submodule ℂ E) :
    Module.finrank ℂ (Tw.sub s V) = Module.finrank ℂ V := by
  have hσ : Function.Bijective (cj s) := Function.Involutive.bijective (cj_cj s)
  let f : (Tw.sub s V) →ₛₗ[cj s] V :=
    { toFun := fun x => ⟨Tw.out x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact finrank_eq_of_semi hσ f ⟨fun x y h => Subtype.ext (congrArg Subtype.val h), fun y => ⟨⟨Tw.mk s y.1, y.2⟩, rfl⟩⟩

theorem finrank_comap_of_le_range {E F : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (e : E →ₗ[ℂ] F) (he : Function.Injective e) (V : Submodule ℂ F) (hV : V ≤ LinearMap.range e) :
    Module.finrank ℂ (V.comap e) = Module.finrank ℂ V := by
  have h := (Submodule.equivMapOfInjective e he (V.comap e)).finrank_eq
  rwa [Submodule.map_comap_eq_self hV] at h

theorem finrank_EEC {D : D7} (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp St) :
    Module.finrank ℂ (EEC St Gd) = Module.finrank ℂ (goodSub St Gd) := by
  let f : EEC St Gd →ₛₗ[starRingEnd ℂ] goodSub St Gd :=
    { toFun := fun x => ⟨star (x : L2X St), (mem_EEC St Gd _).1 x.2⟩
      map_add' := fun x y => Subtype.ext ((conjL (muX St)).map_add _ _)
      map_smul' := fun c x => Subtype.ext ((conjL (muX St)).map_smulₛₗ c _) }
  refine finrank_eq_of_semi (Function.Involutive.bijective (fun z => Complex.conj_conj z)) f ⟨fun x y h => ?_, fun y => ?_⟩
  · exact Subtype.ext (star_injective (congrArg Subtype.val h))
  · refine ⟨⟨star (y : L2X St), ?_⟩, Subtype.ext (star_star _)⟩
    rw [mem_EEC, star_star]
    exact y.2

theorem finrank_of_evalTieT {D : D7} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} {M : DSModel (D.sp.Y 0) S}
    {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))} {E : Submodule ℂ (MMap M)}
    {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St} {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA} {t : GA D (D.sp.Y 0)} {c : ℝ}
    (hE : EvalTieT M μ 𝓕 E St Gd ι t c) : Module.finrank ℂ (goodSub St Gd) = Module.finrank ℂ E := by
  obtain ⟨_, _, j, _⟩ := hE
  rw [← finrank_EEC, ← j.finrank_eq]

theorem clauses {D : D7} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} (s : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs}
    (Dc : DefCols Df) (hK : St.LevelSubgroupCharacter) (Gd : GoodOp St) (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW St hK (wdD x))
    (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram) (Sp : SPer Dc) (hSp : Sp = spOf s Dc hK Gd wdD pw bR)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V : Submodule ℂ E) (n : ℝ)
    (sEE : E →ₗ⋆[ℂ] Sp.HH) (sEEc : E →ₗ⋆[ℂ] Tw s (HHX St)) (h : HEq sEE sEEc)
    (h1 : ∀ e ∈ V, n * ‖sEEc e‖ ^ 2 = ‖e‖ ^ 2)
    (h2 : ∀ e ∈ V, ((Tw.out (s := s) (sEEc e) : HHX St) : L2X St) ∈ goodSub St Gd)
    (h3 : Module.finrank ℂ (goodSub St Gd) = Module.finrank ℂ V) :
    (∀ e ∈ V, n * ‖sEE e‖ ^ 2 = ‖e‖ ^ 2) ∧ (∀ e ∈ V, sEE e ∈ Sp.Rw) ∧
      Module.finrank ℂ Sp.Rw = Module.finrank ℂ V := by
  subst hSp
  obtain rfl := eq_of_heq h
  refine ⟨h1, h2, ?_⟩
  rw [← h3]
  refine (finrank_twSub s ((goodSub St Gd).comap (HHX St).subtype)).trans ?_
  refine finrank_comap_of_le_range _ Subtype.val_injective _ ?_
  rw [Submodule.range_subtype]
  exact inf_le_left

theorem seeIso : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.toRealDat.models_HE → (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) ≤ R.toRealDat.EEat R.triv → ∀ (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp St) (hK : St.LevelSubgroupCharacter) (wdD : (F.Dc (R.toCx3 F).zs).Mem → D.what₂.Word) (pw : ∀ x, PerW St hK (wdD x)) (bR : ∀ x, Fin ((F.Dc (R.toCx3 F).zs).a x) → (D.mem (wdD x)).A.Mram), F.Sp (R.toCx3 F).zs = spOf (twAt D.what₂.embLL A3.A.v0) (F.Dc (R.toCx3 F).zs) hK Gd wdD pw bR → ∀ (ι : GA D (D.sp.Y 0) ≃* St.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ), 0 < c → EvalTieT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) St Gd ι t c → ∀ (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (sEEc : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (HHX St)) (κS : ℂ), HEq sEE sEEc → (∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) (hx : R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true))), sEEc x = Tw.mk (twAt D.what₂.embLL A3.A.v0) (κS • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) St Gd ι t c ⟨R.HE.e (Tw.out x), hx⟩) ∧ RealDat.nP F.lv2 true * ‖sEEc x‖ ^ 2 = ‖x‖ ^ 2) → (R.toCx3 F).SEEIso sEE := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hHE hle St Gd hK wdD pw bR hSp ι t c _ hE sEE sEEc κS hh hS
  refine clauses (twAt D.what₂.embLL A3.A.v0) (F.Dc (R.toCx3 F).zs) hK Gd wdD pw bR (F.Sp (R.toCx3 F).zs) hSp
    ((R.toCx3 F).EEl true) ((R.toCx3 F).nP true) sEE sEEc hh (fun e he => (hS e he).2) (fun e he => ?_) ?_
  · refine (congrArg (fun y : Tw (twAt D.what₂.embLL A3.A.v0) (HHX St) =>
      ((Tw.out y : HHX St) : L2X St) ∈ goodSub St Gd) (hS e he).1).mpr ?_
    show ((κS • sEEofTT (R.MY 0) R.ν0 R.fd0 _ St Gd ι t c ⟨R.HE.e (Tw.out e), he⟩ : HHX St) : L2X St) ∈ goodSub St Gd
    rw [Submodule.coe_smul]
    refine Submodule.smul_mem _ _ ?_
    unfold sEEofTT
    rw [dif_pos hE]
    exact (mem_EEC St Gd _).1 (hE.choose_spec.2.choose _).2
  · refine (finrank_of_evalTieT hE).trans ?_
    refine Eq.symm ((finrank_twSub (E := R.HE.H) (twAt D.what₂.embLL A3.A.v0)
      ((R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)).comap R.HE.e)).trans ?_)
    refine finrank_comap_of_le_range _ hHE.1 _ ?_
    rw [hHE.2.1]
    exact hle

end GlobalTheory.Mem.SJ.RowIso

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorsNeBotOfMemSumIntertwiningRangesStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedVectors_ne_bot_of_mem_sum_intertwining_ranges : ∀ {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X] {ι : Type} [Finite ι] {σ : Representation ℂ G V}, σ.IsIrreducible → ∀ {ρ : Representation ℂ G X} (T : ι → σ.IntertwiningMap ρ) (K : Subgroup G) {f : X}, f ∈ ⨆ j, LinearMap.range (T j).toLinearMap → f ≠ 0 → (∀ k ∈ K, ρ k f = f) → GlobalTheory.PRep.fixed σ K ≠ ⊥ := by
  first | exact @GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range | exact GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range | (intros; apply GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorChangeOrthonormalBasesSubstStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialVector_change_orthonormalBases_subst : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → ∀ (k : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (u : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ τ, k τ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ, u τ ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) → ∀ f, IsThetaFunO ψ S T f → ∀ P : PolF D T.rank S.rank, pureTensorO ψ θ S T (fun _ => 1) (cart M) (fun τ => BS τ * u τ) (fun τ => onb M τ * k τ) f P = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (fsub M.ε k u P) := by
  first | exact @GlobalTheory.FockBasis.pureTensorO_basis | exact GlobalTheory.FockBasis.pureTensorO_basis | (intros; apply GlobalTheory.FockBasis.pureTensorO_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandOperatorCommutesIsometryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_operator_commutes_isometry : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (θ : InfF D), IsInfFam θ → ∀ (τ : D.what₂.Tau) (k : ℕ) (φ : GA D V → ℂ), φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V → gelf θ V' τ k (I.tr φ) = I.tr (gelf θ V τ k φ) := by
  first | exact @GlobalTheory.Mem.Isom.IsoMat.gelf_tr | exact GlobalTheory.Mem.Isom.IsoMat.gelf_tr | (intros; apply GlobalTheory.Mem.Isom.IsoMat.gelf_tr <;> assumption)
end

