import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0222
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0190
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0048
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0294
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0293
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0287
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0086
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0092
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0161
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0197
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0206
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0223
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.PureDegreeZero
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0224

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSubquotientParabolicProductTwoFiniteLStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducibleSubquotient_parabolicProductTwo_finiteLength : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ₁ : Representation ℂ (GL (Fin r) k) V) (ρ₂ : Representation ℂ (GL (Fin t) k) W) (π : Irr k (r + t)), IsSmooth ρ₁ → IsSmooth ρ₂ → HasFiniteLength ρ₁ → HasFiniteLength ρ₂ → IsSubquotient π.π (prod₂ ρ₁ ρ₂) → ∃ (π₁ : Irr k r) (π₂ : Irr k t), IsSubquotient π₁.π ρ₁ ∧ IsSubquotient π₂.π ρ₂ ∧ IsSubquotient π.π (prod₂ π₁.π π₂.π) := by
  first | exact @GlobalTheory.ProdSubquot.irreducible_subquotient_prod₂ | exact GlobalTheory.ProdSubquot.irreducible_subquotient_prod₂ | (intros; apply GlobalTheory.ProdSubquot.irreducible_subquotient_prod₂ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfRegularAlgebraicPolarizedPStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgebraicHeckeChar_of_regularAlgebraic_polarizedPair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → PolarizedPair π χ → ∃ n : (maximalRealSubfield E →+* ℂ) → ℤ, IsAlgPos χ n := by
  first | exact @GlobalTheory.RegAlgCharAlg.isAlgPos_of_polarizedPair | exact GlobalTheory.RegAlgCharAlg.isAlgPos_of_polarizedPair | (intros; apply GlobalTheory.RegAlgCharAlg.isAlgPos_of_polarizedPair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsComplOfTempered
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.WeilDeligne.TemperedCharPol

open GlobalTheory.WeilDeligne.PrimDecomp Module

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem map_wtSpace {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (a : WDRep h V) (b : WDRep h V')
    (e : V ≃ₗ[ℂ] V') (he : ∀ σ v, e (a.ρ σ v) = b.ρ σ (e v)) (k : ℤ) :
    (wtSpace a k).map (e : V →ₗ[ℂ] V') = wtSpace b k := by
  apply le_antisymm
  · exact map_absSpace_le e.toLinearMap (he (frob h)) _
  · intro v hv
    refine ⟨e.symm v, ?_, by simp⟩
    exact (mem_absSpace_iff e (he (frob h)) _ (e.symm v)).mp (by rw [LinearEquiv.apply_symm_apply]; exact hv)

theorem isCompl_of_tempered {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (ha : a.Tempered) (m : ℕ) (hmtop : ∀ k : ℤ, (m : ℤ) < k → wtSpace a k = ⊥) :
    IsCompl (strand a.N (wtSpace a (-(m : ℤ))) m) (lowPart (wtSpace a) a.N m) := by
  obtain ⟨-, hNk⟩ := GlobalTheory.T.weil_deligne_weight_space_stable E Ω A w h _ a
  have hpure := ha (frob h) deg_frob
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have hq0 := zero_lt_one.trans hq
  have hind : iSupIndep (wtSpace a) := by
    refine iSupIndep_absSpace _ fun i j hij => ?_
    rw [Real.rpow_right_inj hq0 hq.ne'] at hij
    exact_mod_cast (by linarith : (i : ℝ) = j)
  have htop : ⨆ i, wtSpace a i = ⊤ := hpure.1
  have hbij : ∀ i : ℕ, Set.BijOn (a.N ^ i) (wtSpace a (-(i : ℤ))) (wtSpace a i) := by
    intro i
    simp only [wtSpace, Int.cast_neg, Int.cast_natCast]
    exact hpure.2 i
  exact GlobalTheory.T.primitive_strand_complement_lefschetz _ (wtSpace a) a.N m hind htop hNk hbij hmtop

theorem step {d : ℕ}
    (ih : ∀ x y : WD h, x.lpDim < d → x.tempered → y.tempered → (∀ g, x.charPol g = y.charPol g) → x = y)
    {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (a : WDRep h V) (b : WDRep h V')
    (hd : finrank ℂ V = d) (ha : a.Tempered) (hb : b.Tempered)
    (e : V ≃ₗ[ℂ] V') (he : ∀ σ v, e (a.ρ σ v) = b.ρ σ (e v)) : WD.mk a = WD.mk b := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact WD.sound ⟨e, he, fun v => by rw [Subsingleton.elim v 0]; simp⟩
  obtain ⟨m, hm0, hmtop⟩ := GlobalTheory.T.tempered_weight_space_bound E Ω A w h V a ha hV
  have hmap := map_wtSpace a b e he
  have hmtop' : ∀ k : ℤ, (m : ℤ) < k → wtSpace b k = ⊥ := fun k hk => by
    rw [← hmap, hmtop k hk, Submodule.map_bot]
  obtain ⟨hρa, hNa⟩ := GlobalTheory.T.weil_deligne_weight_space_stable E Ω A w h _ a
  obtain ⟨hρb, hNb⟩ := GlobalTheory.T.weil_deligne_weight_space_stable E Ω A w h _ b
  obtain ⟨hBa, hCa⟩ := GlobalTheory.T.weight_filtration_strand_decomposition E Ω A w h _ a m hρa hNa hmtop
  obtain ⟨hBb, hCb⟩ := GlobalTheory.T.weight_filtration_strand_decomposition E Ω A w h _ b m hρb hNb hmtop'
  have e1a := GlobalTheory.T.weil_deligne_direct_sum_of_compl E Ω A w h _ a _ _ hBa hCa (isCompl_of_tempered a ha m hmtop)
  have e1b := GlobalTheory.T.weil_deligne_direct_sum_of_compl E Ω A w h _ b _ _ hBb hCb (isCompl_of_tempered b hb m hmtop')
  have e2a := GlobalTheory.T.tempered_top_weight_strand E Ω A w h _ a m (fun σ v hv => hρa _ σ v hv) hBa ha hmtop
  have e2b := GlobalTheory.T.tempered_top_weight_strand E Ω A w h _ b m (fun σ v hv => hρb _ σ v hv) hBb hb hmtop'

  have hy : WD.mk (restrictρ a (wtSpace a (-(m : ℤ))) (fun σ v hv => hρa _ σ v hv)) =
      WD.mk (restrictρ b (wtSpace b (-(m : ℤ))) (fun σ v hv => hρb _ σ v hv)) := by
    refine WD.sound ⟨(e.submoduleMap (wtSpace a (-(m : ℤ)))).trans (LinearEquiv.ofEq _ _ (hmap _)),
      fun σ v => ?_, fun v => ?_⟩
    · apply Subtype.ext
      simp [he]
    · simp
  have hB : WD.mk (restrict a _ hBa) = WD.mk (restrict b _ hBb) := by rw [e2a, e2b, hy]

  have hcC : ∀ g, (WD.mk (restrict a _ hCa)).charPol g = (WD.mk (restrict b _ hCb)).charPol g := by
    intro g
    have hab : (WD.mk a).charPol g = (WD.mk b).charPol g := by
      rw [WD.charPol_mk, WD.charPol_mk, ← LinearEquiv.charpoly_conj e]
      congr 1
      ext v
      simp [LinearEquiv.conj_apply, he]
    rw [e1a, e1b, WD.charPol_lpSum, WD.charPol_lpSum, hB] at hab
    exact mul_left_cancel₀ (WD.charPol_monic _ g).ne_zero hab
  have htC : (WD.mk (restrict a _ hCa)).tempered :=
    GlobalTheory.T.tempered_of_tempered_lpSum' E Ω A w h _ _ (by rw [← e1a, WD.tempered_mk]; exact ha)
  have htC' : (WD.mk (restrict b _ hCb)).tempered :=
    GlobalTheory.T.tempered_of_tempered_lpSum' E Ω A w h _ _ (by rw [← e1b, WD.tempered_mk]; exact hb)
  have hdim : (WD.mk (restrict a _ hCa)).lpDim < d := by
    have h1 := congrArg WD.lpDim e1a
    rw [WD.lpDim_sum, WD.lpDim_mk, hd] at h1
    have hUpos : 0 < finrank ℂ (wtSpace a (-(m : ℤ))) :=
      Nat.pos_of_ne_zero fun h0 => hm0 (Submodule.finrank_eq_zero.mp h0)
    have hBpos : 0 < (WD.mk (restrict a _ hBa)).lpDim := by
      rw [WD.lpDim_mk]
      exact hUpos.trans_le (Submodule.finrank_mono (le_strand _ _ _))
    omega
  rw [e1a, e1b, hB, ih _ _ hdim htC htC' hcC]

theorem main : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x y : WD h), x.tempered → y.tempered → (∀ g : Weil h, x.charPol g = y.charPol g) → x = y := by
  intro E Ω _ _ _ _ _ A w h
  have key : ∀ d : ℕ, ∀ x y : WD h, x.lpDim = d → x.tempered → y.tempered →
      (∀ g, x.charPol g = y.charPol g) → x = y := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro x y hxd hx hy hc
      induction x using WD.ind with
      | hP n a =>
      induction y using WD.ind with
      | hP n' b =>
      rw [WD.tempered_mk] at hx hy
      rw [WD.lpDim_mk] at hxd
      obtain ⟨e, he⟩ := GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq E Ω A w h n n' a b
        (fun σ => by rw [← WD.charPol_mk, ← WD.charPol_mk]; exact hc σ)
      exact step (fun x y hxy => ih _ hxy x y rfl) a b hxd hx hy e he
  exact fun x y => key _ x y rfl

end GlobalTheory.WeilDeligne.TemperedCharPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstAtOfIsCrysAt
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.CrysSst

open Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PMon Module TensorProduct

theorem finrank_Dst_le {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V) :
    FiniteDimensional ℚ_[l] ↥(Dst P ρ) ∧
      finrank ℚ_[l] ↥(Dst P ρ) ≤ finrank ℚ_[l] V * finrank ℚ_[l] ↥(K0 K) := by
  obtain ⟨hdom, hreg, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
  have hup := GlobalTheory.PstRank.rank_DpstUr_le P hdom hreg ρ
  haveI : FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) :=
    Module.rank_lt_aleph0_iff.mp (hup.trans_lt (Cardinal.nat_lt_aleph0 _))
  have hup' : finrank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) ≤ finrank ℚ_[l] V := by
    rw [← finrank_eq_rank] at hup
    exact_mod_cast hup
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  let val : DpstUr P ρ →+ V ⊗[ℚ_[l]] Bst P :=
    (Dpst P ρ).subtype.toAddMonoidHom.comp (toUr P ρ).symm.toAddMonoidHom
  have hSD : Dst P ρ ≤ Dpst P ρ := fun s hs => (mem_Dpst P ρ).mpr ⟨K, fun g _ => (mem_Dst P ρ).mp hs g⟩
  obtain ⟨b, hbS, hsp, hli⟩ := exists_linearIndependent ↥(MaximalUnramifiedExtension l) {y : DpstUr P ρ | val y ∈ Dst P ρ}
  haveI : Finite ↥b := hli.finite
  letI : Fintype ↥b := Fintype.ofFinite _
  have hspan : ∀ y : DpstUr P ρ, y ∈ Submodule.span ↥(MaximalUnramifiedExtension l) b → ∃ c : ↥b → ↥(MaximalUnramifiedExtension l),
      ∑ i, c i • (i : DpstUr P ρ) = y := fun y hy => by
    rw [← Submodule.mem_span_range_iff_exists_fun, Subtype.range_coe]; exact hy
  let inc : ↥(K0 K) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) := IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l)
  let f : (↥b → ↥(K0 K)) →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P :=
    { toFun := fun c => ∑ i, mulV P ℚ_[l] V (inc (c i)) (val i)
      map_add' := fun c c' => by simp [Finset.sum_add_distrib]
      map_smul' := fun q c => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => mulV_padic_smul P _ V q (inc (c i)) (val i) }
  have hle : Dst P ρ ≤ LinearMap.range f := by
    intro s hs
    obtain ⟨c, hc⟩ := hspan (toUr P ρ ⟨s, hSD hs⟩) (hsp ▸ Submodule.subset_span hs)
    have hfix : ∀ i, (c i : Om l) ∈ K.1 := fun i => mem_of_GK_fixed fun g => by
      have := semilinear_coord_fixed hli (fun a => ⟨_, galois_mem_Kur g a⟩)
        (actD P ρ g).toAddMonoidHom
        (fun a y => LinearMap.congr_fun (actD_mulD P ρ g a _ rfl) y)
        (fun j => Subtype.ext ((mem_Dst P ρ).mp (hbS j.2) g)) c
        (by rw [hc]; exact Subtype.ext ((mem_Dst P ρ).mp hs g)) i
      exact congrArg Subtype.val this
    refine ⟨fun i => ⟨c i, hfix i, (c i).2⟩, ?_⟩
    have := congrArg val hc
    rw [map_sum] at this
    exact this
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  have h1 : finrank ℚ_[l] ↥(Dst P ρ) ≤ Fintype.card ↥b * finrank ℚ_[l] ↥(K0 K) := by
    refine (Submodule.finrank_mono hle).trans ((LinearMap.finrank_range_le f).trans ?_)
    simp [Module.finrank_pi_fintype]
  exact h1.trans (Nat.mul_le_mul_right _ (hli.fintype_card_le_finrank.trans hup'))

theorem isSst_of_isCrys {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    {K LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (h : IsCrys (P.PD K) ρ) : IsSst P ρ := by
  haveI := LL.2
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  obtain ⟨hfin, hb⟩ := finrank_Dst_le P AI T (GlobalTheory.PstCoeff.resQ ρ)
  have hD : Dst P (GlobalTheory.PstCoeff.resQ ρ) = (Dst P ρ).restrictScalars ℚ_[l] := by
    ext x
    simp [mem_Dst, GlobalTheory.PstCoeff.stRep_resQ]
  have e : finrank ℚ_[l] ↥(Dst P (GlobalTheory.PstCoeff.resQ ρ)) = finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 ↥(Dst P ρ) := by
    rw [hD, finrank_mul_finrank]
    rfl
  have hfin' : FiniteDimensional ℚ_[l] ↥((Dst P ρ).restrictScalars ℚ_[l]) := hD ▸ hfin
  haveI : Module.Finite ℚ_[l] ↥(Dst P ρ) := hfin'
  haveI : FiniteDimensional ↥LL.1 ↥(Dst P ρ) :=
    Module.Finite.of_restrictScalars_finite ℚ_[l] ↥LL.1 ↥(Dst P ρ)
  have hV : finrank ℚ_[l] V = finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 V := (finrank_mul_finrank ℚ_[l] ↥LL.1 V).symm
  have hup : finrank ↥LL.1 ↥(Dst P ρ) ≤ finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 V := by
    rw [e, hV] at hb
    refine Nat.le_of_mul_le_mul_left ?_ (finrank_pos (R := ℚ_[l]) (M := ↥LL.1))
    calc finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 ↥(Dst P ρ)
        ≤ finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 V * finrank ℚ_[l] ↥(K0 K) := hb
      _ = finrank ℚ_[l] ↥LL.1 * (finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 V) := by ring
  have hle : (Dcris (P.PD K) ρ).map (crisIncl P ↥LL.1 V) ≤ Dst P ρ := fun x hx =>
    ((mem_Dst_and_monV_eq_zero_iff l P K LL V ρ x).mpr hx).1
  have hlo : finrank ↥LL.1 ↥(Dcris (P.PD K) ρ) ≤ finrank ↥LL.1 ↥(Dst P ρ) := by
    rw [(Submodule.equivMapOfInjective _ (crisIncl_injective P) (Dcris (P.PD K) ρ)).finrank_eq]
    exact Submodule.finrank_mono hle
  unfold IsCrys at h
  unfold IsSst
  exact le_antisymm hup (h ▸ hlo)

end GlobalTheory.CrysSst

theorem GlobalTheory.CrysSst.isSstAt_of_isCrysAt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r : ↥Gw →* GL (Fin a) (Om l)), IsCrysAt P Bw r → IsSstAt P Bw r := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw a r hc
  obtain ⟨T⟩ := hT
  obtain ⟨LL', r', hm, hcr⟩ := hc
  exact ⟨LL', r', hm, GlobalTheory.CrysSst.isSst_of_isCrys P AI T (Bw.repE LL' r') hcr⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSystemsLowerBoundsSecondRealPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.TwU.SiteSys

variable {D : D7}

theorem orbMap_posPl (p : ℕ) (r : OrbitPlaces.Pl D) (e : ℕ) (s : ZMod (nP D p)) :
    OrbitPlaces.orbMap D p (posPl D p r e) s = OrbitPlaces.orbMap D p r (s + (e : ZMod (nP D p))) := by
  unfold OrbitPlaces.orbMap
  rw [posPl_add, ZMod.val_add, ZMod.val_natCast, posPl_mod, ← posPl_add D p r s.val, posPl_mod, posPl_add, add_comm]

theorem topsOrb_posPl (p : ℕ) (r : OrbitPlaces.Pl D) (e : ℕ) :
    OrbitPlaces.topsOrb D p (posPl D p r e) = OrbitPlaces.topsOrb D p r := by
  unfold OrbitPlaces.topsOrb
  refine Finset.card_equiv (Equiv.addRight (e : ZMod (nP D p))) fun s => ?_
  simp [orbMap_posPl]

theorem errF_posPl {L : SizeData₂ D} (K : Consts) (ce : ErrC) (j p : ℕ) (r : OrbitPlaces.Pl D) (e : ℕ) :
    OrbitPlaces.errF L K ce j p (posPl D p r e) = OrbitPlaces.errF L K ce j p r := by
  have h : ∑ s : ZMod (nP D p), wPl D j (OrbitPlaces.orbMap D p (posPl D p r e) s) =
      ∑ s : ZMod (nP D p), wPl D j (OrbitPlaces.orbMap D p r s) := by
    simp only [orbMap_posPl]
    exact Equiv.sum_comp (Equiv.addRight (e : ZMod (nP D p))) (fun s => wPl D j (OrbitPlaces.orbMap D p r s))
  unfold OrbitPlaces.errF
  rw [h, topsOrb_posPl]

theorem posPl_true_one {p : ℕ} (hs : ¬ IsSg D p) (t : HH D) : posPl D p (true, t) 1 = (true, t + hP D p) := by
  simp [posPl, partner, hs]

theorem notSg {T p : ℕ} (hg : GIdx D.host T p) : ¬ IsSg D p := by
  intro h
  have h1 : D.host.cls p = PrimeClass.inertClass := hg.2.2.1
  unfold IsSg at h
  rw [h1] at h
  exact absurd h (by decide)

theorem sysTw_sites : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts) (Dx : DivX D) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (E : OrbitPlaces.Ent D) (LC : D.what₂.Tup → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Σ Lv : Levels (Y.Fl u w hg), Chain Lv), LatTied hT X Y → FillsAll hT Y → L.FDef → OrbitPlaces.OrbitLetterBoundsAll 11 1 → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge 11 1 K ce → (∀ μ, DV.Used D μ → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), D.what₂.places.resChar w ∉ Dx.Qp μ → SiteAdm D u w hg (Y.Fl u w hg) (LC μ u w hg).1 (LC μ u w hg).2) → SysTw D L X K Dx (reW Y LC) lev Xe ce 1 := by
  intro D L hT X Y K Dx lev Xe ce E LC hty hfa hF hadm hSh hCL hS hE μ hμ hT' hty' u w hg hQ
  obtain ⟨i, std, vp, unif, eO, eO_spec, dG, dG_spec, om, Y5, hA, h0, hj⟩ := hS μ hμ u w hg hQ
  obtain ⟨r, hr1, hr2⟩ := GlobalTheory.SecondOrbits.places_off_first_orbits D u w hg L hT X Y hty
  refine ⟨i, std, vp, unif, eO, eO_spec, dG, dG_spec, om, Y5, hA,
    fun v j => if ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n then
      FOrb D j (D.what₂.places.resChar w) (true, r v) - OrbitPlaces.errF L K ce j (D.what₂.places.resChar w) (true, r v) else 0,
    ?_, ?_⟩
  · intro v hv j hjm
    obtain ⟨-, -, -, a2c, -, -, -, -, -, -, -, -, a11⟩ := hA
    by_cases hp : ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n
    · simp only [if_pos hp]
      exact GlobalTheory.T.local_model_bound_place_over_second_embedding D u w hg L hT X Y K ce E hty hfa hadm hSh hCL hp _ _ std vp unif eO eO_spec dG dG_spec om Y5 a2c v (r v)
        (hr1 v hv).1 (hr1 v hv).2.2 j hjm
    · simp only [if_neg hp]
      exact a11 v j (lt_of_lt_of_eq hjm (hty u w hg).1.symm)
  · refine (GlobalTheory.T.low_term_le_second_real_place_bounds D u w hg L X K ce Xe dG hF h0 hj).trans (sub_le_sub_right (le_of_eq ?_) _)
    refine Finset.sum_congr rfl fun j _ => ?_
    refine (hr2 (fun t => if ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n then
      FOrb D j (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce j (D.what₂.places.resChar w) (true, t) else 0) ?_).symm
    intro t
    have h1 := posPl_true_one (notSg hg) t
    have h2 := FOrb_step D j (D.what₂.places.resChar w) (true, t) 1
    have h3 := errF_posPl (L := L) K ce j (D.what₂.places.resChar w) (true, t) 1
    rw [h1] at h2 h3
    simp only [h2, h3]

end GlobalTheory.TwU.SiteSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatchedSphericalPairsCommuteCompositeLiftStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_spherical_pairs_commute_composite_lift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ SF, IsSF R SF → ∀ t P, Good R t P → ∀ cX c0, MatchE R t P cX c0 → ∀ hX, IsOpsX R t hX → (∀ h, IsOpsE R h → ∀ y, R.Th t (hX P cX y) = h P c0 (R.Th t y)) ∧ ∀ c, ∀ w ∈ EEc R SF c, hX P cX (LinearMap.adjoint (R.Th t) w) = evC (Yc D 0) P (fun d => c P (dualLab d)) c0 • LinearMap.adjoint (R.Th t) w := by
  first | exact @GlobalTheory.Hk3.SysE.matched_commute | exact GlobalTheory.Hk3.SysE.matched_commute | (intros; apply GlobalTheory.Hk3.SysE.matched_commute <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodProductCommutesFrobeniusZpowStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodProduct_commutes_frobenius_zpow : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] (ρs ρt : Representation ↥L.1 ↥(GK K) V) (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1) (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρs)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρm)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρt)] (n : ℤ) (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)), ((phiU P ρt ^ n : (Module.End ↥L.1 ↥(Dpst P ρt))ˣ) : Module.End ↥L.1 ↥(Dpst P ρt)) (GlobalTheory.Pst.TwistLetters.dmul P ρs ρt ρm χ hm ht x y) = GlobalTheory.Pst.TwistLetters.dmul P ρs ρt ρm χ hm ht (((phiU P ρs ^ n : (Module.End ↥L.1 ↥(Dpst P ρs))ˣ) : Module.End ↥L.1 ↥(Dpst P ρs)) x) (((phiU P ρm ^ n : (Module.End ↥L.1 ↥(Dpst P ρm))ˣ) : Module.End ↥L.1 ↥(Dpst P ρm)) y) := by
  first | exact @GlobalTheory.Pst.TwistLetters.phiU_zpow_dmul | exact GlobalTheory.Pst.TwistLetters.phiU_zpow_dmul | (intros; apply GlobalTheory.Pst.TwistLetters.phiU_zpow_dmul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDetStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_local_component_det : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (π : D.naut.CG 1) (w : PlE D.host) (ξ : (w.adicCompletion D.host.E)ˣ →* ℂˣ) (h : IsComp (P.chr.e1 π).1 w ξ), P.T.e w (D.naut.locG π w) = rcAt hL D w 1 (Irr.ofDet 1 ξ h.1) := by
  first | exact @GlobalTheory.RankOneComp.locG_rankOne_eq_rcAt | exact GlobalTheory.RankOneComp.locG_rankOne_eq_rcAt | (intros; apply GlobalTheory.RankOneComp.locG_rankOne_eq_rcAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SstCpOfNoIwahori
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open GlobalTheory.GalCut7

noncomputable section

namespace GlobalTheory.IwaPkg

open GlobalTheory.GalCut GlobalTheory.TheRec GlobalTheory.Cong GlobalTheory.UnitaryBC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def SstCp (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
    ∀ σ, π.IsLocComp w σ → PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥ →
      IsSstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ ∀ rc, IsTheRec h rc →
        ∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = (rc (algNorm σ)).charPol g

def IwaLimit : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) →
    ∀ w₀ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), SplitAtt π ι r ∧ ∀ w, IsSplitAt w → Apart w w₀ → SstCp π ι r w

theorem sstCp_of_noIwahori {π : CuspSub E a} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin a) (Qbar l)} {w : HeightOneSpectrum (𝓞 E)}
    (h0 : ∀ σ, π.IsLocComp w σ → PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) = ⊥) : SstCp π ι r w := by
  intro P AI _ A h O _ _ _ Bw hj σ hσ hI
  exact absurd (h0 σ hσ) hI

end GlobalTheory.IwaPkg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardBasesHyperbolicPairOrthonormalStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardSeries_scaled_eq_orthonormalSeries_hyperbolicSubst : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → OrbitPlaces.OrbOK D p → ((IsResidueClassZero D p ∧ hP D p ≠ 0) ∨ IsSg D p) → ∀ (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p), OwOK (nP D p) σ om oms → TrDual (nP D p) σ om oms → ∀ (R : Finset (OrbitPlaces.Pl D)), OrbitPlaces.IsReps D p R → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b → TaylorLogMetric.Orthonormal D b → ∃ f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p, HypPair σ f f' ∧ ∀ (c : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (stdSer D lam (fun _ => 1) P P' G) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst (hypZ D p σ om oms R f f') (thOrth D lam c b G) := by
  first | exact @GlobalTheory.KerStd.hyp_of_stdBases | exact GlobalTheory.KerStd.hyp_of_stdBases | (intros; apply GlobalTheory.KerStd.hyp_of_stdBases <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaTrilinearFormLocalGroupInvariantStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTrilinearForm_localGroup_invariant : ∀ (D : D7) (M : MtFam D) (i : D.nd.Loc) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (X : RowMod D rep (D.nd.j i)) (μ η : HChar D.host.E) (Θ : ThetaMod D M i X μ η) (s : SplitPlace D.host.E) (μw ηw : (s.w.adicCompletion D.host.E)ˣ →* ℂˣ) (ι : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] Θ.Ω) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), (∀ (h : GAf D.host.E D.R.nV) (g : GAf D.host.E D.R.r), TrivOutside {s.v} h → TrivOutside {s.v} g → ∀ Φ Φ' : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E)), (Φ' : Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E) → ℂ) = om μw (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r g)) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV h)) Φ → Θ.ω (h, g) (ι Φ) = ((ηw (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV h))) : ℂˣ) : ℂ) • ι Φ') → ∀ (Wl Vl : Type) [AddCommGroup Wl] [Module ℂ Wl] [AddCommGroup Vl] [Module ℂ Vl] (πl : Representation ℂ (GL (Fin D.R.nV) (s.w.adicCompletion D.host.E)) Wl) (σl : Representation ℂ (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)) Vl) (T' : Wl →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ)), (∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → ∀ a, ((T' (πl (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) a) : ↥(NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ)) : GAf D.host.E D.R.nV → (M.loc i).wt.W) = NG.rt D.host.E D.R.nV x (T' a : GAf D.host.E D.R.nV → (M.loc i).wt.W)) → ∀ (T'' : Vl →ₗ[ℂ] ↥X.C), (∀ x : GAf D.host.E D.R.r, TrivOutside {s.v} x → ∀ a, ((T'' (σl (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a) : ↥X.C) : X.A) = X.ρ x (T'' a)) → ∀ (g : GL (Fin D.R.r) (s.w.adicCompletion D.host.E)) (h : GL (Fin D.R.nV) (s.w.adicCompletion D.host.E)) (Φ Φ' : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E))), (Φ' : Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E) → ℂ) = om μw g h Φ → ∀ a c', Θ.Λ (ι Φ') (T' (twist πl (detChar (Fin D.R.nV) ηw) h a)) (T'' (σl g c')) = Θ.Λ (ι Φ) (T' a) (T'' c') := by
  first | exact @GlobalTheory.ThetaLocInv.thetaRead_inv | exact GlobalTheory.ThetaLocInv.thetaRead_inv | (intros; apply GlobalTheory.ThetaLocInv.thetaRead_inv <;> assumption)
end

