import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0295
import Formalism.PieriBlockIdeals.PieriColumnMinors.HeightDescentMinors
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1136
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1149
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdFreeTopFormEqZeroOfIsPrimeOf
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

theorem formOrd_dForm_of_isPrimeOf : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (D : ℕ) (x : Fin D → Q),
  IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem) x) →
  ∀ P : Place cL, P.IsPrimeOf Q → P.formOrd (dForm cL (fun i => (x i : L))) = 0 := by
  intro L _ cL Q hQ D x hx P hP
  let α : ℂ →+* Q := cL.codRestrict Q hQ.const_mem
  let ρ : Q →+* P.ring := RingHom.codRestrict Q.subtype P.ring (fun q => hP.1 q q.2)
  have hρ : ρ.comp α = P.const := RingHom.ext fun _ => Subtype.ext rfl
  have e : dForm cL (fun i => (x i : L)) = P.toRat D (dForm P.const fun i => ρ (x i)) := by
    have h := TopForm.formMap_dForm (D := D) (α := P.const) (β := cL) P.ring.subtype rfl (fun i => ρ (x i))
    refine Eq.trans ?_ h.symm
    congr 1
  let S : Submonoid Q :=
    { carrier := {b | (b : L) ≠ 0 ∧ P.ord b = 0}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨?_, ?_⟩
        · change (a : L) * b ≠ 0
          exact mul_ne_zero ha.1 hb.1
        · change P.ord ((a : L) * b) = 0
          rw [P.ord_mul ha.1 hb.1, ha.2, hb.2, add_zero]
      one_mem' := ⟨one_ne_zero, P.ord_one⟩ }
  letI := α.toAlgebra
  letI := P.const.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower ℂ Q P.ring := IsScalarTower.of_algebraMap_eq' hρ.symm
  haveI : IsLocalization S P.ring :=
    { map_units := fun ⟨b, hb⟩ => by
        have hinv : (b : L)⁻¹ ∈ P.ring := by
          rw [← P.ord_nonneg_iff (inv_ne_zero hb.1), P.ord_inv, hb.2, neg_zero]
        exact IsUnit.of_mul_eq_one (⟨(b : L)⁻¹, hinv⟩ : P.ring)
          (Subtype.ext (mul_inv_cancel₀ hb.1))
      surj := fun z => by
        obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hP.2 z z.2
        exact ⟨(⟨a, ha⟩, ⟨⟨b, hb⟩, hb0, hbo⟩), Subtype.ext e⟩
      exists_of_eq := fun {a b} e => by
        have h : (a : L) = b := congrArg (fun z : P.ring => (z : L)) e
        exact ⟨1, by rw [Subtype.ext h]⟩ }
  haveI : Algebra.FormallyEtale Q P.ring := .of_isLocalization S
  have hG : IsFreeGen P.ring (TopForm.formMap D ρ hρ (dForm α x)) :=
    hx.of_isBaseChange (isBaseChange_exteriorPower
      (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ Q P.ring) D)
  rw [TopForm.formMap_dForm] at hG
  rw [e]
  exact P.formOrd_toRat hG

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusMatrixCofactorEqQPowFrame
section
set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.WachPlace.FrameHeight

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {f : ℕ}
    (W : LocWach PD LL O v f)

theorem φD_smul_A (T : LocLat G Qp LL O) (a : LetA O f) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O f) W.EE a) x
  rwa [algebraMap_smul, W.φE_ext, algebraMap_smul] at this

theorem φpull_le_span {n : ℕ} (T : LocLat G Qp LL O) (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) :
    W.φpull T ≤ Submodule.span (LetA O f) (Set.range fun j => W.φD T (b j : W.DD T)) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  have e := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
  simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at e
  rw [← e, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [φD_smul_A]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem exists_inv {n : ℕ} (T : LocLat G Qp LL O) (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T))
    (PA : Matrix (Fin n) (Fin n) (LetA O f))
    (hφ : ∀ k, W.φD T (b k : W.DD T) = ∑ m, PA m k • (b m : W.DD T)) (h : ℕ) (i : ZMod f)
    (h5 : ∀ y ∈ W.Nl T i, W.Q ^ h • y ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (i - 1))) :
    ∃ Qm : Matrix (Fin n) (Fin n) (PowerSeries O),
      (PA.map fun a => a i) * Qm = (W.Q i ^ h) • (1 : Matrix (Fin n) (Fin n) (PowerSeries O)) := by
  have hsp : ∀ k, ∃ c : Fin n → LetA O f,
      ∑ j, c j • W.φD T (b j : W.DD T) = W.Q ^ h • (letE i : LetA O f) • (b k : W.DD T) := by
    intro k
    have hy : (letE i : LetA O f) • (b k : W.DD T) ∈ W.Nl T i :=
      Submodule.mem_map_of_mem (b k).2
    have h1 := h5 _ hy
    have hle : Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (i - 1)) ≤ W.φpull T :=
      Submodule.span_mono (Set.image_mono (by
        rintro _ ⟨x, hx, rfl⟩
        exact (W.N T).smul_mem _ hx))
    exact (Submodule.mem_span_range_iff_exists_fun (LetA O f)).1 (φpull_le_span W T b (hle h1))
  choose c hc using hsp
  have hli : LinearIndependent (LetA O f) fun m => (b m : W.DD T) :=
    b.linearIndependent.map' (W.N T).subtype (Submodule.ker_subtype _)
  have key : ∀ k m, ∑ j, c k j * PA m j = if m = k then W.Q ^ h * (letE i : LetA O f) else 0 := by
    intro k
    have e1 : ∑ m, (∑ j, c k j * PA m j - if m = k then W.Q ^ h * (letE i : LetA O f) else 0) •
        (b m : W.DD T) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, Finset.sum_smul, mul_smul]
      rw [← hc k, sub_eq_zero, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hφ, Finset.smul_sum]
    intro m
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ e1 m)
  refine ⟨Matrix.of fun j k => c k j i, ?_⟩
  refine Matrix.ext fun m k => ?_
  have e2 := congrFun (key k m) i
  simp only [Finset.sum_apply, Pi.mul_apply] at e2
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  simp only [Matrix.map_apply, Matrix.of_apply]
  rw [show (∑ j, PA m j i * c k j i) = ∑ j, c k j i * PA m j i from
    Finset.sum_congr rfl fun j _ => mul_comm _ _, e2]
  by_cases hmk : m = k
  · simp [hmk, letE]
  · simp [hmk]

end Generic

end GlobalTheory.WachPlace.FrameHeight

namespace GlobalTheory.WachPlace.FrameHeight

theorem frame_height : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (n h : ℕ) (γ : ((HW l).W K 1 LL hA.2.2).Gam) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T)) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)), GlobalTheory.AdmLoc.CrysWith ((D.loc l).PD K) ((HW l).W K 1 LL hA.2.2).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u ∧ u ≤ (h : ℤ)) → IsFrame ((HW l).W K 1 LL hA.2.2) T γ b N → ∀ i, ∃ Q : Mx (PowerSeries ↥(OL LL)) n n, (N.P i).map (inc l ↥(OL LL)) * Q = (q l ↥(OL LL) ^ h) • (1 : Mx (PowerSeries ↥(OL LL)) n n) := by
  intro D HW F Cm l _ K LL hA T U n h γ b N hU hb hfr i
  have hJ : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet ((HW l).W K 1 LL hA.2.2) T (fun _ => 0) (fun _ => h) := by
    intro τ i' hτ a ha
    haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ).1
    have h1 := (GlobalTheory.Per.JumpMult.jump_iff_of_finite ((D.loc l).PD K) T.ρ τ a).2.2.1 ha
    rw [hU.2 i' τ (fun x => DFunLike.congr_fun hτ x) a] at h1
    have h2 := hb i' a (Multiset.count_ne_zero.1 (by exact_mod_cast h1))
    exact ⟨by simpa using h2.1, h2.2⟩
  have h5 := (GlobalTheory.NL.Heights.heights_from_jumps D HW F Cm l K 1 LL hA.2.2 T (fun _ => 0) (fun _ => h)
    hU.1 hJ).2.1 i
  obtain ⟨Qm, hQm⟩ := exists_inv ((HW l).W K 1 LL hA.2.2) T b
    (fun m k => fun i => inc l ↥(OL LL) (N.P i m k)) hfr.2.1 h i h5
  have hq : ((HW l).W K 1 LL hA.2.2).Q i = q l ↥(OL LL) := by
    have e1 : ((HW l).W K 1 LL hA.2.2).Q = ((HW l).W K 1 LL hA.2.2).q := by
      unfold LocWach.Q
      rw [(HW l).W_s K 1 LL hA.2.2]
      rfl
    rw [e1]
    change ((HW l).W K 1 LL hA.2.2).q₀ = q l ↥(OL LL)
    have e2 := ((HW l).W K 1 LL hA.2.2).q₀_def
    rw [(D.loc l).PD_p K, ← (q_multiplicative_holds l ↥(OL LL)).1] at e2
    refine PowerSeries.ext fun j => ?_
    have e3 := congrArg (PowerSeries.coeff (j + 1)) e2
    simpa only [PowerSeries.coeff_succ_X_mul] using e3
  refine ⟨Qm, ?_⟩
  rw [← hq]
  exact hQm

end GlobalTheory.WachPlace.FrameHeight

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyHessianDeterminantRealPart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.FSDet

theorem sum_conj_mul_self {n : ℕ} (v : ReciprocityTheory.L2DbarEstimates.V n) :
    (∑ j, starRingEnd ℂ (v j) * v j) = (‖v‖ : ℂ) ^ 2 := by
  have h := EuclideanSpace.norm_sq_eq v
  have h2 : ((‖v‖ : ℂ)) ^ 2 = ((‖v‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [h2, h]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.conj_mul']

theorem det_one_add_vecMulVec' {m : Type} [Fintype m] [DecidableEq m] (a b : m → ℂ) :
    (1 + Matrix.vecMulVec a b).det = 1 + a ⬝ᵥ b := by
  have := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) a b
  rw [Matrix.vecMulVec_eq (ι := Unit), this, dotProduct_comm]

end GlobalTheory.FSDet

namespace GlobalTheory.FSDet

theorem det_fubiniStudy_hess :
    ∀ (n : ℕ) (v : ReciprocityTheory.L2DbarEstimates.V n), (ReciprocityTheory.L2DbarEstimates.cHess n (fun w => (Real.log (1 + ‖w‖ ^ 2) : ℂ)) v).det.re = ((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹ := by
  intro n v
  rw [GlobalTheory.T.complexHessian_log_one_add_normSq n v]
  set t : ℂ := 1 + (‖v‖ : ℂ) ^ 2 with ht
  have htr : t = ((1 + ‖v‖ ^ 2 : ℝ) : ℂ) := by rw [ht]; push_cast; rfl
  have ht0 : t ≠ 0 := by
    rw [htr]; exact_mod_cast (by positivity : (1 + ‖v‖ ^ 2 : ℝ) ≠ 0)
  have hM : (Matrix.of (fun j l => (if j = l then (1:ℂ) else 0) / t - (starRingEnd ℂ (v j) * v l) / t ^ 2) : Matrix (Fin n) (Fin n) ℂ)
      = t⁻¹ • (1 + Matrix.vecMulVec (fun j => -(starRingEnd ℂ (v j)) / t) (fun l => v l)) := by
    ext j l
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    field_simp
    ring
  rw [hM, Matrix.det_smul, det_one_add_vecMulVec', Fintype.card_fin]
  have hdot : (fun j => -(starRingEnd ℂ (v j)) / t) ⬝ᵥ (fun l => v l) = -((‖v‖ : ℂ) ^ 2) / t := by
    rw [← sum_conj_mul_self v, dotProduct, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hval : t⁻¹ ^ n * (1 + -((‖v‖ : ℂ) ^ 2) / t) = (((1 + ‖v‖ ^ 2 : ℝ) ^ (n + 1))⁻¹ : ℝ) := by
    have h1 : (1 + -((‖v‖ : ℂ) ^ 2) / t) = t⁻¹ := by
      field_simp
      rw [ht]; ring
    rw [h1, ← pow_succ, inv_pow, htr]
    push_cast
    rfl
  rw [hdot, hval, Complex.ofReal_re]

end GlobalTheory.FSDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreClosedSubvariety
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.FibreClosure

theorem interNum_genericFibre_eq_interNumRed : ∀ (B Y : Scheme.{0}) [IsIntegral B] (f : Y ⟶ B) (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → ∀ (x : G) (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z], i (genericPoint Z) = j x → ∀ (G' : Scheme.{0}) (j' : G' ⟶ Z) (s' : G' ⟶ Sp B.functionField), IsPullback j' s' (i ≫ f) (B.fromSpecStalk (genericPoint B)) → ∀ (ι : Type) [Fintype ι] (P : ι → LB Y), (∀ a, (P a).IsLB) → (letI := algebraΓOfHom s'; interNum B.functionField (structureModule G') (fun a => ((P a).pull i).pull j')) = (letI := algebraΓOfHom s; interNumRed B.functionField (⟨closure {x}, isClosed_closure⟩ : Closeds _) (fun a => (P a).pull j)) := by
  intro B Y _ f G j s hG x Z i _ _ hx G' j' s' hG' ι _ P hP
  obtain ⟨hj, hrj, -, -⟩ := GlobalTheory.T.generic_fibre_preimmersion_integral B Y f G j s hG
  obtain ⟨-, hrj', -, hint'⟩ := GlobalTheory.T.generic_fibre_preimmersion_integral B Z (i ≫ f) G' j' s' hG'

  let u : G' ⟶ G := hG.lift (j' ≫ i) s' (by rw [Category.assoc]; exact hG'.w)
  have hu₁ : u ≫ j = j' ≫ i := hG.lift_fst _ _ _
  have hu₂ : u ≫ s = s' := hG.lift_snd _ _ _
  have hsq : IsPullback j' u i j := IsPullback.of_bot (by rw [hu₂]; exact hG') hu₁.symm hG
  have : IsClosedImmersion u := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq ‹_›

  have hη : (i ≫ f) (genericPoint Z) = genericPoint B := by
    have : j x ∈ Set.range j := ⟨x, rfl⟩
    rw [hrj] at this
    rw [Scheme.Hom.comp_apply, hx]
    exact this
  have hne : Nonempty G' := by
    have : genericPoint Z ∈ (i ≫ f) ⁻¹' {genericPoint B} := hη
    rw [← hrj'] at this
    obtain ⟨y, -⟩ := this
    exact ⟨y⟩
  obtain ⟨_, hgen⟩ := hint' hne
  have hux : u (genericPoint G') = x := by
    apply (Scheme.Hom.isEmbedding j).injective
    rw [← Scheme.Hom.comp_apply, hu₁, Scheme.Hom.comp_apply, hgen, hx]
  have hrange : Set.range u = closure {x} := by
    apply subset_antisymm
    · rintro _ ⟨y, rfl⟩
      have hy : y ∈ closure {genericPoint G'} := by
        rw [(genericPoint_spec G').def]; trivial
      have := image_closure_subset_closure_image (f := u) u.continuous ⟨y, hy, rfl⟩
      rwa [Set.image_singleton, hux] at this
    · exact (Scheme.Hom.isClosedEmbedding u).isClosed_range.closure_subset_iff.2
        (Set.singleton_subset_iff.2 ⟨_, hux⟩)
  letI := algebraΓOfHom s'
  letI := algebraΓOfHom s
  rw [GlobalTheory.InterModel.interNumRed_eq_interNumOn _ u _ hrange,
    interNumOn_eq_interNum_pull (appTop_algebraΓOfHom u s hu₂) (fun a => pull_isLB (hP a) j)]
  refine interNum_congr_lbIso _ _ (fun a => pull_isLB (pull_isLB (hP a) i) j')
    (fun a => pull_isLB (pull_isLB (hP a) j) u) fun a => ?_
  exact LBIso.trans (pull_isLB (pull_isLB (hP a) i) j') (pull_isLB (hP a) (u ≫ j))
    (pull_isLB (pull_isLB (hP a) j) u)
    (GlobalTheory.GenSpread.lbIso_pull_pull (hP a) j' hu₁).symm
    (GlobalTheory.GenSpread.lbIso_pull_pull (hP a) u rfl)

end GlobalTheory.FibreClosure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointMorphismFactorization
section
open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NormFnField

variable {Z : Scheme.{0}} [IsIntegral Z] {K : Type} [Field K] [Algebra Z.functionField K]

theorem stalkIso_germ_app (g : Spec (CommRingCat.of K) ⟶ Z)
    (hg : g = Spec.map (CommRingCat.ofHom (algebraMap Z.functionField K)) ≫
      Z.fromSpecStalk (genericPoint Z))
    (U : Z.Opens) (hU : g (IsLocalRing.closedPoint K) ∈ U) (a : Γ(Z, U)) :
    (stalkClosedPointIso (CommRingCat.of K)).hom
        ((Spec (CommRingCat.of K)).presheaf.germ (g ⁻¹ᵁ U) (IsLocalRing.closedPoint K) hU
          (g.app U a)) =
      algebraMap Z.functionField K
        (Z.presheaf.germ U (genericPoint Z) ((genericPoint_specializes _).mem_open U.isOpen hU) a) := by
  subst hg
  have e := Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
    (CommRingCat.ofHom (algebraMap Z.functionField K)) U hU
  refine Eq.trans ?_ (congrArg (fun q => q.hom a) e)
  change _ = (stalkClosedPointIso (CommRingCat.of K)).hom.hom ((Scheme.Hom.stalkMap _ _).hom
    ((Z.presheaf.germ U _ hU).hom a))
  congr 1
  exact (Scheme.Hom.germ_stalkMap_apply _ _ _ _ _).symm

end GlobalTheory.NormFnField

namespace GlobalTheory.NormFnField

theorem normalization_functionField : ∀ (Z : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral Z] (K : Type) [Field K] [Algebra Z.functionField K] [FiniteDimensional Z.functionField K] (g : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ Z) [AlgebraicGeometry.QuasiCompact g] [AlgebraicGeometry.QuasiSeparated g], g = AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap Z.functionField K)) ≫ Z.fromSpecStalk (genericPoint Z) → ∃ (hη : g.fromNormalization (genericPoint g.normalization) ⤳ genericPoint Z) (ψ : K →+* g.normalization.functionField), ψ.comp (algebraMap Z.functionField K) = GlobalTheory.TrueGeo.SmallSec.fnMap g.fromNormalization hη := by
  intro Z _ K _ _ _ g _ _ hg
  set cp : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K with hcp
  set j := g.toNormalization with hj
  set π := g.fromNormalization with hπ
  have hjπ : j ≫ π = g := g.toNormalization_fromNormalization
  have h1 : j cp ⤳ genericPoint g.normalization := by
    rw [specializes_iff_mem_closure]
    have hr : Set.range j = {j cp} :=
      Set.ext fun y => ⟨fun ⟨z, hz⟩ => hz ▸ congrArg j (Subsingleton.elim z cp),
        fun hy => ⟨cp, hy.symm⟩⟩
    rw [← hr, g.toNormalization.denseRange.closure_range]
    trivial
  have hgcp : g cp ⤳ genericPoint Z := by
    have : g cp ∈ Set.range (Z.fromSpecStalk (genericPoint Z)) := by
      rw [hg, Scheme.Hom.comp_apply]; exact ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hη : π (genericPoint g.normalization) ⤳ genericPoint Z := by
    have := (genericPoint_specializes (j cp)).map π.continuous
    rw [← Scheme.Hom.comp_apply, hjπ] at this
    exact this.trans hgcp
  refine ⟨hη, ?_⟩
  let φ : g.normalization.functionField ⟶ CommRingCat.of K :=
    g.normalization.presheaf.stalkSpecializes h1 ≫ Scheme.stalkClosedPointTo j

  have hφ : ∀ (V : g.normalization.Opens) (hV : genericPoint g.normalization ∈ V) (s : Γ(g.normalization, V)),
      φ.hom (g.normalization.presheaf.germ V _ hV s) =
        (stalkClosedPointIso (CommRingCat.of K)).hom
          ((Spec (CommRingCat.of K)).presheaf.germ (j ⁻¹ᵁ V) cp (h1.mem_open V.isOpen hV) (j.app V s)) := by
    intro V hV s
    change (Scheme.stalkClosedPointTo j).hom ((g.normalization.presheaf.stalkSpecializes h1).hom
      (g.normalization.presheaf.germ V _ hV s)) = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
    change (stalkClosedPointIso (CommRingCat.of K)).hom.hom ((Scheme.Hom.stalkMap j cp).hom _) = _
    congr 1
    exact Scheme.Hom.germ_stalkMap_apply _ _ _ _ _

  have hφf : ∀ z, φ.hom (GlobalTheory.TrueGeo.SmallSec.fnMap π hη z) = algebraMap Z.functionField K z := by
    intro z
    obtain ⟨U, hU, a, rfl⟩ := Z.presheaf.exists_germ_eq z
    have e1 : GlobalTheory.TrueGeo.SmallSec.fnMap π hη (Z.presheaf.germ U _ hU a) =
        g.normalization.presheaf.germ (π ⁻¹ᵁ U) _ (hη.mem_open U.isOpen hU) (π.app U a) := by
      change (π.stalkMap _).hom ((Z.presheaf.stalkSpecializes hη).hom (Z.presheaf.germ U _ hU a)) = _
      rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
      exact Scheme.Hom.germ_stalkMap_apply _ _ _ _ _
    rw [e1]
    refine (hφ _ _ _).trans ?_
    exact stalkIso_germ_app (j ≫ π) (hjπ.trans hg) U
      ((h1.map π.continuous).mem_open U.isOpen (hη.mem_open U.isOpen hU)) a
  have hinj : Function.Injective φ.hom := φ.hom.injective
  have hsurj : Function.Surjective φ.hom := by
    intro k
    obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint Z)) isOpen_univ
    haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
    haveI := functionField_isFractionRing_of_isAffineOpen Z U hU
    letI : Algebra Γ(Z, U) K :=
      ((algebraMap Z.functionField K).comp (algebraMap Γ(Z, U) Z.functionField)).toAlgebra
    haveI : IsScalarTower Γ(Z, U) Z.functionField K := .of_algebraMap_eq' rfl
    have hAinj : Function.Injective (algebraMap Γ(Z, U) K) :=
      (algebraMap Z.functionField K).injective.comp (IsFractionRing.injective Γ(Z, U) Z.functionField)
    have halg : IsAlgebraic Γ(Z, U) k :=
      (IsFractionRing.isAlgebraic_iff Γ(Z, U) Z.functionField K).mpr (Algebra.IsAlgebraic.isAlgebraic k)
    obtain ⟨y, hy0, hc⟩ := halg.exists_integral_multiple
    have hcU : g cp ∈ U := hgcp.mem_open U.isOpen hηU
    letI : Algebra Γ(Z, U) Γ(Spec (CommRingCat.of K), g ⁻¹ᵁ U) := (g.app U).hom.toAlgebra
    let ρ : Γ(Spec (CommRingCat.of K), g ⁻¹ᵁ U) →+* K :=
      ((Spec (CommRingCat.of K)).presheaf.germ (g ⁻¹ᵁ U) cp hcU ≫
        (stalkClosedPointIso (CommRingCat.of K)).hom).hom
    have hρA : ∀ a : Γ(Z, U), ρ (algebraMap _ _ a) = algebraMap Γ(Z, U) K a :=
      fun a => stalkIso_germ_app g hg U hcU a
    have htop : g ⁻¹ᵁ U = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem g hcU
    let res := (Spec (CommRingCat.of K)).presheaf.map (homOfLE (le_top : g ⁻¹ᵁ U ≤ ⊤)).op
    have hres : Function.Bijective res.hom := by
      have : IsIso res := by
        have e : homOfLE (le_top : g ⁻¹ᵁ U ≤ ⊤) = eqToHom htop := Subsingleton.elim _ _
        simp only [res, e]; infer_instance
      exact ConcreteCategory.bijective_of_isIso res
    have hρres : ∀ t, ρ (res.hom t) = (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom t := by
      intro t
      change (stalkClosedPointIso _).hom.hom (((Spec _).presheaf.germ _ cp hcU).hom (res.hom t)) = _
      refine (congrArg (stalkClosedPointIso (CommRingCat.of K)).hom.hom
        (TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of K)).presheaf
          (homOfLE (le_top : g ⁻¹ᵁ U ≤ ⊤)) cp hcU t)).trans ?_
      exact congrArg (fun q => q.hom t) (germ_stalkClosedPointIso_hom (CommRingCat.of K))
    have hρ : Function.Bijective ρ := by
      have hb : Function.Bijective (ρ ∘ res.hom) := by
        rw [show ρ ∘ res.hom = (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom from funext hρres]
        exact ConcreteCategory.bijective_of_isIso _
      exact (Function.Bijective.of_comp_iff ρ hres).mp hb
    let ρA : Γ(Spec (CommRingCat.of K), g ⁻¹ᵁ U) →ₐ[Γ(Z, U)] K := { ρ with commutes' := hρA }
    obtain ⟨r, hr⟩ := hρ.2 (y • k)
    have hrint : IsIntegral Γ(Z, U) r :=
      (isIntegral_algHom_iff ρA hρ.1).mp (by rw [show ρA r = y • k from hr]; exact hc)
    let b : Γ(g.normalization, π ⁻¹ᵁ U) := (g.normalizationObjIso hU).inv.hom ⟨r, hrint⟩
    have hξU : genericPoint g.normalization ∈ π ⁻¹ᵁ U := hη.mem_open U.isOpen hηU
    have hb : φ.hom (g.normalization.presheaf.germ _ _ hξU b) = y • k := by
      refine (hφ _ _ _).trans ?_
      have hv : ((g.normalizationObjIso hU).hom ≫
          CommRingCat.ofHom (Subalgebra.val _).toRingHom).hom b = r := by
        change ((g.normalizationObjIso hU).hom.hom ((g.normalizationObjIso hU).inv.hom ⟨r, hrint⟩)).1 = r
        rw [Iso.inv_hom_id_apply]
      rw [g.normalizationObjIso_hom_val hU, Scheme.Hom.appLE] at hv
      rw [← hr, ← hv]
      change _ = (stalkClosedPointIso _).hom.hom (((Spec _).presheaf.germ _ cp hcU).hom
        (((Spec _).presheaf.map _).hom ((g.toNormalization.app _).hom b)))
      exact congrArg (stalkClosedPointIso (CommRingCat.of K)).hom.hom
        (TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of K)).presheaf _ cp hcU _).symm
    have hy : φ.hom (GlobalTheory.TrueGeo.SmallSec.fnMap π hη (Z.presheaf.germ U _ hηU y)) =
        algebraMap Γ(Z, U) K y := hφf _
    have hy0' : algebraMap Γ(Z, U) K y ≠ 0 := fun h => hy0 (hAinj (h.trans (map_zero _).symm))
    refine ⟨g.normalization.presheaf.germ _ _ hξU b *
      (GlobalTheory.TrueGeo.SmallSec.fnMap π hη (Z.presheaf.germ U _ hηU y))⁻¹, ?_⟩
    rw [map_mul, map_inv₀, hb, hy, Algebra.smul_def]
    field_simp
  let e := RingEquiv.ofBijective φ.hom ⟨hinj, hsurj⟩
  refine ⟨e.symm.toRingHom, ?_⟩
  ext z
  apply hinj
  change e (e.symm (algebraMap _ K z)) = φ.hom (GlobalTheory.TrueGeo.SmallSec.fnMap π hη z)
  rw [hφf]
  exact e.apply_symm_apply _

end GlobalTheory.NormFnField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixSmoothIsUnitInHolomorphicChart
section
set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix ComplexOrder

namespace GlobalTheory.GoodTop

theorem gram_smooth_isUnit_holoChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → y ∈ e.source → ∀ {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → MContDiffAt ∞ (fun v => H A (e.symm v) ()) (e y) ∧ IsUnit (H A (e.symm (e y)) ()).det := by
  intro F _ σ X m E O H hH e he y hyO hye A hA
  refine ⟨fun a b => ?_, ?_⟩
  · obtain ⟨hre, him⟩ := hH.smooth y hyO A hA () a b
    have h1 : ContDiffAt ℝ ∞ (fun v => (H A (e.symm v) () a b).re) (e y) := contDiffAt_holoChart he hye hre
    have h2 : ContDiffAt ℝ ∞ (fun v => (H A (e.symm v) () a b).im) (e y) := contDiffAt_holoChart he hye him
    have h3 : ContDiffAt ℝ ∞ (fun v => ((H A (e.symm v) () a b).re : ℂ) + ((H A (e.symm v) () a b).im : ℂ) * Complex.I)
        (e y) :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp (e y) h1).add
        ((Complex.ofRealCLM.contDiff.contDiffAt.comp (e y) h2).mul contDiffAt_const)
    exact h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => (Complex.re_add_im _).symm)
  · rw [e.left_inv hye]
    exact isUnit_iff_ne_zero.mpr (hH.posDef y hyO A hA ()).det_pos.ne'

end GlobalTheory.GoodTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTopFormChartIntegralCongrOnStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasTopFormChartIntegral_congr_on : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (e : κ → OpenPartialHomeomorph Y (V n)) {S : Set Y}, MeasurableSet S → ∀ {d d' : κ → Y → ℝ} {t : ℝ}, (∀ i y, y ∈ S → y ∈ (e i).source → d i y = d' i y) → HasInt e d S t → HasInt e d' S t := by
  first | exact @GlobalTheory.GoodTop.hasInt_congr_on | exact GlobalTheory.GoodTop.hasInt_congr_on | (intros; apply GlobalTheory.GoodTop.hasInt_congr_on <;> assumption)
end

