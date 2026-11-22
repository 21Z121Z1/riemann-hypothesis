import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1638
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPdivGroupForPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapDegreeEqExpCharPowMulCardKernel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0216
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixDescentUnramifiedDvr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCO
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

namespace GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7}

def IsCO (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Prop :=
  IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) ∧
    IsCompact ((Lev.levA V K : Subgroup (GA D V)) : Set (GA D V))

def LocCO {n : ℕ} {w : Pl D.host.E} (K : Subgroup (GL (Fin n) (Kw w))) : Prop :=
  IsOpen (K : Set (GL (Fin n) (Kw w))) ∧ ∃ C : Set (GL (Fin n) (Kw w)), IsCompact C ∧ (K : Set (GL (Fin n) (Kw w))) ⊆ C

end GlobalTheory.FunObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalQuotientTransitionCocycleStatement
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_quotient_transition_cocycle : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A)
    (B : ∀ j, Over (𝒰.X j)) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j) (b : ∀ j k, pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k) ⟶ (B k).left),
    (∀ j, Flat (q j).left) → (∀ j, Surjective (q j).left) → (∀ j, QuasiCompact (q j).left) →
    (∀ j k, b j k ≫ (B k).hom = pullback.snd _ _) →
    (∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
        (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ (q j).left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ (q k).left) →
    ∀ (j k l : 𝒰.I₀) (T : Scheme.{0}) (x : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k))
      (y : T ⟶ pullback ((B k).hom ≫ 𝒰.f k) (𝒰.f l)) (z : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f l)),
      x ≫ b j k = y ≫ pullback.fst _ _ → x ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ → y ≫ b k l = z ≫ b j l := by
  first | (exact @GlobalTheory.cocycle_local_quotient_transition) | (exact GlobalTheory.cocycle_local_quotient_transition) | (intros; apply GlobalTheory.cocycle_local_quotient_transition  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingFiniteIdealsOfMaximalIdealPrincipalNilp
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory

theorem localRing_finite_ideals_of_maximalIdeal_principal_nilpotent :
    ∀ (S : Type) [CommRing S] [IsLocalRing S], (IsLocalRing.maximalIdeal S).IsPrincipal →
    IsNilpotent (IsLocalRing.maximalIdeal S) → (Set.univ : Set (Ideal S)).Finite := by
  intro S _ _ hprin hnil
  classical
  obtain ⟨x, hx⟩ := hprin.principal
  obtain ⟨M, hM⟩ := hnil
  set m := IsLocalRing.maximalIdeal S with hm
  have hM' : m ^ M = ⊥ := hM
  have hpow : ∀ n : ℕ, m ^ n = Ideal.span {x ^ n} := by
    intro n
    rw [hx]
    exact Ideal.span_singleton_pow x n
  apply ((Set.finite_Iic M).image fun n => m ^ n).subset
  intro I _
  by_cases hI : I = ⊥
  · exact ⟨M, Set.mem_Iic.mpr le_rfl, by simp only [hM', hI]⟩
  · have hnot : ¬ I ≤ m ^ M := by
      rw [hM']; exact fun h => hI (le_bot_iff.mp h)
    have hex : ∃ k, ¬ I ≤ m ^ k := ⟨M, hnot⟩
    have hk := Nat.find_spec hex
    have hkM : Nat.find hex ≤ M := Nat.find_min' hex hnot
    have hk0 : Nat.find hex ≠ 0 := by
      intro h; apply hk; rw [h, pow_zero]; rw [Ideal.one_eq_top]; exact le_top
    obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 := Nat.exists_eq_succ_of_ne_zero hk0
    have hIn : I ≤ m ^ n := by
      by_contra h
      exact Nat.find_min hex (show n < Nat.find hex by omega) h
    rw [hn] at hk
    obtain ⟨a, haI, ha⟩ := SetLike.not_le_iff_exists.mp hk
    have ha' : a ∈ m ^ n := hIn haI
    rw [hpow, Ideal.mem_span_singleton'] at ha'
    obtain ⟨y, rfl⟩ := ha'
    have hy : IsUnit y := by
      by_contra hy
      apply ha
      have hym : y ∈ m := (IsLocalRing.mem_maximalIdeal y).mpr hy
      rw [hx, Ideal.mem_span_singleton'] at hym
      obtain ⟨z, rfl⟩ := hym
      rw [hpow, Ideal.mem_span_singleton']
      exact ⟨z, by ring⟩
    refine ⟨n, Set.mem_Iic.mpr (by omega), ?_⟩
    show m ^ n = I
    apply le_antisymm _ hIn
    rw [hpow, Ideal.span_le, Set.singleton_subset_iff]
    have := I.mul_mem_left ((hy.unit⁻¹ : Sˣ) : S) haI
    rwa [← _root_.mul_assoc, IsUnit.val_inv_mul, _root_.one_mul] at this

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowRankFiltrationStep
section
open ValuativeRel Matrix

namespace GlobalTheory.RankCoinv

theorem mem_lowRank_succ_sup_twistSpan_of_mem_lowRank : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (r : ℕ), r < Fintype.card A → ∀ Φ ∈ (GlobalTheory.RankCoinv.lowRank r : Submodule ℂ (Matrix A D k → ℂ)), Φ ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ν β hν hνϖ r hr Φ hΦ
  obtain ⟨⟨hlc, hcs⟩, hvan⟩ := hΦ
  classical

  have hSclosed : IsClosed {X : Matrix A D k | Φ X ≠ 0} := by
    have : {X : Matrix A D k | Φ X ≠ 0} = (Φ ⁻¹' {0})ᶜ := by ext; simp
    rw [this]; exact (hlc.isOpen_fiber 0).isClosed_compl
  have hScpt : IsCompact {X : Matrix A D k | Φ X ≠ 0} :=
    hcs.isCompact.of_isClosed_subset hSclosed (fun X hX => subset_tsupport Φ hX)

  let m₀ : Matrix A D k → ℕ := fun X =>
    if h : X.rank = r then Classical.choose (GlobalTheory.T.low_rank_box_function_stable k A D ϖ hϖ ν β hν hνϖ r X h hr) else 0
  have hm₀ : ∀ X : Matrix A D k, ∀ h : X.rank = r, ∀ m ≥ m₀ X, ∀ C ∈ box ϖ X (fun _ => m₀ X),
      boxFn ϖ C (fun _ => m) ∈ lowRank (r + 1) ⊔ twistSpan ν β := by
    intro X h
    have := Classical.choose_spec (GlobalTheory.T.low_rank_box_function_stable k A D ϖ hϖ ν β hν hνϖ r X h hr)
    simpa [m₀, h] using this
  let U : Matrix A D k → Set (Matrix A D k) := fun X =>
    if X.rank ≤ r then box ϖ X (fun _ => m₀ X) else {Y | r + 1 ≤ Y.rank}
  have hU : ∀ X ∈ {X : Matrix A D k | Φ X ≠ 0}, U X ∈ nhds X := by
    intro X _
    by_cases h : X.rank ≤ r
    · simp only [U, h, if_true]
      refine (isClopen_box ϖ X _).isOpen.mem_nhds ?_
      intro i j; simp
    · simp only [U, h, if_false]
      exact (GlobalTheory.T.isOpen_rank_ge k A D (r + 1)).mem_nhds (by simp only [Set.mem_setOf_eq]; omega)
  obtain ⟨t, htS, hcover⟩ := hScpt.elim_nhds_subcover U hU
  obtain ⟨m₁, hm₁⟩ := GlobalTheory.T.schwartz_bruhat_box_decomposition k A D ϖ hϖ Φ ⟨hlc, hcs⟩
  obtain ⟨s, hdec, hconst⟩ := hm₁ (max m₁ (t.sup m₀)) (le_max_left _ _)
  set m := max m₁ (t.sup m₀) with hm
  rw [hdec]
  refine Submodule.sum_mem _ fun c hc => ?_
  by_cases hex : ∃ X₂ ∈ box ϖ c (fun _ => m), X₂.rank ≤ r
  · obtain ⟨X₂, hX₂, hX₂r⟩ := hex
    by_cases hc0 : Φ c = 0
    · rw [hc0, zero_smul]; exact zero_mem _
    refine Submodule.smul_mem _ _ ?_
    have hX₂S : Φ X₂ ≠ 0 := by rw [hconst c hc X₂ hX₂]; exact hc0
    have hX₂eq : X₂.rank = r := by
      by_contra hne
      exact hX₂S (hvan X₂ (lt_of_le_of_ne hX₂r hne))
    obtain ⟨x, hxt, hxU⟩ := Set.mem_iUnion₂.1 (hcover hX₂S)
    have hxS : Φ x ≠ 0 := htS x hxt
    by_cases hxr : x.rank ≤ r
    · simp only [U, hxr, if_true] at hxU
      have hxeq : x.rank = r := by
        by_contra hne
        exact hxS (hvan x (lt_of_le_of_ne hxr hne))
      have hmx : m₀ x ≤ m := le_trans (Finset.le_sup (f := m₀) hxt) (le_max_right _ _)
      rw [← boxFn_eq_of_mem hX₂]
      exact hm₀ x hxeq m hmx X₂ hxU
    · simp only [U, hxr, if_false, Set.mem_setOf_eq] at hxU
      omega
  · push_neg at hex
    refine Submodule.smul_mem _ _ (Submodule.mem_sup_left ?_)
    refine ⟨boxFn_mem_SB ϖ c _, fun Y hY => ?_⟩
    have hYn : Y ∉ box ϖ c (fun _ => m) := fun hYb => by
      have := hex Y hYb; omega
    simp [boxFn, Set.indicator_of_notMem hYn]

end GlobalTheory.RankCoinv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapDegEqPowMulCard
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.ZV GlobalTheory.DegKer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiAbelianTower

theorem isFinite_pow {K : Type} [Field K] [IsAlgClosed K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G]
    (D : TorusExtension G) (N : ℕ) (hN : 1 ≤ N) : IsFinite ((𝟙 G) ^ N : G ⟶ G).left := by
  letI := D.addCommGroup
  letI := D.grpB
  have := D.q_hom
  have := D.i_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_quasiCompact
  have := D.free
  have := D.finite
  have h1 : IsFinite ((𝟙 D.B) ^ N : D.B ⟶ D.B).left := GlobalTheory.MulFiniteAny.isFinite_mulA K D.B D.isAbelian N hN
  have hf : IsFinite (mulN (splitTorus (Sp K) D.X) N).left := Diag.isFinite_mulN _ D.X (by omega)
  rw [GrpTangent.mulN_eq_pow] at hf
  have := isAffineHom_descendsAlong_fpqc.{0}
  have hP := IsPullback.of_hasPullback D.q ((𝟙 D.B) ^ N)
  have w : ((𝟙 G) ^ N) ≫ D.q = D.q ≫ ((𝟙 D.B) ^ N) := by
    rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  have ha := hP.lift_fst _ _ w
  have hb := hP.lift_snd _ _ w
  have a2 : IsAffineHom (hP.lift _ _ w).left :=
    ExtensionMul.of_pow_kernel @IsAffineHom D.i D.q D.isKernel N hP ha hb inferInstance
  have a3 : UniversallyClosed (hP.lift _ _ w).left :=
    ExtensionMul.of_pow_kernel @UniversallyClosed D.i D.q D.isKernel N hP ha hb inferInstance
  have a4 : LocallyOfFiniteType (hP.lift _ _ w).left :=
    ExtensionMul.of_pow_kernel @LocallyOfFiniteType D.i D.q D.isKernel N hP ha hb inferInstance
  have a5 : IsFinite (hP.lift _ _ w).left :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
      ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, a4⟩
  have hP' := (hP.map (Over.forget _)).flip
  have b1 : IsFinite (pullback.fst D.q ((𝟙 D.B) ^ N)).left := MorphismProperty.of_isPullback (P := @IsFinite) hP' h1
  rw [← ha, Over.comp_left]
  infer_instance

theorem mapDeg_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    [IsFinite φ] [IsFinite ψ] [Surjective φ] [Surjective ψ] {D E : ℕ} (hD : MapDeg φ D) (hE : MapDeg ψ E) :
    MapDeg (φ ≫ ψ) (E * D) := by
  refine MapDeg.of_isFinite fun U hU hne => ?_
  obtain ⟨z, hz⟩ := hne
  obtain ⟨y, rfl⟩ := ψ.surjective z
  obtain ⟨x, rfl⟩ := φ.surjective y
  haveI : Nonempty U := ⟨⟨_, hz⟩⟩
  haveI : Nonempty (ψ ⁻¹ᵁ U) := ⟨⟨φ x, hz⟩⟩
  haveI : Nonempty (φ ⁻¹ᵁ ψ ⁻¹ᵁ U) := ⟨⟨x, hz⟩⟩
  letI := (ψ.app U).hom.toAlgebra
  letI := (φ.app (ψ ⁻¹ᵁ U)).hom.toAlgebra
  letI : Algebra Γ(Z, U) Γ(X, φ ⁻¹ᵁ ψ ⁻¹ᵁ U) := ((φ ≫ ψ).app U).hom.toAlgebra
  haveI : IsScalarTower Γ(Z, U) Γ(Y, ψ ⁻¹ᵁ U) Γ(X, φ ⁻¹ᵁ ψ ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite Γ(Z, U) Γ(Y, ψ ⁻¹ᵁ U) := ψ.finite_app U hU
  haveI := IsSchemeTheoreticallyDominant.of_isDominant φ
  haveI := IsSchemeTheoreticallyDominant.of_isDominant ψ
  haveI : FaithfulSMul Γ(Z, U) Γ(Y, ψ ⁻¹ᵁ U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (ψ.app_injective U)
  haveI : FaithfulSMul Γ(Y, ψ ⁻¹ᵁ U) Γ(X, φ ⁻¹ᵁ ψ ⁻¹ᵁ U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (φ.app_injective _)
  rw [← hE.finrank_eq U hU ⟨_, hz⟩, ← hD.finrank_eq _ (hU.preimage ψ) ⟨φ x, hz⟩]
  exact (Module.finrank_mul_finrank' Γ(X, φ ⁻¹ᵁ ψ ⁻¹ᵁ U)).symm

theorem finrank_eq_of_mapDeg {X Y : Scheme.{0}} [IsIntegral Y] (φ : X ⟶ Y) [IsFinite φ] [Flat φ] {D : ℕ}
    (hD : MapDeg φ D) (y : Y) : φ.finrank y = D := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  replace hU : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨_, hy⟩⟩
  letI := (φ.app U).hom.toAlgebra
  haveI : Module.Finite Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := φ.finite_app U hU
  haveI : Module.Flat Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := by
    have := φ.flat_appLE hU (hU.preimage φ) le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  have hp : IsPullback (hU.preimage φ).fromSpec (Spec.map (φ.app U)) φ hU.fromSpec :=
    (IsOpenImmersion.isPullback _ _ _ _ (by
      rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec φ hU (hU.preimage φ)])
      (by simp)).flip
  obtain ⟨q, rfl⟩ : y ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hy
  rw [← hD.finrank_eq U hU ⟨_, hy⟩, ← FiniteCover.rankAtStalk_bot,
    Module.rankAtStalk_eq_of_le_of_finite_of_flat _ (p := ⊥) (q := q) bot_le,
    ← Scheme.Hom.finrank_of_isPullback _ _ _ _ hp q]
  exact Scheme.Hom.finrank_SpecMap_algebraMap Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) _

theorem mapDeg_eq_pow_mul_card (K : Type) [Field K] [IsAlgClosed K] (G : Over (Sp K)) [GrpObj G]
    [IsIntegral G.left] [LocallyOfFiniteType G.hom] (α : G ⟶ G) [IsMonHom α] [IsFinite α.left] :
    Finite {x : Out.baseOver (Sp K) ⟶ G // x ≫ α = 1} ∧
      ∃ e : ℕ, MapDeg α.left (ringExpChar K ^ e * Nat.card {x : Out.baseOver (Sp K) ⟶ G // x ≫ α = 1}) := by
  have hs := (flat_and_surjective_of_isFinite_grpEnd K G α).2
  obtain ⟨D, -, hD⟩ := exists_mapDeg_of_isFinite _ _ α.left inferInstance hs
  obtain ⟨_, ⟨U, hU, rfl⟩, hξ, -⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint G.left)) isOpen_univ
  have : Nonempty U := ⟨⟨_, hξ⟩⟩
  have : Nonempty (α.left ⁻¹ᵁ U) := by
    obtain ⟨x, hx⟩ := α.left.surjective (genericPoint G.left)
    exact ⟨⟨x, show α.left x ∈ U from hx ▸ hξ⟩⟩
  letI := (α.left.app U).hom.toAlgebra
  have : Module.Finite Γ(G.left, U) Γ(G.left, α.left ⁻¹ᵁ U) := α.left.finite_app U hU
  have : IsSchemeTheoreticallyDominant α.left := .of_isDominant _
  have : FaithfulSMul Γ(G.left, U) Γ(G.left, α.left ⁻¹ᵁ U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (α.left.app_injective U)
  let c : K →+* Γ(G.left, U) :=
    (G.hom.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have : ExpChar Γ(G.left, U) (ringExpChar K) := expChar_of_injective_ringHom c.injective _
  let Ω := AlgebraicClosure (FractionRing Γ(G.left, U))
  have : FaithfulSMul Γ(G.left, U) Ω := by
    rw [faithfulSMul_iff_algebraMap_injective,
      IsScalarTower.algebraMap_eq Γ(G.left, U) (FractionRing Γ(G.left, U)) Ω, RingHom.coe_comp]
    exact (RingHom.injective _).comp (IsFractionRing.injective _ _)
  obtain ⟨h0, e, he⟩ := finrank_eq_pow_mul_card Γ(G.left, U) Γ(G.left, α.left ⁻¹ᵁ U) Ω (ringExpChar K)
  rw [card_fibre_eq α.left hU Ω] at h0 he
  set z := Spec.map (CommRingCat.ofHom (algebraMap Γ(G.left, U) Ω)) ≫ hU.fromSpec with hz
  let z' : Over.mk (z ≫ G.hom) ⟶ G := Over.homMk z rfl
  have h1 : Nat.card {y : Over.mk (z ≫ G.hom) ⟶ G // y ≫ α = z'} =
      Nat.card {y : Spec (CommRingCat.of Ω) ⟶ G.left // y ≫ α.left = z} := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun y => ⟨y.1.left, congrArg CommaMorphism.left y.2⟩) ⟨?_, ?_⟩)
    · intro y y' h
      exact Subtype.ext (Over.OverMorphism.ext (congrArg Subtype.val h))
    · rintro ⟨y, hy⟩
      refine ⟨⟨Over.homMk y ?_, Over.OverMorphism.ext hy⟩, rfl⟩
      change y ≫ G.hom = z ≫ G.hom
      rw [← hy, Category.assoc, Over.w α]
  rw [← h1] at h0 he
  have hne := (Nat.card_ne_zero.mp h0).1
  rw [← card_coset_eq G _ α z' hne, ← card_ker_eq G α Ω (z ≫ G.hom)] at h0 he
  refine ⟨(Nat.card_ne_zero.mp h0).2, e, ?_⟩
  rw [← he, hD.finrank_eq U hU ⟨_, hξ⟩]
  exact hD

theorem exists_finrank_torsion (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [IsAlgClosed K] (h0 : (p : K) = 0)
    (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom]
    (D : TorusExtension G) : ∃ h : ℕ, ∀ (n : ℕ) (S : Type) [CommRing S] [Algebra K S] [Module.Finite K S]
      (y : SpAlg K S ⟶ G), IsPullback y.left (spMap (algebraMap K S)) (mulN G (p ^ n)).left η[G].left →
        Module.finrank K S = p ^ (n * h) := by
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ G.hom ‹_› ‹_›
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_subsingleton G.hom
  have hm : ∀ N, IsMonHom ((𝟙 G) ^ N : G ⟶ G) := fun N => GlobalTheory.AbLaw.MulN.isMonHom_mulA G N
  have hf : ∀ n, IsFinite ((𝟙 G) ^ p ^ n : G ⟶ G).left := fun n => isFinite_pow G D _ (Nat.one_le_pow _ _ hp.out.pos)
  have hl := fun n => (flat_and_surjective_of_isFinite_grpEnd K G ((𝟙 G) ^ p ^ n)).1
  have hs := fun n => (flat_and_surjective_of_isFinite_grpEnd K G ((𝟙 G) ^ p ^ n)).2
  obtain ⟨hfin, e, he⟩ := mapDeg_eq_pow_mul_card K G ((𝟙 G) ^ p ^ 1)
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero hp.out).2 h0
  rw [ringExpChar.eq K p] at he
  let M : Subgroup (Out.baseOver (Sp K) ⟶ G) := (IsMonHom.monoidHom ((𝟙 G) ^ p ^ 1 : G ⟶ G) _).ker
  haveI : Finite M := hfin
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := M)).1 fun g => ⟨1, Subtype.ext (by
    have h : g.1 ≫ (𝟙 G) ^ p ^ 1 = 1 := g.2
    rw [MonObj.comp_pow, Category.comp_id] at h
    exact h)⟩
  have hd : ∀ n, MapDeg ((𝟙 G) ^ p ^ n : G ⟶ G).left (p ^ (n * (e + k))) := fun n => by
    induction n with
    | zero =>
      simp only [pow_zero, pow_one, zero_mul]
      exact MapDeg.id_one _
    | succ n ih =>
      have h := mapDeg_comp _ _ he ih
      rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, ← pow_mul, ← pow_add,
        show Nat.card {x : Out.baseOver (Sp K) ⟶ G // x ≫ (𝟙 G) ^ p ^ 1 = 1} = p ^ k from hk, ← pow_add,
        ← pow_add, add_comm 1 n] at h
      rwa [add_mul, _root_.one_mul]
  refine ⟨e + k, fun n S _ _ _ y H => ?_⟩
  rw [GrpTangent.mulN_eq_pow] at H
  have h := Scheme.Hom.finrank_of_isPullback _ _ _ _ H (⊥ : PrimeSpectrum K)
  rw [finrank_eq_of_mapDeg _ (hd n)] at h
  rw [← h, ← FiniteCover.rankAtStalk_bot]
  exact (Scheme.Hom.finrank_SpecMap_algebraMap K S _).symm

theorem exists_tower : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] (A : Over (Sp O)) [GrpObj A], IsSemiAbelian A → (∀ N, 1 ≤ N → IsFinite (torsion A N).hom ∧ Flat (torsion A N).hom) → ∃ G : PDivGroup p O, Nonempty (G.TorsionTower A) := by
  intro p hp O _ _ A _ hA hf
  by_cases h0 : (p : O) = 0
  swap
  · exact RaynaudPDiv.exists_tower p O h0 A hA hf
  have := hA.comm
  have := hA.smooth
  have := hA.geomConnected
  let K := AlgebraicClosure (FractionRing O)
  have hi : Function.Injective (algebraMap O K) :=
    (algebraMap (FractionRing O) K).injective.comp (IsFractionRing.injective O _)
  let B := (Over.pullback (spMap (algebraMap O K))).obj A
  have : Smooth B.hom := inferInstanceAs (Smooth (pullback.snd A.hom _))
  have : GeometricallyConnected B.hom := inferInstanceAs (GeometricallyConnected (pullback.snd A.hom _))
  choose R _ _ y h1 h2 H using fun n : ℕ => RaynaudPDiv.exists_isPullback_torsion O A (p ^ n)
    (hf _ (Nat.one_le_pow _ _ hp.out.pos)).1 (hf _ (Nat.one_le_pow _ _ hp.out.pos)).2
  have h := fun n => AbelianPDiv.isUnivTorsion_of_isPullback (y n) (H n)
  obtain ⟨D⟩ := hA.fibres K (spMap (algebraMap O K))
  obtain ⟨d, hd⟩ := exists_finrank_torsion p K (by rw [← map_natCast (algebraMap O K), h0, map_zero]) B D
  have hk : ∀ n, Module.finrank K (K ⊗[O] R n) = p ^ (n * d) := fun n => by
    obtain ⟨y', h'⟩ := AbelianPDiv.exists_isPullback_baseChange (y n) (H n) K
    exact hd n _ y' h'
  have hr : ∀ n (q : PrimeSpectrum O), Module.rankAtStalk (R n) q = p ^ (n * d) := fun n q => by
    rw [← Module.rankAtStalk_eq_of_le_of_finite_of_flat (R n)
        (p := PrimeSpectrum.comap (algebraMap O K) ⊥) (q := q) ?_, ← Module.rankAtStalk_baseChange,
      Module.rankAtStalk_eq_finrank_of_free, hk n]
    · rfl
    · intro a ha
      have ha' : algebraMap O K a = 0 := ha
      rw [(map_eq_zero_iff _ hi).1 ha']
      exact zero_mem _
  choose r r1 r2 r3 using fun n : ℕ =>
    (h n).exists_res (h (n + 1)) (by rw [pow_succ, pow_mul, (h n).1, one_pow])
  let G : PDivGroup p O :=
    { height := d
      A := R
      hopf := fun n => (h n).hopfAlgebra
      cocomm := fun n => (h n).isCocomm
      finite := h1
      projective := h2
      rank_eq := hr
      res := r
      res_surjective := r1
      ker_res := r2 }
  exact ⟨G, ⟨{
    y := y
    mul := fun n B _ _ => (h n).mul_y
    inj := fun n B _ _ _ _ => (h n).inj
    surj := fun n B _ _ z hz => ((h n).2 B z hz).exists
    res := r3 }⟩⟩

end GlobalTheory.SemiAbelianTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixDescentUnramifiedDvrStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_descent_unramified_dvr : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → ∀ D : Set (K' ≃ₐ[K] K'), (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y) → (∀ x : W, (∀ σ ∈ D, ∀ y : W, σ (algebraMap W K' x) = algebraMap W K' y → y - x ∈ maximalIdeal W) → ∃ r : R, x - algebraMap R W r ∈ maximalIdeal W) → ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) K'), IsUnit g.det → (∀ σ ∈ D, ∃ h : Matrix (Fin n) (Fin n) W, g.map σ = h.map (algebraMap W K') * g) → ∃ (h : Matrix (Fin n) (Fin n) W) (k : Matrix (Fin n) (Fin n) K), IsUnit h.det ∧ k.map (algebraMap K K') = h.map (algebraMap W K') * g := by
  first | exact @GlobalTheory.matrix_descent_unramified | exact GlobalTheory.matrix_descent_unramified | (intros; apply GlobalTheory.matrix_descent_unramified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixMemSpanIncM
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory

theorem matrix_mem_span_incM : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (m n : ℕ)
    (u : Matrix (Fin m) (Fin n) (AF F ⊗[F] E)),
    u ∈ Submodule.span (AF F) (Set.range (incM F : Matrix (Fin m) (Fin n) E → Matrix (Fin m) (Fin n) (AF F ⊗[F] E))) := by
  intro F E _ _ _ _ _ m n u
  classical
  rw [Matrix.matrix_eq_sum_single u]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  generalize u i j = a
  induction a using TensorProduct.induction_on with
  | zero => rw [Matrix.single_zero]; exact Submodule.zero_mem _
  | add x y hx hy => rw [Matrix.single_add]; exact Submodule.add_mem _ hx hy
  | tmul a e =>
    have h : Matrix.single i j (a ⊗ₜ[F] e) = a • incM F (Matrix.single i j e) := by
      ext k l
      simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.single, Matrix.of_apply]
      split_ifs
      · change _ = a • ((1 : AF F) ⊗ₜ[F] e)
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      · simp
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodingerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_theta_sum_of_schrodinger : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    @Measurable _ _ (borel _) _ (fun w : (κ → AF F) × (κ → AF F) => GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)) := by
  first | exact @GlobalTheory.ThetaTransformMeas.main | exact GlobalTheory.ThetaTransformMeas.main | (intros; apply GlobalTheory.ThetaTransformMeas.main <;> assumption)
end

