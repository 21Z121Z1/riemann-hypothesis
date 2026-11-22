import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0050
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0127
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExists
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0008
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0189
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0009
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0185
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0188
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExpLogCoverBound

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeFirst
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.MuFrame

private theorem isMultiHomog_mul_geometry {K : Type} {Jt : K → Type} [∀ k, Fintype (Jt k)]
    {p q : MvPolynomial ((k : K) × Jt k) ℤ} {a b : K → ℕ}
    (hp : IsMultiHomog p a) (hq : IsMultiHomog q b) : IsMultiHomog (p * q) (a + b) := by
  classical
  unfold IsMultiHomog at *
  intro m hm k
  obtain ⟨m1, h1, m2, h2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hp m1 h1 k, hq m2 h2 k, Pi.add_apply]

private theorem isMultiHomog_add_geometry {K : Type} {Jt : K → Type} [∀ k, Fintype (Jt k)]
    {p q : MvPolynomial ((k : K) × Jt k) ℤ} {a : K → ℕ}
    (hp : IsMultiHomog p a) (hq : IsMultiHomog q a) : IsMultiHomog (p + q) a := by
  classical
  unfold IsMultiHomog at *
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hp m h k
  · exact hq m h k

private theorem isMultiHomog_X_geometry {K : Type} {Jt : K → Type} [∀ k, Fintype (Jt k)] [DecidableEq K]
    (k : K) (i : Jt k) :
    IsMultiHomog (MvPolynomial.X ⟨k, i⟩ : MvPolynomial ((k : K) × Jt k) ℤ) (Pi.single k 1) := by
  classical
  unfold IsMultiHomog
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases hk : k' = k
  · subst hk
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Finsupp.single_apply, Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  · have hk' : k ≠ k' := Ne.symm hk
    simp [Finsupp.single_apply, hk, hk']

private theorem isMultiHomog_prod_X_one {K : Type} [Fintype K] {Jt : K → Type} [∀ k, Fintype (Jt k)]
    (ch : (k : K) → Jt k) :
    IsMultiHomog (∏ k, (MvPolynomial.X ⟨k, ch k⟩ : MvPolynomial ((k : K) × Jt k) ℤ)) (fun _ => 1) := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog
      (∏ k ∈ s, (MvPolynomial.X ⟨k, ch k⟩ : MvPolynomial ((k : K) × Jt k) ℤ))
      (∑ k ∈ s, Pi.single k 1) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · have h1 : IsMultiHomog (MvPolynomial.C (1 : ℤ) : MvPolynomial ((k : K) × Jt k) ℤ) 0 :=
        isMultiHomog_C_zero 1
      simpa using h1
    · intro a s ha ih
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact isMultiHomog_mul_geometry (isMultiHomog_X_geometry a (ch a)) ih
  have h := key Finset.univ
  convert h using 1
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

private theorem isValueAt_add' {K : Type} {Jt : K → Type} [∀ k, Fintype (Jt k)] {Ω : Type} [Field Ω]
    {y : (k : K) × Jt k → Ω} {w : (k : K) × Jt k → ℂ} {s s' : Ω} {v v' : ℂ}
    (h1 : IsValueAt y s w v) (h2 : IsValueAt y s' w v') : IsValueAt y (s + s') w (v + v') := by
  unfold IsValueAt at *
  obtain ⟨d, g, h, hg, hh, hy, hgs, hw, rfl⟩ := h1
  obtain ⟨d', g', h', hg', hh', hy', hgs', hw', rfl⟩ := h2
  refine ⟨d + d', g * h' + g' * h, h * h', isMultiHomog_add_geometry (isMultiHomog_mul_geometry hg hh') ?_,
    isMultiHomog_mul_geometry hh hh', ?_, ?_, ?_, ?_⟩
  · rw [add_comm d d']; exact isMultiHomog_mul_geometry hg' hh
  · rw [map_mul]; exact mul_ne_zero hy hy'
  · simp only [map_mul, map_add, hgs, hgs']; ring
  · simp only [map_mul]; exact mul_ne_zero hw hw'
  · simp only [map_mul, map_add]; rw [div_add_div _ _ hw hw']; ring

private theorem isValueAt_mul' {K : Type} {Jt : K → Type} [∀ k, Fintype (Jt k)] {Ω : Type} [Field Ω]
    {y : (k : K) × Jt k → Ω} {w : (k : K) × Jt k → ℂ} {s s' : Ω} {v v' : ℂ}
    (h1 : IsValueAt y s w v) (h2 : IsValueAt y s' w v') : IsValueAt y (s * s') w (v * v') := by
  unfold IsValueAt at *
  obtain ⟨d, g, h, hg, hh, hy, hgs, hw, rfl⟩ := h1
  obtain ⟨d', g', h', hg', hh', hy', hgs', hw', rfl⟩ := h2
  refine ⟨d + d', g * g', h * h', isMultiHomog_mul_geometry hg hg', isMultiHomog_mul_geometry hh hh', ?_, ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hy hy'
  · simp only [map_mul, hgs, hgs']; ring
  · simp only [map_mul]; exact mul_ne_zero hw hw'
  · simp only [map_mul]; rw [div_mul_div_comm]

private theorem isValueAt_aeval_segreCoord_div {K : Type} [Fintype K] {Jt : K → Type} [∀ k, Fintype (Jt k)]
    {Ω : Type} [Field Ω] (y : (k : K) × Jt k → Ω) (w : (k : K) × Jt k → ℂ) (ch : (k : K) → Jt k)
    (hy : segreCoord y ch ≠ 0) (hw : ∏ k, w ⟨k, ch k⟩ ≠ 0) (P : MvPolynomial ((k : K) → Jt k) ℤ) :
    IsValueAt y (MvPolynomial.aeval (fun c' => segreCoord y c' / segreCoord y ch) P) w
      (MvPolynomial.aeval (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    unfold IsValueAt
    refine ⟨0, MvPolynomial.C a, 1, isMultiHomog_C_zero a, ?_, ?_, ?_, ?_, ?_⟩
    · have h1 : IsMultiHomog (MvPolynomial.C (1 : ℤ) : MvPolynomial ((k : K) × Jt k) ℤ) 0 :=
        isMultiHomog_C_zero 1
      simpa using h1
    · simp
    · simp
    · simp
    · simp
  | add p q hp hq => simpa only [map_add] using isValueAt_add' hp hq
  | mul_X p i hp =>
    rw [map_mul, map_mul]
    refine isValueAt_mul' hp ?_
    unfold IsValueAt
    refine ⟨fun _ => 1, ∏ k, MvPolynomial.X ⟨k, i k⟩, ∏ k, MvPolynomial.X ⟨k, ch k⟩,
      isMultiHomog_prod_X_one i, isMultiHomog_prod_X_one ch, ?_, ?_, ?_, ?_⟩
    · simpa [segreCoord] using hy
    · simp only [map_prod, MvPolynomial.aeval_X]
      exact (div_mul_cancel₀ _ hy).symm
    · simpa using hw
    · simp [MvPolynomial.aeval_X]

theorem nonempty_muFrameAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Nonempty (MuFrameAt Hd w) := by
  classical
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z w hco
  unfold CoordsAt at hco
  choose ch hch using hco.1
  have hy : ∀ k, Dc.y ⟨k, ch k⟩ ≠ 0 := fun k => (hco.2 k (ch k) (hch k)).1
  have hwc : ∀ k, w ⟨k, ch k⟩ ≠ 0 := fun k => (hch k).ne_zero
  have hseg : segreCoord Dc.y ch ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hy k)
  have hsegw : ∏ k, w ⟨k, ch k⟩ ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hwc k)
  obtain ⟨m, f, cc, hf, hcc, hsum, hfr⟩ := Hd.locally ch hseg
  have hmem : ∀ a, a ∈ chartRing ℤ (segreCoord Dc.y) ch → ∃ P : MvPolynomial ((k : K) → J k) ℤ,
      MvPolynomial.aeval (fun c' => segreCoord Dc.y c' / segreCoord Dc.y ch) P = a := by
    intro a ha
    unfold ReciprocityTheory.ChartRestriction.G.Geo.chartRing at ha
    rw [Algebra.adjoin_range_eq_range_aeval] at ha
    obtain ⟨P, hP⟩ := ha
    exact ⟨P, hP⟩
  choose P hP using fun l => hmem (f l) (hf l)
  choose Q hQ using fun l => hmem (cc l) (hcc l)
  have hginj : Function.Injective (genMap Or.𝔐.ξ ⟨centre z, Or.𝔐.all _⟩) :=
    (CoordTie.gen Or.𝔐.tie).inj _
  have hlift : ∀ q : (k : K) × J k, ∃ t : Or.𝔐.X.presheaf.stalk (centre z),
      genMap Or.𝔐.ξ ⟨centre z, Or.𝔐.all _⟩ t = Dc.y q / Dc.y ⟨q.1, ch q.1⟩ ∧
      (Scheme.stalkClosedPointTo z).hom t = w q / w ⟨q.1, ch q.1⟩ := by
    rintro ⟨k, i⟩
    obtain ⟨r0, hv, hr0⟩ := (hco.2 k (ch k) (hch k)).2 i
    unfold ValAt at hv
    obtain ⟨hsp, t, ht1, ht2⟩ := hv
    refine ⟨t, ht1, ?_⟩
    rw [ht2, hr0, mul_div_assoc, div_self (hwc k), _root_.mul_one]
  choose t ht1 ht2 using hlift
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Or.𝔐.X.presheaf.stalk (centre z) →+* ℂ,
      ψ = (Scheme.stalkClosedPointTo z).hom := ⟨_, rfl⟩
  have ht2' : ∀ q, ψ (t q) = w q / w ⟨q.1, ch q.1⟩ := by
    intro q; rw [hψ]; exact ht2 q
  have hval : ∀ R : MvPolynomial ((k : K) → J k) ℤ, ∃ s : Or.𝔐.X.presheaf.stalk (centre z),
      genMap Or.𝔐.ξ ⟨centre z, Or.𝔐.all _⟩ s =
        MvPolynomial.aeval (fun c' => segreCoord Dc.y c' / segreCoord Dc.y ch) R ∧
      ψ s =
        MvPolynomial.aeval (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) R := by
    intro R
    induction R using MvPolynomial.induction_on with
    | C a =>
      refine ⟨((a : ℤ) : Or.𝔐.X.presheaf.stalk (centre z)), ?_, ?_⟩
      · rw [map_intCast, MvPolynomial.aeval_C]; exact (eq_intCast _ a).symm
      · rw [map_intCast, MvPolynomial.aeval_C]; exact (eq_intCast _ a).symm
    | add p q hp hq =>
      obtain ⟨s, hs1, hs2⟩ := hp
      obtain ⟨s', hs1', hs2'⟩ := hq
      exact ⟨s + s', by rw [map_add, map_add, hs1, hs1'], by rw [map_add, map_add, hs2, hs2']⟩
    | mul_X p i hp =>
      obtain ⟨s, hs1, hs2⟩ := hp
      refine ⟨s * ∏ k, t ⟨k, i k⟩, ?_, ?_⟩
      · rw [map_mul, map_prod, hs1, map_mul, MvPolynomial.aeval_X]
        congr 1
        simp only [ht1]
        unfold segreCoord
        rw [Finset.prod_div_distrib]
      · rw [map_mul, map_prod, hs2, map_mul, MvPolynomial.aeval_X]
        congr 1
        simp only [ht2']
        rw [Finset.prod_div_distrib]
  obtain ⟨s, hs1, hs2⟩ := hval (∑ l, Q l * P l - 1)
  have hz : genMap Or.𝔐.ξ ⟨centre z, Or.𝔐.all _⟩ s = 0 := by
    rw [hs1, map_sub, map_sum, map_one]
    simp only [map_mul, hP, hQ]
    rw [hsum, sub_self]
  have hs0 : s = 0 := hginj (by rw [hz, map_zero])
  have hW : ∑ l, MvPolynomial.aeval (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) (Q l) *
      MvPolynomial.aeval (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) (P l) = 1 := by
    have h2 := hs2
    rw [hs0, map_zero, map_sub, map_sum, map_one] at h2
    simp only [map_mul] at h2
    exact sub_eq_zero.mp h2.symm
  obtain ⟨l0, hl0⟩ : ∃ l, MvPolynomial.aeval
      (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) (P l) ≠ 0 := by
    by_contra hne
    push_neg at hne
    rw [Finset.sum_eq_zero (fun l _ => by rw [hne l, MulZeroClass.mul_zero])] at hW
    exact zero_ne_one hW
  have hunit : IsUnitAt Dc.y (f l0) w := by
    have hv := isValueAt_aeval_segreCoord_div Dc.y w ch hseg hsegw (P l0)
    rw [hP l0] at hv
    exact Exists.intro _ (And.intro hv hl0)
  obtain ⟨b, hb, u, hu, hΛ⟩ := hfr l0
  exact ⟨MuFrameAt.mk ch (f l0) (And.intro hwc hunit) b hb u hu hΛ⟩

end GlobalTheory.CompanionTheory.Ar.MuFrame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedSpaceOfDivisible
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem eq_one_of_divisible {P Q : Type*} [CommGroup P] [Finite Q] (c : P → Q)
    (hc : ∀ a b t : P, c a = c b → c (a * t) = c (b * t))
    (hd : ∀ n : ℕ, n ≠ 0 → ∀ x : P, ∃ y : P, y ^ n = x) (x : P) : c x = c 1 := by
  let H : Subgroup P :=
    { carrier := {a | c a = c 1}
      one_mem' := rfl
      mul_mem' := fun {a b} ha hb => by
        have := hc a 1 b ha
        rw [_root_.one_mul] at this
        exact this.trans hb
      inv_mem' := fun {a} ha => by
        have := hc a 1 a⁻¹ ha
        rw [_root_.mul_inv_cancel, _root_.one_mul] at this
        exact this.symm }
  have hinj : Function.Injective (fun q : P ⧸ H => c q.out) := by
    intro q r hqr
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' r, QuotientGroup.eq]
    have := hc _ _ (q.out)⁻¹ hqr
    simp only [mul_inv_cancel] at this
    change c _ = c 1
    rw [mul_comm, this.symm]
  have : Finite (P ⧸ H) := Finite.of_injective _ hinj
  have hi : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨y, rfl⟩ := hd _ hi x
  exact Subgroup.pow_index_mem H y

theorem connectedSpace_of_divisible : ∀ (K : Type) [Field K] [IsAlgClosed K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G], LocallyOfFiniteType G.hom → QuasiCompact G.hom → (∀ n : ℕ, n ≠ 0 → ∀ x : 𝟙_ (Over (Sp K)) ⟶ G, ∃ y : 𝟙_ (Over (Sp K)) ⟶ G, y ^ n = x) → ConnectedSpace G.left := by
  intro K _ _ G _ _ hl hq hd
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : IsNoetherian G.left := {}
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  let pt : (𝟙_ (Over (Sp K))).left := IsLocalRing.closedPoint K
  let F : (𝟙_ (Over (Sp K)) ⟶ G) → G.left := fun x => x.left pt
  have hopen : ∀ x : G.left, IsOpen (connectedComponent x) :=
    fun x => isOpen_connectedComponent_of_noetherianSpace x
  have : DiscreteTopology (_root_.ConnectedComponents G.left) :=
    ConnectedComponents.discreteTopology_iff.2 hopen
  have : Finite (_root_.ConnectedComponents G.left) := finite_of_compact_of_discrete
  let c : (𝟙_ (Over (Sp K)) ⟶ G) → _root_.ConnectedComponents G.left := fun x => F x
  have htr : ∀ a t : 𝟙_ (Over (Sp K)) ⟶ G,
      F (a * t) = (GrpObj.mulRight t).hom.left (F a) := by
    intro a t
    have h : a ≫ (GrpObj.mulRight t).hom = a * t := by
      simp [comp_lift_assoc, Hom.mul_def]
    simp only [F, ← h, Over.comp_left, Scheme.Hom.comp_apply]
  have hc : ∀ a b t, c a = c b → c (a * t) = c (b * t) := by
    intro a b t hab
    have := congrArg (Continuous.connectedComponentsMap (GrpObj.mulRight t).hom.left.continuous) hab
    simpa [c, htr] using this
  have hall := eq_one_of_divisible c hc hd
  have hsurj : ∀ x : G.left, IsClosed {x} → ∃ a, F a = x := by
    intro x hx
    refine ⟨Over.homMk (pointOfClosedPoint G.hom x hx) (pointOfClosedPoint_comp G.hom x hx), ?_⟩
    exact pointOfClosedPoint_apply G.hom x hx _
  have huniv : connectedComponent (F 1) = Set.univ := by
    by_contra hne
    obtain ⟨x, hx, hcl⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.2 hne)
      (IsOpen.isLocallyClosed isClosed_connectedComponent.isOpen_compl)
    obtain ⟨a, rfl⟩ := hsurj x hcl
    apply hx
    have h1 : connectedComponent (F a) = connectedComponent (F 1) :=
      ConnectedComponents.coe_eq_coe.1 (hall a)
    rw [← h1]
    exact mem_connectedComponent
  exact connectedSpace_iff_connectedComponent.2 ⟨F 1, huniv⟩

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedSpaceOfIsFieldGlobalFunctions
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem connectedSpace_of_isField_globalFunctions (Z : Scheme.{0}) (h : IsField Γ(Z, ⊤)) :
    ConnectedSpace Z := by
  have hne : Nonempty Z := by
    by_contra hZ
    have hb : (⊤ : Z.Opens) = ⊥ := by
      ext x
      exact (hZ ⟨x⟩).elim
    have hs : Subsingleton Γ(Z, ⊤) := by
      rw [hb]
      infer_instance
    obtain ⟨a, b, hab⟩ := h.exists_pair_ne
    exact hab (Subsingleton.elim a b)
  have hp : PreconnectedSpace Z := by
    refine preconnectedSpace_iff_clopen.2 fun U hU => ?_
    obtain ⟨e, he, hUe⟩ := GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen Z U hU
    by_cases h0 : e = 0
    · left
      rw [← hUe, h0, Z.basicOpen_zero]
      rfl
    · right
      obtain ⟨b, hb⟩ := h.mul_inv_cancel h0
      have h1 : e = 1 := by
        calc e = e * e * b := by rw [_root_.mul_assoc, hb, _root_.mul_one]
          _ = e * b := by rw [he]
          _ = 1 := hb
      rw [← hUe, h1, Z.basicOpen_of_isUnit isUnit_one]
      rfl
  exact { toPreconnectedSpace := hp, toNonempty := hne }

theorem geometricallyConnected_of_isIso_appTop :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K), QuasiCompact p → QuasiSeparated p →
      IsIso p.appTop → GeometricallyConnected p := by
  intro K _ X p _ _ _
  refine ⟨fun L _ y Z a q H => ?_⟩
  have hy : Flat y := by
    obtain ⟨φ, rfl⟩ := Spec.map_surjective y
    rw [Flat.SpecMap_iff]
    algebraize [φ.hom]
    exact inferInstanceAs (Module.Flat K L)
  have hq : IsIso q.appTop := GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback H
  let e₁ : Γ(Spec (.of L), ⊤) ≃+* Γ(Z, ⊤) := (asIso q.appTop).commRingCatIsoToRingEquiv
  let e₂ : Γ(Spec (.of L), ⊤) ≃+* L := (Scheme.ΓSpecIso (.of L)).commRingCatIsoToRingEquiv
  have hL : IsField Γ(Spec (.of L), ⊤) := MulEquiv.isField (Field.toIsField L) e₂.toMulEquiv
  exact connectedSpace_of_isField_globalFunctions Z (MulEquiv.isField hL e₁.symm.toMulEquiv)

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstructibleStableOpen
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isClosed_of_stable_of_noetherian {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] [QuasiSober X] (V : Set X)
    (hg : StableUnderGeneralization V) (hs : StableUnderSpecialization V) : IsClosed V := by
  have key : ∀ x ∈ V, irreducibleComponent x ⊆ V := by
    intro x hx y hy
    have hS : IsGenericPoint (isIrreducible_irreducibleComponent (x := x)).genericPoint
        (irreducibleComponent x) :=
      (isIrreducible_irreducibleComponent (x := x)).isGenericPoint_genericPoint
        isClosed_irreducibleComponent
    exact hs (hS.specializes hy) (hg (hS.specializes mem_irreducibleComponent) hx)
  have hV : V = ⋃₀ {C | C ∈ irreducibleComponents X ∧ C ⊆ V} := by
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨irreducibleComponent x,
        ⟨irreducibleComponent_mem_irreducibleComponents x, key x hx⟩, mem_irreducibleComponent⟩
    · exact Set.sUnion_subset fun C hC => hC.2
  rw [hV, Set.sUnion_eq_biUnion]
  exact Set.Finite.isClosed_biUnion
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset fun C hC => hC.1)
    fun C hC => isClosed_of_mem_irreducibleComponents C hC.1

theorem isOpen_of_stable (k : Type) [CommRing k] [IsNoetherianRing k] (U : Set (PrimeSpectrum k))
    (hg : StableUnderGeneralization U) (hs : StableUnderSpecialization U) : IsOpen U := by
  rw [← isClosed_compl_iff]
  exact isClosed_of_stable_of_noetherian Uᶜ
    (stableUnderGeneralization_compl_iff.mpr hs) (stableUnderSpecialization_compl_iff.mpr hg)

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DetLatticeFrameGen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.det_lattice_frame_gen : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (b₀ b : Fin r → V) (T : Matrix (Fin r) (Fin r) Ω) (p : Cpt ξ), LinearIndependent Ω b₀ → L.IsFrameAt b p → (∀ k, b k = ∑ k', T k' k • b₀ k') → (detLat L b₀).IsGenAt p T.det := by
  first | exact @LevelTowerAlt.determinant_lattice_generator | exact LevelTowerAlt.determinant_lattice_generator
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCoordsOfGenericPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coords_of_generic_point : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Spec (CommRingCat.of Ω) ⟶ Y.X), IsCptGen ξ₀ → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ Y.X) (bd : Ideal (MRing J)), Nonempty K ∧ (∀ q : X, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ∧ ξ ≫ f = ξ₀ ∧ Cmp.IsSncModel y D.dim bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ f (centre z) ∉ abLocus Y.t.G) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.exists_sncBase | exact GlobalTheory.CompanionTheory.Ar.SncBase.exists_sncBase | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.exists_sncBase <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDvrThroughDiscPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_through_disc_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (z : Fin n → ℂ), z ∈ Metric.ball (0 : Fin n → ℂ) 1 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : C.R →+* V) (r : V →+* ℂ) (tV : SAB H (Sp V)) (_ : SABMap tV C.t (spMap f)), GlobalTheory.LN.CDvr V ∧ Function.Surjective r ∧ RingHom.ker r = IsLocalRing.maximalIdeal V ∧ r.comp f = C.ψ z ∧ GlobalTheory.LN.PolAt tV (Out.jK V) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotLoc.exists_curve_through_point | exact GlobalTheory.CompanionTheory.Ar.QuotLoc.exists_curve_through_point | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotLoc.exists_curve_through_point <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieMetricStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lie_metric : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li), Nonempty (LieMetric M y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.MetricAny.exists_lieMetric | exact GlobalTheory.CompanionTheory.Ar.MetricAny.exists_lieMetric | (intros; apply GlobalTheory.CompanionTheory.Ar.MetricAny.exists_lieMetric <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExpLogCoverBoundStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_exp_log_cover_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n a : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (ρ : ℝ) (e : Flat.FamExp t.G M (Metric.ball 0 ρ) ψ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ), 0 < ρ → ρ ≤ 1 → Flat.IsHolPts (Metric.ball 0 ρ) ψ → (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, (∀ p, p ∈ e.per ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ↔ ∃ x, L.P w x = p) ∧ ∀ (N : ℕ) (ζ : ℂˣ) (x x' : Λ), 0 < N → GlobalTheory.UU.CubWeil t.cub N (e.ex ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ((N : ℂ)⁻¹ • L.P w x)) (e.ex ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ((N : ℂ)⁻¹ • L.P w x')) (unitOn ζ) → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((L.E x x' : ℤ) : ℂ) / N)) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ (ws : ℕ → Fin n → ℂ) (W : Submodule ℤ Λ) (per : W →+ (Fin g → ℂ)), (∀ m, ws m ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le) → Tendsto (fun m => GroundTheory.Heights₂.Heights.Regular.expCover a (ws m)) atTop (𝓝 z) → (∀ x : W, Tendsto (fun m => L.P (ws m) x) atTop (𝓝 (per x))) → (∀ (x : ℕ → Λ) (p : Fin g → ℂ), Tendsto (fun m => L.P (ws m) (x m)) atTop (𝓝 p) → ∃ x₀ : W, p = per x₀ ∧ ∀ᶠ m in atTop, x m = x₀) → (∀ x : W, per x ∈ e.per ((ρ : ℂ) • z)) ∧ (∀ p ∈ e.per ((ρ : ℂ) • z), ∃ x : W, per x = p) ∧ ∀ (N : ℕ) (ζ : ℂˣ) (x x' : W), 0 < N → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((L.E x x' : ℤ) : ℂ) / N) → GlobalTheory.UU.CubWeil t.cub N (e.ex ((ρ : ℂ) • z) ((N : ℂ)⁻¹ • per x)) (e.ex ((ρ : ℂ) • z) ((N : ℂ)⁻¹ • per x')) (unitOn ζ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotLoc.limit_lattice | exact GlobalTheory.CompanionTheory.Ar.QuotLoc.limit_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotLoc.limit_lattice <;> assumption)
end

