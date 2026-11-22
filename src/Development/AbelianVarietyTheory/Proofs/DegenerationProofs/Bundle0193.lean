import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0095
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0093
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0169
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisRowsHaveClassWeight
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ClassWeight
open GlobalTheory.UT

theorem proj_mulVec {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) {T : AddSubgroup S.Gam}
    (hT : S.IsoFree T) (c : T →+ ZMod S.N) {K : Type} [CommRing K] (y : o →+* K) (v : S.J → K)
    (h : ∀ t : T, ((S.ρ t).map y).mulVec v = y S.ζN ^ (c t).val • v) : ((S.proj T c).map y).mulVec v = v := by
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero S.N := ⟨by omega⟩
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have := Fintype.ofFinite T
  obtain ⟨d, ⟨e⟩⟩ := hT.2
  have hu : IsUnit (Nat.card T : o) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
    exact S.unit.pow _
  have hζ : S.ζN ^ S.N = 1 := (S.prim.pow (pow_pos (NeZero.pos _) 2) (by ring) : IsPrimitiveRoot S.ζN S.N).pow_eq_one
  have h1 : ∀ a : ZMod S.N, S.ζN ^ (-a).val * S.ζN ^ a.val = 1 := fun a => by
    have := (AddChar.zmodChar S.N hζ).map_add_eq_mul (-a) a
    rw [neg_add_cancel, AddChar.map_zero_eq_one] at this
    exact this.symm
  let φ : Matrix S.J S.J o →+ (S.J → K) :=
    { toFun := fun M => (M.map y).mulVec v
      map_zero' := by simp
      map_add' := fun M M' => by rw [Matrix.map_add _ (map_add y), Matrix.add_mulVec] }
  have hφ : ∀ (a : o) M, φ (a • M) = y a • φ M := fun a M => by
    funext i
    simp [φ, Matrix.mulVec, dotProduct, Finset.mul_sum, _root_.mul_assoc]
  show φ _ = v
  rw [ThetaSys.proj, finsum_eq_sum_of_fintype, hφ, map_sum]
  have h2 : ∀ t : T, φ (S.ζN ^ (-(c t)).val • S.ρ t) = v := fun t => by
    rw [hφ]
    refine (congrArg _ (h t)).trans ?_
    rw [smul_smul, ← map_pow, ← map_mul, h1, map_one, one_smul]
  simp only [h2, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul, ← map_natCast y, ← map_mul, ← Nat.card_eq_fintype_card,
    Ring.inverse_mul_cancel _ hu, map_one, one_smul]

theorem mulVec_eq_of_eigen {K B M J : Type} [CommRing K] [CommRing B] [AddCommGroup M] [Module B M] [Fintype J]
    (κ : K →+* B) (hκ : Function.Injective κ) (E : M →ₗ[B] M) {s : J → M} (hs : LinearIndependent B s)
    (m : Matrix J J K) (h₁ : ∀ j, E (s j) = ∑ l, κ (m l j) • s l) {t : M} {z c : K} (h₂ : E t = κ z • t)
    {v : J → K} (h₃ : ∑ j, κ (v j) • s j = κ c • t) : m.mulVec v = z • v := by
  have h₄ := congrArg E h₃
  rw [map_smul, h₂, smul_comm, ← h₃, map_sum] at h₄
  simp only [map_smul, h₁, Finset.smul_sum, smul_smul] at h₄
  rw [Finset.sum_comm] at h₄
  simp only [← Finset.sum_smul] at h₄
  funext l
  apply hκ
  have h₅ := Fintype.linearIndependent_iffₛ.1 hs _ _ h₄ l
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.smul_apply, smul_eq_mul]
  rw [← h₅]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

section
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt GlobalTheory.FieldBaseChange
attribute [local instance] gtGroup
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {F : Type} [Field F]
  [Algebra (FractionRing R) F]

theorem isTor_nsmul {τ : Multiplicative D.toPre.X →* Fˣ} {g : GtPtF D.toPre F} (h : IsTor τ g) (n : ℕ) :
    IsTor (τ ^ n) (n • g) := by
  rw [isTor_iff, isTorusPtF_iff_eq] at h ⊢
  rw [h, ← map_nsmul]
  rfl

theorem exists_qkPt_tor {τ : Multiplicative D.toPre.X →* Fˣ} {g : GtPtF D.toPre F} (h : IsTor τ g) {n : ℕ}
    (hn : τ ^ n = 1) : ∃ q : QkPt D.toPre F n, q.y = 0 ∧ q.g = g := by
  refine ⟨⟨0, g, n • g, (isNsmul_iff_eq _ _ _).2 rfl, (isIota_iff_eq D.tau_bimult _ _).2 ?_⟩, rfl, rfl⟩
  have := isTor_nsmul h n
  rw [hn, isTor_iff, isTorusPtF_iff_eq] at this
  rw [this, map_zero]
  exact map_zero _

variable [CharZero R] [IsAlgClosed F] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem act_of_class (hL : LL) (hA : AdmBase R I) (hG : IsSemiAbelian G) (U : Unif I D A G) {N : ℕ} (hN : Odd N)
    (q : QkPt D.toPre F N) {τ : Multiplicative D.toPre.X →* Fˣ} (hy : q.y = 0) (hτ : IsTor τ q.g) (hτN : τ ^ N = 1)
    {x : TFK (R := R) F ⟶ A.A} (hx : QkToAkU U.toUnifPre F N q x)
    {θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)} (hθ : SymLift A.A A.L N N x θ) {w₀ : W0 U.toUnifPre}
    (hw₀ : w₀.IsGen) {t t' : SecA A F N} {s : Fam D.toPre F N} (hs : U.ExpandsF F N w₀ t s) (c : D.toPre.X)
    (hc : ∀ α, (∀ m, α ≠ c + N • m) → ∀ j, (s.s α).f j = 0) (ha : IsActOf A.A A.L N θ t t') :
    SecM.ofSec A.A t' = kf R F (τ (Multiplicative.ofAdd c)).val • SecM.ofSec A.A t := by
  obtain ⟨w, hw⟩ := (GlobalTheory.UT.SymFrame.main hL R I hA D F N hN q).1
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hL.1.globalFns U F hN.pos w₀ hw₀
  have hΦ := GlobalTheory.T.symmetricLift_oddOrder_acts_as_expansionOperator hL R I hA D A G hG U F N hN q x hx θ hθ w₀ hw₀ w hw t t' s (e t') hs ((he _ _).2 rfl) ha
  have h₁ := ((TorusWeight.torus_weight hL R I hA D A G hG U F N hN q τ hy hτ w hw).2 _ _).1 hΦ
  have h₂ : e t' = (τ (Multiplicative.ofAdd c)).val • s := fam_ext fun α j => by
    refine (h₁ α j).trans ?_
    by_cases h : ∃ m, α = c + N • m
    · obtain ⟨m, rfl⟩ := h
      have : τ (Multiplicative.ofAdd (c + N • m)) = τ (Multiplicative.ofAdd c) := by
        rw [ofAdd_add, map_mul, ofAdd_nsmul, map_pow, ← MonoidHom.pow_apply, hτN, MonoidHom.one_apply, _root_.mul_one]
      rw [this]
      rfl
    · have h0 := hc α (fun m hm => h ⟨m, hm⟩) j
      rw [DVR.smul_f, h0, mul_zero, mul_zero]
  have h₃ := e.injective (h₂.trans ((congrArg _ ((he _ _).1 hs).symm).trans (e.map_smul _ _).symm))
  exact Subtype.ext (funext fun j => congrArg (fun z : LB.Sec _ => z.f j) h₃)
end

theorem exists_torus_point (hL : LL) (hT : UTorsSt) {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} {u : ρ.UTest p y₀} (l : u.Lab)
    (a : S.perp l.yy.ker) : ∃ (q : QkPt u.D.toPre (PadicAlgCl p) S.N) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)
      (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ), q.y = 0 ∧ IsTor τ q.g ∧ τ ^ S.N = 1 ∧
      QkToAkU u.U.toUnifPre (PadicAlgCl p) S.N q x ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt (S.r • a.1)).left ∧
      ∀ α, (τ (Multiplicative.ofAdd α)).val = y₀ (algebraMap o S.R S.ζN) ^ (l.wt α a).val := by
  have : CharZero u.V :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  have hA : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hr := S.r_pos
  have hN₂ := S.N_ge
  have : NeZero S.N := ⟨by omega⟩
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  obtain ⟨x, hx, hadd, -, honto⟩ := GlobalTheory.T.uniformised_model_labelled_torsion_points o Ω S ρ p y₀ u
  let y : o →+* PadicAlgCl p := y₀.comp (algebraMap o S.R)
  obtain ⟨pk, τ, hy, hτ, hq, hval⟩ := GlobalTheory.T.exists_torus_torsionPoint_standardAlternatingForm hL hT o Ω S ρ p y₀ u l x hx hadd honto a.1 a.2
  have hζ : y S.ζN ^ S.N = 1 := by
    have h : IsPrimitiveRoot S.ζN S.N := S.prim.pow (pow_pos (NeZero.pos _) 2) (by ring)
    rw [← map_pow, h.pow_eq_one, map_one]
  have hwt : ∀ α, ((τ ^ S.r) (Multiplicative.ofAdd α)).val = y S.ζN ^ (l.wt α a).val := fun α => by
    obtain ⟨a', ha'⟩ := l.yy_onto (QuotientAddGroup.mk α)
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hval a' α ha', l.wt_eq a' α ha' a, ZMod.castHom_apply,
      ZMod.cast_eq_val, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ, ← map_pow y, ThetaSys.ζN, ← pow_mul]
    refine (map_pow y _ _).symm.trans (congrArg y ?_)
    rw [← pow_mul]
    congr 1
    ring
  have hτN : (τ ^ S.r) ^ S.N = 1 := MonoidHom.ext fun α => Units.ext (by
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, ← ofAdd_toAdd α, hwt, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    rfl)
  let _ := TorusExt.gtGroup u.D.toPre (PadicAlgCl p)
  have hτ' := isTor_nsmul hτ S.r
  obtain ⟨q, hq₀, hq₁⟩ := exists_qkPt_tor hτ' hτN
  have hxr : x a ^ S.r = x (S.r • a) := by
    have h0 : x 0 = 1 := by
      have := hadd 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    exact (map_pow (⟨⟨fun z => x z.toAdd, h0⟩, fun z z' => hadd _ _⟩ : Multiplicative S.Gam →* _)
      (Multiplicative.ofAdd a.1) S.r).symm
  have hq' := (GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL u.V _ hA u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N S.r (S.r * S.N) (by omega) hr
    (mul_comm _ _) q pk (x a)).2 (hq₀.trans hy.symm) ((TorusExt.isNsmul_iff_eq _ _ _).2 hq₁) hq
  rw [hxr] at hq'
  exact ⟨q, _, _, hq₀, hq₁ ▸ hτ', hτN, hq', hx _, hwt⟩

theorem row_weight : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (f : S.J → ∀ α, u.D.toPre.SecB S.N α), u.Basis l S.N σ cls f → ∀ b : Matrix S.J S.J (FractionRing u.V), u.Link σ b → ∀ i, ((S.proj _ (l.wt (cls i))).map fun a => y₀ (algebraMap o S.R a)).mulVec (b.map (algebraMap _ (PadicAlgCl p)) i) = b.map (algebraMap _ (PadicAlgCl p)) i := by
  intro hL hT o Ω _ _ _ _ S ρ p _ y₀ u l σ cls f hB b hb i
  have : CharZero u.V :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  have hA : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hodd : Odd S.N := by rw [ρ.N_eq]; exact ρ.n_odd.pow.pow
  have hN₄ : 4 ≤ S.N := by
    have h₁ : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    rw [ρ.N_eq]
    exact Nat.pow_le_pow_left h₁ 2
  obtain ⟨w, hw⟩ := u.lb
  obtain ⟨w₀, hw₀⟩ := u.U.toUnifPre.ext
  choose s hs using fun j => exists_moved u hw (ρ.s j)
  obtain ⟨t, e, ht, he, hcrd⟩ := GlobalTheory.T.exists_generic_sections_from_integral_model hL o Ω S ρ p y₀ u S.N S.J σ f hB.2.2.2.1 hB.2.2.2.2.1 w₀ hw₀
  obtain ⟨c, hc⟩ := GlobalTheory.T.abelianSections_proportional_of_coordinates hL.1.globalFns u.V u.A (PadicAlgCl p) S.N S.J S.J t s
    (b.map (algebraMap _ (PadicAlgCl p))) fun z => by
      obtain ⟨a, rfl⟩ : ∃ a : u.PtC, z = a ≫ u.U.gen.hom := ⟨z ≫ u.U.gen.inv, by simp⟩
      obtain ⟨v, hv⟩ := ((CrdCalc.crd_calculus _ (LPow u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p))) _ s
        (DVR.linComb_isLB _ u.A.isLB _ _)).1 (PadicAlgCl p) (ptSecT u.A.A (a ≫ u.U.gen.hom)).left).1
      have h₁ := hb a v (GlobalTheory.T.homogeneousCoordinates_of_geometricFibre o Ω S ρ p y₀ u w hw s hs a v hv)
      exact ⟨v, (GlobalTheory.T.crd_ne_zero_injective_surjective_of_basis hL o Ω S ρ p y₀ u l S.N hN₄ S.J σ cls f hB).1 a _ h₁, hv, hcrd a _ h₁⟩
  let y : o →+* PadicAlgCl p := y₀.comp (algebraMap o S.R)
  refine proj_mulVec S l.isoFree _ y _ fun a => ?_
  obtain ⟨q, x, τ, hq₀, hτ, hτN, hq, hx, hwt⟩ := exists_torus_point hL hT l a
  obtain ⟨θ, hθ, hact⟩ := GlobalTheory.T.exists_symmetricLift_action_geometricFibre o Ω S ρ p y₀ u w hw s hs a.1 _ hx (hq w₀ hw₀).1
  obtain ⟨E, hE, -⟩ := GlobalTheory.thetaGrp_acts_linearly hL.1.globalFns _ u.A (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p))
  have h₁ : ∀ j, E θ (SecM.ofSec u.A.A (s j)) =
      ∑ m, kf u.V (PadicAlgCl p) (y (S.ρ a m j)) • SecM.ofSec u.A.A (s m) := fun j =>
    hact j (SecM.toSec u.A.A (E θ (SecM.ofSec u.A.A (s j)))) ((hE _ _ _).2 rfl)
  have h₂ : E θ (SecM.ofSec u.A.A (t i)) =
      kf u.V (PadicAlgCl p) (y S.ζN ^ (l.wt (cls i) a).val) • SecM.ofSec u.A.A (t i) := by
    have h₃ := act_of_class hL hA u.semi u.U hodd q hq₀ hτ hτN hq hθ hw₀ (ht i) (cls i)
      (fun α hα => he i α (hB.2.2.2.2.2.1 i α hα)) (t' := SecM.toSec u.A.A (E θ (SecM.ofSec u.A.A (t i))))
      ((hE _ _ _).2 rfl)
    exact h₃.trans (congrArg (fun z => kf u.V (PadicAlgCl p) z • SecM.ofSec u.A.A (t i)) (hwt (cls i)))
  exact mulVec_eq_of_eigen (kf u.V (PadicAlgCl p)) (kf_bijective _ _).1 (E θ).toLinearMap
    (GlobalTheory.T.linearIndependent_thetaBasis_geometric_fibre hL o Ω S ρ p y₀ u w hw s hs) ((S.ρ a).map y) h₁ h₂ (hc i)

end GlobalTheory.ZH.ClassWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcFamilyFourthConditionInvertiblePushforwardStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcFamily_fourthCondition_invertible_pushforward : DVR.TwistBaseChangeStatement → Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ArcFamSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → Amp Y → Y.N4 := by
  first | exact @GlobalTheory.LN.ArcClause.arc_clause | exact GlobalTheory.LN.ArcClause.arc_clause | (intros; apply GlobalTheory.LN.ArcClause.arc_clause <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CompatibleLineBundlesFormalThickening
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalAlgebraise

theorem ker_factor_sq {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) :
    RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))) ^ 2 = ⊥ := by
  have hle : RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))) ≤
      (I ^ (e + 1)).map (Ideal.Quotient.mk _) := by
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact Ideal.mem_map_of_mem _ hx
  refine le_bot_iff.1 ((Ideal.pow_right_mono hle _).trans ?_)
  rw [← Ideal.map_pow, ← pow_mul, le_bot_iff, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact Ideal.pow_le_pow_right (by omega)

open GlobalTheory.AbLaw in

theorem algebraisation : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, Smooth (Y e).hom) → (∀ e, (N e).IsLB ∧ (v e).IsGen) → RelAmple (Y 0) (N 0) → ∃ (B : Over (Spec (CommRingCat.of R))) (M : LB B.left) (b : ∀ e, (Y e).left ⟶ B.left), GlobalTheory.AbLaw.IsProjBy B.hom ∧ Smooth B.hom ∧ M.IsLB ∧ RelAmple B M ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  intro _ _ R _ _ _ _ I hI hc _ Y β N v hβ hY hN hA
  have hfl : ∀ e, Flat (Y e).hom := fun e => by have := hY e; infer_instance
  have hamp : ∀ e, RelAmple (Y e) (N e) := by
    intro e
    induction e with
    | zero => exact hA
    | succ e ih =>
      have := hY (e + 1)
      exact GlobalTheory.T.relAmple_lift_squareZero_thickening _ _ _ (Ideal.Quotient.factor_surjective _) (ker_factor_sq I e) (Y (e + 1)) (Y e) (β e)
        (hβ e) inferInstance _ _ (hN _).1 (hN _).1 ⟨v e, (hN e).2⟩ ih
  have hproj : ∀ e, IsProjBy (Y e).hom := fun e => by
    obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy _ (Y e) (N e) (hN e).1).1 (hamp e)
    exact ⟨_, isLB_pw (hN e).1 _, n, s, hs⟩
  have hle : I ^ (0 + 1) ≤ IsLocalRing.maximalIdeal R := by
    rw [zero_add, pow_one]
    exact IsLocalRing.le_maximalIdeal hI
  let g₀ : R ⧸ I ^ (0 + 1) →+* IsLocalRing.ResidueField R := Ideal.Quotient.factor hle
  have hg₀ : Function.Surjective g₀ := Ideal.Quotient.factor_surjective hle
  have hpb := IsPullback.of_hasPullback (Y 0).hom (Spec.map (CommRingCat.ofHom g₀))
  obtain ⟨d, hd, h0, n, s₀, hs₀⟩ := GlobalTheory.T.exists_very_ample_power _ (Y 0) (N 0) (hN 0).1 hA _ g₀ _ _ _ hpb
  have hv : ∀ e, LBIso (AbLaw.pw (N e) d) ((AbLaw.pw (N (e + 1)) d).pull (β e)) := fun e => by
    rw [GlobalTheory.Algebraise.pw_pull]
    exact GlobalTheory.Algebraise.lbIso_pw ⟨v e, (hN e).2⟩ d
  choose v' hv' using hv
  have hN' : ∀ e, (AbLaw.pw (N e) d).IsLB ∧ (v' e).IsGen := fun e => ⟨isLB_pw (hN e).1 d, hv' e⟩
  have hL := LB.isLB_pull (hN' 0).1 (pullback.fst (Y 0).hom (Spec.map (CommRingCat.ofHom g₀)))
  choose s hs0 hs using fun j => GlobalTheory.T.exists_compatible_sections_thickenings_localRing R I hI Y β hβ hfl hproj
    (fun e => AbLaw.pw (N e) d) v' hN' _ g₀ hg₀ _ _ _ hpb _ _ hL (CubePf.idIsoL_isGen hL) h0 (s₀ j)
  have hva : VeryAmpleBy (Y 0).hom (AbLaw.pw (N 0) d) (fun j => s j 0) := by
    have : (fun j => s j 0) = s₀ := funext hs0
    rw [this]
    exact hs₀
  obtain ⟨B, H, s', b, w, hH, hB, hb, hbβ, -, -⟩ := GlobalTheory.T.exists_projective_algebraisation_formal_complete_local R I hI hc Y β hβ hfl
    (fun e => AbLaw.pw (N e) d) v' hN' n (fun e j => s j e) (fun e j => hs j e) hva
  have hP : IsProjBy B.hom := ⟨H, hH, n, s', hB⟩
  have hS : Smooth B.hom := GlobalTheory.T.smooth_of_smooth_thickenings' R I hI B (isProper_of_isProjBy R B.left B.hom hP) Y b hb hY
  have hF : Flat B.hom := inferInstance
  obtain ⟨M, hM, hNM⟩ := GlobalTheory.LBAlgLocal.exists_lineBundle_of_thickenings R I hI hc Y β hβ B b hP hF hb hbβ N v hN
  haveI : Nontrivial (R ⧸ I ^ (0 + 1)) := g₀.domain_nontrivial
  exact ⟨B, M, b, hP, hS, hM, GlobalTheory.T.relAmple_of_ample_on_closed_subscheme_localBase R B M hF hP hM _ _ Ideal.Quotient.mk_surjective (Y 0) (b 0) (hb 0)
    (N 0) (hN 0).1 (hNM 0) hA, hb, hbβ, hNM⟩

end GlobalTheory.FormalAlgebraise
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsCombTranslatesOfNuGe
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem isActOf_smul_of_val_eq {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    {m : T ⊗ A ⟶ A} {a b : ℤ} {α α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
    (ea : ∀ (r : (T ⊗ A).left ⟶ (T ⊗ A).left) y J, Good L y J → val α r y J = val α' r y J)
    {θ θ' : ThetaGrp A L a T} (ept : θ.pt = θ'.pt)
    (eθ : ∀ y J, Good L y J → val θ.φ (𝟙 _) y J = val θ'.φ (𝟙 _) y J)
    {th th' : LB.Sec (LPow A L b T)} {s₀ s₁ t' : LB.Sec (LPow A L a T)} {c : Γ(T.left, ⊤)}
    (eth : ∀ j, th.f j = liftFun A _ c * th'.f j)
    (hs₀ : IsTwistPull A L (lift (fst T A) m) m (lift_snd _ _) a b α th s₀)
    (hs₁ : IsTwistPull A L (lift (fst T A) m) m (lift_snd _ _) a b α' th' s₁) (ht' : IsActOf A L a θ' s₁ t') :
    IsActOf A L a θ s₀ (SecM.toSec A (c • SecM.ofSec A t')) := by
  have f₁ : (lift (fst T A) m).left ≫ (fst T A).left = (fst T A).left := by
    rw [← Over.comp_left, lift_fst]
  have f₂ : (translT A θ'.pt).left ≫ (fst T A).left = (fst T A).left := by
    rw [← Over.comp_left, translT, lift_fst]
  refine VVRank.isTwistPull_of_sv A hL θ.isGen fun y J hJ => ?_
  rw [ThetaPtMove.sv_of_eq_mul (t := t') (c := c) (fun j => rfl) _ y hJ, VVRank.sv_of_isTwistPull A ht' _ y hJ,
    VVRank.sv_of_isTwistPull A hs₁ _ y hJ, VVRank.sv_of_isTwistPull A hs₀ _ y hJ,
    ThetaPtMove.sv_of_eq_mul eth _ y hJ, eθ y J hJ, ea _ y J hJ, ept]
  simp only [Category.assoc, f₁, f₂]
  ring

theorem isActOf_smul_of_thC (hLaw : Laws) {V : Type} [CommRing V] [IsDomain V] [CharZero V]
    (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) {F : Type} [Field F] [Algebra (FractionRing V) F]
    {ρ : LB.Gen (A.L.pull (eSec A.A))} {m : ℕ} (hm : Odd m) {th th' : SecA A F 1} {c : Γ((TFK (R := V) F).left, ⊤)}
    (eth : ∀ j, th.f j = liftFun A.A _ c * th'.f j)
    {α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := V) F) A.A).left, (snd (TFK (R := V) F) A.A ^ m).left]
      ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])} {s₀ : SecA A F (m ^ 2)} (hα : α.IsGen)
    (hn : LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left)
      (rigT A.A A.L ρ (TFK (R := V) F) (((m ^ 2 : ℕ) : ℤ) - 1)))
    (hs₀ : IsTwistPull A.A A.L (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₀)
    {x : TFK (R := V) F ⟶ A.A} (hx : x ^ (m ^ 2) = 1) {t' : SecA A F (m ^ 2)} {c' : F} (h : ThC A ρ m th' x t' c')
    {θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := V) F)} (hθ : SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x θ) :
    IsActOf A.A A.L ((m ^ 2 : ℕ) : ℤ) θ s₀ (SecM.toSec A.A (c • SecM.ofSec A.A t')) := by
  have hL := A.isLB
  let T := TFK (R := V) F
  have hu : IsUnit ((m ^ 2 : ℕ) : Γ(Spec (CommRingCat.of (FractionRing V)), ⊤)) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).commRingCatIsoToRingEquiv.symm
    rw [← map_natCast e]
    refine (IsUnit.mk0 _ ?_).map e
    rw [← map_natCast (algebraMap V (FractionRing V))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2
      (Nat.cast_ne_zero.2 (pow_ne_zero 2 hm.pos.ne'))
  obtain ⟨α', s₁, θ', hα', hn', hs₁, hθ', ht', -⟩ := h
  obtain ⟨-, huniq⟩ := hLaw.symLift _ A (m ^ 2) hm.pow hu T x hx
  have ea := gen_unique hL (fst T A.A).left (ptSecT A.A 1).left NormTheta.ptSec_fst
    (CommPairing.surj_fst hLaw.globalFns A.isAb T) hα hα' (fun y J hJ => by
      have a := (val_corr hJ hn (𝟙 _)).trans (val_corr hJ hn' (𝟙 _)).symm
      rwa [val_pull hJ, val_pull hJ, Category.id_comp] at a)
  have eθ := huniq θ θ' hθ hθ'
  have ept : θ.pt = θ'.pt := hθ.pt_eq.trans hθ'.pt_eq.symm
  have eθ' : ∀ y J, Good A.L y J → val θ.φ (𝟙 _) y J = val θ'.φ (𝟙 _) y J := fun y J hJ => by
    rw [val_corr hJ eθ]
  exact isActOf_smul_of_val_eq (α := α) (α' := α') (th := th) (th' := th') (s₁ := s₁) hL
    (fun r y J hJ => ea _ r y J hJ) ept eθ' eth hs₀ hs₁ ht'

theorem comb_smul {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {k : ℤ} {n : ℕ}
    {σ σ₁ : LB.Sec (LPow A L k T)} {t : Fin n → LB.Sec (LPow A L k T)} {a : Fin n → Γ(T.left, ⊤)} {c : Γ(T.left, ⊤)}
    (eσ : σ = SecM.toSec A (∑ i, a i • SecM.ofSec A (t i))) (h : ∀ j, σ₁.f j = liftFun A _ c * σ.f j) (j) :
    σ₁.f j = ∑ i, liftFun A _ (a i) * (SecM.toSec A (c • SecM.ofSec A (t i))).f j := by
  have e₀ : SecM.ofSec A σ = ∑ i, a i • SecM.ofSec A (t i) := congrArg (SecM.ofSec A) eσ
  have e₁ : SecM.ofSec A σ₁ = c • SecM.ofSec A σ := Subtype.ext (funext h)
  have e : SecM.ofSec A σ₁ = ∑ i, a i • c • SecM.ofSec A (t i) := by
    rw [e₁, e₀, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  have e' := congrArg (fun q => q.1 j) e
  simp only [Submodule.coe_sum, Finset.sum_apply] at e'
  exact e'

theorem exists_isComb_translates_of_nuGe : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th' : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th' ϑ → Prim D Q v ϑ → ∀ (m N : ℕ), Odd m → IsUnit (m : V) → 3 ≤ m → N = m ^ 2 → ∀ (th : SecA A F 1) (c : F), IsComb (fun _ : Unit => th') (fun _ => c) th → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := V) F) A.A).left, (snd (TFK (R := V) F) A.A ^ m).left] ![(N : ℤ), -((1 : ℕ) : ℤ)])) (s₀ : SecA A F N), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := V) F) ((N : ℤ) - 1)) → IsTwistPull A.A A.L (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _) (N : ℤ) ((1 : ℕ) : ℤ) α th s₀ → ∀ (σ σ₁ : SecA A F N) (s : Fam D.toPre F N), U.ExpandsF F N w₀ σ s → NuGe D Q F v N s 0 → IsComb (fun _ : Unit => σ) (fun _ => c) σ₁ → ∃ (n : ℕ) (a : Fin n → F) (x : Fin n → (TFK (R := V) F ⟶ A.A)) (t : Fin n → SecA A F N), (∀ i, 0 ≤ v (a i) ∧ x i ^ N = 1 ∧ ∀ θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := V) F), SymLift A.A A.L N N (x i) θ → IsActOf A.A A.L N θ s₀ (t i)) ∧ IsComb t a σ₁ := by
  intro hLL hBC hVR hTW hUU V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th' ϑ hth hprim m N hm hmu h3
    hNm th c hthc α s₀ hα hn hs₀ σ σ₁ s hσ hs hσ₁
  subst hNm
  have hLaw : Laws := hLL.1
  obtain ⟨n, a, x, t', c', r, h, rfl⟩ := (GlobalTheory.T.valuation_nonneg_iff_span_multiplicationTranslates hLL hBC hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th' ϑ
    hth hprim m hm hmu h3 s).1 hs
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hN1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  obtain ⟨hB, hlin⟩ := expBijF_and_expandsF_lin hLL V _ hA D A G hG U
  obtain ⟨hB₁, hB₂⟩ := hB F (m ^ 2) hN1 w₀ hN.1
  let T := TFK (R := V) F
  let κ : F ≃+* Γ(T.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv

  have hsum : ∀ S : Finset (Fin n), U.ExpandsF F (m ^ 2) w₀
      (SecM.toSec A.A (∑ i ∈ S, κ (a i) • SecM.ofSec A.A (t' i))) (∑ i ∈ S, a i • r i) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have := hlin F (m ^ 2) w₀ σ σ (SecM.toSec A.A (κ (-1) • SecM.ofSec A.A σ + SecM.ofSec A.A σ)) _ _ (-1) hσ hσ
        fun j => rfl
      rw [map_neg, map_one, neg_one_smul, neg_one_smul, neg_add_cancel, neg_add_cancel] at this
      rw [Finset.sum_empty, Finset.sum_empty]
      exact this
    | insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact hlin F (m ^ 2) w₀ _ _ _ _ _ (a i) (h i).2.2.2 ih fun j => rfl
  have eth : ∀ j, th.f j = liftFun A.A _ (κ c) * th'.f j := fun j => (hthc j).trans (Fintype.sum_unique _)
  refine ⟨n, a, x, fun i => SecM.toSec A.A (κ c • SecM.ofSec A.A (t' i)), fun i => ⟨(h i).1, (h i).2.1, fun θ hθ => ?_⟩,
    fun j => ?_⟩
  · exact isActOf_smul_of_thC hLaw A hm eth hα hn hs₀ (h i).2.1 (h i).2.2.1 hθ
  · exact comb_smul (a := fun i => κ (a i)) (c := κ c) ((hB₂ _).unique hσ (hsum Finset.univ))
      (fun j => (hσ₁ j).trans (Fintype.sum_unique _)) j

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointUnitValuePrimitiveIntegralFamiStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionPoint_unit_value_primitive_integral_family : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ k n : ℕ, 4 ≤ k → n.Prime → IsUnit (n : V) → ∀ (t : SecA A F k) (s : Fam D.toPre F k) (α : D.toPre.X), U.ExpandsF F k w₀ t s → IntGe D v s 0 → (∀ q : ℚ, 0 < q → ¬ VGe D F v k α (s.s α) q) → ∃ (j : ℕ) (x : TFK (R := V) F ⟶ A.A), 2 ≤ j ∧ FromGt U.toUnifPre (n ^ j) x ∧ ∀ e (c : F), IsTorsFrame A ρ (n ^ j) x e → ValAt t x e c → v c = 0 := by
  first | exact @GlobalTheory.OneBasis.UnitValue.exists_unit_value | exact GlobalTheory.OneBasis.UnitValue.exists_unit_value | (intros; apply GlobalTheory.OneBasis.UnitValue.exists_unit_value <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralFamilyValuesTorsionTorusExtensionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_family_values_torsion_torusExtension : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → ∀ (x : TFK (R := V) F ⟶ A.A) e (t : SecA A F k) (s : Fam D.toPre F k) (c : F), FromGt U.toUnifPre n x → IsTorsFrame A ρ n x e → U.ExpandsF F k w₀ t s → IntGe D v s 0 → ValAt t x e c → 0 ≤ v c := by
  first | exact @GlobalTheory.OneBasis.integral_value_at_torsion | exact GlobalTheory.OneBasis.integral_value_at_torsion | (intros; apply GlobalTheory.OneBasis.integral_value_at_torsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelUniformisationOfAbelianLocusDirectImageStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_uniformisation_of_abelianLocus_directImage : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Ega → USt → PelSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → Y.N3 := by
  first | exact @GlobalTheory.model_uniformisation_of_clauses | exact GlobalTheory.model_uniformisation_of_clauses | (intros; apply GlobalTheory.model_uniformisation_of_clauses <;> assumption)
end

