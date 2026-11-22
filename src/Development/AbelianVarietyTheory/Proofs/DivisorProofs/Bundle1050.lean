import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import GroundTheory.Brauer.Splitting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0124
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0994
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0993
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0934
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0975
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotMkEqIffPositiveScalarFormIsomorphic
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx.Form

theorem rel_equivalence {p : ℕ} [Fact p.Prime] (G : HTGroup p) : Equivalence (Form.Rel (G := G)) := by
  have sh_mul : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
    intro a b; simp only [sh, map_mul, MulOpposite.unop_mul]
  have sh_one : sh G (1 : G.C) = 1 := by simp only [sh, map_one, MulOpposite.unop_one]
  refine ⟨fun P => ?_, fun {P Q} h => ?_, fun {P Q R} h h' => ?_⟩
  · exact ⟨1, 1, one_pos, by simp [sh_one]⟩
  · obtain ⟨y, s, hs, hβ⟩ := h
    refine ⟨y⁻¹, s⁻¹, inv_pos.mpr hs, ?_⟩
    have e : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
      rw [← sh_mul, Units.inv_mul, sh_one]
    rw [hβ]
    simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, e, mul_one,
      inv_mul_cancel₀ hs.ne', mul_inv_cancel₀ hs.ne', one_smul, Units.inv_mul_cancel_left]
  · obtain ⟨y, s, hs, hβ⟩ := h
    obtain ⟨y', s', hs', hβ'⟩ := h'
    refine ⟨y' * y, s' * s, mul_pos hs' hs, ?_⟩
    rw [hβ', hβ, Units.val_mul, sh_mul]
    simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, mul_comm s]

theorem mk_eq_iff_rel : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Form G),
    Quot.mk Form.Rel P = Quot.mk Form.Rel Q ↔ Form.Rel P Q := by
  intro p _ G P Q
  rw [← (rel_equivalence G).eqvGen_iff]
  exact ⟨Quot.eqvGen_exact, Quot.eqvGen_sound⟩

end GlobalTheory.LKCx.Form
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLimsupOfEventuallyPolynomialStatement
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankGrowthLimsup_of_eventually_polynomial : ∀ (D a : ℕ) (h : ℕ → ℕ) (H : Polynomial ℚ), 1 ≤ a → (∀ᶠ n : ℕ in atTop, (h n : ℚ) = H.eval (n : ℚ)) → (H.degree ≤ D → ∀ δ : ℕ, (δ : ℚ) = (D.factorial : ℚ) * H.coeff D → growth D (fun k => (h (a * k) : ℕ∞)) = (a : ℝ≥0∞) ^ D * δ) ∧ ((D : WithBot ℕ) < H.degree → growth D (fun k => (h (a * k) : ℕ∞)) = ⊤) := by
  first | exact @GlobalTheory.CompHt.growth_of_eventually_eq_eval | exact GlobalTheory.CompHt.growth_of_eventually_eq_eval | (intros; apply GlobalTheory.CompHt.growth_of_eventually_eq_eval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLimsupShiftLeStatement
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankGrowthLimsup_shift_le : ∀ (D e : ℕ) (r : ℕ → ℕ∞), growth D (fun k => r (k + e)) ≤ growth D r := by
  first | exact @GlobalTheory.GrowthShift.growth_shift_le | exact GlobalTheory.GrowthShift.growth_shift_le | (intros; apply GlobalTheory.GrowthShift.growth_shift_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatMuPOfRowTest
section
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open Formalism.IndefR.Rat Formalism.IndefR.Cx.CxData in

theorem ratMuP_of_rowTest : ∀ (D : D7) [IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), Formalism.IndefR.Rat.RowTest (R.toCx3 F) → R.PrincipalLevelBijective F → (R.toCx3 F).RATmu (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false := by
  intro D _ G _ _ Pl0 I0 T A3 Ks _ _ _ R F hT hH2
  obtain ⟨N, ψ, hψ, hr⟩ := hT
  obtain ⟨hinj0, hall⟩ := hH2
  intro t i k
  have hmem : (R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t (Pi.single k 1) ∈
      LinearMap.range ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false A3.A.fam.μ0) := by
    rw [← (hall t).2]; exact LinearMap.mem_range_self _ _
  have key := coord_rat _ ψ hψ ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false A3.A.fam.μ0) hinj0
    (fun j l => by rw [CxData.iC, Formalism.IndefR.Rat.lin_single]; exact hr _ _ _)
    (solve ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false A3.A.fam.μ0)
      ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t (Pi.single k 1)))
    (fun j => by rw [solve_spec _ _ hmem, CxData.iC, Formalism.IndefR.Rat.lin_single]; exact hr _ _ _) i
  obtain ⟨a, ha⟩ := key
  exact ⟨a, ha⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

namespace GlobalTheory.AdelicSvN

variable {F : Type} [Field F]

def act {R : Type} [CommRing R] [Algebra F R] {κ : Type} [Fintype κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F)
    (w : (κ → R) × (κ → R)) : (κ → R) × (κ → R) :=
  ((g.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2) ∘ Sum.inl, (g.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2) ∘ Sum.inr)

theorem act_one {R : Type} [CommRing R] [Algebra F R] {κ : Type} [Fintype κ] [DecidableEq κ]
    (w : (κ → R) × (κ → R)) : act (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) w = w := by
  have h : (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  simp only [act, h, Matrix.one_mulVec]
  rfl

theorem act_mul {R : Type} [CommRing R] [Algebra F R] {κ : Type} [Fintype κ]
    (g h : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (w : (κ → R) × (κ → R)) : act (g * h) w = act g (act h w) := by
  have e : (g * h).map (algebraMap F R) = g.map (algebraMap F R) * h.map (algebraMap F R) :=
    Matrix.map_mul (f := algebraMap F R)
  simp only [act, e, ← Matrix.mulVec_mulVec, Sum.elim_comp_inl_inr]

variable (F) in

def gens (κ : Type) [Fintype κ] [DecidableEq κ] : Set (Matrix (κ ⊕ κ) (κ ⊕ κ) F) :=
  {g | ∃ A : Matrix κ κ F, IsUnit A.det ∧ g = Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ} ∪
    {g | ∃ C : Matrix κ κ F, Cᵀ = C ∧ g = Matrix.fromBlocks 1 0 (-C) 1} ∪ {Matrix.fromBlocks 0 1 (-1) 0}

variable [NumberField F]

def Realised (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop :=
  ∃ S : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ,
    (∀ φ ∈ schA F κ, S φ ∈ schA F κ) ∧ (∀ φ ∈ schA F κ, ∃ φ' ∈ schA F κ, S φ' = φ) ∧
    (∀ l ∈ (adeleClass F).adm κ, ∃ l' ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ, l' φ = l (S φ)) ∧
    ∀ w, ∀ φ ∈ schA F κ, S (schr ψ w φ) = schr ψ (act g w) (S φ)

theorem realised_one (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] [DecidableEq κ] :
    Realised ψ (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) :=
  ⟨id, fun φ h => h, fun φ h => ⟨φ, h, rfl⟩, fun l hl => ⟨l, hl, fun _ _ => rfl⟩,
    fun w φ _ => by rw [act_one]; rfl⟩

theorem Realised.mul {ψ : AddChar (AF F) ℂ} {κ : Type} [Fintype κ] {g h : Matrix (κ ⊕ κ) (κ ⊕ κ) F}
    (hg : Realised ψ g) (hh : Realised ψ h) : Realised ψ (g * h) := by
  obtain ⟨S, hS, hSs, hSa, hSi⟩ := hg
  obtain ⟨T, hT, hTs, hTa, hTi⟩ := hh
  refine ⟨S ∘ T, fun φ hφ => hS _ (hT φ hφ), fun φ hφ => ?_, fun l hl => ?_, fun w φ hφ => ?_⟩
  · obtain ⟨φ₁, h₁, rfl⟩ := hSs φ hφ
    obtain ⟨φ₂, h₂, rfl⟩ := hTs φ₁ h₁
    exact ⟨φ₂, h₂, rfl⟩
  · obtain ⟨l₁, hl₁, e₁⟩ := hSa l hl
    obtain ⟨l₂, hl₂, e₂⟩ := hTa l₁ hl₁
    exact ⟨l₂, hl₂, fun φ hφ => (e₂ φ hφ).trans (e₁ _ (hT φ hφ))⟩
  · simp only [Function.comp_apply]
    rw [hTi w φ hφ, hSi _ _ (hT φ hφ), act_mul]

end GlobalTheory.AdelicSvN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularElementSeparableMinpoly
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx

theorem commute_units_conj {A : Type*} [Monoid A] (U : Aˣ) {a e : A} (h : Commute a e) :
    Commute ((U : A) * a * ↑U⁻¹) ((U : A) * e * ↑U⁻¹) := by
  unfold Commute SemiconjBy at *
  calc (U : A) * a * ↑U⁻¹ * ((U : A) * e * ↑U⁻¹) = U * (a * e) * ↑U⁻¹ := by
        simp only [mul_assoc, Units.inv_mul_cancel_left]
    _ = U * (e * a) * ↑U⁻¹ := by rw [h]
    _ = _ := by simp only [mul_assoc, Units.inv_mul_cancel_left]

theorem comm_of_conj {A : Type*} [Monoid A] (U : Aˣ) (e : A)
    (h : ∀ a b : A, Commute a ((U : A) * e * ↑U⁻¹) → Commute b ((U : A) * e * ↑U⁻¹) → Commute a b)
    (a b : A) (ha : Commute a e) (hb : Commute b e) : Commute a b := by
  have h1 := h _ _ (commute_units_conj U ha) (commute_units_conj U hb)
  have h2 := commute_units_conj U⁻¹ h1
  have e1 : ∀ z : A, ((U⁻¹ : Aˣ) : A) * ((U : A) * z * ↑U⁻¹) * ↑(U⁻¹)⁻¹ = z := by
    intro z; simp [mul_assoc]
  rwa [e1, e1] at h2

variable {p : ℕ} [Fact p.Prime]

theorem ubc_val_eq (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t)
    (y : grp G β) (h : G.GAf) (w : AwayP p) :
    ∃ U : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
    ((ubcMap (AfP.eval w) (h⁻¹ * toAfF G β x t hx y * h)).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
      (U : w.1.adicCompletion ℚ ⊗[ℚ] G.C) * ((1 : w.1.adicCompletion ℚ) ⊗ₜ (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) *
        ((U⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
  set φ : AfP p ⊗[ℚ] G.C →ₐ[ℚ] w.1.adicCompletion ℚ ⊗[ℚ] G.C :=
    Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) with hφ
  have hm : ((ubcMap (AfP.eval w) (toAfF G β x t hx y)).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
      φ x * ((1 : w.1.adicCompletion ℚ) ⊗ₜ (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * φ ↑x⁻¹ := by
    show φ ((x : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ↑x⁻¹) = _
    rw [map_mul, map_mul]
    congr 2
  refine ⟨((ubcMap (AfP.eval w) h).1.1)⁻¹ * Units.map φ.toMonoidHom x, ?_⟩
  rw [map_mul, map_mul, map_inv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv, Units.val_mul, _root_.mul_inv_rev, inv_inv]
  rw [hm]
  simp only [Units.coe_map, MonoidHom.coe_coe, mul_assoc]
  rw [Units.coe_map_inv]
  rfl

end GlobalTheory.LKCx

namespace GlobalTheory.LKCx

end GlobalTheory.LKCx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularFunctionsPthPowerTwist
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

open CategoryTheory AlgebraicGeometry TopologicalSpace in

theorem _root_.GlobalTheory.DI.pow_mul_locRing_subset_regularAt {X : Scheme.{0}} [IsIntegral X] (p : ℕ)
    (G H : _root_.GlobalTheory.Cartier.CartierDiv X) (y : X) (h : (H - p • G).Eff) :
    {z : X.functionField | ∃ c ∈ {c : X.functionField | G.RegularAt y c},
      ∃ b ∈ _root_.GlobalTheory.LogDR.locRing y, z = c ^ p * b} ⊆
      {c | H.RegularAt y c} := by
  rintro z ⟨c, ⟨g, hg, hcg⟩, b, hb, rfl⟩
  obtain ⟨k, hk, hk1⟩ := h y
  have hH : H.IsEqn y (k * g ^ p) := by
    have := hk.add (hg.nsmul p)
    simpa using this
  refine ⟨k * g ^ p, hH, ?_⟩
  rw [← _root_.GlobalTheory.LogDR.mem_locRing] at hcg hk1 ⊢
  have hz : c ^ p * b * ((k * g ^ p : (X.functionField)ˣ) : X.functionField) =
      (c * g) ^ p * b * (1 * k) := by
    push_cast
    ring
  rw [hz]
  exact mul_mem (mul_mem (pow_mem hcg p) hb) hk1

end GlobalTheory.DI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularSectionExtendsOverFibre
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.PropZCore

theorem unitAt_zpow {X : Scheme.{0}} [IsIntegral X] {x : X} {g : X.functionField} (h : UnitAt x g)
    (n : ℤ) : UnitAt x (g ^ n) := by
  have hp : ∀ m : ℕ, UnitAt x (g ^ m) := by
    intro m
    induction m with
    | zero => rw [pow_zero]; exact unitAt_one x
    | succ m ih => rw [pow_succ]; exact ih.mul h
  rcases n with m | m
  · rw [Int.ofNat_eq_coe, zpow_natCast]; exact hp m
  · rw [zpow_negSucc]; exact (hp _).inv

theorem gen_of_exponent : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ Spec (.of O)) (D : LB Z), Hyp f D → genericPoint Z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) →
  IsField Γ(reducedSpecialFibre f, ⊤) →
  (∀ (φ : Z.functionField) (x : Z),
    (∀ z : Z, z ⤳ x → IsDiscreteValuationRing (Z.presheaf.stalk z) → RegAt z φ) → RegAt x φ) →
  ∀ τ : D.ι → Z.functionFieldˣ, IsRatSec D τ →
  (∀ (i : D.ι) (z : Z), z ∈ D.U i → z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) → UnitAt z (τ i : Z.functionField)) →
  ∀ (M : ℕ) (n : ℤ) (x₀ : Z), 1 ≤ M → x₀ ∉ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) →
  (∀ (i : D.ι) (z : Z), z ∈ D.U i → IsDiscreteValuationRing (Z.presheaf.stalk z) →
    RegAt z (fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n * ((τ i : Z.functionField) ^ M)⁻¹)) →
  (∀ i : D.ι, x₀ ∈ D.U i → UnitAt x₀ (fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n * ((τ i : Z.functionField) ^ M)⁻¹)) →
  ∃ gen : (lbPow D M).Gen, gen.IsGen ∧
    ∀ (i : D.ι) (h : genericPoint Z ∈ D.U i),
      fnOf ((lbPow D M).U i) h (gen.s i).1 * fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n = (τ i : Z.functionField) ^ M := by
  have L1 := GlobalTheory.T.exists_reduced_fibre_point
  have L2 := GlobalTheory.T.exists_global_section_unit_stalk
  intro O _ _ _ ϖ hϖ Z _ f D hD hgen hfield hhart τ hτ hτu M n x₀ hM hx₀ hreg hunit
  set π := f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ) with hπ
  set P : Z.functionField := fnOf ⊤ trivial π with hP
  have hDLB : D.IsLB := hD.2.2.2.2.2.1
  obtain ⟨t, ht⟩ := hD.2.2.2.2.2.2
  obtain ⟨φ, hφ⟩ : ∃ φ : D.ι → Z.functionField, ∀ i, φ i = P ^ n * ((τ i : Z.functionField) ^ M)⁻¹ :=
    ⟨_, fun _ => rfl⟩
  have hregU : ∀ i, ∀ z ∈ D.U i, RegAt z (φ i) := fun i z hz =>
    hhart _ z fun z' hz' hdvr => hφ i ▸ hreg i z' (hz'.mem_open (D.U i).isOpen hz) hdvr
  have ha : ∀ i, ∃ a : Γ(Z, D.U i), ∀ h, fnOf (D.U i) h a = φ i := by
    intro i
    by_cases h : genericPoint Z ∈ D.U i
    · obtain ⟨a, ha⟩ := exists_fnOf_eq h (hregU i)
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h' => (h h').elim⟩
  choose a ha using ha
  have hgne : ∀ i j (h : genericPoint Z ∈ D.U i ⊓ D.U j),
      fnOf _ h (D.g i j : Γ(Z, D.U i ⊓ D.U j)) ≠ 0 := fun i j h =>
    ((D.g i j).isUnit.map (fnOf _ h)).ne_zero
  have hφg : ∀ i j (h : genericPoint Z ∈ D.U i ⊓ D.U j),
      φ i * (fnOf _ h (D.g i j : Γ(Z, D.U i ⊓ D.U j))) ^ M = φ j := by
    intro i j h
    have e := hτ i j h
    have h1 := hgne i j h
    rw [hφ, hφ, e, mul_pow, mul_inv, mul_comm (((fnOf _ h _) ^ M)⁻¹), mul_assoc, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ h1), mul_one]
  have key : ∀ i j (h : genericPoint Z ∈ D.U i ⊓ D.U j),
      (φ i)⁻¹ = (fnOf _ h (D.g i j : Γ(Z, D.U i ⊓ D.U j))) ^ M * (φ j)⁻¹ := by
    intro i j h
    rw [← hφg i j h, mul_inv (φ i), mul_left_comm (_ ^ M) (φ i)⁻¹,
      mul_inv_cancel₀ (pow_ne_zero _ (hgne i j h)), mul_one]
  have hcompat : ∀ i j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG Z (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) (a i) *
      ((D.g i j : Γ(Z, D.U i ⊓ D.U j))) ^ M =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG Z (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) (a j) := by
    intro i j
    apply fn_ext
    intro h
    rw [map_mul, map_pow, fnOf_resG, fnOf_resG, ha, ha, hφg]
  obtain ⟨hh, hhu⟩ := L2 _ _ (reducedSpecialι f) D hDLB t ht M a hcompat
  have germUnit : ∀ i (z : Z) (hz : z ∈ D.U i), UnitAt z (φ i) ↔
      IsUnit ((Z.presheaf.germ (D.U i) z hz).hom (a i)) := by
    intro i z hz
    rw [← ha i (gen_mem hz), unitAt_fnOf_iff hz, Z.mem_basicOpen (a i) z hz]
  obtain ⟨i₀, hi₀⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hDLB x₀
  have hne : hh ≠ 0 := by
    intro h0
    obtain ⟨y₀, rfl⟩ := L1 O ϖ hϖ Z f x₀ hx₀
    obtain ⟨u, hu⟩ := hhu i₀ y₀ hi₀
    have h1 := ((germUnit i₀ _ hi₀).1 (hφ i₀ ▸ hunit i₀ hi₀)).map ((reducedSpecialι f).stalkMap y₀).hom
    have h2 := h1.mul u.isUnit
    rw [← hu, h0, map_zero] at h2
    exact not_isUnit_zero h2
  have hhunit : IsUnit hh := by
    obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hne
    exact IsUnit.of_mul_eq_one b hb
  have hspecial : ∀ i (z : Z) (hz : z ∈ D.U i), z ∉ Z.basicOpen π → UnitAt z (φ i) := by
    intro i z hz hzπ
    obtain ⟨y, rfl⟩ := L1 O ϖ hϖ Z f z hzπ
    obtain ⟨u, hu⟩ := hhu i y hz
    have h1 := hhunit.map ((reducedSpecialFibre f).presheaf.germ ⊤ y trivial).hom
    rw [hu] at h1
    have h2 := h1.mul (u⁻¹).isUnit
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one] at h2
    have : IsLocalHom ((reducedSpecialι f).stalkMap y).hom := inferInstance
    exact (germUnit i _ hz).2 (isUnit_of_map_unit _ _ h2)
  have hgenU : UnitAt (genericPoint Z) P := (unitAt_fnOf_iff (U := ⊤) trivial trivial π).2 hgen
  have hPne : P ≠ 0 := hgenU.ne_zero
  have hall : ∀ i, ∀ z ∈ D.U i, UnitAt z (φ i)⁻¹ := by
    intro i z hz
    refine UnitAt.inv ?_
    by_cases hzπ : z ∈ Z.basicOpen π
    · have h3 := unitAt_zpow (hτu i z hz hzπ) M
      rw [zpow_natCast] at h3
      rw [hφ]
      exact (unitAt_zpow ((unitAt_fnOf_iff (U := ⊤) trivial trivial π).2 hzπ) n).mul h3.inv
    · exact hspecial i z hz hzπ
  choose u hu using fun i => exists_unit_fnOf_eq (hall i)
  refine ⟨⟨u⟩, fun i j => ?_, fun i h => ?_⟩
  · apply Units.ext
    apply fn_ext
    intro h
    have h' : genericPoint Z ∈ D.U i ⊓ D.U j := h
    change fnOf (D.U i ⊓ D.U j) h' ((res (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) (u i) : Γ(Z, D.U i ⊓ D.U j)ˣ) : Γ(Z, D.U i ⊓ D.U j)) =
      fnOf (D.U i ⊓ D.U j) h' (((D.g i j ^ M) * res (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) (u j) : Γ(Z, D.U i ⊓ D.U j)ˣ) : Γ(Z, D.U i ⊓ D.U j))
    rw [Units.val_mul, Units.val_pow_eq_pow_val, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, map_mul, map_pow]
    erw [fnOf_resG, fnOf_resG, hu, hu]
    exact key i j h'
  · change fnOf _ h (u i : Γ(Z, D.U i)) * P ^ n = _
    rw [hu, hφ, mul_inv, inv_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ hPne), one_mul]

end GlobalTheory.PropZCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularWeightsOfGapTwo
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct

namespace GlobalTheory.GapRegular

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Sep (S : SPar) : Prop := ∀ x ∈ S, ∀ y ∈ S, y.1 < x.1 → y.1 + 2 ≤ x.1

theorem Sep.dual {S : SPar} (h : Sep S) : Sep (dualPar S) := by
  intro x hx y hy hxy
  obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hy
  have := h y' hy' x' hx' (by simpa using hxy)
  simp only
  linarith

end GlobalTheory.GapRegular

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroCentralizerParabolicCosetStabilizeStatement
section
open MeasureTheory Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_ne_zero_centralizer_parabolicCosetStabilizer : ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b) (γ : GL ι K),
  GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) γ ≤ GlobalTheory.OrbDesc.blockLevi e →
  ∀ K' : Subgroup (GL ι K), IsOpen (K' : Set (GL ι K)) → IsCompact (K' : Set (GL ι K)) →
  ∀ x ∈ GlobalTheory.OrbDesc.blockPar e,
    (GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) γ ⊓ (GlobalTheory.OrbDesc.blockPar e ⊓ K').map (MulAut.conj x).toMonoidHom).relIndex
      (GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) γ ⊓
        ((GlobalTheory.OrbDesc.blockPar e ⊓ K') ⊔ GlobalTheory.OrbDesc.blockUni e).map (MulAut.conj x).toMonoidHom) ≠ 0 := by
  first | (exact @GlobalTheory.OrbDesc.StabIndex.relIndex_twCent_inf_ne_zero) | (exact GlobalTheory.OrbDesc.StabIndex.relIndex_twCent_inf_ne_zero) | (intros; apply GlobalTheory.OrbDesc.StabIndex.relIndex_twCent_inf_ne_zero  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelOfConjInGroupOfCommonForm
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.RelConj

theorem rel_of_conj_in_form : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P P' : Pair G) (B y y' g : G.Cˣ) (s s' sg : ℚ), 0 < s → 0 < s' → 0 < sg → (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y) → (P'.β : G.C) = algebraMap ℚ G.C s' * (y' * B * sh G y') → (g : G.C) * B * sh G g = algebraMap ℚ G.C sg * B → g * (y⁻¹ * P.γ * y) * g⁻¹ = y'⁻¹ * P'.γ * y' → P.Rel P' := by
  intro p _ G P P' B y y' g s s' sg hs hs' hsg hβ hβ' hg hγ
  have shm : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := fun a b => by simp [sh]
  have hyi : ((y⁻¹ : G.Cˣ) : G.C) * y = 1 := Units.inv_mul y
  have hshy : sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
    rw [← shm, hyi]; simp [sh]
  have key : ((y' * g * y⁻¹ : G.Cˣ) : G.C) * P.β * sh G ((y' * g * y⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C (s * sg) * (y' * B * sh G y') := by
    rw [hβ, Units.val_mul, Units.val_mul, shm, shm, ← Algebra.smul_def]
    calc (y' : G.C) * g * ((y⁻¹ : G.Cˣ) : G.C) * (s • ((y : G.C) * B * sh G y)) *
          (sh G ((y⁻¹ : G.Cˣ) : G.C) * (sh G g * sh G y'))
        = s • ((y' : G.C) * (g * (((y⁻¹ : G.Cˣ) : G.C) * y) * B * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C)) * sh G g) * sh G y') := by
          simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
      _ = s • ((y' : G.C) * ((g : G.C) * B * sh G g) * sh G y') := by
          rw [hyi, hshy, mul_one, mul_one]
      _ = s • (sg • ((y' : G.C) * B * sh G y')) := by
          rw [hg, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
      _ = _ := by rw [smul_smul, Algebra.smul_def]
  refine ⟨y' * g * y⁻¹, s' / (s * sg), div_pos hs' (mul_pos hs hsg), ?_, ?_⟩
  · rw [key, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ (mul_pos hs hsg).ne', hβ']
  · have e : P'.γ = y' * (y'⁻¹ * P'.γ * y') * y'⁻¹ := by group
    rw [e, ← hγ]; group

end GlobalTheory.RelConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatedPairsSamePolarizationStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.related_pairs_same_polarization : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G), P.Rel Q → Q.pol = P.pol ∧ Q.c = P.c := by
  first | (exact @GlobalTheory.LKMid.Pair.rel_pol_c) | (exact GlobalTheory.LKMid.Pair.rel_pol_c) | (intros; apply GlobalTheory.LKMid.Pair.rel_pol_c  <;> assumption)
end

