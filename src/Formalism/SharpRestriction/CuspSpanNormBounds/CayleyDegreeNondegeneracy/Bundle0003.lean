import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NcardPrimesOverOfSplitsCompl
import Formalism.FlagUnipotentLattices.Bundle0006
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.IsPositiveDefiniteForm
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenusOrthonormalIntegralUnimodular
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0001
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyPacketOfEquivalentStatement

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ForPrimeFlagLattice
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ForPrimeFlagLattice (D : D7) (u : D.what₂.Word)
    (Q : (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) → LatV D → Prop) : Prop :=
  (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → Q F0 Λ

def BaseLatticeStructure (D : D7) (u : D.what₂.Word) : Prop :=
  ForPrimeFlagLattice D u fun F0 Λ =>
    Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)) ∧
    Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT (L0X D Λ (lf D F0)) ∧
    latDetH (D.sp.X 0).hT (L0X D Λ (lf D F0)) = ((Tu D u ^ D.R.f : ℕ) : ℝ) ∧
    DiscGen (D.sp.X 0).hT (L0X D Λ (lf D F0)) 1 ∧
    ∀ p : Ideal (𝓞 D.host.F), p.IsMaximal → ((Tu D u : ℕ) : 𝓞 D.host.F) ∈ p →
      eP (D.sp.X 0).hT (L0X D Λ (lf D F0)) p = 1

def BaseLatticeLevel (D : D7) (u : D.what₂.Word) : Prop :=
  ForPrimeFlagLattice D u fun F0 Λ =>
    levelIdx (D.sp.X 0).hT (L0X D Λ (lf D F0)) (Tu D u ^ D.R.f) = (Tu D u - 1) ^ D.R.f

def WordRowsGluing (D : D7) (u : D.what₂.Word) : Prop :=
  ForPrimeFlagLattice D u fun F0 Λ => ∀ s : Finset (LatV D), IsRowReps D F0 s →
    massRows D F0 s = Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ (lf D F0)) * ((Tu D u : ℝ) - 1) ^ D.R.f

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.HypothesesNumericalConsequences
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal

section Frame

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mass_eq_sum_inv_aut_card (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (s : Finset (Submodule (𝓞 K) V))
    (hs : Formalism.ThetaLiftIndependence.IsClassReps h L s) :
    Formalism.HermitianLatticesTheory.mass h L = ∑ M ∈ s, ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ := by
  have hex : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s := ⟨s, hs⟩
  rw [Formalism.HermitianLatticesTheory.massBasic_mass_eq h L hex]
  apply Complex.ofReal_injective
  rw [Formalism.HermitianLatticesTheory.massBasic_sum_cast, Formalism.HermitianLatticesTheory.massBasic_sum_cast]
  exact Formalism.ThetaLiftIndependence.latLiftIndep K V h L _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) _ _ hex.choose_spec hs

end Frame

section Rec

variable (D : D7) (large₂ : SizeData₂ D)

end Rec

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.PlaneMassBoundOfFacts
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.HermitianLatticesTheory

def SecondOrthogonalVector (K : Type) [Field K] [NumberField K] [StarRing K] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V), h.IsSymm → IsOrthoLattice h L 2 →
    ∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M → IsIntegralLat h M → dual h M = M →
    ∀ x ∈ M, x ≠ 0 → ∃ y ∈ M, y ≠ 0 ∧ h x y = 0 ∧ ∀ φ : K →+* ℂ, ‖φ (h y y)‖ ≤ ‖φ (h x x)‖ * rootDiscriminant K

def PlaneClassCount (K : Type) [Field K] [NumberField K] [StarRing K] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V), h.IsSymm → IsOrthoLattice h L 2 →
    ∀ s : Finset (Submodule (𝓞 K) V), Formalism.ThetaLiftIndependence.IsClassReps h L s → ∀ B₁ B₂ : ℝ,
    (∀ M ∈ s, IsIntegralLat h M) →
    (∀ M ∈ s, ∃ x ∈ M, ∃ y ∈ M, x ≠ 0 ∧ y ≠ 0 ∧ h x y = 0 ∧
      ∀ φ : K →+* ℂ, ‖φ (h x x)‖ ≤ B₁ ∧ ‖φ (h y y)‖ ≤ B₂) →
    (s.card : ℝ) ≤ (1 + 2 * B₁) ^ (2 * finrank ℚ K) * (1 + 2 * B₂) ^ (2 * finrank ℚ K) *
      (B₁ * B₂) ^ (4 * finrank ℚ K)

theorem card_class_reps_plane_le (K : Type) [Field K] [NumberField K] [StarRing K] (B₁ : ℝ)
    (hA : ShortVectorEveryPlace K B₁) (hB : SecondOrthogonalVector K) (hC : PlaneClassCount K) (hrd : 0 ≤ rootDiscriminant K)
    (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (hs : h.IsSymm) (hL : IsOrthoLattice h L 2)
    (s : Finset (Submodule (𝓞 K) V)) (hreps : Formalism.ThetaLiftIndependence.IsClassReps h L s) :
    (s.card : ℝ) ≤ (1 + 2 * B₁) ^ (2 * finrank ℚ K) * (1 + 2 * (B₁ * rootDiscriminant K)) ^ (2 * finrank ℚ K) *
      (B₁ * (B₁ * rootDiscriminant K)) ^ (4 * finrank ℚ K) := by
  refine hC V h L hs hL s hreps B₁ (B₁ * rootDiscriminant K)
    (fun M hM => (genus_orthonormal_integral_unimodular h hs L hL M (hreps.1 M hM)).1) fun M hM => ?_
  have hg := hreps.1 M hM
  obtain ⟨hint, huni⟩ := genus_orthonormal_integral_unimodular h hs L hL M hg
  obtain ⟨x, hx, hx0, hxB⟩ := hA V h L hs hL M hg
  obtain ⟨y, hy, hy0, hxy, hyB⟩ := hB V h L hs hL M hg.1 hint huni x hx hx0
  exact ⟨x, hx, y, hy, hx0, hy0, hxy, fun φ =>
    ⟨hxB φ, (hyB φ).trans (mul_le_mul_of_nonneg_right (hxB φ) hrd)⟩⟩

end Formalism.MainNotions.BridgeLemma₂

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem plane_mass_bound_of_facts (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C B₁ : ℝ)
    (hA : ShortVectorEveryPlace D.host.E B₁) (hB : SecondOrthogonalVector D.host.E) (hCt : PlaneClassCount D.host.E)
    (hB0 : 0 ≤ B₁) (hB1 : B₁ ≤ 4 * D.R.f * D.host.rdE) (hC : 55 * max 1 (1 / Cl) ≤ C ^ 2)
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) : UnitaryVolumeMass.Mass2At D large₂ C := by
  intro V _ _ _ _ h L hs ho
  obtain ⟨-, -, h3, -, h5, -, -, -, -, -, h11, -, -, -, -, -, -, -, h19, -⟩ := hH
  have hm := D.R.two_le_m
  have hf : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) h3
  have hL1 : 1 ≤ large₂.sc.L := by
    unfold Scale.L
    exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hrd : 2 ≤ D.host.rdE := by
    have e : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
    rw [← e]; linarith
  have hlrd : Real.log D.host.rdE ≤ max 1 (1 / Cl) * large₂.sc.L := by
    refine le_trans h11 ?_
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
  have hlf : Real.log (D.R.f : ℝ) ≤ (D.R.m : ℝ) := by
    refine le_trans h5 ?_
    rw [Real.sqrt_le_left (by positivity)]
    have h1 : D.R.rS ≤ D.R.m := by unfold Ranks.rS; omega
    have h2 : (D.R.rS : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast h1
    have h3 : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast hm
    nlinarith
  have hrdE : rootDiscriminant D.host.E = D.host.rdE := rfl
  have hnum := mass_pow_le_exp_rpow D.R.f D.R.m D.host.rdE large₂.sc.L B₁ C (max 1 (1 / Cl)) hf hm hrd hL1 (le_max_left _ _) hlf hlrd hB0 hB1 hC
  have hb : large₂.sc.b = Real.exp large₂.sc.L := rfl
  rw [hb]
  refine mass_le_of_card_class_reps_le h L _ (by positivity) fun s hreps => ?_
  have hc := card_class_reps_plane_le D.host.E B₁ hA hB hCt (by rw [hrdE]; linarith) V h L hs ho s hreps
  rw [hrdE, Formalism.MainNotions.StandardLattice.finrank_host] at hc
  exact hc.trans hnum

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.PrimitiveMeanOverWords
section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Def

variable (D : D7)

abbrev LatticeW : Type := Submodule (𝓞 D.host.E) (D.sp.X 0).V

def latticeTraceOnW {T : D.host.E} (F : LFlag (hS D) D.R.rS T) (A : LatV D) : LatticeW D :=
  (A ⊔ toO (hS D) (Xsp F)).comap ((D.sp.iXY 0).restrictScalars (𝓞 D.host.E))

def sublatticeIndex' (A B : LatticeW D) : ℕ := Nat.card (A ⧸ B.comap A.subtype)

def latticeRank (P : LatticeW D) : ℕ := finrank D.host.E (Submodule.span D.host.E (P : Set (D.sp.X 0).V))

def latticeSaturation (L0 P : LatticeW D) : LatticeW D :=
  L0 ⊓ (Submodule.span D.host.E (P : Set (D.sp.X 0).V)).restrictScalars (𝓞 D.host.E)

abbrev latticeDetW (P : LatticeW D) : ℝ := latDetH (D.sp.X 0).hT P

def sublatticeQuadruples (L0 : LatticeW D) (s : ℕ) (De : ℝ) : Set (LatticeW D × LatticeW D × LatticeW D × LatticeW D) :=
  {q | IsPrimitiveSub q.1 L0 ∧ latticeRank D q.1 = D.R.k - s ∧ q.2.1 ≤ q.1 ∧ q.2.2.1 ≤ q.2.1 ∧ q.2.2.2 ≤ q.2.1 ∧
    sublatticeIndex' D q.1 q.2.1 ≠ 0 ∧ sublatticeIndex' D q.2.1 q.2.2.1 ≠ 0 ∧ sublatticeIndex' D q.2.1 q.2.2.2 ≠ 0 ∧
    latticeDetW D q.1 * sublatticeIndex' D q.1 q.2.1 * sublatticeIndex' D q.2.1 q.2.2.1 * sublatticeIndex' D q.2.1 q.2.2.2 ≤ De ∧
    latticeRank D q.2.2.1 = D.R.k - s ∧ latticeRank D q.2.2.2 = D.R.k - s ∧ latticeDetW D q.2.2.1 ≤ De ∧ latticeDetW D q.2.2.2 ≤ De}

def quadrupleOfTriple (Λ : LatV D) {T T' : D.host.E} (F : LFlag (hS D) D.R.rS T) (p : Trip D T') :
    LatticeW D × LatticeW D × LatticeW D × LatticeW D :=
  (latticeSaturation D (L0X D Λ F) (latticeTraceOnW D F (Mlat Λ F p.1 p.2.1 p.2.2 (gS D))),
    latticeTraceOnW D F (Mlat Λ F p.1 p.2.1 p.2.2 (gS D)),
    latticeTraceOnW D F (Mlat Λ F p.1 p.2.1 p.2.2 (gS D)) ⊓ latticeTraceOnW D F (Thp Λ F p.1),
    latticeTraceOnW D F (Mlat Λ F p.1 p.2.1 p.2.2 (gS D)) ⊓ latticeTraceOnW D F (Thp Λ F p.2.1))

def termsOverSublattice (Λ : LatV D) {T : D.host.E} (T' : D.host.E) (F : LFlag (hS D) D.R.rS T) (Z : GramM D)
    (P : LatticeW D) : Set (LFlag (hS D) D.R.rS T') :=
  {F' | IsTermF D Λ F F' ∧ ZEquiv (ZhatL F F') Z ∧ P ≤ latticeTraceOnW D F (Thp Λ F F')}

def positionCount (r f s : ℕ) (NT De Hh : ℝ) : ℝ :=
  NT ^ (2 * r) * De ^ r * 9 ^ (s * f) * Hh ^ (9 * s + 9 * s * r + 16 * r ^ 2)

variable (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def QuadrupleMembership (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ (Z' Z'' : GramM D) (s : ℕ) (De : ℝ), 1 ≤ s →
  ∀ p ∈ PairSet D Λ ((Tu D u' : ℕ) : D.host.E) (lf D F0) Z' Z'' s De,
    quadrupleOfTriple D Λ (lf D F0) p ∈ sublatticeQuadruples D (L0X D Λ (lf D F0)) s De

def TermPositionCount (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ Z : GramM D, RelZ D Z → ∀ s : ℕ, 1 ≤ s → s ≤ D.R.k →
  ∀ P : LatticeW D, P ≤ L0X D Λ (lf D F0) → latticeRank D P = D.R.k - s →
  ∀ De Hh : ℝ, 1 ≤ De → latticeDetW D P ≤ De → HHZ D large₂.sc.b C Z ≤ Hh → De ≤ Hh ^ 3 →
    (cntCl (termsOverSublattice D Λ ((Tu D u' : ℕ) : D.host.E) (lf D F0) Z P) (TEqv D Λ (lf D F0)) : ℝ≥0∞) ≤
      ENNReal.ofReal (positionCount D.R.rS D.R.f s (NT D u) De Hh)

def PairsModuloNormCount (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ (Z' Z'' : GramM D) (s : ℕ) (De : ℝ), 1 ≤ s →
  ∀ p₀ ∈ PairSet D Λ ((Tu D u' : ℕ) : D.host.E) (lf D F0) Z' Z'' s De,
    (cntCl {p | p ∈ PairSet D Λ ((Tu D u' : ℕ) : D.host.E) (lf D F0) Z' Z'' s De ∧
        TEqv D Λ (lf D F0) p₀.1 p.1 ∧ TEqv D Λ (lf D F0) p₀.2.1 p.2.1} (PEqv D Λ (lf D F0)) : ℝ≥0∞) ≤
      (((4 * D.R.f * s).factorial : ℕ) : ℝ≥0∞)

def PairsFibreCount (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ Z' Z'' : GramM D, RelZ D Z' → RelZ D Z'' → ∀ s : ℕ, 2 ≤ s → s ≤ D.R.k →
  ∀ De Hh : ℝ, 1 ≤ De → HHZ D large₂.sc.b C Z' * HHZ D large₂.sc.b C Z'' ≤ Hh → De ≤ Hh ^ 3 →
    (cntPairs D Λ ((Tu D u' : ℕ) : D.host.E) (lf D F0) Z' Z'' s De : ℝ≥0∞) ≤
      ((sublatticeQuadruples D (L0X D Λ (lf D F0)) s De).encard : ℝ≥0∞) *
        ENNReal.ofReal (positionCount D.R.rS D.R.f s (NT D u) De Hh ^ 2 * ((4 * D.R.f * s).factorial : ℝ))

def QuadrupleMeanBound (C' Cl Cg cb Cu cT CT C0 A A1 : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ what₂ : Finset (LatV D), IsRowReps D F0 what₂ → ∀ s : ℕ, 2 ≤ s → s ≤ D.R.k → ∀ De : ℝ, 1 ≤ De →
  ∀ HH : ℝ, Hb large₂.sc.b A1 D.R.m D.R.f ≤ HH →
    MeanLe D F0 what₂ (fun Λ => (sublatticeQuadruples D (L0X D Λ (lf D F0)) s De).encard)
      ((De / NT D u) ^ D.R.k * (De * NT D u) ^ (A1 * ((s : ℝ) + cF D.R.f)) * De ^ (cF D.R.f + 4) * XiS D u HH A1 s)

def PrimitiveMeanOverWords (C' Cl Cg cb Cu cT CT C0 A A1 : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ what₂ : Finset (LatV D), IsRowReps D F0 what₂ → ∀ s : ℕ, 2 ≤ s → s ≤ D.R.k → ∀ de : ℕ, 1 ≤ de →
  ∀ HH : ℝ, Hb large₂.sc.b A1 D.R.m D.R.f ≤ HH →
    MeanLe D F0 what₂ (fun Λ => cntPrim (D.sp.X 0).hT (L0X D Λ (lf D F0)) (D.R.k - s) de)
      (((de : ℝ) / NT D u) ^ D.R.k * ((de : ℝ) * NT D u) ^ (A1 * s + A1 * Real.log D.R.f) * XiS D u HH A1 s)

def MeanOverWordsEqGenus : Prop :=
  (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ what₂ : Finset (LatV D), IsRowReps D F0 what₂ → ∀ Λ₀ : LatV D, IsRowLat D F0 Λ₀ →
  ∀ reps : Finset (LatticeW D), Formalism.ThetaLiftIndependence.IsClassReps (D.sp.X 0).hT (L0X D Λ₀ (lf D F0)) reps →
  ∀ N : LatticeW D → ℕ∞, (∀ γ ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ L, N (Formalism.HermitianLatticesTheory.gmap γ L) = N L) →
    (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * (N (L0X D Λ (lf D F0)) : ℝ≥0∞)) *
        ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ₀ (lf D F0))) =
      (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) *
        ∑ L' ∈ reps, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℝ))⁻¹ * (N L' : ℝ≥0∞)

def GramDeterminantIsNatural : Prop :=
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ M : LatticeW D, M ≤ L0X D Λ (lf D F0) →
    ∃ de : ℕ, 1 ≤ de ∧ latticeDetW D M = de

end Def

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsDef
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7}

abbrev termGramMatrix (X : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u') : GramM D := ZhatL (X.fl t) (X.fl' t)

def wordPairGramNorm (D : D7) (u u' : D.what₂.Word) (Z : GramM D) : ℝ := ∏ τ, nV D (Tu D u) (Tu D u') Z τ

def wordPairGramProduct (D : D7) (u u' : D.what₂.Word) (Z : GramM D) : ℝ :=
  (∏ τ, Gz D (Tu D u) (Tu D u') Z τ) * ((gS D : ℝ)⁻¹) ^ (D.R.m * D.R.f)

def pairDeterminant (X : TermTie D) {u u' : D.what₂.Word} (p : D.s.Pair u u') : ℝ :=
  latDet (hS D) (Mlat (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) (X.fl' (D.s.psnd p)) (X.beta p) (gS D)) *
    (iIdx (X.abelian₂ (D.s.pfst p)) (gS D) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) : ℝ) *
    (iIdx (X.abelian₂ (D.s.pfst p)) (gS D) (X.fl (D.s.pfst p)) (X.fl' (D.s.psnd p)) : ℝ)

def wordPairDeterminantGeOne (X : TermTie D) (u u' : D.what₂.Word) : Prop :=
  ∀ p : D.s.Pair u u', D.s.Gterm (D.s.pfst p) ≠ 0 → D.s.Gterm (D.s.psnd p) ≠ 0 → 1 ≤ pairDeterminant X p

def wordPairEntriesInLattice (X : TermTie D) (u u' : D.what₂.Word) : Prop :=
  ∀ a b : Fin (D.R.rS + 1), ∃ Λ : AddSubgroup (D.what₂.Tau → ℂ), (∀ x ∈ Λ, x ≠ 0 → 1 ≤ ∏ v, ‖x v‖) ∧
    ∀ (t : D.s.Term u u') (Z : GramM D), D.s.Gterm t ≠ 0 → D.s.relevant t → ZEquiv (termGramMatrix X t) Z →
      (fun τ => ((rhoF D a * rhoF D b : ℝ) : ℂ) * embS D τ (Z a b)) ∈ Λ

end Defs

end Formalism.MainNotions.BridgeLemma₂

end
end

