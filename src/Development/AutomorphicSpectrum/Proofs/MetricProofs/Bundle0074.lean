import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0021
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0030
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0073
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0098
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0033
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0095
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0025
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0069
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetCuspFramePlurisubharmonic
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogIndexOfOrthogonalFamily
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameLeadingTerm
section
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX

section Pure

variable {Ψ : Type} [Fintype Ψ] {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
  {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]

def segIxEquiv : ((k : K₀ ⊕ StepIx Ψ p q) → idx (p := p) (q := q) J₀ n k) ≃
    FlagIx ((k : K₀) → J₀ k) n (rk Ψ p q) :=
  Equiv.sumPiEquivProdPi (idx (p := p) (q := q) J₀ n)

end Pure

end GlobalTheory.CompanionTheory.Ar.PB.FMX

theorem GlobalTheory.CompanionTheory.Ar.PB.FMX.exists_flagTotal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∃ (Z : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ Z) (f : Z ⟶ 𝔐.X), @CoordTie Z _ _ ℤ _ (Ring.toIntAlgebra _) ξ' _ (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) ∧ (∀ q : Z, genPt ξ' ⤳ q) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ' 𝔐.ξ f (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) ∧ Smooth f := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ hF
  classical
  obtain ⟨hL, hc, hφ, hB⟩ := hF
  set r := rk (CMType H) D.p D.q with hr
  set x : ((k : K₀) → J₀ k) → Ω := seg x₀ with hxdef
  set cF := cc 𝔐 bW bO with hcF
  have hx : CoordTie ℤ 𝔐.ξ x := 𝔐.tie
  obtain ⟨c₀, hc₀⟩ := hx.cover ⟨genPt 𝔐.ξ, specializes_refl _⟩
  have hB' : ∀ s, ∃ B : Matrix (Fin (r s)) (Fin (n s)) Ω, B * Matrix.of (fun j l => φ s j (cF s l)) = 1 := hB
  obtain ⟨J₁, hJ₁, hfrac⟩ := GlobalTheory.T.frame_matrix_chart_ratios Ω (EE 𝔐) (CMType H ⊕ CMType H) r n ((k : K₀) → J₀ k) x φ cF c₀ hc₀.1
    (GlobalTheory.T.function_field_ratio_generators 𝔐.X Ω 𝔐.ξ _ x c₀ hx hc₀.1) hB'
  have : Finite (FlagIx ((k : K₀) → J₀ k) n r) := by unfold FlagIx; infer_instance
  obtain ⟨X', ξ', s', hx', hirr', -, hprop, -⟩ :=
    GlobalTheory.T.exists_proper_integral_model (GenField Ω r) ℤ (FlagIx ((k : K₀) → J₀ k) n r) (flagCoord _ x φ cF) J₁ hJ₁ hfrac
  obtain ⟨f, hdom, hch⟩ := GlobalTheory.T.dominates_of_coords_regular 𝔐.X Ω 𝔐.ξ ℤ _ x X' (GenField Ω r) ξ' (algebraMap Ω (GenField Ω r)) hx hx'.gen
    hirr' (fun z p' => by simp [intCast_mem (regAt ξ' p') z]) (fun p' => by
      obtain ⟨⟨c1, J⟩, hne, hrat⟩ := hx'.cover p'
      have e1 : ∀ k, flagCoord _ x φ cF (k, J) = algebraMap Ω (GenField Ω r) (x k) *
          ∏ q : (Σ s, Fin (r s)), ((flagMat φ cF q.1).submatrix (J q) (Fin.castLE q.2.2)).det := fun k => rfl
      rw [e1] at hne
      refine ⟨c1, left_ne_zero_of_mul hne, fun k => ?_⟩
      have := hrat (k, J)
      rwa [e1, e1, mul_div_mul_right _ _ (right_ne_zero_of_mul hne)] at this)
  have hsm := GlobalTheory.T.flag_frames_generic_model_right 𝔐.X Ω 𝔐.ξ (EE 𝔐) _ x (CMType H ⊕ CMType H) r (VV 𝔐) (LL 𝔐) m n φ cF X' ξ' f hx 𝔐.all hL hφ hc
    hx' hirr' hdom hch
  have hseg : seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀) =
      flagCoord ((k : K₀) → J₀ k) x φ cF ∘ segIxEquiv (Ψ := CMType H) (p := D.p) (q := D.q) (n := n) (J₀ := J₀) := by
    funext c'
    show ∏ k, yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀ ⟨k, c' k⟩ =
      algebraMap Ω (GenField Ω r) (∏ k, x₀ ⟨k, c' (.inl k)⟩) *
        ∏ q : (Σ s, Fin (r s)), ((flagMat φ cF q.1).submatrix (c' (.inr q)) (Fin.castLE q.2.2)).det
    rw [Fintype.prod_sum_type, map_prod]
    rfl
  refine ⟨X', ξ', f, ?_, hirr', hdom, hsm⟩
  rw [hseg]
  convert coordTie_comp_equiv hx' (segIxEquiv (Ψ := CMType H) (p := D.p) (q := D.q) (n := n) (J₀ := J₀)) using 1 <;> exact Subsingleton.elim _ _
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameOrderBound
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.DimBase

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar GlobalTheory.CompanionTheory.Ar.TieArith ReciprocityTheory.ChartRestriction.G.AI.I4

section Comparison₂

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
  {K : Type} [Fintype K] {J : K → Type}

theorem exists_chart (y : (Σ k, J k) → Ω) (h : CoordTie ℤ ξ (seg y)) :
    ∃ c : ∀ k, J k, ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  obtain ⟨c, hchart⟩ := h.cover (genCpt ξ)
  exact ⟨c, fun k ↦ (Finset.prod_ne_zero_iff.mp hchart.1) k (Finset.mem_univ k)⟩

theorem ratioField_eq_top [CharZero Ω] (y : (Σ k, J k) → Ω) (h : CoordTie ℤ ξ (seg y)) (c : ∀ k, J k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : ratioField y c = ⊤ := by
  have hne : seg y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ hc k
  rw [eq_top_iff]
  intro a _
  obtain ⟨g, hg, u, hu, -, rfl⟩ := FracChart.exists_eq_div_adjoin X Ω ξ _ (seg y) c h hne a
  exact div_mem (adjoin_le_ratioField y c hg) (adjoin_le_ratioField y c hu)

theorem trdeg_eq_of_ringKrullDim [∀ k, Fintype (J k)] [CharZero Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (htop : ratioField y c = ⊤) (d : ℕ)
    (hdim : ringKrullDim (MRing J ⧸ mCoordIdeal y) = ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    Algebra.trdeg ℤ Ω = d := by
  have hb : blockFnField y = ⊤ := by rw [← Cmp.ratioField_eq_blockFnField y c hc, htop]
  have htr : Algebra.trdeg ℤ (blockFnField y) = Algebra.trdeg ℤ Ω := by
    rw [hb]
    exact (IntermediateField.topEquiv (F := ℚ) (E := Ω)).toRingEquiv.toIntAlgEquiv.trdeg_eq
  rw [Cmp.ringKrullDim_coord y c hc, htr] at hdim
  have h1 : (Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal)).toENat + 1 =
      ((d + 1 + Fintype.card K : ℕ) : ℕ∞) := WithBot.coe_injective hdim
  have h2 : (Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal)).toENat =
      ((d + Fintype.card K : ℕ) : ℕ∞) := by
    generalize (Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal)).toENat = e at h1
    cases e using ENat.recTopCoe with
    | top => exact absurd h1 (by rw [top_add]; exact (ENat.coe_ne_top _).symm)
    | coe e =>
      have h3 : e + 1 = d + 1 + Fintype.card K := by exact_mod_cast h1
      have h4 : e = d + Fintype.card K := by omega
      rw [h4]
  have h5 : Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal) = ((d + Fintype.card K : ℕ) : Cardinal) :=
    Cardinal.toENat_eq_nat.mp h2
  rw [Nat.cast_add] at h5
  exact (Cardinal.add_nat_inj _).mp h5

end Comparison₂

theorem isArithVar_xb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (d : ℕ), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → IsArithVar (mCoordIdeal x₀) (d + 1) → IsArithVar (mCoordIdeal (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (d + 1) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ d _ hT hA
  obtain ⟨c₀, hc₀⟩ := exists_chart 𝔐.ξ x₀ 𝔐.tie
  obtain ⟨cb, hcb⟩ := exists_chart 𝔐.ξ _ hT
  have hd : Algebra.trdeg ℤ Ω = d :=
    trdeg_eq_of_ringKrullDim x₀ c₀ hc₀ (ratioField_eq_top 𝔐.ξ x₀ 𝔐.tie c₀ hc₀) d hA.2.2.2
  obtain ⟨k₀⟩ := hA.1
  have hK : Nonempty (NonPluckerBlocks (blkF (CMType H) D.p D.q K₀)) := by
    refine ⟨⟨.inl k₀, fun r ↦ ?_⟩⟩
    unfold blkF
    split <;> simp
  exact isArithVar_of_ratioField_eq_top _ cb hcb (ratioField_eq_top 𝔐.ξ _ hT cb hcb) d hd

end GlobalTheory.CompanionTheory.Ar.PB.FMX.DimBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameUnitCriterion
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar

section Fields

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {G : Type} [Field G] [CharZero G]

omit [∀ k, Fintype (ι k)] in

theorem prod_div_mem (y : (Σ k, ι k) → G) (u v : ∀ k, ι k) :
    (∏ k, y ⟨k, u k⟩) / (∏ k, y ⟨k, v k⟩) ∈ blockFnField y := by
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun k _ => IntermediateField.subset_adjoin _ _ ⟨⟨k, u k⟩, ⟨k, v k⟩, rfl, rfl⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem blockFnField_eq_top [Algebra ℤ G] (y : (Σ k, ι k) → G) {κ : Type} (f : κ → G) (c₀ : κ)
    (hsub : ∀ j, f j / f c₀ ∈ blockFnField y)
    (hgen : ∀ a : G, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => f j / f c₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => f j / f c₀), h ≠ 0 ∧ a = g / h) :
    blockFnField y = ⊤ := by
  have hle : ∀ g ∈ Algebra.adjoin ℤ (Set.range fun j => f j / f c₀), g ∈ blockFnField y := by
    intro g hg
    induction hg using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hsub j
    | algebraMap r => rw [eq_intCast]; exact intCast_mem (blockFnField y) r
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  rw [eq_top_iff]
  intro a _
  obtain ⟨g, hg, h, hh, -, rfl⟩ := hgen a
  exact div_mem (hle g hg) (hle h hh)

theorem trdeg_top : Algebra.trdeg ℤ (⊤ : IntermediateField ℚ G) = Algebra.trdeg ℤ G := by
  have e : (⊤ : IntermediateField ℚ G) ≃ₐ[ℤ] G := (IntermediateField.topEquiv (F := ℚ) (E := G)).restrictScalars ℤ
  exact e.trdeg_eq

end Fields

section Gen

variable (Ω : Type) [Field Ω] [CharZero Ω] {S : Type} (r : S → ℕ)

theorem trdeg_genField [inst : Algebra ℤ (GenField Ω r)] :
    Algebra.trdeg ℤ (GenField Ω r) = Algebra.trdeg ℤ Ω + Cardinal.mk (GenIx r) := by
  obtain rfl : inst = OreLocalization.instAlgebra := Subsingleton.elim _ _
  haveI : Algebra.IsAlgebraic (MvPolynomial (GenIx r) Ω) (GenField Ω r) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial (GenIx r) Ω))
  haveI : FaithfulSMul ℤ Ω := (faithfulSMul_iff_algebraMap_injective ℤ Ω).mpr
    (by simpa using (Int.cast_injective (α := Ω)))
  have h1 := trdeg_add_eq ℤ Ω (A := GenField Ω r)
  have h2 := trdeg_add_eq Ω (MvPolynomial (GenIx r) Ω) (A := GenField Ω r)
  rw [trdeg_eq_zero (R := MvPolynomial (GenIx r) Ω) (A := GenField Ω r), add_zero, MvPolynomial.trdeg_of_isDomain] at h2
  rw [← h1, ← h2, Cardinal.lift_id]

end Gen

section Dim

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {G : Type} [Field G] [CharZero G]

theorem isArithVar_of_trdeg [Nonempty K] (y : (Σ k, ι k) → G) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (e : ℕ)
    (htr : Algebra.trdeg ℤ (blockFnField y) = e) : IsArithVar (mCoordIdeal y) (e + 1) := by
  refine ⟨‹_›, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal y, relevant y c hc⟩, horizontal y, ?_⟩
  rw [GlobalTheory.CompanionTheory.Ar.Cmp.ringKrullDim_coord y c hc, htr, map_add, Cardinal.toENat_nat, Cardinal.toENat_nat]
  have h4 : (e : ℕ∞) + (Fintype.card K : ℕ∞) + 1 = ((e + 1 + Fintype.card K : ℕ) : ℕ∞) := by
    push_cast
    ring
  rw [h4]
  rfl

theorem trdeg_of_isArithVar (x : (Σ k, ι k) → G) (d : ℕ) (hx : IsArithVar (mCoordIdeal x) (d + 1)) :
    ∃ c : ∀ k, ι k, (∀ k, x ⟨k, c k⟩ ≠ 0) ∧ Algebra.trdeg ℤ (blockFnField x) = d := by
  obtain ⟨-, ⟨-, -, hrel⟩, -, hdim⟩ := hx
  have hne : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, MvPolynomial.aeval_X, h0, map_zero, zero_mul]
  choose c hc using hne
  refine ⟨c, hc, ?_⟩
  rw [GlobalTheory.CompanionTheory.Ar.Cmp.ringKrullDim_coord x c hc] at hdim
  have h1 : (Algebra.trdeg ℤ (blockFnField x) + (Fintype.card K : Cardinal)).toENat + 1 =
      ((d + 1 + Fintype.card K : ℕ) : ℕ∞) := WithBot.coe_injective hdim
  rw [map_add, Cardinal.toENat_nat] at h1
  have h3 : (Algebra.trdeg ℤ (blockFnField x)).toENat + ((Fintype.card K + 1 : ℕ) : ℕ∞) =
      (d : ℕ∞) + ((Fintype.card K + 1 : ℕ) : ℕ∞) := by
    push_cast at h1 ⊢
    rw [← add_assoc, h1]
    ring
  have h2 : (Algebra.trdeg ℤ (blockFnField x)).toENat = (d : ℕ∞) :=
    WithTop.add_right_cancel (ENat.coe_ne_top _) h3
  exact Cardinal.toENat_eq_nat.mp h2

end Dim

section Main

variable {Ψ : Type} [Fintype Ψ] {p q : ℕ}

theorem mk_genIx : Cardinal.mk (GenIx (rk Ψ p q)) = ((Fintype.card Ψ * (p.choose 2 + q.choose 2) : ℕ) : Cardinal) := by
  show Cardinal.mk (Σ s : Ψ ⊕ Ψ, {lk : Fin (rk Ψ p q s) × Fin (rk Ψ p q s) // lk.2 < lk.1}) = _
  rw [Cardinal.mk_fintype, Fintype.card_sigma]
  simp only [FlagTrdeg.card_below_diagonal]
  rw [Fintype.sum_sum_type]
  simp [rk, Nat.choose_two_right]
  ring

variable {Ω : Type} [Field Ω] [CharZero Ω] {E : Type} [AddCommGroup E] [Module Ω E]
  {n : Ψ ⊕ Ψ → ℕ} (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (rk Ψ p q s) → E)
  {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω)

abbrev vals (s : Ψ ⊕ Ψ) : Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω := Matrix.of fun j l => φ s j (c s l)

def chartOf (j : FlagIx ((k : K₀) → J₀ k) n (rk Ψ p q)) : ∀ k, idx (p := p) (q := q) J₀ n k
  | .inl k => j.1 k
  | .inr t => j.2 t

theorem flagCoord_eq_prod (j : FlagIx ((k : K₀) → J₀ k) n (rk Ψ p q)) :
    flagCoord _ (seg x₀) φ c j = ∏ k, yv (vals φ c) x₀ ⟨k, chartOf j k⟩ := by
  rw [Fintype.prod_sum_type]
  simp only [flagCoord, yv, chartOf, seg, map_prod]
  rfl

theorem isArithVar_yv (hB : ∀ s, ∃ B : Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω, B * vals φ c s = 1)
    (hgen : ∀ c₀, seg x₀ c₀ ≠ 0 → ∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => seg x₀ j / seg x₀ c₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => seg x₀ j / seg x₀ c₀), h ≠ 0 ∧ a = g / h)
    (d : ℕ) (hx : IsArithVar (mCoordIdeal x₀) (d + 1)) :
    IsArithVar (mCoordIdeal (yv (vals φ c) x₀)) (d + Fintype.card Ψ * (p.choose 2 + q.choose 2) + 1) := by
  classical
  obtain ⟨c₀, hc₀, htr⟩ := trdeg_of_isArithVar x₀ d hx
  have hs : seg x₀ c₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc₀ k
  obtain ⟨J, hJ, hfrac⟩ := CoordGen.flagCoord_generate Ω E (Ψ ⊕ Ψ) (rk Ψ p q) n _ (seg x₀) φ c c₀ hs (hgen c₀ hs) hB
  haveI : CharZero (GenField Ω (rk Ψ p q)) :=
    charZero_of_injective_algebraMap (algebraMap Ω (GenField Ω (rk Ψ p q))).injective
  have hy : ∀ k, yv (vals φ c) x₀ ⟨k, chartOf J k⟩ ≠ 0 := by
    rw [flagCoord_eq_prod] at hJ
    exact fun k => Finset.prod_ne_zero_iff.1 hJ k (Finset.mem_univ k)
  have htop := blockFnField_eq_top (yv (vals φ c) x₀) (flagCoord _ (seg x₀) φ c) J
    (fun j => by rw [flagCoord_eq_prod, flagCoord_eq_prod]; exact prod_div_mem _ _ _) hfrac
  have htop0 := blockFnField_eq_top x₀ (seg x₀) c₀ (fun j => prod_div_mem x₀ _ _) (hgen c₀ hs)
  haveI : Nonempty (K₀ ⊕ StepIx Ψ p q) := ⟨.inl hx.1.some⟩
  refine isArithVar_of_trdeg _ (chartOf J) hy _ ?_
  rw [htop, trdeg_top, trdeg_genField, ← trdeg_top (G := Ω), ← htop0, htr, mk_genIx]
  push_cast
  rfl

end Main

theorem isArithVar_flagModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (d : ℕ), FormsOK 𝔐 bW bO m φ → IsArithVar (mCoordIdeal x₀) (d + 1) → IsArithVar (mCoordIdeal (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (d + Fintype.card (CMType H) * (D.p.choose 2 + D.q.choose 2) + 1) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ d hF hx
  exact isArithVar_yv φ (cc 𝔐 bW bO) x₀ hF.2.2.2
    (fun c₀ hc₀ => FracChart.exists_eq_div_adjoin 𝔐.X Ω 𝔐.ξ _ (seg x₀) c₀ 𝔐.tie hc₀) d hx

end GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptIsVectorBundleRank
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.FlagBun

section Map

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

theorem isFrameAt_map_of_injective {L : Lat ξ E} {f : E →ₗ[Ω] E'} (hf : Function.Injective f) {r : ℕ}
    {b : Fin r → E} {p : Cpt ξ} (h : L.IsFrameAt b p) : (L.map f).IsFrameAt (fun a => f (b a)) p := by
  refine ⟨h.1.map' f (LinearMap.ker_eq_bot.2 hf), ?_⟩
  show (L p).map (f.restrictScalars (regAt ξ p)) = _
  rw [h.2, Submodule.map_span, ← Set.range_comp]
  rfl

theorem isVB_map_of_injective {L : Lat ξ E} {f : E →ₗ[Ω] E'} (hf : Function.Injective f) {r : ℕ}
    {V : Submodule Ω E} (h : L.IsVB r V) : (L.map f).IsVB r (V.map f) := by
  intro p hp
  obtain ⟨U, hU, b, hb, hq⟩ := h p hp
  refine ⟨U, hU, fun a => f (b a), ?_, fun q hqT hqU => isFrameAt_map_of_injective hf (hq q hqT hqU)⟩
  rw [← hb, Submodule.map_span, ← Set.range_comp]
  rfl

end Map

section Bundles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω}

theorem inW_injective (A : HodgeCpt Y S x) : Function.Injective (inW A) :=
  LinearMap.inl_injective

theorem inO_injective (A : HodgeCpt Y S x) (τ : CMType H) : Function.Injective (inO A τ) := by
  intro a b h
  have e := congrFun (congrArg Prod.snd h) τ
  simpa [inO] using e

end Bundles

theorem LL_isVB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω]
    [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω)
    (𝔐 : HodgeCpt Y S x₀), ∀ s, (LL 𝔐 s).IsVB (rk (CMType H) D.p D.q s) (VV 𝔐 s) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 s
  rcases s with τ | τ
  · exact isVB_map_of_injective (inW_injective 𝔐) (𝔐.vb (.inl τ))
  · exact isVB_map_of_injective (inO_injective 𝔐 τ) (omBundle_isVB 𝔐 τ)

end GlobalTheory.CompanionTheory.Ar.PB.FMX
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IteratedDerivBoundGaussianGrowthStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iterated_deriv_bound_gaussian_growth : ∀ (f : ℂ → ℂ) (M lam : ℝ) (n n' i : ℕ), Differentiable ℂ f → 0 < lam → 1 ≤ n → 1 ≤ n' → i ≤ n' → (∀ τ, ‖f τ‖ ≤ M * Real.exp (n * ‖τ‖ ^ 2 * lam ^ 2 / 2)) → ‖iteratedDeriv i f 0‖ ≤ Real.sqrt (Real.exp 1 * n * n') ^ i * lam ^ i * M := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.norm_iteratedDeriv_zero_le_of_gaussian_growth | exact GlobalTheory.CompanionTheory.Ar.Sl.norm_iteratedDeriv_zero_le_of_gaussian_growth | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.norm_iteratedDeriv_zero_le_of_gaussian_growth <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftToLogResolutionAnalytic
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.HoloLift

variable {e : ℕ} {V : Set (Fin e → ℂ)}

def inclChart (hV : IsOpen V) [Nonempty V] : OpenPartialHomeomorph V (Fin e → ℂ) :=
  hV.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val

theorem inclChart_source (hV : IsOpen V) [Nonempty V] : (inclChart hV).source = Set.univ := by
  simp [inclChart]

theorem inclChart_target (hV : IsOpen V) [Nonempty V] : (inclChart hV).target = V := by
  simp [inclChart]

theorem inclChart_apply (hV : IsOpen V) [Nonempty V] (y : V) : inclChart hV y = y := by
  simp [inclChart]

theorem val_inclChart_symm (hV : IsOpen V) [Nonempty V] {w : Fin e → ℂ} (hw : w ∈ V) :
    (((inclChart hV).symm w : V) : Fin e → ℂ) = w := by
  have h := (inclChart hV).right_inv (x := w) (by rw [inclChart_target]; exact hw)
  rwa [inclChart_apply] at h

theorem eventually_val_inclChart_symm (hV : IsOpen V) [Nonempty V] {w : Fin e → ℂ} (hw : w ∈ V) :
    ∀ᶠ w' in 𝓝 w, (((inclChart hV).symm w' : V) : Fin e → ℂ) = w' := by
  filter_upwards [hV.mem_nhds hw] with w' hw' using val_inclChart_symm hV hw'

def inclAtlas (hV : IsOpen V) [Nonempty V] : FinHolAtlas e V where
  n := 1
  chart _ := inclChart hV
  cover x := ⟨0, by rw [inclChart_source]; trivial⟩
  holo j k := by
    rintro w ⟨hw, -⟩
    rw [inclChart_target] at hw
    refine analyticAt_id.congr ?_
    filter_upwards [eventually_val_inclChart_symm hV hw] with w' hw'
    simp only [Function.comp, inclChart_apply, hw', id]

end GlobalTheory.CompanionTheory.Ar.PB.HoloLift

open GlobalTheory.CompanionTheory.Ar.PB.HoloLift in

theorem GlobalTheory.CompanionTheory.Ar.PB.HoloLift.holo_of_analytic_lift : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D e : ℕ) (R : AnLogRes P J D), J = ⊤ → ∀ (V : Set (Fin e → ℂ)) (μ : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (g : (Fin e → ℂ) → R.X), IsOpen V → (∀ q, AnalyticOnNhd ℂ (fun u => μ u q) V) → (∀ u ∈ V, SameOrbit (R.lift (g u) (g u)) (μ u)) → ContinuousOn g V ∧ ∀ k, AnalyticOnNhd ℂ (R.A.chart k ∘ g) (V ∩ g ⁻¹' (R.A.chart k).source) := by
  intro K _ ι _ P J D e R hJ V μ g hV hμ hg
  subst hJ
  rcases V.eq_empty_or_nonempty with rfl | hne
  · refine ⟨continuousOn_empty _, fun k w hw => ?_⟩
    exact absurd hw.1 (Set.notMem_empty w)
  haveI : Nonempty V := hne.to_subtype
  let B : FinHolAtlas e V := inclAtlas hV
  let Vf : V → Set V := fun _ => Set.univ
  let μf : V → V → (Σ k, ι k) → ℂ := fun _ u => μ u
  let h : V → R.X := fun y => g y
  have hVo : ∀ y, IsOpen (Vf y) := fun _ => isOpen_univ
  have hVm : ∀ y, y ∈ Vf y := fun _ => Set.mem_univ _
  have hμf : ∀ y q, B.HoloOn (Vf y) fun u => μf y u q := by
    rintro y q j w ⟨hw, -⟩
    have hw' : w ∈ V := by simpa [B, inclAtlas, inclChart_target] using hw
    refine (hμ q w hw').congr ?_
    filter_upwards [eventually_val_inclChart_symm hV hw'] with w' h'
    simp only [Function.comp, μf, B, inclAtlas, h']
  have hc : ∀ y y', ∀ u ∈ Vf y ∩ Vf y', SameOrbit (μf y u) (μf y' u) := fun _ _ u _ =>
    Proj.orbit_trans (Proj.orbit_symm (hg u u.2)) (hg u u.2)
  have hh : ∀ y, SameOrbit (R.lift (h y) (h y)) (μf y y) := fun y => hg y y.2
  have hnz : ∀ y k, ∃ i, μf y y ⟨k, i⟩ ≠ 0 := fun y k => by
    obtain ⟨i, hi⟩ := (R.mem (h y) (h y) (R.mem_U _)).1 k
    exact ⟨i, Proj.orbit_ne (hh y) hi⟩
  have hcont : Continuous h := CovMap.continuous_of_orbit_of_ne R B hVo hVm hμf hnz hc hh
  refine ⟨continuousOn_iff_continuous_restrict.2 hcont, fun k w hw => ?_⟩
  have hA := Proj.analytic_of_orbit R B hVo hVm hμf hc hh hcont (0 : Fin 1) k
  have hmem : w ∈ (B.chart (0 : Fin 1)).target ∩
      (B.chart (0 : Fin 1)).symm ⁻¹' (h ⁻¹' (R.A.chart k).source) := by
    refine ⟨by simpa [B, inclAtlas, inclChart_target] using hw.1, ?_⟩
    have e1 := val_inclChart_symm hV hw.1
    show g (((inclChart hV).symm w : V) : Fin e → ℂ) ∈ (R.A.chart k).source
    rw [e1]
    exact hw.2
  refine (hA w hmem).congr ?_
  filter_upwards [eventually_val_inclChart_symm hV hw.1] with w' h'
  show R.A.chart k (g (((inclChart hV).symm w' : V) : Fin e → ℂ)) = R.A.chart k (g w')
  rw [h']
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetCuspFramePlurisubharmonicStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_det_cusp_frame_plurisubharmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ) (I : Submodule (𝓞 E) Λ), IsOpen U → IsHolFam U R → IsCMFam σ → IsEigFrames U (fun t => (R t).B) σ b → (∀ t ∈ U, (R t).IsCusp I) → ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t) - Real.log ((R t).nz σ I)) ∧ ContinuousOn (fun t => (R t).nz σ I) U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.phi_isPsh_continuous | exact GlobalTheory.CompanionTheory.Ar.Cusp.phi_isPsh_continuous | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.phi_isPsh_continuous <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogIndexOfOrthogonalFamilyStatement
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_index_of_orthogonal_family : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r : ℕ) (v : Fin r → V), 2 * Fintype.card Ψ = Module.finrank ℚ E → IsOFamily A.ρ A.I v → ∀ s, logIdx (A.tor s) (fun a => eigComp A.ρ (A.σ s) (v a)) / Module.finrank ℚ L = -(r * Real.log (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ)))) + Real.log (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) / Module.finrank ℚ E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.torusPartDegree | exact GlobalTheory.CompanionTheory.Ar.Cusp.torusPartDegree | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.torusPartDegree <;> assumption)
end

