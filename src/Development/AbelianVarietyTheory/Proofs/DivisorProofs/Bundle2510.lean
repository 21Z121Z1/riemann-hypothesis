import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2343
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0024
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0688
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0056
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteOfIsClosedOfFiniteInterClosedPoints
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelLevelPPower
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatModel

theorem lt_norm_mul_of_close {K : Type} [NormedField K] [IsUltrametricDist K] {a₁ a₂ c₁ c₂ : K} {ε : ℝ}
    (h₂ : ‖a₂‖ ≤ 1) (hc₁ : ‖c₁ - a₁‖ ≤ ε) (hc₂ : ‖c₂ - a₂‖ ≤ ε) (hε1 : ε ≤ 1) (h₁ : ‖a₁‖ ≤ 1)
    (hε : ε < ‖a₁ * a₂‖) : ε < ‖c₁ * c₂‖ := by
  have hc2 : ‖c₂‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (c₂ - a₂) a₂
    rw [sub_add_cancel] at this
    exact this.trans (max_le (hc₂.trans hε1) h₂)
  have e : c₁ * c₂ - a₁ * a₂ = (c₁ - a₁) * c₂ + a₁ * (c₂ - a₂) := by ring
  have hd : ‖c₁ * c₂ - a₁ * a₂‖ ≤ ε := by
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_mul hc₁ hc2 (norm_nonneg _) ((norm_nonneg _).trans hc₁)).trans_eq (mul_one ε)
    · rw [norm_mul]
      exact (mul_le_mul h₁ hc₂ (norm_nonneg _) zero_le_one).trans_eq (one_mul ε)
  have := IsUltrametricDist.norm_add_le_max (a₁ * a₂ - c₁ * c₂) (c₁ * c₂)
  rw [sub_add_cancel, norm_sub_rev] at this
  rcases le_max_iff.1 this with h | h
  · exact absurd (hε.trans_le h) (not_lt.2 hd)
  · exact hε.trans_le h

theorem exists_large_minors : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → TateSt → ValueSt → BoundSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (τ : Psi H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ n : ℕ,
    ∀ (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → l'.A = p ^ n →
    ∀ (N : ℕ) (a : Fin N → Dw.La) (T S : Ind Dw τ.1 → Fin N → c'.V W), LatData Dw (embV c' W (conjEmb τ.1)) a T S →
    ∀ [Algebra c.F ℂ_[p]] (f : Rul Xo c) (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
      (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]), HTAt Y r ν yb yy P π ψ y →
      (p : ℝ)⁻¹ ^ n < ‖((((discr E : ℤ) : ℂ_[p]) ^ 2 * (p : ℂ_[p]) ^ 2) ^ (Dw.mult τ.1 + Dw.mult (conjEmb τ.1)))‖ →
      ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
      ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)) (U₁ U₂ : Fin g → Fin g → 𝓞_ℂ_[p])
        (h : Fin N → Fin g → 𝓞_ℂ_[p]), IsTanBasis Y.t yb e → EigAt Y.t yb (β.comp (embV c' W τ.1)) e U₁ →
        EigAt Y.t yb (β.comp (embV c' W (conjEmb τ.1))) e U₂ → HTApprox Y n yy P π ψ a e h →
        ∃ (σ : Equiv.Perm (Ind Dw τ.1)) (K₁ : Fin (Dw.mult τ.1) → Fin g) (K₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g),
          ((p : ℝ)⁻¹ ^ n < ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) *
        pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p])‖) := by
  intro hKer hTate hVal hBound E _ _ _ H Dw τ p _ _ hs n l l' Xo Xo' c c' W Y r ν hle hov hA N a T S hLat _ f yb yy P π ψ y
    hHT hn β hβ g e U₁ U₂ h hTan hE₁ hE₂ hApp
  obtain ⟨ta, w₁, w₂, σ, hta, hw₁, hw₂, hG₁, hG₂⟩ :=
    GlobalTheory.T.integral_model_level_p_power_frame hKer hTate hVal E H Dw τ p hs n l l' Xo Xo' c c' W Y r ν hle hov hA N a T S hLat yb yy P π ψ y
      hHT β hβ
  obtain ⟨x, hx, hM⟩ := GlobalTheory.T.integral_model_map_over_inclusion E H Dw p l l' Xo Xo' c c' W Y r ν hle hov yb yy P π ψ y hHT β hβ g e hTan
  have hCB : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.CokernelBound P := (hKer p ℂ_[p] _ 𝓞_ℂ_[p] (𝓞 E) P).2.2.1
  set d : ℂ_[p] := ((discr E : ℤ) : ℂ_[p]) with hd
  have hnorm : ∀ z : 𝓞_ℂ_[p], ‖(z : ℂ_[p])‖ ≤ 1 := fun z => (GlobalTheory.PadicComplexHost.mem_iff_norm p _).1 z.2
  have hd0 : d ^ 2 * (p : ℂ_[p]) ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E)))
    (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))
  have hε1 : (p : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by positivity)
    (inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le))

  have key : ∀ (σ' : E →+* ℂ) (U : Fin g → Fin g → 𝓞_ℂ_[p]), EigAt Y.t yb (β.comp (embV c' W σ')) e U →
      ∀ w : P.V, w ∈ htLat c P σ' → w ∈ Submodule.span ℂ_[p] (Set.range P.bLie) →
        w ∈ P.eigV (embInt c P.integers σ') → ∃ M : Fin g → 𝓞_ℂ_[p],
          (d ^ 2 * (p : ℂ_[p]) ^ 2) • w = ∑ k, (M k : ℂ_[p]) • ∑ b, (U k b : ℂ_[p]) • P.bLie (x b) := by
    intro σ' U hU w h1 h2 h3
    obtain ⟨x', hx'e, hx'⟩ := hBound E H l c p P hCB σ' w h1 h2 h3
    obtain ⟨M, hM'⟩ := hM σ' U hU x' hx'e
    refine ⟨M, ?_⟩
    rw [← hM', hx', smul_smul]
    congr 1
    ring
  choose M₁ hM₁ using fun i => key τ.1 U₁ hE₁ (w₁ i) (hw₁ i).1 (hw₁ i).2.1 (hw₁ i).2.2
  choose M₂ hM₂ using fun i => key (conjEmb τ.1) U₂ hE₂ (w₂ i) (hw₂ i).1 (hw₂ i).2.1 (hw₂ i).2.2
  have hcong : ∀ (U : Fin g → 𝓞_ℂ_[p]) (Tc : Ind Dw τ.1 → Fin N → 𝓞_ℂ_[p]) (i : Ind Dw τ.1),
      ‖(((∑ b, (∑ a, Tc i a * h a b) * U b : 𝓞_ℂ_[p]) : ℂ_[p]) -
        P.pairV (∑ b, (U b : ℂ_[p]) • P.bLie (x b)) (∑ m, (Tc i m : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m))‖ ≤ (p : ℝ)⁻¹ ^ n :=
    fun U Tc i => GlobalTheory.T.p_adic_pairing_approximation E p P n N g ta x h Tc U (fun m b => hApp m (ta m) (hta m) b (x b) (hx b)) i
  have hpair : ∀ (M : Fin g → 𝓞_ℂ_[p]) (X : Fin g → P.V) (t : P.V),
      P.pairV (∑ k, (M k : ℂ_[p]) • X k) t = ∑ k, (M k : ℂ_[p]) * P.pairV (X k) t := by
    intro M X t
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  obtain ⟨K₁, hK₁, hK₁', hK₁''⟩ := GlobalTheory.T.exists_minor_norm_det_bounds_and_det_sub_le p n (Dw.mult τ.1) g (d ^ 2 * (p : ℂ_[p]) ^ 2)
    (fun k j => P.pairV (∑ b, (U₁ k b : ℂ_[p]) • P.bLie (x b))
      (∑ m, ((β (T (σ (Sum.inl j)) m) : 𝓞_ℂ_[p]) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m))
    (fun k j => ((∑ b, covec β T h (σ ∘ Sum.inl) j b * U₁ k b : 𝓞_ℂ_[p]) : ℂ_[p]))
    (Matrix.of fun k k' => P.pairV (w₁ k) (∑ m, (β (T (σ (Sum.inl k')) m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m))
    (fun i k => (M₁ i k : ℂ_[p])) hd0 (fun k j => hnorm _)
    (fun k j => hcong (U₁ k) (fun i a => β (T i a)) (σ (Sum.inl j))) (fun i k => hnorm _) hG₁
    (fun i j => by
      rw [Matrix.of_apply, ← smul_eq_mul, ← LinearMap.smul_apply, ← map_smul, hM₁ i, hpair])
  obtain ⟨K₂, hK₂, hK₂', hK₂''⟩ := GlobalTheory.T.exists_minor_norm_det_bounds_and_det_sub_le p n (Dw.mult (conjEmb τ.1)) g (d ^ 2 * (p : ℂ_[p]) ^ 2)
    (fun k j => P.pairV (∑ b, (U₂ k b : ℂ_[p]) • P.bLie (x b))
      (∑ m, ((β (S (σ (Sum.inr j)) m) : 𝓞_ℂ_[p]) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m))
    (fun k j => ((∑ b, covec β S h (σ ∘ Sum.inr) j b * U₂ k b : 𝓞_ℂ_[p]) : ℂ_[p]))
    (Matrix.of fun k k' => P.pairV (w₂ k) (∑ m, (β (S (σ (Sum.inr k')) m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m))
    (fun i k => (M₂ i k : ℂ_[p])) hd0 (fun k j => hnorm _)
    (fun k j => hcong (U₂ k) (fun i a => β (S i a)) (σ (Sum.inr j))) (fun i k => hnorm _) hG₂
    (fun i j => by
      rw [Matrix.of_apply, ← smul_eq_mul, ← LinearMap.smul_apply, ← map_smul, hM₂ i, hpair])
  refine ⟨σ, K₁, K₂, ?_⟩
  have e₁ : ((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) : 𝓞_ℂ_[p]) : ℂ_[p]) =
      (Matrix.of fun k j => ((∑ b, covec β T h (σ ∘ Sum.inl) j b * U₁ (K₁ k) b : 𝓞_ℂ_[p]) : ℂ_[p])).det := by
    change algebraMap 𝓞_ℂ_[p] ℂ_[p] (Matrix.det _) = _
    rw [RingHom.map_det]
    rfl
  have e₂ : ((pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p]) =
      (Matrix.of fun k j => ((∑ b, covec β S h (σ ∘ Sum.inr) j b * U₂ (K₂ k) b : 𝓞_ℂ_[p]) : ℂ_[p])).det := by
    change algebraMap 𝓞_ℂ_[p] ℂ_[p] (Matrix.det _) = _
    rw [RingHom.map_det]
    rfl
  change (p : ℝ)⁻¹ ^ n < ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) : 𝓞_ℂ_[p]) : ℂ_[p]) *
    ((pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p])‖
  rw [e₁, e₂]
  refine lt_norm_mul_of_close hK₂' hK₁'' hK₂'' hε1 hK₁' (hn.trans_le ?_)
  rw [pow_add, norm_mul, norm_pow, norm_pow]
  exact (mul_le_mul hK₁ hK₂ (by positivity) (norm_nonneg _)).trans_eq (norm_mul _ _).symm

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSectionExpandsIntegrallyGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaSpecialise

namespace GlobalTheory.IntExpand

theorem gs_secPull {X Y Z : Scheme.{0}} {L : LB X} (s : L.Sec) (φ : Y ⟶ X) (r : Z ⟶ Y) (z : Z)
    (j : (L.pull φ).ι) (hz : r z ∈ (L.pull φ).U j) :
    gs r z ((L.pull φ).U j) ((GlobalTheory.Cartier.secPull s φ).f j) = gs (r ≫ φ) z (L.U (j PUnit.unit)) (s.f (j PUnit.unit)) := by
  unfold GlobalTheory.Cartier.secPull
  exact (gs_res r z _ hz _).trans (gs_pull r φ z _ (Set.mem_iInter.1 hz PUnit.unit) _)

theorem gs_secMaps {X Z : Scheme.{0}} {A B : LB X} {w : LB.Iso A B} {a : A.Sec} {b : B.Sec}
    (h : GlobalTheory.Cartier.SecMaps w a b) (r : Z ⟶ X) (z : Z) (p : B.ι) (q : A.ι) (hp : r z ∈ B.U p)
    (hq : r z ∈ A.U q) :
    gs r z (B.U p) (b.f p) = ↑(gm r z ((B.div A).U (p, q)) (w.s (p, q))) * gs r z (A.U q) (a.f q) := by
  have e := congrArg (gs r z (B.U p ⊓ A.U q)) (h.on p q (W := B.U p ⊓ A.U q) inf_le_left inf_le_right)
  have hm : r z ∈ B.U p ⊓ A.U q := ⟨hp, hq⟩
  rw [gs_mul r z _ hm] at e
  unfold resG at e
  rw [gs_res r z _ hm, gs_res r z _ hm, gs_res r z _ hm] at e
  rw [e, gs_unit r z _ (by exact hm)]
  rfl

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D A G), ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre), w₀.IsGen → ∀ (s : A.L.Sec) (σ : U.LG.L.Sec), GlobalTheory.Cartier.SecMaps w₀ (GlobalTheory.Cartier.secPull s U.gen.hom.left) (GlobalTheory.Cartier.secPull σ (pullback.fst G.hom (jK V))) → ∀ (C : Type) [Field C] [Algebra (FractionRing V) C], ∃ (σ₁ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (th : GlobalTheory.UT.SecA A C 1) (ϑ : Fam D.toPre C 1), (∀ (i : U.LG.L.ι) (h : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i), σ₁.f (fun _ => i) = resG _ h (σ.f i)) ∧ (∀ e, U.ExpandsAt e 1 σ₁ f) ∧ MBLow.IsPolAVSectionInverseImage A (TFK (R := V) C) s th ∧ U.ExpandsF C 1 w₀ th ϑ ∧ ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C α) (DegPre.famε 1) (ϑ.s α) (D.toPre.famφB α) (DegPre.famε 1) (f α) (DegPre.prB D.toPre C).left 1 := by
  intro V _ _ _ _ hV D A G _ _ hG U w₀ hw s σ hS C _ _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let σ₁ : H0 U.LG.L 1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.secOne U.LG.L σ
  have h1 : ∀ (i : U.LG.L.ι) (h : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i), σ₁.f (fun _ => i) = resG _ h (σ.f i) := fun i h =>
    fn_ext fun x hx => (ReciprocityTheory.ChartRestriction.G.PullbackSections.gs_pull1 U.LG.L (𝟙 _) σ (𝟙 _) x _ hx).trans (by
      rw [Category.comp_id]; exact (gs_res (𝟙 _) x h hx (σ.f i)).symm)
  let sK : U.SecK 1 := genericSec U.toUnifPre 1 σ₁
  have hsK : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => ((1 : ℕ) : ℤ)) sK (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) σ₁ (pullback.fst G.hom (jK V)) 1 :=
    (secScal_one_iff U.LG.isLB).2 fun y J hJ => (sval_pullOver _ _ _ _ hJ).symm
  obtain ⟨E, hE, -⟩ := (U.expand 1 le_rfl).1 sK
  obtain ⟨f, hf, hEf⟩ := GlobalTheory.ExpInt.main V ϖ hϖ D A G U.toUnifPre 1 σ₁ sK hsK E hE
  obtain ⟨ϑ, hϑ⟩ := GlobalTheory.FamBaseChange.main GlobalTheory.globalFns_holds V _ D 1 E f hEf C
  let th : GlobalTheory.UT.SecA A C 1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.pull1 A.L (snd (TFK (R := V) C) A.A).left s
  have hth : MBLow.IsPolAVSectionInverseImage A (TFK (R := V) C) s th := by
    refine fun i h => fn_ext fun x hx => ?_
    exact (ReciprocityTheory.ChartRestriction.G.PullbackSections.gs_pull1 A.L _ s (𝟙 _) x _ hx).trans (gs_appLE _ _ _ h (𝟙 _) x hx (s.f i)).symm
  have n₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  obtain ⟨u, hu, hu₁⟩ := GlobalTheory.ThetaBaseChange.exists_unpull hw _ n₁ rfl
  have ht : PSec u (fun _ : Fin 1 => (snd (TFK (R := V) C) A.A).left) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ))
      ((snd (TFK (R := V) C) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V)) th σ₁ := by
    intro Z r z p q hp hq
    obtain ⟨p0, rfl⟩ : ∃ p0, p = fun _ => p0 := ⟨p 0, funext fun k => congrArg p (Subsingleton.elim k 0)⟩
    obtain ⟨q0, rfl⟩ : ∃ q0, q = fun _ => q0 := ⟨q 0, funext fun k => congrArg q (Subsingleton.elim k 0)⟩
    have hp0 := hp 0
    have hq0 := hq 0
    have e1 := hu₁ Z (r ≫ (snd (TFK (R := V) C) A.A).left) z p0 q0 hp0 hq0
    have c2 : ((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) ≫ U.gen.hom.left =
        r ≫ (snd (TFK (R := V) C) A.A).left := by
      rw [Category.assoc, n₁, Category.comp_id]
    have mB : ((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) z ∈
        (U.LG.L.pull (pullback.fst G.hom (jK V))).U (fun _ => p0) := Set.mem_iInter.2 fun _ => hp0
    have mA : ((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) z ∈
        (A.L.pull U.gen.hom.left).U (fun _ => q0) := Set.mem_iInter.2 fun _ => by
      show (((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) ≫ U.gen.hom.left) z ∈ A.L.U q0
      rw [c2]; exact hq0
    have e2 := GlobalTheory.IntExpand.gs_secMaps hS _ z (fun _ => p0) (fun _ => q0) mB mA
    rw [GlobalTheory.IntExpand.gs_secPull _ _ _ _ _ mB, GlobalTheory.IntExpand.gs_secPull _ _ _ _ _ mA, c2] at e2
    refine (ReciprocityTheory.ChartRestriction.G.PullbackSections.gs_pull1 U.LG.L (𝟙 _) σ
      (r ≫ (snd (TFK (R := V) C) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V)) z (fun _ => p0)
      (Set.mem_iInter.2 fun _ => by exact hp0)).trans ?_
    refine Eq.trans ?_ (congrArg (fun t => _ * t)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.gs_pull1 A.L _ s r z (fun _ => q0) (Set.mem_iInter.2 fun _ => hq0)).symm)
    rw [Fin.prod_univ_one]
    dsimp only
    rw [Nat.cast_one, zpow_one, e1]
    have c1 : (r ≫ (snd (TFK (R := V) C) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V)) ≫ 𝟙 G.left =
        ((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) ≫ pullback.fst G.hom (jK V) := by
      simp only [Category.assoc, Category.comp_id]
    rw [c1]
    exact e2
  refine ⟨σ₁, f, th, ϑ, h1, hf, hth, expandsF_of_integral U.toUnifPre C hu₁ σ₁ f hf ϑ ?_ th ht, hϑ⟩
  intro α y J hJ
  exact (((secScal_one_iff D.toPre.P.isLB).1 (hϑ α)) y J hJ).symm

end GlobalTheory.IntExpand
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvCompOfIsGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SymSpread

theorem inv_comp_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (GrpObj.inv : G' ⟶ G').left ≫ φ = φ ≫ (GrpObj.inv : G ⟶ G).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom h G') (𝟙 G'))
  simpa [pushHom, pushPt, Hom.inv_def] using e

end GlobalTheory.SymSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldApplyConstantEqZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem isInv_constFn (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left) (hv : IsInv G v dd) (O : G.left.Opens) (r : R) :
    dd O (constFn G.hom O r) = 0 := by
  refine TopCat.Presheaf.section_ext G.left.sheaf O _ _ fun y hy => ?_
  let g : Sp (G.left.presheaf.stalk y) ⟶ G.left := G.left.fromSpecStalk y
  let φ : R →+* G.left.presheaf.stalk y := (Spec.preimage (g ≫ G.hom)).hom
  have hφ : g ≫ G.hom = spMap φ := (Spec.map_preimage (g ≫ G.hom)).symm
  have ht : ⊤ ≤ g ⁻¹ᵁ O := by
    intro z _
    have hz : g z ∈ Set.range g := ⟨z, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hz
    exact hz.mem_open O.isOpen hy
  have hcomp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (f' : B →+* C),
      spMap (f'.comp f) = spMap f' ≫ spMap f := by
    intro A B C _ _ _ f f'
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  let g' : tEpsG (g ≫ G.hom) ⟶ G :=
    Over.homMk (spMap (algebraMap _ (DualNumber (G.left.presheaf.stalk y))) ≫ g) (by simp)
  have hdual : (dualMap φ).comp (algebraMap R (DualNumber R)) =
      (algebraMap _ (DualNumber (G.left.presheaf.stalk y))).comp φ := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let v' : tEpsG (g ≫ G.hom) ⟶ G :=
    Over.homMk (spMap (dualMap φ) ≫ (tv v).left) (by
      rw [Category.assoc, Over.w (tv v)]
      simp only [Over.mk_hom, Category.comp_id]
      rw [← hcomp, hdual, hcomp, hφ])
  have key := hv.2 _ φ g (g' * v').left O (constFn G.hom O r) hφ ht ⟨g', v', rfl, rfl, rfl⟩
  have h0 : (valR (g' * v').left O (constFn G.hom O r)).snd = 0 := by
    by_cases hw : ⊤ ≤ (g' * v').left ⁻¹ᵁ O
    · rw [GlobalTheory.Points.valR_constFn_of_over G.hom ((algebraMap _ (DualNumber (G.left.presheaf.stalk y))).comp φ)
        _ ?_ O hw r]
      · simp [TrivSqZeroExt.algebraMap_eq_inl]
      · rw [Over.w (g' * v'), hcomp]
        simp only [Over.mk_hom]
        rw [hφ]
    · simp [valR, dif_neg hw]
  rw [h0] at key
  exact ((GlobalTheory.FormalValue.valR_fromSpecStalk y O hy _).symm.trans key.symm).trans
    (map_zero (G.left.presheaf.germ O y hy).hom).symm

end GlobalTheory.Heat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveLineBundleFamilyOfGeometricFibresStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdditive_lineBundleFamily_of_geometricFibres : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A] [IsLocallyNoetherian T.left], IsAbelianScheme A → ∀ (N : LB (A ⊗ T).left) (hN : N.IsLB), Triv (ev N (1 : T ⟶ A) (𝟙 T)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (t : Over.mk s ⟶ T), IsAdditive (ev N (fst A (Over.mk s)) (snd A (Over.mk s) ≫ t))) → IsAdditive N := by
  first | exact @GlobalTheory.AddFib.isAdditive_of_geomFibres | exact GlobalTheory.AddFib.isAdditive_of_geomFibres | (intros; apply GlobalTheory.AddFib.isAdditive_of_geomFibres <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfIsDual
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDual

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

theorem isAdditive_swap_of_isDual (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hd : IsDual A B P) :
    IsAdditive (swap P) := by
  have hP := hd.isLB
  have ext : ∀ {Y : Over S} {x y : Y ⟶ B},
      (∀ (Z : Over S) (u : Z ⟶ Y) (a : Z ⟶ A), evc hP a (u ≫ x) = evc hP a (u ≫ y)) → x = y := by
    intro Y x y h
    have hM : (ev P (fst A Y) (snd A Y ≫ x)).IsLB := pull_isLB hP _
    refine (hd.univ Y _ hM ((isAdditive_iff hM).2 fun Z a a' t ↦ ?_)).unique
      ((cls_eq_iff hM hM).1 rfl) ((cls_eq_iff hM (pull_isLB hP _)).1 ?_)
    · simp only [evc_ev hP, lift_fst, lift_snd_assoc]
      exact (isAdditive_iff hP).1 hd.additive _ _ _ _
    · exact h (A ⊗ Y) (snd A Y) (fst A Y)
  have h₁ : (ev P (fst A (B ⊗ B)) (snd A (B ⊗ B) ≫ fst B B)).IsLB := pull_isLB hP _
  have h₂ : (ev P (fst A (B ⊗ B)) (snd A (B ⊗ B) ≫ snd B B)).IsLB := pull_isLB hP _
  have hM := isLB_tens h₁ h₂
  have eM : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ B ⊗ B),
      evc hM a t = evc hP a (t ≫ fst B B) + evc hP a (t ≫ snd B B) := by
    intro Y a t
    show CechPic.pull _ (cls _ hM) = _
    rw [cls_tens h₁ h₂ hM, map_add]
    exact congrArg₂ (· + ·) ((evc_ev hP _ _ h₁ a t).trans (by rw [lift_fst, lift_snd_assoc]))
      ((evc_ev hP _ _ h₂ a t).trans (by rw [lift_fst, lift_snd_assoc]))
  obtain ⟨m, hm, -⟩ := hd.univ (B ⊗ B) _ hM ((isAdditive_iff hM).2 fun Y a a' t ↦ by
    rw [eM, eM, eM, (isAdditive_iff hP).1 hd.additive, (isAdditive_iff hP).1 hd.additive]
    abel)
  have hm' : (ev P (fst A (B ⊗ B)) (snd A (B ⊗ B) ≫ m)).IsLB := pull_isLB hP _
  have key : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ B ⊗ B),
      evc hP a (t ≫ m) = evc hP a (t ≫ fst B B) + evc hP a (t ≫ snd B B) := by
    intro Y a t
    have e : evc hM a t = evc hm' a t := by rw [evc, evc, (cls_eq_iff hM hm').2 hm]
    rw [← eM, e, evc_ev hP, lift_fst, lift_snd_assoc]
  have hl : ∀ {Y : Over S} (b : Y ⟶ B), lift b 1 ≫ m = b := fun b ↦ ext fun Z u a ↦ by
    rw [← Category.assoc, key]
    simp only [Category.assoc, comp_lift, lift_fst, lift_snd, MonObj.comp_one, evc_one_right hP hd.zero, add_zero]
  have hr : ∀ {Y : Over S} (b : Y ⟶ B), lift 1 b ≫ m = b := fun b ↦ ext fun Z u a ↦ by
    rw [← Category.assoc, key]
    simp only [Category.assoc, comp_lift, lift_fst, lift_snd, MonObj.comp_one, evc_one_right hP hd.zero, zero_add]
  have e1 : ∀ (X : Over S) [MonObj X], (1 : 𝟙_ (Over S) ⟶ X) = η[X] := fun X _ ↦ by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have hη : η[B ⊗ B] ≫ m = η[B] := by
    have e : (1 : 𝟙_ (Over S) ⟶ B ⊗ B) = lift (1 : 𝟙_ (Over S) ⟶ B) 1 := by
      ext <;> simp
    rw [← e1 (B ⊗ B), ← e1 B, e, hl]
  haveI : IsMonHom m := GlobalTheory.rigidity_holds S (B ⊗ B) B (AbelianSchemeGerms.isAbelianScheme_tensor B B hB hB) hB m hη
  have hs : (swap P).IsLB := pull_isLB hP _
  refine (isAdditive_iff hs).2 fun Y b b' a ↦ ?_
  rw [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs]
  have e : b * b' = lift b b' ≫ m := by
    have e' : lift b b' = lift b 1 * lift 1 b' := by
      ext <;> simp [MonObj.mul_comp]
    rw [e', MonObj.mul_comp, hl, hr]
  rw [e, key, lift_fst, lift_snd]

theorem isDual_isAdditive_swap : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left),
    IsAbelianScheme B → IsDual A B P → IsAdditive (swap P) :=
  fun _ _ _ _ _ _ hB hd ↦ isAdditive_swap_of_isDual hB hd

end GlobalTheory.AbDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfLiftTranslationFiniteIndexLattices
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftAffine

section
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem sub_mem_of_ex_eq {z w : Fin g → ℂ} (h : u.ex z = u.ex w) : z - w ∈ u.Λ := by
  have e := u.ex_add (z - w) w
  rw [sub_add_cancel, h] at e
  exact (u.ker _).1 (mul_eq_right.1 e.symm)

theorem ex_eq_of_sub_mem {z w : Fin g → ℂ} (h : z - w ∈ u.Λ) : u.ex z = u.ex w := by
  have e := u.ex_add (z - w) w
  rw [sub_add_cancel, (u.ker _).2 h, _root_.one_mul] at e
  exact e

theorem exists_ex_apply_eq [LocallyOfFiniteType A.hom] (x : A.left) (hx : IsClosed ({x} : Set A.left)) :
    ∃ z, (u.ex z).left (IsLocalRing.closedPoint ℂ) = x := by
  obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk (U := 𝟙_ (Over (Sp ℂ))) (V := A) (pointOfClosedPoint A.hom x hx)
    ((pointOfClosedPoint_comp A.hom x hx).trans rfl))
  exact ⟨z, by rw [hz]; exact pointOfClosedPoint_apply A.hom x hx _⟩

end

theorem isAffineHom_of_lift : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (B : Over (Sp ℂ)) [GrpObj B], IsAbelianScheme B →
    ∀ (L : LB A.left) (L' : LB B.left) (u : HolUnif A L g) (u' : HolUnif B L' g) (a : Fin g → ℂ) (N : ℕ),
    0 < N → u.Λ ≤ u'.Λ → (∀ x ∈ u'.Λ, N • x ∈ u.Λ) →
    ∀ ψ : A.left ⟶ B.left, ψ ≫ B.hom = A.hom → (∀ z, (u.ex z).left ≫ ψ = (u'.ex (z + a)).left) → IsAffineHom ψ := by
  intro g A _ hA B _ hB L L' u u' a N hN hle hN' ψ hψ hex
  have := hA.proper
  have := hB.proper
  have : IsProper (ψ ≫ B.hom) := by rw [hψ]; infer_instance
  have : IsProper ψ := IsProper.of_comp ψ B.hom
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  haveI := u'.discrete
  haveI := holUnif_isZLattice u'
  haveI : Module.Finite ℤ u'.Λ := ZLattice.module_finite ℝ u'.Λ
  let K : Submodule ℤ u'.Λ := u.Λ.comap u'.Λ.subtype
  have hQ : Finite (u'.Λ ⧸ K) := by
    refine Module.finite_of_fg_torsion _ fun q => ?_
    induction q using Submodule.Quotient.induction_on with
    | H l =>
      refine ⟨⟨(N : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hN.ne')⟩, ?_⟩
      change ((N : ℤ) • Submodule.Quotient.mk l : u'.Λ ⧸ K) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      change ((((N : ℤ) • l : u'.Λ)) : Fin g → ℂ) ∈ u.Λ
      rw [Submodule.coe_smul, natCast_zsmul]
      exact hN' _ l.2
  have hLQF : LocallyQuasiFinite ψ := by
    refine GlobalTheory.locallyQuasiFinite_of_finite_fibres_closedPoints ψ fun y hy => ?_
    have hcl : IsClosed ({ψ y} : Set B.left) := by simpa using ψ.isClosedMap _ hy
    refine GlobalTheory.finite_of_isClosed_of_finite_inter_closedPoints (hcl.preimage ψ.continuous) ?_
    obtain ⟨z₀, rfl⟩ := exists_ex_apply_eq u y hy
    let r := Function.surjInv (Submodule.Quotient.mk_surjective K)
    have hr : ∀ q, Submodule.Quotient.mk (r q) = q := Function.surjInv_eq (Submodule.Quotient.mk_surjective K)
    refine (Set.finite_range fun q : u'.Λ ⧸ K =>
      (u.ex (z₀ + ((r q : u'.Λ) : Fin g → ℂ))).left (IsLocalRing.closedPoint ℂ)).subset ?_
    rintro x ⟨hx, hxc⟩
    obtain ⟨z, rfl⟩ := exists_ex_apply_eq u x hxc
    have hx' : ((u.ex z).left ≫ ψ) (IsLocalRing.closedPoint ℂ) =
        ((u.ex z₀).left ≫ ψ) (IsLocalRing.closedPoint ℂ) := by
      first | exact hx | simpa using hx | (simp only [Scheme.Hom.comp_apply]; exact hx)
    rw [hex, hex] at hx'
    have e1 : u'.ex (z + a) = u'.ex (z₀ + a) :=
      Over.OverMorphism.ext (ext_of_apply_closedPoint_eq B.hom (Over.w _) (Over.w _) hx')
    have hl : z - z₀ ∈ u'.Λ := by
      simpa [add_sub_add_right_eq_sub] using sub_mem_of_ex_eq u' e1
    refine ⟨Submodule.Quotient.mk ⟨z - z₀, hl⟩, ?_⟩
    have h2 : (r (Submodule.Quotient.mk ⟨z - z₀, hl⟩) - ⟨z - z₀, hl⟩ : u'.Λ) ∈ K :=
      (Submodule.Quotient.eq K).1 (hr _)
    have h3 : ((r (Submodule.Quotient.mk ⟨z - z₀, hl⟩) : u'.Λ) : Fin g → ℂ) - (z - z₀) ∈ u.Λ := h2
    dsimp only
    rw [ex_eq_of_sub_mem u (z := z₀ + _) (w := z) (by convert h3 using 1; abel)]
  have : IsFinite ψ := .of_isProper_of_locallyQuasiFinite _
  infer_instance

end GlobalTheory.LiftAffine
end
end

