import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceReductionsConjOfNestedFrameStabilisers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0394
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerFockProductEqProdRealPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0395

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceComponentMonomialLatticeSplitCore
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.FinPl.FrameLat

section

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mulVec_sec_w (p : SplitPt D k) {m n : ℕ} (a : Matrix (Fin m) (Fin n) (AE D)) (y : Fin n → k) :
    a *ᵥ (fun i => p.sec (y i)) = fun i => p.sec ((a.map p.pr *ᵥ y) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, sec_mul_right, mul_comm]

theorem inc_mul_sec_mem_iff (p : SplitPt D k) (α : D.host.E) (x : k) :
    incA D α * p.sec x ∈ intAt D (· = p.v) ↔ p.pr (incA D α) * x ∈ 𝒪[k] := by
  rw [mul_comm, sec_mul_right, mul_comm x]
  exact ⟨fun h => (p.int_iff _).2 h.2, sec_mem_intAt p _⟩

theorem proj_mulVec_add {R : Type} [CommRing R] {l m n : ℕ} {P : Matrix (Fin m) (Fin l) R} {J : Matrix (Fin l) (Fin m) R}
    {J' : Matrix (Fin l) (Fin n) R} (h1 : P * J = 1) (h0 : P * J' = 0) (u : Fin m → R) (v : Fin n → R) :
    P *ᵥ (J *ᵥ u + J' *ᵥ v) = u := by
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, h0, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]

end

set_option maxHeartbeats 1000000 in

theorem wShape_of_mono (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S S₀ A Ln : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A Ln) (ζ : Fin Ln.rank → D.host.E)
    (L : Lat S) (M : Lat S₀) (N : Lat A) (α α' : Fin ρ → D.host.E) (μ : D.host.E) (g : GA D A)
    (hmono : MonoAt d L M p.v)
    (hX : ∀ i, ∀ a ∈ idAt D (· = p.v), colMul d.jX i a ∈ latV S L (· = p.v) ↔ incA D (α i) * a ∈ intAt D (· = p.v))
    (hY : ∀ i, ∀ a ∈ idAt D (· = p.v), colMul d.jY i a ∈ latV S L (· = p.v) ↔ incA D (α' i) * a ∈ intAt D (· = p.v))
    (hline : LineAt (vecB o ζ) μ M p.v) (hsplit : SplitsAt o M p.v) (htr : TraceAt o g N M p.v) :
    WShape p d o ζ L (fun i => p.pr (incA D (α i))) (fun i => p.pr (incA D (α' i))) (p.pr (incA D μ)) g N := by
  intro x x' t y
  let f : D.host.E →+* k := p.pr.comp (incA D)
  have hz : o.jB *ᵥ (fun i => p.sec ((t • (f ∘ ζ)) i)) = p.sec t • ratV (vecB o ζ) := by
    rw [mulVec_sec_w, Matrix.mulVec_smul]
    funext i
    have h := RingHom.map_mulVec f o.iB ζ i
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, sec_mul_right]
    exact congrArg (fun u => p.sec (t * u)) h.symm
  obtain ⟨c, hc⟩ : ∃ c : Fin S₀.rank → AE D, c = o.jB *ᵥ (fun i => p.sec ((t • (f ∘ ζ)) i)) +
    o.jA *ᵥ (Formalism.L2.Theta.mt A g *ᵥ fun r => p.sec (y r)) := ⟨_, rfl⟩
  have hcid : ∀ i, c i ∈ idAt D (· = p.v) := fun i => by
    rw [hc, mulVec_sec_w, mulVec_sec_w, mulVec_sec_w]
    exact add_mem (sec_mem_idAt p _) (sec_mem_idAt p _)
  have hvec : (fun r => p.sec ((atW p d.e *ᵥ x + atW p d.e' *ᵥ x' + t • (fun r' => p.pr (incA D ((d.i₀ *ᵥ vecB o ζ) r'))) +
        atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A g).map p.pr *ᵥ y)) r)) =
      d.jX *ᵥ (fun i => p.sec (x i)) + d.jY *ᵥ (fun i => p.sec (x' i)) + d.j0 *ᵥ c := by
    have h1 : (fun r' => p.pr (incA D ((d.i₀ *ᵥ vecB o ζ) r'))) = d.i₀.map f *ᵥ (o.iB.map f *ᵥ (f ∘ ζ)) := by
      have h2 : o.iB.map f *ᵥ (f ∘ ζ) = f ∘ vecB o ζ := by
        funext i; exact (RingHom.map_mulVec f o.iB ζ i).symm
      rw [h2]
      funext i; exact RingHom.map_mulVec f d.i₀ _ i
    have h3 : atW p (d.i₀ * o.iA) = d.i₀.map f * o.iA.map f := Matrix.map_mul (f := f)
    rw [hc, Matrix.mulVec_add, h1, h3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul]
    have e1 : d.jX.map p.pr = atW p d.e := rfl
    have e2 : d.jY.map p.pr = atW p d.e' := rfl
    have e3 : d.j0.map p.pr = d.i₀.map f := rfl
    have e4 : o.jA.map p.pr = o.iA.map f := rfl
    have e5 : o.jB.map p.pr = o.iB.map f := rfl
    rw [mulVec_sec_w p d.jX, mulVec_sec_w p d.jY, mulVec_sec_w p o.jB, mulVec_sec_w p d.j0,
      mulVec_sec_w p (Formalism.L2.Theta.mt A g), mulVec_sec_w p o.jA, mulVec_sec_w p d.j0, e1, e2, e3, e4, e5]
    funext r
    simp only [Pi.add_apply, map_add p.sec, add_assoc]
  rw [hvec, hmono]
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, d.pX_jX, d.pX_jY, d.pX_j0, d.pY_jX, d.pY_jY, d.pY_j0, d.p0_jX,
    d.p0_jY, d.p0_j0, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
  have hA : o.pA *ᵥ c = Formalism.L2.Theta.mt A g *ᵥ fun r => p.sec (y r) := by
    rw [hc, add_comm]; exact proj_mulVec_add o.pA_jA o.pA_jB _ _
  have hB : o.pB *ᵥ c = fun i => p.sec ((t • (f ∘ ζ)) i) := by
    rw [hc]; exact proj_mulVec_add o.pB_jB o.pB_jA _ _
  rw [hsplit c hcid, hA, hB, hz, hline _ (sec_mem_idAt p t), ← htr _ (fun i => sec_mem_idAt p _), inc_mul_sec_mem_iff]
  refine and_congr (forall_congr' fun i => ?_) (and_congr (forall_congr' fun i => ?_) and_comm)
  · rw [hX i _ (sec_mem_idAt p _), inc_mul_sec_mem_iff]
  · rw [hY i _ (sec_mem_idAt p _), inc_mul_sec_mem_iff]

end GlobalTheory.Core.Mi.LatMatch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceReductionsConjOfNestedFrameStabilisersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceReductions_conj_of_nestedFrameStabilisers : ∀ (D : D7) (V : HSp D) (β₁ β₂ : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), Formalism.IndefR.Lev.IsBaseFrame V β₁ Λ N → ∀ (e : Formalism.L2.Theta.AE D) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP → (∀ κ ∈ GfC V, Formalism.IndefR.Lev.finE V κ ∈ Formalism.L2.DIV.St β₁ → Formalism.IndefR.Lev.finE V κ ∈ Formalism.L2.DIV.St β₂) → ∃ m : GL (Fin V.rank) (Formalism.L2.DIV.kP PP), ∀ y, y ∈ Formalism.L2.DIV.St β₁ → y ∈ Formalism.L2.DIV.St β₂ → Formalism.L2.DIV.redFn β₂ PP y = m * Formalism.L2.DIV.redFn β₁ PP y * m⁻¹ := by
  first | exact @GlobalTheory.NestedStab.redFn_conj_of_stab_le | exact GlobalTheory.NestedStab.redFn_conj_of_stab_le | (intros; apply GlobalTheory.NestedStab.redFn_conj_of_stab_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.PlacesDistinct

variable {D : D7}

theorem placeIdem_unique {v : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F}
    (h : IsPlaceIdem D v ε) (h' : IsPlaceIdem D v ε') : ε = ε' := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  obtain ⟨α', rfl, h1', h2'⟩ := h'
  congr 1
  refine RestrictedProduct.ext _ _ fun u => ?_
  by_cases hu : u = v
  · subst hu
    exact h1.trans h1'.symm
  · exact (h2 u hu).trans (h2' u hu).symm

theorem finPart_idem_int {e : AE D} {w : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.L2.NTheta.IsIdemAt e w) :
    finPart D e ∈ intAE D := by
  have h1 := (h.2 1 one_ne_zero).not
  have hw : (1 : 𝓞 D.host.E) ∉ w.asIdeal := fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have := not_not.1 (h1.1 hw)
  simpa using this

theorem conj_mem_of {e e' : AE D} {w w' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.L2.NTheta.IsIdemAt e w)
    (h' : Formalism.L2.NTheta.IsIdemAt e' w') (hsum : e + cA D e = e' + cA D e') {x x' : 𝓞 D.host.E} (hx' : (x' : D.host.E) = star (x : D.host.E))
    (hx0 : x ≠ 0) (hxw : x ∈ w.asIdeal) (hxw' : x ∉ w'.asIdeal) : x' ∈ w'.asIdeal := by
  have hx'0 : x' ≠ 0 := by
    intro h0
    apply hx0
    have : star (x : D.host.E) = 0 := by rw [← hx', h0]; rfl
    exact RingOfIntegers.coe_eq_zero_iff.mp (star_eq_zero.mp this)
  have hN : finPart D (e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D := (h.2 x hx0).1 hxw
  have hI' : finPart D (e' * incA D ((x : D.host.E)⁻¹)) ∈ intAE D := not_not.1 (mt (h'.2 x hx0).2 hxw')
  have he := finPart_idem_int h
  have hee : e = e * e' + e * cA D e' := by
    rw [← mul_add, ← hsum, mul_add, h.1.1, h.1.2.1, add_zero]
  have hsplit : e * incA D ((x : D.host.E)⁻¹) =
      e * (e' * incA D ((x : D.host.E)⁻¹)) + e * (cA D e' * incA D ((x : D.host.E)⁻¹)) := by
    conv_lhs => rw [hee]
    ring
  have hA : finPart D (e * (e' * incA D ((x : D.host.E)⁻¹))) ∈ intAE D := by
    rw [map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE he hI'
  have hB : finPart D (cA D e' * incA D ((x : D.host.E)⁻¹)) ∉ intAE D := by
    intro hB
    apply hN
    rw [hsplit, map_add]
    refine add_mem hA ?_
    rw [map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE he hB
  have hC : cA D e' * incA D ((x : D.host.E)⁻¹) = cA D (e' * incA D ((x' : D.host.E)⁻¹)) := by
    rw [map_mul, GlobalTheory.FinPl.FrameLat.cA_incA, hx', star_inv₀, star_star]
  rw [hC, GlobalTheory.FinPl.FrameLat.cA_int_iff] at hB
  exact (h'.2 x' hx'0).2 hB

theorem prime_eq {e e' : AE D} {w w' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.L2.NTheta.IsIdemAt e w)
    (h' : Formalism.L2.NTheta.IsIdemAt e' w') (hsum : e + cA D e = e' + cA D e') {π π' : 𝓞 D.host.E}
    (hπ' : (π' : D.host.E) = star (π : D.host.E)) (hw : π ∈ w.asIdeal) (hw' : π ∈ w'.asIdeal)
    (hc : π' ∉ w'.asIdeal) : w = w' := by
  by_contra hne
  have hnle : ¬ w.asIdeal ≤ w'.asIdeal := by
    intro hle
    apply hne
    exact HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top hle)
  obtain ⟨x₀, hx₀w, hx₀w'⟩ := Set.not_subset.1 hnle
  have hx₀0 : x₀ ≠ 0 := fun h0 => hx₀w' (h0 ▸ w'.asIdeal.zero_mem)
  have hy : π + x₀ ∉ w'.asIdeal := fun hm => hx₀w' (by simpa using w'.asIdeal.sub_mem hm hw')
  have hy0 : π + x₀ ≠ 0 := fun h0 => hy (h0 ▸ w'.asIdeal.zero_mem)
  obtain ⟨c₀, hc₀⟩ : ∃ c : 𝓞 D.host.E, (c : D.host.E) = star (x₀ : D.host.E) :=
    ⟨⟨star (x₀ : D.host.E), (x₀.2).map (starRingEnd D.host.E).toIntAlgHom⟩, rfl⟩
  have h1 : c₀ ∈ w'.asIdeal := conj_mem_of h h' hsum hc₀ hx₀0 hx₀w hx₀w'
  have h2 : π' + c₀ ∈ w'.asIdeal :=
    conj_mem_of h h' hsum (x := π + x₀) (by push_cast; rw [star_add]; exact congrArg₂ (· + ·) hπ' hc₀) hy0 (w.asIdeal.add_mem hw hx₀w) hy
  exact hc (by simpa using w'.asIdeal.sub_mem h2 h1)

end GlobalTheory.AdForm.PlacesDistinct

open GlobalTheory.AdForm.PlacesDistinct in

theorem GlobalTheory.AdForm.StdT.places_injective : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → Function.Injective fun i => (p i).v := by
  intro B X I _ _ l Z u k _ _ _ _ ι p β Q L hS
  obtain ⟨⟨e, he⟩, -⟩ := hS
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := hPr.piT_cop u
  have hne : X.piT u ≠ 0 := by
    intro h0
    rw [h0, map_zero, isCoprime_zero_left] at hcop
    exact not_isUnit_zero hcop
  intro i i' hv
  have hv : (p i).v = (p i').v := hv
  apply e.injective
  apply Subtype.ext
  have hmem : ∀ j, X.piT u ∈ (e j).1.asIdeal := fun j => (Formalism.L2.Col.mem_divs hne _).1 (e j).2
  obtain ⟨ε, hε, hε'⟩ := (p i).above
  obtain ⟨ε', hε2, hε2'⟩ := (p i').above
  rw [hv] at hε
  have hsum : (p i).e + cA (I.rec7 l Z) (p i).e = (p i').e + cA (I.rec7 l Z) (p i').e := by
    rw [hε', hε2', placeIdem_unique hε hε2]
  refine prime_eq (he i) (he i') hsum (π := X.piT u) (π' := B.fields.conjO (X.piT u)) rfl (hmem i) (hmem i') ?_
  intro hc
  obtain ⟨a, b, hab⟩ := hcop
  exact (e i').1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ (e i').1.asIdeal.add_mem (Ideal.mul_mem_left _ a (hmem i')) (Ideal.mul_mem_left _ b hc)))

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StpTopIdxEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.TwDat.Is

theorem stp_top_idx_eq {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι)
    (b b' : (I.stp u a B.R.m).β) : b = b' := by
  show (b : Idx I.sel (I.tup a) (I.idx a) B.R.m) = b'
  obtain ⟨x, hx⟩ := b
  obtain ⟨y, hy⟩ := b'
  have h1 : x = none := by simpa using hx
  have h2 : y = none := by simpa using hy
  subst h1; subst h2; rfl

theorem chOf_top_eq : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ (c₀ : (I.stp u a B.R.m).Cl) (β : Ch₀ B.R.m), A.chOf B.R.m c₀ = β := by
  intro B X I _ _ l Z u a Ch₀ A hA c₀ β
  obtain ⟨c, rfl⟩ := hA.chOf_onto B.R.m le_rfl β
  exact ((hA.reads B.R.m le_rfl).key c₀ c).2
    ⟨stp_top_idx_eq I u a _ _, GlobalTheory.Mem.Col2.ChEx.cos_of_neT I (by omega) _ _⟩

end GlobalTheory.AdForm.TwDat.Is
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaDatumFockVectorsAreFockVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftFockVec

open GlobalTheory.FockIndep GlobalTheory.OrientedHeis

theorem ptAt_isFockVec : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ Q, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (ptAt R i σ BW f Q) := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h Q
  have h' := h
  obtain ⟨-, -, -, -, -, -, -, hlv, hpt, -, -⟩ := h'
  obtain ⟨⟨hψ, hv⟩, -⟩ := hlv
  have hθ : IsInfFam R.θ := hv.inf
  obtain ⟨⟨p, hp⟩, -⟩ := hv.norm
  obtain ⟨-, hθf, hS, hvac⟩ := GlobalTheory.LiftFockVac.levVec_fockVac R F i t σ s P cμ cη m ω BW f₀ f c io h p.1 p.2 hp
  have hT : ∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i σ) τ) := GlobalTheory.FrameEquiv.isCartanInv_cart_model (R.MW i σ)
  set Ap := aPlusAll (heisO R.ψ (Vc D i) (Wc D i)) R.θ (fun τ => cplxO ((fun _ => (1 : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ)) τ) (cart (R.MW i σ) τ)) (R.BV i) BW with hAdef
  have hadd : ∀ g g', IsThetaFunO R.ψ (Vc D i) (Wc D i) g → IsThetaFunO R.ψ (Vc D i) (Wc D i) g' →
      IsThetaFunO R.ψ (Vc D i) (Wc D i) (g + g') := fun _ _ => theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO R.ψ (Vc D i) (Wc D i) g → IsThetaFunO R.ψ (Vc D i) (Wc D i) (a • g) :=
    fun a _ => theta_smul a
  have hA : ∀ k g, IsThetaFunO R.ψ (Vc D i) (Wc D i) g → IsThetaFunO R.ψ (Vc D i) (Wc D i) (Ap k g) :=
    fun _ _ h => aPlus_theta hψ hθ _ _ _ h
  have hc : ∀ i' j g, IsThetaFunO R.ψ (Vc D i) (Wc D i) g → Ap i' (Ap j g) = Ap j (Ap i' g) :=
    fun i' j _ h => aPlus_comm' hψ hθ i'.1 _ hS hT j.1 _ h
  have Aadd : ∀ i' g g', IsThetaFunO R.ψ (Vc D i) (Wc D i) g → IsThetaFunO R.ψ (Vc D i) (Wc D i) g' →
      Ap i' (g + g') = Ap i' g + Ap i' g' :=
    fun i' _ _ h h' => aPlus_add hψ hθ i'.1 _ _ h h'
  have Asm : ∀ i' (a : ℂ) g, IsThetaFunO R.ψ (Vc D i) (Wc D i) g → Ap i' (a • g) = a • Ap i' g :=
    fun i' a _ h => aPlus_smul hψ hθ i'.1 _ _ a h
  have hpt' : ∀ Q', ptAt R i σ BW f Q' = pureTensorL Ap f Q' := fun _ => rfl
  have hder : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) ℂ),
      ∃ c' : FVar D (Wc D i).rank (Vc D i).rank → ℂ, ∀ Q',
      annih (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i σ) τ)) z (pureTensorL Ap f Q') =
        pureTensorL Ap f (∑ k, c' k • MvPolynomial.pderiv k Q') := by
    intro τ z
    refine ⟨fun k => (fockScale D k.1 : ℂ)⁻¹ * (-(4 * Real.pi * Complex.I) *
      ((omDir (Vc D i) (Wc D i) τ z k.1 (unitMap (R.BV i k.1) (BW k.1) k.2.1 k.2.2) : ℝ) +
        Complex.I * (omDir (Vc D i) (Wc D i) τ (cplxO 1 (cart (R.MW i σ) τ) z) k.1
          (unitMap (R.BV i k.1) (BW k.1) k.2.1 k.2.2) : ℝ))), fun Q' => ?_⟩
    exact GlobalTheory.ArchRec.DerFock.pure_deriv hadd hsm hA hc Aadd Asm
      (fun _ _ h h' => annih_add hψ hθ _ _ _ h h') (fun a _ h => annih_smul hψ hθ _ _ _ a h)
      (fun j _ h => GlobalTheory.FockIndep.annih_aPlus hψ hθ τ z hS hT j.1 _ h) hθf (hvac τ z) Q'
  refine ⟨hpt Q, Q.totalDegree + 1, fun l hl => ?_⟩
  have key : ∀ l : List (D.what₂.Tau × Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) ℂ),
      ∃ Q' : MvPolynomial (FVar D (Wc D i).rank (Vc D i).rank) ℂ,
      l.foldr (fun p g => annih (heisO R.ψ (Vc D i) (Wc D i)) R.θ p.1 (cplxO 1 (cart (R.MW i σ) p.1)) p.2 g)
          (pureTensorL Ap f Q) = pureTensorL Ap f Q' ∧
        ∀ n : FVar D (Wc D i).rank (Vc D i).rank →₀ ℕ, Q.totalDegree < n.degree + l.length → Q'.coeff n = 0 := by
    intro l
    induction l with
    | nil =>
      refine ⟨Q, rfl, fun n hn => MvPolynomial.coeff_eq_zero_of_totalDegree_lt ?_⟩
      have h2 : Q.totalDegree < n.degree := by simpa using hn
      exact h2
    | cons q l ih =>
      obtain ⟨Q', hQ', hQc⟩ := ih
      obtain ⟨c', hc'⟩ := hder q.1 q.2
      refine ⟨∑ k, c' k • MvPolynomial.pderiv k Q', ?_, fun n hn => ?_⟩
      · rw [List.foldr_cons, hQ', hc']
      · refine GlobalTheory.FockVecOfVac.coeff_sum_pderiv_eq_zero c' Q' (Q.totalDegree - l.length)
          (fun n' hn' => hQc n' (by omega)) n ?_
        simp only [List.length_cons] at hn
        omega
  obtain ⟨Q', hQ', hQc⟩ := key l
  have hQ0 : Q' = 0 := MvPolynomial.ext _ _ fun n => by
    rw [hQc n (by rw [hl]; omega), MvPolynomial.coeff_zero]
  show l.foldr _ (ptAt R i σ BW f Q) = 0
  rw [hpt', hQ', hQ0, map_zero]

end GlobalTheory.LiftFockVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFourierSumEqSumHeisenbergTranslatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFourierSum_eq_sum_heisenberg_translates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) (f₀ Φ f : WO S T → ℂ) (ι : Type) (s : Finset ι) (K : ι → ℂ) (xs ys : ι → WO S T) (k : ℕ), 0 < k → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f → (∀ i ∈ s, IsHalf e (xs i)) → (∀ i ∈ s, IsHalf (cA D e) (ys i)) → (∀ i ∈ s, ∀ u ∈ Λ, ψ (symplO S T (k • u) (ys i)) = 1) → (∀ t, Φ t = ∑ i ∈ s, K i * (ψ (symplO S T (t + xs i) (ys i)) * halfInd e Λ (t + xs i))) → f = ∑ i ∈ s, K i • heisO ψ S T (xs i) (heisO ψ S T (ys i) f₀) := by
  first | exact @GlobalTheory.HalfFourier.thetaAt_eq_sum_heis_translates | exact GlobalTheory.HalfFourier.thetaAt_eq_sum_heis_translates | (intros; apply GlobalTheory.HalfFourier.thetaAt_eq_sum_heis_translates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerFockProductEqProdRealPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaInner_fockProduct_eq_prod_realPlaces : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ (m : Measure (WO V W)) (X : Set (WO V W)), IsCovolOne (ratL W V) m X → ∀ f, IsVacVec ψ θ M M' f → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f ≠ 0 ∧ ∀ (P : D.what₂.Tau → LPol W.rank V.rank), ∀ g ∈ GinfC V, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (g, 1) (ptOf ψ θ M M' f (glue P))) (ptOf ψ θ M M' f (glue P)) = GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f * ∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (atTau θ V τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g), 1) (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ) f (P τ))) (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ) f (P τ)) / GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f := by
  first | exact @GlobalTheory.FockProdCoef.ipTh_ptOf_glue | exact GlobalTheory.FockProdCoef.ipTh_ptOf_glue | (intros; apply GlobalTheory.FockProdCoef.ipTh_ptOf_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftDatumIsNonzeroFockVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftDatum_isNonzeroFockVacuum : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → l2 μ 𝓧 f f ≠ 0 ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ (∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1) ∧ ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i σ) τ)) f := by
  first | exact @GlobalTheory.LiftFockVac.levVec_fockVac | exact GlobalTheory.LiftFockVac.levVec_fockVac | (intros; apply GlobalTheory.LiftFockVac.levVec_fockVac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftFockVectorsSphericalPrincipalFixedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftFockVectors_spherical_principalFixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t P, (∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ)) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ptP i t P) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff R.ψ (Vc D i) (Wc D i) (GlobalTheory.AdelicU.frameLat (Vc D i)) (GlobalTheory.AdelicU.frameLat (Wc D i)) (under (R.Pg ∪ R.Q t)) (R.ptP i t P) ∧ ∀ κ ∈ prin (Vc D i) (R.βV i) (R.Pg ∪ R.Q t), R.ωP i t (κ, 1) (R.ptP i t P) = R.ptP i t P := by
  first | exact @GlobalTheory.ThPFock.fock_sph_prin | exact GlobalTheory.ThPFock.fock_sph_prin | (intros; apply GlobalTheory.ThPFock.fock_sph_prin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsNeZeroOfLValueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftUpwards_ne_zero_of_lValue : ∀ D : D7, GlobalTheory.Core.Rk.IP.HeckeForm D → MetEx D → LevFacts D → ZetaNe D → UpNe D := by
  first | exact @GlobalTheory.ChainOnto.upNe_of_heckeForm | exact GlobalTheory.ChainOnto.upNe_of_heckeForm | (intros; apply GlobalTheory.ChainOnto.upNe_of_heckeForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrcSingleApply
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem trc_single_apply {D : D7} {V : HSp D} (b : GA D V) (ε : ℂ) (f : GA D V → ℂ) (x : GA D V) :
    trc (Finsupp.single b ε) f x = ε * f (x * b) := by
  unfold trc
  by_cases hε : ε = 0
  · simp [hε]
  · rw [Finsupp.support_single_ne_zero _ hε]
    simp [GlobalTheory.MixPer.rTrans]
end GlobalTheory.AdForm

noncomputable section
namespace GlobalTheory.AdForm

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z))
  (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) {t : T} (r : RowCh R P u g t) (k : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u a))
  (tl : ColT I l u a B.R.m → CXP R P t → ℂ)

def ellTop (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)) (ε : ℂ)
    (G' : CXP R P t → (I.per l u a).Mt) (c : (I.fm l u a).clsP) (f : CXP R P t) :
    (FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) →ₗ[ℂ] ℂ :=
  (ε * (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ)) •
    ((I.per l u a).period.flip (G' f) ∘ₗ eW.symm.toLinearMap ∘ₗ
      LinearMap.single ℂ (fun _ : (I.fm l u a).clsP => FrP (I.rec7 l Z) → ℂ) c ∘ₗ
      LinearMap.funLeft ℂ ℂ (fun y : FrP (I.rec7 l Z) => (⟨y.1, y.2⟩ : FrN (I.rec7 l Z) (B.R.N B.R.m - 1))))

theorem ellTop_apply (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)) (ε : ℂ)
    (G' : CXP R P t → (I.per l u a).Mt) (c : (I.fm l u a).clsP) (f : CXP R P t) (φ : FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) :
    ellTop R P eW ε G' c f φ = ε * (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ) *
      (I.per l u a).period (eW.symm (Pi.single c (fun y : FrP (I.rec7 l Z) => φ ⟨y.1, y.2⟩))) (G' f) := by
  simp only [ellT, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, LinearMap.flip_apply,
    LinearEquiv.coe_coe, LinearMap.coe_single, smul_eq_mul]
  rfl

@[reducible] def clsTop (s : ℕ → ℂ)
    (J : SmT R.MX → GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ)
    (UT : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) (h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X')
    (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)) (ε : ℂ) (G' : CXP R P t → (I.per l u a).Mt) :
    ClsT (realOf u R g s J) (tupOf R P u g t r k tl) where
  cl := (I.fm l u a).clsP
  U := UT
  h := h
  ell := fun _ _ _ c f => ellTop R P eW ε G' c f

end GlobalTheory.AdForm
end
end

