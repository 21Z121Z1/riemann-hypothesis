import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumTieNumberFieldPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1795
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1781
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1744
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1782
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumTieHodgeTateKernel
section
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

namespace GlobalTheory.DetInv.FinrankMapAddFinrankInf

theorem finrank_map_add_finrank_inf {C V V' : Type} [Field C] [AddCommGroup V] [Module C V]
    [AddCommGroup V'] [Module C V'] [FiniteDimensional C V] (f : V →ₗ[C] V') (U : Submodule C V) :
    Module.finrank C U =
      Module.finrank C ↥(LinearMap.ker f ⊓ U) + Module.finrank C (U.map f) := by
  rw [← LinearMap.finrank_range_add_finrank_ker (f.domRestrict U), LinearMap.range_domRestrict,
    LinearMap.ker_domRestrict, add_comm, ← Submodule.finrank_map_subtype_eq,
    Submodule.map_comap_subtype, inf_comm]

theorem shift_eq_of_isTie : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (ε : PreTilt O p) (h : ℕ) (D : Datum ε h (ℤ_[p] ⊗[ℤ] 𝓞 E)) (φ : P.V ≃ₗ[C] (Fin h → C)), IsPrimitiveRoot (root ε).untilt p → IsTie P D (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom φ → ∀ (σ : ℤ_[p] ⊗[ℤ] 𝓞 E →+* O) (ψ : E →+* C) (r : NNReal), σ.comp (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom = embO P.integers ψ → IsShift C v D σ r → ∀ (a q : ℕ) (x : Fin a → P.V) (y : Fin q → P.V) (g : Matrix (Fin a) (Fin a) C) (g' : Matrix (Fin q) (Fin q) C), Module.finrank C (P.eigW (embO P.integers ψ)) = a → Module.finrank C (P.eigW ((embO P.integers ψ).comp (starRingEnd (𝓞 E)))) = q → Submodule.span O (Set.range x) = P.wRec (embO P.integers ψ) → Submodule.span O (Set.range y) = P.wRec ((embO P.integers ψ).comp (starRingEnd (𝓞 E))) → IsLatBasis C (open Classical in P.latTQuot (σ := fun φ' : E →+* C => embO P.integers φ') (isSplitting_embO P.integers) ψ) (fun i => ∑ j, g i j • x j) → IsLatBasis C (P.latTSub ((embO P.integers ψ).comp (starRingEnd (𝓞 E)))) (fun i => ∑ j, g' i j • y j) → v g.det = r * v g'.det ∧ g'.det ≠ 0 ∧ Module.finrank C (eig C (actT D) σ) = a + q := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ E _ _ _ P ε h D φ hε T σ ψ r hσ hr a q x y g g' ha hq hx hy hg hg'
  classical
  have hv := P.integers
  obtain ⟨hE1, hE2, hE3, -⟩ :=
    (PadicInclusionHoms.eig_lattices_of_isTie p C v O E P ε h D φ hε T).2.2.2 σ ψ hσ
  obtain ⟨m, k, hm, hk, hkg⟩ := GlobalTheory.T.datum_tie_lattice_compatibility p C v O E P ε h D φ hε T σ ψ hσ q y g' hq hy hg'
  haveI : FiniteDimensional C P.V := φ.symm.finiteDimensional
  have hW : ∀ z, z ∈ P.W ↔ φ z ∈ LinearMap.ker (alC C D) := T.ker
  have hxW : ∀ j, x j ∈ P.eigW (embO P.integers ψ) := by
    intro j
    have h1 := P.wRec_le _ (hx.le (Submodule.subset_span ⟨j, rfl⟩))
    refine ⟨?_, h1.2⟩
    obtain ⟨_, ⟨u, rfl⟩, hu⟩ := (T.lie _).1 h1.1
    refine (hW _).2 ?_
    rw [(ker_bC_eq_range_alC_and_ker_alC_eq_range_bC p C v O hv ε hε _ h D).2, ← hu]
    refine ⟨incl C h u, funext fun i => ?_⟩
    simp [bC, redC, incl, Datum.bb, Matrix.mulVec, dotProduct, map_sum]
  have hle : Submodule.span C (Set.range fun i => ∑ j, g i j • x j) ≤
      Submodule.span C (Set.range x) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hle' : Submodule.span C (Set.range x) ≤ P.eigW (embO P.integers ψ) :=
    Submodule.span_le.2 (Set.range_subset_iff.2 hxW)
  have hsp : Submodule.span C (Set.range fun i => ∑ j, g i j • x j) = P.eigW (embO P.integers ψ) :=
    Submodule.eq_of_le_of_finrank_eq (hle.trans hle')
      (by rw [finrank_span_eq_card hg.1, ha, Fintype.card_fin])
  have hxi : LinearIndependent C x := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, le_antisymm hle' (hsp.ge.trans hle),
      ha, Fintype.card_fin]
  have hmap : ∀ {n : ℕ} (w : Fin n → P.V), Submodule.span O (Set.range fun i => φ (w i)) =
      (Submodule.span O (Set.range w)).map ((φ : P.V →ₗ[C] (Fin h → C)).restrictScalars O) := by
    intro n w
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have b1 : IsBasisOf C (lieSub C D σ) (fun i => φ (x i)) :=
    ⟨hxi.map' (φ : P.V →ₗ[C] (Fin h → C)) φ.ker, by rw [hmap, hx, hE2]⟩
  have b2 : IsBasisOf C (wQuot C D σ) (fun i => ∑ j, g i j • φ (x j)) := by
    have e : (fun i => ∑ j, g i j • φ (x j)) = fun i => φ (∑ j, g i j • x j) := by
      funext i
      simp only [map_sum, map_smul]
    rw [e]
    refine ⟨hg.1.map' (φ : P.V →ₗ[C] (Fin h → C)) φ.ker, ?_⟩
    rw [hmap, hg.2, hsp, wQuot, ← hE3]
    refine le_antisymm ?_ ?_
    · rintro _ ⟨z, ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨z, h1, rfl⟩, (hW z).1 h2.1⟩
    · rintro _ ⟨⟨z, h1, rfl⟩, h2⟩
      refine ⟨z, ⟨h1, (hW z).2 h2, ?_⟩, rfl⟩
      obtain ⟨t, -, rfl⟩ := h1
      exact EigenSplit.proj_mem (isSplitting_embO (E := E) hv) P.actV ψ t
  have hs := hr a q _ g m k b1 b2 hm hk
  refine ⟨?_, right_ne_zero_of_mul_eq_one hkg, ?_⟩
  · rw [← hs, mul_assoc, ← map_mul, hkg, map_one, _root_.mul_one]
  · have e1 : LinearMap.ker (alC C D) ⊓ eig C (actT D) σ =
        (P.eigW (embO P.integers ψ)).map (φ : P.V →ₗ[C] (Fin h → C)) := by
      rw [← hE1]
      refine le_antisymm ?_ ?_
      · rintro _ ⟨h1, z, h2, rfl⟩
        exact ⟨z, ⟨(hW z).2 h1, h2⟩, rfl⟩
      · rintro _ ⟨z, h1, rfl⟩
        exact ⟨(hW z).1 h1.1, z, h1.2, rfl⟩
    have e2 : (eig C (actT D) σ).map (alC C D) =
        Submodule.span C (Set.range fun i => ∑ j, k i j • m j) := by
      refine le_antisymm ?_ (Submodule.span_le.2 ?_)
      · rw [← hE1]
        rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        obtain ⟨c, hc, hcz⟩ := P.exists_smul_mem_latT z
        have hc' : algebraMap O C c ≠ 0 := fun h0 => hc (hv.hom_inj (by rw [h0, map_zero]))
        have h1 := P.latTSub_le_latTQuot (σ := fun φ' : E →+* C => embO P.integers φ')
          (isSplitting_embO P.integers) ψ (x := algebraMap O C c • z)
          ((mem_eigSubLat _).2 ⟨by rwa [algebraMap_smul], Submodule.smul_mem _ _ hz⟩)
        have h2 : alC C D (φ (algebraMap O C c • z)) ∈ alQuot C D σ :=
          ⟨_, hE3.le ⟨_, h1, rfl⟩, rfl⟩
        rw [← hk.2, map_smul, map_smul] at h2
        exact (Submodule.smul_mem_iff _ hc').1 (Submodule.span_le_restrictScalars O C _ h2)
      · rintro _ ⟨i, rfl⟩
        obtain ⟨z, hz, e⟩ := hk.2.le (Submodule.subset_span ⟨i, rfl⟩)
        exact ⟨z, hz.1, e⟩
    rw [finrank_map_add_finrank_inf (alC C D), e1, e2, LinearEquiv.finrank_map_eq, ha,
      finrank_span_eq_card hk.1, Fintype.card_fin]

end GlobalTheory.DetInv.FinrankMapAddFinrankInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleWeightNatural
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.WeightNat

theorem weight_nat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A A' WW : HSp D) (FA : GlobalTheory.ChainFr.Fr A) (FW : GlobalTheory.ChainFr.Fr WW)
    (a b : D.what₂.Tau → ℚ) (α β : (Formalism.L2.Theta.AE D)ˣ →* Circle) (ωA : GlobalTheory.Grid.WRep A WW), IsInfFam θ →
    (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) A.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) WW.rank 0) →
    GlobalTheory.SquareComm.IsTriple A A' WW α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
    GlobalTheory.Grid.IsWeil ψ true A WW β (β / α) ωA → (∃ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f ∧ f ≠ 0) →
    ∃ n₀ : D.what₂.Tau → ℕ, ∀ τ, (n₀ τ : ℚ) = b τ - a τ - (WW.rank : ℚ) / 2 := by
  intro D ψ θ A A' WW FA FW a b α β ωA hθ hA hW hT hexp hWeil hf
  obtain ⟨f, hf, hf0⟩ := hf
  have key : ∀ τ, ∃ z : ℤ, (z : ℚ) = b τ - a τ - (WW.rank : ℚ) / 2 ∧ 0 ≤ z := by
    intro τ
    obtain ⟨a', b', ha', hb', hgap⟩ := hT.gap τ
    have e1 := GlobalTheory.Mem.HeckeExp.hasInfExp_unique ha' (hexp τ).1
    have e2 := GlobalTheory.Mem.HeckeExp.hasInfExp_unique hb' (hexp τ).2
    have hdiv := GlobalTheory.RealQuot.hasInfExp_div D α β τ (a τ) (b τ) (hexp τ).1 (hexp τ).2
    obtain ⟨x, y, hx, -, -⟩ := GlobalTheory.CompactFockAction.compactFockAll D _ WW (GlobalTheory.SquareComm.frSgn true FA) FW θ ψ β (β / α)
      (ωA.toSgn true) f τ (b τ) (b τ - a τ) hθ hWeil (hexp τ).2 hdiv hf hf0
    obtain ⟨p, q, -, hr, -⟩ := hT.sig
    have hpos : 0 < A.rank := by omega
    have h1 := hx ⟨0, hpos⟩
    generalize (GlobalTheory.SquareComm.frSgn true FA).ε τ ⟨0, hpos⟩ = e at h1
    have h2 := GlobalTheory.CompactFockAction.card_sign (FW.ε τ) e
    set c := (Finset.univ.filter fun i => FW.ε τ i = e).card
    have hz : ((-(c : ℤ) - x e : ℤ) : ℚ) = b τ - a τ - (WW.rank : ℚ) / 2 := by
      push_cast
      unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.wtS at h1
      cases e <;> simp at h1 h2 <;> linarith
    have hq : (0 : ℚ) < b τ - a τ - (WW.rank : ℚ) / 2 := by
      rw [← e1, ← e2]; linarith
    refine ⟨-(c : ℤ) - x e, hz, ?_⟩
    have : (0 : ℚ) ≤ ((-(c : ℤ) - x e : ℤ) : ℚ) := by rw [hz]; exact hq.le
    exact_mod_cast this
  choose z hz hz0 using key
  refine ⟨fun τ => (z τ).toNat, fun τ => ?_⟩
  rw [← hz τ]
  exact_mod_cast Int.toNat_of_nonneg (hz0 τ)

end GlobalTheory.WeightNat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthPeriodicOfCosetIndicatorExpansion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DepthUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem nsmul_mem_of_isCosetDatum {t : T} {p : Pair T} {k : ℕ} {d : FinDatum G t p} (h : IsCosetDatum k d)
    {x : WO (G.pS p) (G.pT p)} (hx : d.fn x ≠ 0) : k • x ∈ pairLat G p := by
  obtain ⟨x₀, -, h1, hfn⟩ := h
  rw [hfn] at hx
  obtain ⟨u, hu, -, rfl⟩ := Set.mem_of_indicator_ne_zero hx
  rw [nsmul_add]
  exact add_mem h1 (nsmul_mem (nsmul_mem hu k) k)

theorem fn_add_nsmul_of_isCosetDatum {t : T} {p : Pair T} {k : ℕ} {d : FinDatum G t p} (h : IsCosetDatum k d)
    {u : WO (G.pS p) (G.pT p)} (hu : u ∈ pairLat G p) (hu' : IsHalf d.e u) (x : WO (G.pS p) (G.pT p)) :
    d.fn (x + k • u) = d.fn x := by
  obtain ⟨x₀, -, -, hfn⟩ := h
  rw [hfn]
  by_cases hx : x ∈ halfCoset d.e (pairLat G p) k x₀
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((add_nsmul_mem_halfCoset_iff hu hu').2 hx)]; rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (add_nsmul_mem_halfCoset_iff hu hu').1 hx)]

theorem depthOK_of_isCosetExpansion : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (k : ℕ) (τ : PureDat G t →₀ ℂ), IsCosetExpansion S t Φ β k τ → ∃ e, IsIdemSum e (locPl G t) ∧ ExpWith S t Φ β e τ ∧ DepthOK S t Φ β e k := by
  intro D T L sc G W U S t Φ β k τ h
  obtain ⟨-, ⟨e, he, hP, hsum⟩, hcos⟩ := h
  refine ⟨e, he, ⟨hP, hsum⟩, ?_, ?_⟩
  · intro x y hx hy hne
    unfold flatProd at hne
    rw [← hsum x y hx hy] at hne
    obtain ⟨d, hd, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    beta_reduce at hne
    have h1 : ∏ j, (d.1 j).fn (x j) ≠ 0 := fun h0 => hne (by rw [h0, mul_zero, zero_mul])
    have h2 : ∏ i, (d.2 i).fn (y i) ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
    rw [Finset.prod_ne_zero_iff] at h1 h2
    exact ⟨fun j => nsmul_mem_of_isCosetDatum ((hcos d hd).1 j) (h1 j (Finset.mem_univ _)),
      fun i => nsmul_mem_of_isCosetDatum ((hcos d hd).2 i) (h2 i (Finset.mem_univ _))⟩
  · intro x u y v hx hy hu hv
    have hx' : ∀ j, IsHalf e ((x + k • u) j) := fun j a b => by
      show e * (x j + k • u j) a b = (x j + k • u j) a b
      rw [Matrix.add_apply, mul_add, hx j a b, isHalf_nsmul_of k (hu j).1 a b]
    have hy' : ∀ i, IsHalf e ((y + k • v) i) := fun i a b => by
      show e * (y i + k • v i) a b = (y i + k • v i) a b
      rw [Matrix.add_apply, mul_add, hy i a b, isHalf_nsmul_of k (hv i).1 a b]
    unfold flatProd
    rw [← hsum _ _ hx' hy', ← hsum x y hx hy]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hx1 : ∀ j, (d.1 j).fn ((x + k • u) j) = (d.1 j).fn (x j) := fun j =>
      fn_add_nsmul_of_isCosetDatum ((hcos d hd).1 j) (hu j).2 (((hP d hd).1 j).2.1 ▸ (hu j).1) (x j)
    have hy1 : ∀ i, (d.2 i).fn ((y + k • v) i) = (d.2 i).fn (y i) := fun i =>
      fn_add_nsmul_of_isCosetDatum ((hcos d hd).2 i) (hv i).2 (((hP d hd).2 i).2.1 ▸ (hv i).1) (y i)
    simp only [hx1, hy1]

end GlobalTheory.DepthUnf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDerivativesBorelFrameChangeCanonicalWeightStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_derivatives_borelFrameChange_canonicalWeight : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {P Q : FrPt Xo c K}
    (t : Ix Dw → Kˣ) (hz : z ≫ toFlag M = X.ptY Q) (ht : FrBor t Q P)
    {v v' : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)}
    (hv : IsTanFrame (psiSet H) P v) (hv' : IsTanFrame (psiSet H) Q v')
    {zv zv' : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)}
    (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b)) (hl' : ∀ b, zv' b ≫ toFlag M = X.ptY (v' b))
    (O : M.X.Opens) (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
    (hzv' : ∀ b, ⊤ ≤ zv' b ⁻¹ᵁ O), (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det =
      (∏ ix, t ix ^ exOf Dw (kap Dw) 0 ix).val *
        (Matrix.of fun a b => (evalPt (zv' (tanOrd Dw b)) O (hzv' _) (g a)).snd).det := by
  first | exact @GlobalTheory.CompHS.det_der_frBor | exact GlobalTheory.CompHS.det_der_frBor | (intros; apply GlobalTheory.CompHS.det_der_frBor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDerivativesTangentLiftNeZeroStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_derivatives_tangentLift_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {Q : FrPt Xo c K}
    (hz : z ≫ toFlag M = X.ptY Q) {v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)}
    (hv : IsTanFrame (psiSet H) Q v) {zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)}
    (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b)) (i : M.K.bundle.ι) (O : M.X.Opens) (hO : O ≤ M.K.bundle.U i)
    (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hzO : ⊤ ≤ z ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
    (hJ : evalPt z O hzO (M.K.jacobian i hO g) ≠ 0), (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det ≠ 0 := by
  first | exact @GlobalTheory.CompHS.det_tanLift_ne_zero | exact GlobalTheory.CompHS.det_tanLift_ne_zero | (intros; apply GlobalTheory.CompHS.det_tanLift_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalHermitianFrameSignsPosOfDefinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

open scoped ComplexOrder

namespace GlobalTheory.DefiniteFrame

theorem cT_conj_eq {m p : Type} (M : Matrix m p ℂ) :
    Formalism.UG.cT (starRingEnd ℂ) M = M.conjTranspose := by
  ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]

theorem Jpq_zero (n : ℕ) : Formalism.UG.Jpq n 0 = 1 := by
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [Formalism.UG.Jpq, Matrix.one_apply]
    · exact j.elim0
  · exact i.elim0

theorem posSemidef_of_hasSignature {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.UG.HasSignature G n 0) : G.PosSemidef := by
  obtain ⟨e, P, hP⟩ := h
  rw [cT_conj_eq, Jpq_zero] at hP
  set Q : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ := P.inv
  have hPQ : P.val * Q = 1 := by
    exact P.val_inv
  have hR : G.reindex e e = Q.conjTranspose * 1 * Q := by
    rw [← hP]
    calc G.reindex e e = (P.val * Q).conjTranspose * G.reindex e e * (P.val * Q) := by
          rw [hPQ]; simp
      _ = Q.conjTranspose * (P.val.conjTranspose * G.reindex e e * P.val) * Q := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
  have hpsd : (G.reindex e e).PosSemidef := by
    rw [hR]; exact Matrix.PosSemidef.one.conjTranspose_mul_mul_same Q
  have h2 := hpsd.submatrix e
  have : (G.reindex e e).submatrix e e = G := by
    ext i j; simp
  rwa [this] at h2

end GlobalTheory.DefiniteFrame

open Matrix in

theorem GlobalTheory.DefiniteFrame.frame_signs_pos : ∀ (D : D7) (V : HSp D) (F : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau),
    Formalism.UG.HasSignature (gramAt D V τ) V.rank 0 → ∀ j, F.ε τ j = true := by
  intro D V F τ hs j
  have hG := GlobalTheory.DefiniteFrame.posSemidef_of_hasSignature hs
  have hu : IsUnit (F.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (F.fr_unit τ)
  have hJ : Formalism.REAL.Jm (F.ε τ) = ((F.fr τ)⁻¹).conjTranspose * gramAt D V τ * (F.fr τ)⁻¹ := by
    rw [← F.fr_gram τ, Matrix.conjTranspose_nonsing_inv]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul (F.fr τ)ᴴ (by rw [Matrix.det_conjTranspose]; exact hu.star), Matrix.one_mul]
  have hpsd : (Formalism.REAL.Jm (F.ε τ)).PosSemidef := by
    rw [hJ]; exact hG.conjTranspose_mul_mul_same _
  have hd := hpsd.diag_nonneg (i := j)
  by_contra hne
  simp only [Bool.not_eq_true] at hne
  simp [Formalism.REAL.Jm, hne] at hd
  norm_num at hd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalIntegralHeisenbergTranslateIntegralIndic
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.InertLagInd

variable {F : Type} [Field F] [NumberField F] {v : Pl F} {κ : Type} [Fintype κ]

theorem invOf_two_mem (h : (2 : 𝓞 F) ∉ v.asIdeal) : ⅟(2 : Fv F v) ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation F (algebraMap (𝓞 F) F 2) = 1 := (v.valuation_eq_one_iff_notMem (K := F)).2 h
  rw [map_ofNat] at h1
  have h2 : Valued.v (algebraMap F (Fv F v) (2 : F)⁻¹) = v.valuation F (2 : F)⁻¹ :=
    v.valuedAdicCompletion_eq_valuation' _
  simp only [map_inv₀] at h2
  rw [h1, inv_one, map_ofNat] at h2
  rw [invOf_eq_inv, map_inv₀, h2]

theorem schr_box_apply (ψ : AddChar (Fv F v) ℂ) (φ₁ φ₂ : (κ → Fv F v) → ℂ) (w : (κ → Fv F v) × (κ → Fv F v))
    (x : κ → Fv F v) :
    schr ψ (Sum.elim w.1 0, Sum.elim w.2 0) (boxFun φ₁ φ₂) (Sum.elim x x) =
      ψ (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * (φ₁ (x + w.1) * φ₂ x) := by
  simp only [schr, boxFun, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero]
  congr 2
  all_goals (congr 1; funext i; simp)

end GlobalTheory.InertLagInd

namespace GlobalTheory.InertLagInd

theorem diagW_box_indicator : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ]
    (ψ : AddChar (AF F) ℂ), PsiUnr ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ φ₀ ∈ SB (κ → Fv F v), ∃ c : ℂ, c ≠ 0 ∧ ∃ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U ∧ IsCompact U ∧ 0 ∈ U ∧
      ∀ w, diagW (psiAt ψ v) μ (boxFun φ₀ φ₀) w = U.indicator (fun _ => c) w := by
  intro F _ _ v κ _ ψ hψ h2 μ hμ
  classical
  letI : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨S, hS⟩ : ∃ S : Set (κ → Fv F v), S = {x | ∀ k, x k ∈ v.adicCompletionIntegers F} := ⟨_, rfl⟩
  have hmem : ∀ x, x ∈ S ↔ ∀ k, x k ∈ v.adicCompletionIntegers F := fun x => by subst hS; rfl
  have hpi : S = Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext x; simp [hmem]
  have hSo : IsOpen S := by
    rw [hpi]; exact isOpen_set_pi Set.finite_univ (fun _ _ => Valued.isOpen_integer _)
  have hSc : IsCompact S := by
    rw [hpi]; exact isCompact_univ_pi (fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v)
  have h0S : (0 : κ → Fv F v) ∈ S := (hmem 0).2 fun k => zero_mem _
  have hadd : ∀ {a}, a ∈ S → ∀ x, (x + a ∈ S ↔ x ∈ S) := fun {a} ha x => by
    rw [hmem, hmem]
    rw [hmem] at ha
    exact ⟨fun h k => by simpa using sub_mem (h k) (ha k), fun h k => add_mem (h k) (ha k)⟩
  have hind : ∀ {a}, a ∈ S → ∀ x, S.indicator (1 : (κ → Fv F v) → ℂ) (x + a) = S.indicator 1 x := fun ha x => by
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hadd ha x).2 hx)]; rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (hadd ha x).1 hx)]
  have hψ1 : ∀ y ∈ v.adicCompletionIntegers F, psiAt ψ v y = 1 := fun y hy => by
    rw [psiAt_apply]; simpa using (hψ 1).2 (one_mem _) y hy
  have hφ : S.indicator (1 : (κ → Fv F v) → ℂ) ∈ SB (κ → Fv F v) := by
    rw [hS]; exact GlobalTheory.StdVacuum.indicator_mem_SB v
  refine ⟨S.indicator 1, hφ, ((μ.real S : ℝ) : ℂ), ?_, S ×ˢ S, hSo.prod hSo, hSc.prod hSc, ⟨h0S, h0S⟩, ?_⟩
  · have h1 : μ S ≠ 0 := hSo.measure_ne_zero μ ⟨0, h0S⟩
    have h2' : μ S ≠ ⊤ := hSc.measure_lt_top.ne
    exact Complex.ofReal_ne_zero.2 (by rw [measureReal_def]; exact ENNReal.toReal_ne_zero.2 ⟨h1, h2'⟩)
  intro w
  simp only [diagW, schr_box_apply]
  by_cases hw1 : w.1 ∈ S
  · by_cases hw2 : w.2 ∈ S
    · rw [Set.indicator_of_mem (Set.mem_prod.2 ⟨hw1, hw2⟩)]
      have key : ∀ x, psiAt ψ v (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) *
          (S.indicator 1 (x + w.1) * S.indicator 1 x) = S.indicator (1 : (κ → Fv F v) → ℂ) x := by
        intro x
        rw [hind hw1 x]
        by_cases hx : x ∈ S
        · rw [Set.indicator_of_mem hx, hψ1]
          · simp
          · rw [hmem] at hx hw1 hw2
            exact add_mem (sum_mem fun i _ => mul_mem (hx i) (hw2 i))
              (mul_mem (invOf_two_mem h2) (sum_mem fun i _ => mul_mem (hw1 i) (hw2 i)))
        · simp [Set.indicator_of_notMem hx]
      simp_rw [key]
      rw [show S.indicator (1 : (κ → Fv F v) → ℂ) = S.indicator (fun _ => (1 : ℂ)) from rfl,
        integral_indicator_const _ hSo.measurableSet]
      simp
    · rw [Set.indicator_of_notMem (fun h => hw2 (Set.mem_prod.1 h).2)]
      obtain ⟨i, hi⟩ : ∃ i, w.2 i ∉ v.adicCompletionIntegers F := by
        by_contra h; push_neg at h; exact hw2 ((hmem _).2 h)
      obtain ⟨y, hy, hne⟩ : ∃ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (w.2 i * y) ≠ 1 := by
        by_contra h; push_neg at h; exact hi ((hψ _).1 h)
      have ha : Pi.single i y ∈ S := (hmem _).2 fun k => by
        rw [Pi.single_apply]; split_ifs
        · exact hy
        · exact zero_mem _
      set g : (κ → Fv F v) → ℂ := fun x => psiAt ψ v (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) *
          (S.indicator 1 (x + w.1) * S.indicator 1 x) with hg
      have hshift : ∀ x, g (x + Pi.single i y) = psiAt ψ v (w.2 i * y) * g x := by
        intro x
        simp only [hg]
        rw [add_right_comm, hind ha, hind ha, add_dotProduct, single_dotProduct,
          show x ⬝ᵥ w.2 + y * w.2 i + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2) =
            w.2 i * y + (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) by ring, AddChar.map_add_eq_mul]
        ring
      have hI : ∫ x, g x ∂μ = psiAt ψ v (w.2 i * y) * ∫ x, g x ∂μ := by
        rw [← integral_const_mul, ← integral_add_right_eq_self _ (Pi.single i y)]
        simp only [hshift]
      rw [psiAt_apply] at hI
      have : (1 - psiLoc ψ v (w.2 i * y)) * ∫ x, g x ∂μ = 0 := by rw [sub_mul, one_mul, ← hI, sub_self]
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne.symm)
  · rw [Set.indicator_of_notMem (fun h => hw1 (Set.mem_prod.1 h).1)]
    have hz : ∀ x, psiAt ψ v (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) *
        (S.indicator (1 : (κ → Fv F v) → ℂ) (x + w.1) * S.indicator 1 x) = 0 := by
      intro x
      by_cases hx : x ∈ S
      · have : x + w.1 ∉ S := fun h => hw1 (by rw [add_comm] at h; exact (hadd hx w.1).1 h)
        simp [Set.indicator_of_notMem this]
      · simp [Set.indicator_of_notMem hx]
    simp_rw [hz]
    exact integral_zero _ _

end GlobalTheory.InertLagInd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfSchroedingerTranslatesThetaSumZeroStatement
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_schroedingerTranslates_thetaSum_zero : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
    (∀ w : (κ → AF F) × (κ → AF F), thetaSum F (schr ψ w Φ) = 0) → Φ = 0 := by
  first | exact @GlobalTheory.ThetaInj.main | exact GlobalTheory.ThetaInj.main | (intros; apply GlobalTheory.ThetaInj.main <;> assumption)
end

