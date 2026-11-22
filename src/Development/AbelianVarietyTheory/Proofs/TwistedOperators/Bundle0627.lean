import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0268
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0274
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationXiZeroEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0281
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0397
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMulFirstFactorLagrangianAl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0519
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0600
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0453
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0189
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0378
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0447
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0324
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0500
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultTEqZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0497
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0610
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteNodeCartanOrthonormalBasisAllPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowReal

section DefOnb

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem gramAt_negSp (V : HSp D) (ρ : D.what₂.Tau) : gramAt D (negSp V) ρ = -gramAt D V ρ := by
  unfold gramAt
  rw [negSp_gram]
  exact Matrix.map_neg _ (map_neg (tauE D ρ)) _

theorem isCartanInv_neg {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : IsCartanInv (-G) (-s) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [neg_mul_neg, h1], ?_, ?_⟩
  · rw [Matrix.conjTranspose_neg, neg_mul_neg, Matrix.mul_neg, h2]
  · rw [neg_mul_neg]; exact h3

theorem defNode_cart_onb {μ0 : T} (hL : L.Is μ0) (W : G.Weil) (X : Node) (hX : DefNode D.R.m X) (ρ : D.what₂.Tau) :
    IsCartanInv (gramAt D (G.V X) ρ) (W.cart X ρ) ∧ IsONBasis (gramAt D (G.V X) ρ) (W.cart X ρ) (W.onb X ρ) (G.V X).rank ∧
    IsCartanInv (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) ∧
      IsONBasis (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) (W.onb X ρ) 0 := by
  have hC := W.cart_is X hX.inRange ρ
  have hP : (W.onb X ρ)ᴴ * gramAt D (G.V X) ρ * W.onb X ρ = 1 := posOnb_of_defNode W μ0 hL hX ρ
  obtain ⟨ε, h1, h2⟩ := W.onb_is X hX.inRange ρ
  have hJ : Formalism.REAL.Jm ε = 1 := h1.symm.trans hP
  rw [hJ, Matrix.mul_one] at h2
  have hn : gramAt D (negSp (G.V X)) ρ = -gramAt D (G.V X) ρ := gramAt_negSp _ _
  refine ⟨hC, ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, ?_⟩, ?_, ⟨fun _ => -1, fun a => Or.inr ⟨rfl, Nat.zero_le _⟩, ?_, ?_⟩⟩
  · rw [hP]; simp [Matrix.diagonal_one]
  · rw [h2]; simp [Matrix.diagonal_one]
  · rw [hn]; exact isCartanInv_neg hC
  · rw [hn, Matrix.mul_neg, Matrix.neg_mul, hP]
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, h]
  · rw [Matrix.neg_mul, h2]
    ext i j
    simp [Matrix.mul_diagonal]

theorem defNode_cart_onb_all : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) (X : Node), DefNode D.R.m X → ∀ ρ,
    IsCartanInv (gramAt D (G.V X) ρ) (W.cart X ρ) ∧ IsONBasis (gramAt D (G.V X) ρ) (W.cart X ρ) (W.onb X ρ) (G.V X).rank ∧
    IsCartanInv (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) ∧
      IsONBasis (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) (W.onb X ρ) 0 :=
  fun hL W X hX ρ => defNode_cart_onb hL W X hX ρ

end DefOnb

end GlobalTheory.RowReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridCoreIffFirstRowExtByZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CoreRowLat

variable {D : D7}

theorem gen_negSp (S T : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * (negSp S).gram k j) : WO S T) =
      -(Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) := by
  ext i j; simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem latO_negSp (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P = latO S T LS LT P := by
  apply le_antisymm
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩
    show _ ∈ latO S T LS LT P
    rw [gen_negSp S T α a s t]
    exact neg_mem (AddSubgroup.subset_closure ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩)
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩
    rw [← neg_neg (Matrix.of _), ← gen_negSp S T α a s t]
    exact neg_mem (AddSubgroup.subset_closure ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩)

theorem latO_mul_left {S T T' : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {LT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)} {P : HeightOneSpectrum (𝓞 D.host.F) → Prop}
    (A : Matrix (Fin T'.rank) (Fin T.rank) D.host.E) (hA : ∀ t ∈ LT, A *ᵥ t ∈ LT') {u : WO S T}
    (hu : u ∈ latO S T LS (LT : Set _) P) : (rat A : Mx D T'.rank T.rank) * u ∈ latO S T' LS (LT' : Set _) P :=
  GlobalTheory.OverTgt.mul_mem_latO (rat A) (fun _ hy => GlobalTheory.SeeSaw.CoreGlue.rat_mulVec_mem A hA hy) hu

theorem latO_mul_right {S S' T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LS' : Set (Fin S'.rank → D.host.E)}
    {LT : Set (Fin T.rank → D.host.E)} {P : HeightOneSpectrum (𝓞 D.host.F) → Prop}
    (M : Matrix (Fin S.rank) (Fin S'.rank) D.host.E)
    (hM : ∀ s ∈ LS, ∃ s' ∈ LS', ∀ j, ∑ l, (∑ k, star (s k) * S.gram k l) * M l j = ∑ k, star (s' k) * S'.gram k j)
    {u : WO S T} (hu : u ∈ latO S T LS LT P) : u * (rat M : Mx D S.rank S'.rank) ∈ latO S' T LS' LT P := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩ := hw
    obtain ⟨s', hs', hss⟩ := hM s hs
    refine AddSubgroup.subset_closure ⟨α, hαi, hα, a, ha, s', hs', t, ht, ?_⟩
    ext i j
    rw [Matrix.mul_apply, Matrix.of_apply, ← hss j, Finset.mul_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.of_apply]
    show _ * incA D (M l j) = _
    rw [GlobalTheory.RankZeroVac.incA_tmul', Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_assoc]
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.neg_mul]; exact neg_mem hx

theorem hatMx_mul_left {m m' n : ℕ} (I : Ideal (𝓞 D.host.E)) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {Λ'' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)}
    (A : Matrix (Fin m') (Fin m) D.host.E) (hA : ∀ t ∈ Λ', A *ᵥ t ∈ Λ'') {x : Mx D m n}
    (hx : x ∈ hatMx (I • homLat Λ Λ')) : (rat A : Mx D m' m) * x ∈ hatMx (I • homLat Λ Λ'') := by
  have h := GlobalTheory.TwistHatMx.rat_conj_mem_hatMx I 1 A (fun y hy => by rwa [Matrix.one_mulVec]) hA x hx
  rwa [rat_one, Matrix.mul_one] at h

theorem hatMx_mul_right {m n n' : ℕ} (I : Ideal (𝓞 D.host.E)) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ₁ : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)}
    (N : Matrix (Fin n) (Fin n') D.host.E) (hN : ∀ s ∈ Λ₁, N *ᵥ s ∈ Λ) {x : Mx D m n}
    (hx : x ∈ hatMx (I • homLat Λ Λ')) : x * (rat N : Mx D n n') ∈ hatMx (I • homLat Λ₁ Λ') := by
  have h := GlobalTheory.TwistHatMx.rat_conj_mem_hatMx I N 1 hN (fun y hy => by rwa [Matrix.one_mulVec]) x hx
  rwa [rat_one, Matrix.one_mul] at h

theorem wittEmbedding_preserves_hermitianForm {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (s : Fin S₀.rank → D.host.E) (j : Fin S₀.rank) :
    ∑ l, (∑ k, star ((d.i₀ *ᵥ s) k) * S.gram k l) * d.i₀ l j = ∑ k, star (s k) * S₀.gram k j := by
  have h : Matrix.vecMul (Matrix.vecMul (star (d.i₀ *ᵥ s)) S.gram) d.i₀ = Matrix.vecMul (star s) S₀.gram := by
    rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, d.iso]
  have hj := congrFun h j
  simpa only [Matrix.vecMul, dotProduct, Pi.star_apply] using hj

end GlobalTheory.CoreRowLat

namespace GlobalTheory.CoreRowLat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem std_zA_lat {F : Frames G} (hF : Std F) : (∀ y ∈ G.Λ (.grid 0 0), F.oz.iA *ᵥ y ∈ G.Λ (.core 0)) ∧
    ∀ x ∈ G.Λ (.core 0), F.oz.qA *ᵥ x ∈ G.Λ (.grid 0 0) := by
  have hΛ : G.Λ (.core 0) = sumLat (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι) (L.ΛY 0) G.sp.dec0.a (fun _ => 1) :=
    G.sp.lat0
  have hqi : F.oz.qA * F.oz.iA = 1 := rat_injective (by rw [rat_mul, rat_one]; exact F.oz.pA_jA)
  have hperp := G.sp.dec0.perp
  have hqa : F.oz.qA * G.sp.dec0.a = 0 := by
    change (HSpace.gram (Yc D 0))⁻¹ * (F.oz.iAᴴ * HSpace.gram (G.V (.core 0))) * G.sp.dec0.a = 0
    rw [hF.zA, Matrix.mul_assoc, Matrix.mul_assoc]
    have hp : (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι)ᴴ * HSpace.gram (G.sp.P 0).sp * G.sp.dec0.a = 0 := hperp
    rw [← Matrix.mul_assoc (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι)ᴴ, hp, Matrix.mul_zero]
  refine ⟨fun y hy => ?_, fun x hx => ?_⟩
  · rw [hΛ]
    refine ⟨y, hy, 0, fun _ => (FractionalIdeal.mem_one_iff _).2 ⟨0, map_zero _⟩, ?_⟩
    rw [Matrix.mulVec_zero, add_zero, hF.zA]
  · rw [hΛ] at hx
    obtain ⟨y, hy, u, -, rfl⟩ := hx
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hF.zA, hqi, hqa, Matrix.one_mulVec,
      Matrix.zero_mulVec, add_zero]
    exact hy

theorem std_aJ_lat {F : Frames G} (hF : Std F) (h : 2 * 0 + 2 ≤ D.R.m) :
    (∀ y ∈ G.Λ (.core 1), (F.dJ 0 h).i₀ *ᵥ y ∈ G.Λ (.grid 1 0)) ∧
    (∀ x ∈ G.Λ (.grid 1 0), ∃ y ∈ G.Λ (.core 1), x = (F.dJ 0 h).i₀ *ᵥ y) ∧
    ∀ x ∈ G.Λ (.grid 1 0), (F.dJ 0 h).q0 *ᵥ x ∈ G.Λ (.core 1) := by
  have h1 : 1 ≤ D.R.m := by omega
  have hΛ : G.Λ (.grid 1 0) = sumLat (frameMat (G.V (.grid 1 0)) (G.V (.core 1)) (G.colDec 1 le_rfl h1).ι) (G.Λ (.core 1))
      (G.colDec 1 le_rfl h1).a (stairId (G.pl.stA sc) (G.pl.stAbar sc) (1 - 1)) := G.sp.colLat 1 le_rfl h1
  have hi : (F.dJ 0 h).i₀ = frameMat (G.V (.grid 1 0)) (G.V (.core 1)) (G.colDec 1 le_rfl h1).ι := hF.aJ 0 h
  have hqi : (F.dJ 0 h).q0 * (F.dJ 0 h).i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact (F.dJ 0 h).p0_j0)
  have mem : ∀ x, x ∈ G.Λ (.grid 1 0) ↔ ∃ y ∈ G.Λ (.core 1), x = (F.dJ 0 h).i₀ *ᵥ y := by
    intro x
    rw [hΛ, hi]
    constructor
    · rintro ⟨y, hy, u, -, rfl⟩
      refine ⟨y, hy, ?_⟩
      have : (G.colDec 1 le_rfl h1).a *ᵥ u = 0 := by
        funext i; simp [Matrix.mulVec, dotProduct]
      rw [this, add_zero]
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, 0, fun p => p.elim0, by rw [Matrix.mulVec_zero, add_zero]⟩
  refine ⟨fun y hy => (mem _).2 ⟨y, hy, rfl⟩, fun x hx => (mem x).1 hx, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := (mem x).1 hx
  rwa [Matrix.mulVec_mulVec, hqi, Matrix.one_mulVec]

end GlobalTheory.CoreRowLat

namespace GlobalTheory.CoreRowLat

variable {D : D7}

theorem depthLattice_generalPosition_iff_extByZero {P₁ P₀ Y Lz S : HSp D} (o : OrthDec P₀ Y Lz) (d : HypDec S P₁ 0)
    {Λ₁ : Submodule (𝓞 D.host.E) (Fin P₁.rank → D.host.E)} {Λ₀ : Submodule (𝓞 D.host.E) (Fin P₀.rank → D.host.E)}
    {ΛY : Submodule (𝓞 D.host.E) (Fin Y.rank → D.host.E)} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    (I : Ideal (𝓞 D.host.E)) (Q : AE D → Prop)
    (hiA : ∀ y ∈ ΛY, o.iA *ᵥ y ∈ Λ₀) (hqA : ∀ x ∈ Λ₀, o.qA *ᵥ x ∈ ΛY)
    (hi0 : ∀ y ∈ Λ₁, d.i₀ *ᵥ y ∈ ΛS) (hq0 : ∀ x ∈ ΛS, ∃ y ∈ Λ₁, x = d.i₀ *ᵥ y) (hq0' : ∀ x ∈ ΛS, d.q0 *ᵥ x ∈ Λ₁)
    (a : WO P₁ Y) :
    (o.jA * a ∈ latO (negSp P₁) P₀ (Λ₁ : Set _) (Λ₀ : Set _) (fun _ => True) ∧
      ∀ e : AE D, Q e → e • (o.jA * a) ∈ hatMx (I • homLat Λ₁ Λ₀)) ↔
    (d.ext0 Y a ∈ latO (negSp S) Y (ΛS : Set _) (ΛY : Set _) (fun _ => True) ∧
      ∀ e : AE D, Q e → e • d.ext0 Y a ∈ hatMx (I • homLat ΛS ΛY)) := by
  have hpj : d.p0 * (rat d.i₀ : Mx D _ _) = 1 := d.p0_j0
  have hpA : (rat o.qA : Mx D _ _) * o.jA = 1 := o.pA_jA
  have cB : ∀ x : WO P₁ Y, x * d.p0 * (rat d.i₀ : Mx D _ _) = x := fun x => by
    rw [Matrix.mul_assoc, hpj, Matrix.mul_one]
  have cA : ∀ x : WO P₁ Y, (rat o.qA : Mx D _ _) * (o.jA * x) = x := fun x => by
    rw [← Matrix.mul_assoc, hpA, Matrix.one_mul]
  have ext : d.ext0 Y a = a * d.p0 := rfl
  rw [ext, latO_negSp, latO_negSp]
  have hA1 : o.jA * a ∈ latO P₁ P₀ (Λ₁ : Set _) (Λ₀ : Set _) (fun _ => True) ↔
      a ∈ latO P₁ Y (Λ₁ : Set _) (ΛY : Set _) (fun _ => True) := by
    constructor
    · intro hu
      have := latO_mul_left o.qA hqA hu
      rwa [cA] at this
    · intro hu; exact latO_mul_left o.iA hiA hu
  have hB1 : a ∈ latO P₁ Y (Λ₁ : Set _) (ΛY : Set _) (fun _ => True) ↔
      a * d.p0 ∈ latO S Y (ΛS : Set _) (ΛY : Set _) (fun _ => True) := by
    constructor
    · intro hu
      exact latO_mul_right d.q0 (fun s hs => ⟨d.i₀ *ᵥ s, hi0 s hs, fun j => GlobalTheory.RankZeroVac.wittDecomposition_gram_projection_identity d s j⟩) hu
    · intro hu
      have := latO_mul_right d.i₀ (fun s hs => by
        obtain ⟨y, hy, rfl⟩ := hq0 s hs
        exact ⟨y, hy, fun j => wittEmbedding_preserves_hermitianForm d y j⟩) hu
      rwa [cB] at this
  have hA2 : ∀ e : AE D, e • (o.jA * a) ∈ hatMx (I • homLat Λ₁ Λ₀) ↔ e • a ∈ hatMx (I • homLat Λ₁ ΛY) := by
    intro e
    rw [← Matrix.mul_smul]
    constructor
    · intro hx
      have := hatMx_mul_left I o.qA hqA hx
      rwa [cA] at this
    · intro hx; exact hatMx_mul_left I o.iA hiA hx
  have hB2 : ∀ e : AE D, e • a ∈ hatMx (I • homLat Λ₁ ΛY) ↔ e • (a * d.p0) ∈ hatMx (I • homLat ΛS ΛY) := by
    intro e
    rw [← Matrix.smul_mul]
    constructor
    · intro hx; exact hatMx_mul_right I d.q0 hq0' hx
    · intro hx
      have := hatMx_mul_right I d.i₀ hi0 hx
      rwa [cB] at this
  exact and_congr (hA1.trans hB1) (forall_congr' fun e => imp_congr_right fun _ => (hA2 e).trans (hB2 e))

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem jA_mem_latCore_iff : OnStd fun {D} _ _ _ {G} _ F => ∀ (h : 2 * 0 + 2 ≤ D.R.m) (a : WO (G.V (.core 1)) (Yc D 0)),
    F.oz.jA * a ∈ latCore G 0 ↔ (F.dJ 0 h).ext0 (Yc D 0) a ∈ latRow G 0 := by
  intro D _ T L _ _ sc G W M _ F hF h a
  obtain ⟨hiA, hqA⟩ := std_zA_lat hF
  obtain ⟨hi0, hq0, hq0'⟩ := std_aJ_lat hF h
  exact depthLattice_generalPosition_iff_extByZero F.oz (F.dJ 0 h) G.modul (fun e => IsIdemSum e G.pl.W0) hiA hqA hi0 hq0 hq0' a

end GlobalTheory.CoreRowLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMulFirstFactorLagrangianAlStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalFixingDoublingMatrix_mul_fromBlocks_mul_diagCols : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (c : AE F E) (K K' : Matrix (Fin d) (Fin d) (AE F E)),
    K * K' = 1 → K' * K = 1 → (c * c) • (K - 1) = K - 1 →
    GlobalTheory.SplitDblGen.diagonalFixingDoublingMatrix c d * Matrix.fromBlocks K 0 0 1 * diagCols (E := AE F E) (Fin d) =
      GlobalTheory.SplitDblGen.nMat c K K' * diagCols (E := AE F E) (Fin d) * GlobalTheory.SplitDblGen.tMat c K := by
  first | exact @GlobalTheory.SplitDblGen.diagonalFixingDoubling_mul_firstFactor_lagrangian | exact GlobalTheory.SplitDblGen.diagonalFixingDoubling_mul_firstFactor_lagrangian | (intros; apply GlobalTheory.SplitDblGen.diagonalFixingDoubling_mul_firstFactor_lagrangian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledFirstFactorMemDoubledLatticeStabilizerStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledFirstFactor_mem_doubledLatticeStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d) (v : Pl F),
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, GlobalTheory.InertDbl.inlD σ W k ∈ GlobalTheory.InertDbl.KAtD σ W v := by
  first | exact @GlobalTheory.InertDbl.inlD_mem_KAtD | exact GlobalTheory.InertDbl.inlD_mem_KAtD | (intros; apply GlobalTheory.InertDbl.inlD_mem_KAtD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledStabilizerGeneratedDiagAntidiagSplitPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledStabilizer_generated_diag_antidiag_splitPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → PsiUnr B.ψ v →
    (2 : 𝓞 F) ∉ v.asIdeal → 3 < Ideal.absNorm v.asIdeal → ∀ H : Subgroup (GlobalTheory.DblVac.UD σ G.W),
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PAnti σ G.W → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ G.W v, g ∈ H := by
  first | exact @GlobalTheory.DblVac.gen_diag_anti_split | exact GlobalTheory.DblVac.gen_diag_anti_split | (intros; apply GlobalTheory.DblVac.gen_diag_anti_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledVacuumEigenvalueEqOneSplitPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuum_eigenvalue_eq_one_splitPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → v ∉ X.T → PsiUnr B.ψ v →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.V.J) (incM F G.W.J) G.M.co dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  first | exact @GlobalTheory.DblVacSiegelAny.eigen_eq_one_of_diag_split | exact GlobalTheory.DblVacSiegelAny.eigen_eq_one_of_diag_split | (intros; apply GlobalTheory.DblVacSiegelAny.eigen_eq_one_of_diag_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankThetaChainWeilDatumExtendsToStep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto.StepExists

set_option maxHeartbeats 1000000 in

theorem stepEx : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ D : D7, StepEx D := by
  intro h1 h2 h3 h4 D c hc k hk s s' hs hs' ω f hpre
  obtain ⟨X, hX, -, -, hX3, hX4, hX5⟩ := GlobalTheory.T.exists_real_discreteSeries_data_theta_properties h1 h2
  have I : Inputs D X := GlobalTheory.T.thetaPairAnalyticHypotheses_of_discreteSeries h1 h2 h3 h4 D X hX
  have hPL : PairLifts D X :=
    GlobalTheory.T.pairThetaLift_factors_through_intertwiner D X I (GlobalTheory.T.thetaLifts_cuspidal_of_lower_tower_lifts_vanish D X I (GlobalTheory.T.lowerTowerLiftsVanish_of_vanish_on_fock D X I (GlobalTheory.T.lowerTowerLifts_vanish_on_fock D X I)))
  have hrule : ∀ τ, RulePar X (s.par τ) (s'.par τ) (c.a k τ) (c.a k τ) := fun τ =>
    ((GlobalTheory.T.realThetaCorrespondence_upwardPair_both_directions h1 h2 D c.t _ _ _ _ (hpre.par τ)).2 X hX3 hX4 hX5).1
  have hwe : IsWeilExp c.ψ s.V s'.V (c.a k) (c.a k) ω :=
    ⟨c.χ k, c.χ k, hpre.weil, fun τ => ⟨hc.exp k hk τ, hc.exp k hk τ⟩⟩
  obtain ⟨It, hIt⟩ := (GlobalTheory.T.exists_realIntertwiners_upwardThetaPair h1 h2 D c.t s.V s'.V s.par s'.par s.M s'.M (c.a k) (c.a k) c.θ c.ψ hc.inf
    hpre.par).1
  have hItW := hIt ω f hwe hpre.vac
  have hL := hPL s.par s'.par (c.a k) (c.a k) hrule s.V s'.V s.M s'.M c.θ c.ψ hc.inf ω hwe f It hpre.vac hItW
    s'.ν s'.fd hs'.haar hs'.fund f (isVacF_of_isVacVec hpre.vac)

  have hlev : ∀ F : s'.CC c, ∃ u ∈ s.CC c, ∀ φ v h,
      IntegrableOn (fun g => thetaKO ω h g (ptOf c.ψ c.θ s.M s'.M f φ) *
        (F : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) v g) s'.fd s'.ν ∧
      ∫ g in s'.fd, thetaKO ω h g (ptOf c.ψ c.θ s.M s'.M f φ) * (F : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) v g ∂s'.ν =
        u (It φ v) h := by
    intro F
    obtain ⟨F', hF', hint⟩ := hL _ (GlobalTheory.ChainOnto.multT_le_noLevel c.θ s'.M _ _ F.2)
    refine ⟨F', ?_, hint⟩
    have hlaw : ∀ P v, ∀ κ ∈ s.J, ∀ g, F' (It P v) (g * κ) = F' (It P v) g := by
      intro P v κ hκ g
      rw [← (hint P v (g * κ)).2, ← (hint P v g).2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g' => ?_)
      have hm : ((g * κ, g') : GA D s.V × GA D s'.V) = (g, g') * (κ, 1) := by simp
      simp only [thetaKO]
      rw [hm, map_mul, Module.End.mul_apply, hpre.law P κ hκ 1 (one_mem _)]
    refine GlobalTheory.T.mem_multiplicitySpace_level_of_KFinite_tensors D s.V s.par s.M c.θ hc.inf _ _ (fun κ hκ => hs.fin hκ) F' hF' ?_
    intro w hw κ hκ g
    have hx := GlobalTheory.T.kFiniteSpan_le_span_realIntertwiner_values h1 h2 D s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ (c.a k) (c.a k) ω f It hc.inf hwe
      hpre.vac hItW hw
    suffices e : F' w (g * κ) = F' w g by rw [e]; simp
    clear hw
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨P, v, _, rfl⟩ := hx; exact hlaw P v κ hκ g
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, Pi.add_apply, hx, hy]
    | smul a x _ hx => simp only [map_smul, Pi.smul_apply, smul_eq_mul, hx]

  let pt : PolF D s'.V.rank s.V.rank →ₗ[ℂ] (WO s.V s'.V → ℂ) :=
    pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) f
  have hp : ptOf c.ψ c.θ s.M s'.M f = pt := rfl
  have hint : ∀ F : s'.CC c, ∀ φ v g, IntegrableOn (fun h => (LinearMap.proj 0 ∘ₗ ω (g, h)) (pt φ) *
      (F : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) v h) s'.fd s'.ν := fun F φ v g => by
    obtain ⟨u, -, hu⟩ := hlev F
    exact (hu φ v g).1
  obtain ⟨B, hB⟩ := GlobalTheory.Chain.IoLift.exists_trilinear s'.ν s'.fd (fun g h => LinearMap.proj 0 ∘ₗ ω (g, h)) pt
    (s'.CC c) hint
  have hex : ∀ F : s'.CC c, ∃ u ∈ s.CC c, ∀ φ v, u (It φ v) = B φ v F := fun F => by
    obtain ⟨u, hu, he⟩ := hlev F
    refine ⟨u, hu, fun φ v => ?_⟩
    rw [hB]
    funext g
    exact ((he φ v g).2).symm
  have hun : ∀ u ∈ s.CC c, (∀ φ v, u (It φ v) = 0) → u = 0 := fun u hu h0 => by
    obtain ⟨φ, v, hne⟩ : ∃ φ v, It φ v ≠ 0 := by
      by_contra hn
      exact hItW.ne (LinearMap.ext₂ fun φ v => by_contra fun h => hn ⟨φ, v, h⟩)
    exact GlobalTheory.Grid.Sep.multT_eq_zero hu hne (h0 φ v)
  obtain ⟨io, hio⟩ := GlobalTheory.Chain.IoLift.ioExists_of_forall (T := It) (C' := s.CC c) hint B hB hex hun
  exact ⟨⟨ω, f, It, io⟩, rfl, rfl, ⟨hpre, hItW, hio⟩⟩

end GlobalTheory.EvenOnto.StepExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryFactorFiniteSetOfPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicUnitary_factor_finiteSetOfPlaces : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)),
    ∃ gS k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J, g = gS * k ∧
      (∀ u : AF F, (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w u = 0) → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS - 1) = 0) ∧
      (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) ∧
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
        u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1)) ∧
      (∀ w ∉ S, ∀ z ∈ GlobalTheory.InertSph.latAt X w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k *ᵥ z = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g *ᵥ z ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k⁻¹ *ᵥ z = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ *ᵥ z) := by
  first | exact @GlobalTheory.PlaceCut.exists_cut | exact GlobalTheory.PlaceCut.exists_cut | (intros; apply GlobalTheory.PlaceCut.exists_cut <;> assumption)
end

