import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0648
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0412
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0063
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0057
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0663
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0484
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0705
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0697
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0372
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0651
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0617
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0628
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0640
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0631
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0624
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0637
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0615
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0682
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0672
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0700
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0706
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0074
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0079
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0113
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0080
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0089
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0123
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0091
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0103
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0128
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0114
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0081
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0003
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.UniformTransfer.UnitaryIntegralLevel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0703
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0698
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0702
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalCellMultiplicityZeroOfSplitColumn
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

noncomputable section

namespace GlobalTheory.CompanionTheory.FineProd.CellMulti

set_option synthInstance.maxHeartbeats 400000

theorem jhMult_cell_eq_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h r : ℕ} (x : Fin h → IrrGL k) (y : Fin r → IrrGL k), (∀ j, (y j).IsCusp) → ∀ (b : Fin h → Fin r → ℕ) (hrow : ∀ i, ∑ j, b i j = (x i).1) (hcol : ∀ j, ∑ i, b i j = (y j).1) (j : Fin r) (i i' : Fin h), i ≠ i' → b i j ≠ 0 → b i' j ≠ 0 → jhMult (piTensor fun j => (y j).rep) (cellFunctor (c := fun i j => Fin (b i j)) (fun i => stdBlocks (b i) (hrow i)) (fun j => stdBlocks (fun i => b i j) (hcol j)) (piTensor fun i => (x i).rep)) = 0 := by
  intro k _ _ _ _ hA h r x y hy b hrow hcol j i i' hii hi hi'
  classical
  by_contra h0
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hτ : (piTensor fun j => (y j).rep).IsIrreducible := GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => (y j).2.rep
  have hτs : IsSmooth (piTensor fun j => (y j).rep) := isSmooth_piTensor fun j => (y j).2.rep.smooth
  obtain ⟨s, -, hS⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_of_cell (GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).2 _ _
    (fun i => (x i).2.rep.smooth) (fun i => hasFiniteLength_of_isIrreducible (x i).2.rep.irr) hτ hτs h0
  have h1 := GlobalTheory.LocGL.SupportUnique.isSubquotient_factor (fun j => multiProd (stdBlocks (fun i => b i j) (hcol j)) fun i => (s i j).ρ) j
    (y j).2.rep.irr
    ((GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (y j).rep) (fun j => (y j).2.rep.irr) j).trans
      (GlobalTheory.LocGL.SupportUnique.isSubquotient_comp hS _))
  let Y : Fin h → IrrGL k := fun i => IrrGL.of (s i j).ρ (s i j).smooth (s i j).irr
  have hYb : ∀ c, (Y c).1 = b c j := fun _ => rfl
  let ψ := prodIrrEquiv (hcol j) (fun i => (s i j).ρ) (fun i => (s i j).smooth) fun i => (s i j).irr
  have h2 := h1.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective)
  let S : Finset (Fin h) := Finset.univ.filter fun c => b c j ≠ 0
  let o : Fin S.card ↪o Fin h := S.orderEmbOfFin rfl
  have hcard : 2 ≤ S.card := Finset.one_lt_card.2 ⟨i, by simp [S, hi], i', by simp [S, hi'], hii⟩
  have ho : ∀ a, o a ∈ S := fun a => Finset.orderEmbOfFin_mem _ _ _
  have hrange : ∀ c, (Y c).1 ≠ 0 → c ∈ Set.range o := fun c hc => by
    rw [Finset.range_orderEmbOfFin]
    simpa [S, hYb] using hc
  have hsum : ∑ a, (Y (o a)).1 = (y j).1 := by
    have e1 : ∑ a, (Y (o a)).1 = ∑ c : S, b c j :=
      Fintype.sum_equiv (S.orderIsoOfFin rfl).toEquiv _ _ fun a => rfl
    rw [e1, Finset.sum_coe_sort S (fun c => b c j), ← hcol j]
    exact Finset.sum_subset (Finset.subset_univ _) fun c _ hc => by simpa [S] using hc
  obtain ⟨E⟩ := GlobalTheory.T.induced_product_drop_zero_factors Y (hcol j) o o.strictMono hrange hsum
  have h3 := h2.trans (.of_injective E.toIntertwiningMap E.toLinearEquiv.injective)
  refine jhMult_ne_zero_iff.2 h3
    (GlobalTheory.T.cuspidal_multiplicity_product_zero hA (y j) (fun a => Y (o a)) hsum (hy j) hcard fun a => Nat.pos_of_ne_zero ?_)
  have := ho a
  simpa [S, hYb] using this

end GlobalTheory.CompanionTheory.FineProd.CellMulti
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSwapProductGeneric
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.GenSwap

open GlobalTheory.CompanionTheory.BZSwap

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSubquotient_of_equiv {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} {ρ' : Representation ℂ G U}
    (h : IsSubquotient σ ρ) (E : ρ.Equiv ρ') : IsSubquotient σ ρ' :=
  h.trans (IsSubquotient.of_surjective E.symm.toIntertwiningMap E.symm.surjective)

theorem isSubquotient_of_equiv_left {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {τ : Representation ℂ G U}
    {ρ : Representation ℂ G V} (E : σ.Equiv τ) (h : IsSubquotient σ ρ) : IsSubquotient τ ρ :=
  (IsSubquotient.of_surjective E.toIntertwiningMap E.surjective).trans h

theorem isGenericFor_prodIrr (hW : GlobalTheory.BZMir.Leib.WhitHeredity k) (hC : GlobalTheory.BZSeg.CuspGeneric k)
    {ψ : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1) {h N : ℕ} (x : Fin h → IrrGL k)
    (hc : ∀ a, (x a).IsCusp) (hd : ∑ a, (x a).1 = N) : IsGenericFor ψ (prodIrr x hd) := by
  rw [← isGeneric_iff_isGenericFor hψ h1]
  exact (GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity k hW h N (fun a => (x a).1) hd (fun a => (x a).2.rep.V)
    (fun a => (x a).rep) (fun a => (x a).2.rep.smooth)).2 fun a =>
      hC _ _ _ (hc a).1 (x a).2.rep.smooth (x a).2.rep.irr (hc a).2

theorem isSubquotient_of_generic_common {N : ℕ} {ψ : AddChar k Circle} (hψ : Continuous ψ) {U V V' W : Type}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [AddCommGroup W] [Module ℂ W] (T : Representation ℂ (GL (Fin N) k) U) (P : Representation ℂ (GL (Fin N) k) V)
    (P' : Representation ℂ (GL (Fin N) k) V') (hT : IsSubquotient T P) (hT' : IsSubquotient T P')
    (hTg : IsGenericFor ψ T) (hP : IsSmooth P) (hfl : GlobalTheory.SmGL.HasFiniteLength P)
    (hr : Module.rank ℂ (TwJacquet P (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (σ : Representation ℂ (GL (Fin N) k) W) (hi : σ.IsIrreducible) (hgσ : IsGenericFor ψ σ)
    (hsq : IsSubquotient σ P) : IsSubquotient σ P' := by
  have hTs : IsSmooth T := hT.isSmooth hP
  have hTf : GlobalTheory.SmGL.HasFiniteLength T := GlobalTheory.CompanionTheory.IrrSub.hasFiniteLength_of_isSubquotient hT hfl
  obtain ⟨A, B, -, hi', -, hg'⟩ := GlobalTheory.T.generic_has_generic_irreducible_subquotient k ψ hψ N T hTs hTf hTg
  have s₁ := GlobalTheory.ParIndExact.isSubquotient_subQuot A B
  obtain ⟨e⟩ := GlobalTheory.T.whittaker_rank_extension_bound k ψ hψ N P σ (subQuot A B) hP hr hi hi' hsq (s₁.trans hT) hgσ hg'
  exact isSubquotient_of_equiv_left e.symm (s₁.trans hT')

theorem isSubquotient_of_common {s N : ℕ} (hW : GlobalTheory.BZMir.Leib.WhitHeredity k) {ψ : AddChar k Circle}
    (hψ : Continuous ψ) (h1 : ψ ≠ 1) (d : Fin s → ℕ) (hN : ∑ a, d a = N) {X Y Z : Fin s → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    [∀ a, AddCommGroup (Z a)] [∀ a, Module ℂ (Z a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (π' : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Y a))
    (τ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Z a)) (hπ : ∀ a, IsSmooth (π a)) (hπ' : ∀ a, IsSmooth (π' a))
    (hτ : ∀ a, IsSmooth (τ a)) (hq : ∀ a, IsSubquotient (τ a) (π a)) (hq' : ∀ a, IsSubquotient (τ a) (π' a))
    (hg : ∀ a, IsGenericFor ψ (τ a)) {V V' W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [AddCommGroup W] [Module ℂ W] (P : Representation ℂ (GL (Fin N) k) V) (P' : Representation ℂ (GL (Fin N) k) V')
    (E : (multiProd (stdBlocks d hN) π).Equiv P) (E' : (multiProd (stdBlocks d hN) π').Equiv P')
    (hP : IsSmooth P) (hfl : GlobalTheory.SmGL.HasFiniteLength P)
    (hr : Module.rank ℂ (TwJacquet P (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (σ : Representation ℂ (GL (Fin N) k) W) (hi : σ.IsIrreducible) (hgσ : IsGenericFor ψ σ)
    (hsq : IsSubquotient σ P) : IsSubquotient σ P' := by
  have hTg : IsGenericFor ψ (multiProd (stdBlocks d hN) τ) := by
    obtain ⟨H⟩ := hW ψ hψ h1 s N d hN Z τ hτ
    have : Nontrivial (⨂[ℂ] a, TwJacquet (τ a) (unipB k (Fin (d a))) (whitChar ψ (d a))) :=
      (GlobalTheory.CompanionTheory.Leib.nontrivial_piTensorProduct_iff _).2 hg
    exact H.toEquiv.nontrivial
  exact isSubquotient_of_generic_common hψ _ P P'
    (isSubquotient_of_equiv (GlobalTheory.T.product_preserves_subquotient k d N hN Z X τ π hπ hq) E)
    (isSubquotient_of_equiv (GlobalTheory.T.product_preserves_subquotient k d N hN Z Y τ π' hπ' hq') E') hTg hP hfl hr σ hi hgσ hsq

theorem isSubquotient_of_positions {s N : ℕ} (hW : GlobalTheory.BZMir.Leib.WhitHeredity k) {ψ : AddChar k Circle}
    (hψ : Continuous ψ) (h1 : ψ ≠ 1) (d : Fin s → ℕ) (hN : ∑ a, d a = N) {X Y : Fin s → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (π' : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Y a))
    (hπ : ∀ a, IsSmooth (π a)) (hπ' : ∀ a, IsSmooth (π' a)) (hg : ∀ a, IsGenericFor ψ (π a))
    (hf : ∀ a, GlobalTheory.SmGL.HasFiniteLength (π a))
    (hsw : ∀ a (W : Type) [AddCommGroup W] [Module ℂ W] (g : Representation ℂ (GL (Fin (d a)) k) W),
      IsSmooth g → g.IsIrreducible → IsSubquotient g (π a) → IsSubquotient g (π' a))
    {V V' W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [AddCommGroup W] [Module ℂ W] (P : Representation ℂ (GL (Fin N) k) V) (P' : Representation ℂ (GL (Fin N) k) V')
    (E : (multiProd (stdBlocks d hN) π).Equiv P) (E' : (multiProd (stdBlocks d hN) π').Equiv P')
    (hP : IsSmooth P) (hfl : GlobalTheory.SmGL.HasFiniteLength P)
    (hr : Module.rank ℂ (TwJacquet P (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (σ : Representation ℂ (GL (Fin N) k) W) (hi : σ.IsIrreducible) (hgσ : IsGenericFor ψ σ)
    (hsq : IsSubquotient σ P) : IsSubquotient σ P' := by
  have ex := fun a => GlobalTheory.T.generic_has_generic_irreducible_subquotient k ψ hψ (d a) (π a) (hπ a) (hf a) (hg a)
  choose A B _ hirr hsm hgen using ex
  have hq : ∀ a, IsSubquotient (subQuot (A a) (B a)) (π a) := fun a => GlobalTheory.ParIndExact.isSubquotient_subQuot _ _
  exact isSubquotient_of_common hW hψ h1 d hN π π' (fun a => subQuot (A a) (B a)) hπ hπ' hsm hq
    (fun a => hsw a _ _ (hsm a) (hirr a) (hq a)) hgen P P' E E' hP hfl hr σ hi hgσ hsq

theorem fac_rev {h j : ℕ} (hj : j + 1 < h) (x : Fin h → IrrGL k) (i : Fin 2) :
    (fac hj x 1 : Fin 2 → IrrGL k) (Fin.rev i) = (fac' hj x 1 : Fin 2 → IrrGL k) i := by
  rw [fac_one hj x, fac'_one hj x]
  fin_cases i <;> rfl

theorem nonempty_equiv_of_eq {n M : ℕ} {u v : Fin n → IrrGL k} (e : u = v) (h₁ : ∑ a, (u a).1 = M)
    (h₂ : ∑ a, (v a).1 = M) : Nonempty ((prodIrr u h₁).Equiv (prodIrr v h₂)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

set_option maxHeartbeats 1000000 in

theorem position_swap (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : Zc.Cos.GKLocal k) {h j : ℕ} (hj : j + 1 < h)
    (x : Fin h → IrrGL k) (d : Fin 3 → ℕ)
    (s₁ : ∀ a, ∑ b, (fac hj x a b).1 = d a) (s₂ : ∀ a, ∑ b, (fac' hj x a b).1 = d a) :
    ∀ a (W : Type) [AddCommGroup W] [Module ℂ W] (g : Representation ℂ (GL (Fin (d a)) k) W),
      IsSmooth g → g.IsIrreducible → IsSubquotient g (prodIrr (fac hj x a) (s₁ a)) →
      IsSubquotient g (prodIrr (fac' hj x a) (s₂ a)) := by
  refine fin_three_forall ?_ ?_ ?_
  · intro W _ _ g _ _ hq
    obtain ⟨E⟩ := nonempty_equiv_of_eq (fac'_zero hj x).symm (s₁ 0) (s₂ 0)
    exact isSubquotient_of_equiv hq E
  · intro W _ _ g hgs hgi hq
    have hd2 : ∑ a, (fac hj x 1 (Fin.rev a)).1 = d 1 :=
      (Equiv.sum_comp Fin.revPerm fun b => (fac hj x 1 b).1).trans (s₁ 1)
    obtain ⟨E⟩ := prodIrr_congr rfl (fun a => fac hj x 1 (Fin.rev a)) (fac' hj x 1) (fun i => fac_rev hj x i) hd2 (s₂ 1)
    exact isSubquotient_of_equiv (GlobalTheory.T.reversed_product_same_subquotients hA hGK (fac hj x 1) (s₁ 1) hd2 g hgs hgi hq) E
  · intro W _ _ g _ _ hq
    obtain ⟨E⟩ := nonempty_equiv_of_eq (fac'_two hj x).symm (s₁ 2) (s₂ 2)
    exact isSubquotient_of_equiv hq E

set_option maxHeartbeats 1000000 in

theorem core (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : Zc.Cos.GKLocal k) (hW : GlobalTheory.BZMir.Leib.WhitHeredity k)
    (hR : GlobalTheory.BZSeg.WhitRankIrr k) (hC : GlobalTheory.BZSeg.CuspGeneric k) (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (h1 : ψ ≠ 1) {h N j : ℕ} (hj : j + 1 < h) (x : Fin h → IrrGL k) (hc : ∀ a, (x a).IsCusp) (d : Fin 3 → ℕ)
    (s₁ : ∀ a, ∑ b, (fac hj x a b).1 = d a) (s₂ : ∀ a, ∑ b, (fac' hj x a b).1 = d a) (hN : ∑ a, d a = N)
    (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)).1 = N)
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W) (hi : σ.IsIrreducible)
    (hg : IsGenericFor ψ σ) (hsq : IsSubquotient σ (prodIrr x hd)) :
    IsSubquotient σ (prodIrr (fun a => x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)) hd') := by
  have hJ : j < h := by omega
  have hkey : ∀ c, fac' hj x (ofLex (order hj c)).1 (ofLex (order hj c)).2 =
      x (Equiv.swap (⟨j, hJ⟩ : Fin h) ⟨j + 1, hj⟩ c) := fun c =>
    congrArg (fun y => x (Equiv.swap (⟨j, hJ⟩ : Fin h) ⟨j + 1, hj⟩ y)) (place_order hj c)
  obtain ⟨p⟩ := flatten (grp h j) (fac hj x) d s₁ hN (order hj) x (fun c => congrArg x (place_order hj c)) hd
  obtain ⟨q⟩ := flatten (grp h j) (fac' hj x) d s₂ hN (order hj)
    (fun a => x (Equiv.swap (⟨j, hJ⟩ : Fin h) ⟨j + 1, hj⟩ a)) hkey hd'
  exact isSubquotient_of_positions hW hψ h1 d hN (fun a => prodIrr (fac hj x a) (s₁ a))
    (fun a => prodIrr (fac' hj x a) (s₂ a)) (fun _ => isSmooth_prodIrr _ _) (fun _ => isSmooth_prodIrr _ _)
    (fun a => isGenericFor_prodIrr hW hC hψ h1 _ (fun _ => hc _) _) (fun _ => GlobalTheory.T.product_irreducible_finite_length hA _ _)
    (position_swap hA hGK hj x d s₁ s₂) _ _ p q
    (isSmooth_prodIrr _ _) (GlobalTheory.T.product_irreducible_finite_length hA _ _) (GlobalTheory.T.whittaker_rank_product_le_one k hW hR ψ hψ h1 h N x hd) σ hi hg hsq

theorem isSubquotient_prodIrr_swap : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k → GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.CuspGeneric k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ {h N : ℕ} (x : Fin h → IrrGL k), (∀ a, (x a).IsCusp) → ∀ (hd : ∑ a, (x a).1 = N) (j : ℕ) (hj : j + 1 < h) (hd' : ∑ a, (x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)).1 = N) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible → IsGenericFor ψ σ → IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)) hd') := by
  intro k _ _ _ _ hA hGK hW hR hC ψ hψ h1 h N x hc hd j hj hd' W _ _ σ _ hi hg hsq
  have t : ∑ b : Fin 2, ((fac' hj x 1 : Fin 2 → IrrGL k) b).1 = ∑ b : Fin 2, ((fac hj x 1 : Fin 2 → IrrGL k) b).1 := by
    rw [fac_one hj x, fac'_one hj x]
    simp [Fin.sum_univ_two, add_comm]
  have s₂ : ∀ a, ∑ b, (fac' hj x a b).1 = ∑ b, (fac hj x a b).1 :=
    fin_three_forall (by rw [fac'_zero hj x]) t (by rw [fac'_two hj x])
  exact core hA hGK hW hR hC ψ hψ h1 hj x hc (fun a => ∑ b, (fac hj x a b).1) (fun _ => rfl) s₂
    ((sum_place hj fun c => (x c).1).trans hd) hd hd' σ hi hg hsq

end GlobalTheory.CompanionTheory.GenSwap

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockSeriesZetaBound
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD

theorem fibres (F : Type) [Field F] [NumberField F] (ρ : 𝓞 F) (hρ : ρ ≠ 0) (a : FQ F) (b : FQ F) :
    Finite {D : FQ F // a + ρ • D = b} ∧
      Nat.card {D : FQ F // a + ρ • D = b} ≤ Ideal.absNorm (Ideal.span {ρ}) := by
  have hne : Ideal.span {ρ} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hρ
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.torsion_card_le_absNorm_pow F 1 (intVec F 1) (isLat_intVec 1) (Ideal.span {ρ}) hne
  rw [pow_one] at hcard
  by_cases hb : ∃ D₀ : FQ F, a + ρ • D₀ = b
  · obtain ⟨D₀, hD₀⟩ := hb
    let φ : {D : FQ F // a + ρ • D = b} → {x : FQ F // ∀ r ∈ Ideal.span {ρ}, r • x = 0} :=
      fun D => ⟨D.1 - D₀, by
        intro r hr
        obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hr
        have h1 : ρ • (D.1 - D₀) = 0 := by
          have h2 : a + ρ • D.1 = a + ρ • D₀ := D.2.trans hD₀.symm
          rw [smul_sub, sub_eq_zero]
          exact add_left_cancel h2
        rw [mul_smul, h1, smul_zero]⟩
    have hφ : Function.Injective φ := by
      intro x y hxy
      have h3 : x.1 - D₀ = y.1 - D₀ := congrArg Subtype.val hxy
      exact Subtype.ext (sub_left_inj.1 h3)
    have hF : Finite {D : FQ F // a + ρ • D = b} := Finite.of_injective φ hφ
    exact ⟨hF, (Nat.card_le_card_of_injective φ hφ).trans hcard⟩
  · have hE : IsEmpty {D : FQ F // a + ρ • D = b} := ⟨fun D => hb ⟨D.1, D.2⟩⟩
    exact ⟨inferInstance, by simp⟩

theorem den_eq (F : Type) [Field F] [NumberField F] (ρ : 𝓞 F) (f : F) (D : FQ F) :
    den F (f + ((ρ : 𝓞 F) : F) * (Quotient.out D : Fin 1 → F) 0) =
      Ideal.torsionOf (𝓞 F) (FQ F)
        ((Submodule.Quotient.mk (fun _ => f) : FQ F) + ρ • D) := by
  unfold den
  congr 1
  have hD : D = Submodule.Quotient.mk (Quotient.out D : Fin 1 → F) :=
    (Quotient.out_eq D).symm
  conv_rhs => rw [hD]
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  congr 1
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp [Algebra.smul_def]

theorem term_le (A δ N n : ℕ) (s : ℝ) (hs : 0 < s) (hδ : δ ≠ 0) (hN : N ≠ 0) (hn : n ≠ 0)
    (h : δ * N ^ 2 * n ^ 2 ≤ A) :
    (A : ℝ) ^ (-s) ≤ (δ : ℝ) ^ (-s) * (N : ℝ) ^ (-(2 * s)) * (n : ℝ) ^ (-(2 * s)) := by
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast Nat.pos_of_ne_zero hδ
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hle : (δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2 ≤ A := by exact_mod_cast h
  have hpos : (0 : ℝ) < (δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2 := by positivity
  have hsq : ∀ x : ℝ, 0 < x → (x ^ 2) ^ (-s) = x ^ (-(2 * s)) := by
    intro x hx
    rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le]
    congr 1
    push_cast
    ring
  calc (A : ℝ) ^ (-s) ≤ ((δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
    _ = (δ : ℝ) ^ (-s) * (N : ℝ) ^ (-(2 * s)) * (n : ℝ) ^ (-(2 * s)) := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity), hsq _ hN', hsq _ hn']

theorem sum_delta_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (s : ℝ), 1 < s → Summable (fun D : FQ F => (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s)) ∧ ∑' D : FQ F, (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) ≤ C * zetaR F (2 * s - 1) * (delta c : ℝ) ^ (-s) * (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
  intro F E _ _ _ _ _ σ hσ
  obtain ⟨C, hC, hmink⟩ := GlobalTheory.T.ideal_principal_element_norm_bound E
  refine ⟨C, hC, ?_⟩
  intro m c hc u s hs
  have hT : tor c u ≠ ⊥ :=
    GlobalTheory.T.lattice_quotient_torsion_nonzero E m (lam c) (GlobalTheory.T.lam_is_lattice E m c) (Submodule.Quotient.mk u)
  obtain ⟨t, htT, ht0, htC⟩ := hmink (tor c u) hT
  obtain ⟨f, hf⟩ := GlobalTheory.T.delta_block_lower_bound_torsion F E σ hσ m c hc u t htT ht0
  have hkt : Ideal.absNorm (Ideal.span {RingOfIntegers.norm F t}) =
      Ideal.absNorm (Ideal.span {t}) := (GlobalTheory.T.relative_norm_cm_absNorm F E σ hσ t).2
  have hNt : Ideal.absNorm (Ideal.span {t}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    simpa [Ideal.span_singleton_eq_bot] using ht0
  have hρ : RingOfIntegers.norm F t ≠ 0 := by
    intro h0
    rw [h0] at hkt
    apply hNt
    rw [← hkt]
    simp
  generalize hρdef : RingOfIntegers.norm F t = ρ at hf hkt hρ
  have hδ : delta c ≠ 0 := (GlobalTheory.T.delta_eq_lattice_index E m c).1
  have hN : Ideal.absNorm (tor c u) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hT
  have hδ' : (0 : ℝ) < delta c := by exact_mod_cast Nat.pos_of_ne_zero hδ
  have hN' : (0 : ℝ) < Ideal.absNorm (tor c u) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hs0 : 0 < s := by linarith
  obtain ⟨hsum, hzeta⟩ := GlobalTheory.T.torsion_norm_zeta_bound F 1 (intVec F 1) (isLat_intVec 1) (2 * s - 1) (by linarith)
  have hexp : (((1 : ℕ) : ℝ) + (2 * s - 1)) = 2 * s := by
    push_cast
    ring
  rw [hexp] at hsum hzeta
  let g : FQ F → ℝ := fun x => (Ideal.absNorm (Ideal.torsionOf (𝓞 F) (FQ F) x) : ℝ) ^ (-(2 * s))
  have hg0 : ∀ x, 0 ≤ g x := fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _
  let a : FQ F := Submodule.Quotient.mk (fun _ => f)
  let π : FQ F → FQ F := fun D => a + ρ • D
  obtain ⟨hsum2, hle2⟩ := GlobalTheory.T.tsum_comp_bounded_fibres_le (FQ F) (FQ F) π (Ideal.absNorm (Ideal.span {ρ}))
    (fun b => fibres F ρ hρ a b) g hg0 hsum
  let P : ℝ := (delta c : ℝ) ^ (-s) * (Ideal.absNorm (tor c u) : ℝ) ^ (-(2 * s))
  have hP : 0 ≤ P := by positivity
  have hterm : ∀ D : FQ F,
      (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) ≤
        P * g (π D) := by
    intro D
    have h1 := hf ((Quotient.out D : Fin 1 → F) 0)
    rw [den_eq F ρ f D] at h1
    have hn : Ideal.absNorm (Ideal.torsionOf (𝓞 F) (FQ F) (π D)) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact GlobalTheory.T.lattice_quotient_torsion_nonzero F 1 (intVec F 1) (isLat_intVec 1) (π D)
    exact term_le _ _ _ _ s hs0 hδ hN hn h1
  have hnn : ∀ D : FQ F,
      0 ≤ (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) :=
    fun D => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsumP : Summable (fun D : FQ F => P * g (π D)) := hsum2.mul_left P
  refine ⟨Summable.of_nonneg_of_le hnn hterm hsumP, ?_⟩
  have hS : 0 ≤ ∑' x, g x := tsum_nonneg hg0
  have hZ : 0 ≤ zetaR F (2 * s - 1) := hS.trans hzeta
  have hkC : (Ideal.absNorm (Ideal.span {ρ}) : ℝ) ≤ C * Ideal.absNorm (tor c u) := by
    rw [hkt]
    exact htC
  have hpow : (Ideal.absNorm (tor c u) : ℝ) ^ (-(2 * s)) * (Ideal.absNorm (tor c u) : ℝ) =
      (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
    rw [show (1 - 2 * s) = -(2 * s) + 1 by ring, Real.rpow_add hN', Real.rpow_one]
  calc ∑' D : FQ F, (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s)
      ≤ ∑' D : FQ F, P * g (π D) :=
        (Summable.of_nonneg_of_le hnn hterm hsumP).tsum_le_tsum hterm hsumP
    _ = P * ∑' D : FQ F, g (π D) := tsum_mul_left
    _ ≤ P * ((Ideal.absNorm (Ideal.span {ρ}) : ℝ) * ∑' x, g x) :=
        mul_le_mul_of_nonneg_left hle2 hP
    _ ≤ P * ((C * Ideal.absNorm (tor c u)) * zetaR F (2 * s - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hP
        exact mul_le_mul hkC hzeta hS (by positivity)
    _ = C * zetaR F (2 * s - 1) * (delta c : ℝ) ^ (-s) *
          (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
        rw [← hpow]
        simp only [P]
        ring

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalLatticeIndexPowStatement
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_lattice_index_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (i j : ℕ), i ≤ a → j ≤ b → (intSub a b w).relIndex (latD ϖ a b i j) = (qV E w) ^ (i * (b - j)) := by
  first | exact @GlobalTheory.CompanionTheory.CtS.LatDiag.relIndex_intSub_latD | exact GlobalTheory.CompanionTheory.CtS.LatDiag.relIndex_intSub_latD | (intros; apply GlobalTheory.CompanionTheory.CtS.LatDiag.relIndex_intSub_latD <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DivisorGeneralPointBranches
section
namespace GlobalTheory.CompanionTheory.ComplexSets

open GroundTheory.Heights₂.Heights in

theorem divisorGeneralPointBranches : GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches.Statement :=
  DivisorGeneralPointBranches.proof DivisorOneComponent.proof
    (DivisorBranches.proof IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof
      GroundTheory.Heights₂.Heights.AutoClose.DivisorRegularGeneric
      (NormalDivisorChartGeneric.proof
        (NormalModelDivisorChartGeneric.proof
          (NormalModelGoodPointGeneric.proof NormalCodimOneCompleteIntersection.proof
            NormalCodimOneUniformiser.proof JacobianRankOffHypersurface.proof
            ProjectionUnramifiedGeneric.proof)
          NormalModelGoodPointChart.proof))
      NormalDoublePointsGeneric.proof DivisorGoodPointBranches.proof)

end GlobalTheory.CompanionTheory.ComplexSets
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalVSum
section
noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisUnif.EIdemP

open scoped TensorProduct NNReal Matrix NumberField.AdeleRing
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eSF_eq (S : Finset (Pl F)) : eSF S = ((1, ∑ v ∈ S, singleFin v 1) : AF F) := by
  simp only [eSF, LinearMap.inl_apply, LinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]
  rfl

open Classical in
theorem evalV_sum (S : Finset (Pl F)) (u : Pl F) :
    evalV F u (∑ v ∈ S, singleFin v 1) = if u ∈ S then 1 else 0 := by
  rw [map_sum]
  have hs : ∀ v : Pl F, evalV F u (singleFin v 1) = if u = v then 1 else 0 := by
    intro v
    have e1 : evalV F u (singleFin v 1) = (singleFin v (1 : Fv F v) : Af F) u := rfl
    have e2 : (singleFin v (1 : Fv F v) : Af F) = singleV F v 1 := rfl
    rw [e1, e2]
    unfold singleV
    by_cases huv : u = v
    · subst huv
      rw [if_pos rfl]
      exact RestrictedProduct.single_eq_same _ _ _
    · rw [if_neg huv]
      exact RestrictedProduct.single_eq_of_ne _ _ huv
  simp only [hs]
  rw [Finset.sum_ite_eq]

end GlobalTheory.CompanionTheory.RgEisUnif.EIdemP
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientJacquetSegmentStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_subquotient_jacquet_segment : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Γ : Segment k) (hF : FineJac Γ) (u : IrrGL k) (hu : IsLSeg Γ u.rep) (hs : ∑ i, (dec Γ i).1 = u.1) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Levi k fun i => Fin ((dec Γ i).1)) X), ρ.IsIrreducible → IsSubquotient ρ (jac (stdBlocks (fun i => (dec Γ i).1) hs) u.rep) → Nonempty (ρ.Equiv (piTensor fun i => (dec Γ i).rep)) := by
  first | exact @GlobalTheory.CompanionTheory.SegFineCons.equiv_piTensor_dec | exact GlobalTheory.CompanionTheory.SegFineCons.equiv_piTensor_dec | (intros; apply GlobalTheory.CompanionTheory.SegFineCons.equiv_piTensor_dec <;> assumption)
end

