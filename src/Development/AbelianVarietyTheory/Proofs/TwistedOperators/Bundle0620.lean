import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0567
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0235
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0595
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0333
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0530
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0517
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0592
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0597
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1474
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0045
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactPairRealAverageFockEqJetOperator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0278
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsRealFnNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0546
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0563
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0588
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1735
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0601
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosDefOfNode
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

open scoped ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefConv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)

def IsInvCont (X : Node) (F : Fn G X) : Prop := Continuous F ∧ ∀ γ ∈ GQ (G.V X), ∀ g, F (γ * g) = F g

def Good (a : Arrow T) (f : Sch G a) : Prop :=
  (Continuous fun p : GA D (G.V a.src) × GA D (G.V a.tgt) => W.kerA a f p.1 p.2) ∧
  (∀ γ ∈ GQ (G.V a.src), ∀ γ' ∈ GQ (G.V a.tgt), ∀ g h, W.kerA a f (γ * g) (γ' * h) = W.kerA a f g h) ∧
  (∀ τ, (gramAt D (G.V a.src) τ).PosDef) ∧ (M.ν a.src).IsHaarMeasure ∧
  IsFundamentalDomain (GQ (G.V a.src)) (M.fd a.src) (M.ν a.src)

theorem step {a : Arrow T} {f : Sch G a} (hg : Good W M a f) {F : Fn G a.src} (hF : IsInvCont a.src F) :
    LiftConv W M a f F ∧ IsInvCont a.tgt (liftA W M a f F) := by
  obtain ⟨hK, hinv, hpos, hH, hfd⟩ := hg
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact _ hpos
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V a.src)
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V a.tgt)
  have hl : ∀ γ ∈ GQ (G.V a.src), ∀ g h, W.kerA a f (γ * g) h = W.kerA a f g h := fun γ hγ g h => by
    simpa using hinv γ hγ 1 (one_mem _) g h
  have hr : ∀ γ ∈ GQ (G.V a.tgt), ∀ g h, W.kerA a f g (γ * h) = W.kerA a f g h := fun γ hγ g h => by
    simpa using hinv 1 (one_mem _) γ hγ g h
  refine ⟨fun h => ?_, ?_, fun γ hγ h => ?_⟩
  · exact GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact _ _ _ C hfd hC hcov _
      ((hK.comp (Continuous.prodMk_left h)).mul hF.1) (fun γ hγ g => by simp only [hl γ hγ, hF.2 γ hγ])
  · exact GlobalTheory.DefLiftCont.continuous_integral_of_cocompact (G := GA D (G.V a.tgt)) (GQ (G.V a.src)) (M.ν a.src)
      (M.fd a.src) C hfd hC hcov (fun h g => W.kerA a f g h * F g)
      ((hK.comp continuous_swap).mul (hF.1.comp continuous_snd)) (fun γ hγ h g => by simp only [hl γ hγ, hF.2 γ hγ])
  · simp only [liftA_apply, hr γ hγ]

theorem path {X : Node} {F : Fn G X} (hF : IsInvCont X F) : ∀ {Y : Node} (p : Path T X Y) (d : PureT G p),
    Path.Fam.All (fun a f => Good W M a f) d → PathConv W M p d F ∧ IsInvCont Y (liftP W M p d F)
  | _, .nil, _, _ => ⟨trivial, hF⟩
  | _, .snoc a p, d, h => by
    obtain ⟨h1, h2⟩ := path hF p d.1 h.1
    obtain ⟨h3, h4⟩ := step W M h.2 h2
    exact ⟨⟨h1, h3⟩, h4⟩

theorem all_colFam {S : Arrow T → Type} {P : ∀ a, S a → Prop} (t : T) :
    ∀ n (f : ∀ j : Fin n, S (.col t j)), (∀ j, P _ (f j)) → Path.Fam.All P (colFam t n f)
  | 0, _, _ => trivial
  | n + 1, f, h => ⟨all_colFam t n _ fun j => h j.castSucc, h (Fin.last n)⟩

theorem all_rowFam {S : Arrow T → Type} {P : ∀ a, S a → Prop} (j : ℕ) :
    ∀ n (f : ∀ i : Fin n, S (.right i j)), (∀ i, P _ (f i)) → Path.Fam.All P (rowFam j n f)
  | 0, _, _ => trivial
  | n + 1, f, h => ⟨all_rowFam j n _ fun i => h i.castSucc, h (Fin.last n)⟩

end GlobalTheory.DefConv

namespace GlobalTheory.DefConv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem posDef_of_node (G : GridData L sc) {μ0 : T} (hL : L.Is μ0) {X : Node} (h : X.InRange D.R.m)
    (h0 : X.neg D.R.m = 0) (τ : D.what₂.Tau) : (gramAt D (G.V X) τ).PosDef := by
  have hV := node_isV G hL h
  rw [h0] at hV
  refine GlobalTheory.RepsObj.gramAt_posDef (fun σ => ?_) hV.sigOK τ
  rw [hV.sig σ, hV.rank, Nat.sub_zero]

variable (W : G.Weil) {U : Set T} (S : GridChoice W U)

theorem theta_fock {t : T} {p : Pair T} (hp : DefPair D.R.m p) (hr : p.InRange D.R.m) (d : FinDatum G t p)
    (hv : S.Z.HasVec d) (Q : PolF D (G.pT p).rank (G.pS p).rank) :
    IsThetaFunO W.ψ (G.pS p) (G.pT p) (W.fock p (movedVec t S d) Q) := by
  have h1 := (GlobalTheory.FockRealVec.vec_theta_fock W S.Z hp d hv).1
  have h2 : IsThetaFunO W.ψ _ _ (movedVec t S d) := (W.om_is p hr).om_pres _ _ h1
  exact GlobalTheory.FockTheta.ptStable D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ _ _ _ Q h2

end GlobalTheory.DefConv

namespace GlobalTheory.DefConv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)

theorem good_col {t : T} {j : ℕ} (hj : j < D.R.m) (f : Sch G (.col t j))
    (hf : IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) f) (hpos : ∀ τ, (gramAt D (G.V (.top j)) τ).PosDef)
    {K : Subgroup (GL (Fin (G.V (.top j)).rank) (Lev.EAf D))} (hM : M.IsAt (.top j) K) : Good W M (.col t j) f := by
  have hr : (Pair.top t j : Pair T).InRange D.R.m := by show j + 1 ≤ D.R.m; omega
  obtain ⟨hc, -⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant W.ψ _ _ _ _ _ (W.om_is _ hr) f hf
  exact ⟨hc, fun γ hγ γ' hγ' g h => GlobalTheory.T.thetaKernel_grid_rational_left_invariant W _ hr f hf γ hγ γ' hγ' g h, hpos, hM.haar_fund.1, hM.haar_fund.2⟩

theorem good_row {i : ℕ} (hi : i < D.R.m) (f : Sch G (.right i D.R.m))
    (hf : IsThetaFunO W.ψ (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) f)
    (hpos : ∀ τ, (gramAt D (G.V (.grid i D.R.m)) τ).PosDef)
    {K : Subgroup (GL (Fin (G.V (.grid i D.R.m)).rank) (Lev.EAf D))} (hM : M.IsAt (.grid i D.R.m) K) :
    Good W M (.right i D.R.m) f := by
  have hr : (Pair.chi i D.R.m : Pair T).InRange D.R.m := by show i + 1 ≤ D.R.m ∧ D.R.m ≤ D.R.m; omega
  obtain ⟨hc, -⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant W.ψ _ _ _ _ _ (W.om_is _ hr) f hf
  refine ⟨?_, fun γ hγ γ' hγ' g h => GlobalTheory.T.thetaKernel_grid_rational_left_invariant W _ hr f hf γ hγ γ' hγ' g h, hpos, hM.haar_fund.1, hM.haar_fund.2⟩
  exact hc.comp (((continuous_negGA _).comp continuous_snd).prodMk continuous_fst)

end GlobalTheory.DefConv

namespace GlobalTheory.DefConv

end GlobalTheory.DefConv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimitiveFrameDatumBlockSubstitution
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.FrameSubst

theorem vecMul_bound {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] {G : GL n k} (hG : G ∈ KO k n) (c : k) (x : n → k)
    (hx : ∀ j, valuation k (x j) ≤ valuation k c) (j : n) : valuation k ((x ᵥ* G.val) j) ≤ valuation k c := by
  have hG' := ((mem_KO_iff G).1 hG).1
  simp only [vecMul, dotProduct]
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [map_mul]
  exact (mul_le_mul' (hx i) ((Valuation.mem_integer_iff _ _).1 (hG' i j))).trans (by rw [mul_one])

theorem vecMul_bound_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] {G : GL n k} (hG : G ∈ KO k n) (c : k) (x : n → k) :
    (∀ j, valuation k ((x ᵥ* G.val) j) ≤ valuation k c) ↔ ∀ j, valuation k (x j) ≤ valuation k c := by
  refine ⟨fun h j => ?_, fun h => vecMul_bound hG c x h⟩
  have := vecMul_bound ((KO k n).inv_mem hG) c _ h j
  rwa [vecMul_vecMul, Units.mul_inv, vecMul_one] at this

theorem mem_glLat_fromBlocks {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D₁ D₂ : Type} [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂] (ϖ : kˣ) (e : ℕ)
    {G₁ : GL D₁ k} {G₂ : GL D₂ k} (h₁ : G₁ ∈ KO k D₁) (h₂ : G₂ ∈ KO k D₂) (G : GL (D₁ ⊕ D₂) k)
    (hG : G.val = fromBlocks G₁.val 0 0 G₂.val) : G ∈ glLat (blockLat ϖ e (Assignment.two.block D₁ D₂)) := by
  intro x
  have hl : ∀ j, (x ᵥ* G.val) (Sum.inl j) = ((fun i => x (Sum.inl i)) ᵥ* G₁.val) j := fun j => by
    simp [hG, vecMul, dotProduct, Fintype.sum_sum_type]
  have hr : ∀ j, (x ᵥ* G.val) (Sum.inr j) = ((fun i => x (Sum.inr i)) ᵥ* G₂.val) j := fun j => by
    simp [hG, vecMul, dotProduct, Fintype.sum_sum_type]
  rw [mem_blockLat_two, mem_blockLat_two]
  simp only [hl, hr]
  refine and_congr ?_ (vecMul_bound_iff h₂ _ _)
  have := vecMul_bound_iff h₁ 1 (fun i => x (Sum.inl i))
  simpa using this

theorem isPrimFrame_mul_glLat {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [Fintype D] [DecidableEq D] {Λ : Submodule 𝒪[k] (D → k)} (g : GL D k)
    (hg : g ∈ glLat Λ) (X : Matrix A D k) : IsPrimFrame Λ (X * g.val) ↔ IsPrimFrame Λ X := by
  refine ⟨fun h => ?_, fun h => Model.isPrimFrame_mul h g hg⟩
  have := Model.isPrimFrame_mul h g⁻¹ ((glLat Λ).inv_mem hg)
  rwa [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this

theorem fFun_comp_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k]
    {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ)
    (H : GL D k) (hH : apow (gdet H) ((Fintype.card D : ℂ) / 2) = 1) (X : Matrix A D k) :
    fFun μ σ ν (fun Y => Ψ (Y * H.val)) X = (((ν (gdet H))⁻¹ : ℂˣ) : ℂ) * fFun μ σ ν Ψ (X * (invT H).val) := by
  classical
  by_cases hX : ∃ h : GL D k, X = X0 k σ * (invT h).val
  · obtain ⟨h, rfl⟩ := hX
    have e1 : X0 k σ * (invT h).val * (invT H).val = X0 k σ * (invT (h * H)).val := by
      rw [map_mul, Units.val_mul, Matrix.mul_assoc]
    have e2 : smallF μ ν (fun Y => Ψ (Y * H.val)) (Y0 k σ * h.val) = smallF μ ν Ψ (Y0 k σ * (h * H).val) := by
      unfold smallF; congr 1; funext g; simp only [Units.val_mul, Matrix.mul_assoc]
    rw [e1, splitTheta_fFun_frameFirstBlock_mul, splitTheta_fFun_frameFirstBlock_mul, e2, gdet_mul, map_mul, apow_mul, hH, Units.val_mul,
      Units.val_inv_eq_inv_val]
    have hn : (ν (gdet H) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
    simp only [Units.val_mul]
    ring
  · have hX' : ¬ ∃ h : GL D k, X * (invT H).val = X0 k σ * (invT h).val := by
      rintro ⟨h, hh⟩
      apply hX
      refine ⟨h * H⁻¹, ?_⟩
      have := congrArg (· * ((invT H)⁻¹).val) hh
      simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this
      rw [this, map_mul, map_inv, Units.val_mul]
    rw [fFun, dif_neg hX, fFun, dif_neg hX', mul_zero]

theorem phiA_blockSubst : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k]
    {A A' D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D₁] [DecidableEq D₁]
    [Fintype D₂] [DecidableEq D₂] (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D₁ ⊕ D₂)
    (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ) (Ψ : Matrix A' (D₁ ⊕ D₂) k → ℂ), ∀ M₁ ∈ KO k D₁, ∀ M₂ ∈ KO k D₂,
    ∀ X : Matrix A (D₁ ⊕ D₂) k,
      phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂))
          (fun Y => Ψ (Y * fromBlocks (invT M₁).val 0 0 M₂.val)) X =
        (ν (gdet M₁) : ℂ) * (((ν (gdet M₂))⁻¹ : ℂˣ) : ℂ) *
          phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)) Ψ (X * fromBlocks M₁.val 0 0 (invT M₂).val) := by
  intro k _ _ _ _ _ _ A A' D₁ D₂ _ _ _ _ _ _ _ _ μ _ σ ν ϖ e Ψ M₁ hM₁ M₂ hM₂ X
  classical
  let H : GL (D₁ ⊕ D₂) k := ⟨fromBlocks (invT M₁).val 0 0 M₂.val, fromBlocks ((invT M₁)⁻¹).val 0 0 (M₂⁻¹).val,
    by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩
  have hHinv : (invT H).val = fromBlocks M₁.val 0 0 (invT M₂).val := by
    rw [invT_val]
    show (fromBlocks ((invT M₁)⁻¹).val 0 0 (M₂⁻¹).val)ᵀ = _
    rw [fromBlocks_transpose, invT_inv_val, transpose_transpose, transpose_zero, transpose_zero, ← invT_val]
  have hdet : gdet H = (gdet M₁)⁻¹ * gdet M₂ := by
    rw [← gdet_invT]
    ext
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_fromBlocks_zero₁₂ _ _ _
  have habs : apow (gdet H) ((Fintype.card (D₁ ⊕ D₂) : ℂ) / 2) = 1 := by
    rw [hdet, apow_mul, apow_inv, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hM₁),
      apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hM₂), one_mul]
  have hfac : (((ν (gdet H))⁻¹ : ℂˣ) : ℂ) = (ν (gdet M₁) : ℂ) * (((ν (gdet M₂))⁻¹ : ℂˣ) : ℂ) := by
    rw [hdet, map_mul, map_inv, mul_inv, inv_inv, Units.val_mul]
  have hgl : invT H ∈ glLat (blockLat ϖ e (Assignment.two.block D₁ D₂)) :=
    mem_glLat_fromBlocks ϖ e hM₁ (invT_mem_KO hM₂) _ hHinv
  show phiA μ σ ν ϖ e _ (fun Y => Ψ (Y * H.val)) X = _
  rw [← hHinv]
  unfold phiA
  rw [latA_blockLat, compl_block_one, isPrimFrame_mul_glLat (invT H) hgl]
  split_ifs
  · rw [fFun_comp_mul μ σ ν Ψ H habs X, hfac]
  · simp

end GlobalTheory.FrameSubst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealMetaplecticFamilyDerivativeQuadratic
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical Matrix

namespace GlobalTheory.QuadFam

open GlobalTheory.RealWeil

theorem coordAll (hP : GlobalTheory.Published.RealMetaplecticRepresentation) (l : Type) [Fintype l] [DecidableEq l]
    (A : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)) (T : ℝ → Sch l →ₗ[ℂ] Sch l)
    (hA : ∀ w, Continuous fun t => A t w) (hT : ∀ s t f, T (s + t) f = T s (T t f)) (hT0 : ∀ f, T 0 f = f)
    (hI : ∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(T t f₁) = rhoFun (A t w) ⇑(T t f))
    (hiso : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) (hpt : ∀ f y, Continuous fun t => T t f y) :
    ∃ (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (c : ℂ), ∀ f y, HasDerivAt (fun t => T t f y) (quad X f y + c * f y) 0 := by
  obtain ⟨hs, hgrp, h0⟩ := GlobalTheory.T.symplectic_and_flow_of_intertwining_unitary l A T hT hT0 hI hiso
  cases isEmpty_or_nonempty l with
  | inl hl =>
    have hq : ∀ f y, quad (0 : Matrix (l ⊕ l) (l ⊕ l) ℝ) f y = 0 := fun f y => by simp [quad]
    obtain ⟨c, hc⟩ := GlobalTheory.T.isometryFamilies_derivatives_differ_by_scalar_at_zero l (fun t w => A t w) T (fun _ => LinearMap.id) (fun f y => quad 0 f y) hT hT0
      (fun _ _ _ => rfl) (fun _ => rfl) hgrp h0 hI
      (fun t w f f₁ h => by
        rw [LinearMap.id_apply, LinearMap.id_apply, h, Subsingleton.elim (A t w) w]) hiso
      (fun _ _ => rfl) hpt (fun f y => by rw [hq]; exact hasDerivAt_const _ _)
    exact ⟨0, c, hc⟩
  | inr hl =>
    let M : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ := fun t => LinearMap.toMatrix' (A t)
    have hM : ∀ t w, M t *ᵥ w = A t w := fun t w => LinearMap.toMatrix'_mulVec (A t) w
    have hMc : Continuous M := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [M, LinearMap.toMatrix'_apply]
      exact (continuous_apply i).comp (hA _)
    have hM0 : M 0 = 1 := by
      have : A 0 = LinearMap.id := LinearMap.ext h0
      simp only [M, this, LinearMap.toMatrix'_id]
    have hMm : ∀ s t, M (s + t) = M s * M t := by
      intro s t
      have : A (s + t) = (A s).comp (A t) := LinearMap.ext (hgrp s t)
      simp only [M, this, LinearMap.toMatrix'_comp]
    obtain ⟨X, hX⟩ := GlobalTheory.T.continuous_matrix_oneParameterGroup_eq_exp _ M hMc hM0 hMm
    have hsp : X ∈ LieAlgebra.Symplectic.sp l ℝ := by
      refine GlobalTheory.T.mem_symplecticLieAlgebra_of_exp_smul_mem_symplecticGroup l X fun t => ?_
      obtain ⟨N, hN⟩ := GlobalTheory.exists_symplecticGroup_of_sympl l (A t) (hs t)
      have e : Matrix.toLin' (N : Matrix (l ⊕ l) (l ⊕ l) ℝ) = A t := LinearMap.ext fun w => by
        rw [Matrix.toLin'_apply, hN]
      have e2 : (N : Matrix (l ⊕ l) (l ⊕ l) ℝ) = M t := by
        simp only [M, ← e, LinearMap.toMatrix'_toLin']
      rw [← hX t, ← e2]
      exact N.2
    obtain ⟨U, hU, hU0, hUI, hUiso, hUd⟩ := GlobalTheory.T.metaplectic_oneParameter_schwartz_intertwining hP l X hsp
    have hB : ∀ t w, NormedSpace.exp (t • X) *ᵥ w = A t w := fun t w => by rw [← hX, hM]
    obtain ⟨c, hc⟩ := GlobalTheory.T.isometryFamilies_derivatives_differ_by_scalar_at_zero l (fun t w => A t w) T U (fun f y => quad X f y) hT hT0 hU hU0 hgrp h0 hI
      (fun t w f f₁ h => by rw [hUI t w f f₁ h, hB]) hiso hUiso hpt hUd
    exact ⟨X, c, hc⟩

theorem deriv_quad : GlobalTheory.Published.RealMetaplecticRepresentation → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V), μ.IsAddHaarMeasure → ∀ (P : V → V → ℝ), IsPairing P →
    ∀ (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ)),
    (∀ v, Continuous fun t => A t v) →
    (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = schrF P v ⇑f → ⇑(T t f₁) = schrF P (A t v) ⇑(T t f)) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    (∀ f y, Continuous fun t => T t f y) →
    (∀ f φ : 𝓢(V, ℂ), Continuous fun t => ∫ x, T t f x * starRingEnd ℂ (φ x) ∂μ) →
    ∃ (m : ℕ) (a b : Fin m → V × V) (c : Fin m → ℂ) (c₀ : ℂ), ∀ (f : 𝓢(V, ℂ)) (g₁ g₂ : Fin m → 𝓢(V, ℂ)),
      (∀ i y, g₁ i y = fderiv ℝ (⇑f) y (b i).1 - 2 * Real.pi * Complex.I * (P y (b i).2 : ℂ) * f y) →
      (∀ i y, g₂ i y = fderiv ℝ (⇑(g₁ i)) y (a i).1 - 2 * Real.pi * Complex.I * (P y (a i).2 : ℂ) * g₁ i y) →
      ∀ y, HasDerivAt (fun t => T t f y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  intro hP V _ _ _ _ _ μ hμ P hp A T hA hT hT0 hI hiso hpt _
  exact GlobalTheory.T.realPairingSpace_result_of_schrodingerCoordinates V μ hμ P hp _ rfl (fun A' T' => coordAll hP (Fin _) A' T') A T hA hT hT0 hI hiso hpt

end GlobalTheory.QuadFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointsTopNodeOntoUnitaryHaarUnique
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowTest

theorem realPts_ontoUni_haar_unique : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j ≤ D.R.m →
    GlobalTheory.KJInf.OntoUni (fun (k : GinfC (G.V (.top j))) τ =>
      ((realIn W.θ S.N.fr (.top j) (k : GA D (G.V (.top j))) τ : GL (Fin (G.V (.top j)).rank) ℂ) :
        Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)) ∧
    ∀ κ κ' : Measure (GinfC (G.V (.top j))), κ.IsHaarMeasure → IsProbabilityMeasure κ → κ'.IsHaarMeasure →
      IsProbabilityMeasure κ' → κ = κ' := by
  intro D T L sc G W U S μ0 _ j hj
  have hX : DefNode D.R.m (Node.top j) := hj
  have hO := GlobalTheory.SeeSaw.ontoUni_inB D W.θ (G.V (.top j)) (S.N.frC _) W.θ_is (GlobalTheory.RealType.frC_on S.N hX)
  refine ⟨?_, ?_⟩
  · have e : (fun (k : GinfC (G.V (.top j))) τ =>
        ((realIn W.θ S.N.fr (.top j) (k : GA D (G.V (.top j))) τ : GL (Fin (G.V (.top j)).rank) ℂ) :
          Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)) =
        fun k : GinfC (G.V (.top j)) => GlobalTheory.SeeSaw.inB W.θ (G.V (.top j)) (S.N.frC (.top j)) k.1 :=
      funext fun k => funext fun τ => GlobalTheory.RowHoweAvg.realIn_coe W.θ S.N _ _ τ
    rw [e]
    exact hO
  · intro κ κ' h1 h2 h3 h4
    haveI : LocallyCompactSpace (GinfC (G.V (.top j))) :=
      (GlobalTheory.AdelicSplit.isClosed_GinfC' _).locallyCompactSpace
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure κ κ'

end GlobalTheory.RowTest
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPt0InvMemStdLatIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove GlobalTheory.FirstRowVertex
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.FirstRowLat

variable {D : D7}

theorem givenLevel_zero_le_KO {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E)
    (k : ℕ) (hk : 1 ≤ k) (g : GL (Fin ((locGrid G t w).rank (0, k))) (Kw w)) (hg : g ∈ givenLevel G t w (0, k)) :
    g ∈ GlobalTheory.SplitWeil.KO (Kw w) (Fin ((locGrid G t w).rank (0, k))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  change g ∈ (stepGroup L t w (j + 1)).map (GlobalTheory.StepData.reGL (ixFin G t w (j + 1))).toMonoidHom at hg
  by_cases hP : w ∈ L.Pg
  · exact ((GlobalTheory.Adopt.thetaGridBlockCongruence_typePrime_description G t w hP (j + 1) g).1 hg).1
  · exact ((GlobalTheory.Adopt.thetaGridBlockCongruence_offTypePrime_description G t w hP (j + 1) g).1 hg).1

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem levRow_zero_stab (S : GridChoice W U) {μ₀ : T} (hL : L.Is μ₀) (t : T) (k : FinPt G (.grid 0 D.R.m))
    (hk : finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _)) :
    Lev.finE (G.V (.grid 0 D.R.m)) k.1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.grid 0 D.R.m))) := by
  have hβ : IsFrame (S.B.β 0 D.R.m) (G.Λ (.grid 0 D.R.m)) := S.B.isFrame_β hL (Nat.zero_le _) le_rfl
  have hsd : IsSelfDualC (G.V (.grid 0 D.R.m)) (G.Λ (.grid 0 D.R.m)) := by
    have key : ∀ X : LSp D, X = ⟨D.sp.X', L.ΛX⟩ → IsSelfDualC X.sp X.lat := by
      rintro X rfl
      exact GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hL.βX
    exact key _ (colY_m L)
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have e := GlobalTheory.FunObj.LevRowSucc.prodLev_inf_UA hβ hsd (locPl G t)
    (fun w => rank_vertex G t w (X := (0, D.R.m)) ⟨Nat.zero_le _, le_rfl⟩) (fun w => GlobalTheory.SplitWeil.KO (Kw w.1) _) (fun _ => rfl)
  have hle : S.levRow t 0 (Nat.zero_le _) ≤ prodLev (S.B.β 0 D.R.m) (locPl G t)
      (fun w => rank_vertex G t w (X := (0, D.R.m)) ⟨Nat.zero_le _, le_rfl⟩) (fun w => GlobalTheory.SplitWeil.KO (Kw w.1) _) := by
    refine inf_le_inf_right _ (iInf_mono fun w => Subgroup.comap_mono ?_)
    intro g hg
    exact givenLevel_zero_le_KO G t w.1 D.R.m hm g hg
  have hmem : finG (G.V (.grid 0 D.R.m)) k ∈ prodLev (S.B.β 0 D.R.m) (locPl G t)
      (fun w => rank_vertex G t w (X := (0, D.R.m)) ⟨Nat.zero_le _, le_rfl⟩) (fun w => GlobalTheory.SplitWeil.KO (Kw w.1) _) ⊓
        UA D.sp.cm (G.V (.grid 0 D.R.m)).gram :=
    Subgroup.mem_inf.2 ⟨hle hk, GlobalTheory.LevSplit.finE_mem_UA _ _⟩
  rw [e, congLev_top] at hmem
  exact (Subgroup.mem_inf.1 hmem).2

end GlobalTheory.FirstRowLat

theorem GlobalTheory.FirstRowLat.rowPt0_inv_mem_stdLat_iff : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ {t : T}, t ∈ U → ∀ k : FinPt G (.grid 0 D.R.m), finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _) →
    ∀ x : WO (G.pS (.chi (firstIx D) D.R.m : Pair T)) (G.pT (.chi (firstIx D) D.R.m : Pair T)),
      actO _ _ (G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ x ∈ stdLat S (.chi (firstIx D) D.R.m : Pair T) ↔ x ∈ stdLat S (.chi (firstIx D) D.R.m : Pair T) := by
  intro D T L sc G W U S μ₀ hL t _ k hk x
  have h1 := GlobalTheory.FirstRowLat.levRow_zero_stab S hL t k hk
  have h2 := GlobalTheory.LastColLat.conj_stab S.N (X := .grid 0 D.R.m) (by simp [DefNode]) k h1
  have e : G.toPair (.chi (firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1 =
      (1, ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1) := by
    show (negGA _ 1, _) = _
    rw [map_one]
    rfl
  rw [e]
  exact GlobalTheory.LastColLat.actO_inv_mem_latO_iff _ _ _ _ _ h2 x

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaContinuationStatement
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
theorem _root_.GlobalTheory.T.seesaw_weil_zeta_continuation : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)))
          (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ)
          (u : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E))
          (f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank))), f ∈ Γ.M'.Pol Bs.ψ Bs.emb →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Γ.M'.heisLine Bs.ψ u) f f₁ →
          (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M'.vac v) →
          ∃ L : ℝ →+ WO (sgn false W₁) X, Continuous L ∧ (∀ t, (L t).map (finPart D) = 0) ∧
            GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ) =
              fun x => deriv (fun t : ℝ => heisO ψ (sgn false W₁) X (L t) (GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) x) 0 := by
  first | exact @GlobalTheory.ThetaRealDeriv.thO_pure_deriv_second | exact GlobalTheory.ThetaRealDeriv.thO_pure_deriv_second | (intros; apply GlobalTheory.ThetaRealDeriv.thO_pure_deriv_second <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingColumnArgsMovedPointConjAtPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingColumnArgs_movedPoint_conj_atPlace : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))), ∀ w ∈ locPl G t,
    ∀ x : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)),
      S.colAt t w (movedPt t j hj ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))) x) = colMove j (kapAt S t j hj k w) (S.colAt t w x) := by
  first | exact @GlobalTheory.TopLevelInv.colAt_movedPt_conj | exact GlobalTheory.TopLevelInv.colAt_movedPt_conj | (intros; apply GlobalTheory.TopLevelInv.colAt_movedPt_conj <;> assumption)
end

