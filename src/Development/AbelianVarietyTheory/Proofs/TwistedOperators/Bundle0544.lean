import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0526
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0751
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0094
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0530
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0527
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
import Development.AbelianVarietyTheory.Definitions.Divisors.OmAUnipFourierInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0302
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedKernelOfVectorSmul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

theorem kkVec_smul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (p : Pair T) (c : ℂ) (f : WO (G.pS p) (G.pT p) → ℂ) (x : FinPt G p.small) (y : FinPt G p.big),
    kkVec S p (c • f) x y = c • kkVec S p f x y := by
  intro D T L sc G W U S p c f x y
  unfold GlobalTheory.TopZeroInv.kkVec fockComp
  have hT : jetTab W S.N.frC p (c • f) (x * S.N.u _) (y * S.N.u _) =
      c • jetTab W S.N.frC p f (x * S.N.u _) (y * S.N.u _) := by
    funext k
    simp only [jetTab, kerFin, fockIn, GlobalTheory.FiniteFock.pureTensorO_smul, Pi.smul_apply, smul_eq_mul,
      GlobalTheory.ChiGrid.GridData.Weil.ker, thetaKO, map_smul]
  have h := (GlobalTheory.JetIdentity.jetOpL (K := ℂ) (wt G p.small) (wt G p.big) (nuEnd G p)).map_smul c
    (jetTab W S.N.frC p f (x * S.N.u _) (y * S.N.u _))
  simp only [GlobalTheory.JetIdentity.jetOpL, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply] at h
  rw [hT, h, smul_comm]

end GlobalTheory.TopZeroInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PGEquivOfBaseW
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GEquivCx

set_option maxHeartbeats 400000 in

theorem pGEquiv_of_baseW : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.toRealDat.BaseW F.lv2 → R.toRealDat.ExAt → R.PGEquiv F := by
  intro hCR D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hB hE
  have hC : GlobalTheory.Hk3.Core R.toRealDat F.lv2 :=
    ⟨hB.lev, hB.grp, hB.fam, hB.models, RealDat.chain_of_weak hB.chain hE, RealDat.thP_of_weak hB.thP hE⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.LiftGroupEquiv.th_thG_act hCR R.toRealDat F.lv2 hC
  refine ⟨fun t g x => ?_, fun j t g x => ?_⟩
  · exact h1 t g x
  · have e : cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.thG j t (R.jV j t ((A3.A.fam.L j t).r g x)) =
        R.gW j (sg0 D A3.A) g (cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.thG j t (R.jV j t x)) :=
      (congrArg (fun y => cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • y) (h2 j t g x)).trans
        (LinearMap.map_smul _ _ _).symm
    exact e

end GlobalTheory.GEquivCx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairFnUpdateMoveV
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.RowVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem negGA_mem_GfC_row (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
  simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
  rw [e]
  exact hg

theorem ker_mul_row (W : G.Weil) (p : Pair T) (F : WO (G.pS p) (G.pT p) → ℂ) (g k : GA D (G.V p.small))
    (h k' : GA D (G.V p.big)) : W.ker p F (g * k) (h * k') = W.ker p (W.om p (G.toPair p k k') F) g h := by
  have e : G.toPair p (g * k) (h * k') = G.toPair p g h * G.toPair p k k' := by
    cases p <;> simp [GridData.toPair, map_mul, Prod.ext_iff]
  unfold GridData.Weil.ker
  rw [e]
  simp only [thetaKO, Prod.mk.eta, map_mul, Module.End.mul_apply]

theorem fockComp_mul_row (W : G.Weil) (B : VertexFrames G) (p : Pair T) (hp : p.InRange D.R.m)
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f) (x g : FinPt G p.small) (y h : FinPt G p.big) :
    fockComp W B p f (x * g) (y * h) = fockComp W B p (W.om p (G.toPair p g h) f) x y := by
  have hmem : (G.toPair p g h).1 ∈ GfC (G.pS p) ∧ (G.toPair p g h).2 ∈ GfC (G.pT p) := by
    cases p with
    | chi i j => exact ⟨negGA_mem_GfC_row _ h.2, g.2⟩
    | mu t i j => exact ⟨g.2, h.2⟩
    | core i => exact ⟨negGA_mem_GfC_row _ h.2, g.2⟩
    | top t j => exact ⟨g.2, h.2⟩
  have key : ∀ P, W.ker p (fockIn W B p f P) ((x : GA D (G.V p.small)) * (g : GA D (G.V p.small))) ((y : GA D (G.V p.big)) * (h : GA D (G.V p.big))) =
      W.ker p (fockIn W B p (W.om p (G.toPair p g h) f) P) x y := by
    intro P
    rw [ker_mul_row]
    congr 1
    have e := (GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ _ _ _ _ (W.om p) (W.om_is p hp) W.θ_is
      (G.cartS W.cart p) (G.cartS W.cart p) (G.onS B p) (G.onS B p) (G.onT W.cart p) (G.onT W.cart p) (G.onT B p) (G.onT B p)
      (G.toPair p g h).1 (G.toPair p g h).2
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hmem.1, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hmem.2, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hmem.1, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hmem.2, Matrix.one_mul]) f hf P).2
    simp only [Prod.mk.eta] at e
    exact e
  unfold fockComp
  congr 1
  funext k
  exact key _

theorem kkV_mul_big (S : GridChoice W U) (p : Pair T) (hp : p.InRange D.R.m) (f : WO (G.pS p) (G.pT p) → ℂ)
    (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f) (a : FinPt G p.small) (b h : FinPt G p.big) :
    kkV S p f a (b * h) =
      kkV S p (W.om p (G.toPair p 1 (((S.N.u p.big)⁻¹ * h * S.N.u p.big : FinPt G p.big) : GA D (G.V p.big))) f) a b := by
  have e := fockComp_mul_row W S.N.frC p hp f hf (a * S.N.u _) 1 (b * S.N.u _) ((S.N.u p.big)⁻¹ * h * S.N.u p.big)
  rw [mul_one, OneMemClass.coe_one] at e
  unfold kkV
  rw [show b * h * S.N.u p.big = b * S.N.u p.big * ((S.N.u p.big)⁻¹ * h * S.N.u p.big) by group, e]

theorem kkV_mul_small (S : GridChoice W U) (p : Pair T) (hp : p.InRange D.R.m) (f : WO (G.pS p) (G.pT p) → ℂ)
    (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f) (a g : FinPt G p.small) (b : FinPt G p.big) :
    kkV S p f (a * g) b =
      kkV S p (W.om p (G.toPair p (((S.N.u p.small)⁻¹ * g * S.N.u p.small : FinPt G p.small) : GA D (G.V p.small)) 1) f) a b := by
  have e := fockComp_mul_row W S.N.frC p hp f hf (a * S.N.u _) ((S.N.u p.small)⁻¹ * g * S.N.u p.small) (b * S.N.u _) 1
  rw [mul_one, OneMemClass.coe_one] at e
  unfold kkV
  rw [show a * g * S.N.u p.small = a * S.N.u p.small * ((S.N.u p.small)⁻¹ * g * S.N.u p.small) by group, e]

theorem pairFn_update_moveV (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)) (v : ∀ a, FactorFn G t a)
    (hv : ∀ a, v a ∈ thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    pairFn S x (Function.update y (j + 1) (y (j + 1) * k)) v = pairFn S x y (moveV S j hj k v) := by
  have e : ∀ (i : ℕ) (h : i < D.R.m), moveV S j hj k v (.inl ⟨i, h⟩) = v (.inl ⟨i, h⟩) := fun i h =>
    (Function.update_of_ne Sum.inl_ne_inr _ _).trans (Function.update_of_ne Sum.inl_ne_inr _ _)
  have hcol : colV S (moveV S j hj k v) x = colV S v x := by
    simp only [colV, e]
  have key : ∀ (i : ℕ) (hi : i < D.R.m),
      kkV S (.chi i D.R.m) (v (.inr ⟨i, hi⟩)) (Function.update y (j + 1) (y (j + 1) * k) i)
        (Function.update y (j + 1) (y (j + 1) * k) (i + 1)) =
      kkV S (.chi i D.R.m) (moveV S j hj k v (.inr ⟨i, hi⟩)) (y i) (y (i + 1)) := by
    intro i hi
    by_cases h1 : i = j
    · subst h1
      rw [Function.update_of_ne (show i ≠ i + 1 by omega), Function.update_self]
      have hm : moveV S i hj k v (.inr ⟨i, hi⟩) =
          W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) 1 (moved S i k)) (v (.inr ⟨i, hi⟩)) :=
        (Function.update_of_ne (by simp) _ _).trans (Function.update_self _ _ _)
      rw [hm]
      exact kkV_mul_big S (.chi i D.R.m) (show i + 1 ≤ D.R.m ∧ D.R.m ≤ D.R.m from ⟨by omega, le_rfl⟩) _ (hv (.inr ⟨i, hi⟩)) (y i) (y (i + 1)) k
    by_cases h2 : i = j + 1
    · subst h2
      rw [Function.update_self, Function.update_of_ne (show j + 1 + 1 ≠ j + 1 by omega)]
      have hm : moveV S j hj k v (.inr ⟨j + 1, hi⟩) =
          W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (v (.inr ⟨j + 1, hi⟩)) :=
        Function.update_self _ _ _
      rw [hm]
      exact kkV_mul_small S (.chi (j + 1) D.R.m) (show j + 1 + 1 ≤ D.R.m ∧ D.R.m ≤ D.R.m from ⟨by omega, le_rfl⟩) _ (hv (.inr ⟨j + 1, hi⟩))
        (y (j + 1)) k (y (j + 1 + 1))
    · rw [Function.update_of_ne h2, Function.update_of_ne (show i + 1 ≠ j + 1 by omega)]
      have hm : moveV S j hj k v (.inr ⟨i, hi⟩) = v (.inr ⟨i, hi⟩) :=
        (Function.update_of_ne (by simp; omega) _ _).trans (Function.update_of_ne (by simp; omega) _ _)
      rw [hm]
  have hrow : rowV S v (Function.update y (j + 1) (y (j + 1) * k)) = rowV S (moveV S j hj k v) y := by
    simp only [rowV, key]
  rw [pairFn, pairFn, hcol, hrow]

end GlobalTheory.RowVertexInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialFourierSumInverseOfLatticeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.FlipMatch.FourierInv

open ValuativeRel

theorem card_res_pow (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (e : ℕ) : Fintype.card (Res k e) = resCard k ^ e := by
  rw [← Nat.card_eq_fintype_card]
  have hne : IsLocalRing.maximalIdeal 𝒪[k] ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have hq := cardQuot_pow_of_prime (P := IsLocalRing.maximalIdeal 𝒪[k]) hne (i := e)
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at hq
  exact hq

theorem fourierSum_invFourierSum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A : Type) [Fintype A] [DecidableEq A] (C : Type) [Fintype C] [DecidableEq C] (ψ : AddChar k Circle) (ϖ : kˣ) (n : ℕ) (P : Finset C), IsUnif ϖ → HasConductor ψ 1 →
    ∀ Ξ : Matrix A C k → ℂ, HasDepth ϖ n (blockLat ϖ n P) Ξ → fourierSum ψ ϖ n P (invFourierSum ψ ϖ n P Ξ) = Ξ := by
  intro k _ _ _ _ A _ _ C _ _ ψ ϖ n P hϖ hψ Ξ hΞ
  funext Y
  rw [fourierSum_apply]
  split_ifs with hY
  · let r : A → P → 𝒪[k] := fun i j => ⟨((ϖ ^ n : kˣ) : k) * Y i j, hY i j j.2⟩
    let S₀ : A → P → Res k n := fun i j => Ideal.Quotient.mk _ (r i j)
    set M : Matrix A P k := (ϖ ^ n)⁻¹ • liftRes S₀ with hM
    have h0 : 0 < valuation k ((ϖ ^ n : kˣ) : k) := zero_lt_iff.2 (by simp)
    have hdiff : ∀ i (j : P), Y i j - M i j ∈ 𝒪[k] := fun i j => by
      have h1 : ((Quotient.out (S₀ i j) : 𝒪[k]) - r i j) ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ n :=
        Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out _)
      rw [GlobalTheory.SplitFlip.Model.val_le_iff_mem hϖ] at h1
      have e1 : Y i j - M i j = -((((ϖ ^ n)⁻¹ : kˣ) : k) * (((Quotient.out (S₀ i j) : 𝒪[k]) - r i j : 𝒪[k]) : k)) := by
        simp only [hM, Matrix.smul_apply, Units.smul_def, smul_eq_mul, liftRes, Matrix.of_apply, r]
        push_cast
        rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ϖ.ne_zero), one_mul]
        ring
      rw [e1, Valuation.mem_integer_iff, Valuation.map_neg, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      exact inv_mul_le_one_of_le₀ h1 h0.le
    have triv : ∀ y : k, y ∈ 𝒪[k] → ψ y = 1 := fun y hy =>
      (hψ 1).2 le_rfl y (by simpa using (Valuation.mem_integer_iff _ _).1 hy)
    have hpair : ∀ T : A → P → Res k n,
        ψ (pairCols P Y (liftRes T)) = ψ (pairCols P (setCols P Y M) (liftRes T)) := fun T => by
      have e2 : pairCols P Y (liftRes T) = pairCols P (setCols P Y M) (liftRes T) +
          ∑ i, ∑ j : P, liftRes T i j * (Y i j - M i j) := by
        simp only [pairCols, setCols, Matrix.of_apply, Finset.coe_mem, dif_pos, Subtype.coe_eta,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e2, AddChar.map_add_eq_mul, triv _ (Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
        mul_mem (liftRes_mem T i j) (hdiff i j)), mul_one]
    have hinv : Ξ (setCols P Y M) = Ξ Y := by
      have e3 : setCols P Y M = Y + Matrix.of fun i j => if h : j ∈ P then M i ⟨j, h⟩ - Y i j else 0 := by
        ext i j; by_cases h : j ∈ P <;> simp [setCols, h]
      rw [e3]
      refine hΞ.2 Y _ (GlobalTheory.SplitFlip.FourierDepth.mem_matLat_smul_blockLat.2 ⟨fun i j hj => ?_, fun i j hj => ?_⟩)
      · simp only [Matrix.of_apply, dif_pos hj]
        have := neg_mem (hdiff i ⟨j, hj⟩)
        simpa using this
      · simp [hj]
    simp_rw [hpair]
    rw [GlobalTheory.SplitFlip.Model.sum_invFourierSum hϖ hψ n P Ξ Y S₀]
    have hq : (resCard k : ℂ) ≠ 0 := by
      show ((Nat.card 𝓀[k] : ℕ) : ℂ) ≠ 0
      exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField 𝒪[k])).ne'
    have hc : ((resCard k : ℂ) ^ (n * Fintype.card A * P.card))⁻¹ *
        ((resCard k : ℂ) ^ n) ^ (Fintype.card A * P.card) = 1 := by
      rw [← pow_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq)]
    rw [← hM, hinv, card_res_pow, Nat.cast_pow, ← mul_assoc, hc, one_mul]
  · symm
    refine hΞ.1 Y fun h => hY ?_
    exact (GlobalTheory.SplitFlip.FourierDepth.mem_matLat_blockLat.1 h).1

end GlobalTheory.FlipMatch.FourierInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathArgsOfNotMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipRun

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def sandwich {X Y Z U : Node} {A : Path T X Y} {r : Path T Y Z} {B' : Path T Z U} (α : PureT G A) (σ : TotT G r)
    (β : PureT G B') : TotT G ((A.comp r).comp B') :=
  σ.sum fun d c => Finsupp.single ((α.append d).append β) c

def RepFinAt {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) {X Y : Node} (p : Path T X Y) (e : AE D) (τ : TotT G p)
    (Tl : ∀ w, (locGrid G t w).Args → ℂ) : Prop :=
  ∃ φ : PureT G p → PureT G p, (∀ d ∈ τ.support, VecAll ρ e p (φ d) d) ∧
    ∀ x : ArgT G p, HalfAll e p x → (τ.sum fun d c => c * famProd p (φ d) x) = ∏ w ∈ locPl G t, Tl w (pathArgs B t w p x)

section Helpers

theorem arrows_comp_eq {X Y : Node} (p : Path T X Y) : ∀ {Z : Node} (q : Path T Y Z), (p.comp q).arrows = p.arrows ++ q.arrows
  | _, .nil => by simp [Path.comp, Path.arrows]
  | _, .snoc a q => by simp [Path.comp, Path.arrows, arrows_comp_eq p q]

theorem onGrid_comp {m : ℕ} {t : T} {X Y Z : Node} {p : Path T X Y} {q : Path T Y Z} (hp : OnGrid m t p) (hq : OnGrid m t q) :
    OnGrid m t (p.comp q) := fun a ha => by
  rw [arrows_comp_eq] at ha
  rcases List.mem_append.1 ha with h | h
  exacts [hp a h, hq a h]

theorem onGrid_routeSmall {m : ℕ} (t : T) {i j : ℕ} (hi : i < m) (hj : j < m) : OnGrid m t (routeSmall t i j) := by
  intro a ha
  simp only [routeSmall, Path.arrows, List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact Or.inr ⟨i, j, hi.le, hj, rfl⟩
  · exact Or.inl ⟨i, j, hi, hj.le, rfl⟩

theorem onGrid_routeBig {m : ℕ} (t : T) {i j : ℕ} (hi : i < m) (hj : j < m) : OnGrid m t (routeBig t i j) := by
  intro a ha
  simp only [routeBig, Path.arrows, List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact Or.inl ⟨i, j + 1, hi, hj, rfl⟩
  · exact Or.inr ⟨i + 1, j, hi, hj, rfl⟩

theorem tensE_add (W : G.Weil) {X Y : Node} (p : Path T X Y) (Q : PolE G →₀ ℂ) (τ τ' : TotT G p) :
    tensE W p Q (τ + τ') = tensE W p Q τ + tensE W p Q τ' := by
  unfold tensE tensT
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr fun P _ => ?_
  refine Finsupp.sum_add_index' (fun _ => by simp) fun d a b => ?_
  rw [mul_add, Finsupp.single_add]

theorem tensE_zero (W : G.Weil) {X Y : Node} (p : Path T X Y) (Q : PolE G →₀ ℂ) : tensE W p Q 0 = 0 := by
  unfold tensE tensT
  simp

theorem tensE_sum (W : G.Weil) {X Y : Node} (p : Path T X Y) (Q : PolE G →₀ ℂ) {ι : Type} (s : Finset ι) (f : ι → TotT G p) :
    tensE W p Q (∑ κ ∈ s, f κ) = ∑ κ ∈ s, tensE W p Q (f κ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tensE_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, tensE_add, ih]

theorem liftT_sum (W : G.Weil) (M : Vol G) {X Y : Node} (p : Path T X Y) {ι : Type} (s : Finset ι) (f : ι → TotT G p) (F : Fn G X) :
    liftT W M p (∑ κ ∈ s, f κ) F = ∑ κ ∈ s, liftT W M p (f κ) F := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [liftT]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, liftT_add, ih]

abbrev latA (G : GridData L sc) (a : Arrow T) : AddSubgroup (WO (G.pS a.pair) (G.pT a.pair)) :=
  latO (G.pS a.pair) (G.pT a.pair) (G.latS a.pair : Set _) (G.latT a.pair : Set _) fun _ => True

theorem arrow_data {W : G.Weil} (ρ : RealMatch W) {μ₀ : T} (hL : L.Is μ₀) {t : T} {a : Arrow T} (ha : IsGridArrow D.R.m t a) :
    IsSelfDualC (G.pS a.pair) (G.latS a.pair) ∧ IsSelfDualC (G.pT a.pair) (G.latT a.pair) ∧ W.IsVac a.pair (vacOf ρ a) := by
  rcases ha with ⟨i, j, hi, hj, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
  · exact ⟨isSelfDualC_neg (node_isV G hL (X := .grid (i + 1) j) ⟨hi, hj⟩).sd, (node_isV G hL (X := .grid i j) ⟨hi.le, hj⟩).sd,
      ρ.vX_is i j hi hj⟩
  · exact ⟨(node_isV G hL (X := .grid i j) ⟨hi, hj.le⟩).sd, (node_isV G hL (X := .grid i (j + 1)) ⟨hi, hj⟩).sd,
      ρ.vT_is t i j hi hj⟩

theorem exists_arrowModel {W : G.Weil} (ρ : RealMatch W) {μ₀ : T} (hL : L.Is μ₀) {t : T} {e : AE D}
    (he : IsIdemSum e (locPl G t)) {a : Arrow T} (ha : IsGridArrow D.R.m t a) :
    ∃ Tm : Sch G a →ₗ[ℂ] Sch G a,
      (∀ φ f, IsLocVec W a.pair e (vacOf ρ a) φ f ↔ IsSBHalf e (latA G a) φ ∧ f = Tm φ) ∧
      (∀ φ, IsSBHalf e (latA G a) φ → Tm φ = 0 → φ = 0) ∧
      ∀ φ, IsSBHalf e (latA G a) φ → IsThetaFunO W.ψ _ _ (Tm φ) := by
  obtain ⟨hS, hT, hv⟩ := arrow_data ρ hL ha
  obtain ⟨T₀, h0, h1⟩ := LocTensor.exists_model hS hT he hv
  obtain ⟨⟨Tm, hTm⟩, h2⟩ := h1 _ (GlobalTheory.isSBHalf_halfInd e _)
  have hm := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hi := GlobalTheory.PlaceVec.idemSum_infPart he
  have hf : vacOf ρ a ≠ 0 := by
    have h3 := hTm.vac
    rw [one_smul, ← h2 Tm hTm] at h3
    exact h3 ▸ h0
  refine ⟨Tm, fun φ f => ⟨fun h => ⟨h.1, h.2.2 Tm hTm⟩, fun h => ⟨h.1, ?_⟩⟩, fun φ hφ h => ?_, fun φ hφ => ?_⟩
  · rw [h.2, ← (h1 φ h.1).2 Tm hTm]
    exact h1 φ h.1
  · by_contra h'
    exact GlobalTheory.PlaceModelInj.placeModel_ne_zero D W.ψ _ _ _ _ e _ φ Tm W.ψ_std hS hT hm he.2 hi hTm hf hφ h' h
  · exact GlobalTheory.SchrTheta.isTheta_placeModel D W.ψ W.ψ_std _ _ _ _ hS hT e hm hi _ hv.2.theta Tm hTm φ hφ

theorem OnGrid.init {m : ℕ} {t : T} {X : Node} {a : Arrow T} {p : Path T X a.src} (h : OnGrid m t (.snoc a p)) : OnGrid m t p :=
  fun b hb => h b (List.mem_append_left [a] hb)

theorem OnGrid.last {m : ℕ} {t : T} {X : Node} {a : Arrow T} {p : Path T X a.src} (h : OnGrid m t (.snoc a p)) :
    IsGridArrow m t a := h a (List.mem_append_right p.arrows (List.mem_singleton_self a))

theorem vecAll_unique {W : G.Weil} (ρ : RealMatch W) {μ₀ : T} (hL : L.Is μ₀) {t : T} {e : AE D}
    (he : IsIdemSum e (locPl G t)) {X : Node} : ∀ {Y : Node} (p : Path T X Y), OnGrid D.R.m t p → ∀ (φ φ' d : PureT G p),
      VecAll ρ e p φ d → VecAll ρ e p φ' d → φ = φ'
  | _, .nil, _, _, _, _, _, _ => rfl
  | _, .snoc a p, hg, φ, φ', d, h, h' => by
    obtain ⟨Tm, h1, h2, -⟩ := exists_arrowModel ρ hL he hg.last
    obtain ⟨a1, a2⟩ := (h1 _ _).1 h.2
    obtain ⟨b1, b2⟩ := (h1 _ _).1 h'.2
    refine Prod.ext (vecAll_unique ρ hL he p hg.init φ.1 φ'.1 d.1 h.1 h'.1) (sub_eq_zero.1 (h2 _ ?_ ?_))
    · exact (LocTensor.sbSpace e (latA G a)).sub_mem a1 b1
    · rw [map_sub, ← a2, ← b2, sub_self]

theorem vecAll_append {W : G.Weil} (ρ : RealMatch W) (e : AE D) {X Y : Node} (p : Path T X Y) (φ d : PureT G p) :
    ∀ {Z : Node} (q : Path T Y Z) (φ' d' : PureT G q),
      VecAll ρ e (p.comp q) (φ.append φ') (d.append d') ↔ VecAll ρ e p φ d ∧ VecAll ρ e q φ' d'
  | _, .nil, _, _ => (and_iff_left trivial).symm
  | _, .snoc a q, φ', d' => by
    show VecAll ρ e (p.comp q) (φ.append φ'.1) (d.append d'.1) ∧ IsLocVec W a.pair e (vacOf ρ a) φ'.2 d'.2 ↔ _
    rw [vecAll_append ρ e p φ d q φ'.1 d'.1, and_assoc]
    rfl

theorem famProd_append {X Y : Node} (p : Path T X Y) (φ : PureT G p) (x : ArgT G p) :
    ∀ {Z : Node} (q : Path T Y Z) (φ' : PureT G q) (y : ArgT G q),
      famProd (p.comp q) (φ.append φ') (x.append y) = famProd p φ x * famProd q φ' y
  | _, .nil, _, _ => (mul_one _).symm
  | _, .snoc a q, φ', y => by
    show famProd (p.comp q) (φ.append φ'.1) (x.append y.1) * φ'.2 y.2 = _ * (famProd q φ'.1 y.1 * φ'.2 y.2)
    rw [famProd_append p φ x q φ'.1 y.1, mul_assoc]

theorem halfAll_append (e : AE D) {X Y : Node} (p : Path T X Y) (x : ArgT G p) :
    ∀ {Z : Node} (q : Path T Y Z) (y : ArgT G q), HalfAll e (p.comp q) (x.append y) ↔ HalfAll e p x ∧ HalfAll e q y
  | _, .nil, _ => (and_iff_left trivial).symm
  | _, .snoc a q, y => by
    show HalfAll e (p.comp q) (x.append y.1) ∧ IsHalf e y.2 ↔ _
    rw [halfAll_append e p x q y.1, and_assoc]
    rfl

theorem exists_append {S : Arrow T → Type} {X Y : Node} (p : Path T X Y) :
    ∀ {Z : Node} (q : Path T Y Z) (z : (p.comp q).Fam S), ∃ (x : p.Fam S) (y : q.Fam S), z = x.append y
  | _, .nil, z => ⟨z, (), rfl⟩
  | _, .snoc a q, z => by
    obtain ⟨x, y, h⟩ := exists_append p q z.1
    exact ⟨x, (y, z.2), Prod.ext h rfl⟩

theorem edges_comp {X Y Z : Node} (p : Path T X Y) (q : Path T Y Z) : edges (p.comp q) = edges p ++ edges q := by
  rw [edges, arrows_comp_eq, List.map_append]; rfl

theorem edges_snoc {X : Node} (a : Arrow T) (p : Path T X a.src) : edges (.snoc a p) = edges p ++ [edgeOf a] := by
  simp [edges, Path.arrows]

theorem edges_bound {m : ℕ} {t : T} {i j : ℕ} : ∀ {Y : Node} (p : Path T (.grid i j) Y), OnGrid m t p →
    ∃ i' j', Y = .grid i' j' ∧ i ≤ i' ∧ j' ≤ j ∧ (edges p).Nodup ∧
      ∀ b ∈ edges p, i ≤ b.src.1 ∧ b.tgt.1 ≤ i' ∧ j' ≤ b.tgt.2 ∧ b.src.2 ≤ j
  | _, .nil, _ => ⟨i, j, rfl, le_rfl, le_rfl, List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
  | _, .snoc a p, hg => by
    obtain ⟨i', j', h1, h2, h3, h4, h5⟩ := edges_bound p hg.init
    rw [edges_snoc]
    rcases hg.last with ⟨k, l, -, -, rfl⟩ | ⟨k, l, -, -, rfl⟩
    · obtain ⟨rfl, rfl⟩ : k = i' ∧ l = j' := Node.grid.inj h1
      refine ⟨k + 1, l, rfl, by omega, h3, List.nodup_append.2 ⟨h4, List.nodup_singleton _, fun b hb c hc e => ?_⟩, fun b hb => ?_⟩
      · obtain rfl := List.mem_singleton.1 hc
        subst e
        have := (h5 _ hb).2.1
        simp [edgeOf] at this
      · rcases List.mem_append.1 hb with hb | hb
        · have := h5 b hb; omega
        · obtain rfl := List.mem_singleton.1 hb
          simp only [edgeOf]; omega
    · obtain ⟨rfl, rfl⟩ : k = i' ∧ l + 1 = j' := Node.grid.inj h1
      refine ⟨k, l, rfl, h2, by omega, List.nodup_append.2 ⟨h4, List.nodup_singleton _, fun b hb c hc e => ?_⟩, fun b hb => ?_⟩
      · obtain rfl := List.mem_singleton.1 hc
        subst e
        have := (h5 _ hb).2.2.1
        simp [edgeOf] at this
      · rcases List.mem_append.1 hb with hb | hb
        · have := h5 b hb; omega
        · obtain rfl := List.mem_singleton.1 hb
          simp only [edgeOf]; omega

theorem pathArgs_of_notMem (B : Frames G) (t : T) (w : Pl D.host.E) {X : Node} :
    ∀ {Y : Node} (p : Path T X Y) (x : ArgT G p) (b), b ∉ edges p → pathArgs B t w p x b = 0
  | _, .nil, _, _, _ => rfl
  | _, .snoc a p, x, b, hb => by
    rw [edges_snoc, List.mem_append, not_or, List.mem_singleton] at hb
    show argAt B t w a x.2 b (pathArgs B t w p x.1 b) = 0
    rw [argAt, dif_neg (Ne.symm hb.2), pathArgs_of_notMem B t w p x.1 b hb.1]

theorem pathArgs_snoc (B : Frames G) (t : T) (w : Pl D.host.E) {X : Node} (a : Arrow T) (p : Path T X a.src)
    (x : ArgT G (.snoc a p)) :
    pathArgs B t w (.snoc a p) x = Function.update (pathArgs B t w p x.1) (edgeOf a) (locArg B t w a x.2) := by
  funext b
  show argAt B t w a x.2 b (pathArgs B t w p x.1 b) = _
  by_cases h : edgeOf a = b
  · subst h
    rw [argAt, dif_pos rfl, Function.update_self]; rfl
  · rw [argAt, dif_neg h, Function.update_of_ne (Ne.symm h)]

theorem pathArgs_append (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : Node} (p : Path T X Y) (x : ArgT G p) :
    ∀ {Z : Node} (q : Path T Y Z) (y : ArgT G q), (∀ b ∈ edges q, b ∉ edges p) →
      pathArgs B t w (p.comp q) (x.append y) = pathArgs B t w p x + pathArgs B t w q y
  | _, .nil, _, _ => (add_zero _).symm
  | _, .snoc a q, y, h => by
    rw [edges_snoc] at h
    have h1 := pathArgs_append B t w p x q y.1 fun b hb => h b (List.mem_append_left _ hb)
    have h2 := pathArgs_of_notMem B t w p x _ (h _ (List.mem_append_right _ (List.mem_singleton_self _)))
    refine (pathArgs_snoc B t w a (p.comp q) (x.append y.1, y.2)).trans ?_
    rw [pathArgs_snoc]
    funext b
    by_cases hb : b = edgeOf a
    · subst hb
      rw [Pi.add_apply, Function.update_self, Function.update_self, h2, zero_add]
    · rw [Pi.add_apply, Function.update_of_ne hb, Function.update_of_ne hb, h1, Pi.add_apply]

end Helpers

end GlobalTheory.FlipRun

end
end

