import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0661
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1415
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselMeanPeriodConvergesContinuous
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0674
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0667
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0526
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinrankInvFunBranch
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0670

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicModelInvariantSub
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.KFinAlg

def tensDeg (F : Type) [Field F] [NumberField F] (P Q R S D : ℕ) : Submodule ℂ (GlobalTheory.RealLift.Tens F P Q R S) :=
  LinearMap.range (PiTensorProduct.map fun _ : InfinitePlace F =>
    (MvPolynomial.restrictTotalDegree (Formalism.BasicNotions.TH.Ix P Q × Formalism.BasicNotions.TH.Ix R S) ℂ D).subtype)

theorem tensDeg_mono {F : Type} [Field F] [NumberField F] {P Q R S D D' : ℕ} (h : D ≤ D') :
    tensDeg F P Q R S D ≤ tensDeg F P Q R S D' := by
  have hi : MvPolynomial.restrictTotalDegree (Formalism.BasicNotions.TH.Ix P Q × Formalism.BasicNotions.TH.Ix R S) ℂ D ≤
      MvPolynomial.restrictTotalDegree _ ℂ D' := fun x hx => by
    rw [MvPolynomial.mem_restrictTotalDegree] at hx ⊢; omega
  rintro _ ⟨t, rfl⟩
  refine ⟨PiTensorProduct.map (fun _ => Submodule.inclusion hi) t, ?_⟩
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  rfl

theorem exists_tensDeg {F : Type} [Field F] [NumberField F] {P Q R S : ℕ} (T : GlobalTheory.RealLift.Tens F P Q R S) :
    ∃ D, T ∈ tensDeg F P Q R S D := by
  classical
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    refine ⟨Finset.univ.sup fun w => (m w).totalDegree, r • PiTensorProduct.tprod ℂ (fun w =>
      (⟨m w, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 (Finset.le_sup (f := fun w => (m w).totalDegree)
        (Finset.mem_univ w))⟩ : MvPolynomial.restrictTotalDegree _ ℂ _)), ?_⟩
    simp [PiTensorProduct.map_tprod]
  | add x y hx hy =>
    obtain ⟨D₁, h₁⟩ := hx
    obtain ⟨D₂, h₂⟩ := hy
    exact ⟨max D₁ D₂, Submodule.add_mem _ (tensDeg_mono (le_max_left _ _) h₁) (tensDeg_mono (le_max_right _ _) h₂)⟩

theorem exp_stable {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (hU : GlobalTheory.RealLift.IsExp L U)
    (N : Submodule ℂ V) (hN : ∀ y ∈ N, L y ∈ N) : ∀ y ∈ N, U y ∈ N := by
  intro y hy
  by_contra hne
  obtain ⟨l, hl1, hl2⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hne inferInstance
  have hpow : ∀ m : ℕ, (L ^ m) y ∈ N := by
    intro m
    induction m with
    | zero => simpa using hy
    | succ m ih => rw [pow_succ', Module.End.mul_apply]; exact hN _ ih
  have hz : ∀ m : ℕ, ((m.factorial : ℂ))⁻¹ * l ((L ^ m) y) = 0 := fun m => by
    have hm : l ((L ^ m) y) ∈ N.map l := Submodule.mem_map_of_mem (hpow m)
    rw [hl2, Submodule.mem_bot] at hm
    rw [hm, mul_zero]
  have h1 := hU y l
  simp only [hz] at h1
  exact hl1 (h1.unique hasSum_zero)

theorem polKFin (fockFirst : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∃ (A : InfinitePlace F → Matrix (Fin a) (Formalism.BasicNotions.TH.Ix (a - Γ.p) Γ.p) ℂ)
      (Φ : GlobalTheory.RealLift.Tens F (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))
      (c : InfinitePlace F → ℂ),
      (∀ w, GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w))) (A w)) ∧
      (∀ w, Γ.V.θ w * A w = A w * Formalism.BasicNotions.TH.Jm (a - Γ.p) Γ.p) ∧
      LinearMap.range Φ = Γ.M.Pol Bs.ψ Bs.emb ∧
      GlobalTheory.RealLift.ActsBy Bs.emb A (om.comp (MonoidHom.inl _ _)) Φ
        (Formalism.BasicNotions.TH.fockAct1 (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) c) : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb,
    ∃ P : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), FiniteDimensional ℂ P ∧ P ≤ Γ.M.Pol Bs.ψ Bs.emb ∧
      f ∈ P ∧ ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.V Bs.emb, ∀ g ∈ P, ∃ g₁ ∈ P,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) (⇑g) (⇑g₁) := by
  intro hPr F E _ _ _ _ _ σ Bs a a' Γ Xc om om' hT f hf
  classical
  obtain ⟨A, Φ, c, hA, hAθ, hr, hact⟩ := fockFirst hPr F E σ Bs a a' Γ Xc om om' hT
  have hb := hT.base
  have hwp : GlobalTheory.WeilM.IsUWeilPair (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.WeilM.adeleClass F) Bs.ψ (-1)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.W.J) Γ.M.co Xc.β (Xc.β / Xc.α) om := hT.weil
  have hadm := fun g => (hwp.isUSplitting).adm g
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf
  obtain ⟨D, hD⟩ := exists_tensDeg T
  haveI : FiniteDimensional ℂ (tensDeg F (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) D) :=
    LinearMap.finiteDimensional_range _
  refine ⟨(tensDeg F _ _ _ _ D).map Φ, inferInstance, hr ▸ LinearMap.map_le_range, ⟨T, hD, rfl⟩, ?_⟩
  rintro k hk _ ⟨T', hT', rfl⟩
  obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.T.unitaryLieElements_generate_oneParamLines F E σ (Fin a) _ _ Bs.emb
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J) 1 A Γ.V.θ hb.cm hA hAθ k hk.1 hk.2
  let L := GlobalTheory.RealLift.sumPl (fun w => Formalism.BasicNotions.TH.fockAct1 (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) (Yg w) +
    (c w * (Yg w).trace) • (1 : Module.End ℂ _))
  have hloc : GlobalTheory.RealLift.LocFin L := GlobalTheory.RealLift.locFin_sumPl _ _ _ fun w v => by
    obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights _ _ _ _).1 v
    exact ⟨W, hW, hv, fun y hy => W.add_mem (hs (Yg w) (hKC w) y hy) (W.smul_mem _ hy)⟩
  obtain ⟨U, hexp, hSA⟩ := GlobalTheory.T.weakExponential_action_on_fockVectors F (Fin a × Fin (a + a')) _ Φ L ((om.comp (MonoidHom.inl _ _)).comp γ) hloc
    (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Yg hgen T)
  let Lw : ∀ w : InfinitePlace F, Module.End ℂ (Formalism.BasicNotions.TH.Pol (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) :=
    fun w => Formalism.BasicNotions.TH.fockAct1 (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) (Yg w) +
      (c w * (Yg w).trace) • (1 : Module.End ℂ _)
  let Nw : ∀ w : InfinitePlace F, Submodule ℂ (Formalism.BasicNotions.TH.Pol (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) :=
    fun _ => MvPolynomial.restrictTotalDegree _ ℂ D
  have hN : ∀ i, ∀ z ∈ Nw i, Lw i z ∈ Nw i := by
    intro i z hz
    simp only [Lw, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact Submodule.add_mem _ (GlobalTheory.FockPolGK.kStable1 _ _ _ _ D (Yg i) (hKC i) z hz) (Submodule.smul_mem _ _ hz)
  have hLst : ∀ y ∈ tensDeg F _ _ _ _ D, L y ∈ tensDeg F _ _ _ _ D := by
    intro y hy
    change GlobalTheory.RealLift.sumPl Lw y ∈ _
    rw [GlobalTheory.RealLift.sumPl, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun w _ => GlobalTheory.RealLift.atPl_mem_range_map Lw Nw hN w y hy
  refine ⟨Φ (U T'), ⟨U T', exp_stable hexp _ hLst T' hT', rfl⟩, ?_⟩
  have h1 := hSA T'
  rw [MonoidHom.comp_apply, hγ1] at h1
  exact (GlobalTheory.RealLift.actsLaws F _ (Φ T') (Φ (U T')) (Φ (U T'))).2.1 _ (map_zero _) h1

def pureL {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F]
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun f := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ
  map_add' f g := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
  map_smul' c f := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem algD_kFinite : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ ΦD ∈ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb,
    ∃ U : Submodule ℂ ((Fin a × Fin (a + a') → AF F) → ℂ), FiniteDimensional ℂ U ∧
      U ≤ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb ∧ ΦD ∈ U ∧
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.V Bs.emb, ∀ x ∈ U, om (k, 1) x ∈ U := by
  intro hPr F E _ _ _ _ _ σ Bs a a' Γ Xc om om' hT ΦD hΦ
  have hPair := GlobalTheory.ThK.RealUniq.isPair_V hT
  have hstdM := hPair.good.std
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hSB, hcof, rfl⟩ := hx
    obtain ⟨P, hPfin, hPle, hfP, hPst⟩ := polKFin GlobalTheory.T.exists_archimedean_matrices_triple hPr F E σ Bs a a' Γ Xc om om' hT f hf
    have hstd : ∀ᶠ v in Filter.cofinite,
        φ v = Set.indicator {x : Fin a × Fin (a + a') → Fv F v |
          ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := by
      filter_upwards [hcof, hstdM] with v h1 h2
      rw [h1, h2]
    refine ⟨P.map (pureL φ), inferInstance, ?_, ⟨f, hfP, rfl⟩, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      exact Submodule.subset_span ⟨g, φ, hPle hg, hSB, hcof, rfl⟩
    · rintro k hk _ ⟨g, hg, rfl⟩
      obtain ⟨g₁, hg₁, hA⟩ := hPst k hk g hg
      have key : om (k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ :=
        hA _ (GlobalTheory.ThK.EvUniqInf.rest_pure _ _ hSB hstd)
      exact ⟨g₁, hg₁, key.symm⟩
  | zero =>
    exact ⟨⊥, inferInstance, bot_le, Submodule.zero_mem _, fun k _ x hx => by
      rw [Submodule.mem_bot] at hx; subst hx; rw [map_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨U₁, h1, l1, m1, s1⟩ := hx
    obtain ⟨U₂, h2, l2, m2, s2⟩ := hy
    refine ⟨U₁ ⊔ U₂, inferInstance, sup_le l1 l2, Submodule.add_mem_sup m1 m2, fun k hk z hz => ?_⟩
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hz
    rw [map_add]
    exact Submodule.add_mem_sup (s1 k hk y₁ hy₁) (s2 k hk y₂ hy₂)
  | smul c x _ hx =>
    obtain ⟨U, h, l, m, s⟩ := hx
    exact ⟨U, h, l, U.smul_mem c m, s⟩

end GlobalTheory.SquareAgree.KFinAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFrameOfGridLatticeLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.FlatPlace

open GlobalTheory.LocMod (Place Frame)

section Entries

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem epsV_even (t : T) (w : Pl D.host.E) {j : ℕ} (hj : Even j) : epsV G t w (D.R.m, j) = 1 := by
  rw [epsV_apply]
  split_ifs
  · refine Units.ext ?_
    rw [sgnAt, GlobalTheory.SplitFlip.diagGL_val, Units.val_one, ← diagonal_one]
    congr 1
    funext x
    rw [if_neg (fun h => (Nat.not_odd_iff_even.2 hj) h.1)]
    rfl
  · rfl

theorem baseM_val (t : T) (w : Pl D.host.E) (j : ℕ) : (baseM G t w j).val = diagonal fun x =>
    if j = 0 then (((unifAt w : Kw w)) ^ (cosExp G w * (x.val + 1 - topRank (locGrid G t w) j)))⁻¹ else 1 := by
  unfold baseM
  split_ifs with h
  · subst h
    have e : (stair (locGrid G t w) (unifAt w) (cosExp G w) 0)⁻¹ =
        GlobalTheory.SplitFlip.diagGL fun x : Fin ((locGrid G t w).rank ((locGrid G t w).m, 0)) =>
          (unifAt w ^ (cosExp G w * (x.val + 1 - topRank (locGrid G t w) 0)))⁻¹ := by
      refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
      rw [Units.val_mul, stair, GlobalTheory.SplitFlip.diagGL_val, GlobalTheory.SplitFlip.diagGL_val, diagonal_mul_diagonal, Units.val_one,
        ← diagonal_one]
      congr 1
      funext x
      simp
    have e2 := congrArg Units.val e
    rw [GlobalTheory.SplitFlip.diagGL_val] at e2
    refine e2.trans ?_
    congr 1
    funext x
    simp
  · rw [Units.val_one, ← diagonal_one]

theorem mvFr_entries (S : GridChoice W U) {t : T} (ht : t ∈ U) {w : Pl D.host.E} (hw : w ∈ locPl G t) (p : Place D (Kw w))
    {j : ℕ} (hj : j < D.R.m) (hje : Even j) (a : GA D (G.V (.grid D.R.m j)))
    (ha : (mt _ a).map p.π * (frRow S.B t w j hj.le).β = (frRow S.B t w j hj.le).β * (baseM G t w j).val) {c : ℕ}
    (hc : topRank (locGrid G t w) j + c = (locGrid G t w).rank (D.R.m, j)) (r : Fin (G.V (.grid D.R.m j)).rank) :
    (∀ q, (mvFr p a (frRow S.B t w j hj.le) (epsV G t w (D.R.m, j)) (frame hc)).β r (Sum.inl q) =
      ((frameMat _ _ (G.rowDec j hj).ι).map (algebraMap D.host.E (Kw w)) * (loc w (S.βp j)).val) r
        (Fin.cast (topRank_eq G t w hj.le) q)) ∧
    ∀ (q : Fin c) (q' : Fin (D.R.m - 1 - j)), q'.val = q.val →
      (mvFr p a (frRow S.B t w j hj.le) (epsV G t w (D.R.m, j)) (frame hc)).β r (Sum.inr q) =
        algebraMap D.host.E (Kw w) ((G.rowDec j hj).a r q') * frameSign (Kw w) (D.R.m - 1 - j) q' := by
  have hrow := S.row t ht w hw j hj
  unfold IsSumFrame at hrow
  have hT := topRank_eq G t w hj.le
  have key : ∀ z, (mvFr p a (frRow S.B t w j hj.le) (epsV G t w (D.R.m, j)) (frame hc)).β r z =
      (loc w (S.B.β D.R.m j)).val r (Fin.cast (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj.le⟩) (frame hc z)) *
        (if j = 0 then (((unifAt w : Kw w)) ^ (cosExp G w * ((frame hc z).val + 1 - topRank (locGrid G t w) j)))⁻¹ else 1) := by
    intro z
    show ((mt _ a).map p.π * (frRow S.B t w j hj.le).β * (epsV G t w (D.R.m, j)).val) r (frame hc z) = _
    rw [epsV_even t w hje, Units.val_one, Matrix.mul_one, ha, baseM_val, mul_diagonal]
    rfl
  refine ⟨fun q => ?_, fun q q' hq => ?_⟩
  · rw [key]
    have e1 : Fin.cast (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj.le⟩) (frame hc (Sum.inl q)) =
        frame (G.rowDec j hj).rank (Sum.inl (Fin.cast hT q)) := by
      ext; simp [frame]
    have e2 := congrFun (congrFun hrow r) (Sum.inl (Fin.cast hT q))
    rw [submatrix_apply, id, fromCols_apply_inl] at e2
    rw [e1, e2]
    have e3 : (frame hc (Sum.inl q)).val + 1 - topRank (locGrid G t w) j = 0 := by
      have := q.2; simp [frame]
    rw [e3]
    simp
  · rw [key]
    have e1 : Fin.cast (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj.le⟩) (frame hc (Sum.inr q)) =
        frame (G.rowDec j hj).rank (Sum.inr q') := by
      ext; simp [frame, hq, hT]
    have e2 := congrFun (congrFun hrow r) (Sum.inr q')
    rw [submatrix_apply, id, fromCols_apply_inr, mul_diagonal, Matrix.map_apply] at e2
    rw [e1, e2]
    have e3 : (frame hc (Sum.inr q)).val + 1 - topRank (locGrid G t w) j = q'.val + 1 := by
      simp [frame, hq]; omega
    rw [e3]
    have hu : ((unifAt w : Kw w)) ≠ 0 := Units.ne_zero _
    split_ifs
    · field_simp
    · simp

end Entries

section Main

section Alg

variable {k : Type} [Field k]

theorem alg_e (x y : k) (hx : x ≠ 0) (σ i : ℕ) (h : i ≤ σ) : y * 1 = (x ^ σ)⁻¹ * x ^ (σ - i) * (y * x ^ i) := by
  obtain ⟨e, rfl⟩ : ∃ e, σ = i + e := ⟨σ - i, by omega⟩
  rw [Nat.add_sub_cancel_left, pow_add]
  field_simp

theorem scalar_inv_pow_mul_cancel (x y : k) (hx : x ≠ 0) (σ : ℕ) : y * 1 = (x ^ σ)⁻¹ * (x ^ σ * y) := by
  field_simp

theorem alg_e' (x y : k) (hx : x ≠ 0) (σ i : ℕ) (h : i < σ) :
    y * -1 = (x ^ σ)⁻¹ * (-(-((-x) ^ σ * x ^ σ)) / x) * (-1 / x) ^ (σ - 1 - i) * (y * ((-x) ^ i)⁻¹) := by
  obtain ⟨e, rfl⟩ : ∃ e, σ = i + 1 + e := ⟨σ - 1 - i, by omega⟩
  have hx' : -x ≠ 0 := neg_ne_zero.2 hx
  rw [show i + 1 + e - 1 - i = e by omega, show (-1 / x) = (-x)⁻¹ by rw [neg_div, one_div, neg_inv], inv_pow, pow_add (-x),
    pow_succ (-x)]
  have ha : (-x) ^ i ≠ 0 := pow_ne_zero _ hx'
  have hb : (-x) ^ e ≠ 0 := pow_ne_zero _ hx'
  generalize (-x) ^ i = a at ha ⊢
  generalize (-x) ^ e = b at hb ⊢
  field_simp

end Alg

section Core

variable {D : D7} {A B : HSp D} {c : ℕ}

theorem coreMat_iA_bes {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    GlobalTheory.RowUnf.coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iA = frameMat B A d.ι := by
  refine (Matrix.submatrix_mul_equiv _ _ _ _ _).trans ?_
  show Matrix.fromCols (frameMat B A d.ι) (GlobalTheory.RowUnf.midCol d h) *
      Matrix.fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) (0 : Matrix (Fin 1) (Fin A.rank) D.host.E) = _
  rw [Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem coreMat_vecB_bes {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) (x : D.host.E) :
    GlobalTheory.RowUnf.coreMat d h *ᵥ vecB (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)) (fun _ => x) =
      fun k => x * d.a k ⟨σ, by omega⟩ := by
  have e : GlobalTheory.RowUnf.coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iB =
      GlobalTheory.RowUnf.midCol d h := by
    refine (Matrix.submatrix_mul_equiv _ _ _ _ _).trans ?_
    show Matrix.fromCols (frameMat B A d.ι) (GlobalTheory.RowUnf.midCol d h) *
        Matrix.fromRows (0 : Matrix (Fin A.rank) (Fin 1) D.host.E) (1 : Matrix (Fin 1) (Fin 1) D.host.E) = _
    rw [Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, zero_add]
  show GlobalTheory.RowUnf.coreMat d h *ᵥ (_ *ᵥ _) = _
  rw [Matrix.mulVec_mulVec, e]
  funext k
  show ∑ j : Fin 1, GlobalTheory.RowUnf.midCol d h k j * x = _
  simp [GlobalTheory.RowUnf.midCol, mul_comm]

theorem nLine_norm (x : D.host.E) :
    star (fun _ : Fin (GlobalTheory.SeeSaw.Model.nLine D).rank => x) ⬝ᵥ (GlobalTheory.SeeSaw.Model.nLine D).gram *ᵥ (fun _ => x) = -(star x * x) := by
  show ∑ i : Fin 1, star x * ∑ j : Fin 1, (GlobalTheory.SeeSaw.Model.nLine D).gram i j * x = _
  simp [GlobalTheory.RowUnf.nLine_gram]

end Core

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem BesP₂ (ch : Choice R) : BesP ch := by
  intro t w hw p hp M hM j σ hj vN a ha c hc
  have hjm : j < D.R.m := by omega
  have hje : Even j := by
    obtain ⟨k, hk⟩ := D.R.m_even
    exact ⟨k - σ - 1, by omega⟩
  have E := mvFr_entries ch.S.toGridChoice (Set.mem_univ t) hw p hjm hje a ha hc
  have hpr : ∀ x, p.pr x = algebraMap D.host.E (Kw w) x := fun x => by
    rw [Place.pr, hp.2.1]
    exact GlobalTheory.FunObj.Good.cpt_incA w x
  have hxi : p.xi = algebraMap D.host.E (Kw w) D.host.xi0 := hpr _
  have hx0 : algebraMap D.host.E (Kw w) D.host.xi0 ≠ 0 := hxi ▸ GlobalTheory.LocMod.Witness.xi_ne p
  have hTA : (locGrid ch.G t w).rank (D.R.m, j) + j + 1 = topRank (locGrid ch.G t w) j + D.R.m :=
    (topRank_add (G := locGrid ch.G t w) one_le_sLen j).symm
  have hc' : c = 2 * σ + 1 := by omega
  have hc2 : D.R.m - 1 - j = 2 * σ + 1 := by omega
  refine ⟨hc', fun r q => ?_, fun i q hiq r => ?_, fun q hq r => ?_, fun i q hiq r => ?_⟩
  · refine ((E r).1 q).trans ?_
    have e1 : ((besAt ch.G hM j σ hj vN).d.i₀ * (besAt ch.G hM j σ hj vN).o.iA) =
        frameMat (ch.G.V (Node.grid D.R.m j)) (ch.G.V (Node.top j)) (ch.G.rowDec j hjm).ι :=
      coreMat_iA_bes (ch.G.rowDec j hjm) hc2
    rw [e1]
    erw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    exact congrArg₂ (· * ·) (hpr _).symm rfl
  · refine ((E r).2 q ⟨q.val, by omega⟩ rfl).trans ?_
    have hd : (besAt ch.G hM j σ hj vN).d.e r i = (ch.G.rowDec j hjm).a r ⟨q.val, by omega⟩ * D.host.xi0 ^ i.val := by
      show (((ch.G.rowDec j hjm).iso σ (by omega) * diagonal (GlobalTheory.RowChain.lam σ) :
        Matrix (Fin (ch.G.V (Node.grid D.R.m j)).rank) (Fin σ) D.host.E)) r i = _
      erw [mul_diagonal]
      simp only [HermitianOrthogonalExtensionData.iso, submatrix_apply, id, GlobalTheory.RowChain.lam]
      congr 2
      show (ch.G.rowDec j hjm).a r (Fin.castLE (by omega) i) = _
      exact congrArg _ (Fin.ext (by simp [hiq]))
    rw [hd, hpr, hxi, map_mul, map_pow, frameSign, if_neg (by first | omega | (simp only [Fin.val_mk]; omega) | (simp; omega))]
    exact alg_e _ _ hx0 σ i.val (by omega)
  · refine ((E r).2 q ⟨σ, by omega⟩ hq.symm).trans ?_
    have hv : (besAt ch.G hM j σ hj vN).d.i₀ *ᵥ vecB (besAt ch.G hM j σ hj vN).o (besAt ch.G hM j σ hj vN).ζ =
        fun k => D.host.xi0 ^ σ * (ch.G.rowDec j hjm).a k ⟨σ, by omega⟩ :=
      coreMat_vecB_bes (ch.G.rowDec j hjm) hc2 (D.host.xi0 ^ σ)
    rw [hv, hpr, hxi, map_mul, map_pow, frameSign, if_neg (by first | omega | (simp only [Fin.val_mk]; omega) | (simp; omega))]
    exact scalar_inv_pow_mul_cancel _ _ hx0 σ
  · refine ((E r).2 q ⟨q.val, by omega⟩ rfl).trans ?_
    have hd : (besAt ch.G hM j σ hj vN).d.e' r i =
        (ch.G.rowDec j hjm).a r ⟨q.val, by omega⟩ * (star (D.host.xi0 ^ i.val))⁻¹ := by
      show (((ch.G.rowDec j hjm).a.submatrix id (fun i : Fin σ => (Fin.castLE (by omega : σ ≤ D.R.m - 1 - j) i).rev) *
        diagonal (fun a => (star (GlobalTheory.RowChain.lam (D := D) σ a))⁻¹) :
        Matrix (Fin (ch.G.V (Node.grid D.R.m j)).rank) (Fin σ) D.host.E)) r i = _
      erw [mul_diagonal]
      simp only [submatrix_apply, id, GlobalTheory.RowChain.lam]
      congr 2
      show (ch.G.rowDec j hjm).a r (Fin.castLE (by omega) i).rev = _
      exact congrArg _ (Fin.ext (by simp only [Fin.val_rev, Fin.val_castLE]; omega))
    have hz : p.hz (besAt ch.G hM j σ hj vN) = algebraMap D.host.E (Kw w) (-(star (D.host.xi0 ^ σ) * D.host.xi0 ^ σ)) := by
      rw [Place.hz, hpr]
      exact congrArg _ (nLine_norm _)
    have hs : ∀ n : ℕ, star (D.host.xi0 ^ n) = (-D.host.xi0) ^ n := fun n => by
      rw [star_pow, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg]
    rw [hd, hz, hpr, hxi, hs, hs, frameSign, if_pos (by first | omega | (simp only [Fin.val_mk]; omega) | (simp; omega))]
    simp only [map_mul, map_neg, map_pow, map_inv₀]
    exact alg_e' _ _ hx0 σ i.val i.2

end Main

theorem Big₂ : Big fun ch => BesP ch :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ R _ _ ch _ _ => BesP₂ (R := R) ch⟩⟩

end GlobalTheory.FlatPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselMeanPeriodConvergesContinuousStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselMean_period_converges_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), RapidDec B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → (∀ h, AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 (fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ (rTrans h G) (flBF s (s.om (1, h) Φ)))) ∧ Continuous fun h => J.perAll ψ B s.om₀ φ (rTrans h G) (flBF s (s.om (1, h) Φ)) := by
  first | exact @GlobalTheory.BesMean.perAll_flBF_cont | exact GlobalTheory.BesMean.perAll_flBF_cont | (intros; apply GlobalTheory.BesMean.perAll_flBF_cont <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnAtReadsPlacePartLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ColAtPart

theorem colAt_smul_of_mul_idem : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (w : locPl ch.G t) (eL e' : AE D), IsIdemSum eL {w.1} → e' * eL = eL → ∀ u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), ch.S.colAt t w.1 (fun j => e' • u j) = ch.S.colAt t w.1 u := by
  unfold Big
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intros
  beta_reduce
  intro t w eL e' hL he u
  have hw := (GlobalTheory.FunObj.Comparison₂.cpt_idemSum hL).2.1 w.1 (Finset.mem_singleton_self _)

  have h1 := congrArg (fun a => cpt w.1 (toEAf _ a)) he
  simp only [map_mul, hw, mul_one] at h1
  funext j
  simp only [GridChoice.colAt]
  split_ifs with hj
  · congr 1
    congr 1
    congr 1
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.comp_apply, map_mul, h1, one_mul]
  · rfl

end GlobalTheory.ColAtPart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlacesLiftLevelDatumEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugatePlaces_liftLevelDatum_eq : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∃ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q ∧ IdemTwo Lv.w ∧ (∀ κ ∈ Lv.J, ∀ κ' : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E), κ'.map (Ideal.Quotient.mk Lv.𝔪) = (κ : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ Lv.𝔪)) → ∀ PP ∈ Pg, ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ conjI PP.asIdeal) ∧ ∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ), Lv.dat hn y = omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))))) * omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))))) := by
  first | exact @GlobalTheory.LiftDat.level_datum_eq | exact GlobalTheory.LiftDat.level_datum_eq | (intros; apply GlobalTheory.LiftDat.level_datum_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestRealPlacesDefinitePeriodsOnOneLine
section
open GlobalTheory.RowClaim GlobalTheory.RowReal

theorem GlobalTheory.RowReal.periodsOnLine_big : Big fun ch => PeriodsOnLine ch :=
  big_mono (fun ch h => periodsOnLine_of_invLine GlobalTheory.OneFunctional.oneLine ch h) GlobalTheory.T.rowTest_definitePeriods_invariant_functional
end

