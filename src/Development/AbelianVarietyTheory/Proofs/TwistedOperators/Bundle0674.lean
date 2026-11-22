import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0665
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0657
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0192
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0199
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0286
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0213
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovY
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowKFix

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

def movY (j : ℕ) (hj : j + 1 + 1 < D.R.m) (k : GA D (G.V (.grid D.R.m (j + 1))))
    (y : ∀ i : Fin D.R.m, Mx D (G.V (.grid D.R.m (i + 1))).rank (G.V (.grid D.R.m i)).rank) :
    ∀ i : Fin D.R.m, Mx D (G.V (.grid D.R.m (i + 1))).rank (G.V (.grid D.R.m i)).rank :=
  Function.update (Function.update y ⟨j, by omega⟩
      (actO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) 1 k⁻¹ (y ⟨j, by omega⟩)))
    ⟨j + 1, by omega⟩ (actO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m (j + 1 + 1))) k⁻¹ 1 (y ⟨j + 1, by omega⟩))

end GlobalTheory.RowKFix

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal

namespace GlobalTheory.LocAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

open Classical in

def PlaceCl (s : ℤˣ) (t : T) (w : Pl D.host.E)
    (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w)) (ζ : ℂ) : Prop :=
  ∀ e, IsIdemSum e {w} → ∀ (M : Vol ch.G) (hM : M.Is t) (r r₀ h : Pts ch.G),
    OneLoc t w e r (fun j => if j ∈ idx D then sgnAt ch.G t s w j * (repsAt ch.G t w).elt β (D.R.m, j) else 1) →
    OneLoc t w e r₀ (fun j => if j = 0 then (stair (locGrid ch.G t w) (unifAt w) (cosExp ch.G w) j)⁻¹ else 1) →
    (∀ j, j ≤ D.R.m → ∃ δ, IsTilt ch.G j δ ∧ δ⁻¹ * h j ∈ GlobalTheory.FinPl.grpOff _ (· = w.under (𝓞 D.host.F))) →
    ∀ (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w).rank b.tgt)) (Fin ((locGrid ch.G t w).rank b.src)) (Kw w) → ℂ),
      (∀ i j x, φ (.ex i j) x = 1) → ∀ v f : SchDown ch.G t, (∀ j, IsThetaFunO ch.W.ψ _ _ (v j)) →
      (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (v j) (fun y => if IsHalf e y then φ (.theta D.R.m j)
        (ch.S.B.coord t w (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩
          (y.map fun a => cpt w (toEAf D a))) else 0) (f j)) →
      ∀ (I : Type) (S : Finset I) (x : I → ℂ) (d : I → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (c : I → Combs ch.G),
        (∀ i ∈ S, ∀ j : Fin D.R.m, (d i j).e = e ∧ IsCombOf ch.W (d i j) ((c i).1 j)) →
        (∀ y : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf e (y j)) →
          ∑ i ∈ S, x i * ∏ j, (d i j).fn (y j) = flatTensor one_le_sLen (psiAt ch.W w) (unitVol w)
            (moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt β)
              ((locGrid ch.G t w).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) φ)) (ch.S.toGridChoice.colAt t w y) 0) →
        ∀ u, evT (conAt ch.W hM f (h * r)) 1 u 0 = ζ * ∑ i ∈ S, x i * evT (combC ch.W (c i) (conAt ch.W hM v (h * r₀))) 1 u 0

theorem placeAt_iff (s : ℤˣ) : PlaceAt ch s ↔ ∃ (κ : Pl D.host.E → ℂ) (z : T → Pl D.host.E → ℂˣ),
    (∀ t w, z t w ∈ xiVals R.toLevCh t) ∧ (∀ w, w ∉ ch.G.pl.W0 → κ w = 1) ∧
    ∀ t, ∀ w ∈ locPl ch.G t, ∀ β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w), ∃ ζ : ℂ,
      ((w ∈ ch.G.pl.W0 → ∀ i, β i = DoubleCoset.mk _ _ (stair (locGrid ch.G t w) (unifAt w) (cosExp ch.G w) (i + 1))) →
        ζ = κ w * (z t w : ℂ)⁻¹) ∧ PlaceCl ch s t w β ζ := Iff.rfl

end GlobalTheory.LocAsm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowChainLastStepVectorEqThetaOfDatumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowChain_last_step_vector_eq_theta_of_datum : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {large₂ : SizeData₂ D},
    HidaSetting large₂ R F → ∀ ch : Choice R, ch.Is → ∀ (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j)) (hj : (j : ℕ) + 1 = D.R.m),
    HEq g (R.vX t) → ∃ e' : AE D, IsIdemSum e' (GlobalTheory.FlipTop.topPl R.toLevCh t) ∧
      IsThetaAt ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e' (latO (ch.G.pS (.mu t 0 j)) (ch.G.pT (.mu t 0 j)) (ch.G.latS (.mu t 0 j) : Set _) (ch.G.latT (.mu t 0 j) : Set _) fun _ => True) 1 (ch.rm.vT 0 j)
        (GlobalTheory.FlipTop.topFn ch.S.B t e' j (GlobalTheory.FlipTop.rank_col ch.G (by omega)) (GlobalTheory.FlipTop.rank_col ch.G (by omega))) g := by
  first | exact @GlobalTheory.FlipTopChain.last_step_theta | exact GlobalTheory.FlipTopChain.last_step_theta | (intros; apply GlobalTheory.FlipTopChain.last_step_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPeriodGroupsSplitRealFiniteLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowGrpSplit

theorem grpAt_all {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) : GrpAt ch := by
  intro j hj
  have hj' := List.mem_range'_1.1 hj
  obtain ⟨hi, hf, hc, he, hu, hrest⟩ := GlobalTheory.AdelicSplit.adelic_split D (ch.G.V (.grid D.R.m j))
  have hV := ch.G.isV (X := .grid D.R.m j) ⟨le_rfl, by omega⟩ (fun k hk => by
    simp only [Node.grid.injEq] at hk; omega)
  have hlat := congLev_open_compact (ch.G.V (.grid D.R.m j)) hV.sd.1 (𝔪 := ⊤) top_ne_bot
  have hR : IsClosed ((rowGrp ch.G j : Subgroup (GA D (ch.G.V (.grid D.R.m j)))) : Set (GA D (ch.G.V (.grid D.R.m j)))) ∧ (∀ a ∈ GinfC _, ∀ b ∈ GfC _, a * b ∈ rowGrp ch.G j → a ∈ rowGrp ch.G j ∧ b ∈ rowGrp ch.G j) ∧
      (∀ μ : Measure (rowGrp ch.G j), μ.IsHaarMeasure → μ.IsInvInvariant) ∧
      ∀ μ : Measure ((rowGrp ch.G j).subgroupOf (GfC _)), μ.IsHaarMeasure → μ.IsInvInvariant := by
    by_cases h1 : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m
    · rw [show rowGrp ch.G j = _ from dif_pos h1]
      obtain ⟨a, b, c⟩ := (hrest _ _ _).1
      exact ⟨GlobalTheory.jacGrp_isClosed D _ _ _ _, a, b, c⟩
    · have h2 : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m := by omega
      rw [show rowGrp ch.G j = _ from (dif_neg h1).trans (dif_pos h2)]
      obtain ⟨a, b, c⟩ := (hrest _ _ _).2 _ _ _
      exact ⟨GlobalTheory.BesClosed.besGrp_isClosed D _ _ _ _ _ _ _, a, b, c⟩
  exact
    { clA := hi
      clB := hf
      clR := hR.1
      comm := hc
      prod := he
      split := hR.2.1
      le := inf_le_left
      cpt := hlat.2
      opn := by
        have e : (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) :
            Set (GfC (ch.G.V (.grid D.R.m j)))) = Subtype.val ⁻¹'
            (((ch.G.levMax (.grid D.R.m j)).comap (Lev.finE _) : Subgroup (GA D (ch.G.V (.grid D.R.m j)))) :
              Set (GA D (ch.G.V (.grid D.R.m j)))) := by
          ext x
          exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
        rw [e]
        exact hlat.1.preimage continuous_subtype_val
      uniR := hR.2.2.1
      uniRB := hR.2.2.2
      uniB := hu }

theorem grpAt_big : Big fun ch => GrpAt ch :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => grpAt_all ch⟩⟩

end GlobalTheory.RowGrpSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestCellValueOfStepsLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem defTot_smul {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T)
    (M : Vol G) (c : ℂ) (σ : PolCol G × PolRow G →₀ ℂ) (τ : PureDat G t →₀ ℂ) (φ : Fn G (.top 0)) (F : Fn G (.grid 0 D.R.m)) :
    defTot t S M (c • σ) τ φ F = c * defTot t S M σ τ φ F := by
  unfold defTot
  rw [Finsupp.sum_smul_index (by intro P; simp), Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  dsimp only
  rw [Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

set_option maxHeartbeats 1600000 in

theorem valAt_of_steps (ch : Choice R) (s : ℤˣ) (hFl : FlatAt ch s) (hT : TensAt ch) (hV : VolAt ch) (hW : WtAt ch s)
    (hFo : FockAt ch) (hB : BasicAt ch) (hO : OneAt ch) (hS : ∀ t a, ch.S.SumOK t (ch.Phi a)) : ValAt ch s := by
  obtain ⟨z1, hz1, hFl⟩ := hFl
  obtain ⟨z2, hz2, hFo⟩ := hFo
  obtain ⟨hBa, hBf, hBM, hBM', hBgood, hBgood', hBc⟩ := hB
  refine ⟨fun t => z1 t * z2 t, fun t => Subgroup.mul_mem _ (hz1 t) (hz2 t), ?_⟩
  intro ρ μ hρμ P p hp
  obtain ⟨c0, hc0⟩ := hW ρ μ hρμ
  obtain ⟨C, hCr, hC⟩ := hFl P.2 p hp
  obtain ⟨σ₀, hσ₀⟩ := hFo C hCr P.1
  refine ⟨c0 • σ₀, ?_⟩
  intro t a τ hτ M hM β hβ b hb M' τ' hM' hτ' y
  obtain ⟨cc, hcc⟩ := hBc t (ch.Phi a) β τ' hτ'
  obtain ⟨ζ, hζ, hid⟩ := hC t (ch.Phi a) τ hτ M hM β b hb τ' cc hτ' hcc
  have hζ' : ζ = ((z1 t : ℂˣ) : ℂ)⁻¹ := hζ (hO t _ β hβ)
  obtain ⟨sc, hsc, hwx⟩ := hc0 t (ch.Phi a) β b hb M M' hM hM'
  have hgood : ∀ d ∈ τ'.support, Good ch.W (combC ch.W (cc d) C) (combR ch.rm (cc d)) := fun d hd =>
    hBgood' C hCr (cc d) (fun j hj => ((hcc d hd).1 ⟨j, hj⟩).1)
  have h1 : tot ch.W hM P τ (colFn ch a) (formTop ch t y) (p * b) = ζ * τ'.sum fun d x =>
      x * per ch.W M t (combC ch.W (cc d) C) (combR ch.rm (cc d)) P.1 (colFn ch a) (formTop ch t y) := by
    have key := hT t M (hBM t M hM) (colFn ch a) (formTop ch t y) (hBa a) (hBf t y)
      ((SchRow ch.G × SchDown ch.G t) ⊕ PureDat ch.G t) (τ.support.disjSum τ'.support)
      (Sum.elim (fun d => τ d) (fun d => -ζ * τ' d))
      (Sum.elim (fun d => conAt ch.W hM (fockD ch.W t d.2 P.2) (p * b)) (fun d => combC ch.W (cc d) C))
      (Sum.elim Prod.fst (fun d => combR ch.rm (cc d))) ?_ ?_ P.1
    · rw [Finset.sum_disjSum] at key
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, mul_assoc, Finset.sum_neg_distrib] at key
      unfold tot
      rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
      linear_combination key
    · rintro (d | d) hd
      · exact hBgood t (ch.Phi a) τ hτ M hM d (Finset.inl_mem_disjSum.1 hd) P.2 (p * b)
      · exact hgood d (Finset.inr_mem_disjSum.1 hd)
    · intro u y'
      have e := hid u y'
      rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum] at e
      rw [Finset.sum_disjSum]
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, mul_assoc, Finset.sum_neg_distrib]
      rw [e]
      ring
  have h2 : (τ'.sum fun d x => x * per ch.W M t (combC ch.W (cc d) C) (combR ch.rm (cc d)) P.1 (colFn ch a) (formTop ch t y)) =
      sProd D sc * τ'.sum fun d x => x * per ch.W M' t (combC ch.W (cc d) C) (combR ch.rm (cc d)) P.1 (colFn ch a) (formTop ch t y) := by
    rw [Finsupp.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    dsimp only
    rw [hV t M M' sc (hBM t M hM) (hBM' t _ β M' hM') hsc (colFn ch a) (formTop ch t y) (hBa a) (hBf t y) _ _ (hgood d hd) P.1]
    ring
  have h3 := hσ₀ t a β M' (hBM' t _ β M' hM') (hS t a) τ' cc hτ' hcc y
  rw [h1, h2, h3, defTot_smul, hζ', Units.val_mul, mul_inv]
  linear_combination (((z1 t : ℂˣ) : ℂ)⁻¹ * ((z2 t : ℂˣ) : ℂ)⁻¹ *
    defTot t ch.S.toGridChoice M' σ₀ τ' (colFn ch a) (formTop ch t y)) * hwx

end

theorem valAt_big : Big fun ch => ∀ s, FlatAt ch s → TensAt ch → VolAt ch → WtAt ch s → FockAt ch → BasicAt ch → OneAt ch →
    (∀ t a, ch.S.SumOK t (ch.Phi a)) → ValAt ch s :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ s => valAt_of_steps ch s⟩⟩

end GlobalTheory.RowVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestCombinationDependsOnProductFunction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CombDet

theorem row_position {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {t : T} {p : Pair T}
    {I : Type} (S : Finset I) (e : AE D) (d : I → FinDatum G t p) (c : I → (WO (G.pS p) (G.pT p) →₀ ℂ))
    (hd : ∀ i ∈ S, (d i).e = e ∧ IsCombOf W (d i) (c i)) (f₀ : WO (G.pS p) (G.pT p) → ℂ)
    (h1 : IsThetaFunO W.ψ _ _ f₀)
    (h2 : IsLatVac (heisO W.ψ _ _) (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True) f₀) :
    ∃ Tm : (WO (G.pS p) (G.pT p) → ℂ) →ₗ[ℂ] (WO (G.pS p) (G.pT p) → ℂ), ∀ i ∈ S, comb W.ψ _ _ (c i) f₀ = Tm (d i).fn := by
  rcases S.eq_empty_or_nonempty with hS | ⟨i₀, hi₀⟩
  · exact ⟨0, fun i hi => by simp [hS] at hi⟩
  have key : ∀ i ∈ S, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e
      (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True) 1 f₀ (d i).fn (comb W.ψ _ _ (c i) f₀) := by
    intro i hi
    have h := (hd i hi).2.2.2 f₀ h1 h2
    have he := (hd i hi).1
    unfold FinDatum.IsTheta at h
    rw [he] at h
    exact h
  obtain ⟨Tm, hTm⟩ := (key i₀ hi₀).1
  exact ⟨Tm, fun i hi => (key i hi).2 Tm hTm⟩

def Spans {I Y : Type} (S : Finset I) (H : Y → I → ℂ) (g : I → ℂ) : Prop :=
  ∃ (J : Type) (P : Finset J) (a : J → ℂ) (y : J → Y), ∀ i ∈ S, g i = ∑ j ∈ P, a j * H (y j) i

theorem sum_prod_eq_zero {I ι : Type} [Fintype ι] {Y : ι → Type} (S : Finset I) (x : I → ℂ) (H : ∀ l, Y l → I → ℂ)
    (g : ι → I → ℂ) (hg : ∀ l, Spans S (H l) (g l)) (h : ∀ z : ∀ l, Y l, ∑ i ∈ S, x i * ∏ l, H l (z l) i = 0) :
    ∑ i ∈ S, x i * ∏ l, g l i = 0 := by
  classical
  choose J P a y hy using hg
  have e : ∀ i ∈ S, x i * ∏ l, g l i =
      ∑ z ∈ Fintype.piFinset P, (∏ l, a l (z l)) * (x i * ∏ l, H l (y l (z l)) i) := by
    intro i hi
    rw [Finset.prod_congr rfl fun l _ => hy l i hi, Finset.prod_univ_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.prod_mul_distrib]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_comm]
  refine Finset.sum_eq_zero fun z _ => ?_
  rw [← Finset.mul_sum, h fun l => y l (z l), mul_zero]

theorem reproducing {I X : Type} (S : Finset I) (V : Submodule ℂ (X → ℂ)) (F : I → X → ℂ) (hF : ∀ i ∈ S, F i ∈ V) :
    ∃ (P : Finset X) (u : X → X → ℂ), (∀ x, u x ∈ V) ∧ ∀ i ∈ S, F i = ∑ x ∈ P, F i x • u x := by
  classical
  obtain ⟨P, u, hu⟩ := GlobalTheory.exists_finite_reproducing_of_submodule V
    (S.attach.image fun i : {i // i ∈ S} => (⟨F i.1, hF i.1 i.2⟩ : V))
  refine ⟨P, fun x => u x, fun x => (u x).2, fun i hi => ?_⟩
  have := congrArg V.subtype (hu ⟨F i, hF i hi⟩ (Finset.mem_image.2 ⟨⟨i, hi⟩, Finset.mem_attach _ _, rfl⟩))
  simpa only [map_sum, map_smul, Submodule.subtype_apply] using this

theorem spans_linear {I X Z : Type} (S : Finset I) (F : I → X → ℂ) (Tm : (X → ℂ) →ₗ[ℂ] (Z → ℂ)) (z : Z) (g : I → ℂ)
    (hg : ∀ i ∈ S, g i = Tm (F i) z) : Spans S (fun x i => F i x) g := by
  obtain ⟨P, u, -, hu⟩ := reproducing S ⊤ F fun _ _ => trivial
  refine ⟨X, P, fun x => Tm (u x) z, id, fun i hi => ?_⟩
  rw [hg i hi]
  conv_lhs => rw [hu i hi]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, id]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

def vacSp {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f ∧ IsLatVac (heisO ψ S T) Λ f}
  add_mem' := by
    intro f g hf hg
    have key : ∀ u, heisO ψ S T u (f + g) = heisO ψ S T u f + heisO ψ S T u g := fun u => by
      funext w; simp only [heisO, Pi.add_apply, mul_add]
    refine ⟨GlobalTheory.LocMod.LinSpace.isThetaFunO_add hf.1 hg.1, fun u hu => ?_, fun e he u hu hh => ?_⟩
    · rw [key, hf.2.1 u hu, hg.2.1 u hu]
    · rw [key, hf.2.2 e he u hu hh, hg.2.2 e he u hu hh]
  zero_mem' := ⟨GlobalTheory.LocMod.LinSpace.isThetaFunO_zero ψ S T, fun u _ => by funext w; simp [heisO],
    fun e _ u _ _ => by funext w; simp [heisO]⟩
  smul_mem' := by
    intro c f hf
    have key : ∀ u, heisO ψ S T u (c • f) = c • heisO ψ S T u f := fun u => by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    refine ⟨GlobalTheory.LocMod.LinSpace.isThetaFunO_smul c hf.1, fun u hu => ?_, fun e he u hu hh => ?_⟩
    · rw [key, hf.2.1 u hu]
    · rw [key, hf.2.2 e he u hu hh]

theorem col_position {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {t : T} (j : ℕ)
    {I : Type} (S : Finset I) (e : AE D) (d₁ : I → FinDatum G t (.top t j)) (d₂ : I → FinDatum G t (.top t (j + 1)))
    (c₁ : I → (WO (G.V (.top j)) (G.V (.top (j + 1))) →₀ ℂ)) (c₂ : I → (WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) →₀ ℂ))
    (h₁ : ∀ i ∈ S, (d₁ i).e = e ∧ IsCombOf W (d₁ i) (c₁ i)) (h₂ : ∀ i ∈ S, (d₂ i).e = e ∧ IsCombOf W (d₂ i) (c₂ i))
    (C : WO (G.V (.top j)) (G.V (.top (j + 1))) → WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) → ℂ)
    (hC : IsBiVac W.ψ _ _ _ (G.Λ (.top j) : Set _) (G.Λ (.top (j + 1)) : Set _) (G.Λ (.top (j + 1 + 1)) : Set _) C) (u v) :
    Spans S (fun (p : WO (G.V (.top j)) (G.V (.top (j + 1))) × WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1)))) i =>
      (d₁ i).fn p.1 * (d₂ i).fn p.2) fun i => biComb W.ψ _ _ _ (c₁ i) (c₂ i) C u v := by
  classical
  choose Tu hTu using fun u' => row_position W S e d₂ c₂ h₂ (C u') (hC.right u').1 (hC.right u').2
  let Lm : (WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) → ℂ) →ₗ[ℂ] (WO (G.V (.top j)) (G.V (.top (j + 1))) → ℂ) :=
    LinearMap.pi fun u' => (LinearMap.proj v) ∘ₗ Tu u'
  let Vac := vacSp W.ψ _ _ (latO (G.V (.top j)) (G.V (.top (j + 1))) (G.Λ (.top j) : Set _) (G.Λ (.top (j + 1)) : Set _) fun _ => True)
  have hL : ∀ i ∈ S, Lm (d₂ i).fn = fun u' => comb W.ψ _ _ (c₂ i) (C u') v := fun i hi => by
    funext u'
    exact (congrFun (hTu u' i hi) v).symm
  have hV : ∀ i ∈ S, (d₂ i).fn ∈ Vac.comap Lm := fun i hi => by
    rw [Submodule.mem_comap, hL i hi]
    have : (fun u' => comb W.ψ _ _ (c₂ i) (C u') v) =
        ∑ b ∈ (c₂ i).support, ((c₂ i) b * W.ψ (symplOH _ _ v b)) • fun u' => C u' (v + b) := by
      funext u'
      simp only [GlobalTheory.BiCombStable.comb_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [this]
    exact Vac.sum_mem fun b _ => Vac.smul_mem _ (hC.left (v + b))
  obtain ⟨P, ε, hε, hP⟩ := reproducing S (Vac.comap Lm) (fun i => (d₂ i).fn) hV
  choose Tx hTx using fun x => row_position W S e d₁ c₁ h₁ (Lm (ε x)) (hε x).1 (hε x).2
  obtain ⟨Q, η, -, hQ⟩ := reproducing S ⊤ (fun i => (d₁ i).fn) fun _ _ => trivial
  refine ⟨_, Q ×ˢ P, fun p => Tx p.2 (η p.1) u, id, fun i hi => ?_⟩
  have e1 : biComb W.ψ _ _ _ (c₁ i) (c₂ i) C u v = GlobalTheory.BiCombStable.combL W.ψ _ _ (c₁ i) (Lm (d₂ i).fn) u := by
    rw [hL i hi]; rfl
  have e2 : ∀ x, GlobalTheory.BiCombStable.combL W.ψ _ _ (c₁ i) (Lm (ε x)) = ∑ q ∈ Q, (d₁ i).fn q • Tx x (η q) := fun x => by
    refine (hTx x i hi).trans ?_
    refine (congrArg (Tx x) (hQ i hi)).trans ?_
    simp only [map_sum, map_smul]
  have e3 : GlobalTheory.BiCombStable.combL W.ψ _ _ (c₁ i) (Lm (d₂ i).fn) =
      ∑ x ∈ P, (d₂ i).fn x • GlobalTheory.BiCombStable.combL W.ψ _ _ (c₁ i) (Lm (ε x)) := by
    refine (congrArg (fun f => GlobalTheory.BiCombStable.combL W.ψ _ _ (c₁ i) (Lm f)) (hP i hi)).trans ?_
    simp only [map_sum, map_smul]
  show biComb W.ψ _ _ _ (c₁ i) (c₂ i) C u v = _
  rw [e1, e3, Finset.sum_product_right, Finset.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [e2, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, id]
  ring

theorem prod_range_pairs (f : ℕ → ℂ) (n : ℕ) :
    ∏ j ∈ Finset.range (2 * n), f j = ∏ k ∈ Finset.range n, f (2 * k) * f (2 * k + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih,
      Finset.prod_range_succ, mul_assoc]

theorem sum_evT_eq_zero {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (ρ : RealMatch W)
    (t : T) (e : AE D) (I : Type) (S : Finset I) (x : I → ℂ) (d : I → PureDat G t) (c : I → Combs G)
    (hd : ∀ i ∈ S, (∀ j : Fin D.R.m, ((d i).1 j).e = e ∧ IsCombOf W ((d i).1 j) ((c i).1 j)) ∧
      ∀ n, ((d i).2 n).e = e ∧ IsCombOf W ((d i).2 n) ((c i).2 n))
    (h : ∀ (u : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1)))) (y : RowPt G), (∀ j, IsHalf e (u j)) →
      (∀ n, IsHalf e (y n)) → ∑ i ∈ S, x i * ((∏ j, ((d i).1 j).fn (u j)) * ∏ n, ((d i).2 n).fn (y n)) = 0)
    (C : BiFam G) (hC : IsRealFam W C) (u : ColPt G) (y : RowPt G) :
    ∑ i ∈ S, x i * evT (combC W (c i) C) (combR ρ (c i)) u y = 0 := by
  classical
  have hm : 0 + 2 * ((D.R.m - 2) / 2) + 2 = D.R.m := top_idx
  have h' : ∀ (u : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1)))) (y : RowPt G),
      ∑ i ∈ S, x i * ((∏ j, ((d i).1 j).fn (u j)) * ∏ n, ((d i).2 n).fn (y n)) = 0 := by
    intro u y
    by_cases hu : ∀ j, IsHalf e (u j)
    · by_cases hy : ∀ n, IsHalf e (y n)
      · exact h u y hu hy
      · obtain ⟨n, hn⟩ := not_forall.1 hy
        refine Finset.sum_eq_zero fun i hi => ?_
        have h0 : ((d i).2 n).fn (y n) = 0 := by
          by_contra h0
          exact hn (((hd i hi).2 n).1 ▸ ((d i).2 n).sb.1 _ h0)
        rw [Finset.prod_eq_zero (f := fun n => ((d i).2 n).fn (y n)) (Finset.mem_univ n) h0, mul_zero, mul_zero]
    · obtain ⟨j, hj⟩ := not_forall.1 hu
      refine Finset.sum_eq_zero fun i hi => ?_
      have h0 : ((d i).1 j).fn (u j) = 0 := by
        by_contra h0
        exact hj (((hd i hi).1 j).1 ▸ ((d i).1 j).sb.1 _ h0)
      rw [Finset.prod_eq_zero (f := fun j => ((d i).1 j).fn (u j)) (Finset.mem_univ j) h0, zero_mul, mul_zero]

  have hrow : ∀ (u : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1)))),
      ∑ i ∈ S, (x i * ∏ j, ((d i).1 j).fn (u j)) * ∏ n, combR ρ (c i) n (y n) = 0 := by
    intro u
    refine sum_prod_eq_zero S _ (fun (n : Fin D.R.m) (z : WO (G.pS (.chi n D.R.m : Pair T)) (G.pT (.chi n D.R.m : Pair T))) i =>
      ((d i).2 n).fn z) (fun n i => combR ρ (c i) n (y n)) (fun n => ?_) fun z => ?_
    · have hv := ρ.vX_is n D.R.m n.2 le_rfl
      obtain ⟨Tm, hTm⟩ := row_position W S e (fun i => (d i).2 n) (fun i => (c i).2 n) (fun i hi => (hd i hi).2 n) _
        hv.2.theta hv.2.lat
      exact spans_linear S (fun i => ((d i).2 n).fn) Tm (y n) _ fun i hi => congrFun (hTm i hi) (y n)
    · simpa only [mul_assoc] using h' u z

  let F : I → ∀ j : ℕ, WO (G.V (.top j)) (G.V (.top (j + 1))) → ℂ := fun i j =>
    if hj : j < D.R.m then ((d i).1 ⟨j, hj⟩).fn else 0
  have hcol := sum_prod_eq_zero (ι := Fin (D.R.m / 2)) S (fun i => x i * ∏ n, combR ρ (c i) n (y n))
    (fun k (w : ColPt G) i => F i (2 * k) (w (2 * k)) * F i (2 * k + 1) (w (2 * k + 1)))
    (fun k i => combC W (c i) C (2 * k) (u (2 * k)) (u (2 * k + 1))) (fun k => ?_) fun z => ?_
  · rw [← hcol]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [evT, Finset.prod_range]
    ring
  · have k0 : 2 * (k : ℕ) < D.R.m := by have := k.2; omega
    have k1 : 2 * (k : ℕ) + 1 < D.R.m := by have := k.2; omega
    obtain ⟨J, P, a, p, hp⟩ := col_position W (2 * k) S e (fun i => (d i).1 ⟨2 * k, k0⟩) (fun i => (d i).1 ⟨2 * k + 1, k1⟩)
      (fun i => (c i).1 (2 * k)) (fun i => (c i).1 (2 * k + 1)) (fun i hi => (hd i hi).1 ⟨2 * k, k0⟩)
      (fun i hi => (hd i hi).1 ⟨2 * k + 1, k1⟩) (C (2 * k)) (hC _ (even_two_mul _) k0).1 (u (2 * k)) (u (2 * k + 1))
    refine ⟨J, P, a, fun j => Function.update (Function.update (0 : ColPt G) (2 * k) (p j).1) (2 * k + 1) (p j).2,
      fun i hi => (hp i hi).trans (Finset.sum_congr rfl fun j _ => ?_)⟩
    simp only [F, dif_pos k0, dif_pos k1, Function.update_self,
      Function.update_of_ne (show 2 * (k : ℕ) ≠ 2 * k + 1 by omega)]
  · let w : ColPt G := fun j => if hj : j / 2 < D.R.m / 2 then z ⟨j / 2, hj⟩ j else 0
    have hw : ∀ (k : Fin (D.R.m / 2)) (j : ℕ), j / 2 = (k : ℕ) → w j = z k j := by
      rintro ⟨k, hk⟩ j hj
      have hj' : j / 2 = k := hj
      subst hj'
      exact dif_pos hk
    rw [← hrow fun j => w j]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : ∏ j : Fin D.R.m, ((d i).1 j).fn (w j) = ∏ j ∈ Finset.range D.R.m, F i j (w j) := by
      rw [Finset.prod_range]
      exact Finset.prod_congr rfl fun j _ => by simp only [F, dif_pos j.2]
    have e2 : Finset.range D.R.m = Finset.range (2 * (D.R.m / 2)) := by congr 1; omega
    rw [e1, e2, prod_range_pairs (fun j => F i j (w j)), Finset.prod_range,
      Finset.prod_congr rfl fun (k : Fin (D.R.m / 2)) _ => show F i (2 * k) (w (2 * k)) * F i (2 * k + 1) (w (2 * k + 1)) =
        F i (2 * k) (z k (2 * k)) * F i (2 * k + 1) (z k (2 * k + 1)) by
          rw [hw k _ (by omega), hw k _ (by omega)]]
    ring

theorem comb_det : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t e, IsIdemSum e (locPl ch.G t) → ∀ (I : Type) (S : Finset I) (x : I → ℂ) (d : I → PureDat ch.G t) (c : I → Combs ch.G), (∀ i ∈ S, (∀ j : Fin D.R.m, ((d i).1 j).e = e ∧ IsCombOf ch.W ((d i).1 j) ((c i).1 j)) ∧ ∀ n, ((d i).2 n).e = e ∧ IsCombOf ch.W ((d i).2 n) ((c i).2 n)) → (∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : RowPt ch.G), (∀ j, IsHalf e (u j)) → (∀ n, IsHalf e (y n)) → ∑ i ∈ S, x i * ((∏ j, ((d i).1 j).fn (u j)) * ∏ n, ((d i).2 n).fn (y n)) = 0) → ∀ C, IsRealFam ch.W C → ∀ u y, ∑ i ∈ S, x i * evT (combC ch.W (c i) C) (combR ch.rm (c i)) u y = 0 :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ t e _ I S x d c hd h C hC u y =>
    sum_evT_eq_zero ch.W ch.rm t e I S x d c hd h C hC u y⟩⟩

end GlobalTheory.CombDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestFlippedFiniteTensorRowIsThetaFunction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FlipRowTheta

theorem row_isThetaFunO : Big fun ch => ∀ t Φ τ, IsFlipFin t ch.S.B ch.rm Φ τ → ∀ d ∈ τ.support, ∀ i,
    IsThetaFunO ch.W.ψ _ _ (d.1 i) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hSet ch hch hsc => ?_⟩⟩
  intro t Φ τ hτ d hd i
  obtain ⟨e, _he, φ, hφ, _⟩ := hτ
  have hv := ch.rm.vX_is i D.R.m i.2 le_rfl
  exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt ch.W.ψ_std ch.W.θ_is ((hφ d hd).1 i).2 hv.2.theta

end GlobalTheory.FlipRowTheta

end
end

