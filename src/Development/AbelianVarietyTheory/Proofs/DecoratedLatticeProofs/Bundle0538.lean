import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0518
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0477
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0321
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0457
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0469
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0403
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0497
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0487
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0521
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0488
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0529
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTrace.LastRow

theorem row_lt_of_smul_pair_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (Q : GlobalTheory.LatPair.Pair k (Fin n)) (b b' M : Matrix (Fin n) (Fin n) k) (hb : b * b' = 1) (c : k) (r₀ : Fin n)
    (hQ : ∀ (x : Fin n → k) (a : 𝓀[k]), Q.HasVal x a ↔ ∃ y : Fin n → 𝒪[k], (∀ r, (y r : k) = (b *ᵥ x) r) ∧
      ∃ s : 𝒪[k], (s : k) = c ∧ a = residue 𝒪[k] (s * y r₀))
    (g : GL (Fin n) k) (hg : M = b * g.val * b') (hfix : g • Q = Q) (s : Fin n) :
    valuation k (M r₀ s - (1 : Matrix (Fin n) (Fin n) k) r₀ s) < 1 := by
  obtain ⟨x0, hx0⟩ : ∃ x, Q.fn x ≠ 0 := by
    by_contra h
    exact Q.fn_ne (LinearMap.ext fun x => not_not.1 fun hx => h ⟨x, hx⟩)
  obtain ⟨y0, -, s0, hs0, ha0⟩ := (hQ x0.1 (Q.fn x0)).1 ⟨x0.2, rfl⟩
  have hu : residue 𝒪[k] s0 ≠ 0 := by
    intro h
    apply hx0
    rw [ha0, map_mul, h, zero_mul]
  let yE : Fin n → 𝒪[k] := Pi.single s 1
  have hyE : ∀ r, (yE r : k) = (Pi.single s 1 : Fin n → k) r := by
    intro r
    simp only [yE, Pi.single_apply]
    split_ifs <;> rfl
  have h1 : Q.HasVal (b' *ᵥ Pi.single s 1) (residue 𝒪[k] (s0 * yE r₀)) := by
    refine (hQ _ _).2 ⟨yE, fun r => ?_, s0, hs0, rfl⟩
    rw [Matrix.mulVec_mulVec, hb, Matrix.one_mulVec, hyE]
  have h2 : Q.HasVal (g • (b' *ᵥ (Pi.single s 1 : Fin n → k))) (residue 𝒪[k] (s0 * yE r₀)) := by
    rw [← hfix, GlobalTheory.LatPair.Pair.smul_hasVal, inv_smul_smul]
    exact h1
  obtain ⟨y1, hy1, s1, hs1, ha1⟩ := (hQ _ _).1 h2
  obtain rfl : s1 = s0 := Subtype.ext (hs1.trans hs0.symm)
  have hM : (y1 r₀ : k) = M r₀ s := by
    rw [hy1]
    change (b *ᵥ (g.val *ᵥ (b' *ᵥ (Pi.single s 1 : Fin n → k)))) r₀ = _
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hg, Matrix.mulVec_single_one]
    rfl
  have h3 : residue 𝒪[k] (y1 r₀ - yE r₀) = 0 := by
    rw [map_mul, map_mul] at ha1
    rw [map_sub, mul_left_cancel₀ hu ha1, sub_self]
  have h4 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.1
    ((IsLocalRing.mem_maximalIdeal _).1 ((IsLocalRing.residue_eq_zero_iff _).1 h3))
  have h5 : ((y1 r₀ - yE r₀ : 𝒪[k]) : k) = M r₀ s - (1 : Matrix (Fin n) (Fin n) k) r₀ s := by
    rw [AddSubgroupClass.coe_sub, hM, hyE, Pi.single_apply, Matrix.one_apply]
  rw [← h5]
  exact h4

set_option maxHeartbeats 1000000 in

theorem exists_gl {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : GlobalTheory.FinPl.SplitPt D k} {V : HSp D} (β : GlobalTheory.FinPl.Frame p V (Fin V.rank)) (κ : GA D V) :
    ∃ g : GL (Fin V.rank) k, (mt V κ).map p.pr = β.b * g.val * β.b' := by
  have hm : ∀ x y : GA D V, x * y = 1 → (mt V x).map p.pr * (mt V y).map p.pr = 1 := by
    intro x y h
    have e : mt V x * mt V y = 1 := by
      simp only [Formalism.L2.Theta.mt]
      rw [← Units.val_mul, ← map_mul, h, map_one, Units.val_one]
    rw [← Matrix.map_mul, e]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hc : ∀ A A' : Matrix (Fin V.rank) (Fin V.rank) k, A * A' = 1 → (β.b' * A * β.b) * (β.b' * A' * β.b) = 1 := by
    intro A A' h
    calc (β.b' * A * β.b) * (β.b' * A' * β.b) = β.b' * (A * ((β.b * β.b') * A')) * β.b := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [β.bb', Matrix.one_mul, h, Matrix.mul_one, β.b'b]
  refine ⟨⟨β.b' * (mt V κ).map p.pr * β.b, β.b' * (mt V κ⁻¹).map p.pr * β.b, hc _ _ (hm _ _ (mul_inv_cancel κ)),
    hc _ _ (hm _ _ (inv_mul_cancel κ))⟩, ?_⟩
  calc (mt V κ).map p.pr = (β.b * β.b') * (mt V κ).map p.pr * (β.b * β.b') := by rw [β.bb', Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

set_option maxHeartbeats 2000000 in

theorem entry_cong (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : Formalism.L2.NTheta.IsIdemAt p.e P) (T : ℕ)
    (t t' : 𝓞 D.host.E) (h1 : (t' : D.host.E) = star (t : D.host.E)) (h2 : t * t' = (T : 𝓞 D.host.E)) (h3 : IsCoprime t t')
    (h4 : t ∈ P.asIdeal) (h5 : (T : 𝓞 D.host.F) ∈ p.v.asIdeal) (h6 : (T : 𝓞 D.host.F) ∉ p.v.asIdeal ^ 2)
    (V : HSp D) {n : ℕ} (hn : V.rank = n) (κ : GA D V) (r s : Fin n)
    (hi : Formalism.UG.prV (E := D.host.E) p.v (GlobalTheory.AdForm.finM V hn κ r s) ∈ Formalism.BasicNotions.intV D.host.E p.v)
    (hl : valuation k (((mt V κ).map p.pr) ((finCongr hn).symm r) ((finCongr hn).symm s) -
      (1 : Matrix (Fin V.rank) (Fin V.rank) k) ((finCongr hn).symm r) ((finCongr hn).symm s)) < 1) :
    ∃ c ∈ Formalism.BasicNotions.intV D.host.E p.v, Formalism.UG.prV (E := D.host.E) p.v (GlobalTheory.AdForm.finM V hn κ r s) -
      (1 : Matrix (Fin n) (Fin n) (D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F)) r s =
        Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (t : D.host.E) * c := by
  subst hn
  let y : AE D := mt V κ r s - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) r s
  have hy : Formalism.UG.prV (E := D.host.E) p.v (toEAf D y) = Formalism.UG.prV (E := D.host.E) p.v (GlobalTheory.AdForm.finM V rfl κ r s) -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F)) r s := by
    simp only [y]
    rw [RingHom.map_sub, RingHom.map_sub]
    congr 1
    by_cases h : r = s
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, RingHom.map_one]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, RingHom.map_zero, RingHom.map_zero]
  have h7 : p.pr ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) r s) = (1 : Matrix (Fin V.rank) (Fin V.rank) k) r s := by
    simp only [Matrix.one_apply]; split_ifs <;> simp
  rw [← hy]
  refine GlobalTheory.LocMod.SplitUnif.eq_mul_of_val_lt_one D k p P hP T t t' h1 h2 h3 h4 h5 h6 y ?_ ?_
  · rw [hy]
    refine Subring.sub_mem _ hi ?_
    simp only [Matrix.one_apply]; split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · simp only [y]
    rw [map_sub, h7]
    exact hl

end GlobalTheory.FamTrace.LastRow

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.FamTrace.lastRow_cong_of_keepsPairs : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), GlobalTheory.FamTrace.KeepsPairs a κ → (∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (r s : Fin ((I.rec7 l Z).R.N 0)), Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ r s) ∈ Formalism.BasicNotions.intV (I.rec7 l Z).host.E v) → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), (((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) → ∀ s : Fin ((I.rec7 l Z).R.N 0), ∃ c ∈ Formalism.BasicNotions.intV (I.rec7 l Z).host.E v, Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ (Formalism.L2.Col.lastIdx _) s) - (1 : Matrix (Fin ((I.rec7 l Z).R.N 0)) (Fin ((I.rec7 l Z).R.N 0)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) (Formalism.L2.Col.lastIdx _) s = Formalism.UG.inclE (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (show (I.rec7 l Z).host.E from (X.piT u : B.fields.E)) * c := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat κ hκ hkp hint v hv s
  letI := a.fld; letI := a.val; letI := a.top; haveI := a.loc
  have htP : ∀ p, p ∈ a.v.tP ↔ ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ p.asIdeal := by
    have hψ := hat.pinX.std
    let row : ∀ t, RowCh (pk W) (lvP W) u a.g t := fun t =>
      { vP := fun _ => 0, vT := fun _ _ => 0,
        sBF := fun j ρ h => (GlobalTheory.Unf.Inhab.nonempty_stepBF hψ _ _).some,
        sFB := fun j σ h => (GlobalTheory.Unf.Inhab.nonempty_stepFB hψ _ _).some,
        io := fun _ => 0, ioT := fun _ _ => 0 }
    exact (ha.tie row (fun t =>
      { kom := fun _ => 1, Ch := fun _ => Unit, fin := fun _ => inferInstance, dd := fun _ _ _ => 0, e := fun _ _ => 0,
        eT := fun _ _ _ => 0, Ram := fun _ => Set.univ, S := fun _ => id, rd := fun _ _ _ _ _ => 0, cV := fun _ => 1,
        cK := fun _ => 1, cP := 1 })).1.tP
  obtain ⟨i, rfl⟩ := (ha.shape.pre.tP v).1 ((htP v).2 hv)
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  obtain ⟨e, he⟩ := hat.std.1
  have hpi : X.piT u ∈ (e i).1.asIdeal := by
    have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := hPr.piT_cop u
    have hne : X.piT u ≠ 0 := by
      intro h0
      rw [h0, map_zero, isCoprime_zero_left] at hcop
      exact not_isUnit_zero hcop
    exact (Formalism.L2.Col.mem_divs hne _).1 (e i).2
  have hn := Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)
  haveI : NeZero ((I.rec7 l Z).R.N 0) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  set r₀ : Fin ((I.rec7 l Z).sp.X 0).rank := (finCongr hn).symm (Formalism.L2.Col.lastIdx _) with hr₀def
  set s' : Fin ((I.rec7 l Z).sp.X 0).rank := (finCongr hn).symm s with hs'def
  have hr₀ : r₀.1 + 1 = ((I.rec7 l Z).sp.X 0).rank := by
    have h1 : (Formalism.L2.Col.lastIdx ((I.rec7 l Z).R.N 0)).1 = (I.rec7 l Z).R.N 0 - 1 := rfl
    have h2 : r₀.1 = (Formalism.L2.Col.lastIdx ((I.rec7 l Z).R.N 0)).1 := rfl
    have h3 := NeZero.ne ((I.rec7 l Z).R.N 0)
    omega
  have hQ := GlobalTheory.AdForm.stdT_pair_coords I l Z u a.k a.ι a.o.p a.o.β a.o.Q _ hat.std 0 (Nat.zero_le _) i r₀ hr₀
  obtain ⟨g, hg⟩ := GlobalTheory.FamTrace.LastRow.exists_gl (a.o.β 0 i) κ
  have hl := GlobalTheory.FamTrace.LastRow.row_lt_of_smul_pair_eq _ _ _ _ (a.o.β 0 i).bb' _ r₀ hQ g hg (hkp i g hg) s'
  exact GlobalTheory.FamTrace.LastRow.entry_cong (I.rec7 l Z) a.k (a.o.p i) (e i).1 (he i) ((I.rec7 l Z).mem u).A.T (X.piT u)
    (B.fields.conjO (X.piT u)) ((B.fields_conjO_coe _).trans (GlobalTheory.RankOneLine.star_eq_hostConj (I.rec7 l Z) _).symm)
    (hPr.piT_norm u) (hPr.piT_cop u) hpi hv (GlobalTheory.LevelUnif.T_notMem_sq (I.rec7 l Z) u (W.R.T.cols.forms u).atT _ hv)
    _ hn κ _ s (hint _ _ s) hl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.QPl.EpsSupp

theorem exists_prod_of_mem_support_conv {G : Type} [Monoid G] : ∀ (n : ℕ) (f : Fin n → (G →₀ ℂ)) (g : G),
    g ∈ (conv (List.ofFn f)).support → ∃ x : Fin n → G, (∀ i, x i ∈ (f i).support) ∧ g = (List.ofFn x).prod := by
  classical
  intro n
  induction n with
  | zero =>
    intro f g hg
    simp only [List.ofFn_zero, conv, List.foldr_nil] at hg
    have := Finsupp.support_single_subset hg
    rw [Finset.mem_singleton] at this
    exact ⟨Fin.elim0, fun i => i.elim0, by simp [this]⟩
  | succ n ih =>
    intro f g hg
    rw [List.ofFn_succ] at hg
    simp only [conv, List.foldr_cons] at hg
    have h1 := Finsupp.support_sum hg
    rw [Finset.mem_biUnion] at h1
    obtain ⟨g₀, hg₀, h2⟩ := h1
    have h3 := Finsupp.support_sum h2
    rw [Finset.mem_biUnion] at h3
    obtain ⟨g', hg', h4⟩ := h3
    have h5 := Finsupp.support_single_subset h4
    rw [Finset.mem_singleton] at h5
    obtain ⟨x, hx, hxe⟩ := ih (fun k => f k.succ) g' hg'
    refine ⟨Fin.cons g₀ x, fun i => Fin.cases hg₀ (fun k => hx k) i, ?_⟩
    rw [List.ofFn_succ, List.prod_cons, h5, hxe]
    simp

theorem eps_mem_grpAt {D : D7} {c : Comm D} {v : VCom c} {t : Tup c} (F : QFam v t) (sc cT : ℕ → ℂ)
    (h0 : ∀ i β, (F.Q i).εL 0 β = Finsupp.single 1 1) (j : ℕ) (α : t.Ch j) :
    ∀ g ∈ ((F.pinTup sc cT).ε j α).support, g ∈ GlobalTheory.FinPl.grpAt (c.V j) (· ∈ (F.pinTup sc cT).Q) := by
  classical
  intro g hg
  dsimp only [QFam.pinTup] at hg ⊢
  split_ifs at hg with hc
  · have hg' := Finsupp.support_smul hg
    obtain ⟨x, hx, rfl⟩ := exists_prod_of_mem_support_conv _ _ g hg'
    apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    have hP : (F.Q i).q.v ∈ Finset.univ.image fun i => (F.Q i).q.v := Finset.mem_image_of_mem _ (Finset.mem_univ i)
    rcases hc with ⟨ρ, hρ⟩ | hj
    · obtain ⟨e, -, he⟩ := (F.Q i).εL_at j ρ hρ (2 * ρ) (by have := (F.Q i).hs; omega) (F.eqv j α i)
      have hxi := hx i
      rw [he] at hxi
      obtain ⟨a, -, hax⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hxi)
      rw [← hax]
      exact GlobalTheory.SuppGrp.mem_grpAt_of_suppAt D _ (F.Q i).q _ _ ((F.Q i).gl_loc _ _ _ a).1 _ hP
    · subst hj
      have hxi := hx i
      rw [h0] at hxi
      have h1 := Finsupp.support_single_subset hxi
      rw [Finset.mem_singleton] at h1
      rw [h1]
      exact one_mem _
  · simp at hg

end GlobalTheory.QPl.EpsSupp

open GlobalTheory.QPl.EpsSupp in

theorem GlobalTheory.Fam.famOf_eps_mem : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (J : ∀ t, QJ a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (pk W) (lvP W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (hCh : ∀ t, (col t).Ch = (J t).Ch) (sc cT : ℕ → ℂ) t, ∀ j α, ∀ g ∈ (((famOf a J row col hCh t).pinTup sc cT).ε j α).support,
    g ∈ GlobalTheory.FinPl.grpAt (Yc (I.rec7 l Z) j) (· ∈ ((famOf a J row col hCh t).pinTup sc cT).Q) ∧ g * a.g.b j ∈ GfC (Yc (I.rec7 l Z) j) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _ J _ row col hCh sc cT t j α g hg
  have h1 := eps_mem_grpAt (famOf a J row col hCh t) sc cT (fun i β => ((J t).E i).εL_zero β) j α g hg
  refine ⟨h1, mul_mem (GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ h1) ?_⟩
  rw [← (ha.tie row col).1.b j]
  exact ha.vis.b j
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeIndexStep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LevProd

theorem locHom_eq_one_of_grpAt' {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y : Type} [Fintype Y] [DecidableEq Y] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y)
    {P : GlobalTheory.FinPl.Pl D → Prop} (hP : ¬ P q.v) {x : GA D S} (hx : x ∈ GlobalTheory.FinPl.grpAt S P) :
    GlobalTheory.LevIdx.locHom q S F x = 1 := by
  have h1 : x ∈ GlobalTheory.FinPl.grpOff S (· = q.v) :=
    GlobalTheory.FinPl.SetCut.grpAt_le_grpOff S P (· = q.v) (fun p hp e => hP (e ▸ hp)) hx
  have h2 := GlobalTheory.LocMod.PinInhab.map_mt_eq_one_of_off q (P := (· = q.v)) rfl h1
  symm
  rw [← GlobalTheory.LevIdx.eq_locHom_iff, h2]
  simp [F.βγ]

theorem relax_phi_mem_KO : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : QJ a t), J.Reads → ∀ (α : J.Ch j) t' (J' : QJ a t'), J'.Reads → ∀ g ∈ GlobalTheory.LevProd.relax J j hj α, ∀ i, GlobalTheory.LevProd.phi J' j hj g i ∈ KO (J'.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α t' J' hJ' g hg i
  obtain ⟨⟨hsup, hgf⟩, hphi⟩ := Subgroup.mem_inf.1 hg |>.imp_left Subgroup.mem_inf.1
  by_cases hv : GlobalTheory.LevProd.twAt J (J'.G i).q.v
  · obtain ⟨i₀, hi₀⟩ := hv
    exact GlobalTheory.T.true_geometry_lattice_closed W hW u a ha hTr j hj t J hJ t' J' hJ' i₀ i hi₀ g hgf
      ((Subgroup.mem_pi _).1 (Subgroup.mem_comap.1 hphi) i₀ (Set.mem_univ _))
  · have hle : J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (GlobalTheory.LevProd.twAt J) ≤
        (KO (J'.G i).k _).comap ((Pi.evalMonoidHom _ i).comp (GlobalTheory.LevProd.phi J' j hj)) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact GlobalTheory.T.levProd_phi_mem_KO_of_not_twAt W hW u a ha hTr j hj t J hJ α t' J' hJ' i hv x hx
      · rw [Subgroup.mem_comap, MonoidHom.comp_apply, Pi.evalMonoidHom_apply]
        change GlobalTheory.LevIdx.locHom (J'.G i).q _ _ x ∈ KO (J'.G i).k _
        rw [locHom_eq_one_of_grpAt' _ _ _ hv hx]
        exact one_mem _
    exact hle hsup
end GlobalTheory.LevProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeOpen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LevProd.OffTwist

set_option maxHeartbeats 1000000 in

theorem bc_prV_eq_one (D : D7) (S : HSp D) (n : ℕ) (hn : S.rank = n) (κ : GA D S)
    (g : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hg : GlobalTheory.AdForm.finM S hn κ = g.1) (v w : HeightOneSpectrum (𝓞 D.host.F)) (hw : w ≠ v)
    (hκ : κ ∈ GlobalTheory.FinPl.grpAt S (· = v)) : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) g = 1 := by
  subst hn
  have h1 : GlobalTheory.AdelicU.proj (Formalism.L2.Forms.sigD D) S.gram w κ = 1 :=
    ((GlobalTheory.FinPl.KOpen.mem_grpAt_iff S _ κ).1 hκ).2 w hw
  have hp := GlobalTheory.AdelicU.matHom_proj (Formalism.L2.Forms.sigD D) S.gram w κ
  have hE : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) g =
      GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram w (GlobalTheory.AdelicU.proj _ S.gram w κ) := by
    ext i j
    have hij := congrFun (congrFun hg i) j
    have e1 : (GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram w (GlobalTheory.AdelicU.proj _ S.gram w κ)).val i j =
        GlobalTheory.StabConjIndex.swap w ((GlobalTheory.AdelicU.matHom (Fv D.host.F w) (Formalism.L2.Forms.sigD D) S.gram
          (GlobalTheory.AdelicU.proj (Formalism.L2.Forms.sigD D) S.gram w κ)).val i j) := rfl
    rw [e1, hp]
    show Formalism.UG.prV w (g.1 i j) = GlobalTheory.StabConjIndex.swap w (GlobalTheory.AdelicU.compFin _ _ w _)
    rw [← hij]
    exact GlobalTheory.FamTrace.prV_toEAf_eq_swap D w _
  rw [hE, h1, map_one]

set_option maxHeartbeats 1000000 in

theorem exists_mem_level (D : D7) (S : HSp D) (n : ℕ) (hn : S.rank = n) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (K : StepLevel D.host.F D.host.E (sigD D) (S.gram.reindex (finCongr hn) (finCongr hn)) T f bad)
    (t : 𝓞 D.host.E) (ht : t ∣ (T : 𝓞 D.host.E))
    (hLb : ∀ x, x ∈ K.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E) ∧ (j.1 + 1 = n → t ∣ r))
    (L : GlobalTheory.FinPl.Lat S) (hfg : L.FG) (hL : ∀ x, x ∈ L ↔ ∀ j, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hb : v ∉ bad) (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal)
    (κ : GA D S) (hκ : κ ∈ GlobalTheory.FinPl.grpAt S (· = v)) (hm : GlobalTheory.FinPl.Moves S κ L L (· = v)) :
    ∃ x : K.U, x.1.1 = GlobalTheory.AdForm.finM S hn κ := by
  obtain ⟨g, hgU, hg⟩ : ∃ g ∈ Formalism.UG.UPts (sigD D) (S.gram.reindex (finCongr hn) (finCongr hn))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F), GlobalTheory.AdForm.finM S hn κ = g.1 := by
    obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso D S n hn
    have hf := GlobalTheory.FinPl.SetCut.grpAt_le_GfC S _ hκ
    exact ⟨(e ⟨κ, hf⟩).1, (e ⟨κ, hf⟩).2, (he ⟨κ, hf⟩).symm⟩
  refine ⟨⟨g, (K.U_eq _).2 ⟨hgU, fun w => ?_⟩⟩, hg.symm⟩
  by_cases hw : w = v
  · subst hw
    subst hn
    have key : ∀ j i : Fin S.rank, ∃ r : 𝓞 D.host.E,
        (Pi.single j (T : D.host.E) : Fin S.rank → D.host.E) i = (r : D.host.E) ∧ t ∣ r := fun j i => by
      rw [Pi.single_apply]
      split_ifs
      · exact ⟨T, (map_natCast (algebraMap (𝓞 D.host.E) D.host.E) T).symm, ht⟩
      · exact ⟨0, rfl, dvd_zero _⟩
    have e := GlobalTheory.FamTrace.levelVL_eq_of_std (sigD D) (S.gram.reindex (finCongr rfl) (finCongr rfl)) (Lb := K.Lb) (Λ := L) hT
      (fun x hx j => let ⟨r, hr, _⟩ := (hLb x).1 hx j; ⟨r, hr⟩)
      (fun j => (hLb _).2 fun i => let ⟨r, hr, hd⟩ := key j i; ⟨r, hr, fun _ => hd⟩)
      (fun x hx => (hL x).1 hx) (fun j => (hL _).2 fun i => let ⟨r, hr, _⟩ := key j i; ⟨r, hr⟩)
    rw [K.Uloc_hyp w hb hT, e]
    exact GlobalTheory.FamTrace.bc_prV_mem_levelVL_of_moves D S _ rfl L L hfg (fun _ => Iff.rfl) κ g hg w hm
  · rw [bc_prV_eq_one D S n hn κ g hg v w hw hκ]
    exact one_mem _

set_option maxHeartbeats 2000000 in

theorem gl_mem_level : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m) t (J : QJ a t), J.Reads → ∀ (α : J.Ch j) t₂ (J₂ : QJ a t₂), J₂.Reads → ∀ i : Fin J₂.r, ¬ GlobalTheory.LevProd.twAt J (J₂.G i).q.v → ∀ (gl : GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J₂.G i).k →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), (∀ y, SuppAt (J₂.G i).q.e _ (gl y) ∧ (mt _ (gl y)).map (J₂.G i).q.pr = ((J₂.G i).FX j (Nat.le_succ_of_le (GlobalTheory.LevProd.step_index_le_s J₂ i hj))).β * y.val * ((J₂.G i).FX j (Nat.le_succ_of_le (GlobalTheory.LevProd.step_index_le_s J₂ i hj))).γ) → ∀ y ∈ KO (J₂.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j), gl y ∈ J.A.U j (J.ι j α) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ α t₂ J₂ hJ₂ i hv gl hgl y hy
  have hjm : j ≤ B.R.m := by omega
  have hok : I.Ok := hW.tr.ok
  have hsup : gl y ∈ GlobalTheory.FinPl.grpAt _ (· = (J₂.G i).q.v) :=
    GlobalTheory.SuppGrp.mem_grpAt_of_suppAt _ _ (J₂.G i).q _ _ (hgl y).1 _ rfl
  have hsd : IsSelfDualC ((I.rec7 l Z).sp.X j) (a.g.x j).L := (ha.x j hjm).sd
  have hKO : GlobalTheory.LevIdx.locHom (J₂.G i).q _ ((J₂.G i).FX j (Nat.le_succ_of_le (GlobalTheory.LevProd.step_index_le_s J₂ i hj))) (gl y) ∈ KO _ _ :=
    (GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 (hgl y).2 ▸ hy
  have hm := GlobalTheory.LevProd.SamePlace.moves_of_mem_KO (J₂.G i).q _ hsd ((J₂.G i).latX j _) hKO
  haveI : Submodule.IsLattice (I.rec7 l Z).host.E (a.g.x j).L := hsd.1
  have hfg : (a.g.x j).L.FG := Submodule.IsLattice.fg (A := (I.rec7 l Z).host.E)
  have hu₂ : I.UnderQ (W.P.I.tup t₂) (J₂.G i).q.v :=
    ⟨J₂.pl i, (hW.tq.Q t₂ (J₂.pl i)).1 (J₂.mem i), ((GlobalTheory.Fam.QJPlaces.places_under W hW u a ha hat t₂ J₂ hJ₂).2 i).symm⟩
  obtain ⟨hTv, hgv⟩ := GlobalTheory.Mem.Col2.TC.underQ_notMem I hok l u _ _ hu₂
  have hbad : (J₂.G i).q.v ∉ J.A.bad j := fun h => by
    rcases hJ.is.bad_le j hjm _ h with (h0 | h0) | ⟨P, hP, e⟩
    · exact hgv 0 h0
    · exact hgv 1 h0
    · obtain ⟨i', hi'⟩ := hJ.surj P ((hW.tq.Q t P).2 hP)
      refine hv ⟨i', ?_⟩
      rw [(GlobalTheory.Fam.QJPlaces.places_under W hW u a ha hat t J hJ).2 i', hi']
      exact e
  have hlb := (hJ.is.reads j hjm).lb (J.ι j α)
  refine (hJ.is.U j hjm _ _).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ hsup, ?_⟩
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have hd : X.piT u ∣ ((B.T u : ℕ) : 𝓞 B.host.E) := ⟨_, (hPr.piT_norm u).symm⟩
  exact exists_mem_level (I.rec7 l Z) _ _ _ (J.A.K j hjm (J.ι j α)).lev (X.piT u) hd hlb (a.g.x j).L hfg
    (fun x => ((hat.pinX.xs j hjm).2.2 x).trans
      (forall_congr' fun r => ⟨fun h => ⟨⟨x r, h⟩, rfl⟩, fun ⟨s, hs⟩ => hs ▸ s.2⟩)) _ hbad hTv _ hsup hm

end GlobalTheory.LevProd.OffTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeStepValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LevProd

theorem locHom_eq_one_of_grpAt {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y : Type} [Fintype Y] [DecidableEq Y] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y)
    {P : GlobalTheory.FinPl.Pl D → Prop} (hP : ¬ P q.v) {x : GA D S} (hx : x ∈ GlobalTheory.FinPl.grpAt S P) :
    GlobalTheory.LevIdx.locHom q S F x = 1 := by
  have h1 : x ∈ GlobalTheory.FinPl.grpOff S (· = q.v) :=
    GlobalTheory.FinPl.SetCut.grpAt_le_grpOff S P (· = q.v) (fun p hp e => hP (e ▸ hp)) hx
  have h2 := GlobalTheory.LocMod.PinInhab.map_mt_eq_one_of_off q (P := (· = q.v)) rfl h1
  symm
  rw [← GlobalTheory.LevIdx.eq_locHom_iff, h2]
  simp [F.βγ]

theorem up_phi_mem_KO : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : QJ a t), J.Reads → ∀ g ∈ GlobalTheory.LevProd.Up a j hj, ∀ i, GlobalTheory.LevProd.phi J j hj g i ∈ KO (J.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ g hg i
  unfold GlobalTheory.LevProd.Up at hg
  split_ifs at hg with h
  · obtain ⟨⟨hsup, hgf⟩, hphi⟩ := Subgroup.mem_inf.1 hg |>.imp_left Subgroup.mem_inf.1
    by_cases hv : GlobalTheory.LevProd.twAt h.choose_spec.choose (J.G i).q.v
    · obtain ⟨i₀, hi₀⟩ := hv
      exact GlobalTheory.T.true_geometry_lattice_closed W hW u a ha hTr j hj _ _ h.choose_spec.choose_spec.1 t J hJ i₀ i hi₀ g hgf
        ((Subgroup.mem_pi _).1 (Subgroup.mem_comap.1 hphi) i₀ (Set.mem_univ _))
    · have hle : h.choose_spec.choose.A.U j (h.choose_spec.choose.ι j h.choose_spec.choose_spec.2.some) ⊔
          GlobalTheory.FinPl.grpAt _ (GlobalTheory.LevProd.twAt h.choose_spec.choose) ≤
          (KO (J.G i).k _).comap ((Pi.evalMonoidHom _ i).comp (GlobalTheory.LevProd.phi J j hj)) := by
        refine sup_le (fun x hx => ?_) (fun x hx => ?_)
        · exact GlobalTheory.T.levProd_phi_mem_KO_of_not_twAt W hW u a ha hTr j hj _ _ h.choose_spec.choose_spec.1 _ t J hJ i hv x hx
        · rw [Subgroup.mem_comap, MonoidHom.comp_apply, Pi.evalMonoidHom_apply]
          change GlobalTheory.LevIdx.locHom (J.G i).q _ _ x ∈ KO (J.G i).k _
          rw [locHom_eq_one_of_grpAt _ _ _ hv hx]
          exact one_mem _
      exact hle hsup
  · rw [Subgroup.mem_bot.1 hg, map_one]
    exact one_mem _
end GlobalTheory.LevProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleColumnScalarAdelicFormContinuousStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tupleColumn_scalarAdelicForm_continuous : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ b y, Continuous (A.rd θ j hj b φ y) := by
  first | exact @GlobalTheory.AdForm.RamCont.rd_continuous | exact GlobalTheory.AdForm.RamCont.rd_continuous | (intros; apply GlobalTheory.AdForm.RamCont.rd_continuous <;> assumption)
end

