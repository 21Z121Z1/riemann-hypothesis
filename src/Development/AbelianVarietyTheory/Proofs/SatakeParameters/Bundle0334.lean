import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0916
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0903
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0737
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0329
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0332
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0801
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0314
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0331
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0317
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0321
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0319
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0320
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0312
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0327
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0325
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorOfMono0
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PlainMono

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem linked_single {ρ ρ' : IrrGL k} (hρ : ρ.IsCusp) (hρ' : ρ'.IsCusp) (hne : ρ ≠ ρ.nu 1) (e : ρ' = ρ.nu 1) :
    (Segment.single ρ hρ).Linked (Segment.single ρ' hρ') := by
  subst e
  refine ⟨⟨Segment.ofFirst ρ hρ 2 two_pos, ?_⟩, ?_, ?_⟩
  · rw [Segment.carrier_single, Segment.carrier_single]
    ext z
    rw [Segment.mem_carrier]
    simp only [Segment.first_ofFirst, Segment.len_ofFirst, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      interval_cases i
      · left; simp
      · right; simp
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by simp⟩
  · rw [Segment.carrier_single, Segment.carrier_single, Set.singleton_subset_iff, Set.mem_singleton_iff]
    exact hne
  · rw [Segment.carrier_single, Segment.carrier_single, Set.singleton_subset_iff, Set.mem_singleton_iff]
    exact fun e => hne e.symm

theorem eq_single_of_len {Δ : Segment k} (h : Δ.len = 1) : Δ = Segment.single Δ.first Δ.isCusp_first :=
  Segment.ext_first (by simp [Segment.single]) (by simp [Segment.single, h])

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem ne_nu_one {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {rc : IrrGL (w.adicCompletion E) → WD h} (L : UpperTheory.Zero.LLC.LawsT a ha rc) {ρ : IrrGL (w.adicCompletion E)}
    (hρ : ρ.IsCusp) : ρ ≠ ρ.nu 1 := by
  intro e0
  refine WD.lpTw_one_ne (rc ρ) (by rw [L.dim]; exact hρ.1) ?_
  calc (rc ρ).lpTw 1 = rc (ρ.nu ((1 : ℝ) : ℂ)) := (L.nu ρ 1).symm
    _ = rc ρ := by rw [Complex.ofReal_one, ← e0]

end GlobalTheory.PlainMono
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SegmentSumNoMonodromyLengthOne
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SegSumOne

theorem segSum_of_mono0 : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (rc : IrrGL (w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc →
    ∀ (l : List (Segment (w.adicCompletion E))), (segSum rc l).mono0 →
      (∀ Δ ∈ l, Δ.len = 1) ∧ segSum rc l = sumList (l.map fun Δ => rc Δ.first) := by
  intro E Ω _ _ _ _ _ A w h rc hrc l hm
  obtain ⟨a, ha, H⟩ := hrc
  have hlen : ∀ Δ ∈ l, Δ.len = 1 := by
    intro Δ hΔ
    have hirr : IsIrrWD ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)) := by
      rw [← H.nu]; exact (H.cusp _ (Δ.isCusp_first.nu _))
    have hmi : (((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len)).mono0 :=
      GlobalTheory.UnlinkedMono.noMonodromy_of_mem_weilDeligneListSum _ hm _ (List.mem_map.2 ⟨Δ, hΔ, rfl⟩)
    have hpos := Δ.len_pos
    by_contra hne
    exact GlobalTheory.SegLen.not_mono0_lpChar_lpSp hirr (by omega) hmi
  refine ⟨hlen, ?_⟩
  unfold segSum
  congr 1
  refine List.map_congr_left fun Δ hΔ => ?_
  rw [hlen Δ hΔ, GlobalTheory.SegLen.lpChar_lpSp_one']
  simp [WD.lpTw_zero]

end GlobalTheory.SegSumOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportOfLengthOneLanglandsDatum
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocGL.LenOneSupport

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_of_isCosocle_prodIrr_one (ρ x : IrrGL k) (y : Fin 1 → IrrGL k) (hy : ∀ a, y a = ρ)
    (hd : ∑ a, (y a).1 = x.1) (h : IsCosocle x.rep (prodIrr y hd)) : x = ρ := by
  have e : y = fun _ => ρ := funext hy
  subst e
  obtain ⟨n, c⟩ := x
  obtain ⟨m, r⟩ := ρ
  have hmn : m = n := by simpa using hd
  subst hmn
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one (⟨m, r⟩ : IrrGL k) hd
  have h2 := h.of_equiv (.refl _) ψ.symm
  obtain ⟨φ⟩ := (isCosocle_self r.rep.irr).unique h2
  have e1 := (IrrGL.of_eq_of (hs := c.rep.smooth) (hi := c.rep.irr) (hs' := r.rep.smooth) (hi' := r.rep.irr)).2 ⟨φ⟩
  exact (IrrGL.of_rep (⟨m, c⟩ : IrrGL k)).symm.trans (e1.trans (IrrGL.of_rep (⟨m, r⟩ : IrrGL k)))

theorem eq_first_of_isLSeg {Δ : Segment k} (hl : Δ.len = 1) {x : IrrGL k} (h : IsLSeg Δ x.rep) : x = Δ.first := by
  have e : Δ = Segment.single Δ.first Δ.isCusp_first := Segment.ext_first rfl hl
  rw [e] at h
  obtain ⟨hd, hc⟩ := h
  refine eq_of_isCosocle_prodIrr_one Δ.first x _ (fun a => ?_) hd hc
  rw [Fin.fin_one_eq_zero a]
  simp [Segment.term, Segment.single, Segment.ofFirst]
  rfl

theorem hasSupport_first_of_isL_len_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (c : ℕ) (Δ : Fin c → Segment k) (x : IrrGL k), (∀ i, (Δ i).len = 1) →
    IsL ((List.ofFn Δ : List (Segment k)) : Multiset (Segment k)) x.rep →
    HasSupport x.rep (Finset.univ.val.map fun i => (Δ i).first) := by
  intro k _ _ _ _ c Δ x hl hL
  obtain ⟨h, y, hd, ⟨Δ', ⟨hmap, -⟩, hy⟩, hcos⟩ := hL
  have hl' : ∀ i, (Δ' i).len = 1 := fun i => by
    have hm : Δ' i ∈ ((List.ofFn Δ : List (Segment k)) : Multiset (Segment k)) :=
      hmap ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
    obtain ⟨j, hj⟩ := List.mem_ofFn.1 (Multiset.mem_coe.1 hm)
    rw [← hj]; exact hl j
  have hyf : y = fun i => (Δ' i).first := funext fun i => eq_first_of_isLSeg (hl' i) (hy i)
  subst hyf
  have hs := hasSupport_of_isSubquotient hcos.1 (fun i => (Δ' i).isCusp_first) hcos.isSubquotient
  have e : (Finset.univ.val.map fun i => (Δ' i).first) = Finset.univ.val.map fun i => (Δ i).first := by
    have e2 : (Finset.univ.val.map Δ : Multiset (Segment k)) = ((List.ofFn Δ : List (Segment k)) : Multiset (Segment k)) := by
      rw [← Fin.univ_val_map]
    have m1 := Multiset.map_map Segment.first Δ' Finset.univ.val
    have m2 := Multiset.map_map Segment.first Δ Finset.univ.val
    simp only [Function.comp_def] at m1 m2
    rw [← m1, ← m2, hmap, e2]
  rw [e] at hs
  exact hs

end GlobalTheory.LocGL.LenOneSupport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SymmTransSymm
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.AwayTop

theorem inFr_trans {E : Type} [Field E] {n m : ℕ} (f f₁ : Sp E n ≃ₗ[E] Sp E n) (g g₁ : Sp E m ≃ₗ[E] Sp E m) (z : HomE E n m) :
    inFr f₁ g₁ z = (g₁.trans g.symm).symm.toLinearMap ∘ₗ inFr f g z ∘ₗ (f₁.trans f.symm).toLinearMap := by
  refine LinearMap.ext fun w => ?_
  simp [inFr, LinearEquiv.trans_symm]

theorem symm_trans_symm {E : Type} [Field E] {n : ℕ} (f f₁ : Sp E n ≃ₗ[E] Sp E n) (y : Sp E n) :
    f₁.symm y = (f₁.trans f.symm).symm (f.symm y) := by
  simp [LinearEquiv.trans_symm]

theorem ptAway_top : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i hi, i = t.m2 + 1 → PtAway A a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie i hi hi1
  subst hi1
  intro β β' x x' x₁ x₁' p p' p₁ p₁' h1 h2 h3 h4 hag
  have hagS : ∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1 :=
    fun v hv => (hag v hv).1
  have hagT : ∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁'.1 = bc (prV (E := D.host.E) v) x'.1 :=
    fun v hv => (hag v hv).2
  have hok := t.idx_ok μ
  have hc := hok.cst_ok
  have e : ∀ q q', xiPt A (t.m2 + 1) hi β β' q q' =
      XiTop t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) q (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β q) q' := by
    intro q q'
    funext z
    unfold xiPt
    rw [dif_neg (by omega), if_neg (by omega)]
  rw [e, e]

  have hF := GlobalTheory.T.chartFrames_congruent_one_of_same_badPlace_components A dtU a hP hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ p p₁ h1 h3 hagS
  have hF' := GlobalTheory.T.chartFrames_congruent_one_of_same_badPlace_components A dtU a hP hTie (t.m2 + 1 + 1) hi β' x' x₁' p' p₁' h2 h4 hagT

  have hcos : cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁ = cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p := by
    ext y
    simp only [cosetOf, Set.mem_setOf_eq]
    refine forall_congr' fun P => ?_
    have hb := GlobalTheory.T.chartBaseCoset_bounded_typePrimes_and_twist A dtU a hP hTie (Nat.le_of_succ_le hi) β P (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P)
      ((GlobalTheory.TwU.Model.sameCoset_equiv t.sel (t.tup μ) (t.cst μ) P).refl _)
    have key := GlobalTheory.T.sameCouplingCoset_invariant_frame_congruent_one t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm)
      (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P) hc (hF P).1 (hF P).2 (hok.depthQ P) hb.1 hb.2 ((frsF t.sel (t.tup μ) p P).symm y)
    rw [← symm_trans_symm] at key
    exact key
  rw [hcos]
  funext z
  rw [XiTop_eq, XiTop_eq]
  congr 1
  ·
    unfold phiT
    congr 1
    refine propext (forall_congr' fun P => ?_)
    have hA := GlobalTheory.T.point_decoration_agree_below A dtU a hP hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ p p₁ h1 h3 hagS P
    have hA' := GlobalTheory.T.point_decoration_agree_below A dtU a hP hTie (t.m2 + 1 + 1) hi β' x' x₁' p' p₁' h2 h4 hagT P
    have hB := GlobalTheory.T.chartFunctional_eq_of_agree_at_badPlaces A dtU a hP hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ p p₁ h1 h3 hagS P
    have hB' := GlobalTheory.T.chartFunctional_eq_of_agree_at_badPlaces A dtU a hP hTie (t.m2 + 1 + 1) hi β' x' x₁' p' p₁' h2 h4 hagT P
    rw [hA, hA']
    refine forall_congr' fun w => imp_congr_right fun hw => and_congr_right fun hzw => ?_
    rw [hB w hw (hA ▸ hw), hB' _ hzw (hA' ▸ hzw)]
  ·
    refine Finset.prod_congr rfl fun P _ => ?_
    obtain ⟨r, hr⟩ := GlobalTheory.T.exists_vector_prescribed_cosets_badPrimes_frames t.sel (t.tup μ) (t.cst μ) (frsF t.sel (t.tup μ) p) (fun P => y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P)
    have hrep : repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) ∈ cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p :=
      Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) ⟨r, hr⟩
    have hb := GlobalTheory.T.chartBaseCoset_bounded_typePrimes_and_twist A dtU a hP hTie (Nat.le_of_succ_le hi) β P _ (hrep P)
    rw [inFr_trans (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p₁ P) (frsF t.sel (t.tup μ) p' P) (frsF t.sel (t.tup μ) p₁' P) z,
      symm_trans_symm (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p₁ P)]
    by_cases hG : P.1 ∈ t.Pr.vGs
    · exact GlobalTheory.T.lastStepDatum_typePrime_invariant_frames_congruent_one A dtU a hP hTie P hG _ _ (hF P).1 (hF P).2 (hF' P).1 (hF' P).2 _ _ (hb.1 hG)
    · exact GlobalTheory.T.lastStepDatum_twistPrime_invariant_congruentFrames A dtU a hP hTie P hG _ _ (hF P).1 (hF P).2 (hF' P).1 (hF' P).2 _ _ (hb.2 hG)

end GlobalTheory.TwV.AwayTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilityFirst
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EigSplit

open Formalism.IndefR.Links in
theorem cast_add {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (x y : D.what₂.Mt μ a) :
    (h ▸ (x + y) : D.what₂.Mt μ b) = (h ▸ x : D.what₂.Mt μ b) + (h ▸ y : D.what₂.Mt μ b) := by
  subst h; rfl

theorem cast_zero {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) :
    (h ▸ (0 : D.what₂.Mt μ a) : D.what₂.Mt μ b) = 0 := by
  subst h; rfl

theorem cast_inj {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) {x y : D.what₂.Mt μ a}
    (hxy : (h ▸ x : D.what₂.Mt μ b) = (h ▸ y : D.what₂.Mt μ b)) : x = y := by
  subst h; exact hxy

theorem cast_symm {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (m : D.what₂.Mt μ b) :
    (h ▸ (h.symm ▸ m : D.what₂.Mt μ a) : D.what₂.Mt μ b) = m := by
  subst h; rfl

theorem fn_zero {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) : X.fn hμ j 0 = 0 := by
  unfold GlobalTheory.NJoin.RealAt.fn; simp; rfl

theorem fn_add {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (x y : D.what₂.Mt μ (j.1 + 1)) :
    X.fn hμ j (x + y) = X.fn hμ j x + X.fn hμ j y := by
  unfold GlobalTheory.NJoin.RealAt.fn; simp; rfl

theorem rep_mem {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (Pp : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    {γ : Formalism.L2.Theta.GA D V} (hγ : γ ∈ GlobalTheory.Hk3.rep V Pp d) : γ ∈ Formalism.L2.Theta.GfC V := by
  unfold GlobalTheory.Hk3.rep at hγ
  split_ifs at hγ with hl
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hR⟩ := hl.choose_spec
    exact (hR.1 γ hγ).1
  · simp at hγ

theorem twist_eq {G H W : Type*} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] (ρ : G →* Module.End ℂ W)
    (rr : G →* H) (F : H → W) (g γ : G) (h1 : ρ γ⁻¹ = 1) :
    ρ (g * γ)⁻¹ (F (rr (g * γ))) = ρ g⁻¹ (F (rr g * rr γ)) := by
  rw [mul_inv_rev, map_mul, map_mul, h1, one_mul]

theorem sum_single_one {W : Type*} [AddCommGroup W] [Module ℂ W] (d : List ℤ) (S : List ℤ → W) :
    (Finsupp.single d (1 : ℂ)).sum (fun d z => z • S d) = S d := by
  rw [Finsupp.sum_single_index (h := fun d (z : ℂ) => z • S d) (zero_smul ℂ _), one_smul]

theorem transport {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (j : Fin D.R.m) (t : X.T) (h : DIV.Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (X.R.HV j t).H)
    (hh : GlobalTheory.Hk3.IsOpsV X.R j t h) (Pp : DIV.Pl D.host.E) (hG : GlobalTheory.Hk3.Good X.R t Pp) (d : List ℤ)
    (y : (X.R.HV j t).H) (c : ℂ)
    (hc : ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.R.extV j t y (g * γ) = c • X.R.extV j t y g) :
    h Pp (Finsupp.single d 1) y = c • y := by
  have hcv := (X.given.core.models.cV j).1
  apply X.hinj j t
  funext g
  have e1 : X.R.extV j t (c • y) g = c • X.R.extV j t y g :=
    congrFun ((X.R.extV j t).map_smul c y) g
  have e3 : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.R.extV j t y (g * γ) =
      (X.R.cV j).ρ g⁻¹ ((X.R.HV j t).e y ((Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict g *
        (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict γ)) := by
    intro γ hγ
    exact twist_eq (X.R.cV j).ρ (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict ((X.R.HV j t).e y) g γ
      (hcv γ⁻¹ (inv_mem (rep_mem _ Pp d hγ)))
  have e2 : X.R.extV j t (h Pp (Finsupp.single d 1) y) g =
      ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.R.extV j t y (g * γ) := by
    refine Eq.trans ?_ (Finset.sum_congr rfl e3).symm
    show (X.R.cV j).ρ g⁻¹ ((X.R.HV j t).e (h Pp (Finsupp.single d 1) y)
      ((Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict g)) = _
    refine Eq.trans (congrArg ((X.R.cV j).ρ g⁻¹) (congrFun (hh Pp hG (Finsupp.single d 1) y)
      ((Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict g))) ?_
    unfold GlobalTheory.Hk3.hkF
    exact (congrArg ((X.R.cV j).ρ g⁻¹) (sum_single_one d _)).trans (map_sum ((X.R.cV j).ρ g⁻¹) _ _)
  exact e2.trans ((hc g).trans e1.symm)

theorem eig_zero {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (Pp : DIV.Pl D.host.E) (d : List ℤ) (c : ℂ) :
    ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j 0 (g * γ) = c • X.fn hμ j 0 g := by
  intro g
  rw [fn_zero]
  simp

theorem eig_add {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (Pp : DIV.Pl D.host.E) (d : List ℤ) (c : ℂ)
    (f₁ f₂ : D.what₂.Mt μ (j.1 + 1)) (h₁ : ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₁ (g * γ) = c • X.fn hμ j f₁ g) (h₂ : ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₂ (g * γ) = c • X.fn hμ j f₂ g) :
    ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j (f₁ + f₂) (g * γ) = c • X.fn hμ j (f₁ + f₂) g := by
  intro g
  rw [fn_add]
  simp only [Pi.add_apply, Finset.sum_add_distrib, smul_add, h₁ g, h₂ g]

theorem alongEig {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (x : D.nd.X i) (Pp : DIV.Pl D.host.E) (d : List ℤ) (c : ℂ)
    (hc : ∀ Q : D.naut.AV i, D.naut.ptV i Q = some x → ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1),
      (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g) :
    ∀ m ∈ eigC D.nd D.naut i x, ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1),
      (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) = m → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g := by
  intro m hm
  unfold eigC at hm
  refine Submodule.iSup_induction (fun Q => ⨆ (_ : Q ∈ {P | D.naut.ptV i P = some x}), D.naut.typeV i Q)
    (motive := fun m => ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1),
      (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) = m → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g) hm ?_ ?_ ?_
  · intro Q m' hm' f' hf'
    by_cases hQ : D.naut.ptV i Q = some x
    · rw [iSup_pos (show Q ∈ {P | D.naut.ptV i P = some x} from hQ)] at hm'
      exact hc Q hQ f' (hf' ▸ hm')
    · rw [iSup_neg (show Q ∉ {P | D.naut.ptV i P = some x} from hQ), Submodule.mem_bot] at hm'
      have : f' = 0 := cast_inj hj (hf'.trans (hm'.trans (cast_zero hj).symm))
      subst this
      exact eig_zero X hμ j Pp d c
  · intro f' hf'
    have : f' = 0 := cast_inj hj (hf'.trans (cast_zero hj).symm)
    subst this
    exact eig_zero X hμ j Pp d c
  · intro m1 m2 ih1 ih2 f' hf'
    have hsplit : f' = (hj.symm ▸ m1 : D.what₂.Mt (D.nd.mu i) (j.1 + 1)) + (hj.symm ▸ m2) := by
      apply cast_inj hj
      rw [hf', cast_add, cast_symm, cast_symm]
    subst hsplit
    exact eig_add X hμ j Pp d c _ _ (ih1 _ (cast_symm hj m1)) (ih2 _ (cast_symm hj m2))

theorem placesOff : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ (i : D.nd.Loc), Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Pp ∉ D.nd.S i ∧ Pp ∉ D.nd.Q i := GlobalTheory.T.good_place_avoids_bad_sets

theorem summandEigen : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (Q : D.naut.AV i), ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∃ c : ℂ, ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g := GlobalTheory.T.good_place_hecke_eigen_match

theorem eigenAgree : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (x : D.nd.X i) (Q Q' : D.naut.AV i), D.naut.ptV i Q = some x → D.naut.ptV i Q' = some x → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → Pp ∉ D.nd.S i → Pp ∉ D.nd.Q i → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∀ f₁ f₂ : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f₁ : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → (hj ▸ f₂ : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q' → f₁ ≠ 0 → f₂ ≠ 0 → ∀ c₁ c₂ : ℂ, (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₁ (g * γ) = c₁ • X.fn hμ j f₁ g) → (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₂ (g * γ) = c₂ • X.fn hμ j f₂ g) → c₁ = c₂ := GlobalTheory.T.points_equal_eigen_match

theorem uniform : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (x : D.nd.X i) Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → Pp ∉ D.nd.S i → Pp ∉ D.nd.Q i → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∃ c : ℂ, ∀ Q : D.naut.AV i, D.naut.ptV i Q = some x → ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g := by
  intro hAF hL D P X hAg h41 h7 hTie i hμ j hj x Pp hG hS hPS hPQ d hd
  by_cases hex : ∃ (Q0 : D.naut.AV i) (f0 : D.what₂.Mt (D.nd.mu i) (j.1 + 1)), D.naut.ptV i Q0 = some x ∧
      (hj ▸ f0 : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q0 ∧ f0 ≠ 0
  · obtain ⟨Q0, f0, hQ0, hf0, hf00⟩ := hex
    obtain ⟨c0, hc0⟩ := summandEigen hAF hL D P X hAg h41 h7 hTie i hμ j hj Q0 Pp hG hS d hd
    refine ⟨c0, fun Q hQ f' hf' => ?_⟩
    obtain ⟨cQ, hcQ⟩ := summandEigen hAF hL D P X hAg h41 h7 hTie i hμ j hj Q Pp hG hS d hd
    by_cases hf'0 : f' = 0
    · subst hf'0; exact eig_zero X hμ j Pp d c0
    · have := eigenAgree hAF hL D P X hAg h41 h7 hTie i hμ j hj x Q0 Q hQ0 hQ Pp hG hS hPS hPQ d hd f0 f' hf0 hf'
        hf00 hf'0 c0 cQ (hc0 f0 hf0) (hcQ f' hf')
      rw [this]; exact hcQ f' hf'
  · refine ⟨0, fun Q hQ f' hf' => ?_⟩
    have hf'0 : f' = 0 := by
      by_contra hne; exact hex ⟨Q, f', hQ, hf', hne⟩
    subst hf'0; exact eig_zero X hμ j Pp d 0

theorem main : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∃ c : ℂ, h Pp (Finsupp.single d 1) y = c • y := by
  intro hAF hL D P X hAg h41 h7 hTie i hμ j hj x hx f hf y hy hy0 h hh Pp hG hS d hd
  have hA := placesOff hAF hL D P X hAg i hμ Pp hG
  have hu := uniform hAF hL D P X hAg h41 h7 hTie i hμ j hj x Pp hG hS hA.1 hA.2 d hd
  have hfE := alongEig X i hμ j hj x Pp d hu.choose hu.choose_spec _ hf f rfl
  refine ⟨hu.choose, transport X j _ h hh Pp hG d y hu.choose fun g => ?_⟩
  rw [hy]
  exact hfE g

end GlobalTheory.EigSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaModuleOfCanonical
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.ThetaTri.exists_thetaMod : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)), GlobalTheory.NJoin.IsCanon X j hj Y → Nonempty (ThetaMod D P.M i Y (P.tp.tup (D.nd.mu i) j) P.cf.eta) := by
  intro hHC hCR hL D P X A i j hj Y hc
  have hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) :=
    Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩
  have hC := X.given.core
  have hth : ∀ v, Formalism.IndefR.Datum.IsThetaFunO X.R.ψ (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j)
      (GlobalTheory.ThetaTri.phi0 j (X.tupT (D.nd.mu i)) v) := fun v => hC.thP.pt_theta j _ _
  have h0 : GlobalTheory.ThetaTri.phi0 j (X.tupT (D.nd.mu i)) ∈ GlobalTheory.ThetaTri.OmI A i j hj hc hμ :=
    GlobalTheory.T.theta_lift_linear_form hHC hCR hL D P X A i j hj Y hc hμ _ hth
  refine ⟨{ Ω := ↥(GlobalTheory.ThetaTri.OmI A i j hj hc hμ)
            ω := GlobalTheory.ThetaTri.omI A i j hj hc hμ
            Λ := GlobalTheory.ThetaTri.lamL A i j hj hc hμ
            inv := fun h g φ F F' y y' hF hy => GlobalTheory.T.theta_lift_equivariance hL D P X A i j hj Y hc hμ h g φ.1 φ.2 F F' y y' hF hy
            φ₀ := ⟨_, h0⟩
            read := fun x y F hF => GlobalTheory.T.theta_lift_automorphic_form hL D P X A i j hj Y hc hμ x y F hF
            loc := ?_ }⟩
  intro s μw ηw hμw hηw
  obtain ⟨h1, h2⟩ := GlobalTheory.T.lifted_characters_agree hL D P X A i j hj
  have hv : ∀ v, GlobalTheory.ThetaTri.phi0 j (X.tupT (D.nd.mu i)) v ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.nV) (Fin D.R.r)
      (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) → ℂ))
      (_ : IsLinAt (GlobalTheory.ThetaTri.omStd A j (X.tupT (D.nd.mu i))) s μw ηw ι ∧
        ∀ Φ, Formalism.IndefR.Datum.IsThetaFunO X.R.ψ (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) (ι Φ)),
      LinearMap.range ι := fun v =>
    GlobalTheory.T.thetaFunctions_spanned_heckeTwisted_standardFrame D X.R.ψ (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) D.R.nV D.R.r (A.PV j) (X.PW j) A.hF
      (A.stdV j) (A.stdW j) _ _ (X.R.ωP j (X.tupT (D.nd.mu i))) (hC.thP.ωP j _) _ _ h1 h2 s μw ηw hμw hηw _ (hth v)
  have hlin := GlobalTheory.ThetaTri.mem_iSup_isLinAt_lin' (GlobalTheory.ThetaTri.omStd A j (X.tupT (D.nd.mu i)))
    (Formalism.IndefR.Datum.IsThetaFunO X.R.ψ (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j))
    (· ∈ GlobalTheory.ThetaTri.OmI A i j hj hc hμ)
    (fun β f hf => GlobalTheory.T.theta_lift_linear_form hHC hCR hL D P X A i j hj Y hc hμ _ fun v => by
      simpa [GlobalTheory.ThetaTri.single1] using Formalism.IndefR.Fock.CCR.theta_smul hf (β v))
    s μw ηw _ hv
  exact GlobalTheory.ThetaTri.mem_iSup_isLinAt_omSub _ _ _ _ _ _ _ _ _ s μw ηw h0 hlin
end

