import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0414
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0449
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0416
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0426
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntMOfMulRight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelGroupNeTopNeBot
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0454
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0279
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0455
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0345
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0198
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0855
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0351
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineHomAdjointTwistMemCompletedHomLattice
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0036
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0445
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0443
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastPeriodTailEqLoweredEvaluationPeriod
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

open Formalism.L2.Col in

theorem tailTop_eq_of_pin : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → (∀ c, stabOrd UT (h c) = Nat.card ((I.fm l u a).stabilizer₂ c)) → ∀ G' : CXP R P t → (I.per l u a).Mt, (∀ f, ReadsG K eW j g.bT (G' f) f.1) → ∀ n (hn : n = (I.rec7 l Z).R.m), ∀ ψ ∈ k.Ram n, ∀ f : CXP R P t, (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * ∑ β ∈ @Finset.univ (k.Ch n) (k.fin n), ∑ c : (I.fm l u a).clsP, ((stabOrd UT (h c) : ℕ) : ℂ)⁻¹ * ellTop R P eW ε G' c f ((realOf u R g s J).low n hn fun z => k.rd n β ψ (((realOf u R g s J).fr n).symm z) ((g.oT n hn).emb (h c, 1))) = k.cP * (tupOf R P u g t r k tl).tail n hn ψ f := by
  intro B X I hI hP l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hRP heW hbT hLev hG h hh hst G' hG' n hn ψ hψ f
  subst hn
  have hC : PinColL A ι R.ψ R.θ g.x g.vac c₀ k.kom k.dd w k.Ram k.rd k.cK := hCh
  have hIs : A.Is := hC.is
  have hψF : ψ ∈ (I.fm l u a).Fi B.R.m := ((hC.ram B.R.m le_rfl ψ).1 hψ).1.1
  have hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1 := N_m_succ B.R

  obtain ⟨Lz, hLz⟩ : ∃ Lz, Lz = (I.per l u a).lowerMap ((I.per l u a).evz ψ) := ⟨_, rfl⟩
  have hlow : ∀ c (y : FrN (I.rec7 l Z) (B.R.N B.R.m - 1)),
      Lz c ⟨y.1, y.2⟩ = lowOf I l Z u (fun y' => (I.per l u a).evz ψ c ⟨y'.1, y'.2⟩) y :=
    fun c y => hLz ▸ (GlobalTheory.TrueBranch.branching_true_columns I hI hP l Z u hN).2.2.2 a _ c y
  have heL : ∀ c, eW Lz c = fun y => lowOf I l Z u (fun y' => (I.per l u a).evz ψ c ⟨y'.1, y'.2⟩) ⟨y.1, y.2⟩ := by
    intro c; funext y
    rw [heW Lz c y ⟨y.1, y.2⟩ rfl]
    exact hlow c ⟨y.1, y.2⟩

  have hw : ∀ c, eW Lz c ∈ LinearMap.range j := by
    intro c
    rw [hj.range]
    have hv0 := GlobalTheory.EvzVal.evz_mem_valC I hI hP l Z u a ψ hψF c
    have hv1 := (GlobalTheory.TrueBranch.branching_true_columns I hI hP l Z u hN).2.1.1 _ hv0
    obtain ⟨Pp, hPp, hEq⟩ := hv1
    rw [heL c]
    exact ⟨Pp, hPp, funext fun y => congrFun hEq ⟨y.1, y.2⟩⟩
  obtain ⟨G'', hR'', htl⟩ := hG ψ f
  have hper : (I.per l u a).Ptil ψ (G' f) = tl ψ f := by
    rw [htl]
    have := GlobalTheory.Fam.Check.ReadsG.period_eq K eW j g.bT (hG' f) hR'' Lz hw
    rw [hLz] at this
    exact this

  have hsum : ∀ β : k.Ch B.R.m, ∑ c, ((stabOrd UT (h c) : ℕ) : ℂ)⁻¹ * ellTop R P eW ε G' c f
      (lowOf I l Z u (fun z => k.rd B.R.m β ψ ⟨z.1, z.2⟩ ((g.oT B.R.m rfl).emb (h c, 1)))) = ε * tl ψ f := by
    intro β
    have hev : ∀ c y, A.rd R.θ B.R.m le_rfl (ι B.R.m β) ψ y ((g.oT B.R.m rfl).emb (h c, 1)) = (I.per l u a).evz ψ c y :=
      fun c y => (GlobalTheory.AdForm.rd_emb_evz I hI hP l Z u a Ch₀ A hIs R.θ hX.inf _ hTop.emb bad K hRP (ι B.R.m β)).2 ψ hψF c (h c) (hh c) y
    have hterm : ∀ c, ((stabOrd UT (h c) : ℕ) : ℂ)⁻¹ * ellTop R P eW ε G' c f
        (lowOf I l Z u (fun z => k.rd B.R.m β ψ ⟨z.1, z.2⟩ ((g.oT B.R.m rfl).emb (h c, 1)))) =
        ε * (I.per l u a).period (eW.symm (Pi.single c (eW Lz c))) (G' f) := by
      intro c
      have hne : (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.card_pos (α := (I.fm l u a).stabilizer₂ c)).ne'
      have e2 : (fun z : FrN (I.rec7 l Z) (B.R.N B.R.m) => k.rd B.R.m β ψ ⟨z.1, z.2⟩ ((g.oT B.R.m rfl).emb (h c, 1))) =
          fun y' => (I.per l u a).evz ψ c ⟨y'.1, y'.2⟩ := by
        funext z
        exact (congrFun (hC.rdq B.R.m le_rfl β ψ _) _).trans (hev c _)
      rw [e2, ellTop_apply, hst c, heL c]
      field_simp
    rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.mul_sum, ← LinearMap.sum_apply, ← map_sum, ← map_sum]
    have e3 : ∑ c, Pi.single c (eW Lz c) = eW Lz := Finset.univ_sum_single _
    rw [e3, LinearEquiv.symm_apply_apply, ← hper, hLz]
    rfl
  have hsub : Subsingleton (k.Ch B.R.m) :=
    ⟨fun β β' => hC.live.inj B.R.m ((GlobalTheory.AdForm.TwTest.subsingleton_top hIs).elim _ _)⟩
  rw [hTop.cP]
  have htail : ∀ hm, (tupOf R P u g t r k tl).tail _ hm ψ f = tl ψ f := fun _ => rfl
  rw [htail]
  refine (congrArg (fun S => (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * S) (Finset.sum_congr rfl fun β _ => hsum β)).trans ?_
  have e1 : ∀ {α : Type} (inst : Fintype α), (∀ a b : α, a = b) → α → ∀ x : ℂ,
      @Finset.sum α ℂ _ (@Finset.univ α inst) (fun _ => x) = x := by
    intro α inst hs a x
    haveI : Unique α := ⟨⟨a⟩, fun b => hs _ _⟩
    exact Fintype.sum_unique _
  have e0 : ∀ {α : Type} (inst : Fintype α), IsEmpty α → ∀ x : ℂ,
      @Finset.sum α ℂ _ (@Finset.univ α inst) (fun _ => x) = 0 := by
    intro α inst hE x
    rw [Finset.univ_eq_empty, Finset.sum_empty]
  rcases isEmpty_or_nonempty (k.Ch B.R.m) with hE | hne
  · have h0 : ψ = 0 := by
      funext c
      obtain ⟨β, -⟩ := hC.live.last (A.chOf B.R.m c)
      exact (hE.false β).elim
    have h1 : tl ψ f = 0 := by
      rw [← hper, h0]
      show ((I.per l u a).period ((I.per l u a).lowerMap ((I.per l u a).evz 0))) (G' f) = 0
      simp only [map_zero, LinearMap.zero_apply]
    exact (congrArg (fun S => (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * S) (e0 _ hE _)).trans (by rw [h1]; ring)
  · obtain ⟨β₀⟩ := hne
    exact (congrArg (fun S => (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * S) (e1 _ (fun a b => hsub.elim a b) β₀ _)).trans (by ring)

end GlobalTheory.AdForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepDatumTransportBadPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.Transport.LastTw

section TopQ

open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.TopStep GlobalTheory.TopStep.Model

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {m2 : ℕ}

theorem locTop_shiftQ (hc : cst.Ok) {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) (hD : 2 * cst.M ≤ cst.D P)
    (y : HomE X.E (R.N (m2 + 1)) (R.N R.m)) {a b : Sp X.E (R.N (m2 + 1))} (ha : ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * a i))
    (hb : ∀ i, IntAt P.1 (((qOf P.1 : X.E) ^ cst.M)⁻¹ * (b i - a i))) :
    locTop Ch sel mu cst m2 P y b = locTop Ch sel mu cst m2 P y a := by
  have hq := qOf_ne_zero (P := P.1)
  unfold locTop
  congr 1
  generalize atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y = η
  unfold ftY
  rw [if_neg hP, if_neg hP]
  split_ifs with h
  · congr 1
    have ev : ∀ z : Sp X.E (R.N (m2 + 1)), η z = ∑ j, z j * η (Pi.single j 1) := fun z => by
      conv_lhs => rw [pi_eq_sum_univ' z]
      simp [map_sum]
    have he : IntAt P.1 ((epsSg : ℤ) : X.E) := intCast_mem (intRing P.1) _
    have hd : IntAt P.1 ((epsSg : X.E) * η (b - a)) := by
      rw [ev]
      refine he.mul (intAt_sum _ fun j _ => ?_)
      have := (hb j).mul (h j)
      convert this using 1
      rw [Pi.sub_apply, mul_mul_mul_comm, inv_mul_cancel₀ (pow_ne_zero _ hq), one_mul]
    have hz' : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * η a)) := by
      obtain ⟨D, hD'⟩ := Nat.exists_eq_add_of_le hD
      have := (intAt_pow (intAt_nat (P := P.1) (qOf P.1)) D).mul
        (he.mul (intAt_sum Finset.univ fun j _ => (ha j).mul (h j)))
      convert this using 1
      rw [hD', ev, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have := hc.psi_add P _ _ hz' ((intAt_pow (intAt_nat (P := P.1) (qOf P.1)) _).mul hd)
    rw [hc.psi_int P _ hd, mul_one, ← mul_add, ← map_add, add_sub_cancel] at this
    exact this
  · rfl

theorem locTop_congQ (hm : R.m = m2 + 2) (hc : cst.Ok) {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) (hD : 2 * cst.M ≤ cst.D P)
    (y z : HomE X.E (R.N (m2 + 1)) (R.N R.m))
    (hyz : ∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ (cst.M + 1))⁻¹ * (y (Pi.single s 1) l - z (Pi.single s 1) l)))
    {a : Sp X.E (R.N (m2 + 1))} (ha : ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * a i)) :
    locTop Ch sel mu cst m2 P y a = locTop Ch sel mu cst m2 P z a := by
  have hq := qOf_ne_zero (P := P.1)
  choose t ht ez using fun s l => (⟨_, hyz s l, by field_simp; ring⟩ : ∃ t, IntAt P.1 t ∧
    y (Pi.single s 1) l = z (Pi.single s 1) l + (qOf P.1 : X.E) ^ (cst.M + 1) * t)
  have ez' : ∀ s l, z (Pi.single s 1) l = y (Pi.single s 1) l + (qOf P.1 : X.E) ^ (cst.M + 1) * (0 - t s l) :=
    fun s l => by rw [ez]; ring
  have ht' : ∀ s l, IntAt P.1 (0 - t s l) := fun s l => intAt_sub intAt_zero (ht s l)
  have tr : ∀ (y z : HomE X.E (R.N (m2 + 1)) (R.N R.m)) (t : Fin (R.N (m2 + 1)) → Fin (R.N R.m) → X.E),
      (∀ s l, IntAt P.1 (t s l)) → (∀ s l, y (Pi.single s 1) l = z (Pi.single s 1) l + (qOf P.1 : X.E) ^ (cst.M + 1) * t s l) →
      SuppQ (m2 := m2) P.1 cst.M z → SuppQ (m2 := m2) P.1 cst.M y := fun y z t ht ez hz s => by
    refine ⟨fun i => ?_, ?_⟩
    · rw [ez]
      exact ((hz s).1 i).add ((intAt_pow (intAt_nat _) _).mul (ht _ _))
    · rw [ez, mul_add]
      refine (hz s).2.add ?_
      rw [← mul_assoc, ← pow_add]
      exact (intAt_pow (intAt_nat _) _).mul (ht _ _)
  by_cases hz : SuppQ (m2 := m2) P.1 cst.M z
  swap
  · have h1 : locTop Ch sel mu cst m2 P z a = 0 := by
      by_contra h
      exact hz (suppQ_of_ne hm hP h)
    have h2 : locTop Ch sel mu cst m2 P y a = 0 := by
      by_contra h
      exact hz (tr z y _ ht' ez' (suppQ_of_ne hm hP h))
    rw [h1, h2]
  have hy := tr y z t ht ez hz
  unfold locTop
  refine congrArg₂ (· * ·) ?_ ?_
  · have he : ∀ p p', CongQ P.1
        (LocE.entB (qOf P.1) R.k (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1) 0 0
          (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) p p')
        (LocE.entB (qOf P.1) R.k (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1) 0 0
          (prXp X.E R ∘ₗ z ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) p p') := fun p p' => by
      rw [entB_topQ hm, entB_topQ hm]
      split_ifs with h
      · refine ⟨(hy _).1 _, (hz _).1 _, ?_⟩
        show IntAt _ ((y _ _ - z _ _) / _)
        rw [ez]
        convert (intAt_pow (intAt_nat (P := P.1) (qOf P.1)) cst.M).mul (ht ⟨p', h.2⟩ (Br.iC (N_m_succ R) ⟨p, h.1⟩)) using 1
        rw [pow_succ]
        field_simp
        ring
      · exact congQ_zero
    unfold PhiTop
    rw [if_neg hP]
    unfold LocE.PhiQ
    refine @if_congr _ _ _ (_) (_) _ _ _ _ ?_ ?_ rfl
    · simp only [(he _ _).1, (he _ _).2.1, (he _ _).div_iff]
    · exact unitV_det_congr _ fun s s' => he s.1 s'.1
  · unfold ftY
    have ev : ∀ w : HomE X.E (R.N (m2 + 1)) (R.N R.m), (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ w) a =
        ∑ j, a j * w (Pi.single j 1) (Br.iL (N_m_succ R)) := fun w => by
      rw [LinearMap.comp_apply, atNL_last, apply_eq_sum]
    have he : IntAt P.1 ((epsSg : ℤ) : X.E) := intCast_mem (intRing P.1) _
    rw [if_neg hP, if_neg hP, if_pos (fun i => by rw [LinearMap.comp_apply, atNL_last]; exact (hy _).2),
      if_pos (fun i => by rw [LinearMap.comp_apply, atNL_last]; exact (hz _).2), ev, ev]
    congr 1
    have hd : IntAt P.1 ((epsSg : X.E) * ∑ j, ((qOf P.1 : X.E) ^ cst.M * a j) * ((qOf P.1 : X.E) * t j (Br.iL (N_m_succ R)))) :=
      he.mul (intAt_sum _ fun j _ => (ha j).mul ((intAt_nat _).mul (ht _ _)))
    have hz' : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * ∑ j, a j * z (Pi.single j 1) (Br.iL (N_m_succ R)))) := by
      obtain ⟨D, hD'⟩ := Nat.exists_eq_add_of_le hD
      have := (intAt_pow (intAt_nat (P := P.1) (qOf P.1)) D).mul
        (he.mul (intAt_sum Finset.univ fun j _ => (ha j).mul (hz j).2))
      convert this using 1
      rw [hD', Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have := hc.psi_add P _ _ hz' ((intAt_pow (intAt_nat (P := P.1) (qOf P.1)) _).mul hd)
    rw [hc.psi_int P _ hd, mul_one] at this
    rw [← this]
    congr 1
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ez]
    ring

theorem rep_sub_intQ {u : Pr.Word} {j : ℕ} (h : j + 1 = R.m) (p q : PtAt R sel mu cst u j) (e : cosetIn q = cosetIn p)
    {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) (i : Fin (R.N j)) :
    IntAt P.1 (((qOf P.1 : X.E) ^ cst.M)⁻¹ *
      ((frsF sel mu p.1.1 P).symm (repY p.1.2) i - (frsF sel mu q.1.1 P).symm (repY q.1.2) i)) := by
  have h1 : (frsF sel mu p.1.1 P).symm (repY p.1.2) ∈ cosetIn p P :=
    ⟨_, p.repY_mem h, by rw [sub_self, smul_zero]; exact zero_mem _⟩
  rw [← e] at h1
  obtain ⟨z, hz1, h2⟩ := h1
  rw [if_neg hP] at h2
  have h3 := q.repY_mem h
  obtain ⟨y, -, hY⟩ := q.mem_ybSet h
  have h4 := (mem_locLat _ _ _ _).1 ((Set.ext_iff.1 hY _).1 hz1) P
  have h5 := (mem_locLat _ _ _ _).1 ((Set.ext_iff.1 hY _).1 h3) P
  simp only [if_neg hP, zpow_natCast] at h4 h5
  have h6 : ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (z - repY q.1.2) ∈ q.1.1.deco.1.at P.1 := by
    have := sub_mem h4 h5
    rwa [← smul_sub, sub_sub_sub_cancel_right] at this
  rw [← (frsF sel mu q.1.1 P).apply_symm_apply (_ • (z - _)), frsF_mem, map_smul, map_sub] at h6
  have h7 := add_mem h2 h6
  rw [← smul_add, sub_add_sub_cancel] at h7
  simpa using mem_stdAt.1 h7 i

end TopQ

theorem locTop_transport_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (ok : I.Ok) (u : B.Word) (a : I.ι) (n : ℕ) (h : n + 1 + 1 = B.R.m) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a))
    (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u (n + 1)) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (n + 1 + 1))
    (k y : TC.GA B (B.R.N (n + 1))) (k' y' : TC.GA B (B.R.N (n + 1 + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (n + 1)) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (n + 1 + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 → cosetIn q = cosetIn p →
    ∃ M : ℕ, 0 < M ∧ ∀ M₀ : ℕ, M ∣ M₀ → ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N (n + 1)) (B.R.N (n + 1 + 1)),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      GlobalTheory.TopStep.locTop I.Ch I.sel (I.tup a) (I.cst a) n P
                   (castSp B.fields.E (congrArg B.R.N h) ∘ₗ Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀)
                   ((Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P).symm (Formalism.L2.Col.repY p.1.2)) =
        GlobalTheory.TopStep.locTop I.Ch I.sel (I.tup a) (I.cst a) n P
          (castSp B.fields.E (congrArg B.R.N h) ∘ₗ Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x)
          ((Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P).symm (Formalism.L2.Col.repY q.1.2)) := by
  intro B X I l ok u a n h P p q p' q' k y k' y' hp hN hp' hN' hq hq' e
  have hc := (ok.idx_ok a).cst_ok
  have hqpos : 0 < Formalism.L2.Col.qOf P.1 := Nat.pos_of_ne_zero fun h0 => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · have hsq := Formalism.L2.Col.ciQ_notMem_sq (GlobalTheory.Mem.FieldsLaws.fields_ok B) l.pr hP
    refine ⟨Formalism.L2.Col.qOf P.1, hqpos, ?_⟩
    rintro _ ⟨c, rfl⟩ x x₀ hx
    have hv : Valued.v ((Formalism.L2.Col.qOf P.1 * c : ℕ) : P.1.adicCompletion B.fields.E) < 1 := by
      rw [← map_natCast (algebraMap B.fields.E (P.1.adicCompletion B.fields.E)), valued_algebraMap,
        ← map_natCast (algebraMap (𝓞 B.fields.E) B.fields.E), HeightOneSpectrum.valuation_lt_one_iff_mem, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ GlobalTheory.TopStep.qOf_mem
    have H := GlobalTheory.Transport.Last.read_cong hp hN hp' hN' hq hq' ⟨P.1, hP⟩ x x₀ (fun r s => by
      refine lt_of_eq_of_lt (congrArg Valued.v ?_) ((hx r s).trans_lt hv)
      simp only [GlobalTheory.Transport.Last.locM, GlobalTheory.Transport.Last.ratM, Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, map_sub,
        map_sum, map_mul, adAt_inclE])
    have f1 : ∀ {j : ℕ} (r : Formalism.L2.Col.ChPt (R := B.R) I.sel (I.tup a) u j),
        Formalism.L2.Col.frsF I.sel (I.tup a) r P = r.deco.1.liftFr ⟨P.1, hP⟩ := fun r => dif_pos hP
    rw [← f1, ← f1, ← f1, ← f1] at H
    have hq1 := GlobalTheory.TopStep.repY_int q.1.1 (q.mem_ybSet h) hP
    rw [GlobalTheory.Transport.Last.locTop_shift hc hP _ hq1 (GlobalTheory.Transport.Last.rep_sub_int h p q e hP)]
    exact GlobalTheory.Transport.Last.locTop_of_cong h.symm hc hP hsq _ _ _ hq1 H
  · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.1 P.2).resolve_left hP
    have hD := (ok.idx_ok a).depthQ P hP
    have hq0 := GlobalTheory.TopStep.qOf_ne_zero (P := P.1)
    refine ⟨Formalism.L2.Col.qOf P.1 ^ ((I.cst a).M + 1), pow_pos hqpos _, ?_⟩
    rintro _ ⟨c, rfl⟩ x x₀ hx
    have H := GlobalTheory.T.twist_prime_congruent_maps_frame_readings_bound I u a (n + 1) P hQ (GlobalTheory.Mem.Df.disjoint_vGs_Q I ok l a) p q p' q' k y k' y' hp hN hp' hN' hq hq' _ x x₀ hx
    have hqv := GlobalTheory.TopStep.Model.repY_intQ q.1.1 (q.mem_ybSet h) hP
    rw [locTop_shiftQ hc hP hD _ hqv (rep_sub_intQ h p q e hP)]
    have key : ∀ s r, Formalism.L2.Col.IntAt P.1 (((Formalism.L2.Col.qOf P.1 : B.fields.E) ^ ((I.cst a).M + 1))⁻¹ *
        (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀ (Pi.single s 1) r -
          Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x (Pi.single s 1) r)) := by
      intro s r
      rw [GlobalTheory.Proof.IntegralPowerExpansion.intAt_iff_val]
      have H1 := H r s
      rw [Matrix.sub_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply, Nat.cast_mul, Nat.cast_pow, map_mul] at H1
      have hc1 : P.1.valuation B.fields.E (c : B.fields.E) ≤ 1 := by
        rw [← map_natCast (algebraMap (𝓞 B.fields.E) B.fields.E)]
        exact P.1.valuation_le_one _
      have hpos : P.1.valuation B.fields.E ((Formalism.L2.Col.qOf P.1 : B.fields.E) ^ ((I.cst a).M + 1)) ≠ 0 :=
        (Valuation.ne_zero_iff _).2 (pow_ne_zero _ hq0)
      rw [map_mul, map_inv₀, ← neg_sub, Valuation.map_neg]
      calc _ ≤ (P.1.valuation B.fields.E ((Formalism.L2.Col.qOf P.1 : B.fields.E) ^ ((I.cst a).M + 1)))⁻¹ *
            (P.1.valuation B.fields.E ((Formalism.L2.Col.qOf P.1 : B.fields.E) ^ ((I.cst a).M + 1)) * P.1.valuation B.fields.E (c : B.fields.E)) :=
            by gcongr
        _ ≤ (P.1.valuation B.fields.E ((Formalism.L2.Col.qOf P.1 : B.fields.E) ^ ((I.cst a).M + 1)))⁻¹ *
            (P.1.valuation B.fields.E ((Formalism.L2.Col.qOf P.1 : B.fields.E) ^ ((I.cst a).M + 1)) * 1) :=
            by gcongr
        _ = 1 := by rw [mul_one, inv_mul_cancel₀ hpos]
    refine locTop_congQ h.symm hc hP hD _ _ ?_ hqv
    intro s l
    rw [LinearMap.comp_apply, LinearMap.comp_apply, castSp_apply, castSp_apply]
    exact key s _

end GlobalTheory.Transport.LastTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesIntegralNonzeroConstant
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

namespace GlobalTheory.Core.Rk.Exh.LocalConst

variable {D : D7}

theorem continuous_wcoef {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : WRep S T}
    (hom : IsWeilDatumO ψ S T χS χT om) {ν : Measure (WO S T)} {𝓕 : Set (WO S T)} (hν : IsCovolOne (ratL T S) ν 𝓕)
    {Φ₁ Φ₂ : WO S T → ℂ} (h₁ : IsThetaFunO ψ S T Φ₁) (h₂ : IsThetaFunO ψ S T Φ₂) :
    Continuous (wcoef om ν 𝓕 Φ₁ Φ₂) := by
  have hj := GlobalTheory.Unf.jointCont_all D ψ _ _ _ _ om hom Φ₁ h₁
  show Continuous fun g => ∫ w in 𝓕, om (g, 1) Φ₁ w * conj (Φ₂ w) ∂ν
  exact continuous_covolOne_integral hν (fun g w => om (g, 1) Φ₁ w * conj (Φ₂ w))
    ((hj.comp ((continuous_fst.prodMk continuous_const).prodMk continuous_snd)).mul
      (Complex.continuous_conj.comp (h₂.cont.comp continuous_snd)))
    (fun g => GlobalTheory.Size.mul_conj_periodic hom.std (hom.om_pres _ _ h₁) h₂)

theorem continuous_rcoef {θ : InfFam D} {A : HSp D} {cA : CptF A} (hA : HSpace.SigOK A) (hP : HSpace.IsPosDef A)
    {m : Measure (GA D A)} (hm : m.IsHaarMeasure) {u : GA D A → ℂ} (hu : u ∈ A0 θ A cA) :
    Continuous (rcoef m u u) := by
  obtain ⟨⟨K₀, hK₀, hK₀c⟩, X, K, -, hX, hK, hXK⟩ := GlobalTheory.T.definite_unitary_quotient_compact_fundamentalDomain D A hA hP m hm
  have hu' := (Submodule.mem_inf.1 hu).2
  have huc : Continuous u := hu'.1
  have hul : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ A) u := hu'.2.1
  obtain ⟨C, hC⟩ : ∃ C, ∀ g, ‖u g‖ ≤ C := by
    obtain ⟨C, hC⟩ := hK₀.exists_bound_of_continuousOn huc.continuousOn
    refine ⟨C, fun g => ?_⟩
    obtain ⟨γ, hγ, hg⟩ := hK₀c g
    rw [← hul γ hγ g]
    exact hC _ hg
  have e : ∀ g, rcoef m u u g = ∫ x in X, u (x * g) * conj (u x) ∂m := fun g =>
    GlobalTheory.AutomorphicL2Unitary.pet_eq hX (fun γ hγ x => by simp only [rTr, mul_assoc]; exact hul γ hγ _) hul
  have hfin : m X < ⊤ := (measure_mono hXK).trans_lt hK.measure_lt_top
  rw [show rcoef m u u = fun g => ∫ x in X, u (x * g) * conj (u x) ∂m from funext e]
  refine continuous_of_dominated (bound := fun _ => C * C) (fun g => ?_) (fun g => ?_) ?_ ?_
  · exact ((huc.comp (continuous_id.mul continuous_const)).mul
      (Complex.continuous_conj.comp huc)).aestronglyMeasurable
  · exact .of_forall fun x => by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hC _) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hC x))
  · have : IsFiniteMeasure (m.restrict X) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
    exact integrable_const _
  · exact .of_forall fun x => (huc.comp (continuous_const.mul continuous_id)).mul continuous_const

theorem wcoef_mul_fix {S T : HSp D} (om : WRep S T) (ν : Measure (WO S T)) (𝓕 : Set (WO S T)) (Φ₁ Φ₂ : WO S T → ℂ)
    (x κ : GA D S) (h : om (κ, 1) Φ₁ = Φ₁) : wcoef om ν 𝓕 Φ₁ Φ₂ (x * κ) = wcoef om ν 𝓕 Φ₁ Φ₂ x := by
  have e : ((x * κ, 1) : GA D S × GA D T) = (x, 1) * (κ, 1) := by simp
  simp only [wcoef, e, map_mul, Module.End.mul_apply, h]

theorem rcoef_mul_fix {A : HSp D} (m : Measure (GA D A)) (u : GA D A → ℂ) (x κ : GA D A) (h : ∀ g, u (g * κ) = u g) :
    rcoef m u u (x * κ) = rcoef m u u x := by
  have e : rTr A (x * κ) u = rTr A x u := funext fun g => by simp only [rTr, ← mul_assoc, h]
  simp only [rcoef, e]

end GlobalTheory.Core.Rk.Exh.LocalConst

namespace GlobalTheory.Core.Rk.Exh.LocalConst

theorem integral_const : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (B W H : HSp D) (o : OrthDec B W H) (χA χW : (AE D)ˣ →* Circle) (omB : WRep A B) (omW : WRep A W) (omH : WRep A H), IsWeilDatumO ψ A B χA χW omB → IsWeilDatumO ψ A W χA χW omW → IsWeilDatumO ψ A H χA 1 omH → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u ∈ A0 θ A cA, (∀ κ ∈ prin A β Z, ∀ g, u (g * κ) = u g) → ∀ (sW : RealMat W) (Φ : WO A W → ℂ), Occ ψ θ sW omW m β Z u Φ → ∀ f, IsThetaFunO ψ A H f → f ≠ 0 → (∀ κ ∈ prin A β Z, omH (κ, 1) f = f) → (∀ b ∈ GinfC A, omH (b, 1) f = f) → (∀ ν 𝓕, IsCovolOne (ratL H A) ν 𝓕 → ∀ g ∈ openOff A (frameLat A) (under Z), g ∉ prinInf A β Z → wcoef omH ν 𝓕 f f g = 0) → ∀ νB 𝓕B, IsCovolOne (ratL B A) νB 𝓕B → ∃ C : ℂ, C ≠ 0 ∧ ∀ s : ℂ, ∫ g in openOff A (frameLat A) (under Z), integrand omB m νB 𝓕B (frameLat A) a (o.boxT A Φ f) (o.boxT A Φ f) u u s g ∂m = C := by
  intro D ψ θ A cA a hD B W H o χA χW omB omW omH hB hW hH β Z hZ m hm u hu hufix sW Φ hOcc f hf hf0 hfκ hfb hoff
    νB 𝓕B hνB
  obtain ⟨νW, 𝓕W, hνW⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank A.rank
  obtain ⟨νH, 𝓕H, hνH⟩ := GlobalTheory.MixModel.exists_isCovolOne D H.rank A.rank
  have hΦ : IsThetaFunO ψ A W Φ := hOcc.fock.1
  obtain ⟨hPm, hPsub, hPh, mR, hmR, hint⟩ := GlobalTheory.T.principalCongruence_realPoints_integration_heightOne D θ A cA a hD β Z hZ.frame m hm
  set F : GA D A → ℂ := fun g => wcoef omW νW 𝓕W Φ Φ g * wcoef omH νH 𝓕H f f g * rcoef m u u g with hFdef
  have hFc : Continuous F := ((continuous_wcoef hW hνW hΦ hΦ).mul (continuous_wcoef hH hνH hf hf)).mul
    (continuous_rcoef hD.sig hD.pos hm hu)
  have hbox := GlobalTheory.T.weilCoefficient_externalProduct_eq_mul_orthogonalSum D ψ A B W H o χA χW omB omW omH hB hW hH νB 𝓕B νW 𝓕W νH 𝓕H hνB hνW hνH Φ f hΦ hf
  have hFκ : ∀ (b : GinfC A), ∀ κ ∈ prin A β Z, F ((b : GA D A) * κ) = F b := fun b κ hκ => by
    simp only [hFdef, wcoef_mul_fix omW νW 𝓕W Φ Φ _ κ (hOcc.fix κ hκ), wcoef_mul_fix omH νH 𝓕H f f _ κ (hfκ κ hκ),
      rcoef_mul_fix m u _ κ (hufix κ hκ)]
  set c : ℂ := GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip A H νH 𝓕H f f with hc
  have hc0 : c ≠ 0 := by
    have h := GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hH.std hf hf0 hνH
    have e : c = GlobalTheory.RawLift.thetaIP νH 𝓕H f f := by
      simp only [hc, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip, GlobalTheory.RawLift.thetaIP, mul_comm (f _), Complex.star_def]
    rwa [e]
  have hFb : ∀ b : GinfC A, F b = c * (wcoef omW νW 𝓕W Φ Φ b * rcoef m u u b) := fun b => by
    have e : wcoef omH νH 𝓕H f f b = c := by simp only [wcoef, hfb b b.2, hc]
    simp only [hFdef, e]
    ring
  refine ⟨c * ∫ b : GinfC A, wcoef omW νW 𝓕W Φ Φ b * rcoef m u u b ∂mR, mul_ne_zero hc0 (hOcc.real νW 𝓕W hνW mR hmR),
    fun s => ?_⟩
  have hOm : MeasurableSet (openOff A (frameLat A) (under Z)) :=
    (isOpen_openOff A _ (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) _).measurableSet
  have h1 : ∫ g in openOff A (frameLat A) (under Z), integrand omB m νB 𝓕B (frameLat A) a (o.boxT A Φ f) (o.boxT A Φ f)
      u u s g ∂m = ∫ g in openOff A (frameLat A) (under Z), (prinInf A β Z).indicator F g ∂m := by
    refine setIntegral_congr_fun hOm fun g hg => ?_
    by_cases hgP : g ∈ prinInf A β Z
    · rw [Set.indicator_of_mem hgP]
      simp only [integrand, hbox g, hPh g hgP, one_npow, mul_one, hFdef]
    · rw [Set.indicator_of_notMem hgP]
      simp only [integrand, hbox g, hoff νH 𝓕H hνH g hg hgP, mul_zero, zero_mul]
  rw [h1, setIntegral_indicator hPm, Set.inter_eq_right.2 hPsub, hint F hFc hFκ]
  simp only [hFb]
  exact integral_const_mul c _

end GlobalTheory.Core.Rk.Exh.LocalConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineHomAdjointTwistMemCompletedHomLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineHomAdjointTwist_mem_completedHomLattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S L L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (MS : GlobalTheory.FinPl.Lat S) (LL : GlobalTheory.FinPl.Lat L) (LZ : GlobalTheory.FinPl.Lat L''), q.UnitAA → IsSelfDualC S MS → IsSelfDualC L LL → IsSelfDualC L'' LZ → (∀ y ∈ GlobalTheory.FinPl.latV L'' LZ (· = q.v), (rat τ : Mx D L.rank L''.rank) *ᵥ y ∈ GlobalTheory.FinPl.latV L LL (· = q.v)) → ∀ w ∈ latO S L'' (MS : Set _) (LZ : Set _) (· = q.v), GlobalTheory.FinPl.kap τ S w ∈ latO L S (LL : Set _) (MS : Set _) (· = q.v) := by
  first | exact @GlobalTheory.KapLat2.kap_mem_latO | exact GlobalTheory.KapLat2.kap_mem_latO | (intros; apply GlobalTheory.KapLat2.kap_mem_latO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalCharacterConductorOneExistsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_conductor_one_exists : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (PP : Pl D.host.E), PP ∈ (pk W).Pg ∨ QAll W PP → ∀ l : LocX a (pk W).βX PP, (∃ ψk : AddChar l.k Circle, (ofSplit l.q).IsChar (pk W).ψ ψk ∧ HasConductor ψk 1) ∧ (∃ ν : Measure l.k, IsUnitVol ν) ∧ (QAll W PP → ∃ ϖ : l.kˣ, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ ∧ GlobalTheory.SymBridge.IsCompl PP (Formalism.L2.Col.qOf PP) (l.q.pr.comp (incA D)) ϖ) := by
  first | exact @GlobalTheory.WeilCondUnif.cond_unif | exact GlobalTheory.WeilCondUnif.cond_unif | (intros; apply GlobalTheory.WeilCondUnif.cond_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittSourceProofStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelFormulasWittSource_proof : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedSource D := by
  first | exact @GlobalTheory.MixSourceFormulas.mixed_source | exact GlobalTheory.MixSourceFormulas.mixed_source | (intros; apply GlobalTheory.MixSourceFormulas.mixed_source <;> assumption)
end

