import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0721
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0724
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0706
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0733
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0725
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0730
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTwistOfSeedCharacterPowers
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up.GoodPrimeSelection

theorem heq_sigma_app {P P' Tw Tw' Y Y' : Type} (hP : P = P') (hTw : Tw = Tw') (hY : Y = Y')
    {RCG : Tw → Finset Y → Type} {RCG' : Tw' → Finset Y' → Type} {gR : ∀ i Q, CommGroup (RCG i Q)} {gR' : ∀ i Q, CommGroup (RCG' i Q)}
    {Ok : Tw → ℕ → Type} {Ok' : Tw' → ℕ → Type} {cO : ∀ i k, CommRing (Ok i k)} {cO' : ∀ i k, CommRing (Ok' i k)}
    (hRCG : HEq RCG RCG') (hgR : HEq gR gR') (hOk : HEq Ok Ok') (hcO : HEq cO cO')
    {twI : P → Tw} {twI' : P' → Tw'} (h1 : HEq twI twI') {Q : P → Finset Y} {Q' : P' → Finset Y'} (h2 : HEq Q Q')
    {k : P → ℕ} {k' : P' → ℕ} (h3 : HEq k k')
    {psi : ∀ w, RCG (twI w) (Q w) →* (Ok (twI w) (k w))ˣ} {psi' : ∀ w, RCG' (twI' w) (Q' w) →* (Ok' (twI' w) (k' w))ˣ}
    (h4 : HEq psi psi') {w : P} {w' : P'} (hw : HEq w w') :
    HEq (⟨twI w, Q w, k w, psi w⟩ : Σ (i : Tw) (Q : Finset Y) (k : ℕ), RCG i Q →* (Ok i k)ˣ)
      (⟨twI' w', Q' w', k' w', psi' w'⟩ : Σ (i : Tw') (Q : Finset Y') (k : ℕ), RCG' i Q →* (Ok' i k)ˣ) := by
  subst hP hTw hY
  cases hRCG; cases hgR; cases hOk; cases hcO; cases h1; cases h2; cases h3; cases h4; cases hw
  rfl

theorem heq_sigma_pow {Tw Tw' Y Y' : Type} (hTw : Tw = Tw') (hY : Y = Y')
    {RCG : Tw → Finset Y → Type} {RCG' : Tw' → Finset Y' → Type} {gR : ∀ i Q, CommGroup (RCG i Q)} {gR' : ∀ i Q, CommGroup (RCG' i Q)}
    {Ok : Tw → ℕ → Type} {Ok' : Tw' → ℕ → Type} {cO : ∀ i k, CommRing (Ok i k)} {cO' : ∀ i k, CommRing (Ok' i k)}
    (hRCG : HEq RCG RCG') (hgR : HEq gR gR') (hOk : HEq Ok Ok') (hcO : HEq cO cO')
    {p : Σ (i : Tw) (Q : Finset Y) (k : ℕ), RCG i Q →* (Ok i k)ˣ} {p' : Σ (i : Tw') (Q : Finset Y') (k : ℕ), RCG' i Q →* (Ok' i k)ˣ}
    (hp : HEq p p') (b : Bool) (c : ℤ) :
    HEq (⟨p.1, p.2.1, p.2.2.1, BlochKatoReduction.Gen.psiAt b (p.2.2.2 ^ c)⟩ : Σ (i : Tw) (Q : Finset Y) (k : ℕ), RCG i Q →* (Ok i k)ˣ)
      (⟨p'.1, p'.2.1, p'.2.2.1, BlochKatoReduction.Gen.psiAt b (p'.2.2.2 ^ c)⟩ : Σ (i : Tw') (Q : Finset Y') (k : ℕ), RCG' i Q →* (Ok' i k)ˣ) := by
  subst hTw hY
  cases hRCG; cases hgR; cases hOk; cases hcO; cases hp
  rfl

theorem disjoint_of_heq {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H')
    {A B : Finset (PlE H)} {A' B' : Finset (PlE H')} (hA : HEq A A') (hB : HEq B B') (h : Disjoint A B) : Disjoint A' B' := by
  subst hR; cases hH; cases hA; cases hB; exact h

theorem plE_eq {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H') : PlE H = PlE H' := by
  subst hR; cases hH; rfl

theorem auxiliaryPrime_eq_of_same_ranks_host {D D' : D7} (hR : D.R = D'.R) (hH : HEq D.host D'.host) : AbsolutelyIrreducibleSpan.q0 D = AbsolutelyIrreducibleSpan.q0 D' := by
  cases D; cases D'
  dsimp only at hR hH
  subst hR; cases hH
  rfl

theorem discr_eq {D D' : D7} (hR : D.R = D'.R) (hH : HEq D.host D'.host) :
    (NumberField.discr D.host.E).natAbs.primeFactors = (NumberField.discr D'.host.E).natAbs.primeFactors := by
  cases D; cases D'
  dsimp only at hR hH
  subst hR; cases hH
  rfl

theorem mem_avD_iff {D : D7} (i : D.ntw.Tw) (v : PlE D.host) :
    v ∈ avD D (avDesign D) i ↔ ∃ p ∈ avPrimes D ∪ avPrimesDesign D i, v ∈ placesOver D.host.E p := by
  classical
  unfold avD
  rw [Finset.mem_union, mem_avRec, mem_avDesign]
  constructor
  · rintro (⟨p, hp, hv⟩ | ⟨p, hp, hv⟩)
    · exact ⟨p, Finset.mem_union_left _ hp, hv⟩
    · exact ⟨p, Finset.mem_union_right _ hp, hv⟩
  · rintro ⟨p, hp, hv⟩
    rcases Finset.mem_union.1 hp with hp | hp
    · exact Or.inl ⟨p, hp, hv⟩
    · exact Or.inr ⟨p, hp, hv⟩

theorem avD_heq {D D' : D7} (h : SameExport D D') {i : D.ntw.Tw} {i' : D'.ntw.Tw} (hi : HEq i i') :
    HEq (avD D (avDesign D) i) (avD D' (avDesign D') i') := by
  have hl : D.ntw.l i = D'.ntw.l i' := ((same_basic h.gal h.set h.frm).2.2.2.2 i i' hi).1
  have hd : avPrimesDesign D i = avPrimesDesign D' i' := by
    unfold avPrimesDesign
    rw [hl, auxiliaryPrime_eq_of_same_ranks_host h.gal.R h.gal.host, discr_eq h.gal.R h.gal.host]
  refine heq_places h.gal.R h.gal.host (s := avPrimes D ∪ avPrimesDesign D i) (mem_avD_iff i) ?_
  intro v
  rw [mem_avD_iff i' v, h.av, hd]

def normE {D : D7} (xd : ThData D) (h : XdAll xd) : IntegralHeckeForms.XD D where
  Dat0 i j b := if 1 ≤ j ∧ j ≤ D.R.m then Set.univ else ∅
  theta_base_equivariant i j b a ha u := by
    by_cases hj : 1 ≤ j ∧ j ≤ D.R.m
    · exact xd.thetaBase_invariant_action i j b a (by rw [h i j b hj.1 hj.2]; trivial) u
    · rw [if_neg hj] at ha
      exact ha.elim

theorem normE_eq {D : D7} (xd : ThData D) (h : XdAll xd) :
    ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, (normE xd h).Dat0 i j b = (twEOf xd).Dat0 i j b := by
  intro i j hj b
  rw [Finset.mem_Icc] at hj
  show (if 1 ≤ j ∧ j ≤ D.R.m then Set.univ else ∅) = xd.xd0 i j b
  rw [if_pos hj, h i j b hj.1 hj.2]

theorem heq_ite_univ {T T' : Type} (hT : T = T') {Dat : T → ℕ → Bool → Type} {Dat' : T' → ℕ → Bool → Type}
    (hD : HEq Dat Dat') {m m' : ℕ} (hm : m = m') :
    HEq (fun i j b => (if 1 ≤ j ∧ j ≤ m then Set.univ else ∅ : Set (Dat i j b)))
      (fun i j b => (if 1 ≤ j ∧ j ≤ m' then Set.univ else ∅ : Set (Dat' i j b))) := by
  subst hT hm; cases hD; rfl

theorem normE_heq {D D' : D7} (h : SameExport D D') (xd : ThData D) (hx : XdAll xd) (xd' : ThData D') (hx' : XdAll xd') :
    HEq (normE xd hx).Dat0 (normE xd' hx').Dat0 :=
  heq_ite_univ (eq_of_heq h.set.Tw) h.frm.Dat (by rw [h.gal.R])

theorem goodTw_swap {D : D7} {E E' : IntegralHeckeForms.XD D} (hE : ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, E.Dat0 i j b = E'.Dat0 i j b)
    {N0 : D.ntw.Tw → ℕ} {i : D.ntw.Tw} {e : ℝ} {S : ∀ (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b)}
    {A Q : Finset (PlE D.host)} {k : ℕ} {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ}
    (h : IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) E N0 i e S A Q k ψ) : IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) E' N0 i e S A Q k ψ := by
  unfold IntegralHeckeForms.GoodTw at h ⊢
  obtain ⟨h1, ⟨eB, h0, hs, hI⟩, h3, h4⟩ := h
  refine ⟨h1, ⟨eB, h0, hs, fun j hj b => ?_⟩, fun j hj b => ?_, h4⟩
  · have := hI j hj b
    unfold IntegralHeckeForms.SgJ at this ⊢
    rwa [← hE i j hj b]
  · have := h3 j hj b
    unfold IntegralHeckeForms.SgJ at this ⊢
    rwa [← hE i j hj b]

theorem ok_swap {D : D7} {I I' : TwIn D} (hE : ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, I.E.Dat0 i j b = I'.E.Dat0 i j b)
    (hS : I.S = I'.S) {i : D.ntw.Tw} (h : I.Ok i) : I'.Ok i := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun j hj b => ?_, fun j hj b => ?_⟩
  · have := h1 j hj b
    unfold TwIn.Sg IntegralHeckeForms.SgJ IntegralHeckeForms.FullRk at this ⊢
    rw [← hE i j hj b]
    exact this
  · have := h2 j hj b
    unfold TwIn.Sg IntegralHeckeForms.SgJ at this ⊢
    rw [← hE i j hj b, ← hS]
    exact this

theorem good_pack {D D' : D7} (h : SameExport D D') {I : TwIn D} {I' : TwIn D'} (hE : HEq I.E.Dat0 I'.E.Dat0)
    (hN : HEq I.N0 I'.N0) (hS : HEq I.S I'.S) {p : TwPack D} {p' : TwPack D'} (hp : HEq p p')
    {A : Finset (PlE D.host)} {A' : Finset (PlE D'.host)} (hA : HEq A A')
    (hg : IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) I.E I.N0 p.1 (twEps D p.1) (I.S p.1) A p.2.1 p.2.2.1 p.2.2.2) :
    IntegralHeckeForms.GoodTw D'.nexp (BlochKatoReduction.bk0 D') I'.E I'.N0 p'.1 (twEps D' p'.1) (I'.S p'.1) A' p'.2.1 p'.2.2.1 p'.2.2.2 := by
  obtain ⟨-, -, -, h1, h2⟩ := same_basic h.gal h.set h.frm
  obtain ⟨h3, h4, h5, h6⟩ := h1 p p' hp
  obtain ⟨h7, h8, -⟩ := h2 _ _ h3
  obtain ⟨i, Q, k, ψ⟩ := p
  obtain ⟨i', Q', k', ψ'⟩ := p'
  dsimp only at h3 h4 h5 h6 h7 h8 hg ⊢
  subst h5
  have he : twEps D' i' = twEps D i := by rw [twEps, twEps, h7]
  rw [he]
  exact goodTw_transfer h.gal h.set h.frm (B := BlochKatoReduction.bk0 D) (B' := BlochKatoReduction.bk0 D') h.br rfl rfl hE hN h3 _ (h8 _ _ hS).1 hA h4 k h6 hg

theorem psiAt_pow_pow {Γ A : Type} [Group Γ] [CommGroup A] (b : Bool) (ψ : Γ →* A) (a c : ℤ) :
    ∃ e : ℤ, e.natAbs = a.natAbs * c.natAbs ∧ BlochKatoReduction.Gen.psiAt b ((ψ ^ a) ^ c) = ψ ^ e := by
  obtain ⟨e, he, h⟩ := Formalism.MainNotions.N.TwAll.psiAt_side_zpow true b ψ (a * c)
  refine ⟨e, by rw [he, Int.natAbs_mul], ?_⟩
  rw [← zpow_mul, h]
  simp [BlochKatoReduction.Gen.psiAt]

theorem goodO_of_seed : ∀ (D₁ D₂ D₃ : D7) (A : D₁.ntw.Tw → Finset (PlE D₁.host)) (σ : Seed D₁ A) (C₂ : NChoice D₂)
    (C₃ : NChoice D₃) (xd : ThData D₃) (u : D₃.what₂.places.Pl → D₁.what₂.places.Pl), SameExport D₁ D₂ → Kept C₂ C₃ →
    avPrimes D₂ = avPrimes D₃ → D₂.what₂.places.Pl = D₃.what₂.places.Pl → XdAll xd → (∀ i, avD D₁ (avDesign D₁) i ⊆ A i) →
    (∀ v₂ v₃, HEq v₂ v₃ → TwistedAt D₃ v₃ → TwistedAt D₁ (u v₃) ∧ ∃ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l (σ.s (u v₃))) ∧
      HEq (rawPack C₂ v₂) (GlobalTheory.HeightCounting.twPackPow D₁ a (σ.pack (u v₃)))) → GoodO D₃ C₃ xd := by
  intro D₁ D₂ D₃ A σ C₂ C₃ xd u h12 hK hav hPl hxd hA hu
  have h23 : SameExport D₂ D₃ := ⟨hK.gal, hK.set, hK.forms, hK.br, hav⟩
  have h13 : SameExport D₁ D₃ := h12.trans h23
  obtain ⟨hTw, -, hSS, hcomp, hsame⟩ := same_basic h13.gal h13.set h13.frm
  have hY : PlE D₁.host = PlE D₃.host := plE_eq h13.gal.R h13.gal.host

  have key : ∀ v, TwistedAt D₃ v → TwistedAt D₁ (u v) ∧ ∃ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l (σ.s (u v))) ∧
      HEq (GlobalTheory.HeightCounting.twPackPow D₁ a (σ.pack (u v))) (rawPack C₃ v) := by
    intro v hv
    obtain ⟨ht, a, ha, hp⟩ := hu (cast hPl.symm v) v (cast_heq _ _) hv
    refine ⟨ht, a, ha, hp.symm.trans ?_⟩
    exact heq_sigma_app (RCG := D₂.ntw.RCG) (RCG' := D₃.ntw.RCG) (gR := D₂.ntw.grpRCG) (gR' := D₃.ntw.grpRCG)
      (Ok := D₂.ntw.Ok) (Ok' := D₃.ntw.Ok) (cO := D₂.ntw.crOk) (cO' := D₃.ntw.crOk)
      hPl (eq_of_heq hK.set.Tw) (plE_eq hK.gal.R hK.gal.host) hK.set.RCG hK.set.grpRCG hK.set.Ok hK.set.crOk
      hK.twI hK.Q hK.k hK.psi (cast_heq _ _)
  have hN0 : (D₁.ntw.Tw → ℕ) = (D₃.ntw.Tw → ℕ) := by rw [hTw]
  let I₁ : TwIn D₁ := ⟨normE σ.xd σ.all, σ.N0, σ.S⟩
  let In : TwIn D₃ := ⟨normE xd hxd, cast hN0 σ.N0, cast hSS σ.S⟩
  let I₃ : TwIn D₃ := ⟨twEOf xd, cast hN0 σ.N0, cast hSS σ.S⟩
  have hE : HEq I₁.E.Dat0 In.E.Dat0 := normE_heq h13 σ.xd σ.all xd hxd
  have hN : HEq I₁.N0 In.N0 := (cast_heq _ _).symm
  have hS : HEq I₁.S In.S := (cast_heq _ _).symm
  have h1n : ∀ i, ∀ j ∈ Finset.Icc 1 D₁.R.m, ∀ b, (twEOf σ.xd).Dat0 i j b = (normE σ.xd σ.all).Dat0 i j b :=
    fun i j hj b => (normE_eq σ.xd σ.all i j hj b).symm
  have h3n : ∀ i, ∀ j ∈ Finset.Icc 1 D₃.R.m, ∀ b, In.E.Dat0 i j b = I₃.E.Dat0 i j b := normE_eq xd hxd

  have pw : ∀ v, TwistedAt D₃ v → ∀ c : ℤ, Nat.Coprime c.natAbs (D₃.ntw.l (C₃.twI v)) →
      ∀ (B₁ : Finset (PlE D₁.host)) (B₃ : Finset (PlE D₃.host)), HEq B₁ B₃ → B₁ ⊆ A (σ.s (u v)) →
      I₃.Ok (C₃.twI v) ∧ IntegralHeckeForms.GoodTw D₃.nexp (BlochKatoReduction.bk0 D₃) I₃.E I₃.N0 (C₃.twI v) (twEps D₃ (C₃.twI v)) (I₃.S (C₃.twI v)) B₃
        (C₃.Q v) (C₃.k' v) (BlochKatoReduction.Gen.psiAt (C₃.sd v) (C₃.psi' v ^ c)) := by
    intro v hv c hc B₁ B₃ hB hBA
    obtain ⟨ht, a, ha, hp⟩ := key v hv
    have hl : D₁.ntw.l (σ.s (u v)) = D₃.ntw.l (C₃.twI v) := (hsame _ _ (hcomp _ _ hp).1).1
    have hq := heq_sigma_pow (RCG := D₁.ntw.RCG) (RCG' := D₃.ntw.RCG) (gR := D₁.ntw.grpRCG) (gR' := D₃.ntw.grpRCG)
      (Ok := D₁.ntw.Ok) (Ok' := D₃.ntw.Ok) (cO := D₁.ntw.crOk) (cO' := D₃.ntw.crOk)
      hTw hY h13.set.RCG h13.set.grpRCG h13.set.Ok h13.set.crOk hp (C₃.sd v) c
    obtain ⟨e, he, hpe⟩ := psiAt_pow_pow (C₃.sd v) (σ.ψ (σ.s (u v))) a c
    have hce : Nat.Coprime e.natAbs (D₁.ntw.l (σ.s (u v))) := by
      rw [he]
      exact Nat.Coprime.mul ha (hl ▸ hc)
    obtain ⟨hok, hg⟩ := σ.good (u v) ht
    have g1 := goodTw_swap h1n (hg e hce)
    rw [← hpe] at g1
    have g2 : IntegralHeckeForms.GoodTw D₁.nexp (BlochKatoReduction.bk0 D₁) I₁.E I₁.N0 (σ.s (u v)) (twEps D₁ (σ.s (u v))) (I₁.S (σ.s (u v))) B₁
        (σ.Q (σ.s (u v))) (σ.k (σ.s (u v))) (BlochKatoReduction.Gen.psiAt (C₃.sd v) ((σ.ψ (σ.s (u v)) ^ a) ^ c)) :=
      expGood_anti (I := I₁) (p := ⟨σ.Q (σ.s (u v)), σ.k (σ.s (u v)), _⟩) hBA g1
    have ok1 : I₁.Ok (σ.s (u v)) := ok_swap (I := ⟨twEOf σ.xd, σ.N0, σ.S⟩) (I' := I₁) h1n rfl hok
    have g3 := good_pack h13 hE hN hS hq hB g2
    have ok3 := (SameExport.good h13 hE hN hS hq
      ⟨ok1, expGood_anti (I := I₁) (p := ⟨σ.Q (σ.s (u v)), σ.k (σ.s (u v)), _⟩)
        ((avRec_subset_avD D₁ (avDesign D₁) _).trans (hA _)) g1⟩).1
    exact ⟨ok_swap h3n rfl ok3, goodTw_swap h3n g3⟩
  refine ⟨⟨I₃, rfl, fun v hv => ?_, fun v hv _ => ?_⟩, fun v v' hv hv' hne => ?_⟩
  · obtain ⟨ht, a, ha, hp⟩ := key v hv
    exact ⟨(pw v hv 1 (by simp) _ _ h13.avRec ((avRec_subset_avD D₁ (avDesign D₁) _).trans (hA _))).1,
      fun c hc => (pw v hv c hc _ _ h13.avRec ((avRec_subset_avD D₁ (avDesign D₁) _).trans (hA _))).2⟩
  · obtain ⟨ht, a, ha, hp⟩ := key v hv
    have h := (pw v hv 1 (by simp) _ _ (avD_heq h13 (hcomp _ _ hp).1) (hA _)).2
    rw [zpow_one] at h
    exact h
  · obtain ⟨ht, a, ha, hp⟩ := key v hv
    obtain ⟨ht', a', ha', hp'⟩ := key v' hv'
    obtain ⟨hi, hQ, -, -⟩ := hcomp _ _ hp
    obtain ⟨hi', hQ', -, -⟩ := hcomp _ _ hp'
    refine disjoint_of_heq h13.gal.R h13.gal.host hQ hQ' (σ.sep (u v) (u v') ht ht' fun he => hne ?_)
    exact eq_of_heq ((hi.symm.trans (heq_of_eq he)).trans hi')

end GlobalTheory.HeightCounting.Up.GoodPrimeSelection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGaloisStageFitsOfSameCentreActionsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeGaloisStage_fits_of_same_centre_actions : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)), GrpTrue N f → N.nd.PlG = x.o.N.nd.PlG → HEq N.naut.plGw x.o.N.naut.plGw → HEq N.ntypes.cenAmb x.o.N.ntypes.cenAmb → HEq N.ntypes.cenMt x.o.N.ntypes.cenMt → GrpAt (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.I ∧ ∀ eR, StdIso (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.px eR → CenIs P.q.p N eR := by
  first | exact @GlobalTheory.Mem.R3.Rw.SwapN.fits_swap | exact GlobalTheory.Mem.R3.Rw.SwapN.fits_swap | (intros; apply GlobalTheory.Mem.R3.Rw.SwapN.fits_swap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeReadingEigenvaluePlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_reading_eigenvalue_place : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x → ∀ (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), StabC (SOf x) hL' → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → ∀ (j k : ℕ) (Pl : PlE (Dof x).host), 1 ≤ j → j ≤ (Dof x).R.m → IsSplitPl (Dof x).host Pl → Pl ∉ SbD (Dof x) → k ≤ (Dof x).R.r → ∀ la : HeightOneSpectrum (𝓞 (SOf x).Ks), (∀ q : ℕ, q.Prime → (q : 𝓞 (Dof x).host.E) ∈ Pl.asIdeal → (q : 𝓞 (SOf x).Ks) ∉ la.asIdeal) → ∀ (f : (SOf x).WL j) (hf : f ∈ ((SOf x).A j).WK) (hg : hL' j k Pl f ∈ ((SOf x).A j).WK), (∀ y, ((SOf x).A j).nrm la y ⟨f, hf⟩ ≤ 1) → ∀ y, ((SOf x).A j).nrm la y ⟨hL' j k Pl f, hg⟩ ≤ 1 := by
  first | exact @GlobalTheory.RatHeckeBall.ratHecke_keeps_ball | exact GlobalTheory.RatHeckeBall.ratHecke_keeps_ball | (intros; apply GlobalTheory.RatHeckeBall.ratHecke_keeps_ball <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeRowOfLocalAll
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.L2.Theta Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem hkRow_move (Rl : RealDat3 D A3 Ks) {i' i : Fin D.R.m} (h : i' = i) (k : ℕ) (P : PlE D.host)
    (u v : Fin (Rl.nW i') → D.what₂.LL) (u' v' : Fin (Rl.nW i) → D.what₂.LL) (hu : HEq u u') (hv : HEq v v')
    (hec : ∀ (α : GA D (Wc D i')) (R : Finset (GA D (Wc D i'))), IsHeckeAt (Wc D i') P k α →
      Bridge.IsDC (levG (Wc D i') (Rl.βW i') (Rl.datWp i' Rl.triv)) α R →
      (Rl.HW i' (sg0 D A3.A)).e ((Rl.FW i').j (sg0 D A3.A) u) =
        hkNorm Rl i' k P • heckeOn (Rl.MW i' (sg0 D A3.A)) R ((Rl.HW i' (sg0 D A3.A)).e ((Rl.FW i').j (sg0 D A3.A) v))) :
    ∀ (α : GA D (Wc D i)) (R : Finset (GA D (Wc D i))), IsHeckeAt (Wc D i) P k α →
      Bridge.IsDC (levG (Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α R →
      (Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) u') =
        hkNorm Rl i k P • heckeOn (Rl.MW i (sg0 D A3.A)) R ((Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) v')) := by
  subst h
  cases hu
  cases hv
  exact hec

theorem hkRow_of_ad (Rl : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x)
    (Y : NExpRealS Rl cG (ratDatR Rl cG kKs hk)) (H : NExpRealH Rl cG _ Y) (Sb : Finset (PlE D.host))
    (hfi : ∀ i x, HEq ((Y.fi i).e x) x) (hS : ∀ i, Sb ⊆ D.ntw.S0 i)
    (hec : ∀ j k P α Rr, 1 ≤ j → j ≤ D.R.m → HkDat Rl Sb (idxOf D j) k P α Rr → ∀ x : Fin (Rl.nW (idxOf D j)) → D.what₂.LL,
      (Rl.HW (idxOf D j) (sg0 D A3.A)).e ((Rl.FW (idxOf D j)).j (sg0 D A3.A) (H.hL j k P x)) =
        hkNorm Rl (idxOf D j) k P • heckeOn (Rl.MW (idxOf D j) (sg0 D A3.A)) Rr
          ((Rl.HW (idxOf D j) (sg0 D A3.A)).e ((Rl.FW (idxOf D j)).j (sg0 D A3.A) x))) :
    NExpHeckeRowX Rl cG _ Y H fun _ => LinearMap.id := by
  refine ⟨fun i k P hsp _ hoff h2 hkr α R hα hR x _ => ?_⟩
  obtain ⟨i', hi'⟩ := hoff
  exact hkRow_move Rl (idxOf_succ D i) k P (H.hL ((i : ℕ) + 1) k P x) x ((Y.fi i).e (H.hL ((i : ℕ) + 1) k P x)) ((Y.fi i).e x)
    (hfi i _).symm (hfi i _).symm
    (fun α' R' hα' hR' => hec ((i : ℕ) + 1) k P α' R' (by omega) (by have := i.2; omega)
      ⟨hsp, fun h => hi' (hS i' h), h2, hkr, hα', hR'⟩ x) α R hα hR

end Gen

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

theorem hkRowX {x : St P} (l : LC hL x) : NExpHeckeRowX x.m.z.R x.m.z.cG _ l.b.YS (hkH l) fun _ => LinearMap.id :=
  hkRow_of_ad x.m.z.R x.m.z.cG l.rat.kKs l.rat.hk l.b.YS (hkH l) l.rat.In.Sb l.b.fi l.b.Sb_le l.rat.rat.hecke

theorem hkRowL {x : St P} (L : LocAll (lay0 (Dof x))) (l : LC hL x) :
    NExpHeckeRowX (datL x L).R (datL x L).cG _ (ysL L l) (hkHL L l) fun _ => LinearMap.id :=
  ⟨(by with_unfolding_all exact ((hkRowX l).tie :))⟩

end GlobalTheory.HeightCounting.Fin3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFrameFamilyChartCoordinatesHolomorphiStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_frameFamily_chart_coordinates_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), ∀ (c' : AlgChart X.str (σ.comp e.toRingHom) X.dim) (k : U.Comp) (n : ℕ) (W : Set (V n)) (ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q)), IsOpen W → (∀ w ∈ W, ψ w ∈ (U.X k).dom) → (∀ τ i i', DifferentiableOn ℂ (fun w => mat (ψ w) τ i i') W) → ∃ q : V n → CxPts X.str (σ.comp e.toRingHom), IsOpen {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} ∧ (∀ w ∈ W, ∀ h : ψ w ∈ (U.X k).dom, (∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)) → q w ∈ c'.e.source ∧ cxOf e σ hj (q w) = cxPt T.Z (U.un k ⟨ψ w, h⟩)) ∧ DifferentiableOn ℂ (fun w => c'.e (q w)) {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} := by
  first | exact @GlobalTheory.LieBase.isHol_chart_framePt | exact GlobalTheory.LieBase.isHol_chart_framePt | (intros; apply GlobalTheory.LieBase.isHol_chart_framePt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomogeneousComponentChernClassesOfRoots
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

namespace GlobalTheory.GrassComp

theorem esymm_isHomogeneous' (n k : ℕ) : (esymm (Fin n) ℝ k).IsHomogeneous k := by
  unfold esymm
  refine IsHomogeneous.sum _ _ _ fun t ht => ?_
  have h := IsHomogeneous.prod t (fun i => (X i : MvPolynomial (Fin n) ℝ)) (fun _ => 1)
    (fun i _ => isHomogeneous_X ℝ i)
  rw [Finset.sum_const, (Finset.mem_powersetCard.mp ht).2] at h
  simpa using h

theorem chernRoots_monomial_isHomogeneous {ι : Type} (m : ι → ℕ) (s : (ι × ℕ) →₀ ℕ) (c : ℝ) :
    (chernRoots m (monomial s c)).IsHomogeneous (Finsupp.weight Prod.snd s) := by
  rw [chernRoots, aeval_monomial, Finsupp.weight_apply, Finsupp.sum]
  have hc : (algebraMap ℝ (MvPolynomial (Root m) ℝ) c).IsHomogeneous 0 := isHomogeneous_C _ _
  have := hc.mul (IsHomogeneous.prod (s.support) (fun x => (rename (Sigma.mk x.1) (esymm (Fin (m x.1)) ℝ x.2)) ^ s x)
    (fun x => x.2 * s x) (fun x _ => ((esymm_isHomogeneous' (m x.1) x.2).rename_isHomogeneous).pow (s x)))
  simpa [Finsupp.prod, smul_eq_mul, mul_comm] using this

theorem homogeneousComponent_chernRoots {ι : Type} (m : ι → ℕ) (Q : MvPolynomial (ι × ℕ) ℝ) (d : ℕ) :
    homogeneousComponent d (chernRoots m Q) = chernRoots m (weightedHomogeneousComponent Prod.snd d Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [homogeneousComponent_of_mem (chernRoots_monomial_isHomogeneous m s c),
      weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial _ _ _ rfl)]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add, hp, hq]

end GlobalTheory.GrassComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeCellOfInFaceOfCellFormCMFieldStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inRealCone_cell_of_inFace_of_cellForm_CMField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCarrierDim H.bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → Dominates H.bar X → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v β → ∀ x ∈ balForms H.bar X, (∀ y, 0 ≤ x y y) → ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x → lab.evalZ (β + x) = lab.evalZ β → InRCone v x := by
  first | exact @GlobalTheory.PolFan.Mark.FaceIn.inRCone_of_add | exact GlobalTheory.PolFan.Mark.FaceIn.inRCone_of_add | (intros; apply GlobalTheory.PolFan.Mark.FaceIn.inRCone_of_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeCellOfLinearPieceThroughCellPointStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inRealCone_cell_of_linearPiece_through_cellPoint : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {m k : ℕ}
  (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin k → LinearMap.BilinForm ℤ X), IsCell bar φ γ → (∀ i, γ' i ∈ balForms bar X) →
  (∀ i y, 0 ≤ γ' i y y) → φ.LinearOn γ' →
  ∀ (β : LinearMap.BilinForm ℤ X) (a : Fin m → ℝ) (b : Fin k → ℝ), (∀ j, 0 ≤ a j) → (∀ i, 0 < b i) →
    toReal β = ∑ j, a j • toReal (γ j) → toReal β = ∑ i, b i • toReal (γ' i) → ∀ i, InRCone γ (γ' i) := by
  first | exact @GlobalTheory.PolFan.inRCone_of_interior_linearOn' | exact GlobalTheory.PolFan.inRCone_of_interior_linearOn' | (intros; apply GlobalTheory.PolFan.inRCone_of_interior_linearOn' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeGeneratorsOfLinFormEqZero
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem inRCone_of_apply_eq_zero {X : Type} [AddCommGroup X] {m p : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (e : Fin p ↪ Fin m) (β : LinearMap.BilinForm ℤ X) (hnn : ∀ i, 0 ≤ h (δ i))
    (hz : ∀ i, h (δ i) = 0 → i ∈ Set.range e) (hβ : InRCone δ β) (hβ0 : h β = 0) :
    InRCone (fun k => δ (e k)) β := by
  obtain ⟨c, hc, hsum⟩ := hβ
  have happ := apply_eq_of_toReal_eq hsum h
  rw [hβ0, Int.cast_zero] at happ
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin m)), c i * (h (δ i) : ℝ) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hc i) (by exact_mod_cast hnn i)).1 happ.symm
  have hvan : ∀ i, i ∉ Set.range e → c i = 0 := by
    intro i hi
    rcases mul_eq_zero.1 (hterm i (Finset.mem_univ i)) with h1 | h1
    · exact h1
    · exact absurd (hz i (by exact_mod_cast h1)) hi
  refine ⟨fun k => c (e k), fun k => hc (e k), ?_⟩
  rw [hsum, ← Finset.sum_map Finset.univ e (fun i => c i • toReal (δ i))]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have : i ∉ Set.range e := by
    rintro ⟨k, rfl⟩
    exact hi (Finset.mem_map_of_mem e (Finset.mem_univ k))
  rw [hvan i this, zero_smul]

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSummandsOfEvalZAdditiveCellStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inRealCone_summands_of_evalZ_additive_cell : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∀ (k : ℕ) (u : Fin k → LinearMap.BilinForm ℤ X), (∀ j, u j ∈ balForms bar X) → (∀ j y, 0 ≤ u j y y) → InRCone γ (∑ j, u j) → ψ.evalZ (∑ j, u j) ≤ ∑ j, ψ.evalZ (u j) → ∀ j, InRCone γ (u j) := by
  first | exact @GlobalTheory.PolFan.Mark.inRCone_of_evalZ_sum_le | exact GlobalTheory.PolFan.Mark.inRCone_of_evalZ_sum_le | (intros; apply GlobalTheory.PolFan.Mark.inRCone_of_evalZ_sum_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvFunEvalZAddOfLinearOnRealConeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invFun_evalZ_add_of_linearOn_realCone : ∀ (O : Type) [CommRing O] (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), ψ.LinearOn v → ∀ β x : LinearMap.BilinForm ℤ X, InRCone v β → InRCone v x → ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x := by
  first | exact @GlobalTheory.PolFan.Mark.evalZ_add_of_linearOn_inRCone | exact GlobalTheory.PolFan.Mark.evalZ_add_of_linearOn_inRCone | (intros; apply GlobalTheory.PolFan.Mark.evalZ_add_of_linearOn_inRCone <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAuxiliaryHeckeCharacterToricListOfGridStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lamOf_chi_is_chosen_hecke_character_of_placesOk : ∀ (D : D7) {T : Type} (L : Formalism.IndefR.Links.LevCh D T) (sc : GlobalTheory.ChiGrid.Consts) (G : GlobalTheory.ChiGrid.GridData L sc) (w0 : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.LamTie.PlacesOk D.host (AbsolutelyIrreducibleSpan.q0 D) w0 → ∀ a : Fin D.R.m, GlobalTheory.LamTie.IsAuxiliaryHeckeCharacter D.host (G.pl.w G.pl.v0) ((GlobalTheory.BigTop.Fun.lamOf G).c a) ((GlobalTheory.BigTop.Fun.lamOf G).chi a) := by
  first | exact @GlobalTheory.GridLambdaData.isAuxiliaryHeckeCharacter_toricListOfGrid | exact GlobalTheory.GridLambdaData.isAuxiliaryHeckeCharacter_toricListOfGrid | (intros; apply GlobalTheory.GridLambdaData.isAuxiliaryHeckeCharacter_toricListOfGrid <;> assumption)
end

