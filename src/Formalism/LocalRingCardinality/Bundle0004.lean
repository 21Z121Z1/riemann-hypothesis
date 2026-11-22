import Formalism.LocalRingCardinality.Bundle0003
import Formalism.LocalRingCardinality.DataLatDefs
import Formalism.LocalRingCardinality.DataForced
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.PrincipalHermitianLattice

-- bundled from Formalism.LocalRingCardinality.DataErr
section
noncomputable section

namespace Formalism.BasicNotions

open Formalism.FrobeniusOrbits Formalism.MainNotions.G NumberField IsDedekindDomain
open scoped BigOperators

structure ErrC where
  c6 : ℝ
  dig : ℝ
  g : ℝ

def ErrC.Large (c : ErrC) : Prop := 12 ≤ c.c6 ∧ 3 ≤ c.dig ∧ 10 ≤ c.g

structure ErrX (D : D7) where

  piG : Fin 2 → 𝓞 D.host.E
  piG_K : ∀ i, ((piG i : 𝓞 D.host.E) : D.host.E) ∈ D.host.K
  piG_norm : ∀ i, ((piG i : 𝓞 D.host.E) : D.host.E) * D.host.conj (piG i : D.host.E) = (D.host.g i : D.host.E)

  piT : D.what₂.Word → 𝓞 D.host.E
  piT_K : ∀ u, ((piT u : 𝓞 D.host.E) : D.host.E) ∈ D.host.K
  piT_norm : ∀ u, ((piT u : 𝓞 D.host.E) : D.host.E) * D.host.conj (piT u : D.host.E) = ((D.mem u).A.T : D.host.E)
  piT_cong : ∀ u, (piT u - 1) ∈
    Ideal.span {((D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : 𝓞 D.host.E)}

  vPl : ∀ u, (D.mem u).A.vT → HeightOneSpectrum (𝓞 D.host.F)
  vPl_inj : ∀ u, Function.Injective (vPl u)
  norm_mem_place_ideal : ∀ u v, ((D.mem u).A.T : 𝓞 D.host.F) ∈ (vPl u v).asIdeal

def tauLL (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : D.what₂.LL :=
  D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) x)

open scoped TensorProduct in

def PiGLevel (D : D7) (lev : LevelData D) (X : ErrX D) : Prop :=
  letI := D.host.cmStar
  ∀ u (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal),
    Valued.v (((lev u).splitG i v h) ((D.host.conj (X.piG i : D.host.E)) ⊗ₜ[D.host.F] (1 : v.adicCompletion D.host.F))).1 < 1

open scoped TensorProduct in

def PiTLevel (D : D7) (lev : LevelData D) (X : ErrX D) : Prop :=
  letI := D.host.cmStar
  ∀ u (v : (D.mem u).A.vT) (z : intV D.host.E (X.vPl u v)),
    (z : D.host.E ⊗[D.host.F] (X.vPl u v).adicCompletion D.host.F) =
      ((X.piT u : 𝓞 D.host.E) : D.host.E) ⊗ₜ[D.host.F] (1 : (X.vPl u v).adicCompletion D.host.F) →
    ∀ y : (lev u).fM (X.vPl u v) (X.norm_mem_place_ideal u v), z • y = 0

open scoped TensorProduct in

theorem piT_mem_intV (D : D7) (X : ErrX D) (u : D.what₂.Word) (v : (D.mem u).A.vT) :
    ((X.piT u : 𝓞 D.host.E) : D.host.E) ⊗ₜ[D.host.F] (1 : (X.vPl u v).adicCompletion D.host.F) ∈
      intV D.host.E (X.vPl u v) :=
  Subring.subset_closure (Or.inl ⟨⟨_, ⟨X.piT u, rfl⟩⟩, rfl⟩)

def SeenDef (D : D7) (X : ErrX D) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T →
    ((D.fm u).seenP w = true ↔ ∀ τ : D.what₂.Tau, (0 : WithTop ℤ) < D.what₂.places.val w (tauLL D τ (X.piT u : D.host.E)))

def TauOfDef (D : D7) (X : ErrX D) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∀ (v : (D.mem u).A.vT) (x : 𝓞 D.host.F),
    x ∈ (X.vPl u v).asIdeal ↔
      (0 : WithTop ℤ) < D.what₂.places.val w (tauLL D ((D.fm u).tauOf w v) (algebraMap D.host.F D.host.E (x : D.host.F)))

def GamMult (D : D7) (n : ℕ) : Prop :=
  ∀ u μ i, i ≤ D.R.m → ∀ c : (D.chTw u μ).cls i, Nat.card ((D.chTw u μ).stab i c) ∣ n

def DGamDef (D : D7) : Prop :=
  ∀ u μ, GamMult D (D.chTw u μ).DGam ∧ (D.chTw u μ).DGam = (D.mem D.u₀).C.DGam

theorem DGamDef.one {D : D7} (h : DGamDef D) (u u' : D.what₂.Word) (μ : D.what₂.Tup) :
    (D.chTw u' μ).DGam = (D.mem u).C.DGam := by
  rw [← D.memberColumns_twistedChain_base u]
  exact (h u' μ).2.trans (h u D.what₂.mu0).2.symm

def nuAbs (D : D7) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) : ℝ :=
  ∑ i ∈ Finset.range (D.R.N (j - 1)), DV.nuRow D u j τ i

def tauPib {D : D7} (X : ErrX D) (i : Fin 2) (τ : D.what₂.Tau) : D.what₂.LL :=
  tauLL D τ (D.host.conj (X.piG i : D.host.E))

def vNN {D : D7} (X : ErrX D) (i : Fin 2) (u : D.what₂.Word) (j : ℕ) (w : D.what₂.places.Pl) : ℝ :=
  (∑ τ : D.what₂.Tau, nuAbs D u j τ * (vAdd (D.plEq w) (tauPib X i τ) : ℝ)) / (D.what₂.places.ramIdx w : ℝ)

def EatG {D : D7} (L : SizeData₂ D) (X : ErrX D) (c : ErrC) (i : Fin 2) (u : D.what₂.Word) (j : ℕ)
    (w : D.what₂.places.Pl) : ℝ :=
  FTypeG D j + vNN X i u j w +
    c.g * (D.R.f : ℝ) * (Nm D ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz)

open Classical in

def Wtau (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : ℕ :=
  (Finset.range (D.R.m + 1)).sup fun i => Finset.univ.sup fun a : Fin (D.R.N i) =>
    if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0
    else (((D.fm u).lam i τ).w a - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs

def EatT (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) : ℝ :=
  if (D.fm u).seenP w then
    2 * (∑ τ : D.what₂.Tau, (Wtau D u τ : ℝ)) + (D.R.f : ℝ) * Nm D +
      ((topsOf D.host D.eTau).card : ℝ) * ((D.R.t : ℝ) + 1) * ((D.R.m : ℝ) + 1) / 4
  else 0

open Classical in

def ctD (D : D7) (u : D.what₂.Word) (j : ℕ) (t : HH D) : ℝ :=
  nuAbs D u j (tauPl D (false, t)) -
    (if t ∈ D.host.TT then DV.nuRow D u j (tauPl D (false, t)) 0 - DV.nuRow D u j (tauPl D (false, t)) 1 else 0) +
    (if t ∈ D.host.TT then DV.nuRow D u j (tauPl D (true, t)) 0 else 0)

def EatD (D : D7) (j : ℕ) : ℝ :=
  FRamD D j + (Finset.univ.sup' ⟨D.u₀, Finset.mem_univ _⟩ fun u : D.what₂.Word => ∑ t : HH D, ctD D u j t) / 2

def exch (D : D7) : ℝ := (D.R.f : ℝ) * D.R.k * Nm D

def EatC {D : D7} (L : SizeData₂ D) (c : ErrC) (j p : ℕ) : ℝ :=
  c.dig * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a +
    (∑ τ : D.what₂.Tau, wj D j τ) / ((p : ℝ) ^ 2 - 1)

open Classical in

def kindA (D : D7) (p : ℕ) : Finset (Bool × HH D) := Finset.univ.filter fun z => ¬ IsSg D p ∧ z.1 = false

open Classical in

def kindBC (D : D7) (p : ℕ) : Finset (Bool × HH D) := Finset.univ.filter fun z => IsSg D p ∨ z.1 = true

open Classical in

def topsBC (D : D7) (p : ℕ) : Finset (Bool × HH D) := (kindBC D p).filter fun z => IsTopPl D z

open Classical in

def EatX {D : D7} (L : SizeData₂ D) (c : ErrC) (j p : ℕ) : ℝ :=
  if IsCs D p then
    ((D.R.k : ℝ) - 1) * (∑ z ∈ kindBC D p, wPl D j z) / (p : ℝ) ^ 3 +
      c.c6 * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a
  else 0

theorem EatX_of_not {D : D7} (L : SizeData₂ D) (c : ErrC) (j : ℕ) {p : ℕ} (h : ¬ IsCs D p) : EatX L c j p = 0 := if_neg h

def EatI {D : D7} (L : SizeData₂ D) (K : Consts) (c : ErrC) (j p : ℕ) : ℝ :=
  max 0 ((∑ z ∈ kindA D p, FOrb D j p z) / (nP D p : ℝ)) +
    gam p * ((topsBC D p).card : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) +
    c.c6 * (∑ z ∈ kindBC D p, wPl D j z) / (p : ℝ) +
    ((kindBC D p).card : ℝ) * (D.R.N (j - 1) : ℝ) * (D.R.N j : ℝ) *
      (Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) + 1) +
    (K.dl1 * ((kindBC D p).card : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) +
      K.dl2 * ((topsBC D p).card : ℝ) * Real.logb p (2 * L.sc.a) ^ 2) +
    EatX L c j p

open Classical in

def Eval {D : D7} (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) (u : D.what₂.Word) (j : ℕ)
    (w : D.what₂.places.Pl) : ℝ :=
  let p := D.what₂.places.resChar w
  if p = (D.mem u).A.T then EatT D u w else
  (padicValNat p (D.mem u).C.DGam : ℝ) +
    (if p = D.host.g 0 then EatG L X c 0 u j w
     else if p = D.host.g 1 then EatG L X c 1 u j w
     else if D.host.cls p = PrimeClass.ramD then EatD D j
     else if (IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n then
       (if IsResidueClassZero D p ∧ hP D p = 0 then EatC L c j p else EatI L K c j p)
     else 0)

def SizeData₂.EDef {D : D7} (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) : Prop :=
  ∀ u, ∀ j ∈ SizeData₂.lifts D, ∀ w, L.E u j w = Eval L X K c u j w

theorem Eval_above {D : D7} (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) (u : D.what₂.Word) (j : ℕ)
    (w : D.what₂.places.Pl) (hX : L.sc.X'' D.R.n < (D.what₂.places.resChar w : ℝ))
    (hT : D.what₂.places.resChar w ≠ (D.mem u).A.T)
    (hg : D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ))
    (hd : D.what₂.places.resChar w ≠ D.host.d) (hG : ¬ D.what₂.places.resChar w ∣ (D.mem u).C.DGam) :
    Eval L X K c u j w = 0 := by
  have h0 : D.what₂.places.resChar w ≠ D.host.g 0 := fun h => hg (by simp [h])
  have h1 : D.what₂.places.resChar w ≠ D.host.g 1 := fun h => hg (by simp [h])
  have h2 : D.host.cls (D.what₂.places.resChar w) ≠ PrimeClass.ramD := fun h => hd (cls_ramD h)
  have h3 : ¬ ((IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w)) ∧
      (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n) := fun h => absurd h.2 (not_le.2 hX)
  unfold Eval
  simp only [if_neg h0, if_neg h1, if_neg hT, if_neg h2, if_neg h3, padicValNat.eq_zero_of_not_dvd hG]
  simp

def SizeData₂.withEval {D : D7} (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC)
    (hs : ∀ u j w, w ∉ L.supp → Eval L X K c u j w = 0) : SizeData₂ D :=
  { L with
    E := fun u j w => Eval L X K c u j w
    E_supp := hs }

theorem SizeData₂.withEval_EDef {D : D7} (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC)
    (hs : ∀ u j w, w ∉ L.supp → Eval L X K c u j w = 0) : (L.withEval X K c hs).EDef X K c :=
  fun _ _ _ _ => rfl

theorem SizeData₂.EDef.zeroAbove {D : D7} {L : SizeData₂ D} {X : ErrX D} {K : Consts} {c : ErrC} (h : L.EDef X K c)
    (u : D.what₂.Word) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (w : D.what₂.places.Pl)
    (hX : L.sc.X'' D.R.n < (D.what₂.places.resChar w : ℝ)) (hT : D.what₂.places.resChar w ≠ (D.mem u).A.T)
    (hg : D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ))
    (hd : D.what₂.places.resChar w ≠ D.host.d) (hG : ¬ D.what₂.places.resChar w ∣ (D.mem u).C.DGam) :
    L.E u j w = 0 := by
  rw [h u j hj w]; exact Eval_above L X K c u j w hX hT hg hd hG

structure ErrDefs (D : D7) (L : SizeData₂ D) (X : ErrX D) (lev : LevelData D) (K : Consts) (c : ErrC) : Prop where
  large : c.Large
  piG_lev : PiGLevel D lev X
  piT_lev : PiTLevel D lev X
  seen : SeenDef D X
  tauOf : TauOfDef D X
  dgam : DGamDef D
  edef : L.EDef X K c

end Formalism.BasicNotions

end
end

-- bundled from Formalism.LocalRingCardinality.DataKap
section
noncomputable section

namespace Formalism.BasicNotions

open scoped BigOperators

namespace DV

def eQ (D : D7) (j : ℕ) (τ : D.what₂.Tau) : ℚ :=
  if h : 1 ≤ j ∧ j ≤ D.R.m then (D.hc τ).e ⟨j - 1, by omega⟩ else 0

def sigPar (D : D7) (τ : D.what₂.Tau) (i : ℕ) : ℚ :=
  if h : i < D.R.k - 1 then (D.hc τ).v ⟨i, h⟩
  else if hb : i - (D.R.k - 1) < D.R.m then -(D.hc τ).b ⟨i - (D.R.k - 1), hb⟩ else 0

def aPlusQ (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℚ :=
  sigPar D τ i + eQ D j τ - ((D.R.nV : ℚ) - 1 - 2 * (i : ℚ)) / 2 -
    (((D.R.k : ℚ) + j - 1) - ((D.R.m : ℚ) - j)) / 2

def aMinusQ (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c : ℕ) : ℚ :=
  (if h : j + c < D.R.m then (D.hc τ).b ⟨j + c, h⟩ else 0) - eQ D j τ - ((D.R.t : ℚ) + 1 + 2 * (c : ℚ)) / 2

def aPlus (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℝ := ((aPlusQ D j τ i : ℚ) : ℝ)

def aMinus (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c : ℕ) : ℝ := ((aMinusQ D j τ c : ℚ) : ℝ)

def KapDef (D : D7) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ,
    (∀ i : Fin (D.R.sigW j).1, (D.what₂.kaBig j τ i : ℚ) = aPlusQ D j τ i) ∧
    (∀ c : Fin (D.R.sigW j).2, (D.what₂.kaSmall j τ c : ℚ) = -aMinusQ D j τ c)

theorem eQ_cast (D : D7) (j : ℕ) (τ : D.what₂.Tau) : ((eQ D j τ : ℚ) : ℝ) = wSz D j τ := by
  unfold eQ wSz
  split_ifs <;> simp

theorem eQ_int (D : D7) (j : ℕ) (τ : D.what₂.Tau) : ∃ z : ℤ, eQ D j τ = z := by
  unfold eQ
  split_ifs
  · exact (D.hc τ).e_int _
  · exact ⟨0, by simp⟩

theorem sigPar_int (D : D7) (τ : D.what₂.Tau) (i : ℕ) : ∃ z : ℤ, sigPar D τ i = z := by
  unfold sigPar
  split_ifs
  · exact (D.hc τ).v_int _
  · obtain ⟨z, hz⟩ := (D.hc τ).b_int ⟨i - (D.R.k - 1), by assumption⟩
    exact ⟨-z, by rw [hz]; simp⟩
  · exact ⟨0, by simp⟩

theorem nV_cast (R : Ranks) : (R.nV : ℚ) = (R.k : ℚ) + R.m - 1 + R.t := by
  have h : 1 ≤ R.k + R.m := by have := R.two_le_m; omega
  unfold Ranks.nV Ranks.r
  push_cast [Nat.cast_sub h]
  ring

theorem aPlusQ_eq (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) :
    aPlusQ D j τ i = sigPar D τ i + eQ D j τ - ((D.R.k : ℚ) + j - 1 - 1 - i) - ((D.R.t : ℚ) + 1) / 2 := by
  unfold aPlusQ
  rw [nV_cast]
  ring

theorem aPlusQ_int (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ∃ z : ℤ, aPlusQ D j τ i = z := by
  obtain ⟨a, ha⟩ := sigPar_int D τ i
  obtain ⟨b, hb⟩ := eQ_int D j τ
  obtain ⟨s, hs⟩ := D.R.t_odd
  refine ⟨a + b - ((D.R.k : ℤ) + j - 1 - 1 - i) - (s + 1), ?_⟩
  rw [aPlusQ_eq, ha, hb, hs]
  push_cast
  ring

theorem aMinusQ_int (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c : ℕ) : ∃ z : ℤ, aMinusQ D j τ c = z := by
  obtain ⟨b, hb⟩ := eQ_int D j τ
  obtain ⟨s, hs⟩ := D.R.t_odd
  have h1 : ∃ a : ℤ, (if h : j + c < D.R.m then (D.hc τ).b ⟨j + c, h⟩ else 0) = (a : ℚ) := by
    split_ifs
    · exact (D.hc τ).b_int _
    · exact ⟨0, by simp⟩
  obtain ⟨a, ha⟩ := h1
  refine ⟨a - b - (s + 1 + c), ?_⟩
  unfold aMinusQ
  rw [ha, hb, hs]
  push_cast
  ring

theorem aPlusQ_last (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) :
    1 ≤ aPlusQ D j τ (D.R.k + j - 1 - 1) := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hi : ¬ (D.R.k + j - 1 - 1 < D.R.k - 1) := by omega
  have hb : D.R.k + j - 1 - 1 - (D.R.k - 1) < D.R.m := by omega
  have hidx : D.R.k + j - 1 - 1 - (D.R.k - 1) = j - 1 := by omega
  have hc : ((D.R.k + j - 1 - 1 : ℕ) : ℚ) = (D.R.k : ℚ) + j - 1 - 1 := by
    have : D.R.k + j - 1 - 1 = D.R.k + j - 2 := by omega
    rw [this, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hg := (D.hc τ).gap_be ⟨j - 1, by omega⟩
  rw [aPlusQ_eq, hc]
  unfold sigPar eQ
  rw [dif_neg hi, dif_pos hb, dif_pos ⟨h1, h2⟩]
  have : (⟨D.R.k + j - 1 - 1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨j - 1, by omega⟩ := Fin.ext hidx
  rw [this]
  linarith

theorem aMinusQ_last (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j < D.R.m) (τ : D.what₂.Tau) :
    1 ≤ aMinusQ D j τ 0 := by
  have hg := (D.hc τ).gap_eb ⟨j - 1, by omega⟩ (by show j - 1 + 1 < D.R.m; omega)
  have hidx : (⟨j - 1 + 1, by omega⟩ : Fin D.R.m) = ⟨j + 0, by omega⟩ := Fin.ext (by show j - 1 + 1 = j + 0; omega)
  unfold aMinusQ eQ
  rw [dif_pos (by omega : j + 0 < D.R.m), dif_pos ⟨h1, h2.le⟩]
  rw [hidx] at hg
  push_cast
  linarith

theorem exists_blocks (D : D7) :
    ∃ (kb : ∀ j, D.what₂.Tau → Fin (D.R.sigW j).1 → ℤ) (ks : ∀ j, D.what₂.Tau → Fin (D.R.sigW j).2 → ℤ),
      ∀ j τ, (∀ i, (kb j τ i : ℚ) = aPlusQ D j τ i) ∧ (∀ c, (ks j τ c : ℚ) = -aMinusQ D j τ c) :=
  ⟨fun j τ i => (aPlusQ_int D j τ i).choose, fun j τ c => -(aMinusQ_int D j τ c).choose,
    fun j τ => ⟨fun i => (aPlusQ_int D j τ i).choose_spec.symm,
      fun c => by push_cast; rw [← (aMinusQ_int D j τ c).choose_spec]⟩⟩

def lamTr (D : D7) (μ : D.what₂.Tup) (j : ℕ) (π : D.what₂.FT) : ℝ :=
  (LinearMap.trace ℂ (D.what₂.Mj j)
    (D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j ∘ₗ ((D.what₂.isot j π).starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j))).re /
    (Module.finrank ℂ (D.what₂.isot j π) : ℝ)

def LamDef (D : D7) : Prop :=
  ∀ μ j, 1 ≤ j → j ≤ D.R.m → ∀ π, D.what₂.isot j π ≠ ⊥ → D.what₂.lamP μ j π = lamTr D μ j π

def LamScalar (D : D7) : Prop :=
  ∀ μ j, 1 ≤ j → j ≤ D.R.m → ∀ π, ∃ c : ℝ, ∀ x ∈ D.what₂.isot j π, D.what₂.thetaP μ j (D.what₂.thetaT μ j x) = (c : ℂ) • x

theorem lamTr_of_scalar (D : D7) (μ : D.what₂.Tup) (j : ℕ) (π : D.what₂.FT) (c : ℝ) (h0 : D.what₂.isot j π ≠ ⊥)
    (hc : ∀ x ∈ D.what₂.isot j π, D.what₂.thetaP μ j (D.what₂.thetaT μ j x) = (c : ℂ) • x) : lamTr D μ j π = c := by
  set W := D.what₂.isot j π with hW
  have hP : LinearMap.IsProj W (W.starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j) :=
    ⟨fun x => W.starProjection_apply_mem x, fun x hx => Submodule.starProjection_eq_self_iff.2 hx⟩
  have hT : D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j ∘ₗ (W.starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j) =
      (c : ℂ) • (W.starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j) := by
    ext y
    exact hc _ (W.starProjection_apply_mem y)
  have hf : (Module.finrank ℂ W : ℝ) ≠ 0 := by
    have : 0 < Module.finrank ℂ W := Module.finrank_pos_iff.2 (Submodule.nontrivial_iff_ne_bot.2 h0)
    exact_mod_cast this.ne'
  show (LinearMap.trace ℂ (D.what₂.Mj j) (D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j ∘ₗ
    (W.starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j))).re / (Module.finrank ℂ W : ℝ) = c
  rw [hT, map_smul, hP.trace, smul_eq_mul]
  have : ((c : ℂ) * ((Module.finrank ℂ W : ℕ) : ℂ)).re = c * (Module.finrank ℂ W : ℝ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [this, mul_div_assoc, div_self hf, mul_one]

def lamProd (D : D7) {n : ℕ} (ty : Fin n → D.what₂.FT) : ℝ :=
  ∏ σ, ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (ty σ)

end DV

namespace RowSide

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  [FiniteDimensional ℂ EE] (S : RowSide D EE)

def iiStar : EE →ₗ[ℂ] EE := S.iotaQ D.what₂.mu0 ∘ₗ LinearMap.adjoint (S.iotaQ D.what₂.mu0)

def kapRatio {n : ℕ} (ty : Fin n → D.what₂.FT) : ℝ := (LinearMap.det S.iiStar).re / DV.lamProd D ty

def kapOf {n : ℕ} (ty : Fin n → D.what₂.FT) : ℝ :=
  if 0 < S.kapRatio ty then S.kapRatio ty ^ ((n : ℝ)⁻¹) else 1

theorem kapOf_pos {n : ℕ} (ty : Fin n → D.what₂.FT) : 0 < S.kapOf ty := by
  unfold kapOf
  split_ifs with h
  · exact Real.rpow_pos_of_pos h _
  · exact one_pos

theorem RowLatticeBoundForBasis.kap_eq {S : RowSide D EE} {n : ℕ} {b : OrthonormalBasis (Fin n) ℂ EE} {ty : Fin n → D.what₂.FT} {kap : ℝ}
    (h : S.RowLatticeBoundForBasis b ty kap) (hn : 0 < n) : kap = S.kapOf ty := by
  obtain ⟨hbij, hk, ρ, hρ0, -, -, h⟩ := h
  set P : Fin n → ℝ := fun σ => ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (ty σ) with hPdef
  have hT : ∀ σ, S.iiStar (b σ) = ((kap * P σ : ℝ) : ℂ) • b σ := by
    intro σ
    have := h D.what₂.mu0 σ
    rw [hρ0, mul_one] at this
    exact this
  have hP : ∀ σ, P σ ≠ 0 := by
    intro σ h0
    have hz : S.iotaQ D.what₂.mu0 (LinearMap.adjoint (S.iotaQ D.what₂.mu0) (b σ)) = 0 := by
      have := hT σ
      rw [h0] at this
      simpa [iiStar] using this
    have h1 : LinearMap.adjoint (S.iotaQ D.what₂.mu0) (b σ) = 0 := by
      rw [← inner_self_eq_zero (𝕜 := ℂ), LinearMap.adjoint_inner_right, hz, inner_zero_left]
    obtain ⟨y, hy⟩ := (hbij D.what₂.mu0).2 (b σ)
    have h2 : inner ℂ (b σ) (b σ) = 0 := by
      nth_rewrite 1 [← hy]
      rw [← LinearMap.adjoint_inner_right, h1, inner_zero_right]
    have h3 : b σ = 0 := inner_self_eq_zero.1 h2
    have h4 := b.orthonormal.1 σ
    rw [h3, norm_zero] at h4
    exact zero_ne_one h4
  have hdet : LinearMap.det S.iiStar = ((kap ^ n * ∏ σ, P σ : ℝ) : ℂ) := by
    rw [← LinearMap.det_toMatrix b.toBasis]
    have hM : LinearMap.toMatrix b.toBasis b.toBasis S.iiStar =
        Matrix.diagonal (fun σ => ((kap * P σ : ℝ) : ℂ)) := by
      ext i j
      rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis, hT j, map_smul, Finsupp.smul_apply,
        ← OrthonormalBasis.coe_toBasis, Module.Basis.repr_self, Finsupp.single_apply, Matrix.diagonal_apply]
      by_cases hij : j = i
      · subst hij; simp
      · rw [if_neg hij, if_neg (fun h => hij h.symm)]; simp
    rw [hM, Matrix.det_diagonal, ← Complex.ofReal_prod, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hne : (∏ σ, P σ) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun σ _ => hP σ)
  have hr : S.kapRatio ty = kap ^ n := by
    unfold kapRatio DV.lamProd
    rw [hdet, Complex.ofReal_re]
    exact mul_div_cancel_right₀ _ hne
  unfold kapOf
  rw [hr, if_pos (pow_pos hk n), Real.pow_rpow_inv_natCast hk.le hn.ne']

end RowSide

def kapSharp (D : D7) : ℝ := (RowSide.sharp D).kapOf D.what₂.ft

def BaseLevelRowSide.kap0 {D : D7} (X : BaseLevelRowSide D) : ℝ := X.s.kapOf D.what₂.ft0

def DV.KapRBase {D : D7} (X : DivX D) : Prop := X.kapR D.what₂.embLL = kapSharp D

def SharpLatticeBoundForNumber (D : D7) : Prop := SharpLatticeBound D (kapSharp D)

def BaseLevelRowSide.BaseLevelSideLevelOneCondition {D : D7} (X : BaseLevelRowSide D) : Prop := X.L1c0 X.kap0

theorem SharpLatticeBound.iff_def {D : D7} (hn : 0 < D.what₂.Drows) : (∃ kap, SharpLatticeBound D kap) ↔ SharpLatticeBoundForNumber D :=
  ⟨fun ⟨_, h⟩ => by have := RowSide.RowLatticeBoundForBasis.kap_eq h hn; unfold SharpLatticeBoundForNumber kapSharp; rw [← this]; exact h, fun h => ⟨_, h⟩⟩

end Formalism.BasicNotions

end
end

