import Formalism.LocalToGlobal.CharacterGerms.Bundle0018
import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
import Formalism.LocalToGlobal.CharacterGerms.Bundle0016
import Formalism.LocalToGlobal.CharacterGerms.Bundle0013

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieCartAdd
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

section IntSec

variable {V : VF C} {τ : Type}

theorem IntS.mul {f g : MvPowerSeries τ C} (hf : IntS V f) (hg : IntS V g) : IntS V (f * g) := by
  intro μ
  rw [MvPowerSeries.coeff_mul]
  refine VF.Ge.sum fun p _ => ?_
  have hp := (hf p.1).mul (hg p.2)
  simpa using hp

theorem IntS.one : IntS V (1 : MvPowerSeries τ C) := by
  intro μ
  rw [MvPowerSeries.coeff_one]
  split_ifs
  all_goals simp [VF.Ge]

theorem IntS.pow {f : MvPowerSeries τ C} (hf : IntS V f) (n : ℕ) : IntS V (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact IntS.one
  | succ n ih => rw [pow_succ]; exact ih.mul hf

theorem IntS.subst {σ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ha : ∀ s, IntS V (a s)) {f : MvPowerSeries σ C}
    (hf : IntS V f) : IntS V (MvPowerSeries.subst a f) := by
  have hA : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  intro μ
  rw [MvPowerSeries.coeff_subst hA]
  have hterm : ∀ d : σ →₀ ℕ,
      V.Ge 0 (MvPowerSeries.coeff d f • MvPowerSeries.coeff μ (d.prod fun s e => a s ^ e)) := by
    intro d
    have hp : IntS V (d.prod fun s e => a s ^ e) := by
      show IntS V (∏ s ∈ d.support, a s ^ d s)
      exact Finset.prod_induction _ (fun p => IntS V p) (fun _ _ hx hy => IntS.mul hx hy) IntS.one
        (fun s _ => IntS.pow (ha s) _)
    have h2 := (hf d).mul (hp μ)
    simpa [smul_eq_mul] using h2
  by_cases hfin : (Function.support fun d : σ →₀ ℕ =>
      MvPowerSeries.coeff d f • MvPowerSeries.coeff μ (d.prod fun s e => a s ^ e)).Finite
  · rw [finsum_eq_sum _ hfin]
    exact VF.Ge.sum fun d _ => hterm d
  · rw [finsum_of_infinite_support hfin]
    simp [VF.Ge]

theorem intS_ps {f : PowerSeries C} : IntS V f ↔ ∀ n, V.Ge 0 (PowerSeries.coeff n f) := by
  constructor
  · intro h n
    exact h (Finsupp.single () n)
  · intro h μ
    have hμ : μ = Finsupp.single () (μ ()) := by
      ext
      simp [Finsupp.single_apply]
    rw [hμ]
    exact h (μ ())

end IntSec

section Kill

variable {dd : ℕ}

theorem subst_ev_kill (h : PS C 2 dd) (g : Fin 2) (a : Fin 2 → Pt C 1 dd) (hag : a g = 0)
    (hao : ∀ g', g' ≠ g → a g' = pt C dd 0) :
    MvPowerSeries.subst (fun q : Fin 1 × Fin dd => (MvPowerSeries.X (1 - g, q.2) : PS C 2 dd)) (ev a h) =
      MvPowerSeries.rescale (fun s : Fin 2 × Fin dd => if s.1 = g then (0 : C) else 1) h := by
  have hbS : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => (MvPowerSeries.X (1 - g, q.2) : PS C 2 dd)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => MvPowerSeries.constantCoeff_X _
  have haS : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin dd => a p.1 p.2) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro s
    by_cases hs : s.1 = g
    · rw [hs, hag]; simp
    · rw [hao _ hs]; exact MvPowerSeries.constantCoeff_X _
  unfold ev
  rw [MvPowerSeries.subst_comp_subst_apply haS hbS, MvPowerSeries.rescale_eq_subst]
  congr 1
  funext s
  by_cases hs : s.1 = g
  · have h1 : a s.1 s.2 = 0 := by rw [hs, hag]; rfl
    rw [h1, ← MvPowerSeries.coe_substAlgHom hbS, map_zero]
    simp [hs]
  · have h1 : a s.1 s.2 = MvPowerSeries.X ((0 : Fin 1), s.2) := by rw [hao _ hs]; rfl
    rw [h1, MvPowerSeries.subst_X hbS]
    have h2 : s = (1 - g, s.2) := Prod.ext (fin_two_eq_one_sub_of_ne' g s.1 hs) rfl
    simp only [Pi.smul_apply', if_neg hs, one_smul]
    rw [← h2]

theorem coeff_eval_second_zero (G : PS C 2 dd) (μ : Fin dd →₀ ℕ) :
    MvPowerSeries.coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (ev (n := 1) ![pt C dd 0, 0] G) =
      MvPowerSeries.coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 2), x)) G := by
  have hk := subst_ev_kill G 1 ![pt C dd 0, 0] rfl (by
    intro g' hg'
    rw [fin_two_eq_one_sub_of_ne' 1 g' hg']
    rfl)
  have hinj : Function.Injective (fun q : Fin 1 × Fin dd => (((1 : Fin 2) - 1, q.2) : Fin 2 × Fin dd)) :=
    fun a b h => snd_injective_fin_one (Prod.mk.inj (show (((1 : Fin 2) - 1, a.2) : Fin 2 × Fin dd) = ((1 : Fin 2) - 1, b.2) from h)).2
  have h1 := coeff_subst_rename_inj (C := C) (fun q : Fin 1 × Fin dd => (((1 : Fin 2) - 1, q.2) : Fin 2 × Fin dd)) hinj
    (ev (n := 1) ![pt C dd 0, 0] G) (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x))
  rw [hk, ← Finsupp.mapDomain_comp, MvPowerSeries.coeff_rescale] at h1
  rw [← h1]
  have h2 : ((fun q : Fin 1 × Fin dd => (((1 : Fin 2) - 1, q.2) : Fin 2 × Fin dd)) ∘ fun x : Fin dd => ((0 : Fin 1), x)) =
      fun x : Fin dd => ((0 : Fin 2), x) := by
    funext x
    rfl
  rw [h2]
  have h3 : ((μ.mapDomain fun x : Fin dd => ((0 : Fin 2), x)).prod
      fun s m => (if s.1 = 1 then (0 : C) else 1) ^ m) = 1 := by
    unfold Finsupp.prod
    apply Finset.prod_eq_one
    intro s hs
    have hs' := Finsupp.mapDomain_support hs
    rw [Finset.mem_image] at hs'
    obtain ⟨x, _, rfl⟩ := hs'
    show (if (0 : Fin 2) = 1 then (0 : C) else 1) ^ _ = 1
    rw [if_neg (by decide), one_pow]
  rw [h3, one_mul]

end Kill

section SgSec

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)] (Y : FBChart C V O dd) (p : PairData Y d I)

theorem FBChart.raw_sg (v : Fin dd → C) : (Y.raw p).sg v = un1 (Y.sgP v) := by
  ext μ
  show -∑ i, v i * MvPowerSeries.coeff (μ.mapDomain (fun x : Fin dd => ((0 : Fin 2), x)) +
      Finsupp.single ((1 : Fin 2), i) 1) Y.h =
    MvPowerSeries.coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.sgP v)
  simp only [FBChart.sgP, map_neg, map_sum, MvPowerSeries.coeff_C_mul, coeff_eval_second_zero]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [MvPowerSeries.coeff_pderiv, Finsupp.mapDomain_notin_range]
  · simp
  · rintro ⟨x, hx⟩
    simp at hx

end SgSec

section AddSec

variable {dd : ℕ}

theorem pts_eq_X : (fun p : Fin 2 × Fin dd => ![pt C (n := 2) dd 0, pt C (n := 2) dd 1] p.1 p.2) = MvPowerSeries.X := by
  funext p
  rcases p with ⟨i, j⟩
  fin_cases i <;> first | rfl | simp [pt]

theorem addOf_pts (F : Fin dd → PS C 2 dd) (j : Fin dd) :
    addOf F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) j = F j := by
  simp only [addOf, ev]
  rw [pts_eq_X, MvPowerSeries.subst_self]
  rfl

end AddSec

theorem addCvFB_of
    (hG : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
      (Y : FBChart C V O dd), GermISt Y) : AddCvFBSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p γ γ' hγ hγ'
  set ρ : Fin 2 × Fin dd → PowerSeries C := fun q => ![γ, γ'] q.1 q.2 with hρ
  have hρ0 : ∀ q, MvPowerSeries.constantCoeff (ρ q) = 0 := by
    rintro ⟨b, j⟩
    fin_cases b
    · exact (hγ j).1
    · exact (hγ' j).1
  have hρI : ∀ q, IntS V (ρ q) := by
    rintro ⟨b, j⟩
    fin_cases b
    · exact intS_ps.2 (hγ j).2
    · exact intS_ps.2 (hγ' j).2
  have hρS := MvPowerSeries.hasSubst_of_constantCoeff_zero hρ0
  set γ'' : Fin dd → PowerSeries C := fun j => MvPowerSeries.subst ρ (Y.B.G.F j) with hγ''
  have hγ''0 : ∀ j, MvPowerSeries.constantCoeff (γ'' j) = 0 := fun j =>
    constantCoeff_subst_zero hρ0 (Y.B.G.const j)
  have hγ''I : IsCv V γ'' := fun j => ⟨hγ''0 j, intS_ps.1 (IntS.subst hρ0 hρI (Y.intF j))⟩

  have hev : ∀ (a : Pt C 2 dd), (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → ∀ f : PS C 1 dd,
      MvPowerSeries.subst ρ (ev ![a] f) = alongCv (fun j => MvPowerSeries.subst ρ (a j)) (un1 f) := by
    intro a ha f
    unfold alongCv
    rw [eval_single_eq_subst, MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 1 × Fin dd => ha q.2) hρS,
      subst_singlePointUncurry (fun j => constantCoeff_subst_zero hρ0 (ha j))]
  have hp0 : (fun j => MvPowerSeries.subst ρ (pt C (n := 2) dd 0 j)) = γ := by
    funext j
    show MvPowerSeries.subst ρ (MvPowerSeries.X ((0 : Fin 2), j)) = γ j
    rw [MvPowerSeries.subst_X hρS]
    rfl
  have hp1 : (fun j => MvPowerSeries.subst ρ (pt C (n := 2) dd 1 j)) = γ' := by
    funext j
    show MvPowerSeries.subst ρ (MvPowerSeries.X ((1 : Fin 2), j)) = γ' j
    rw [MvPowerSeries.subst_X hρS]
    rfl
  have hpa : (fun j => MvPowerSeries.subst ρ (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) j)) = γ'' := by
    funext j
    rw [addOf_pts]
  have hc0 : ∀ j, MvPowerSeries.constantCoeff (pt C (n := 2) dd 0 j) = 0 := fun j => MvPowerSeries.constantCoeff_X _
  have hc1 : ∀ j, MvPowerSeries.constantCoeff (pt C (n := 2) dd 1 j) = 0 := fun j => MvPowerSeries.constantCoeff_X _
  have hca : ∀ j, MvPowerSeries.constantCoeff (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) j) = 0 :=
    fun j => by rw [addOf_pts]; exact Y.B.G.const j
  refine ⟨γ'', hγ''I, ?_, ?_⟩
  · intro i
    have h := congrArg (MvPowerSeries.subst ρ) (Y.lg_add i)
    rw [← MvPowerSeries.coe_substAlgHom hρS, map_add, MvPowerSeries.coe_substAlgHom hρS, hev _ hca, hev _ hc0,
      hev _ hc1, hpa, hp0, hp1] at h
    exact h
  · intro v hv
    have hsg0 : MvPowerSeries.constantCoeff ((Y.raw p).sg v) = 0 := (Y.raw p).constantCoeff_sg (Y.raw_axis0 p) v
    refine ⟨?_, ?_⟩
    · rw [map_sub, map_sub]
      have e1 : PowerSeries.constantCoeff (alongCv γ'' ((Y.raw p).sg v)) = 0 := constantCoeff_subst_zero hγ''0 hsg0
      have e2 : PowerSeries.constantCoeff (alongCv γ ((Y.raw p).sg v)) = 0 :=
        constantCoeff_subst_zero (fun i => (hγ i).1) hsg0
      have e3 : PowerSeries.constantCoeff (alongCv γ' ((Y.raw p).sg v)) = 0 :=
        constantCoeff_subst_zero (fun i => (hγ' i).1) hsg0
      rw [e1, e2, e3]
      simp
    · have h := IntS.subst hρ0 hρI (hG C V O dd Y v hv)
      rw [← MvPowerSeries.coe_substAlgHom hρS, map_sub, map_sub, MvPowerSeries.coe_substAlgHom hρS, hev _ hca,
        hev _ hc0, hev _ hc1, hpa, hp0, hp1, ← Y.raw_sg p v] at h
      exact intS_ps.1 h

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieMemC
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj

abbrev IIs {T Orb : Type} (r : T → ℕ) (tau : Orb → ZMod 2 → T) (o : Orb) : Type := Σ t : ZMod 2, Fin (r (tau o t))

def subG {C : Type} [Field C] {T Orb : Type} (r : T → ℕ) (tau : Orb → ZMod 2 → T)
    (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n) :
    MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C →ₐ[C] MvPolynomial (Letter T r n) C :=
  MvPolynomial.aeval fun x => ∑ col : Fin 2, MvPolynomial.C (gm x.2.1 x.2.2.2.1 col x.2.2.1) *
    MvPolynomial.X (⟨tau x.2.1 x.2.2.2.1, x.2.2.2.2, plc (x.1, col)⟩ : Letter T r n)

def WtTieC {T Orb : Type} (r : T → ℕ) (tau : Orb → ZMod 2 → T) (gaC : Orb → ZMod 2 → ℕ → ℕ) (a : T → ℕ → ℕ) : Prop :=
  (∀ o s (i : ℕ), i < r (tau o s) → a (tau o s) i = ∑ k ∈ Finset.Icc (i + 1) (r (tau o s)), gaC o s k) ∧
  ∀ σ, (∀ o s, tau o s ≠ σ) → ∀ i, i < r σ → a σ i = 0

structure SelfConjugatePlaceSetting {C : Type} [Field C] {V : VF C} {T : Type} (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    {Orb : Type} [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
    {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (gaC : Orb → ZMod 2 → ℕ → ℕ) (N : ℕ) (L : Orb → List (GlobalTheory 2 × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N) : Prop where

  inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2
  conj : ∀ o t, cc (tau o t) = tau o (t + 1)

  gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1

  hty : ∀ o g (x : IIs r tau o), ((X o).G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + 1
  std : ∀ o g t (c : Fin ((X o).rkF g t)), ((F o).en g t c).2.val = c.val

  alt : ∀ o, (X o).Alt
  hj : ∀ o, (X o).j' < (X o).n
  supp : ∀ o s k, gaC o s k ≠ 0 → 1 ≤ k ∧ k ≤ (X o).rkF 0 s

  mon : ∀ o, ∀ q ∈ L o, ∀ g e M, q.1 = GlobalTheory.mon g e M → ∃ s : ZMod 2, ∀ b k, b ≠ s → e b k = 0
  wt : ∀ o s k, ((L o).map fun q => q.1.wt (X o) 0 s k + q.1.wt (X o) 1 (s + 1) k).sum = gaC o s k
  tie : WtTieC r tau gaC a
  plinj : Function.Injective pl

def IsotropicToStdSubstHarmonic : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
    (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (gaC : Orb → ZMod 2 → ℕ → ℕ) (N : ℕ) (L : Orb → List (GlobalTheory 2 × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N),
    SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl → ∀ (n : ℕ) (plc : Fin N × Fin 2 ↪ Fin n) (isX : T → Prop),
      subG r tau gm plc (blkProd X F N L pl) ∈ harmK r n C cc isX (fun _ => 1)

def IsotropicToStdSubstLineInvariant : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
    (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (gaC : Orb → ZMod 2 → ℕ → ℕ) (N : ℕ) (L : Orb → List (GlobalTheory 2 × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N),
    SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl → ∀ (n : ℕ) (plc : Fin N × Fin 2 ↪ Fin n),
      RowInv r n C (subG r tau gm plc (blkProd X F N L pl))

def IsotropicToStdSubstLineDegree : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
    (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (gaC : Orb → ZMod 2 → ℕ → ℕ) (N : ℕ) (L : Orb → List (GlobalTheory 2 × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N),
    SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl → ∀ (n : ℕ) (plc : Fin N × Fin 2 ↪ Fin n),
      RowDeg r n C a (subG r tau gm plc (blkProd X F N L pl))

def IsotropicToStdSubstIntegral : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (T : Type) (r : T → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
    (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (N : ℕ) (L : Orb → List (GlobalTheory 2 × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N) (n : ℕ) (plc : Fin N × Fin 2 ↪ Fin n)
    (O : Subring C), (∀ o t q s, gm o t q s ∈ O) → ∀ m, (subG r tau gm plc (blkProd X F N L pl)).coeff m ∈ O

section Mem

variable {C : Type} [Field C] {V : VF C} {T : Type} (r : T → ℕ) (cc : T → T) (isX : T → Prop)
  (a : T → ℕ → ℕ) {Orb : Type} [Fintype Orb] (tau : Orb → ZMod 2 → T) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
  (O : Subring C) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

def selfConjTuplesInLattice : Set (∀ o, MvPolynomial (Fin N × WV fun _ => IIs r tau o) C) :=
  {Po | subG r tau gm plc (∏ o, toAll o (Po o)) ∈ HaO r n C O cc isX a}

variable {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]

theorem block_membership_self_conj_first (h1 : IsotropicToStdSubstHarmonic) (h2 : IsotropicToStdSubstLineInvariant) (h3 : IsotropicToStdSubstLineDegree) (h4 : IsotropicToStdSubstIntegral)
    (X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o)) (gaC : Orb → ZMod 2 → ℕ → ℕ)
    (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) (conj : ∀ o t, cc (tau o t) = tau o (t + 1))
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (gm_int : ∀ o t q s, gm o t q s ∈ O)
    (hty : ∀ o g (x : IIs r tau o), ((X o).G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + 1)
    (std : ∀ o g t (c : Fin ((X o).rkF g t)), ((F o).en g t c).2.val = c.val)
    (alt : ∀ o, (X o).Alt) (hj : ∀ o, (X o).j' < (X o).n)
    (supp : ∀ o s k, gaC o s k ≠ 0 → 1 ≤ k ∧ k ≤ (X o).rkF 0 s) (tie : WtTieC r tau gaC a) :
    BlockMembershipSelfConjugate X N F (selfConjTuplesInLattice r cc isX a tau gm O plc) gaC := by
  intro L mon wt pl plinj
  have H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl := ⟨inj, conj, gm_hyp, hty, std, alt, hj, supp, mon, wt, tie, plinj⟩
  exact ⟨⟨h1 C V T r cc a Orb tau gm J X F gaC N L pl H n plc isX, h2 C V T r cc a Orb tau gm J X F gaC N L pl H n plc,
    h3 C V T r cc a Orb tau gm J X F gaC N L pl H n plc⟩, h4 C V T r Orb tau gm J X F N L pl n plc O gm_int⟩

end Mem

def OP {C : Type} [Field C] (O : Subring C) (σ : Type) : Subring (MvPolynomial σ C) :=
  (MvPolynomial.map O.subtype).range

theorem coeff_mem_of_OP {C : Type} [Field C] {O : Subring C} {σ : Type} {P : MvPolynomial σ C} (h : P ∈ OP O σ)
    (m : σ →₀ ℕ) : P.coeff m ∈ O := by
  obtain ⟨Q, rfl⟩ := RingHom.mem_range.1 h
  rw [MvPolynomial.coeff_map]
  exact (Q.coeff m).2

theorem aeval_mem_OP {C : Type} [Field C] {O : Subring C} {σ τ : Type} (f : σ → MvPolynomial τ C)
    (hf : ∀ x, f x ∈ OP O τ) {P : MvPolynomial σ C} (h : P ∈ ZP C σ) : MvPolynomial.aeval f P ∈ OP O τ := by
  obtain ⟨Q, rfl⟩ := RingHom.mem_range.1 h
  clear h
  induction Q using MvPolynomial.induction_on
  · rename_i z
    rw [MvPolynomial.map_C, MvPolynomial.aeval_C, eq_intCast (Int.castRingHom C) z, map_intCast]
    exact intCast_mem _ z
  · rename_i p q hp hq
    rw [map_add, map_add]
    exact add_mem hp hq
  · rename_i p x hp
    rw [map_mul, map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X]
    exact mul_mem hp (hf x)

theorem first_chern_integral : IsotropicToStdSubstIntegral := by
  intro C _ V T r Orb _ tau gm J _ X F N L pl n plc O hO m
  apply coeff_mem_of_OP
  unfold subG
  refine aeval_mem_OP _ (fun x => ?_) (blkProd_mem_ZP X F N L pl)
  refine sum_mem fun col _ => mul_mem ?_ ?_
  · exact RingHom.mem_range.2 ⟨MvPolynomial.C ⟨_, hO _ _ _ _⟩, by rw [MvPolynomial.map_C]; rfl⟩
  · exact RingHom.mem_range.2 ⟨MvPolynomial.X _, MvPolynomial.map_X _ _⟩

end Formalism.L2.FormalSeriesBounds.RF
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieSelfCuts
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

section Core

variable {Orb : Type} {d : ℕ} [NeZero d]

structure LabSGeoCore (C3 : IntChart T io y) (ι : T.Fr →+* C) (Y : FBChart C V (𝓞 E) (chD C3.ch))
    (lab : LabS E C Orb d) : Prop where
  e_eig : ∀ o (x : lab.II Dw o) a, linAct (Y.B.A.act a) (selfLieBasisVector C3 ι lab o x) =
    emA3 io ι (lab.tau o x.1) a • selfLieBasisVector C3 ι lab o x
  e_sat : ∀ o, ∃ w : Fin (chD C3.ch) → lab.II Dw o → C, (∀ x q, V.Ge 0 (w x q)) ∧
    ∀ q q' : lab.II Dw o, ∑ x, selfLieBasisVector C3 ι lab o q x * w x q' = if q = q' then 1 else 0
  e_full : ∀ o a (v : Fin (chD C3.ch) → C), (∀ x, linAct (Y.B.A.act x) v = emA3 io ι (lab.tau o a) x • v) →
    ∃ b : lab.II Dw o → C, (∀ q, q.1 ≠ a → b q = 0) ∧ v = ∑ q, b q • selfLieBasisVector C3 ι lab o q

theorem labSGeo_of (hstar : ∀ a : 𝓞 E, star a = H.bar a) {C3 : IntChart T io y} {ι : T.Fr →+* C} (hι : EmbOK T V ι)
    {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb d} (ha : LabSArith V io ι lab)
    (h : LabSGeoCore C3 ι Y lab) : LabSGeo C3 ι Y lab where
  em_int := fun _ _ x => embedding_integral ι _ x
  em_conj := fun o a x => by rw [← ha.conj o a]; exact (embedding_conjugate hstar ι _ x).symm
  e_int := fun _ _ i => a3uvec_int C3 hι _ i
  e_eig := h.e_eig
  e_sat := h.e_sat
  e_full := h.e_full

end Core

def RankMaximalSelfOfNondegenerate : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0),
    NDG Y → (Y.rawSelf p).RankHyp → ∀ Hc : ∀ g, (Y.rawSelf p).CartHyp V g, RawChart.RankMaximalCondition Hc

variable (Xo c)

def LabSGeoCoreSt : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : LabS E C Orb d), LabSArith V io ι lab → LabSGeoCore C3 ι Y lab

theorem labSGeo_of_core (h : LabSGeoCoreSt Xo c) : LabSGeoSt Xo c :=
  fun hstar T io y C3 C _ _ V ι hι k Y hY Orb d _ lab ha =>
    labSGeo_of hstar hι ha (h hstar T io y C3 C V ι hι k Y hY Orb d lab ha)

theorem rank_maximal_self_charts_of_nondegenerate (h1 : RankMaximalSelfOfNondegenerate) (h2 : NondegenerateCharts Xo c) : RankMaximalSelfCharts Xo c :=
  fun hstar T io y C3 C _ _ V ι hι k Y hY _ d _ _ ha hg hr o Hc =>
    h1 C V (𝓞 E) _ Y d _ (selfOfLab ha hg o) (h2 hstar T io y C3 C V ι hι k Y hY) (rankHyp_ofLabS ha hg hr o) Hc

def HodgeTatePackSelfCharts : Prop := AllSelfConjugateCharts Xo c fun _ _ V _ _ _ _ X => ∀ Hc : ∀ g, X.CartHyp V g, RawChart.HTDPack Hc

end Formalism.L2.FormalSeriesBounds
end
end

