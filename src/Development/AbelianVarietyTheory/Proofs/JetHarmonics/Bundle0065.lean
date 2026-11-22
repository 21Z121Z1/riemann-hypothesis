import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinusHatsTaylorCoeffLeibnizRule
section
namespace GlobalTheory.HatNF.TaylorMinus

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

def Dg (L : LevelData A r) (Y : ℂ) (D : ℕ) (Z : ℂ → A) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (d : ι → ℕ) (x : ι → A), (∀ i, d i ≤ D) ∧
    (∀ s : ℂ, Z (Y - s) = ∑ i, s ^ d i • x i) ∧
    ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = ∑ i, m (q + d i) * x i

variable {L : LevelData A r} {Y : ℂ}

theorem Dg.mono {D E : ℕ} {Z : ℂ → A} (h : Dg L Y D Z) (hDE : D ≤ E) : Dg L Y E Z := by
  obtain ⟨ι, hι, d, x, hd, h1, h2⟩ := h
  exact ⟨ι, hι, d, x, fun i => (hd i).trans hDE, h1, h2⟩

theorem Dg.add {D : ℕ} {Z W : ℂ → A} (h : Dg L Y D Z) (h' : Dg L Y D W) :
    Dg L Y D (fun y => Z y + W y) := by
  obtain ⟨ι, _, d, x, hd, hs, hm⟩ := h
  obtain ⟨κ, _, e, w, he, hs', hm'⟩ := h'
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim d e, Sum.elim x w, ?_, fun s => ?_, fun m hmr q => ?_⟩
  · rintro (i | j)
    exacts [hd i, he j]
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hs, hs']
  · simp only [add_mul, hm m hmr q, hm' m hmr q, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

theorem Dg.mul {D E : ℕ} {Z W : ℂ → A} (h : Dg L Y D Z) (h' : Dg L Y E W) :
    Dg L Y (D + E) (fun y => Z y * W y) := by
  obtain ⟨ι, _, d, x, hd, hs, hm⟩ := h
  obtain ⟨κ, _, e, w, he, hs', hm'⟩ := h'
  refine ⟨ι × κ, inferInstance, fun p => d p.1 + e p.2, fun p => x p.1 * w p.2,
    fun p => Nat.add_le_add (hd p.1) (he p.2), fun s => ?_, fun m hmr q => ?_⟩
  · dsimp only
    rw [hs, hs', Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, pow_add]
  · dsimp only
    rw [mul_assoc, hm' m hmr q, Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, hm m hmr (q + e j), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, show q + e j + d i = q + (d i + e j) by omega]

theorem dg_const (f : A) (hf : ∀ m : ℕ → A, MulRel L m → ∀ q, Commute f (m q)) :
    Dg L Y 0 (fun _ => f) := ⟨Unit, inferInstance, fun _ => 0, fun _ => f, fun _ => le_rfl, fun s => by simp,
    fun m hm q => by simp [(hf m hm q).eq]⟩

theorem dg_lin (Z : ℂ → A) (u : A) (h1 : ∀ s, Z (Y - s) = Z Y + s • u)
    (h2 : ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = m q * Z Y + m (q + 1) * u) : Dg L Y 1 Z := ⟨Fin 2, inferInstance, ![0, 1], ![Z Y, u], by intro i; fin_cases i <;> simp,
    fun s => by simp [Fin.sum_univ_two, h1], fun m hm q => by simp [Fin.sum_univ_two, h2 m hm q]⟩

theorem Dg.out {D : ℕ} {Z : ℂ → A} (h : Dg L Y D Z) :
    ∃ X : ℕ → A, (∀ s : ℂ, Z (Y - s) = ∑ j ∈ Finset.range (D + 1), s ^ j • X j) ∧
      ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = ∑ j ∈ Finset.range (D + 1), m (q + j) * X j := by
  obtain ⟨ι, _, d, x, hd, h1, h2⟩ := h
  have hmap : ∀ i ∈ (Finset.univ : Finset ι), d i ∈ Finset.range (D + 1) :=
    fun i _ => Finset.mem_range.2 (Nat.lt_succ_of_le (hd i))
  refine ⟨fun j => ∑ i ∈ Finset.univ.filter (fun i => d i = j), x i, fun s => ?_, fun m hm q => ?_⟩
  · rw [h1, ← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  · rw [h2 m hm q, ← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]

theorem comm_c {m : ℕ → A} (hm : MulRel L m) (q : ℕ) (l : Fin r) : Commute (L.c l) (m q) := (hm q).1 _ (by simp [LevelData.fns])

theorem comm_cb {m : ℕ → A} (hm : MulRel L m) (q : ℕ) (l : Fin r) : Commute (L.cb l) (m q) := (hm q).1 _ (by simp [LevelData.fns])

theorem comm_cbi {m : ℕ → A} (hm : MulRel L m) (q : ℕ) (l : Fin r) : Commute (L.cbi l) (m q) := (hm q).1 _ (by simp [LevelData.fns])

theorem comm_GG {m : ℕ → A} (hm : MulRel L m) (q : ℕ) : Commute L.GG (m q) := (hm q).1 _ (by simp [LevelData.fns])

theorem comm_zG {m : ℕ → A} (hm : MulRel L m) (q : ℕ) : Commute (L.ζ * L.GGi) (m q) := ((hm q).1 _ (by simp [LevelData.fns])).mul_left ((hm q).1 _ (by simp [LevelData.fns]))

theorem comm_prod {g : Fin r → A} {a : A} (h : ∀ l, Commute (g l) a) : Commute (List.ofFn g).prod a := Commute.list_prod_left _ _ fun x hx => by
    simp only [List.mem_ofFn] at hx
    obtain ⟨l, rfl⟩ := hx
    exact h l

theorem dg_Tvl (l : Fin r) (i j : Fin 2) : Dg L Y 1 (fun y => L.Tvl y l i j) := by
  fin_cases i <;> fin_cases j
  · show Dg L Y 1 (fun y => algebraMap ℂ A y - L.pb l)
    refine dg_lin _ (-1) (fun s => ?_) (fun m hm q => ?_)
    · rw [map_sub, smul_neg, Algebra.smul_def, mul_one]
      abel
    · rw [sub_mul, mul_sub, ((hm q).2.2.1 l), Algebra.commutes, mul_neg, mul_one]
      abel
  · show Dg L Y 1 (fun _ => -L.cb l)
    exact (dg_const _ fun m hm q => (comm_cb hm q l).neg_left).mono zero_le_one
  · show Dg L Y 1 (fun _ => L.cbi l)
    exact (dg_const _ fun m hm q => comm_cbi hm q l).mono zero_le_one
  · show Dg L Y 1 (fun _ => (0 : A))
    exact (dg_const _ fun m hm q => Commute.zero_left _).mono zero_le_one

theorem dg_list (ls : List (Fin r)) (i j : Fin 2) :
    Dg L Y ls.length (fun y => (ls.map (L.Tvl y)).prod i j) := by
  induction ls generalizing i j with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.length_nil]
    exact dg_const _ fun m hm q => by
      rw [Matrix.one_apply]
      split_ifs <;> simp
  | cons l ls ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply, Fin.sum_univ_two, List.length_cons]
    exact (Dg.add ((dg_Tvl l i 0).mul (ih 0 j)) ((dg_Tvl l i 1).mul (ih 1 j))).mono (by omega)

theorem dg_Tvprod (i j : Fin 2) : Dg L Y r (fun y => L.Tvprod y i j) := by
  have h := dg_list (L := L) (Y := Y) (List.ofFn (fun l : Fin r => l)).reverse i j
  rw [List.length_reverse, List.length_ofFn] at h
  have e : (fun y => L.Tvprod y i j) =
      fun y => (((List.ofFn (fun l : Fin r => l)).reverse).map (L.Tvl y)).prod i j := by
    funext y
    simp only [LevelData.Tvprod, List.map_reverse, List.map_ofFn]
    rfl
  rw [e]
  exact h

theorem backwardTaylorDegree_one_mirrorLetter : Dg L Y 1 L.m0 := by
  show Dg L Y 1 (fun y => -L.nabs - algebraMap ℂ A (y - 1 / 2) * (L.ζ * L.GGi))
  refine dg_lin _ (L.ζ * L.GGi) (fun s => ?_) (fun m hm q => ?_)
  · rw [show Y - s - 1 / 2 = (Y - 1 / 2) - s by ring, map_sub, sub_mul, Algebra.smul_def]
    abel
  · have e1 := (hm q).2.2.2.2
    have c1 := (comm_zG hm q).eq
    have c2 := (comm_zG hm (q + 1)).eq
    have c3 := Algebra.commutes (R := ℂ) (Y - 1 / 2) (m q)
    have e0 : (-L.nabs - algebraMap ℂ A (Y - 1 / 2) * (L.ζ * L.GGi)) * m q =
        -(L.nabs * m q) - algebraMap ℂ A (Y - 1 / 2) * (L.ζ * L.GGi * m q) := by noncomm_ring
    rw [e0, e1, c1, ← mul_assoc (algebraMap ℂ A (Y - 1 / 2)) (m q) (L.ζ * L.GGi), c3, c2]
    noncomm_ring

theorem dg_Ahatv : Dg L Y (r + 1) L.Ahatv := by
  have hc : Dg L Y 0 (fun _ => L.Drb) := dg_const _ fun m hm q => comm_prod fun l => comm_cb hm q l
  exact (hc.mul (dg_Tvprod 0 0)).mono (by omega)

theorem backwardTaylorDegree_minusHatR : Dg L Y (r + 1) L.R0v := by
  have hc : Dg L Y 0 (fun _ => L.Dr * L.GG) :=
    dg_const _ fun m hm q => (comm_prod fun l => comm_c hm q l).mul_left (comm_GG hm q)
  have hA : Dg L Y r (fun y => L.Avr y) := dg_Tvprod 0 0
  have hB : Dg L Y (1 + r) (fun y => L.Bvr y) := (dg_Tvprod 1 0).mono (by omega)
  exact (hc.mul ((backwardTaylorDegree_one_mirrorLetter.mul hA).add hB)).mono (by omega)

theorem taylor_minus : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r), ∀ Y : ℂ, ∃ Xa Xr : ℕ → A, (∀ s : ℂ, L.Ahatv (Y - s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xa j) ∧ (∀ s : ℂ, L.R0v (Y - s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xr j) ∧ ∀ m : ℕ → A, MulRel L m → ∀ q, L.Ahatv Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xa j ∧ L.R0v Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xr j := by
  intro A _ _ r L Y
  obtain ⟨Xa, ha1, ha2⟩ := (dg_Ahatv (L := L) (Y := Y)).out
  obtain ⟨Xr, hr1, hr2⟩ := (backwardTaylorDegree_minusHatR (L := L) (Y := Y)).out
  exact ⟨Xa, Xr, ha1, hr1, fun m hm q => ⟨ha2 m hm q, hr2 m hm q⟩⟩

end GlobalTheory.HatNF.TaylorMinus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PlusHatsPassGenerators
section
namespace GlobalTheory.HatNF.GenPlus

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open Formalism.FourierDecayAlt.P.MAx3.H

noncomputable section

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem star_inv_eq {x xi y yi : A} (h : star x = y) (hx : x * xi = 1) (hy : y * yi = 1) : star xi = yi := by
  have h1 : star xi * y = 1 := by rw [← h, ← star_mul, hx, star_one]
  calc star xi = star xi * (y * yi) := by rw [hy, mul_one]
    _ = yi := by rw [← mul_assoc, h1, one_mul]

theorem star_list_prod (l : List A) : star l.prod = (l.map star).reverse.prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.prod_cons, star_mul, ih, List.map_cons, List.reverse_cons, List.prod_append,
      List.prod_singleton]

variable {P : M.Par} {d : Q.NFData P A}

theorem mem_span {b h : A} (hb : b ∈ bmon d) (hh : h ∈ hats d.L) : b * h ∈ nfSpan d (hats d.L) 0 0 1 :=
  Submodule.subset_span ⟨b, hb, [h], rfl, by simpa using hh, by simp⟩

theorem ahat_mem (y : ℂ) : d.L.Ahat y ∈ hats d.L := Or.inl (Or.inl (Or.inl ⟨y, rfl⟩))
theorem plusHatR_mem_hatLettersAllPoints (y : ℂ) : d.L.R0 y ∈ hats d.L := Or.inl (Or.inl (Or.inr ⟨y, rfl⟩))

theorem kappa_comm (h : HatHyp d) (f : M.Ty P → ℂ) (y : ℂ) :
    Commute (d.κ f) (d.L.Ahat y) ∧ Commute (d.κ f) (d.L.R0 y) := by
  obtain ⟨-, -, hR, -, -, -, hs⟩ := h
  have hf : ∀ g ∈ d.L.fns, Commute (d.κ f) g := fun g hg => hR.2.1 f g (Or.inl hg)
  have hn : Commute (d.κ f) d.L.nab := hR.2.1 f _ (Or.inr (by simp))
  have hp : ∀ l, Commute (d.κ f) (d.L.p l) := fun l => hs f _ (by simp [TL.siteOps])
  have hT := d.L.inv_comm_Tprod hp (fun l => hf _ (d.L.inv_mem_c l)) (fun l => hf _ (d.L.inv_mem_ci l)) y
  have hDr : Commute (d.κ f) d.L.Dr := LevelData.inv_comm_ofFn fun l => hf _ (d.L.inv_mem_c l)
  have hDrb : Commute (d.κ f) d.L.Drb := LevelData.inv_comm_ofFn fun l => hf _ (d.L.inv_mem_cb l)
  have hl0 : Commute (d.κ f) (d.L.l0 y) :=
    hn.neg_right.sub_right ((Algebra.commute_algebraMap_right _ _).mul_right
      ((hf _ d.L.inv_mem_ζb).mul_right (hf _ d.L.inv_mem_GGi)))
  exact ⟨hDr.mul_right (hT 0 0),
    (hDrb.mul_right (hf _ d.L.inv_mem_GG)).mul_right ((hl0.mul_right (hT 0 0)).add_right (hT 1 0))⟩

theorem ssn_rule (h : HatHyp d) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (y : ℂ) :
    d.L.Ahat y * ssn d l = ssn d l * d.L.Ahat (y - 1) ∧ d.L.R0 y * ssn d l = ssn d l * d.L.R0 (y - 1) := by
  obtain ⟨-, -, hR, -, -, -, -⟩ := h
  obtain ⟨h1, h2⟩ := hR.2.2.2.2.1 l hl
  have hc := hR.2.2.1 l
  have := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r d.L (d.SS l) 0 (fun x hx => (hc x (Or.inl (Or.inl hx))).symm.eq)
    (fun m => (hc _ (Or.inl (Or.inr ⟨m, rfl⟩))).symm.eq) (fun m => (hc _ (Or.inr ⟨m, rfl⟩)).symm.eq) h1 h2
    (fun x _ => by simp) (fun l => by simp) (fun l => by simp) (by simp) (by simp) y
  exact ⟨this.1, this.2.1⟩

variable [StarModule ℂ A]

theorem star_GG (h : HatHyp d) : star d.L.GG = d.L.GG := by
  obtain ⟨-, ⟨hz, -, hT⟩, -⟩ := h
  have hzb : star d.L.ζb = d.L.ζ := by rw [← hz, star_star]
  rw [d.L.GG_def, star_sub, star_mul, hz, hzb, Algebra.algebraMap_eq_smul_one, star_smul, hT, star_one]

theorem star_GGi (h : HatHyp d) : star d.L.GGi = d.L.GGi := star_inv_eq (star_GG h) d.L.GG_GGi d.L.GG_GGi

theorem star_fns (h : HatHyp d) : ∀ x ∈ d.L.fns, star x ∈ d.L.fns := by
  have hG := star_GG h
  have hGi := star_GGi h
  obtain ⟨-, ⟨hz, -, -⟩, -, -, hc, hci, -⟩ := h
  have hzi : star d.L.ζi = d.L.ζbi := star_inv_eq hz d.L.ζ_ζi d.L.ζb_ζbi
  intro x hx
  simp only [LevelData.fns, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | (rfl | rfl | rfl | rfl | rfl | rfl))
  · rw [hc]; exact d.L.inv_mem_cb l
  · rw [hci]; exact d.L.inv_mem_cbi l
  · rw [← hc, star_star]; exact d.L.inv_mem_c l
  · rw [← hci, star_star]; exact d.L.inv_mem_ci l
  · rw [hz]; exact d.L.inv_mem_ζb
  · rw [hzi]; exact d.L.inv_mem_ζbi
  · rw [← hz, star_star]; exact d.L.inv_mem_ζ
  · rw [← hzi, star_star]; exact d.L.inv_mem_ζi
  · rw [hG]; exact d.L.inv_mem_GG
  · rw [hGi]; exact d.L.inv_mem_GGi

omit [StarModule ℂ A] in
theorem star_ssn (h : HatHyp d) (l : ℕ) : star (ssn d l) = star (d.SS l) * (d.L.Dr * d.L.Drbi) := by
  obtain ⟨-, -, -, -, hc, hci, -⟩ := h
  have h1 : star d.L.Drb = d.L.Dr := by
    unfold LevelData.Drb LevelData.Dr
    rw [star_list_prod, List.map_ofFn]
    have : (star ∘ d.L.cb) = d.L.c := funext fun m => by rw [Function.comp, ← hc, star_star]
    rw [this, rev_prod d.L]
    intro x hx; obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx; exact memF d.L (d.L.inv_mem_c m)
  have h2 : star d.L.Dri = d.L.Drbi := by
    unfold LevelData.Dri LevelData.Drbi
    rw [star_list_prod, List.map_ofFn]
    have : (star ∘ d.L.ci) = d.L.cbi := funext hci
    rw [this, rev_prod d.L]
    intro x hx; obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx; exact memF d.L (d.L.inv_mem_cbi m)
  unfold ssn
  rw [star_mul, star_mul, h1, h2, cl_comm d.L (memDrbi d.L) (memDr d.L)]

theorem star_ssn_rule (h : HatHyp d) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (y : ℂ) :
    d.L.Ahat y * star (ssn d l) = star (ssn d l) * d.L.Ahat (y + 1) ∧
      d.L.R0 y * star (ssn d l) = star (ssn d l) * d.L.R0 (y + 1) := by
  have hGi := star_GGi h
  have hF := star_fns h
  rw [star_ssn h]
  obtain ⟨-, ⟨hz, hn, -⟩, hR, hp, -, -, -⟩ := h
  obtain ⟨h1, h2⟩ := hR.2.2.2.2.1 l hl
  have hc := hR.2.2.1 l
  have hzb : star d.L.ζb = d.L.ζ := by rw [← hz, star_star]
  have hns : star d.L.nabs = d.L.nab := by rw [← hn, star_star]
  have key : ∀ x, Commute (d.SS l) (star x) → x * star (d.SS l) = star (d.SS l) * x := fun x hx => by
    have := congrArg star hx.eq
    simpa [star_mul] using this
  have hf : ∀ x ∈ d.L.fns, x * star (d.SS l) = star (d.SS l) * x :=
    fun x hx => key x (hc _ (Or.inl (Or.inl (hF x hx))))
  have hp1 : ∀ m, d.L.p m * star (d.SS l) = star (d.SS l) * d.L.p m := fun m =>
    key _ (by rw [hp]; exact (hc _ (Or.inr ⟨m, rfl⟩)).neg_right)
  have hp2 : ∀ m, d.L.pb m * star (d.SS l) = star (d.SS l) * d.L.pb m := fun m =>
    key _ (by
      have : star (d.L.pb m) = -d.L.p m := by
        have := congrArg star (hp m)
        rw [star_star, star_neg] at this
        rw [this, neg_neg]
      rw [this]; exact (hc _ (Or.inl (Or.inr ⟨m, rfl⟩))).neg_right)
  have c1 : star (d.SS l) * (d.L.GGi * d.L.ζb) = d.L.ζb * d.L.GGi * star (d.SS l) := by
    rw [← mul_assoc, ← hf _ d.L.inv_mem_GGi, mul_assoc, ← hf _ d.L.inv_mem_ζb, ← mul_assoc,
      (d.L.inv_fcomm d.L.inv_mem_GGi d.L.inv_mem_ζb).eq]
  have c2 : star (d.SS l) * (d.L.GGi * d.L.ζ) = d.L.ζ * d.L.GGi * star (d.SS l) := by
    rw [← mul_assoc, ← hf _ d.L.inv_mem_GGi, mul_assoc, ← hf _ d.L.inv_mem_ζ, ← mul_assoc,
      (d.L.inv_fcomm d.L.inv_mem_GGi d.L.inv_mem_ζ).eq]
  have e1 : d.L.nab * star (d.SS l) = star (d.SS l) * d.L.nab + d.L.ζb * d.L.GGi * star (d.SS l) := by
    have := congrArg star h2
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, hns, hz, hGi] at this
    rw [← c1, this]; abel
  have e2 : d.L.nabs * star (d.SS l) = star (d.SS l) * d.L.nabs + d.L.ζ * d.L.GGi * star (d.SS l) := by
    have := congrArg star h1
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, hn, hzb, hGi] at this
    rw [← c2, this]; abel
  have := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r d.L 0 (star (d.SS l)) (fun x _ => by simp) (fun l => by simp)
    (fun l => by simp) (by simp) (by simp) hf hp1 hp2 e1 e2 y
  exact ⟨this.2.2.2.2.1, this.2.2.2.2.2.1⟩

end

theorem plus_hats_pass_generators : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (d : Q.NFData P A), HatHyp d → ∀ b ∈ bset d, ∀ y : ℂ,
      d.L.Ahat y * b ∈ nfSpan d (hats d.L) 0 0 1 ∧ d.L.R0 y * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  intro P A _ _ _ _ d h b hb y
  have gen : ∀ {x}, x ∈ bset d → x ∈ bmon d := fun h => Submonoid.subset_closure h
  have mDD : d.L.D * d.L.Dbi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mDbD : d.L.Db * d.L.Di ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mζi : d.L.ζi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mζbi : d.L.ζbi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have hdrb : d.L.Drb * d.L.Di ∈ bmon d := by
    rw [drb_eq]; exact Submonoid.mul_mem _ mDbD mζbi
  have hbm := gen hb
  rcases hb with (((hb | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · refine ⟨by rw [(hat_ζi d.L y).1]; exact mem_span hbm (ahat_mem _), ?_⟩
      rw [gen_ζi_R]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact Submodule.add_mem _ (mem_span hbm (plusHatR_mem_hatLettersAllPoints _)) (Submodule.add_mem _
        (Submodule.smul_mem _ _ (mem_span mDbD (ahat_mem _)))
        (Submodule.smul_mem _ _ (mem_span (Submonoid.mul_mem _ (Submonoid.mul_mem _ mζi mζbi) mDbD) (ahat_mem _))))
    · exact ⟨by rw [← (hat_ζbi d.L y).1]; exact mem_span hbm (ahat_mem _),
        by rw [← (hat_ζbi d.L y).2]; exact mem_span hbm (plusHatR_mem_hatLettersAllPoints _)⟩
    · refine ⟨by rw [gen_DD_A]; exact mem_span hbm (ahat_mem _), ?_⟩
      rw [gen_DD_R]
      exact Submodule.add_mem _ (mem_span hbm (plusHatR_mem_hatLettersAllPoints _))
        (Submodule.smul_mem _ _ (mem_span (Submonoid.mul_mem _ mDD hdrb) (ahat_mem _)))
    · refine ⟨by rw [gen_DbD_A]; exact mem_span hbm (ahat_mem _), ?_⟩
      rw [gen_DbD_R]
      exact Submodule.add_mem _ (mem_span hbm (plusHatR_mem_hatLettersAllPoints _))
        (Submodule.smul_mem _ _ (mem_span (Submonoid.mul_mem _ mDbD hdrb) (ahat_mem _)))
  · exact ⟨by rw [← (kappa_comm h f y).1.eq]; exact mem_span hbm (ahat_mem _),
      by rw [← (kappa_comm h f y).2.eq]; exact mem_span hbm (plusHatR_mem_hatLettersAllPoints _)⟩
  · have hi' := Finset.mem_Icc.2 (Set.mem_Icc.1 hi)
    exact ⟨by rw [(ssn_rule h hi' y).1]; exact mem_span hbm (ahat_mem _),
      by rw [(ssn_rule h hi' y).2]; exact mem_span hbm (plusHatR_mem_hatLettersAllPoints _)⟩
  · have hi' := Finset.mem_Icc.2 (Set.mem_Icc.1 hi)
    exact ⟨by beta_reduce; rw [(star_ssn_rule h hi' y).1]; exact mem_span hbm (ahat_mem _),
      by beta_reduce; rw [(star_ssn_rule h hi' y).2]; exact mem_span hbm (plusHatR_mem_hatLettersAllPoints _)⟩

end GlobalTheory.HatNF.GenPlus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProjRaisingProjEqSmul
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.RaiseFormula

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem up_unique {j : ℕ} {a b c : M.Ty P} (h : M.Up P j a b) (h' : M.Up P j a c) : b = c := by
  funext i
  exact Fin.ext ((h i).trans (h' i).symm)

theorem up_index {l j : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {a b : M.Ty P} (h : M.Up P l a b)
    (h' : M.Up P j a b) : j = l := by
  rw [Finset.mem_Icc] at hl
  have h1 := h ⟨l - 1, by omega⟩
  have h2 := h' ⟨l - 1, by omega⟩
  have e : l - 1 + 1 = l := by omega
  simp only [e, if_true] at h1 h2
  by_contra hne
  rw [if_neg (fun x => hne x.symm)] at h2
  omega

theorem up_ne {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {a b : M.Ty P} (h : M.Up P l a b) : b ≠ a := by
  rw [Finset.mem_Icc] at hl
  rintro rfl
  have h1 := h ⟨l - 1, by omega⟩
  have e : l - 1 + 1 = l := by omega
  simp only [e, if_true] at h1
  omega

omit [StarRing A] in
theorem sum_proj (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) : ∑ ρ, NF.proj κ ρ = 1 := by
  unfold NF.proj
  rw [← map_sum, ← map_one κ]
  congr 1
  funext x
  simp [Finset.sum_apply]

omit [StarRing A] in
theorem kap_mul_proj (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (f : M.Ty P → ℂ) (ρ : M.Ty P) :
    κ f * NF.proj κ ρ = f ρ • NF.proj κ ρ := by
  unfold NF.proj
  rw [← map_mul, ← map_smul]
  congr 1
  funext x
  by_cases h : x = ρ <;> simp [h]

omit [StarRing A] in
theorem proj_mul_proj (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) {ρ ρ' : M.Ty P} (h : ρ' ≠ ρ) :
    NF.proj κ ρ' * NF.proj κ ρ = 0 := by
  have := kap_mul_proj κ (fun x => if x = ρ' then 1 else 0) ρ
  rw [if_neg (Ne.symm h), zero_smul] at this
  exact this

theorem proj_SS_proj (d : Q.NFData P A) (hd : d.Rel) {j : ℕ} {ρ ρ' : M.Ty P} (h : ¬ M.Up P j ρ ρ') :
    NF.proj d.κ ρ' * d.SS j * NF.proj d.κ ρ = 0 := by
  have h1 := hd.2.2.2.1 j (fun a => if M.Up P j a ρ' then 1 else 0) (fun x => if x = ρ' then 1 else 0) (by
    intro a b hab
    by_cases hb : b = ρ'
    · subst hb; simp [hab]
    · have : ¬ M.Up P j a ρ' := fun h' => hb (up_unique hab h')
      simp [hb, this])
  have h2 : NF.proj d.κ ρ' * d.SS j = _ := h1
  rw [h2, mul_assoc, kap_mul_proj, if_neg h, zero_smul, mul_zero]

theorem proj_raising_proj_eq_smul (d : Q.NFData P A) (hd : d.Rel) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (Y : ℂ)
    {ρ ρ' : M.Ty P} (h : M.Up P l ρ ρ') :
    NF.proj d.κ ρ' * d.QQ Y 1 0 * NF.proj d.κ ρ =
      M.xEx P {l} ρ Y • (NF.proj d.κ ρ' * d.SS l * NF.proj d.κ ρ) := by
  have hq : d.QQ Y 1 0 = d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y := rfl
  have hc : ∀ g ∈ d.L.fns ∪ {d.L.nab, d.L.nabs}, Commute (NF.proj d.κ ρ') g := fun g hg => hd.2.1 _ g hg
  have c1 : Commute (NF.proj d.κ ρ') d.L.GG := hc _ (by simp [LevelData.fns])
  have c2 : Commute (NF.proj d.κ ρ') d.L.GGi := hc _ (by simp [LevelData.fns])
  have c3 : Commute (NF.proj d.κ ρ') d.L.ζb := hc _ (by simp [LevelData.fns])
  have c4 : Commute (NF.proj d.κ ρ') d.L.nab := hc _ (by simp)
  have c5 : Commute (NF.proj d.κ ρ') (d.x Y) := by
    unfold NF.proj Q.NFData.x
    exact (Commute.all _ _).map d.κ
  have c6 : Commute (NF.proj d.κ ρ') (d.L.l0 Y) := by
    unfold LevelData.l0
    exact c4.neg_right.sub_right ((Algebra.commute_algebraMap_right _ _).mul_right (c3.mul_right c2))
  have c7 := (c1.mul_right c5).mul_right c6
  rw [hq, mul_add, add_mul, c7.eq, mul_assoc _ (NF.proj d.κ ρ'), proj_mul_proj _ (up_ne hl h), mul_zero, zero_add]
  unfold Q.NFData.weightedSumBis
  have key : ∀ j, NF.proj d.κ ρ' * (d.SS j * d.κ fun ρ => M.xEx P {j} ρ Y) * NF.proj d.κ ρ =
      M.xEx P {j} ρ Y • (NF.proj d.κ ρ' * d.SS j * NF.proj d.κ ρ) := by
    intro j
    rw [← mul_assoc, mul_assoc _ (d.κ _), kap_mul_proj, mul_smul_comm]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single l]
  · exact key l
  · intro j _ hj
    rw [key, proj_SS_proj d hd (fun h' => hj (up_index hl h h')), smul_zero]
  · intro h'; exact absurd hl h'

theorem xEx_ne_zero (ex : Finset ℕ) (ρ : M.Ty P) (Y : ℂ) (h : M.xC P ρ Y ≠ 0) : M.xEx P ex ρ Y ≠ 0 := by
  unfold M.xC at h
  unfold M.xEx
  rw [Finset.prod_ne_zero_iff] at h ⊢
  exact fun i hi => h i (Finset.mem_sdiff.1 hi).1

theorem ss_formula : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ Y : ℂ, (∀ ρ : M.Ty P, M.xC P ρ Y ≠ 0) → ∃ co : M.Ty P → M.Ty P → ℂ, d.SS l = ∑ ρ, ∑ ρ', co ρ ρ' • (NF.proj d.κ ρ' * d.QQ Y 1 0 * NF.proj d.κ ρ) := by
  intro P A _ _ _ _ d hd l hl Y hY
  have hr : d.Rel := hd.2.2.1
  refine ⟨fun ρ ρ' => if M.Up P l ρ ρ' then (M.xEx P {l} ρ Y)⁻¹ else 0, ?_⟩
  have h0 : d.SS l = ∑ ρ, ∑ ρ', NF.proj d.κ ρ' * d.SS l * NF.proj d.κ ρ := by
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [sum_proj, one_mul, mul_one]
  refine h0.trans (Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun ρ' _ => ?_)
  by_cases h : M.Up P l ρ ρ'
  · simp only [if_pos h]
    rw [proj_raising_proj_eq_smul d hr hl Y h, smul_smul, inv_mul_cancel₀ (xEx_ne_zero _ _ _ (hY ρ)), one_smul]
  · simp only [if_neg h]
    rw [zero_smul, proj_SS_proj d hr h]

end GlobalTheory.HatNF.RaiseFormula
end

