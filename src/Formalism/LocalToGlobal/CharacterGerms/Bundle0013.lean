import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0002
import Formalism.LocalToGlobal.CharacterGerms.GeOfPowEqOne
import Formalism.LocalToGlobal.CharacterGerms.RowTieTop

-- bundled from Formalism.LocalToGlobal.CharacterGerms.BlockMembershipNormOne
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj

abbrev IIof {T Orb : Type} {d : ℕ} (r : T → ℕ) (tau : Orb → Fin 2 → ZMod d → T) (o : Orb) (g : Fin 2) : Type :=
  Σ t : ZMod d, Fin (r (tau o g t))

def phiL {T Orb : Type} {d : ℕ} (r : T → ℕ) (tau : Orb → Fin 2 → ZMod d → T) (n : ℕ)
    (x : Fin n × WVO (IIof r tau)) : Letter T r n :=
  ⟨tau x.2.1 x.2.2.1 x.2.2.2.1, x.2.2.2.2, x.1⟩

def WtTie {T Orb : Type} {d : ℕ} (r : T → ℕ) (tau : Orb → Fin 2 → ZMod d → T) (Z : Finset Orb)
    (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (a : T → ℕ → ℕ) : Prop :=
  (∀ o ∈ Z, ∀ g t (i : ℕ), i < r (tau o g t) →
    a (tau o g t) i = ∑ k ∈ Finset.Icc (i + 1) (r (tau o g t)), ga o g t k) ∧
  ∀ σ, (∀ o ∈ Z, ∀ g t, tau o g t ≠ σ) → ∀ i, i < r σ → a σ i = 0

section Defs

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb]
  {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]

def blkProd (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, Flag (X o)) (n : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n) : MvPolynomial (Fin n × WVO I) C :=
  ∏ o, toAll o (prodAll (plAt n pl o) fun i => (blkAt L o i).poly (X o) (F o))

end Defs

structure ConjugatePairPlaceSetting {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    {Orb : Type} [Fintype Orb] (tau : Orb → Fin 2 → ZMod d → T) {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (IIof r tau o) (J o)) (F : ∀ o, Flag (X o)) (Z : Finset Orb)
    (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (n : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n) : Prop where

  inj : Function.Injective fun x : Orb × Fin 2 × ZMod d => tau x.1 x.2.1 x.2.2
  conj : ∀ o t, cc (tau o 0 t) = tau o 1 t
  conj' : ∀ o t, cc (tau o 1 t) = tau o 0 t

  hty : ∀ o g (x : IIof r tau o g), ((X o).G g).ty (Sum.inl x) = x.1
  std : ∀ o g t (c : Fin ((X o).rkF g t)), ((F o).en g t c).2.val = c.val

  dich : ∀ o ∈ Z, (X o).Alt ∨ ∀ t, (X o).big 0 t
  hj : ∀ o ∈ Z, (X o).j' < (X o).n
  supp : ∀ o ∈ Z, ∀ g t k, ga o g t k ≠ 0 → 1 ≤ k ∧ k ≤ (X o).rkF g t

  off : ∀ o, o ∉ Z → L o = []
  wt : ∀ o ∈ Z, ∀ g t k, ((L o).map fun q => q.1.wt (X o) g t k).sum = ga o g t k
  tie : WtTie r tau Z ga a
  plinj : Function.Injective pl

def NormOneHarmonic : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → Fin 2 → ZMod d → T) (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (IIof r tau o) (J o)) (F : ∀ o, Flag (X o)) (Z : Finset Orb)
    (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (n : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n),
    ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl →
      ∀ isX : T → Prop, MvPolynomial.rename (phiL r tau n) (blkProd X F n L pl) ∈ harmK r n C cc isX (fun _ => 1)

def NormOneLineInvariant : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → Fin 2 → ZMod d → T) (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (IIof r tau o) (J o)) (F : ∀ o, Flag (X o)) (Z : Finset Orb)
    (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (n : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n),
    ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl →
      RowInv r n C (MvPolynomial.rename (phiL r tau n) (blkProd X F n L pl))

def NormOneLineDegrees : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → Fin 2 → ZMod d → T) (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (IIof r tau o) (J o)) (F : ∀ o, Flag (X o)) (Z : Finset Orb)
    (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (n : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n),
    ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl →
      RowDeg r n C a (MvPolynomial.rename (phiL r tau n) (blkProd X F n L pl))

def NormOneIntegral : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → Fin 2 → ZMod d → T) (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (IIof r tau o) (J o)) (F : ∀ o, Flag (X o)) (Z : Finset Orb)
    (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (n : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n),
    ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl →
      ∀ (O : Subring C) m, (MvPolynomial.rename (phiL r tau n) (blkProd X F n L pl)).coeff m ∈ O

section Mem

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} (r : T → ℕ) (cc : T → T) (isX : T → Prop)
  (a : T → ℕ → ℕ) {Orb : Type} [Fintype Orb] (tau : Orb → Fin 2 → ZMod d → T) (O : Subring C) (n : ℕ)

def harmonicProductFamily : Set (∀ o, MvPolynomial (Fin n × WV (IIof r tau o)) C) :=
  {Po | MvPolynomial.rename (phiL r tau n) (∏ o, toAll o (Po o)) ∈ HaO r n C O cc isX a}

variable {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]

theorem block_membership_norm_one (h1 : NormOneHarmonic) (h2 : NormOneLineInvariant) (h3 : NormOneLineDegrees) (h4 : NormOneIntegral)
    (X : ∀ o, RowData C V d (IIof r tau o) (J o)) (F : ∀ o, Flag (X o)) (Z : Finset Orb)
    (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ)
    (inj : Function.Injective fun x : Orb × Fin 2 × ZMod d => tau x.1 x.2.1 x.2.2)
    (conj : ∀ o t, cc (tau o 0 t) = tau o 1 t) (conj' : ∀ o t, cc (tau o 1 t) = tau o 0 t)
    (hty : ∀ o g (x : IIof r tau o g), ((X o).G g).ty (Sum.inl x) = x.1)
    (std : ∀ o g t (c : Fin ((X o).rkF g t)), ((F o).en g t c).2.val = c.val)
    (dich : ∀ o ∈ Z, (X o).Alt ∨ ∀ t, (X o).big 0 t) (hj : ∀ o ∈ Z, (X o).j' < (X o).n)
    (supp : ∀ o ∈ Z, ∀ g t k, ga o g t k ≠ 0 → 1 ≤ k ∧ k ≤ (X o).rkF g t) (tie : WtTie r tau Z ga a) :
    BlockMembership X n F (harmonicProductFamily r cc isX a tau O n) Z ga := by
  intro L off wt pl plinj
  have H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl := ⟨inj, conj, conj', hty, std, dich, hj, supp, off, wt, tie, plinj⟩
  exact ⟨⟨h1 C V d T r cc a Orb tau J X F Z ga n L pl H isX, h2 C V d T r cc a Orb tau J X F Z ga n L pl H,
    h3 C V d T r cc a Orb tau J X F Z ga n L pl H⟩, h4 C V d T r cc a Orb tau J X F Z ga n L pl H O⟩

end Mem

end Formalism.L2.FormalSeriesBounds.RF
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.CoeffAlongCvCongr
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

theorem coeff_alongCv_congr {σ : Type} [Finite σ] {a a' : σ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) (ha' : ∀ i, PowerSeries.constantCoeff (a' i) = 0) {k : ℕ}
    (h : ∀ i, ∀ m < k, PowerSeries.coeff m (a i) = PowerSeries.coeff m (a' i)) (f : MvPowerSeries σ C) :
    ∀ m < k, PowerSeries.coeff m (alongCv a f) = PowerSeries.coeff m (alongCv a' f) := by
  intro m hm
  have hA : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hA' : MvPowerSeries.HasSubst a' := MvPowerSeries.hasSubst_of_constantCoeff_zero ha'
  have hdiff : ∀ i, a i - a' i ∈ Ideal.span {(PowerSeries.X : PowerSeries C) ^ k} := by
    intro i
    rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro n hn
    rw [map_sub, h i n hn, sub_self]
  have hprod : ∀ e : σ →₀ ℕ, PowerSeries.coeff m (e.prod fun s n => a s ^ n) =
      PowerSeries.coeff m (e.prod fun s n => a' s ^ n) := by
    intro e
    have hq : Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ k}) (e.prod fun s n => a s ^ n) =
        Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries C) ^ k}) (e.prod fun s n => a' s ^ n) := by
      simp only [Finsupp.prod, map_prod, map_pow]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [Ideal.Quotient.eq.2 (hdiff s)]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at hq
    have hm' := hq m hm
    rwa [map_sub, sub_eq_zero] at hm'
  simp only [alongCv]
  change MvPowerSeries.coeff (Finsupp.single () m) (MvPowerSeries.subst a f) =
    MvPowerSeries.coeff (Finsupp.single () m) (MvPowerSeries.subst a' f)
  rw [MvPowerSeries.coeff_subst hA, MvPowerSeries.coeff_subst hA']
  refine finsum_congr fun e => ?_
  congr 1
  exact hprod e

theorem coeff_tyS_congr {l : ℕ} (hl : 2 ≤ l) (a b : ℕ → C) (N : ℕ) (hab : ∀ i < N, a i = b i) (m : ℕ)
    (hm : m < l ^ N) : PowerSeries.coeff m (tyS l a) = PowerSeries.coeff m (tyS l b) := by
  simp only [tyS, PowerSeries.coeff_mk]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : l ^ s = m
  · rw [if_pos hs, if_pos hs]
    apply hab
    by_contra hc
    push_neg at hc
    have h1 : l ^ N ≤ l ^ s := Nat.pow_le_pow_right (by omega) hc
    rw [hs] at h1
    exact absurd hm (not_lt.2 h1)
  · rw [if_neg hs, if_neg hs]

theorem constantCoeff_tyS {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) : PowerSeries.constantCoeff (tyS l a) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [tyS, PowerSeries.coeff_mk]
  simp

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem curve_eq_ex_lg (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    (δ : κ → PowerSeries C) (hδ : ∀ i, PowerSeries.constantCoeff (δ i) = 0) (i : κ) :
    δ i = alongCv (fun j => alongCv δ (X.lg j)) (X.ex i) := by
  have hA : MvPowerSeries.HasSubst X.lg := MvPowerSeries.hasSubst_of_constantCoeff_zero hlg0
  have hB : MvPowerSeries.HasSubst δ := MvPowerSeries.hasSubst_of_constantCoeff_zero hδ
  simp only [alongCv]
  rw [← MvPowerSeries.subst_comp_subst_apply hA hB, hexlg i, MvPowerSeries.subst_X hB]

theorem Vpow_mem' (V : VF C) (g : Fin 2) (s : ℕ) (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) :
    Vpow s x ∈ X.TySet V g := by
  induction s with
  | zero => rwa [Vpow_zero]
  | succ s ih => rw [Vpow_succ]; exact X.V_mem V g _ ih

theorem sumV_mem (V : VF C) (g : Fin 2) (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hex0 : ∀ i, MvPowerSeries.constantCoeff (X.ex i) = 0)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    (hlgex : ∀ i, MvPowerSeries.subst X.ex (X.lg i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    (h0 : (0 : ℕ → I g ⊕ JJ I g → C) ∈ X.TySet V g)
    (hadd : ∀ x y, x ∈ X.TySet V g → y ∈ X.TySet V g → x + y ∈ X.TySet V g)
    (y : ℕ → ℕ → I g ⊕ JJ I g → C) (hy : ∀ s, y s ∈ X.TySet V g) : sumV y ∈ X.TySet V g := by
  have hl2 := V.l_prime.two_le
  have hP : ∀ N : ℕ, ∑ s ∈ Finset.range N, Vpow s (y s) ∈ X.TySet V g := fun N =>
    X.sum_mem V g h0 hadd _ _ fun s _ => X.Vpow_mem' V g s _ (hy s)
  have hPeq : ∀ N i, i < N → ∀ n, (∑ s ∈ Finset.range N, Vpow s (y s)) i n = sumV y i n := by
    intro N i hi n
    rw [Finset.sum_apply, Finset.sum_apply]
    show ∑ s ∈ Finset.range N, (if i < s then 0 else y s (i - s) n) = ∑ s ∈ Finset.range (i + 1), y s (i - s) n
    have hsub : Finset.range (i + 1) ⊆ Finset.range N := Finset.range_subset_range.2 (by omega)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun s hs => ?_
      rw [if_neg]
      have := Finset.mem_range.1 hs
      omega
    · intro s _ hs
      rw [if_pos]
      have : ¬ s < i + 1 := fun h => hs (Finset.mem_range.2 h)
      omega
  choose γN lamN hγN hlamN h1N h2N using hP
  set A : κ → PowerSeries C := fun i => ∑ c : I g, X.u g c i • tyS V.l (fun s => sumV y s (Sum.inl c)) with hA
  have hA0 : ∀ i, PowerSeries.constantCoeff (A i) = 0 := by
    intro i
    rw [hA]
    show PowerSeries.constantCoeff (∑ c : I g, X.u g c i • tyS V.l (fun s => sumV y s (Sum.inl c))) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro c _
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_smul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_tyS hl2, smul_zero]
  set γ : κ → PowerSeries C := fun i => alongCv A (X.ex i) with hγdef
  have hγ0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => constantCoeff_subst_zero hA0 (hex0 i)
  have hlgγ : ∀ i, alongCv γ (X.lg i) = A i := by
    intro i
    have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero hA0
    have e1 : MvPowerSeries.subst A (MvPowerSeries.subst X.ex (X.lg i)) = A i := by
      rw [hlgex i, MvPowerSeries.subst_X hS]
    rw [← e1, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hex0) hS]
    rfl
  have htyN : ∀ N n, ∀ m < V.l ^ N, PowerSeries.coeff m (tyS V.l fun s => sumV y s n) =
      PowerSeries.coeff m (tyS V.l fun s => (∑ s ∈ Finset.range N, Vpow s (y s)) s n) := by
    intro N n m hm
    exact coeff_tyS_congr hl2 _ _ N (fun i hi => (hPeq N i hi n).symm) m hm
  have hγN' : ∀ N i, ∀ m < V.l ^ N, PowerSeries.coeff m (γ i) = PowerSeries.coeff m (γN N i) := by
    intro N i m hm
    rw [X.curve_eq_ex_lg hlg0 hexlg (γN N) (fun i => (hγN N i).1) i]
    refine coeff_alongCv_congr hA0 (fun j => constantCoeff_subst_zero (fun i => (hγN N i).1) (hlg0 j)) ?_ _ m hm
    intro j m' hm'
    show PowerSeries.coeff m' (∑ c : I g, X.u g c j • tyS V.l (fun s => sumV y s (Sum.inl c))) =
      PowerSeries.coeff m' (alongCv (γN N) (X.lg j))
    rw [h1N N j]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [PowerSeries.coeff_smul, PowerSeries.coeff_smul, htyN N _ m' hm']
  have hγI : IsCv V γ := by
    intro i
    refine ⟨hγ0 i, fun n => ?_⟩
    rw [hγN' n i n (Nat.lt_pow_self (by omega))]
    exact (hγN n i).2 n
  set lam : JJ I g → PowerSeries C := fun q => tyS V.l (fun s => sumV y s (Sum.inr q)) +
      alongCv γ (X.sg (X.u (1 - g) q)) -
      ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
        X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => sumV y s (Sum.inl c)) else 0) with hlamdef
  have hlamN' : ∀ N q, ∀ m < V.l ^ N, PowerSeries.coeff m (lam q) = PowerSeries.coeff m (lamN N q) := by
    intro N q m hm
    have e : lamN N q = tyS V.l (fun s => (∑ s ∈ Finset.range N, Vpow s (y s)) s (Sum.inr q)) +
        alongCv (γN N) (X.sg (X.u (1 - g) q)) -
        ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) •
          tyS V.l (fun s => (∑ s ∈ Finset.range N, Vpow s (y s)) s (Sum.inl c)) else 0) := by
      rw [h2N N q]
      abel
    rw [e, hlamdef]
    show PowerSeries.coeff m (tyS V.l (fun s => sumV y s (Sum.inr q)) +
      alongCv γ (X.sg (X.u (1 - g) q)) -
      ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
        X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => sumV y s (Sum.inl c)) else 0)) = _
    rw [map_sub, map_sub, map_add, map_add, map_sum, map_sum, htyN N _ m hm,
      coeff_alongCv_congr hγ0 (fun i => (hγN N i).1) (fun i => hγN' N i) _ m hm]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [PowerSeries.coeff_smul, PowerSeries.coeff_smul, htyN N _ m hm]
    · rfl
  have hlamI : IsCv V lam := by
    intro q
    refine ⟨?_, fun n => ?_⟩
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hlamN' 0 q 0 (by simp),
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact (hlamN 0 q).1
    · rw [hlamN' n q n (Nat.lt_pow_self (by omega))]
      exact (hlamN n q).2 n
  refine ⟨γ, lam, hγI, hlamI, hlgγ, ?_⟩
  intro q
  have hab : ∀ a b c : PowerSeries C, a = (a + b - c) - b + c := by
    intro a b c
    abel
  exact hab _ _ _

end RawChart

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Formal

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def FBChart.chartLinearTerm (Y : FBChart C V O dd) (u : Fin dd → C) : PS C 2 dd :=
  fun μ => ∑ i, u i * MvPowerSeries.coeff
    (μ.mapDomain (fun p : Fin 2 × Fin dd => (p.1.succ, p.2)) + Finsupp.single ((0 : Fin 3), i) 1) Y.B.ph2

def cvAt (s : MvPowerSeries (Fin 2) C) (γ : PowerSeries C) : MvPowerSeries (Fin 2) C :=
  MvPowerSeries.subst (fun _ : Unit => s) γ

def NDG (Y : FBChart C V O dd) : Prop :=
  ∀ γ : Fin dd → PowerSeries C, IsCv V γ → (∃ i, ¬ V.MM (PowerSeries.coeff 1 (γ i))) →
    (∀ i (μ : Fin 2 →₀ ℕ), μ 0 < V.l → μ 1 < V.l → V.MM (MvPowerSeries.coeff μ
      (MvPowerSeries.subst (fun p : Fin 2 × Fin dd => cvAt (MvPowerSeries.X p.1) (γ p.2)) (Y.B.G.F i) -
        cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ i)))) →
    ¬ ∃ b : PS C 1 dd, IntS V b ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ
      (Y.chartLinearTerm (fun i => PowerSeries.coeff 1 (γ i)) -
        (ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] b - ev (n := 2) ![pt C dd 0] b -
          ev (n := 2) ![pt C dd 1] b)))

end Formal

def RankMaximalOfNondegenerate : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I),
    NDG Y → (Y.raw p).RankHyp → ∀ Hc : ∀ g, (Y.raw p).CartHyp V g, RawChart.RankMaximalCondition Hc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

def NondegenerateCharts : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → NDG Y

theorem rank_maximal_charts_of_nondegenerate (h1 : RankMaximalOfNondegenerate) (h2 : NondegenerateCharts Xo c) : RankMaximalCharts Xo c :=
  fun hstar T io y C3 C _ _ V ι hι k Y hY _ d _ lab ha hg hr o Hc =>
    h1 C V (𝓞 E) _ Y d _ (pairOfLab ha hg o) (h2 hstar T io y C3 C V ι hι k Y hY) (rankHyp_ofLab ha hg hr o) Hc

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieCH
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.PGsh.Up CharacteristicFromRanks ValuationFitting

def RawChart.HTDPack {C : Type} [Field C] {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type}
    [Fintype κ] {X : RawChart C d I κ} (Hc : ∀ g, X.CartHyp V g) : Prop :=
  ∃ (rh : ℕ) (h : Fin 2 → ℕ) (ht : ∀ g, Fin (h g) → I g → C) (vm : Valuation C NNReal)
    (R : Type) (_ : CommRing R) (_ : Algebra R C) (_ : Algebra ℤ_[V.l] R)
    (O : Type) (_ : CommRing O) (_ : Algebra ℤ_[V.l] O) (σ : O ≃ₐ[ℤ_[V.l]] O) (cp : R) (gB : ℕ)
    (Hh : HodgeTateDatum V.l gB vm R O σ cp) (U : UnramData V.l gB vm R O σ cp Hh),
    (∀ g i x, V.Ge 0 (ht g i x)) ∧ HodgeTateSetting V.l vm R O σ cp ∧
    Nonempty (Comparison₂ (fun g => RawChart.cart (Hc g)) X.big rh h ht vm R O σ cp gB Hh U) ∧
    ∀ g (i : Fin (h g)) (S : ∀ g, Sys (RawChart.cart (Hc g))) (t : ∀ g, I g → MvPowerSeries (I g) C),
      (∀ g, (S g).IsT (t g)) →
      upG g (mvExp (∑ x : I g, ht g i x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈ IntGerm V t

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

def HodgeTateAllCharts : Prop := AllCharts Xo c fun _ _ V _ _ _ _ X => ∀ Hc : ∀ g, X.CartHyp V g, RawChart.HTDPack Hc

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePEmbIntSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

open Formalism.L2.Pj

theorem vV_algebraMap_nonneg (T : CDVR) (t : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr t) := by
  have hle := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (K := T.Fr) t
  unfold vV valV
  generalize (IsDedekindDomain.HeightOneSpectrum.valuation T.Fr
    (IsDiscreteValuationRing.maximalIdeal T.V)) (algebraMap T.V T.Fr t) = y at hle ⊢
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · obtain ⟨a, rfl⟩ := WithZero.ne_zero_iff_exists.1 hy
    have ha : a ≤ 1 := WithZero.coe_le_one.1 hle
    have hlog : WithZero.log (a : WithZero (Multiplicative ℤ)) = Multiplicative.toAdd a := rfl
    rw [hlog, neg_nonneg]
    exact ha

theorem embIntSt_holds : EmbIntSt := by
  unfold EmbIntSt
  intro T C _ V ι h t
  by_cases ht : t = 0
  · subst ht
    rw [map_zero, map_zero]
    exact VF.Ge.zero 0
  · have hx : algebraMap T.V T.Fr t ≠ 0 :=
      fun h0 => ht ((IsFractionRing.injective T.V T.Fr) (by rw [h0, map_zero]))
    have hl : ((V.l : ℕ) : T.Fr) = algebraMap T.V T.Fr ((V.l : ℕ) : T.V) := (map_natCast _ _).symm
    have h1 := vV_algebraMap_nonneg T t
    have h2 := vV_algebraMap_nonneg T ((V.l : ℕ) : T.V)
    rw [← hl] at h2
    unfold VF.Ge
    rw [h (algebraMap T.V T.Fr t) hx]
    exact WithTop.coe_le_coe.2 (div_nonneg (by exact_mod_cast h1) (by exact_mod_cast h2))

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePLogExSt
section
set_option autoImplicit false

noncomputable section

open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace LogEx

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

def LinN {C : Type} [CommRing C] {dd : ℕ} (f : Pt C 1 dd) : Prop :=
  ∀ i (μ : Fin 1 × Fin dd →₀ ℕ), μ.degree ≤ 1 →
    MvPowerSeries.coeff μ (f i) = MvPowerSeries.coeff μ (MvPowerSeries.X ((0 : Fin 1), i) : PS C 1 dd)

def LogSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (dd : ℕ) (G : FGLaw C dd), ∃ lg : Pt C 1 dd, LinN lg ∧
    ∀ i, ev (n := 2) ![addOf G.F (pt C dd 0) (pt C dd 1)] (lg i) =
      ev (n := 2) ![pt C dd 0] (lg i) + ev (n := 2) ![pt C dd 1] (lg i)

def RInvSt : Prop :=
  ∀ (C : Type) [Field C] (dd : ℕ) (φ : Pt C 1 dd), LinN φ → ∃ ψ : Pt C 1 dd, LinN ψ ∧ comp1 φ ψ = pt C dd 0

section Gen

variable {C : Type} [CommRing C] {dd : ℕ}

theorem linN_const {f : Pt C 1 dd} (hf : LinN f) (i : Fin dd) : constantCoeff (f i) = 0 := by
  have h := hf i 0 (by simp)
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h, MvPowerSeries.coeff_zero_X]

end Gen

end LogEx

end Formalism.L2.FormalSeriesBounds
end
end

