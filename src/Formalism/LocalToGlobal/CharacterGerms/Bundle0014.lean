import Formalism.LocalToGlobal.CharacterGerms.RowTieTop
import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjFB
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0069

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieChar
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

def FBChart.IsChar (Y : FBChart C V O dd) (χ : PS C 1 dd) : Prop :=
  IntS V χ ∧ MvPowerSeries.constantCoeff χ = 1 ∧
    ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] χ = ev (n := 2) ![pt C dd 0] χ * ev (n := 2) ![pt C dd 1] χ

def dlogC (χ : PS C 1 dd) (i : Fin dd) : C := MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) 1) χ

def PairData.yOf {Y : FBChart C V O dd} (p : PairData Y d I) (g : Fin 2) (χ : PS C 1 dd) (x : I g) : C :=
  ∑ i, dlogC χ i * p.u g x i

private theorem ge_zero_mul_of_vf (V : VF C) {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) : V.Ge 0 (a * b) := by
  unfold VF.Ge at *
  rw [V.v.map_mul]
  rw [WithTop.coe_zero] at *
  exact add_nonneg ha hb

private theorem ge_zero_finset_sum (V : VF C) {ι : Type} (s : Finset ι) (f : ι → C) (h : ∀ i ∈ s, V.Ge 0 (f i)) :
    V.Ge 0 (∑ i ∈ s, f i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty]
    unfold VF.Ge
    rw [AddValuation.map_zero]
    exact le_top
  · intro a s ha ih h
    rw [Finset.sum_insert ha]
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    unfold VF.Ge at h1 h2 ⊢
    exact le_trans (le_min h1 h2) (V.v.map_add _ _)

theorem PairData.yOf_int {Y : FBChart C V O dd} (p : PairData Y d I) (g : Fin 2) {χ : PS C 1 dd} (h : Y.IsChar χ)
    (x : I g) : V.Ge 0 (p.yOf g χ x) := by
  unfold PairData.yOf
  exact ge_zero_finset_sum V _ _ fun i _ => ge_zero_mul_of_vf V (h.1 _) (p.u_int g x i)

def CharGermSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I)
    (Hc : ∀ g, (Y.raw p).CartHyp V g) (χ : PS C 1 dd), Y.IsChar χ →
    ∀ (g : Fin 2) (S : ∀ g, Sys (RawChart.cart (Hc g))) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) →
      upG g (mvExp (∑ x : I g, p.yOf g χ x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈ IntGerm V t

def CHCharSt (Y : FBChart C V O dd) (p : PairData Y d I) : Prop :=
  ∀ g a, p.big g a → ∀ w : Fin p.n → I g → C, IsSat V w → (∀ c x, p.ty g x ≠ a → w c x = 0) →
    ∃ χ : Fin p.n → PS C 1 dd, (∀ ρ, Y.IsChar (χ ρ)) ∧
      ((Y.raw p).AltC →
        V.v (Matrix.of fun ρ c : Fin p.n => ∑ x, p.yOf g (χ ρ) x * w c x).det ≤
          (((p.n : ℝ) * gam V.l + ((p.j : ℝ) + p.j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ)) ∧
      ((∀ a, p.big g a) →
        V.v (Matrix.of fun ρ c : Fin p.n => ∑ x, p.yOf g (χ ρ) x * w c x).det ≤
          ((((p.j : ℝ) + p.j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ))

theorem chSt_of_char [NeZero d] (hG : CharGermSt) (Y : FBChart C V O dd) (p : PairData Y d I) (h : CHCharSt Y p)
    (Hc : ∀ g, (Y.raw p).CartHyp V g) : RawChart.CHSt Hc := by
  intro g a hbig w hw hw0
  obtain ⟨χ, hχ, h1, h2⟩ := h g a hbig w hw hw0
  refine ⟨fun ρ x => p.yOf g (χ ρ) x, fun ρ x => p.yOf_int g (hχ ρ) x, ?_, h1, h2⟩
  intro S t ht ρ
  exact hG C V O dd Y d I p Hc (χ ρ) (hχ ρ) g S t ht

section Chart

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

def CharacterHypothesisCharts : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : Lab E Orb d) (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab),
    lab.RankOK Dw → ∀ o, CHCharSt Y (pairOfLab ha hg o)

theorem chart_hypothesis_of_character (hG : CharGermSt) (h : CharacterHypothesisCharts Xo c) : CharacterHypothesisAllCharts Xo c := by
  intro hs T io y C3 C _ _ V ι hemb k Y hbc Orb d _ lab ha hg hrk o Hc
  exact chSt_of_char hG Y _ (h hs T io y C3 C V ι hemb k Y hbc Orb d lab ha hg hrk o) Hc

end Chart

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePDescJet
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.DescP

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Jet

variable {k : Type} [CommRing k] {n d : ℕ}

def HiOrd (K : ℕ) (g : PS k n d) : Prop :=
  ∀ μ : Fin n × Fin d →₀ ℕ, μ.degree < K → coeff μ g = 0

theorem HiOrd.mono {K K' : ℕ} {g : PS k n d} (h : HiOrd K' g) (hK : K ≤ K') : HiOrd K g := fun μ hμ => h μ (lt_of_lt_of_le hμ hK)

theorem HiOrd.mul_left {K : ℕ} {g : PS k n d} (h : HiOrd K g) (a : PS k n d) : HiOrd K (a * g) := by
  intro μ hμ
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun pq hpq => ?_
  have hpq' : pq.1 + pq.2 = μ := Finset.HasAntidiagonal.mem_antidiagonal.1 hpq
  have h2 : Finsupp.degree pq.2 < K :=
    lt_of_le_of_lt (by rw [← hpq', map_add]; exact Nat.le_add_left _ _) hμ
  rw [h _ h2, mul_zero]

theorem HiOrd.sum {K : ℕ} {α : Type} (s : Finset α) (g : α → PS k n d) (h : ∀ i ∈ s, HiOrd K (g i)) :
    HiOrd K (∑ i ∈ s, g i) := by
  intro μ hμ
  rw [map_sum]
  exact Finset.sum_eq_zero fun i hi => h i hi μ hμ

theorem HiOrd.deriv {K : ℕ} {g : PS k n d} (h : HiOrd (K + 1) g) (i : Fin n × Fin d) :
    HiOrd K (MvPowerSeries.pderiv k i g) := by
  intro μ hμ
  rw [MvPowerSeries.coeff_pderiv, h _ (by rw [map_add, Finsupp.degree_single]; omega), zero_mul]

theorem HiOrd.dofN {K : ℕ} {g : PS k n d} (h : HiOrd (K + 1) g) (F : Fin d → PS k 2 d) (b : Fin n)
    (u : Fin d → k) : HiOrd K (DofN F b u g) := by
  unfold DofN
  exact HiOrd.sum _ _ fun j _ => (h.deriv _).mul_left _

theorem HiOrd.iter (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) :
    ∀ (j K : ℕ) (g : PS k n d), HiOrd (K + j) g → HiOrd K ((DofN F b u)^[j] g)
  | 0, K, g, h => h
  | j + 1, K, g, h => by
    rw [Function.iterate_succ_apply]
    exact HiOrd.iter F b u j K _ (HiOrd.dofN (K := K + j) (by rw [add_assoc]; exact h) F b u)

theorem HiOrd.foldr (F : Fin d → PS k 2 d) {ι : Type} (cp : ι → Fin n) (u : ι → Fin d → k) (m : ι →₀ ℕ) :
    ∀ (L : List ι) (K : ℕ) (g : PS k n d), HiOrd (K + (L.map m).sum) g →
      HiOrd K (L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) g)
  | [], K, g, h => by simpa using h
  | l :: L, K, g, h => by
    rw [List.foldr_cons]
    refine HiOrd.iter F (cp l) (u l) (m l) K _ (HiOrd.foldr F cp u m L (K + m l) g ?_)
    rw [List.map_cons, List.sum_cons] at h
    rw [add_assoc]
    exact h

theorem HiOrd.dmonN (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (m : ι →₀ ℕ) {K : ℕ} {g : PS k n d} (h : HiOrd (K + m.degree) g) : HiOrd K (DmonN F cp u m g) := by
  unfold DmonN
  refine HiOrd.foldr F cp u m _ K g ?_
  rw [Finset.sum_map_toList, ← Finsupp.degree_eq_sum]
  exact h

theorem const_dpolyN_eq_zero (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) {g : PS k n d} (h : HiOrd (P.totalDegree + 1) g) :
    constantCoeff (DpolyN F cp u P g) = 0 := by
  unfold DpolyN
  rw [map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hd : Finsupp.degree m ≤ P.totalDegree := by
    have h1 := MvPolynomial.le_totalDegree hm
    rw [Finsupp.degree_apply]
    exact h1
  have h1 : HiOrd 1 (DmonN F cp u m g) := HiOrd.dmonN F cp u m (h.mono (by omega))
  rw [map_mul, ← coeff_zero_eq_constantCoeff_apply (DmonN F cp u m g), h1 0 (by simp), mul_zero]

theorem dofN_add (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (f g : PS k n d) :
    DofN F b u (f + g) = DofN F b u f + DofN F b u g := by
  simp only [DofN, map_add, mul_add, Finset.sum_add_distrib]

theorem dofN_smul (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (c : k) (f : PS k n d) :
    DofN F b u (c • f) = c • DofN F b u f := by
  simp only [DofN, Derivation.map_smul, Finset.smul_sum, mul_smul_comm]

theorem iter_add (A : PS k n d → PS k n d) (hA : ∀ f g, A (f + g) = A f + A g) :
    ∀ (j : ℕ) (f g : PS k n d), A^[j] (f + g) = A^[j] f + A^[j] g
  | 0, f, g => rfl
  | j + 1, f, g => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, hA,
      iter_add A hA j]

theorem iter_smul (A : PS k n d → PS k n d) (hA : ∀ (c : k) f, A (c • f) = c • A f) :
    ∀ (j : ℕ) (c : k) (f : PS k n d), A^[j] (c • f) = c • A^[j] f
  | 0, c, f => rfl
  | j + 1, c, f => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hA, iter_smul A hA j]

theorem foldr_add (F : Fin d → PS k 2 d) {ι : Type} (cp : ι → Fin n) (u : ι → Fin d → k) (m : ι →₀ ℕ) :
    ∀ (L : List ι) (f g : PS k n d),
      L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) (f + g) =
        L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) f + L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) g
  | [], f, g => rfl
  | l :: L, f, g => by
    rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, foldr_add F cp u m L f g,
      iter_add _ (dofN_add F (cp l) (u l))]

theorem foldr_smul (F : Fin d → PS k 2 d) {ι : Type} (cp : ι → Fin n) (u : ι → Fin d → k) (m : ι →₀ ℕ) :
    ∀ (L : List ι) (c : k) (f : PS k n d),
      L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) (c • f) =
        c • L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) f
  | [], c, f => rfl
  | l :: L, c, f => by
    rw [List.foldr_cons, List.foldr_cons, foldr_smul F cp u m L c f,
      iter_smul _ (dofN_smul F (cp l) (u l))]

theorem dpolyN_add (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (f g : PS k n d) :
    DpolyN F cp u P (f + g) = DpolyN F cp u P f + DpolyN F cp u P g := by
  simp only [DpolyN, DmonN, foldr_add, mul_add, Finset.sum_add_distrib]

theorem dpolyN_smul (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (c : k) (f : PS k n d) :
    DpolyN F cp u P (c • f) = c • DpolyN F cp u P f := by
  simp only [DpolyN, DmonN, foldr_smul, mul_smul_comm, Finset.smul_sum]

def nabL (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (G : PS k n d) : PS k n d →ₗ[k] k where
  toFun f := constantCoeff (DpolyN F cp u P (f * G))
  map_add' f g := by
    rw [add_mul, dpolyN_add, map_add]
  map_smul' c f := by
    rw [smul_mul_assoc, dpolyN_smul, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
      map_smul]
    rfl

def cst (D : ℕ) : Fin n × Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => D

theorem hiOrd_sub_trunc (f : PS k n d) (D : ℕ) :
    HiOrd (D + 1) (f - ((trunc' k (cst D) f : MvPolynomial _ k) : PS k n d)) := by
  intro μ hμ
  rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc', if_pos, sub_self]
  intro i
  have h1 : μ i ≤ Finsupp.degree μ := Finsupp.le_degree i μ
  simp [cst]
  omega

theorem coe_eq_sum (p : MvPolynomial (Fin n × Fin d) k) :
    (p : PS k n d) = ∑ μ ∈ p.support, MvPolynomial.coeff μ p • monomial μ (1 : k) := by
  ext ν
  rw [MvPolynomial.coeff_coe, map_sum]
  simp only [map_smul, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · simpa using h

theorem nabL_trunc (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (G : PS k n d) (f : PS k n d) :
    nabL F cp u P G f = ∑ μ ∈ (trunc' k (cst P.totalDegree) f).support,
      MvPolynomial.coeff μ (trunc' k (cst P.totalDegree) f) * nabL F cp u P G (monomial μ (1 : k)) := by
  set T : PS k n d := ((trunc' k (cst P.totalDegree) f : MvPolynomial _ k) : PS k n d) with hTdef
  have h0 : nabL F cp u P G (f - T) = 0 := by
    show constantCoeff (DpolyN F cp u P ((f - T) * G)) = 0
    rw [mul_comm]
    exact const_dpolyN_eq_zero F cp u P ((hiOrd_sub_trunc f P.totalDegree).mul_left G)
  have hsplit : nabL F cp u P G f = nabL F cp u P G (f - T) + nabL F cp u P G T := by
    rw [← map_add, sub_add_cancel]
  rw [hsplit, h0, zero_add, hTdef, coe_eq_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

theorem dpolyN_sub (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (g : PS k n d) (S : Finset (ι →₀ ℕ)) (hS : P.support ⊆ S) :
    DpolyN F cp u P g = ∑ m ∈ S, MvPowerSeries.C (P.coeff m) * DmonN F cp u m g := by
  unfold DpolyN
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, zero_mul]

theorem const_dpolyN_lin (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    {α : Type} (s : Finset α) (c : α → k) (Q : α → MvPolynomial ι k) (g : PS k n d) :
    constantCoeff (DpolyN F cp u (∑ i ∈ s, c i • Q i) g) =
      ∑ i ∈ s, c i * constantCoeff (DpolyN F cp u (Q i) g) := by
  set S := (∑ i ∈ s, c i • Q i).support ∪ s.biUnion (fun i => (Q i).support) with hS
  rw [dpolyN_sub F cp u _ g S Finset.subset_union_left]
  have hQ : ∀ i ∈ s, DpolyN F cp u (Q i) g = ∑ m ∈ S, MvPowerSeries.C ((Q i).coeff m) * DmonN F cp u m g :=
    fun i hi => dpolyN_sub F cp u _ g S
      (fun m hm => Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, hi, hm⟩))
  have hR : ∑ i ∈ s, c i * constantCoeff (DpolyN F cp u (Q i) g) =
      ∑ i ∈ s, c i * constantCoeff (∑ m ∈ S, MvPowerSeries.C ((Q i).coeff m) * DmonN F cp u m g) :=
    Finset.sum_congr rfl fun i hi => by rw [hQ i hi]
  rw [hR]
  simp only [map_sum, map_mul, MvPowerSeries.constantCoeff_C, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_smul, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring

end Jet

theorem exists_fin_sum {α M : Type} [AddCommMonoid M] (s : Finset α) (g : α → M) :
    ∃ (N : ℕ) (e : Fin N → α), (∀ j, e j ∈ s) ∧ ∑ x ∈ s, g x = ∑ j, g (e j) := ⟨s.card, fun j => (s.equivFin.symm j : α), fun j => (s.equivFin.symm j).2, by
    rw [← Finset.sum_coe_sort s, ← Equiv.sum_comp s.equivFin.symm]⟩

end Formalism.L2.FormalSeriesBounds.DescP
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePLSmallCv
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePLSmall

open PartialDerivEval RowTiePE0 RowTiePProj

section Bd

variable {C : Type} [Field C] {V : VF C}

def Bdd (V : VF C) (s : ℕ → C) : Prop := ∃ K : ℝ, ∀ n, V.Ge K (s n)

theorem bdd_const (x : C) : Bdd V (fun _ => x) := by
  obtain ⟨K, hK⟩ := exists_ge (V := V) x
  exact ⟨K, fun _ => hK⟩

theorem Bdd.add {s t : ℕ → C} (hs : Bdd V s) (ht : Bdd V t) : Bdd V (fun n => s n + t n) := by
  obtain ⟨K, hK⟩ := hs
  obtain ⟨L, hL⟩ := ht
  exact ⟨min K L, fun n => ((hK n).mono (min_le_left _ _)).add ((hL n).mono (min_le_right _ _))⟩

theorem Bdd.mul {s t : ℕ → C} (hs : Bdd V s) (ht : Bdd V t) : Bdd V (fun n => s n * t n) := by
  obtain ⟨K, hK⟩ := hs
  obtain ⟨L, hL⟩ := ht
  exact ⟨K + L, fun n => (hK n).mul (hL n)⟩

theorem Bdd.sum {ι : Type} (S : Finset ι) {s : ι → ℕ → C} (h : ∀ i ∈ S, Bdd V (s i)) :
    Bdd V (fun n => ∑ i ∈ S, s i n) := by
  first | exact GlobalTheory.ScalarStatement.main .. | (apply GlobalTheory.ScalarStatement.main <;> assumption) | (intros; apply GlobalTheory.ScalarStatement.main <;> assumption) | (apply @GlobalTheory.ScalarStatement.main <;> assumption) | (intros; apply @GlobalTheory.ScalarStatement.main <;> assumption) | (apply @GlobalTheory.ScalarStatement.main <;> first | assumption | infer_instance) | exact @GlobalTheory.ScalarStatement.main C ‹_› V ι S s h | exact @GlobalTheory.ScalarStatement.main C ‹_› V ι S s | exact @GlobalTheory.ScalarStatement.main C ‹_› V ι S | exact @GlobalTheory.ScalarStatement.main C ‹_› V ι | exact @GlobalTheory.ScalarStatement.main C ‹_› V | exact @GlobalTheory.ScalarStatement.main C ‹_› | exact @GlobalTheory.ScalarStatement.main C

theorem tends_mul_bdd {s t : ℕ → C} (hs : Bdd V s) (ht : Tends V t 0) : Tends V (fun n => s n * t n) 0 := by
  intro w
  obtain ⟨K, hK⟩ := hs
  obtain ⟨n0, h0⟩ := ht (w - K)
  refine ⟨n0, fun n hn => ?_⟩
  have h := (hK n).mul (h0 n hn)
  have e : (0 : C) - s n * t n = s n * (0 - t n) := by ring
  rw [e]
  exact h.mono (by linarith)

variable {σ : Type}

def BddS (V : VF C) (f : ℕ → MvPowerSeries σ C) : Prop := ∀ μ, Bdd V (fun n => coeff μ (f n))

theorem BddS.const (g : MvPowerSeries σ C) : BddS V (fun _ => g) := fun _ => bdd_const _

theorem BddS.of_int {f : ℕ → MvPowerSeries σ C} (h : ∀ n, IntS V (f n)) : BddS V f :=
  fun μ => ⟨0, fun n => h n μ⟩

theorem BddS.mul {f g : ℕ → MvPowerSeries σ C} (hf : BddS V f) (hg : BddS V g) :
    BddS V (fun n => f n * g n) := fun μ => by
  classical
  simp only [coeff_mul]
  exact Bdd.sum _ fun p _ => (hf p.1).mul (hg p.2)

theorem BddS.pow {f : ℕ → MvPowerSeries σ C} (hf : BddS V f) (k : ℕ) : BddS V (fun n => f n ^ k) := by
  induction k with
  | zero => simpa using BddS.const (V := V) (1 : MvPowerSeries σ C)
  | succ k ih => simpa only [pow_succ] using ih.mul hf

theorem BddS.prod {ι : Type} (S : Finset ι) {f : ι → ℕ → MvPowerSeries σ C} (h : ∀ i ∈ S, BddS V (f i)) :
    BddS V (fun n => ∏ i ∈ S, f i n) := by
  first | exact UpperTheory.Reformulated.B.BoundedSums.prod .. | (apply UpperTheory.Reformulated.B.BoundedSums.prod <;> assumption) | (intros; apply UpperTheory.Reformulated.B.BoundedSums.prod <;> assumption) | (apply @UpperTheory.Reformulated.B.BoundedSums.prod <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.BoundedSums.prod <;> assumption) | (apply @UpperTheory.Reformulated.B.BoundedSums.prod <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V σ ι S f h | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V σ ι S f | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V σ ι S | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V σ ι | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V σ | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› | exact @UpperTheory.Reformulated.B.BoundedSums.prod C

theorem BddS.fprod {ι : Type} (d : ι →₀ ℕ) {a : ℕ → ι → MvPowerSeries σ C} (ha : ∀ i, BddS V (fun n => a n i)) :
    BddS V (fun n => d.prod fun i e => a n i ^ e) := by
  unfold Finsupp.prod
  exact BddS.prod _ fun i _ => (ha i).pow _

theorem BddS.subst [Finite σ] {τ : Type} {a : ℕ → σ → MvPowerSeries τ C} {f : ℕ → MvPowerSeries σ C}
    (ha0 : ∀ n s, constantCoeff (a n s) = 0) (ha : ∀ s, BddS V (fun n => a n s)) (hf : BddS V f) :
    BddS V (fun n => MvPowerSeries.subst (a n) (f n)) := fun μ => by
  have e : (fun n => coeff μ (MvPowerSeries.subst (a n) (f n))) = fun n =>
      ∑ d ∈ (Finsupp.finite_of_degree_le (σ := σ) (Finsupp.degree μ)).toFinset,
        coeff d (f n) * coeff μ (d.prod fun s e => a n s ^ e) :=
    funext fun n => coeff_subst_eq_sum (ha0 n) _ _
  rw [e]
  exact Bdd.sum _ fun d _ => (hf d).mul (BddS.fprod d ha μ)

theorem TendsS.mul_bdd {f g : ℕ → MvPowerSeries σ C} (hf : BddS V f) (hg : TendsS V g 0) :
    TendsS V (fun n => f n * g n) 0 := fun μ => by
  classical
  show Tends V (fun n => coeff μ (f n * g n)) (coeff μ 0)
  simp only [coeff_mul, map_zero]
  have h := Tends.sum (V := V) (Finset.HasAntidiagonal.antidiagonal μ)
    (s := fun p n => coeff p.1 (f n) * coeff p.2 (g n)) (x := fun _ => 0)
    fun p _ => tends_mul_bdd (hf p.1) (by simpa using hg p.2)
  simpa using h

def Close (V : VF C) (f g : ℕ → MvPowerSeries σ C) : Prop := TendsS V (fun n => f n - g n) 0

theorem Close.refl (f : ℕ → MvPowerSeries σ C) : Close V f f := by
  unfold Close
  simpa using TendsS.const (V := V) (0 : MvPowerSeries σ C)

theorem Close.mul {a a' b b' : ℕ → MvPowerSeries σ C} (ha : BddS V a) (hb' : BddS V b') (h1 : Close V a b)
    (h2 : Close V a' b') : Close V (fun n => a n * a' n) (fun n => b n * b' n) := by
  have e : (fun n => a n * a' n - b n * b' n) = fun n => a n * (a' n - b' n) + b' n * (a n - b n) :=
    funext fun n => by ring
  unfold Close
  rw [e]
  simpa using (TendsS.mul_bdd ha h2).add (TendsS.mul_bdd hb' h1)

theorem Close.pow {a b : ℕ → MvPowerSeries σ C} (ha : BddS V a) (hb : BddS V b) (h : Close V a b) (k : ℕ) :
    Close V (fun n => a n ^ k) (fun n => b n ^ k) := by
  induction k with
  | zero => simpa using Close.refl (V := V) (fun _ => (1 : MvPowerSeries σ C))
  | succ k ih => simpa only [pow_succ] using Close.mul (ha.pow k) hb ih h

theorem Close.prod {ι : Type} (S : Finset ι) {a b : ι → ℕ → MvPowerSeries σ C} (ha : ∀ i ∈ S, BddS V (a i))
    (hb : ∀ i ∈ S, BddS V (b i)) (h : ∀ i ∈ S, Close V (a i) (b i)) :
    Close V (fun n => ∏ i ∈ S, a i n) (fun n => ∏ i ∈ S, b i n) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using Close.refl (V := V) (fun _ => (1 : MvPowerSeries σ C))
  | insert x S hx ih =>
    simp only [Finset.prod_insert hx]
    exact Close.mul (ha x (Finset.mem_insert_self x S)) (BddS.prod S fun i hi => hb i (Finset.mem_insert_of_mem hi))
      (h x (Finset.mem_insert_self x S))
      (ih (fun i hi => ha i (Finset.mem_insert_of_mem hi)) (fun i hi => hb i (Finset.mem_insert_of_mem hi))
        fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Close.fprod {ι : Type} (d : ι →₀ ℕ) {a b : ℕ → ι → MvPowerSeries σ C} (ha : ∀ i, BddS V (fun n => a n i))
    (hb : ∀ i, BddS V (fun n => b n i)) (h : ∀ i, Close V (fun n => a n i) (fun n => b n i)) :
    Close V (fun n => d.prod fun i e => a n i ^ e) (fun n => d.prod fun i e => b n i ^ e) := by
  unfold Finsupp.prod
  exact Close.prod _ (fun i _ => (ha i).pow _) (fun i _ => (hb i).pow _) fun i _ => Close.pow (ha i) (hb i) (h i) _

theorem Close.subst [Finite σ] {τ : Type} {a b : ℕ → σ → MvPowerSeries τ C}
    (ha0 : ∀ n s, constantCoeff (a n s) = 0) (hb0 : ∀ n s, constantCoeff (b n s) = 0)
    (ha : ∀ s, BddS V (fun n => a n s)) (hb : ∀ s, BddS V (fun n => b n s))
    (h : ∀ s, Close V (fun n => a n s) (fun n => b n s)) (f : MvPowerSeries σ C) :
    Close V (fun n => MvPowerSeries.subst (a n) f) (fun n => MvPowerSeries.subst (b n) f) := fun μ => by
  show Tends V (fun n => coeff μ (MvPowerSeries.subst (a n) f - MvPowerSeries.subst (b n) f)) (coeff μ 0)
  have e : (fun n => coeff μ (MvPowerSeries.subst (a n) f - MvPowerSeries.subst (b n) f)) = fun n =>
      ∑ d ∈ (Finsupp.finite_of_degree_le (σ := σ) (Finsupp.degree μ)).toFinset,
        coeff d f * coeff μ ((d.prod fun s e => a n s ^ e) - (d.prod fun s e => b n s ^ e)) := funext fun n => by
    rw [map_sub, coeff_subst_eq_sum (ha0 n), coeff_subst_eq_sum (hb0 n), ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by rw [map_sub, mul_sub]
  rw [e, map_zero]
  have h2 := Tends.sum (V := V) (Finsupp.finite_of_degree_le (σ := σ) (Finsupp.degree μ)).toFinset
    (s := fun d n => coeff d f * coeff μ ((d.prod fun s e => a n s ^ e) - (d.prod fun s e => b n s ^ e)))
    (x := fun _ => 0) fun d _ => by
      have h3 := (tends_const (V := V) (coeff d f)).mul (Close.fprod d ha hb h μ)
      simpa using h3
  simpa using h2

end Bd

end RowTiePLSmall

end Formalism.L2.FormalSeriesBounds
end
end

