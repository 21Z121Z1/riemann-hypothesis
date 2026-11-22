import Formalism.LocalToGlobal.CharacterGerms.Bundle0028
import Formalism.LocalToGlobal.CharacterGerms.CoeffPowCharFrobenius
import Formalism.LocalToGlobal.CharacterGerms.Bundle0029
import Formalism.LocalToGlobal.CharacterGerms.Bundle0030

-- bundled from Formalism.LocalToGlobal.CharacterGerms.CoeffFirstPairingLinear
section
noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace PhPowP

open PartialDerivEval

section Gen

variable {C : Type} [Field C] {V : VF C}

theorem frob_mv {σ : Type} {A B : MvPowerSeries σ C} (hA : IntS V A) (hB : IntS V B) (μ : σ →₀ ℕ) :
    V.MM (coeff μ ((A + B) ^ V.l - A ^ V.l - B ^ V.l)) := by
  have e : (A + B) ^ V.l - A ^ V.l - B ^ V.l = MvPowerSeries.C (V.l : C) *
      ∑ k ∈ Finset.Ioo 0 V.l, A ^ k * B ^ (V.l - k) * MvPowerSeries.C ((V.l.choose k / V.l : ℕ) : C) := by
    rw [add_pow_prime_eq' V.l_prime A B]
    simp only [map_natCast]
    ring
  rw [e, coeff_C_mul, map_sum, mul_comm]
  refine ValuationNonnegativity.mm_mul_int (VF.Ge.sum fun k _ => ?_) FrobP.mm_l
  rw [coeff_mul_C]
  exact VF.Ge.mul_int (intS_mul (intS_pow hA k) (intS_pow hB _) μ) (VF.ge_natCast _)

theorem frob_sum {σ ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ C) (hf : ∀ i, IntS V (f i))
    (μ : σ →₀ ℕ) : V.MM (coeff μ ((∑ i ∈ s, f i) ^ V.l - ∑ i ∈ s, f i ^ V.l)) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow V.l_prime.ne_zero, sub_zero, map_zero]
    exact ValuationNonnegativity.mm_zero
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb]
    have hS : IntS V (∑ i ∈ s, f i) := intS_sum _ fun i _ => hf i
    have e : (f b + ∑ i ∈ s, f i) ^ V.l - (f b ^ V.l + ∑ i ∈ s, f i ^ V.l) =
        ((f b + ∑ i ∈ s, f i) ^ V.l - f b ^ V.l - (∑ i ∈ s, f i) ^ V.l) +
          ((∑ i ∈ s, f i) ^ V.l - ∑ i ∈ s, f i ^ V.l) := by ring
    rw [e, map_add]
    exact ValuationNonnegativity.mm_add (frob_mv (hf b) hS μ) ih

theorem monomial_pow' {σ : Type} (β : σ →₀ ℕ) (a : C) :
    ∀ n : ℕ, (monomial β a) ^ n = monomial (n • β) (a ^ n)
  | 0 => by
    ext μ
    rw [pow_zero, zero_smul, pow_zero, coeff_one, coeff_monomial]
  | n + 1 => by
    rw [pow_succ, monomial_pow' β a n, monomial_mul_monomial, succ_nsmul, pow_succ]

def divL {σ : Type} (l : ℕ) (α : σ →₀ ℕ) : σ →₀ ℕ := Finsupp.mapRange (fun n => n / l) (Nat.zero_div l) α

theorem divL_apply {σ : Type} (l : ℕ) (α : σ →₀ ℕ) (t : σ) : divL l α t = α t / l := by
  simp [divL]

theorem frobPowMv {σ : Type} (F : MvPowerSeries σ C) (hF : IntS V F) (α : σ →₀ ℕ) :
    V.MM (coeff α (F ^ V.l) - if ∀ t, V.l ∣ α t then coeff (divL V.l α) F ^ V.l else 0) := by
  have hl0 : 0 < V.l := V.l_prime.pos
  obtain ⟨P, hPdef⟩ : ∃ P : MvPowerSeries σ C, P = ∑ β ∈ Finset.Iic α, monomial β (coeff β F) := ⟨_, rfl⟩
  have hmon : ∀ β, IntS V (monomial β (coeff β F)) := fun β μ => by
    rw [coeff_monomial]
    split_ifs
    · exact hF β
    · exact VF.Ge.zero 0
  have e1 : coeff α (F ^ V.l) = coeff α (P ^ V.l) := by
    obtain ⟨R, hR⟩ := sub_dvd_pow_sub_pow F P V.l
    have h0 : coeff α (F ^ V.l - P ^ V.l) = 0 := by
      rw [hR, coeff_mul]
      refine Finset.sum_eq_zero fun x hx => ?_
      have hx1 : x.1 ≤ α := by
        rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hx]
        exact le_self_add
      have hc : coeff x.1 (F - P) = 0 := by
        rw [map_sub, sub_eq_zero, hPdef, map_sum]
        simp only [coeff_monomial]
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_Iic.2 hx1)]
      rw [hc, zero_mul]
    rwa [map_sub, sub_eq_zero] at h0
  have e2 := frob_sum (Finset.Iic α) (fun β => monomial β (coeff β F)) hmon α
  have e3 : coeff α (∑ β ∈ Finset.Iic α, (monomial β (coeff β F)) ^ V.l) =
      if ∀ t, V.l ∣ α t then coeff (divL V.l α) F ^ V.l else 0 := by
    rw [map_sum]
    simp only [monomial_pow', coeff_monomial]
    split_ifs with hdiv
    · have hβ : α = V.l • divL V.l α := by
        ext t
        rw [Finsupp.smul_apply, smul_eq_mul, divL_apply, Nat.mul_div_cancel' (hdiv t)]
      rw [Finset.sum_eq_single (divL V.l α)]
      · rw [if_pos hβ]
      · intro b _ hb
        rw [if_neg]
        intro h
        apply hb
        ext t
        have := congrArg (fun f : σ →₀ ℕ => f t) (h.symm.trans hβ)
        simp only [Finsupp.smul_apply, smul_eq_mul] at this
        exact Nat.eq_of_mul_eq_mul_left hl0 this
      · intro h
        exfalso
        apply h
        rw [Finset.mem_Iic, Finsupp.le_def]
        intro t
        rw [divL_apply]
        exact Nat.div_le_self _ _
    · refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg]
      intro h
      apply hdiv
      intro t
      rw [h, Finsupp.smul_apply, smul_eq_mul]
      exact Nat.dvd_mul_right _ _
  rw [e1, ← e3, ← map_sub, hPdef]
  exact e2

end Gen

section Slice

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

end Slice

section FBs

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd)

end FBs

end PhPowP

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.LogCoordOfDpull
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

def DPullSt (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) : Prop :=
  ∀ (n : ℕ) (b : Fin n) (c : WVO I → C) (F : PS C n dd),
    pullN Y p (DofN (Y.B.FK C) b (fun i => ∑ w : WVO I, c w * (p w.1).u w.2.1 w.2.2 i) F) =
      ∑ w : WVO I, c w • MvPowerSeries.pderiv C (b, w) (pullN Y p F)

namespace VP

theorem cc_subst_eq {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ C) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  set c := MvPowerSeries.constantCoeff f with hc
  have hg : MvPowerSeries.constantCoeff (f - algebraMap C (MvPowerSeries σ C) c) = 0 := by
    simp [hc, MvPowerSeries.algebraMap_apply]
  have hf : f = algebraMap C (MvPowerSeries σ C) c + (f - algebraMap C (MvPowerSeries σ C) c) := by
    ring
  have h1 : MvPowerSeries.subst a (algebraMap C (MvPowerSeries σ C) c) =
      algebraMap C (MvPowerSeries τ C) c := by
    rw [← MvPowerSeries.coe_substAlgHom hs]
    exact (MvPowerSeries.substAlgHom hs).commutes c
  rw [hf, MvPowerSeries.subst_add hs, map_add, h1, constantCoeff_subst_zero ha hg]
  simp [MvPowerSeries.algebraMap_apply]

private theorem jetAt0_zero_left' {σ : Type} (G : MvPowerSeries σ C) :
    jetAt0 (0 : MvPolynomial σ C) G = 0 := by
  simp [jetAt0]

private theorem jetAt0_finset_sum_left {σ ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ C)
    (G : MvPowerSeries σ C) : jetAt0 (∑ j ∈ s, P j) G = ∑ j ∈ s, jetAt0 (P j) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jetAt0_zero_left']
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, tpjet_jetAt0_add, ih]

theorem jet_lin {σ ι : Type} [Fintype ι] (e : ι → σ) (q : MvPolynomial σ C) (c : ι → C) (G : MvPowerSeries σ C) :
    jetAt0 (q * ∑ w, MvPolynomial.C (c w) * MvPolynomial.X (e w)) G =
      jetAt0 q (∑ w, c w • MvPowerSeries.pderiv C (e w) G) := by
  rw [Finset.mul_sum, jetAt0_finset_sum_left, jet_sum_right]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← mul_assoc, jet_mul_X, jet_mul_C, jet_smul_right, dVar_eq_pderiv]

variable {Y : FBChart C V O dd} {p : ∀ o, PairData Y d (I o)}

theorem jet_iter (hD : DPullSt Y p) {n : ℕ} (b : Fin n) (u : Fin dd → C) (c : WVO I → C)
    (hu : u = ∑ w : WVO I, c w • (Y.raw (p w.1)).u w.2.1 w.2.2) (k : ℕ) :
    ∀ (q : MvPolynomial (Fin n × WVO I) C) (g : PS C n dd),
      jetAt0 q (pullN Y p ((DofN (Y.B.FK C) b u)^[k] g)) =
        jetAt0 (q * (∑ w : WVO I, MvPolynomial.C (c w) * MvPolynomial.X (b, w)) ^ k) (pullN Y p g) := by
  have hu' : u = fun i => ∑ w : WVO I, c w * (p w.1).u w.2.1 w.2.2 i := by
    rw [hu]; funext i; rw [Finset.sum_apply]; rfl
  subst hu'
  induction k with
  | zero => intro q g; simp
  | succ k ih =>
    intro q g
    rw [Function.iterate_succ_apply, ih, hD, ← jet_lin (fun w : WVO I => (b, w)), pow_succ, mul_assoc]

theorem jet_list (hD : DPullSt Y p) {n : ℕ} {ι : Type} (cp : ι → Fin n) (uv : ι → Fin dd → C) (co : ι → WVO I → C)
    (m : ι →₀ ℕ) (f : PS C n dd) :
    ∀ (ls : List ι), (∀ ℓ ∈ ls, m ℓ ≠ 0 → uv ℓ = ∑ w : WVO I, co ℓ w • (Y.raw (p w.1)).u w.2.1 w.2.2) →
    ∀ q : MvPolynomial (Fin n × WVO I) C,
      jetAt0 q (pullN Y p (ls.foldr (fun l g => (DofN (Y.B.FK C) (cp l) (uv l))^[m l] g) f)) =
        jetAt0 (q * (ls.map fun l => (∑ w : WVO I, MvPolynomial.C (co l w) * MvPolynomial.X (cp l, w)) ^ m l).prod)
          (pullN Y p f) := by
  intro ls
  induction ls with
  | nil => intro _ q; simp
  | cons l ls ih =>
    intro hls q
    have htl : ∀ ℓ ∈ ls, m ℓ ≠ 0 → uv ℓ = ∑ w : WVO I, co ℓ w • (Y.raw (p w.1)).u w.2.1 w.2.2 :=
      fun ℓ hℓ => hls ℓ (List.mem_cons_of_mem l hℓ)
    rw [List.foldr_cons, List.map_cons, List.prod_cons]
    by_cases hm : m l = 0
    · rw [hm, Function.iterate_zero, id, pow_zero, one_mul]
      exact ih htl q
    · rw [jet_iter hD (cp l) (uv l) (co l) (hls l List.mem_cons_self hm) (m l), ih htl, mul_assoc]

end VP

private theorem jetAt0_one_eq_constantCoeff {σ : Type} (G : MvPowerSeries σ C) :
    jetAt0 (1 : MvPolynomial σ C) G = MvPowerSeries.constantCoeff G := by
  rw [← MvPolynomial.C_1, jet_C, one_mul]

private theorem jetAt0_C_mul' {σ : Type} (a : C) (q : MvPolynomial σ C) (G : MvPowerSeries σ C) :
    jetAt0 (MvPolynomial.C a * q) G = a * jetAt0 q G := by
  rw [mul_comm, jet_mul_C]

theorem logCoord_of_dpull {Y : FBChart C V O dd} {p : ∀ o, PairData Y d (I o)} (hD : DPullSt Y p) :
    LogCoordSt Y p := by
  classical
  intro n ι _ cp uv P Q hQ F
  obtain ⟨co, hco, rfl⟩ := hQ
  have hcc : ∀ H : PS C n dd, MvPowerSeries.constantCoeff (pullN Y p H) = MvPowerSeries.constantCoeff H :=
    fun H => VP.cc_subst_eq (fun q => VP.cc_pullPt (Y := Y) (p := p) q) H
  have hmon : ∀ m ∈ P.support, MvPowerSeries.constantCoeff (DmonN (Y.B.FK C) cp uv m F) =
      jetAt0 (∏ ℓ, (∑ w : WVO I, MvPolynomial.C (co ℓ w) * MvPolynomial.X (cp ℓ, w)) ^ m ℓ) (pullN Y p F) := by
    intro m hm
    have hv : ∀ ℓ ∈ (Finset.univ : Finset ι).toList, m ℓ ≠ 0 →
        uv ℓ = ∑ w : WVO I, co ℓ w • (Y.raw (p w.1)).u w.2.1 w.2.2 := fun ℓ _ hℓ =>
      hco ℓ ((MvPolynomial.mem_vars ℓ).2 ⟨m, hm, Finsupp.mem_support_iff.2 hℓ⟩)
    have h1 := VP.jet_list hD cp uv co m F _ hv 1
    rw [one_mul, Finset.prod_map_toList, jetAt0_one_eq_constantCoeff, hcc] at h1
    exact h1
  rw [DpolyN, map_sum, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', VP.jetAt0_finset_sum_left]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [map_mul, hmon m hm, MvPolynomial.algebraMap_eq, jetAt0_C_mul']
  simp

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RaiseSecondFirstEqZero
section
noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace CocycleCoordinateParts

open PartialDerivEval CocycleIdentity

section Exps

variable {dd : ℕ}

def xup (α : Fin 1 × Fin dd →₀ ℕ) : Fin 2 × Fin dd →₀ ℕ := α.mapDomain fun p => ((0 : Fin 2), p.2)

def zup2 (β : Fin dd →₀ ℕ) : Fin 2 × Fin dd →₀ ℕ := β.mapDomain fun j => ((1 : Fin 2), j)

def zup (β : Fin dd →₀ ℕ) : Fin 3 × Fin dd →₀ ℕ := β.mapDomain fun j => ((2 : Fin 3), j)

def xpart (d : Fin 2 × Fin dd →₀ ℕ) : Fin 1 × Fin dd →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => d ((0 : Fin 2), p.2)

def zpart (d : Fin 2 × Fin dd →₀ ℕ) : Fin dd →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => d ((1 : Fin 2), j)

def lpart (α : Fin 3 × Fin dd →₀ ℕ) : Fin 2 × Fin dd →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => α (Fin.castSucc p.1, p.2)

def zpart3 (α : Fin 3 × Fin dd →₀ ℕ) : Fin dd →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => α ((2 : Fin 3), j)

end Exps

section Ser

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

def slice (β : Fin dd →₀ ℕ) (F : PS C 2 dd) : PS C 1 dd := fun α => coeff (xup α + zup2 β) F

end Ser

section Kill

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

variable {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd)

end Kill

section Closed

end Closed

end CocycleCoordinateParts

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePAllOps
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ RowTiePE0

variable {C : Type} [Field C]

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem allSet_add (V : VF C) (g : Fin 2) (hA : X.AddCvSt V) (hu : ∀ g c i, V.Ge 0 (X.u g c i))
    {L L' : ℕ → I g ⊕ JJ I g → C} : L ∈ X.AllSet V g → L' ∈ X.AllSet V g → L + L' ∈ X.AllSet V g := by
  intro hx hy
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hx
  obtain ⟨γ', lam', hγ', hlam', h1', h2'⟩ := hy
  obtain ⟨γ'', hγ'', hL, hS⟩ := hA γ γ' hγ hγ'
  have hty : ∀ n, PowerSeries.mk (fun m => (L + L') m n) =
      PowerSeries.mk (fun m => L m n) + PowerSeries.mk (fun m => L' m n) := fun n => by
    ext m
    simp [PowerSeries.coeff_mk]
  refine ⟨γ'', fun q => lam q + lam' q + (alongCv γ'' (X.sg (X.u (1 - g) q)) - alongCv γ (X.sg (X.u (1 - g) q)) -
    alongCv γ' (X.sg (X.u (1 - g) q))), hγ'', ?_, ?_, ?_⟩
  · intro q
    obtain ⟨c0, cI⟩ := hS (X.u (1 - g) q) (hu (1 - g) q)
    refine ⟨?_, fun n => ?_⟩
    · rw [map_add, map_add, (hlam q).1, (hlam' q).1, c0]
      simp
    · rw [map_add, map_add]
      exact (((hlam q).2 n).add ((hlam' q).2 n)).add (cI n)
  · intro i
    rw [hL i, h1 i, h1' i, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hty, smul_add]
  · intro q
    have hs : ∀ c : I g, (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => (L + L') m (Sum.inl c)) else 0) =
        (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => L m (Sum.inl c)) else 0) +
        (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => L' m (Sum.inl c)) else 0) := by
      intro c
      rw [hty]
      split_ifs
      · rw [smul_add]
      · rw [add_zero]
    simp only [hs]
    rw [Finset.sum_add_distrib, hty, h2 q, h2' q]
    abel

theorem allSet_repar {V : VF C} {g : Fin 2} (τ : PowerSeries C) (hτ : PowerSeries.constantCoeff τ = 0)
    (hint : ∀ f : PowerSeries C, (∀ n, V.Ge 0 (PowerSeries.coeff n f)) →
      ∀ n, V.Ge 0 (PowerSeries.coeff n (PowerSeries.subst τ f)))
    {x x' : ℕ → I g ⊕ JJ I g → C} (hx : x ∈ X.AllSet V g)
    (hxx : ∀ n, PowerSeries.mk (fun m => x' m n) = PowerSeries.subst τ (PowerSeries.mk fun m => x m n)) :
    x' ∈ X.AllSet V g := by
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hx
  have hS := PowerSeries.HasSubst.of_constantCoeff_zero' hτ
  have hcv : ∀ {σ : Type} (δ : σ → PowerSeries C), IsCv V δ → IsCv V fun i => PowerSeries.subst τ (δ i) := by
    intro σ δ hδ i
    refine ⟨?_, hint _ (hδ i).2⟩
    exact constantCoeff_subst_zero (σ := Unit) (fun _ => hτ) (hδ i).1
  refine ⟨fun i => PowerSeries.subst τ (γ i), fun q => PowerSeries.subst τ (lam q), hcv γ hγ, hcv lam hlam, ?_, ?_⟩
  · intro i
    rw [alongCv_repar (fun i => (hγ i).1) hτ, h1 i, ← PowerSeries.coe_substAlgHom hS, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, PowerSeries.coe_substAlgHom hS, hxx]
  · intro q
    rw [alongCv_repar (fun i => (hγ i).1) hτ, hxx, h2 q, ← PowerSeries.coe_substAlgHom hS, map_add, map_sub,
      map_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [map_smul, PowerSeries.coe_substAlgHom hS, hxx]
    · rw [map_zero]

theorem allSet_teich (V : VF C) (g : Fin 2) (c : C) (hc : V.Ge 0 c) {L : ℕ → I g ⊕ JJ I g → C} :
    L ∈ X.AllSet V g → (fun n k => c ^ n * L n k) ∈ X.AllSet V g := by
  intro hL
  refine X.allSet_repar (c • PowerSeries.X) (by simp) ?_ hL ?_
  · intro f hf n
    rw [← PowerSeries.rescale_eq_subst, PowerSeries.coeff_rescale]
    exact (hc.pow n).mul_int (hf n)
  · intro n
    rw [← PowerSeries.rescale_eq_subst]
    ext m
    rw [PowerSeries.coeff_rescale, PowerSeries.coeff_mk, PowerSeries.coeff_mk]

theorem allSet_lim (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hex0 : ∀ i, MvPowerSeries.constantCoeff (X.ex i) = 0)
    (hlgex : ∀ i, MvPowerSeries.subst X.ex (X.lg i) = MvPowerSeries.X i)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = MvPowerSeries.X i)
    {V : VF C} {g : Fin 2} {L : ℕ → ℕ → I g ⊕ JJ I g → C} {L' : ℕ → I g ⊕ JJ I g → C} :
    (∀ k, L k ∈ X.AllSet V g) → VLim V L L' → L' ∈ X.AllSet V g := by
  intro hx hlim
  choose γ lam hγ hlam hL hM using hx
  have hmk : ∀ n : I g ⊕ JJ I g,
      TendsS V (fun k => PowerSeries.mk (fun m => L k m n)) (PowerSeries.mk (fun m => L' m n)) :=
    fun n μ K => hlim K (μ ()) n
  let Lk : ℕ → κ → PowerSeries C := fun k j => ∑ c : I g, X.u g c j • PowerSeries.mk (fun m => L k m (Sum.inl c))
  let L1 : κ → PowerSeries C := fun j => ∑ c : I g, X.u g c j • PowerSeries.mk (fun m => L' m (Sum.inl c))
  have hLt : ∀ j, TendsS V (fun k => Lk k j) (L1 j) :=
    fun j => LimTy.tendsS_sum _ fun c _ => LimTy.tendsS_smul _ (hmk (Sum.inl c))
  have hγc : ∀ k i, MvPowerSeries.constantCoeff (γ k i) = 0 := fun k i => (hγ k i).1
  have hLkc : ∀ k j, MvPowerSeries.constantCoeff (Lk k j) = 0 := fun k j => by
    show MvPowerSeries.constantCoeff (∑ c : I g, X.u g c j • PowerSeries.mk (fun m => L k m (Sum.inl c))) = 0
    rw [← hL k j]
    exact constantCoeff_subst_zero (hγc k) (hlg0 j)
  have hL1c : ∀ j, MvPowerSeries.constantCoeff (L1 j) = 0 := fun j => by
    have h0 := hLt j 0
    have e : ∀ k, MvPowerSeries.coeff 0 (Lk k j) = 0 := fun k => by
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hLkc k j
    simp only [e] at h0
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h0.unique (tends_const 0)
  have hlgS := MvPowerSeries.hasSubst_of_constantCoeff_zero hlg0
  have hexS := MvPowerSeries.hasSubst_of_constantCoeff_zero hex0
  have hγeq : ∀ k i, γ k i = MvPowerSeries.subst (Lk k) (X.ex i) := by
    intro k i
    have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero (hγc k)
    have e : Lk k = fun j => MvPowerSeries.subst (γ k) (X.lg j) := funext fun j => (hL k j).symm
    rw [e, ← MvPowerSeries.subst_comp_subst_apply hlgS hS, hexlg, MvPowerSeries.subst_X hS]
  let γ' : κ → PowerSeries C := fun i => MvPowerSeries.subst L1 (X.ex i)
  have hγt : ∀ i, TendsS V (fun k => γ k i) (γ' i) := by
    intro i
    have e : (fun k => γ k i) = fun k => MvPowerSeries.subst (Lk k) (X.ex i) := funext fun k => hγeq k i
    rw [e]
    exact TendsS.subst (f := fun _ => X.ex i) hLkc hL1c hLt (TendsS.const _)
  have hγ' : IsCv V γ' := LimTy.isCv_lim hγt hγ
  have hγ'c : ∀ i, MvPowerSeries.constantCoeff (γ' i) = 0 := fun i => (hγ' i).1
  have hL1S := MvPowerSeries.hasSubst_of_constantCoeff_zero hL1c
  have hlog' : ∀ i, alongCv γ' (X.lg i) = L1 i := by
    intro i
    show MvPowerSeries.subst (fun j => MvPowerSeries.subst L1 (X.ex j)) (X.lg i) = L1 i
    rw [← MvPowerSeries.subst_comp_subst_apply hexS hL1S, hlgex, MvPowerSeries.subst_X hL1S]
  let lam' : JJ I g → PowerSeries C := fun q =>
    PowerSeries.mk (fun m => L' m (Sum.inr q)) + alongCv γ' (X.sg (X.u (1 - g) q)) -
      ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
        X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => L' m (Sum.inl c)) else 0
  have hlamk : ∀ k q, lam k q = PowerSeries.mk (fun m => L k m (Sum.inr q)) +
      alongCv (γ k) (X.sg (X.u (1 - g) q)) -
      ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
        X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => L k m (Sum.inl c)) else 0 := by
    intro k q
    rw [hM k q]
    ring
  have hlamt : ∀ q, TendsS V (fun k => lam k q) (lam' q) := by
    intro q
    have e : (fun k => lam k q) = fun k => PowerSeries.mk (fun m => L k m (Sum.inr q)) +
        alongCv (γ k) (X.sg (X.u (1 - g) q)) -
        ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun m => L k m (Sum.inl c)) else 0 :=
      funext fun k => hlamk k q
    rw [e]
    refine ((hmk (Sum.inr q)).add ?_).sub
      (LimTy.tendsS_sum _ fun c _ => LimTy.tendsS_ite _ (LimTy.tendsS_smul _ (hmk (Sum.inl c))))
    exact TendsS.subst (f := fun _ => X.sg (X.u (1 - g) q)) hγc hγ'c hγt (TendsS.const _)
  refine ⟨γ', lam', hγ', LimTy.isCv_lim hlamt hlam, hlog', fun q => ?_⟩
  simp only [lam']
  ring

end RawChart

end Formalism.L2.FormalSeriesBounds
end
end

