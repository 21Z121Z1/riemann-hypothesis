import Development.DiscreteGroups.GlobalIrreducibility.Bundle0038
import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0032
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0037
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0001
import Development.DiscreteGroups.GlobalIrreducibility.DzIneEq
import Development.DiscreteGroups.GlobalIrreducibility.ExistsIneOfVEqOne
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0012
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0033

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DotjUpdate
section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix DiscreteGroups.sglob.LConvGenM DiscreteGroups.sglob.LConvGenF

namespace DiscreteGroups.sglob.LConvGenR

section Dot

variable {k : Type} [Field k] {n : ℕ}

theorem dotj_add (j : ℕ) (ξ c d : Fin n → k) : dotj j ξ (c + d) = dotj j ξ c + dotj j ξ d := by
  simp only [dotj, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [mul_add]

theorem dotj_single (j : ℕ) (ξ : Fin n → k) (a : Fin n) (x : k) :
    dotj j ξ (Pi.single a x) = if a.val < j then ξ a * x else 0 := by
  rw [dotj, Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem dotj_update (j : ℕ) (ξ c : Fin n → k) (a : Fin n) (x : k) (hc : c a = 0) :
    dotj j (Function.update ξ a x) c = dotj j ξ c := by
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = a
  · subst hi; simp [hc]
  · rw [Function.update_of_ne hi]

end Dot

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GL (Fin n) k) V) (ψ : AddChar k Circle)

theorem KUS_empty (j : ℕ) (ξ : Fin n → k) : KUS π ψ j ∅ ξ = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨c, hc, v, rfl⟩
  have : c = 0 := funext fun r => hc r (Finset.notMem_empty r)
  subst this
  have h0 : dotj j ξ (0 : Fin n → k) = 0 := Finset.sum_eq_zero fun i _ => by split_ifs <;> simp
  rw [colU_zero, h0, AddChar.map_zero_eq_one, Circle.coe_one, one_smul, map_one, Module.End.one_apply, sub_self]

theorem smooth_col (hs : IsSmooth π) (j : ℕ) (hj : j < n) (a : Fin n) (v : V) :
    ∃ s : kˣ, ∀ h ∈ ball s, π (colU j (Pi.single a h)) v = v := by
  by_cases ha : a.val < j
  · have hne : a ≠ (⟨j, hj⟩ : Fin n) := fun e => by
      have := congrArg Fin.val e; simp at this; omega
    have hU : {g : GL (Fin n) k | π g v = v} ∈ nhds (1 : GL (Fin n) k) := (hs v).mem_nhds (by simp)
    have h0 : GlobalTheory.RootUp.elem hne (0 : k) = 1 := Units.ext (by simp [GlobalTheory.RootUp.val_elem])
    have hpre : (GlobalTheory.RootUp.elem hne) ⁻¹' {g : GL (Fin n) k | π g v = v} ∈ nhds (0 : k) :=
      (GlobalTheory.RootUp.continuous_elem hne).continuousAt.preimage_mem_nhds (by rw [h0]; exact hU)
    obtain ⟨s, hs'⟩ := exists_cball_subset hpre
    refine ⟨s, fun h hh => ?_⟩
    rw [colU_single_of_lt j hj ha]
    exact hs' hh
  · exact ⟨1, fun h _ => by rw [colU_single_of_ge j (by omega), map_one, Module.End.one_apply]⟩

end DiscreteGroups.sglob.LConvGenR
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzFeMain
section
noncomputable section

set_option linter.unusedSimpArgs false

open GlobalTheory.GLq GlobalTheory.Whittaker GlobalTheory.SmGL Matrix
open scoped Classical

namespace DiscreteGroups.sglob.DzFe

theorem fe : FunctionalEquationAtIndex := by
  intro g _ m ψ₀ hψ τ hτ γ hγ l hl j hj v hA hB
  have hm : 0 < m := by omega
  have hg : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero
  have hg1 : (g : ℂ) - 1 ≠ 0 := by
    have : g ≠ 1 := (Fact.out : g.Prime).ne_one
    exact sub_ne_zero.2 (by exact_mod_cast this)
  set K : ℕ := Fintype.card ({i : JIdx m j // i ≠ j0 m j} → ZMod g) with hK
  have hK0 : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hcardJ : (g : ℂ) ^ Fintype.card (JIdx m j) = (K : ℂ) * g := by
    have := sum_split (g := g) (m := m) j (fun _ => (1 : ℂ))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_fun, ZMod.card,
      Nat.cast_pow] at this
    rw [hK, Fintype.card_fun, ZMod.card, Nat.cast_pow]
    exact this
  set X : ℂ := l (τ.ρ (cyc g (m + 1))⁻¹ v) with hX
  have hL : ∑ N : SIdx m → ZMod g, ∑ b : JIdx m j → ZMod g,
      (ψ₀ (-superDiag (umGL N)) : ℂ) * l (sv ψ₀ τ (Um N * Hm (bcol b)) v) =
      (g : ℂ) ^ Fintype.card (SIdx m) * ((K : ℂ) * (((g : ℂ) - 1) * (γ * l v))) := by
    rw [Finset.sum_congr rfl (fun N _ => Finset.sum_congr rfl (fun b _ => lhs_term ψ₀ τ hγ hτ hm l hl v hA N b))]
    have hb : ∑ b : JIdx m j → ZMod g, (if b (j0 m j) = 0 then (0 : ℂ) else γ * l v) =
        (K : ℂ) * (((g : ℂ) - 1) * (γ * l v)) := by
      have hs := sum_split (g := g) (m := m) j (fun s => if s = 0 then (0 : ℂ) else γ * l v)
      rw [hs]
      congr 1
      have h2 : ∑ s : ZMod g, (if s = 0 then (0 : ℂ) else γ * l v) =
          ∑ _s : ZMod g, γ * l v - ∑ s : ZMod g, (if s = 0 then γ * l v else 0) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun s _ => by split_ifs <;> ring)
      rw [h2, Finset.sum_const, Finset.card_univ, ZMod.card, Finset.sum_ite_eq' Finset.univ (0 : ZMod g),
        if_pos (Finset.mem_univ _), nsmul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun N _ => hb), Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card,
      nsmul_eq_mul]
    push_cast
    ring
  have e1 : ∀ (N : SIdx m → ZMod g) (b : JIdx m j → ZMod g),
      (ψ₀ (-superDiag (umGL N)) : ℂ) * l (sv ψ₀ τ (Um N * Hm (bcol b)) v) =
      ∑ y : Gn g (m + 1), (ψ₀ (-superDiag (umGL N)) : ℂ) *
        (ψ₀ (trace (Um N * Hm (bcol b) * (y : Mt g (m + 1)))) : ℂ) * l (τ.ρ y⁻¹ v) := by
    intro N b
    simp only [sv, map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun y _ => by ring)
  have hR : ∑ N : SIdx m → ZMod g, ∑ b : JIdx m j → ZMod g,
      (ψ₀ (-superDiag (umGL N)) : ℂ) * l (sv ψ₀ τ (Um N * Hm (bcol b)) v) =
      (g : ℂ) ^ Fintype.card (JIdx m j) * (g : ℂ) ^ Fintype.card (SIdx m) *
        ((Fintype.card ((SIdx m → ZMod g) × (ZMod g)ˣ × (WIdx m j → ZMod g)) : ℂ) * X) := by
    calc _ = ∑ N : SIdx m → ZMod g, ∑ b : JIdx m j → ZMod g, ∑ y : Gn g (m + 1),
          (ψ₀ (-superDiag (umGL N)) : ℂ) * (ψ₀ (trace (Um N * Hm (bcol b) * (y : Mt g (m + 1)))) : ℂ) *
            l (τ.ρ y⁻¹ v) := Finset.sum_congr rfl (fun N _ => Finset.sum_congr rfl (fun b _ => e1 N b))
      _ = ∑ N : SIdx m → ZMod g, ∑ y : Gn g (m + 1), ∑ b : JIdx m j → ZMod g,
          (ψ₀ (-superDiag (umGL N)) : ℂ) * (ψ₀ (trace (Um N * Hm (bcol b) * (y : Mt g (m + 1)))) : ℂ) *
            l (τ.ρ y⁻¹ v) := Finset.sum_congr rfl (fun N _ => Finset.sum_comm)
      _ = ∑ y : Gn g (m + 1), ∑ N : SIdx m → ZMod g, ∑ b : JIdx m j → ZMod g,
          (ψ₀ (-superDiag (umGL N)) : ℂ) * (ψ₀ (trace (Um N * Hm (bcol b) * (y : Mt g (m + 1)))) : ℂ) *
            l (τ.ρ y⁻¹ v) := Finset.sum_comm
      _ = ∑ y : Gn g (m + 1), (∑ N : SIdx m → ZMod g, ∑ b : JIdx m j → ZMod g,
          (ψ₀ (-superDiag (umGL N)) : ℂ) * (ψ₀ (trace (Um N * Hm (bcol b) * (y : Mt g (m + 1)))) : ℂ)) *
            l (τ.ρ y⁻¹ v) := Finset.sum_congr rfl (fun y _ => by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl (fun N _ => by rw [Finset.sum_mul]))
      _ = ∑ y : Gn g (m + 1), (if IsY j (y : Mt g (m + 1)) then
          (g : ℂ) ^ Fintype.card (JIdx m j) * (g : ℂ) ^ Fintype.card (SIdx m) *
            (ψ₀ (trace (y : Mt g (m + 1)) - (y : Mt g (m + 1)) 0 0) : ℂ) else 0) * l (τ.ρ y⁻¹ v) :=
          Finset.sum_congr rfl (fun y _ => by rw [kern ψ₀ hψ j])
      _ = (g : ℂ) ^ Fintype.card (JIdx m j) * (g : ℂ) ^ Fintype.card (SIdx m) *
          ∑ y : Gn g (m + 1), (if IsY j (y : Mt g (m + 1)) then
            (ψ₀ (trace (y : Mt g (m + 1)) - (y : Mt g (m + 1)) 0 0) : ℂ) * l (τ.ρ y⁻¹ v) else 0) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun y _ => by split_ifs <;> ring)
      _ = _ := by rw [rhs_sum ψ₀ τ hj l hl v hB]
  have e := hL.symm.trans hR
  have hg1le : 1 ≤ g := (Fact.out : g.Prime).one_le
  rw [hcardJ, card_P, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_sub hg1le,
    Nat.cast_one] at e
  have hne : (g : ℂ) ^ Fintype.card (SIdx m) * (K : ℂ) * ((g : ℂ) - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hg) hK0) hg1
  have key : γ * l v = (g : ℂ) * (g : ℂ) ^ Fintype.card (SIdx m) * (g : ℂ) ^ Fintype.card (WIdx m j) * X :=
    mul_left_cancel₀ hne (by linear_combination e)
  have hexp : (m + 1) * m / 2 + m - j = Fintype.card (SIdx m) + Fintype.card (WIdx m j) + 1 := by
    rw [card_SIdx, card_WIdx]
    generalize (m + 1) * m / 2 = A
    omega
  rw [hexp, pow_add, pow_add, pow_one, key]
  ring

end DiscreteGroups.sglob.DzFe
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.GalUnitCompat
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module ValuativeRel

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem gal_unit_compat (hTR : TameRec) {E E' L Ω : Type} [Field E] [NumberField E] [IsTotallyComplex E]
    [Field E'] [NumberField E'] [IsTotallyComplex E'] [Field L] [NumberField L] [IsTotallyComplex L] [Field Ω]
    [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [Algebra L Ω]
    [IsAlgClosure E Ω] [IsAlgClosure E' Ω] [IsAlgClosure L Ω] (g : ℕ) [Fact g.Prime] (n : ℕ) (hn : 0 < n)
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w') (v : HeightOneSpectrum (𝓞 L)) (hv : IsPlaceOver A v)
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
    (hg : ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2) (hN : normV w' = g ^ n)
    (hgv : ((g : ℕ) : 𝓞 L) ∈ v.asIdeal) (hgv2 : ((g : ℕ) : 𝓞 L) ∉ v.asIdeal ^ 2) (hvN : normV v = g ^ n)
    (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a')
    (aL : Weil hv →* (v.adicCompletion L)ˣ) (haL : IsLocalArtin hv aL)
    (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K) (hr : Function.Surjective red)
    (hk : RingHom.ker red = w'.asIdeal)
    (π : Ω) (hπ : π ^ (g ^ n - 1) = (g : Ω))
    (r : Weil hv →* Weil h) (hrr : ∀ (σ : Weil hv) (z : Ω), (r σ : G E Ω) z = (σ : G L Ω) z)
    (κ : 𝓀[v.adicCompletion L] ≃+* K)
    (hκ : ∀ (u : 𝒪[v.adicCompletion L]) (y : 𝓞 L) (x : 𝓞 E'),
      Valued.v ((u : v.adicCompletion L) - algebraMap L (v.adicCompletion L) (y : L)) < 1 →
      A.valuation (algebraMap L Ω (y : L) - algebraMap E' Ω (x : E')) < 1 →
      κ (IsLocalRing.residue 𝒪[v.adicCompletion L] u) = red x)
    (χ₀ : (ZMod g)ˣ →* ℂˣ) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hlc : LiftsChar i χ₀ χ)
    (x : 𝒪[v.adicCompletion L]ˣ) :
    ∃ (t : Ine (F := L) A) (t' : Ine (F := E') A) (x' : 𝓞 E') (hx0 : red x' ≠ 0),
      aL (ineIncl hv t) = Units.map (algebraMap 𝒪[v.adicCompletion L] (v.adicCompletion L) :
        𝒪[v.adicCompletion L] →* v.adicCompletion L) x ∧
      r (ineIncl hv t) = ineIncl h (resI t') ∧
      Valued.v ((a' (ineIncl h' t') : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x' : E')) < 1 ∧
      Units.map (κ : 𝓀[v.adicCompletion L] →* K)
        (Units.map (IsLocalRing.residue 𝒪[v.adicCompletion L] : 𝒪[v.adicCompletion L] →* 𝓀[v.adicCompletion L]) x) =
        Units.mk0 (red x') hx0 ∧
      χ (a (r (ineIncl hv t))) = χ₀ (Units.map (Algebra.norm (ZMod g) : K →* ZMod g) (Units.mk0 (red x') hx0)) := by
  classical
  set k := v.adicCompletion L
  have hq : normV w = g := normV_eq_of_padic w g i hi
  have hgw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := natCast_mem_of_normV w g 1 one_pos (by rw [hq, pow_one])
  have hgw2 : ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := g_not_mem_sq w g i hi
  have hgw' : ((g : ℕ) : 𝓞 E') ∈ w'.asIdeal := natCast_mem_of_normV w' g n hn hN
  have hcardK : Nat.card K = g ^ n := by
    have e : (𝓞 E' ⧸ w'.asIdeal) ≃+* K :=
      (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hr)
    rw [← hN, normV, Nat.card_congr e.toEquiv]

  set u : kˣ := Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) x with hu
  have hu1 : Valued.v (u : k) = 1 := by
    have h1 : valuation k ((x : 𝒪[k]) : k) = 1 :=
      ((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one).mp x.isUnit
    exact (val_eq_one_iff (u : k)).mp h1
  obtain ⟨t, ht⟩ := exists_ine_of_v_eq_one haL u hu1
  set s := r (ineIncl hv t) with hs
  have hsI : (s : G E Ω) ∈ Ine (F := E) A :=
    ⟨Weil_le_Dec h s.2, fun z hz => by rw [hs, hrr]; exact t.2.2 z hz⟩
  obtain ⟨t'0, ht'0, hres⟩ := ine_lift g A w h w' h' n hn hg hN (s : G E Ω) hsI
  let t' : Ine (F := E') A := ⟨t'0, ht'0⟩
  have htt : ∀ z : Ω, (t : G L Ω) z = (t' : G E' Ω) z := fun z => by
    have e1 := hrr (ineIncl hv t) z
    have e2 : (r (ineIncl hv t) : G E Ω) z = t'0 z := by
      show (s : G E Ω) z = t'0 z
      rw [← hres]; rfl
    exact e1.symm.trans e2
  have hrt : r (ineIncl hv t) = ineIncl h (resI t') := Subtype.ext (by
    show (s : G E Ω) = AlgEquiv.restrictScalars E t'0
    exact hres.symm)
  obtain ⟨x', hx'⟩ := exists_int_approx_compl w' _ (val_artin_ine ha' t').le
  have hx0 : red x' ≠ 0 := red_ne_zero_of_approx ha' hk hx'
  refine ⟨t, t', x', hx0, ht, hrt, hx', ?_, ?_⟩
  · obtain ⟨yL, hyL⟩ := exists_int_approx_compl v ((aL (ineIncl hv t) : kˣ) : k) (by rw [ht, hu1])
    have hm := tr_match hTR g n A v hv w' h' hgv hgv2 hgw' hg hvN hN aL haL a' ha' π hπ t t' htt yL hyL x' hx'
    have hyL' : Valued.v (((x : 𝒪[k]) : k) - algebraMap L k (yL : L)) < 1 := by
      have e : ((x : 𝒪[k]) : k) = ((aL (ineIncl hv t) : kˣ) : k) := by rw [ht]; rfl
      rw [e]; exact hyL
    exact Units.ext (hκ (x : 𝒪[k]) yL x' hyL' hm)
  ·
    let sI : Ine (F := E) A := ⟨s, hsI⟩
    have hsi : s = ineIncl h sI := Subtype.ext rfl
    have hva : Valued.v ((a s : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
      rw [hsi]; exact val_artin_ine ha sI
    set xq := i.symm ((a s : (w.adicCompletion E)ˣ) : w.adicCompletion E) with hxq
    have hixq : i xq = ((a s : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
      rw [hxq, RingEquiv.apply_symm_apply]
    have hnorm1 : ‖xq‖ = 1 := by
      have h1 : ‖i xq‖ ≤ 1 := by rw [hixq, Valued.toNormedField.norm_le_one_iff, hva]
      have h2 : ¬ ‖i xq‖ < 1 := by rw [hixq, Valued.toNormedField.norm_lt_one_iff, hva]; exact lt_irrefl _
      rw [DiscreteGroups.sglob.DzIso.norm_le_iff i hi] at h1
      rw [DiscreteGroups.sglob.DzIso.norm_lt_iff i hi] at h2
      exact le_antisymm h1 (not_lt.mp h2)
    set uq : ℤ_[g]ˣ := PadicInt.mkUnits hnorm1 with huq
    have huqv : ((uq : ℤ_[g]) : ℚ_[g]) = xq := PadicInt.mkUnits_eq hnorm1
    have hχs : χ (a s) = χ₀ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom uq) :=
      hlc.1 uq (a s) (by rw [huqv, hixq])
    set a₀ : ℕ := (PadicInt.toZMod ((uq : ℤ_[g]))).val with ha₀
    have happ : Valued.v (((a (ineIncl h sI)) : w.adicCompletion E) -
        algebraMap E (w.adicCompletion E) (((a₀ : 𝓞 E)) : E)) < 1 := by
      have hmem : (uq : ℤ_[g]) - (a₀ : ℤ_[g]) ∈ IsLocalRing.maximalIdeal ℤ_[g] := by
        rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, ha₀, ZMod.natCast_zmod_val, sub_self]
      have h5 : ‖xq - (a₀ : ℚ_[g])‖ < 1 := by
        have h := (PadicInt.mem_nonunits).mp hmem
        rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast, huqv] at h
        exact h
      have h6 := val_lt_one_of_norm_lt_one w g i hi _ h5
      rw [map_sub, hixq, map_natCast] at h6
      rw [← hsi, show algebraMap E (w.adicCompletion E) (((a₀ : 𝓞 E)) : E) = (a₀ : w.adicCompletion E) by simp]
      exact h6
    have htt' : ∀ z : Ω, (sI : G E Ω) z = (t' : G E' Ω) z := fun z => by
      show (s : G E Ω) z = t'0 z
      rw [← hres]; rfl
    have hb := tr_base hTR g n hn A w h w' h' hgw hgw2 hgw' hg hq hN a ha a' ha' π hπ sI t' htt' (a₀ : 𝓞 E) happ x' hx'
    set e := (g ^ n - 1) / (g - 1) with he
    have hmem' : ((a₀ : 𝓞 E') - x' ^ e) ∈ w'.asIdeal := by
      rw [← h']
      have e1 : algebraMap E' Ω ((((a₀ : 𝓞 E') - x' ^ e : 𝓞 E')) : E') =
          algebraMap E Ω (((a₀ : 𝓞 E)) : E) - algebraMap E' Ω (x' : E') ^ e := by
        rw [show ((((a₀ : 𝓞 E') - x' ^ e : 𝓞 E')) : E') = (a₀ : E') - (x' : E') ^ e by push_cast; ring,
          map_sub, map_pow, map_natCast, show (((a₀ : 𝓞 E)) : E) = (a₀ : E) by push_cast; rfl, map_natCast]
      rw [e1]; exact hb
    have hred : ((a₀ : K)) = red x' ^ e := by
      have h7 : red ((a₀ : 𝓞 E') - x' ^ e) = 0 := by rw [← RingHom.mem_ker, hk]; exact hmem'
      rw [map_sub, map_pow, map_natCast, sub_eq_zero] at h7
      exact h7
    have hnm := algebraMap_norm_eq_pow hcardK (red x')
    have hinj : Function.Injective (algebraMap (ZMod g) K) := (algebraMap (ZMod g) K).injective
    have hnorm : Algebra.norm (ZMod g) (red x') = PadicInt.toZMod (uq : ℤ_[g]) := by
      apply hinj
      rw [hnm, ← he, ← hred, ← ZMod.natCast_zmod_val (PadicInt.toZMod (uq : ℤ_[g])), map_natCast, ← ha₀]
    rw [hχs]
    congr 1
    exact Units.ext (by simp [hnorm])

end DiscreteGroups.sglob.DzType

end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.StepDown
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
  {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle}

include hi in
theorem step_down (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) {n : ℕ}
    (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (φ : τ →ₗ[ℂ] V)
    (hφ : ∀ (κ : GL (Fin n) ℤ_[g]) (x : τ),
      φ (τ.ρ (red g n κ) x) = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ)) (φ x))
    (L : Module.Dual ℂ V) (hL : IsFunctional ψ π L) (x : τ) (d : Fin n → ℤ) (a b : Fin n)
    (hb : b.val = a.val + 1) (hd : d b < d a) :
    L (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ x)) = 0 := by
  classical
  have hS := DzLc.sum_unip_eq_zero τ hτ (Nat.succ_pos a.val) (by have := b.isLt; omega)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d a = d b + ((k + 1 : ℕ) : ℤ) := ⟨(d a - d b - 1).toNat, by omega⟩
  have hterm : ∀ u ∈ GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n (a.val + 1)),
      L (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ (τ.ρ u x))) =
        L (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ x)) := by
    intro u hu
    obtain ⟨κ, hκ, hmem⟩ := DzLc.exists_lift i u hu
    rw [← hκ, hφ]
    have hU := unipRadical_le_unipB hmem
    rw [← rep_conj π _ _ (φ x), hL _ (by rw [Iwasawa.torusPow]; exact conj_mem_unipB _ hU)]
    rw [psi_eq_one i hi hψ, Circle.coe_one, one_mul]
    rw [Iwasawa.torusPow, superDiag_conj]
    refine Valuation.map_sum_lt _ one_ne_zero fun p _ => Valuation.map_sum_lt _ one_ne_zero fun q hq => ?_
    have hq' : q.val = p.val + 1 := (Finset.mem_filter.1 hq).2
    have hent : ∀ r s : Fin n, valuation (w.adicCompletion E)
        ((Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) r s) ≤ 1 :=
      fun r s => (DzIso.valuation_le_iff i hi _).2 (κ r s).2
    by_cases hp : p = a
    · have hqb : q = b := Fin.ext (by rw [hq', hb, hp])
      rw [hp, hqb, torus_entry' d a b k hk]
      exact val_uniformizer_pow_lt k (hent a b)
    · have hpa : p.val ≠ a.val := fun h => hp (Fin.ext h)
      have h0 : (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
          p q = 0 := by
        have := (GlobalTheory.FiniteGL.mem_unipRadical.1 hmem) p q (by
          simp only [GlobalTheory.FiniteGL.twoBlocks]; split_ifs <;> omega)
        rwa [Matrix.sub_apply, Matrix.one_apply_ne (fun h => by rw [h] at hq'; omega), sub_zero] at this
      rw [h0]; simp
  have h3 := congrArg (fun F : Module.End ℂ τ => L (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ (F x)))) hS
  simp only [LinearMap.sum_apply, map_sum, LinearMap.zero_apply, map_zero] at h3
  rw [Finset.sum_congr rfl
    (fun (u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n (a.val + 1))) _ => hterm u.1 u.2), Finset.sum_const, Finset.card_univ, smul_eq_zero] at h3
  exact h3.resolve_left Fintype.card_ne_zero

end DiscreteGroups.sglob.DzRed
end
end

