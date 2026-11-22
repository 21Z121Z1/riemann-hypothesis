import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0001
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0032
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0045

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SgWeight
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem zcases (j : ZMod 2) : j = 0 ∨ j = 1 := by
  revert j; decide

private theorem sg0 (K : Type) [CommRing K] : sg K 0 = 1 := by simp [sg]

private theorem sg1 (K : Type) [CommRing K] : sg K 1 = -1 := by
  show (-1 : K) ^ ((1 : ZMod 2).val) = -1
  rw [show (1 : ZMod 2).val = 1 from rfl]
  simp

private theorem sg_add (K : Type) [CommRing K] (i j : ZMod 2) : sg K (i + j) = sg K i * sg K j := by
  rcases zcases i with rfl | rfl <;> rcases zcases j with rfl | rfl
  · simp [sg0]
  · simp [sg0]
  · simp [sg0]
  · rw [show (1 : ZMod 2) + 1 = 0 from rfl, sg0, sg1]
    ring

private theorem sg_nsmul (K : Type) [CommRing K] (m : ℕ) (i : ZMod 2) : sg K (m • i) = sg K i ^ m := by
  induction m with
  | zero => simp [sg0]
  | succ k ih => rw [succ_nsmul, sg_add, ih, pow_succ]

private theorem sg_weight (K : Type) [CommRing K] {ι : Type} (wt : ι → ZMod 2) (n : ι →₀ ℕ) :
    (n.prod fun s m => sg K (wt s) ^ m) = sg K (Finsupp.weight wt n) := by
  classical
  rw [Finsupp.weight_apply]
  simp only [Finsupp.prod, Finsupp.sum, ← sg_nsmul]
  generalize n.support = t
  refine Finset.induction_on t ?_ ?_
  · simp [sg0]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, sg_add]

private theorem coeff_sg (O : Type) [CommRing O] {ι : Type} (j : ZMod 2) (y : MvPowerSeries ι O) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (sg _ j * y) = sg O j * MvPowerSeries.coeff n y := by
  rcases zcases j with rfl | rfl <;> simp [sg0, sg1]

theorem UpperTheory.V.Fr.ep_ps :
    ∀ (O : Type) [CommRing O], IsUnit (2 : O) → ∀ (ι : Type) [Finite ι] (wt : ι → ZMod 2), ∃ τ : MvPowerSeries ι O →ₐ[O] MvPowerSeries ι O, (∀ y, τ (τ y) = y) ∧ (∀ j, evp τ j = wtPart O wt j) ∧ ∀ j y, (2 : MvPowerSeries ι O) * wcomp O wt j y = y + sg _ j * τ y := by
  classical
  intro O _ h2 ι _ wt
  have hsq : ∀ i : ZMod 2, sg O i * sg O i = 1 := by
    intro i
    rw [← sg_add]
    rcases zcases i with rfl | rfl
    · exact sg0 O
    · rw [show (1 : ZMod 2) + 1 = 0 from rfl]
      exact sg0 O
  have hne : ∀ i j : ZMod 2, i ≠ j → sg O i = - sg O j := by
    intro i j hij
    rcases zcases i with rfl | rfl <;> rcases zcases j with rfl | rfl
    · exact absurd rfl hij
    · simp [sg0, sg1]
    · simp [sg0, sg1]
    · exact absurd rfl hij
  let a : ι → O := fun s => sg O (wt s)
  have hcoef : ∀ y n, MvPowerSeries.coeff n (MvPowerSeries.rescale a y)
      = sg O (Finsupp.weight wt n) * MvPowerSeries.coeff n y := by
    intro y n
    rw [MvPowerSeries.coeff_rescale, sg_weight]
  let τ : MvPowerSeries ι O →ₐ[O] MvPowerSeries ι O :=
    AlgHom.mk (MvPowerSeries.rescale a) (fun r => by
      ext n
      show MvPowerSeries.coeff n (MvPowerSeries.rescale a (algebraMap O _ r)) = _
      rw [hcoef]
      by_cases hn : n = 0
      · subst hn
        simp [sg0]
      · classical
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          MvPowerSeries.coeff_C, if_neg hn, mul_zero])
  have hτ : ∀ y n, MvPowerSeries.coeff n (τ y)
      = sg O (Finsupp.weight wt n) * MvPowerSeries.coeff n y := hcoef
  refine ⟨τ, ?_, ?_, ?_⟩
  · intro y
    ext n
    rw [hτ, hτ, ← mul_assoc, hsq, one_mul]
  · intro j
    ext y
    show τ y = sg _ j * y ↔ ∀ n, Finsupp.weight wt n ≠ j → MvPowerSeries.coeff n y = 0
    constructor
    · intro h n hn
      have := congrArg (MvPowerSeries.coeff n) h
      rw [hτ, coeff_sg, hne _ _ hn] at this
      have h' : 2 * MvPowerSeries.coeff n y = 0 := by
        linear_combination (-sg O j) * this - (2 * MvPowerSeries.coeff n y) * hsq j
      exact (h2.mul_right_eq_zero).mp h'
    · intro h
      ext n
      rw [hτ, coeff_sg]
      by_cases hn : Finsupp.weight wt n = j
      · rw [hn]
      · rw [h n hn, mul_zero, mul_zero]
  · intro j y
    ext n
    rw [two_mul, map_add, coeff_wcomp, map_add, coeff_sg, hτ]
    split_ifs with hn
    · rw [hn]
      linear_combination (-MvPowerSeries.coeff n y) * hsq j
    · rw [hne _ _ hn]
      linear_combination MvPowerSeries.coeff n y * hsq j
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SgZero
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem sg_zero (R : Type) [CommRing R] : sg R 0 = 1 := by simp [sg]

private theorem sg_one (R : Type) [CommRing R] : sg R 1 = -1 := by
  show (-1 : R) ^ (1 : ZMod 2).val = -1
  rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]

theorem UpperTheory.V.Fr.ep_ee :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 3, ∀ (x : Ideal S.A) (L : S.Loc x), S.u.ee ≤ x → ∀ σ, L.IsInv σ → L.ρ.ee = Ideal.span (evp σ 1 : Set L.R) := by
  intro l _ O _ _ _ _ F C₀ hF S x L hx σ hσ
  have hl : l ≠ 2 := hF.l_odd
  have h2O : IsUnit (2 : L.O') := by
    by_contra h
    have hm : (2 : L.O') ∈ maximalIdeal L.O' := (mem_maximalIdeal _).mpr h
    have hr : residue L.O' 2 = 0 := (residue_eq_zero_iff _).mpr hm
    rw [map_ofNat] at hr
    have hd : l ∣ 2 := (CharP.cast_eq_zero_iff (ResidueField L.O') l 2).mp (by exact_mod_cast hr)
    have hp : l.Prime := Fact.out
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
    · exact hp.one_lt.ne' h1
    · exact hl h1
  have h2 : IsUnit (2 : L.R) := by
    have := h2O.map (algebraMap L.O' L.R)
    rw [map_ofNat] at this
    exact this
  have hpw : ∀ a b : Fin 3, Odd (w 3 a - w 3 b) → pw a b = 1 := by
    intro a b h
    obtain ⟨k, hk⟩ := h
    show ((w 3 a - w 3 b : ℤ) : ZMod 2) = 1
    rw [hk, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_ofNat,
      show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
  have hpw0 : ∀ a b : Fin 3, Even (w 3 a - w 3 b) → pw a b = 0 := by
    intro a b h
    obtain ⟨k, hk⟩ := h
    show ((w 3 a - w 3 b : ℤ) : ZMod 2) = 0
    rw [hk, ← two_mul, Int.cast_mul, Int.cast_ofNat, show (2 : ZMod 2) = 0 from rfl, zero_mul]
  apply le_antisymm
  · unfold NRep.ee
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨g, i, j, hodd, rfl⟩
    apply Ideal.subset_span
    have he := hσ.ent g i j
    rw [hpw i j hodd] at he
    exact he
  · refine Ideal.span_le.mpr ?_
    intro y hy
    have hy' : σ y = sg L.R 1 * y := hy
    rw [sg_one] at hy'
    have hIm : L.ρ.ee ≤ maximalIdeal L.R := by
      unfold NRep.ee
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨g, i, j, hodd, rfl⟩
      have hmem : S.u.r g i j ∈ S.u.ee := Ideal.subset_span ⟨g, i, j, hodd, rfl⟩
      have hxm := hx hmem
      rw [← L.lies] at hxm
      exact Ideal.mem_comap.mp hxm
    haveI : Nontrivial (L.R ⧸ L.ρ.ee) :=
      Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal L.R).ne_top hIm)
    haveI : IsCO L.O' (L.R ⧸ L.ρ.ee) :=
      co_quot L.O' L.R _ (Ideal.Quotient.mkₐ L.O' L.ρ.ee) (Ideal.Quotient.mkₐ_surjective _ _)
    have key' : ∀ z (hz : z ∈ Algebra.adjoin O ((S.B : Set S.R) ∪ {x | ∃ g i j, x = S.ρ.r g i j})),
        Ideal.Quotient.mk L.ρ.ee (σ (L.ι ⟨z, hz⟩)) = Ideal.Quotient.mk L.ρ.ee (L.ι ⟨z, hz⟩) := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem z hz =>
        rcases hz with hB | ⟨g, i, j, rfl⟩
        · have hb' : σ (L.b ⟨z, hB⟩) = sg L.R 0 * L.b ⟨z, hB⟩ := hσ.base ⟨z, hB⟩
          rw [sg_zero, one_mul] at hb'
          show Ideal.Quotient.mk _ (σ (L.b ⟨z, hB⟩)) = Ideal.Quotient.mk _ (L.b ⟨z, hB⟩)
          rw [hb']
        · have he' : σ (L.ρ.r g i j) = sg L.R (pw i j) * L.ρ.r g i j := hσ.ent g i j
          show Ideal.Quotient.mk _ (σ (L.ρ.r g i j)) = Ideal.Quotient.mk _ (L.ρ.r g i j)
          rcases Int.even_or_odd (w 3 i - w 3 j) with h | h
          · rw [hpw0 i j h, sg_zero, one_mul] at he'
            rw [he']
          · rw [hpw i j h, sg_one] at he'
            have hm : L.ρ.r g i j ∈ L.ρ.ee := Ideal.subset_span ⟨g, i, j, h, rfl⟩
            rw [he', Ideal.Quotient.eq]
            have hc : -1 * L.ρ.r g i j - L.ρ.r g i j = (-2) * L.ρ.r g i j := by ring
            rw [hc]
            exact Ideal.mul_mem_left _ _ hm
      | algebraMap r =>
        show Ideal.Quotient.mk _ (σ (L.ι (algebraMap O S.A r))) = Ideal.Quotient.mk _ (L.ι (algebraMap O S.A r))
        rw [L.ι.commutes]
        have hc := (σ.restrictScalars O).commutes r
        rw [AlgHom.restrictScalars_apply] at hc
        rw [hc]
      | add a b ha hb iha ihb =>
        show Ideal.Quotient.mk _ (σ (L.ι (⟨a, ha⟩ + ⟨b, hb⟩))) = Ideal.Quotient.mk _ (L.ι (⟨a, ha⟩ + ⟨b, hb⟩))
        simp only [map_add, iha, ihb]
      | mul a b ha hb iha ihb =>
        show Ideal.Quotient.mk _ (σ (L.ι (⟨a, ha⟩ * ⟨b, hb⟩))) = Ideal.Quotient.mk _ (L.ι (⟨a, ha⟩ * ⟨b, hb⟩))
        simp only [map_mul, iha, ihb]
    have huniq := L.univ (L.R ⧸ L.ρ.ee) ((Ideal.Quotient.mkₐ O L.ρ.ee).comp L.ι) (fun a => by
      show res L.O' _ (Ideal.Quotient.mkₐ L.O' L.ρ.ee (L.ι a)) = _
      exact res_map _ _)
    have h1 : ∀ a : S.A, ((Ideal.Quotient.mkₐ L.O' L.ρ.ee).comp σ) (L.ι a) =
        ((Ideal.Quotient.mkₐ O L.ρ.ee).comp L.ι) a := by
      rintro ⟨z, hz⟩
      exact key' z hz
    have h2' : ∀ a : S.A, (Ideal.Quotient.mkₐ L.O' L.ρ.ee) (L.ι a) =
        ((Ideal.Quotient.mkₐ O L.ρ.ee).comp L.ι) a := fun a => rfl
    have heq := huniq.unique h1 h2'
    have hyq := AlgHom.congr_fun heq y
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hy'] at hyq
    have hd := Ideal.Quotient.eq.mp hyq
    have h2y : 2 * y ∈ L.ρ.ee := by
      have hc : 2 * y = -((-1 * y) - y) := by ring
      rw [hc]
      exact neg_mem hd
    obtain ⟨u, hu⟩ := h2
    have hc : y = (↑u⁻¹ : L.R) * (2 * y) := by rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    show y ∈ L.ρ.ee
    rw [hc]
    exact Ideal.mul_mem_left _ _ h2y
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SingleMemOfSpan
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem single_mem_of_span {C K : Type} [CommRing C] [CommRing K] [Algebra C K]
    (A : Subalgebra C (AddMonoidAlgebra K ℤ)) (j : ℤ) (s : Set K)
    (hs : ∀ x ∈ s, AddMonoidAlgebra.single j x ∈ A) {x : K} (hx : x ∈ Submodule.span C s) :
    AddMonoidAlgebra.single j x ∈ A := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hs y hy
  | zero => rw [AddMonoidAlgebra.single_zero]; exact A.zero_mem
  | add y z _ _ hy hz => rw [AddMonoidAlgebra.single_add]; exact A.add_mem hy hz
  | smul c y _ hy => rw [← AddMonoidAlgebra.smul_single]; exact A.smul_mem hy c

theorem UpperTheory.V.Fr.alg_ft :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} (C : Type) [CommRing C] {K : Type} [CommRing K] [Algebra C K] (ρ : NRep F n K), (∀ i j, (Submodule.span C (Set.range fun g => ρ.r g i j)).FG) → Algebra.FiniteType C (lauSub (ρ.part C)) := by
  intro l _ k _ F n C _ K _ _ ρ h
  choose S hS using h
  set G : Set (AddMonoidAlgebra K ℤ) :=
    ⋃ i, ⋃ j, (fun x => AddMonoidAlgebra.single (w n i - w n j) x) '' (S i j : Set K) with hG
  have hGfin : G.Finite :=
    Set.finite_iUnion fun i => Set.finite_iUnion fun j => (S i j).finite_toSet.image _
  have hGmem : ∀ i j x, x ∈ (S i j : Set K) →
      AddMonoidAlgebra.single (w n i - w n j) x ∈ Algebra.adjoin C G := fun i j x hx =>
    Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨x, hx, rfl⟩⟩⟩)
  have hent : ∀ g i j, AddMonoidAlgebra.single (w n i - w n j) (ρ.r g i j) ∈ Algebra.adjoin C G :=
    fun g i j => single_mem_of_span (Algebra.adjoin C G) _ (S i j) (hGmem i j)
      (by rw [hS i j]; exact Submodule.subset_span ⟨g, rfl⟩)
  have hlist : ∀ L : List (F.G0 × Fin n × Fin n),
      AddMonoidAlgebra.single ((L.map fun s => w n s.2.1 - w n s.2.2).sum)
        ((L.map fun s => ρ.r s.1 s.2.1 s.2.2).prod) ∈ Algebra.adjoin C G := by
    intro L
    induction L with
    | nil =>
      simp only [List.map_nil, List.sum_nil, List.prod_nil]
      rw [← AddMonoidAlgebra.one_def]
      exact (Algebra.adjoin C G).one_mem
    | cons s L ih =>
      simp only [List.map_cons, List.sum_cons, List.prod_cons]
      rw [← AddMonoidAlgebra.single_mul_single]
      exact mul_mem (hent _ _ _) ih
  have hmon : ∀ j, ∀ x ∈ ρ.mon j, AddMonoidAlgebra.single j x ∈ Algebra.adjoin C G := by
    rintro j x ⟨L, hL, rfl⟩
    rw [← hL]
    exact hlist L
  have hpart : ∀ j x, x ∈ ρ.part C j → AddMonoidAlgebra.single j x ∈ Algebra.adjoin C G :=
    fun j x hx => single_mem_of_span _ j _ (hmon j) hx
  have heq : Algebra.adjoin C G = lauSub (ρ.part C) := by
    apply le_antisymm
    · rw [Algebra.adjoin_le_iff]
      intro y hy
      obtain ⟨i, hy⟩ := Set.mem_iUnion.1 hy
      obtain ⟨j, hy⟩ := Set.mem_iUnion.1 hy
      obtain ⟨x, hx, rfl⟩ := hy
      apply single_mem_lauSub
      have hx' : x ∈ Submodule.span C (Set.range fun g => ρ.r g i j) := by
        rw [← hS i j]
        exact Submodule.subset_span hx
      refine Submodule.span_le.mpr ?_ hx'
      rintro _ ⟨g, rfl⟩
      exact NRep.r_mem_part C ρ g i j
    · intro p hp
      have hp' : ∀ j, p.coeff j ∈ ρ.part C j := hp
      have hsum : p = p.coeff.sum fun j x => AddMonoidAlgebra.single j x := by
        apply AddMonoidAlgebra.ext
        rw [Finsupp.sum, AddMonoidAlgebra.coeff_sum]
        exact (Finsupp.sum_single _).symm
      rw [hsum]
      exact Subalgebra.sum_mem _ fun j _ => hpart j _ (hp' j)
  exact ⟨(Subalgebra.fg_top _).mpr ⟨hGfin.toFinset, by rw [Set.Finite.coe_toFinset]; exact heq⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrSMul
section
noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

namespace Frame

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (F : Frame l k) (Q : Type) [CommRing Q] [Algebra k Q]

structure Low (y a : F.G0 → Q) : Prop where
  lcy : IsLocallyConstant y
  lca : IsLocallyConstant a
  muly : ∀ g h : F.G0, y (g * h) = (F.Ψ h : k) • y g + y h
  mula : ∀ g h : F.G0, a (g * h) = (F.Ψ h : k) • a g + y (F.star g) * y h + (((F.Ψ g)⁻¹ : kˣ) : k) • a h
  pol : ∀ g, a (F.star g) = a g
  nor : y F.g0 = y (F.star F.g0)
  loc : ∀ v, ∃ α β γ : Q, ∀ s, y (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - 1) • α ∧
    y (F.star (F.loc0 v s)) = (1 - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • β ∧
    a (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • γ -
      (1 - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • (α * β)

variable {F Q} {Q' : Type} [CommRing Q'] [Algebra k Q'] {y a : F.G0 → Q}

theorem Low.map (h : F.Low Q y a) (φ : Q →ₐ[k] Q') : F.Low Q' (fun g => φ (y g)) (fun g => φ (a g)) where
  lcy := h.lcy.comp φ
  lca := h.lca.comp φ
  muly g g' := by simp only [h.muly, map_add, map_smul]
  mula g g' := by simp only [h.mula, map_add, map_smul, map_mul]
  pol g := by simp only [h.pol]
  nor := congrArg φ h.nor
  loc v := by
    obtain ⟨α, β, γ, H⟩ := h.loc v
    refine ⟨φ α, φ β, φ γ, fun s => ?_⟩
    obtain ⟨h1, h2, h3⟩ := H s
    exact ⟨by rw [h1, map_smul], by rw [h2, map_smul], by rw [h3, map_sub, map_smul, map_smul, map_mul]⟩

theorem Low.comb (h : F.Low Q y a) (t : Q) {b : F.G0 → Q} (hb : b ∈ F.strS Q) :
    F.Low Q (fun g => t * y g) (fun g => t ^ 2 * a g + b g) where
  lcy := h.lcy.comp (t * ·)
  lca := (h.lca.comp (t ^ 2 * ·)).add hb.1
  muly g g' := by simp only [h.muly, Algebra.smul_def]; ring
  mula g g' := by simp only [h.mula, hb.2.1 g g', Algebra.smul_def]; ring
  pol g := by simp only [h.pol, hb.2.2.1 g]
  nor := congrArg (t * ·) h.nor
  loc v := by
    obtain ⟨α, β, γ, H⟩ := h.loc v
    obtain ⟨δ, H'⟩ := hb.2.2.2 v
    refine ⟨t * α, t * β, t ^ 2 * γ + δ, fun s => ?_⟩
    obtain ⟨h1, h2, h3⟩ := H s
    refine ⟨?_, ?_, ?_⟩
    · rw [h1]; simp only [Algebra.smul_def]; ring
    · rw [h2]; simp only [Algebra.smul_def]; ring
    · rw [h3, H' s]; simp only [Algebra.smul_def]; ring

theorem Low.zero : F.Low Q 0 0 :=
  ⟨IsLocallyConstant.const 0, IsLocallyConstant.const 0, by simp, by simp, fun _ => rfl, rfl,
    fun _ => ⟨0, 0, 0, by simp⟩⟩

theorem Low.strS (h : F.Low Q 0 a) : a ∈ F.strS Q := by
  refine ⟨h.lca, fun g g' => by simpa using h.mula g g', h.pol, fun v => ?_⟩
  obtain ⟨α, β, γ, H⟩ := h.loc v
  refine ⟨γ, fun s => ?_⟩
  obtain ⟨-, h2, h3⟩ := H s
  rw [h3, mul_comm α, ← smul_mul_assoc, ← h2]
  simp

theorem strS_mul (t : Q) (ha : a ∈ F.strS Q) : (fun g => t * a g) ∈ F.strS Q :=
  strS_map (LinearMap.mulLeft k t) ha

end Frame

namespace Space

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ}
  {Q Q' : Type} [CommRing Q] [Algebra (ResidueField O) Q] [CommRing Q'] [Algebra (ResidueField O) Q']

structure FPt (S : Space O F n) (ξ : S.A →+* Q) : Prop where
  x0 : S.x0 ≤ RingHom.ker ξ
  alg : ∀ c : O, ξ (algebraMap O S.A c) = algebraMap (ResidueField O) Q (residue O c)

theorem FPt.comp {S : Space O F n} {ξ : S.A →+* Q} (h : S.FPt ξ) (φ : Q →ₐ[ResidueField O] Q') :
    S.FPt ((φ : Q →+* Q').comp ξ) where
  x0 x hx := by
    have : ξ x = 0 := h.x0 hx
    show φ (ξ x) = 0
    rw [this, map_zero]
  alg c := by
    show φ (ξ _) = _
    rw [h.alg, AlgHom.commutes]

structure At (S : Space O F 3) (ξ : S.A →+* Q) (y a : F.G0 → Q) : Prop where
  fpt : S.FPt ξ
  low : S.u.triM ≤ RingHom.ker ξ
  hy : ∀ g, ξ (S.u.r g 1 0) = y g
  ha : ∀ g, ξ (S.u.r g 2 0) = a g

theorem At.comp {S : Space O F 3} {ξ : S.A →+* Q} {y a : F.G0 → Q} (h : S.At ξ y a) (φ : Q →ₐ[ResidueField O] Q') :
    S.At ((φ : Q →+* Q').comp ξ) (fun g => φ (y g)) (fun g => φ (a g)) where
  fpt := h.fpt.comp φ
  low x hx := by
    have : ξ x = 0 := h.low hx
    show φ (ξ x) = 0
    rw [this, map_zero]
  hy g := congrArg φ (h.hy g)
  ha g := congrArg φ (h.ha g)

end Space

end UpperTheory.V.Fr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TriangularRepresentationDiagonal
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem lc_of_ker {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (φ : G →* H) (h : IsOpen (φ.ker : Set G)) : IsLocallyConstant φ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker φ h

private theorem diag_mul {n : ℕ} {Q : Type} [CommRing Q] (a b : Matrix (Fin n) (Fin n) Q)
    (ha : ∀ i j, i < j → a i j = 0) (hb : ∀ i j, i < j → b i j = 0) (i : Fin n) :
    (a * b) i i = a i i * b i i :=
  _root_.UpperTheory.Reformulated.B.Qk64.diag_mul a b ha hb i

private theorem key {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}
    (hF : F.Ok C₀) {Q : Type} [CommRing Q] [IsDomain Q] [IsLocalRing Q] [IsNoetherianRing Q]
    [Finite (ResidueField Q)] (f : k →+* Q) (ρ : NRep F n Q) (hc : ρ.Cont (maximalIdeal Q))
    (hb : (ρ.map (residue Q)).IsBar ((residue Q).comp f)) (ht : ρ.triM = ⊥) (h : ℕ) (h0 : h ≠ 0) (i : Fin n)
    (H : ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ ψ : F.G0 →* A, IsOpen (ψ.ker : Set F.G0) →
      (∀ g g', ρ.r g i i = ρ.r g' i i → F.Ψ g ^ w n i = F.Ψ g' ^ w n i → ψ g = ψ g') → ∀ g, ψ g ^ h = 1)
    (g : F.G0) : ρ.r g i i = f ((F.Ψ g ^ w n i : kˣ) : k) := by
  haveI : CharP Q l := charP_of_injective_ringHom f.injective l
  have hz : ∀ g i j, i < j → ρ.r g i j = 0 := fun g i j hij => by
    have : ρ.r g i j ∈ ρ.triM := Ideal.subset_span ⟨g, i, j, hij, rfl⟩
    rwa [ht, Ideal.mem_bot] at this
  let χ : F.G0 →* Q :=
    { toFun := fun g => ρ.r g i i * f (((F.Ψ g ^ w n i)⁻¹ : kˣ) : k)
      map_one' := by simp
      map_mul' := fun a b => by
        rw [map_mul, diag_mul _ _ (hz a) (hz b), Subgroup.coe_mul, map_mul, mul_zpow, mul_inv, Units.val_mul,
          map_mul]
        ring }
  have hχ : ∀ g, χ g = ρ.r g i i * f (((F.Ψ g ^ w n i)⁻¹ : kˣ) : k) := fun _ => rfl
  have hinv : ∀ g : F.G0, f (((F.Ψ g ^ w n i)⁻¹ : kˣ) : k) * f ((F.Ψ g ^ w n i : kˣ) : k) = 1 := fun g => by
    rw [← map_mul, Units.inv_mul, map_one]
  have hΨ : IsLocallyConstant fun g : F.G0 => F.Ψ g :=
    (lc_of_ker F.Ψ hF.Ψ_open).comp_continuous continuous_subtype_val
  have h1 : χ g = 1 := by
    refine adic_char_unipotent_pgroup_quotient (l := l) χ h h0 (fun N => ?_) (fun g => ?_) (fun A _ _ hA ψ hψ hh => H A hA ψ hψ ?_) g
    · have := (hc.1 i i N).mul (hΨ.comp fun u : kˣ =>
        Ideal.Quotient.mk (maximalIdeal Q ^ N) (f (((u ^ w n i)⁻¹ : kˣ) : k)))
      convert this using 1
      funext g
      simp only [hχ, map_mul, Pi.mul_apply, Function.comp]
    · rw [← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero, hχ, map_mul]
      have h2 : residue Q (ρ.r g i i) = residue Q (f ((F.Ψ g ^ w n i : kˣ) : k)) := hb.1 g i
      rw [h2, ← map_mul, mul_comm, hinv, map_one]
    · intro g g' e1 e2
      exact hh g g' (by rw [hχ, hχ, e1, e2])
  rw [hχ] at h1
  calc ρ.r g i i = ρ.r g i i * (f (((F.Ψ g ^ w n i)⁻¹ : kˣ) : k) * f ((F.Ψ g ^ w n i : kˣ) : k)) := by
        rw [hinv, mul_one]
    _ = _ := by rw [← mul_assoc, h1, one_mul]

theorem UpperTheory.V.Fr.triangular_representation_diagonal :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ {Q : Type} [CommRing Q] [IsDomain Q] [IsLocalRing Q] [IsNoetherianRing Q] [Finite (ResidueField Q)] (f : k →+* Q) (ρ : NRep F n Q), ρ.Cont (maximalIdeal Q) → (ρ.map (residue Q)).IsBar ((residue Q).comp f) → ρ.triM = ⊥ → ∀ {ι ι' : Type} (s : ι → F.G0) (s' : ι' → F.G0) (h : ℕ), h ≠ 0 → (∀ a, F.Ψ (s a) = 1) → (∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : F.G0 →* A, IsOpen (χ.ker : Set F.G0) → ((∀ a, χ (s a) = 1) → ∀ g, χ g ^ h = 1) ∧ ((∀ g, χ (F.star g) = χ g) → (∀ a, χ (s' a) = 1) → ∀ g, χ g ^ h = 1)) → (∀ a (i : Fin n), (i : ℕ) = 0 → ρ.r (s a) i i = 1) → (∀ a (i : Fin n), w n i = 0 → ρ.r (s' a) i i = 1) → ∀ (g : F.G0) (i : Fin n), ρ.r g i i = f ((F.Ψ g ^ w n i : kˣ) : k) := by
  intro l _ k _ _ F C₀ n hF hn Q _ _ _ _ _ f ρ hc hb ht ι ι' s s' h h0 hs H h1 h2
  obtain ⟨-, -, sΨ, -, sr⟩ := UpperTheory.V.Fr.star hF
  have A0 : ∀ (i : Fin n), (i : ℕ) = 0 → ∀ g, ρ.r g i i = f ((F.Ψ g ^ w n i : kˣ) : k) := fun i hi =>
    key hF f ρ hc hb ht h h0 i fun A _ _ hA ψ hψ hh => (H A hA ψ hψ).1 fun a => by
      rw [← map_one ψ]
      refine hh _ _ ?_ ?_
      · rw [h1 a i hi]; simp
      · rw [hs a]; simp
  have A1 : ∀ (i : Fin n), w n i = 0 → i.rev = i → ∀ g, ρ.r g i i = f ((F.Ψ g ^ w n i : kˣ) : k) :=
    fun i hi hr => key hF f ρ hc hb ht h h0 i fun A _ _ hA ψ hψ hh => (H A hA ψ hψ).2
      (fun g => hh _ _ (by rw [sr, hr]) (by simp [hi])) fun a => by
      rw [← map_one ψ]
      refine hh _ _ ?_ ?_
      · rw [h2 a i hi]; simp
      · simp [hi]
  have A2 : ∀ (i : Fin n), (i : ℕ) = 0 → w n i.rev = - w n i →
      ∀ g, ρ.r g i.rev i.rev = f ((F.Ψ g ^ w n i.rev : kˣ) : k) := fun i hi hw g => by
    rw [← sr, A0 i hi, sΨ, hw, _root_.zpow_neg, _root_.inv_zpow]
  intro g i
  rcases hn with rfl | rfl
  · fin_cases i
    · exact A0 0 rfl g
    · exact A2 0 rfl (by decide) g
  · fin_cases i
    · exact A0 0 rfl g
    · exact A1 1 (by decide) (by decide) g
    · exact A2 0 rfl (by decide) g
end

