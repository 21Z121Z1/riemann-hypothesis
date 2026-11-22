import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0221
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0059
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0392
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0393
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0217
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCyclic
section
noncomputable section
namespace GlobalTheory.TameInertiaCyclic
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_pow_norm (K : FinExt l) :
    ∃ d : ℕ, 0 < d ∧ ∀ x ∈ K.1, x ≠ 0 → ∃ a : ℤ, ‖x‖ ^ d = (l : ℝ) ^ a := by
  haveI := K.2
  refine ⟨Module.finrank ℚ_[l] ↥K.1, Module.finrank_pos, fun x hxK hx => ?_⟩
  have e := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[l] (PadicAlgCl l) x
  rw [PadicAlgCl.spectralNorm_eq] at e
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : (minpoly ℚ_[l] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hi hx
  have hn := minpoly.natDegree_pos hi
  have hd : (minpoly ℚ_[l] x).natDegree ∣ Module.finrank ℚ_[l] ↥K.1 := by
    have := minpoly.degree_dvd (K := ℚ_[l]) (x := (⟨x, hxK⟩ : ↥K.1)) (Algebra.IsIntegral.isIntegral _)
    rwa [IntermediateField.minpoly_eq] at this
  obtain ⟨c, hc⟩ := hd
  refine ⟨-((minpoly ℚ_[l] x).coeff 0).valuation * c, ?_⟩
  rw [hc, pow_mul, e, one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hn.ne',
    Padic.norm_eq_zpow_neg_valuation h0, zpow_mul, zpow_natCast]

theorem exists_gen (K : FinExt l) :
    ∃ π ∈ K.1, π ≠ 0 ∧ ∀ x ∈ K.1, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π ^ k‖ := by
  obtain ⟨d, hd, H⟩ := exists_pow_norm K
  have hl0 : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  let S : AddSubgroup ℤ :=
    { carrier := {n | ∃ x ∈ K.1, x ≠ 0 ∧ ‖x‖ ^ d = (l : ℝ) ^ n}
      add_mem' := by
        rintro a b ⟨x, hx, hx0, ex⟩ ⟨y, hy, hy0, ey⟩
        exact ⟨x * y, mul_mem hx hy, mul_ne_zero hx0 hy0, by
          rw [norm_mul, mul_pow, ex, ey, zpow_add₀ hl0]⟩
      zero_mem' := ⟨1, one_mem _, one_ne_zero, by simp⟩
      neg_mem' := by
        rintro a ⟨x, hx, hx0, ex⟩
        exact ⟨x⁻¹, inv_mem hx, inv_ne_zero hx0, by rw [norm_inv, inv_pow, ex, zpow_neg]⟩ }
  obtain ⟨f, hf⟩ := Int.subgroup_cyclic S
  have hfS : f ∈ S := by rw [hf]; exact AddSubgroup.subset_closure rfl
  obtain ⟨π, hπ, hπ0, eπ⟩ := hfS
  refine ⟨π, hπ, hπ0, fun x hx hx0 => ?_⟩
  obtain ⟨a, ha⟩ := H x hx hx0
  have haS : a ∈ S := ⟨x, hx, hx0, ha⟩
  rw [hf, AddSubgroup.mem_closure_singleton] at haS
  obtain ⟨k, rfl⟩ := haS
  refine ⟨k, (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hd.ne').1 ?_⟩
  rw [ha, norm_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, eπ, ← zpow_mul,
    smul_eq_mul, mul_comm]

theorem norm_sub_lt (K : FinExt l) (g : GQ l) (hg : ∀ x ∈ K0 K, g x = x) (x : Om l) (hxK : x ∈ K.1)
    (hx : ‖x‖ ≤ 1) : ‖g x - x‖ < 1 := by
  have key : ∀ (σ : GQ l) (y : Om l), ‖y‖ < 1 → ‖σ y - y‖ < 1 := fun σ y hy => by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_gal]; exact hy
    · rw [norm_neg]; exact hy
  rcases hx.lt_or_eq with h | h
  · exact key g x h
  · obtain ⟨ζ, m, hm, hlm, hζ, hn⟩ := FrobLaws.exists_root (l := l) x h
    have hζK : ζ ∈ K.1 := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, IntermediateField.mem_fixedField_iff]
      intro σ hσ
      let b : OO l := ⟨ζ, (norm_root hm hζ).le⟩
      have hb : b ^ m = 1 := Subtype.ext hζ
      have h1 := key σ _ hn
      rw [map_sub, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x hxK] at h1
      have h2 : res b = res (galO σ b) := (res_eq_iff _ _).2 (by
        show ‖ζ - σ ζ‖ < 1
        convert h1 using 2; ring)
      exact (congrArg Subtype.val (res_inj hm hlm hb (by rw [← map_pow, hb, map_one]) h2)).symm
    have := key g _ hn
    rw [map_sub, hg ζ ⟨hζK, IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩⟩] at this
    simpa using this

theorem fix_of_near (K : FinExt l) (g : GQ l) (hst : ∀ x ∈ K.1, g x ∈ K.1)
    (hnear : ∀ x ∈ K.1, x ≠ 0 → ‖g x - x‖ < ‖x‖) {N : ℕ} (hN : ¬ l ∣ N)
    (hgN : ∀ x ∈ K.1, (g ^ N) x = x) (y : Om l) (hy : y ∈ K.1) : g y = y := by
  by_contra hne
  have hx0 : g y - y ≠ 0 := sub_ne_zero.2 hne
  have hxK : g y - y ∈ K.1 := sub_mem (hst y hy) hy
  set x := g y - y with hx
  have h1 : ∀ i : ℕ, ‖(g ^ i) x - x‖ < ‖x‖ := by
    intro i
    induction i with
    | zero => simpa using hx0
    | succ i ih =>
      have e : (g ^ (i + 1)) x - x = (g ^ i) (g x - x) + ((g ^ i) x - x) := by
        rw [pow_succ, AlgEquiv.mul_apply, map_sub (g ^ i)]; ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ih)
      rw [norm_gal]; exact hnear x hxK hx0
  have h2 : ∀ k : ℕ, ‖((g ^ k) y - y) - (k : Om l) * x‖ < ‖x‖ := by
    intro k
    induction k with
    | zero => simpa using hx0
    | succ k ih =>
      have e : ((g ^ (k + 1)) y - y) - ((k + 1 : ℕ) : Om l) * x =
          (((g ^ k) y - y) - (k : Om l) * x) + ((g ^ k) x - x) := by
        rw [pow_succ, AlgEquiv.mul_apply, hx, map_sub]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (h1 k))
  have hmn : ‖(N : Om l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
    exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hN)
  have := h2 N
  rw [hgN y hy, sub_self, zero_sub, norm_neg, norm_mul, hmn, one_mul] at this
  exact lt_irrefl _ this

def ratio (g : GQ l) (x : Om l) : OO l :=
  ⟨g x / x, by
    show ‖g x / x‖ ≤ 1
    rw [norm_div, norm_gal]; exact div_self_le_one _⟩

theorem ratio_mul (g : GQ l) (x y : Om l) : ratio g (x * y) = ratio g x * ratio g y :=
  Subtype.ext (by
    show g (x * y) / (x * y) = g x / x * (g y / y)
    rw [map_mul, mul_div_mul_comm])

theorem res_ratio_iff (g : GQ l) {x : Om l} (hx : x ≠ 0) :
    res (ratio g x) = 1 ↔ ‖g x - x‖ < ‖x‖ := by
  rw [← map_one (res (l := l)), res_eq_iff]
  show ‖g x / x - 1‖ < 1 ↔ _
  have : g x / x - 1 = (g x - x) / x := by field_simp
  rw [this, norm_div, div_lt_one (norm_pos_iff.2 hx)]

theorem res_ratio_zpow (g : GQ l) {x : Om l} (hx : x ≠ 0) (h : res (ratio g x) = 1) (k : ℤ) :
    res (ratio g (x ^ k)) = 1 := by
  induction k using Int.induction_on with
  | zero => rw [res_ratio_iff g (by simp)]; simp
  | succ k ih => rw [zpow_add_one₀ hx, ratio_mul, map_mul, ih, h, one_mul]
  | pred k ih =>
    have e : x ^ (-(k : ℤ)) = x ^ (-(k : ℤ) - 1) * x := by
      rw [← zpow_add_one₀ hx, sub_add_cancel]
    rwa [e, ratio_mul, map_mul, h, mul_one] at ih

theorem cyclic_mod (K : FinExt l) {I : Type} [Group I] (j : I →* GQ l)
    (hst : ∀ g, ∀ x ∈ K.1, j g x ∈ K.1) (hfix : ∀ g, ∀ x ∈ K0 K, j g x = x)
    (H : Subgroup I) [H.Normal] [H.FiniteIndex] (hH : ∀ g, g ∈ H ↔ ∀ x ∈ K.1, j g x = x)
    (hN : ¬ l ∣ H.index) : ∃ γ : I, ∀ g : I, ∃ (n : ℕ) (u : I), u ∈ H ∧ g = γ ^ n * u := by
  obtain ⟨π, hπ, hπ0, hgen⟩ := exists_gen K
  let χ : I →* kk l :=
    { toFun := fun g => res (ratio (j g) π)
      map_one' := by rw [res_ratio_iff _ hπ0]; simpa using hπ0
      map_mul' := fun a b => by
        have e : ratio (j (a * b)) π = ratio (j a) π * galO (j a) (ratio (j b) π) := Subtype.ext (by
          show j (a * b) π / π = j a π / π * j a (j b π / π)
          have : j a π ≠ 0 := by simpa using hπ0
          rw [map_mul, AlgEquiv.mul_apply, map_div₀]
          field_simp)
        have e2 : res (galO (j a) (ratio (j b) π)) = res (ratio (j b) π) :=
          (res_eq_iff _ _).2 (norm_sub_lt K (j a) (hfix a) _ (div_mem (hst b π hπ) hπ)
            (ratio (j b) π).2)
        rw [e, map_mul, e2] }
  have hker : ∀ g, χ g = 1 ↔ g ∈ H := by
    intro g
    constructor
    · intro hg
      rw [hH]
      refine fix_of_near K (j g) (hst g) (fun x hx hx0 => ?_) hN (fun x hx => ?_)
      · obtain ⟨k, hk⟩ := hgen x hx hx0
        have hp : π ^ k ≠ 0 := zpow_ne_zero k hπ0
        have hu : ‖x / π ^ k‖ = 1 := by rw [norm_div, hk, div_self (norm_ne_zero_iff.2 hp)]
        have h1 : res (ratio (j g) (x / π ^ k)) = 1 := by
          rw [res_ratio_iff _ (div_ne_zero hx0 hp), hu]
          exact norm_sub_lt K _ (hfix g) _ (div_mem hx (zpow_mem hπ k)) hu.le
        rw [← res_ratio_iff _ hx0, ← div_mul_cancel₀ x hp, ratio_mul, map_mul, h1,
          res_ratio_zpow _ hπ0 hg, one_mul]
      · rw [← map_pow]
        exact (hH _).1 (H.pow_index_mem g) x hx
    · intro hg
      show res (ratio (j g) π) = 1
      rw [res_ratio_iff _ hπ0, (hH g).1 hg π hπ]
      simpa using hπ0
  let f : I ⧸ H →* kk l := QuotientGroup.lift H χ fun g hg => (hker g).2 hg
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    exact (QuotientGroup.eq_one_iff g).2 ((hker g).1 ha)
  haveI : IsCyclic (I ⧸ H) := isCyclic_of_injective_ringHom f hf
  obtain ⟨c, hc⟩ := IsCyclic.exists_monoid_generator (α := I ⧸ H)
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective c
  refine ⟨γ, fun g => ?_⟩
  obtain ⟨n, hn⟩ := hc (g : I ⧸ H)
  refine ⟨n, (γ ^ n)⁻¹ * g, QuotientGroup.eq.1 ?_, by rw [mul_inv_cancel_left]⟩
  rw [QuotientGroup.mk_pow]
  exact hn

theorem map_mem_Kur (g : GQ l) {c : Om l} (hc : c ∈ MaximalUnramifiedExtension l) : g c ∈ MaximalUnramifiedExtension l := by
  unfold MaximalUnramifiedExtension at hc
  induction hc using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, hm, hlm, hx⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, by rw [← map_pow, hx, map_one]⟩
  | algebraMap x => rw [g.commutes]; exact (MaximalUnramifiedExtension l).algebraMap_mem x
  | add x y _ _ hx hy => rw [map_add]; exact (MaximalUnramifiedExtension l).add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact (MaximalUnramifiedExtension l).inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact (MaximalUnramifiedExtension l).mul_mem hx hy

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

theorem inertia_cyclic : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c'), ¬ l ∣ ((pc P h hN hF hS).H.subgroupOf (pc P h hN hF hS).Iner).index → ∃ γ : (pc P h hN hF hS).Iner, ∀ g : (pc P h hN hF hS).Iner, ∃ (n : ℕ) (u : (pc P h hN hF hS).Iner), ((u : ↥(GK K)) ∈ (pc P h hN hF hS).H) ∧ g = γ ^ n * u := by
  intro l _ P K K' h hN hF hS hidx
  haveI : (pc P h hN hF hS).H.Normal := hN
  haveI : (pc P h hN hF hS).H.FiniteIndex := hF
  haveI : Nontrivial P.R.B := by
    by_contra h
    have : Subsingleton P.R.B := not_nontrivial_iff_subsingleton.mp h
    apply (P.PD K).not_mem_filtration_two
    rw [Subsingleton.elim (P.PD K).t 0, map_zero]
    exact Submodule.zero_mem _
  refine cyclic_mod K' ((GK K).subtype.comp (pc P h hN hF hS).Iner.subtype) ?_ ?_ _ ?_ hidx
  · intro g x hx
    refine (InfiniteGalois.fixedField_fixingSubgroup K'.1).le
      ((IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ => ?_)
    have h1 : (g : ↥(GK K))⁻¹ * ⟨σ, GK_le h hσ⟩ * (g : ↥(GK K)) ∈ GKin h :=
      hN.conj_mem' _ hσ _
    have h2 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 h1 x hx
    have h3 := congrArg ((g : ↥(GK K)) : GQ l) h2
    simpa using h3
  · intro g x hx
    have h1 : (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B ⟨x, hx⟩) = algebraMap ↥(K0 K') P.R.B ⟨x, hx⟩ :=
      g.2 ⟨x, hx⟩
    rw [P.PD_actB] at h1
    have h2 := P.actQ_Kur ((g : ↥(GK K)) : GQ l) ⟨x, hx.2⟩ ⟨_, map_mem_Kur _ hx.2⟩ rfl
    have h3 := (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective (h2.symm.trans h1)
    exact congrArg Subtype.val h3
  · intro g
    exact IntermediateField.mem_fixingSubgroup_iff K'.1 ((g : ↥(GK K)) : GQ l)

end GlobalTheory.TameInertiaCyclic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveTensorBcrisToBdR
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.LocTensorK

private theorem ιB_algebraMap_Kur {l : ℕ} [Fact l.Prime] (P : LocPrime l) (c : ↥(MaximalUnramifiedExtension l)) :
    P.ιB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap (Om l) P.R.BdR (c : Om l) := by
  have hint : IsIntegral ℚ_[l] (c : Om l) := Algebra.IsIntegral.isIntegral _
  obtain ⟨K, hc⟩ : ∃ K : FinExt l, (c : Om l) ∈ K0 K :=
    ⟨⟨IntermediateField.adjoin ℚ_[l] {(c : Om l)},
      IntermediateField.adjoin.finiteDimensional hint⟩,
      IntermediateField.mem_adjoin_simple_self ℚ_[l] (c : Om l), c.2⟩
  have h := (P.PD K).ι.commutes (⟨c, hc⟩ : ↥(K0 K))
  rw [P.PD_ι] at h
  exact h

private theorem indep_of_frac {k Ω B D : Type} [Field k] [Field Ω] [CommRing B] [CommRing D] [Algebra k Ω]
    [IsGalois k Ω] (hD : IsField D) (o : Ω →+* D) (ι : B →+* D) (hι : Function.Injective ι)
    (hk : ∀ c : k, ∃ a : B, ι a = o (algebraMap k Ω c))
    (hfrac : ∀ (a b : B) (x : Ω), b ≠ 0 → ι a = o x * ι b → x ∈ (algebraMap k Ω).range)
    (m : ℕ) (x : Fin m → Ω) (hx : LinearIndependent k x) (b : Fin m → B)
    (hb : ∑ i, o (x i) * ι (b i) = 0) : ∀ i, b i = 0 := by
  letI : Field D := hD.toField
  have hcl : ∀ y : D, y ∈ Subring.closure (Set.range ι) ↔ ∃ a, ι a = y := by
    intro y
    have : Subring.closure (Set.range ι) = ι.range := by
      rw [← RingHom.coe_range, Subring.closure_eq]
    rw [this]; rfl
  have key := GlobalTheory.T.eq_zero_of_sum_map_mul_eq_zero_of_linearIndependent k Ω D o (Subfield.closure (Set.range ι)) (by
    intro y
    constructor
    · intro hy
      obtain ⟨u, hu, v, hv, huv⟩ := Subfield.mem_closure_iff.1 hy
      obtain ⟨a, rfl⟩ := (hcl u).1 hu
      obtain ⟨c, rfl⟩ := (hcl v).1 hv
      by_cases hc : c = 0
      · subst hc
        rw [map_zero, div_zero] at huv
        have : y = 0 := o.injective (by rw [map_zero]; exact huv.symm)
        rw [this]; exact zero_mem _
      · have hc' : ι c ≠ 0 := fun h => hc (hι (by rw [h, map_zero]))
        refine hfrac a c y hc ?_
        rw [← huv, div_mul_cancel₀ _ hc']
    · rintro ⟨c, rfl⟩
      obtain ⟨a, ha⟩ := hk c
      exact Subfield.subset_closure ⟨a, ha⟩) m x hx (fun i => ι (b i))
    (fun i => Subfield.subset_closure ⟨b i, rfl⟩) hb
  intro i
  exact hι (by rw [map_zero]; exact key i)

private theorem tied_tensor_inj : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (m : ℕ) (x : Fin m → Om l), LinearIndependent ↥(MaximalUnramifiedExtension l) x → ∀ b : Fin m → P.R.B, ∑ i, algebraMap (Om l) P.R.BdR (x i) * P.ιB (b i) = 0 → ∀ i, b i = 0 := by
  intro l _ P AI T m x hx b hb
  obtain ⟨hD, -, hι, -⟩ := GlobalTheory.Per.TiedField.tied_field l P AI T
  haveI : IsGalois ℚ_[l] (Om l) := inferInstance
  haveI : IsGalois ↥(MaximalUnramifiedExtension l) (Om l) := inferInstance
  refine indep_of_frac (k := ↥(MaximalUnramifiedExtension l)) hD (algebraMap (Om l) P.R.BdR) (P.ιB : P.R.B →+* P.R.BdR) hι
    (fun c => ⟨algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c, ιB_algebraMap_Kur P c⟩) ?_ m x hx b hb
  intro a c y hc h
  exact ⟨⟨y, GlobalTheory.T.mem_maxUnramified_of_crystallineRatio l P AI T a c y hc h⟩, rfl⟩

end GlobalTheory.LocTensorK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_tensor_Bcris_to_BdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (m : ℕ) (x : Fin m → ↥K.1), LinearIndependent ↥(K0 K) x → ∀ b : Fin m → P.R.B, ∑ i, algebraMap ↥K.1 P.R.BdR (x i) * P.ιB (b i) = 0 → ∀ i, b i = 0 := by
  intro l _ P AI hT K m x hx b hb
  refine GlobalTheory.LocTensorK.tied_tensor_inj l P AI hT m (fun i => (x i : Om l))
    (GlobalTheory.UnramDisjoint.linearIndependent_Kur l K m x hx) b ?_
  exact hb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvIsoOfLocalTateDuality
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.InvColim

theorem colim_equiv {O : Type} [CommRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G]
    [CompactSpace G] {ε : G →* Oˣ} (Θ : NatInv ε (fun M _ _ _ => IsFGTop O M))
    {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] (N : ℕ → Submodule O M) (hmono : Monotone N)
    (hopen : ∀ n, IsOpen (N n : Set M)) (hcov : ∀ x, ∃ n, x ∈ N n) (hfg : ∀ n, IsFGTop O (N n)) :
    ∃ e : H2 (twist ε M) ≃ₗ[O] M, ∀ n (z : H2 (twist ε (N n))),
      e (mapH2 (twist ε (N n)) (twist ε M) (N n).subtype continuous_subtype_val
        (twist_map ε (N n).subtype) z) = Θ.θ (N n) (hfg n) z := by
  have hinj := GlobalTheory.T.map_H2_subtype_injective Θ N hmono hopen hcov hfg
  have hsurj := GlobalTheory.T.exists_H2_preimage_of_monotone_open_exhaustion ε N hmono hopen hcov
  let ι : ∀ n, H2 (twist ε (N n)) →ₗ[O] H2 (twist ε M) := fun n =>
    mapH2 (twist ε (N n)) (twist ε M) (N n).subtype continuous_subtype_val (twist_map ε (N n).subtype)
  let ψ : ∀ n, N n →ₗ[O] H2 (twist ε M) := fun n => ι n ∘ₗ (Θ.θ (N n) (hfg n)).symm.toLinearMap
  have hup : ∀ n m (h : n ≤ m) (y : N n), ψ m (Submodule.inclusion (hmono h) y) = ψ n y := by
    intro n m h y
    let inc := Submodule.inclusion (hmono h)
    have hinc : Continuous inc := continuous_subtype_val.subtype_mk _
    have hι : ∀ w, ι m (mapH2 (twist ε (N n)) (twist ε (N m)) inc hinc (twist_map ε inc) w) = ι n w := by
      intro w
      induction w using Submodule.Quotient.induction_on with
      | H w => rfl
    have hw : (Θ.θ (N m) (hfg m)).symm (inc y) = mapH2 (twist ε (N n)) (twist ε (N m)) inc hinc (twist_map ε inc)
        ((Θ.θ (N n) (hfg n)).symm y) := by
      rw [LinearEquiv.symm_apply_eq, Θ.nat _ _ (hfg n) (hfg m) inc hinc, LinearEquiv.apply_symm_apply]
    show ι m ((Θ.θ (N m) (hfg m)).symm (inc y)) = ι n ((Θ.θ (N n) (hfg n)).symm y)
    rw [hw, hι]
  have hind : ∀ n m (y : M) (hn : y ∈ N n) (hm : y ∈ N m), ψ n ⟨y, hn⟩ = ψ m ⟨y, hm⟩ := by
    intro n m y hn hm
    rw [← hup n (max n m) (le_max_left _ _), ← hup m (max n m) (le_max_right _ _)]
    rfl
  let nn : M → ℕ := fun y => (hcov y).choose
  have hnn : ∀ y, y ∈ N (nn y) := fun y => (hcov y).choose_spec
  let Ψ : M →ₗ[O] H2 (twist ε M) :=
    { toFun := fun y => ψ (nn y) ⟨y, hnn y⟩
      map_add' := fun y y' => by
        have hy : y ∈ N (max (nn y) (nn y')) := hmono (le_max_left _ _) (hnn y)
        have hy' : y' ∈ N (max (nn y) (nn y')) := hmono (le_max_right _ _) (hnn y')
        refine (hind _ _ (y + y') (hnn _) (add_mem hy hy')).trans ?_
        rw [hind _ _ y (hnn y) hy, hind _ _ y' (hnn y') hy', ← map_add]
        rfl
      map_smul' := fun c y => by
        refine (hind _ (nn y) (c • y) (hnn _) (Submodule.smul_mem _ c (hnn y))).trans ?_
        rw [RingHom.id_apply, ← map_smul]
        rfl }
  have hΨ : ∀ n (y : N n), Ψ y = ψ n y := fun n y => hind _ n y (hnn _) y.2
  have hΨi : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨n, hn⟩ := hcov y
    have h1 : ψ n ⟨y, hn⟩ = 0 := (hΨ n ⟨y, hn⟩).symm.trans hy
    have h2 : (Θ.θ (N n) (hfg n)).symm ⟨y, hn⟩ = 0 := hinj n (by rw [map_zero]; exact h1)
    have h3 : (⟨y, hn⟩ : N n) = 0 := by simpa using h2
    exact congrArg Subtype.val h3
  have hΨs : Function.Surjective Ψ := by
    intro z
    obtain ⟨n, z', hz'⟩ := hsurj z
    refine ⟨(Θ.θ (N n) (hfg n) z' : M), ?_⟩
    rw [hΨ n]
    show ι n ((Θ.θ (N n) (hfg n)).symm (Θ.θ (N n) (hfg n) z')) = z
    rw [LinearEquiv.symm_apply_apply]
    exact hz'
  refine ⟨(LinearEquiv.ofBijective Ψ ⟨hΨi, hΨs⟩).symm, fun n z => ?_⟩
  rw [LinearEquiv.symm_apply_eq]
  show _ = Ψ _
  rw [hΨ n]
  show _ = ι n ((Θ.θ (N n) (hfg n)).symm (Θ.θ (N n) (hfg n) z))
  rw [LinearEquiv.symm_apply_apply]

section Lat
variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]

theorem frac_isFGTop (hO : PadicCoeff p O) (hF : FracTop O) (n : ℕ) :
    IsFGTop O ((1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n))) := GlobalTheory.T.isFGTop_p_pow_inverse_lattice hO hF n

theorem frac_cover (hO : PadicCoeff p O) (y : FractionRing O) :
    ∃ n, y ∈ (1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n)) := GlobalTheory.T.exists_pow_p_smul_mem_one_fractionRing hO y

theorem ko_discrete (hF : FracTop O) : DiscreteTopology (KO O) := by
  apply discreteTopology_of_isOpen_singleton_zero
  have h1 : ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) =
      Set.range (algebraMap O (FractionRing O)) := by
    ext y; simp [Submodule.mem_one]
  have h2 : ({0} : Set (KO O)) =
      (1 : Submodule O (FractionRing O)).mkQ '' ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) := by
    ext x
    constructor
    · rintro rfl
      exact ⟨0, zero_mem _, map_zero _⟩
    · rintro ⟨y, hy, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero _).2 hy
  rw [h2]
  exact (Submodule.isOpenQuotientMap_mkQ _).isOpenMap _ (h1 ▸ hF.emb.isOpen_range)

end Lat

theorem inv_iso (hT : Formalism.GaloisCohomology.LocalTateDualityK) : InvIso := by
  intro p _ K O _ _ _ _ _ _ _ G _ _ hK hO hF i ε hε
  obtain ⟨Θ⟩ := GlobalTheory.T.natInvIso_of_localTateDuality_cyclotomicTwist hT hK hO i hε
  haveI : CompactSpace G := i.toHomeomorph.symm.compactSpace
  haveI := ko_discrete hF
  let F : ℕ → Submodule O (FractionRing O) := fun n =>
    (1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n))
  let T : ℕ → Submodule O (KO O) := fun n => LinearMap.ker (LinearMap.lsmul O (KO O) ((p : O) ^ n))
  have hFm : Monotone F := by
    refine monotone_nat_of_le_succ fun n y hy => ?_
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 hy
    refine Submodule.mem_one.2 ⟨(p : O) * a, ?_⟩
    simp only [LinearMap.lsmul_apply] at ha ⊢
    rw [map_mul, ha, pow_succ, mul_comm _ (p : O), mul_smul, Algebra.smul_def (p : O) (((p : O) ^ n) • y)]
  have hFo : ∀ n, IsOpen (F n : Set (FractionRing O)) := fun n => by
    have : (F n : Set (FractionRing O)) =
        (fun y : FractionRing O => ((p : O) ^ n) • y) ⁻¹' Set.range (algebraMap O (FractionRing O)) := by
      ext y; simp [F, Submodule.mem_one]
    rw [this]
    exact hF.emb.isOpen_range.preimage (continuous_const_smul _)
  have hFfg := frac_isFGTop hO hF
  have hred : ∀ n, ∀ y ∈ F n, toKO O y ∈ T n := fun n y hy => by
    simp only [T, LinearMap.mem_ker, LinearMap.lsmul_apply, F, Submodule.mem_comap] at hy ⊢
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero _).2 hy
  have hTm : Monotone T := by
    refine monotone_nat_of_le_succ fun n x hx => ?_
    simp only [T, LinearMap.mem_ker, LinearMap.lsmul_apply] at hx ⊢
    rw [pow_succ, mul_comm, mul_smul, hx, smul_zero]
  have hTo : ∀ n, IsOpen (T n : Set (KO O)) := fun n => isOpen_discrete _
  have hTc : ∀ x, ∃ n, x ∈ T n := fun x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨n, hn⟩ := frac_cover hO y
    exact ⟨n, hred n y hn⟩
  have hTsurj : ∀ n, (F n).map (toKO O) = T n := fun n => by
    refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun y hy => hred n y hy) fun x hx => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine ⟨y, ?_, rfl⟩
    simp only [T, LinearMap.mem_ker, LinearMap.lsmul_apply] at hx
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
    exact hx
  have hTfg : ∀ n, IsFGTop O (T n) := fun n => by
    refine ⟨?_, inferInstance, inferInstance⟩
    have := (hFfg n).fg
    rw [← hTsurj n, Module.Finite.iff_fg]
    exact Submodule.FG.map _ (Module.Finite.iff_fg.1 this)
  obtain ⟨eF, heF⟩ := colim_equiv Θ F hFm hFo (frac_cover hO) hFfg
  obtain ⟨eT, heT⟩ := colim_equiv Θ T hTm hTo hTc hTfg
  refine ⟨eT, eF, fun z => ?_⟩
  obtain ⟨n, hn⟩ := frac_cover hO (eF z)
  set z' := (Θ.θ (F n) (hFfg n)).symm ⟨eF z, hn⟩
  have hz : mapH2 (twist ε (F n)) (twist ε (FractionRing O)) (F n).subtype continuous_subtype_val
      (twist_map ε (F n).subtype) z' = z := eF.injective (by rw [heF, LinearEquiv.apply_symm_apply])
  let red : F n →ₗ[O] T n := ((toKO O).comp (F n).subtype).codRestrict (T n) fun y => hred n y y.2
  have hredc : Continuous red := (toKO_cont.comp continuous_subtype_val).subtype_mk _
  have e3 : mapH2 (twist ε (FractionRing O)) (twist ε (KO O)) (toKO O) toKO_cont (toKO_equiv ε)
      (mapH2 (twist ε (F n)) (twist ε (FractionRing O)) (F n).subtype continuous_subtype_val (twist_map ε _) z') =
      mapH2 (twist ε (T n)) (twist ε (KO O)) (T n).subtype continuous_subtype_val (twist_map ε _)
        (mapH2 (twist ε (F n)) (twist ε (T n)) red hredc (twist_map ε red) z') := by
    induction z' using Submodule.Quotient.induction_on with
    | H w => rfl
  rw [← hz, e3, heT, Θ.nat _ _ (hFfg n) (hTfg n) red hredc]
  refine Eq.trans ?_ (congrArg (toKO O) (heF n z')).symm
  rfl

end GlobalTheory.InvColim
end
end

