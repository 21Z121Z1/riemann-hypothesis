import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.DegeneratingToriPeriodMapEqBaseOfYEqZero
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0020
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoeffMulFSum
section
noncomputable section
namespace GlobalTheory.ArcPts.WeightZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

def chr (x : A.X) : Multiplicative (A.X →+ ℂ) →* ℂ where
  toFun l := eTwoPi (l.toAdd x)
  map_one' := AnArc.e_zero
  map_mul' l l' := AnArc.e_add _ _

theorem chr_injective : Function.Injective (chr A) := by
  intro x y hxy
  by_contra hne
  have hd : x - y ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨i, hi⟩ : ∃ i, (Module.Free.chooseBasis ℤ A.X).repr (x - y) i ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hd
    apply (Module.Free.chooseBasis ℤ A.X).repr.map_eq_zero_iff.mp
    ext j
    simpa using hall j
  let k : ℤ := (Module.Free.chooseBasis ℤ A.X).repr (x - y) i
  let g : A.X →+ ℂ := (Int.castAddHom ℂ).comp ((Module.Free.chooseBasis ℤ A.X).coord i).toAddMonoidHom
  have hg : g (x - y) = k := by simp [g, k]
  have hk : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hi
  let l : A.X →+ ℂ := (2 * (k : ℂ))⁻¹ • g
  have hl : l (x - y) = 1 / 2 := by
    simp only [l, AddMonoidHom.smul_apply, hg, smul_eq_mul]
    field_simp
  have h1 : eTwoPi (l x) = eTwoPi (l y) := congrArg (fun χ => χ (Multiplicative.ofAdd l)) hxy
  have h2 : eTwoPi (l x) = eTwoPi (l (x - y)) * eTwoPi (l y) := by
    rw [← AnArc.e_add, map_sub, sub_add_cancel]
  rw [hl, h1] at h2
  have h3 : eTwoPi (1 / 2) = 1 :=
    mul_right_cancel₀ (AnArc.e_ne_zero (l y)) (h2.symm.trans (one_mul _).symm)
  have h4 : eTwoPi (1 / 2) = -1 := by
    simp only [eTwoPi]
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (1 / 2) = Real.pi * Complex.I by ring, Complex.exp_pi_mul_I]
  rw [h4] at h3
  norm_num at h3

theorem coeff_zero_eq {F G : Finset A.X} {b c : A.X → ℂ} (hF : 0 ∈ F) (hG : 0 ∈ G)
    (h : ∀ l : A.X →+ ℂ, ∑ x ∈ F, b x * eTwoPi (l x) = ∑ x ∈ G, c x * eTwoPi (l x)) : b 0 = c 0 := by
  classical
  have hli : LinearIndependent ℂ (fun x : A.X =>
      ((chr A x : Multiplicative (A.X →+ ℂ) →* ℂ) : Multiplicative (A.X →+ ℂ) → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative (A.X →+ ℂ)) ℂ).comp (chr A) (chr_injective A)
  let g : A.X → ℂ := fun x => (if x ∈ F then b x else 0) - (if x ∈ G then c x else 0)
  have hsum : ∑ x ∈ F ∪ G, g x • ((chr A x : Multiplicative (A.X →+ ℂ) →* ℂ) :
      Multiplicative (A.X →+ ℂ) → ℂ) = 0 := by
    funext m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, g, sub_mul, ite_mul, zero_mul,
      Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.union_inter_cancel_left,
      Finset.union_inter_cancel_right]
    exact sub_eq_zero.mpr (h (Multiplicative.toAdd m))
  have h0 := linearIndependent_iff'.mp hli (F ∪ G) g hsum 0 (Finset.mem_union_left _ hF)
  simpa [g, hF, hG, sub_eq_zero] using h0

theorem exponent_one (α μ : A.X) : A.exponent 1 α μ = A.q (α + μ) - A.q α := by
  rw [AnArc.exponent, AnArc.q_add, A.be_symm μ α]
  push_cast
  ring

theorem FSum_shift (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (v : A.V) :
    A.FSum 1 α th v = HahnSeries.single (-A.q α) ((A.psi α : ℂ)⁻¹) * A.FSum 1 0 (fun z => th (z - A.ct α)) v := by
  ext n
  rw [HahnSeries.coeff_single_mul, AnArc.coeff_FSum, AnArc.coeff_FSum, Finset.mul_sum, sub_neg_eq_add]
  refine Finset.sum_nbij' (fun μ => α + μ) (fun ν => ν - α) ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    simp only [AnArc.mem_level, exponent_one A, zero_add, AnArc.q_zero, sub_zero] at hμ ⊢
    linarith
  · intro ν hν
    simp only [AnArc.mem_level, exponent_one A, zero_add, AnArc.q_zero, sub_zero] at hν ⊢
    rw [show α + (ν - α) = ν by abel]
    linarith
  · intro μ _
    simp
  · intro ν _
    simp
  · intro μ _
    have hu : (A.psi α : ℂ) ≠ 0 := (A.psi α).ne_zero
    have hc : v.2 + A.ct (α + μ) - A.ct α = v.2 + A.ct μ := by rw [map_add]; abel
    simp only [AnArc.term, pow_one, one_smul, zero_add, map_zero, AnArc.e_zero, A.psi_add,
      A.T_symm α μ, hc]
    rw [eq_inv_mul_iff_mul_eq₀ hu]
    ring

theorem coeff_mul_FSum (r : ℂ⸨X⸩) (n : ℤ) : ∃ G₀ : Finset A.X, ∀ G, G₀ ⊆ G → ∀ (th : (Fin A.gB → ℂ) → ℂ) (v : A.V),
    (r * A.FSum 1 0 th v).coeff n = ∑ μ ∈ G, r.coeff (n - A.q μ) * A.term 1 0 th μ v := by
  classical
  refine ⟨(A.finite_be_le (2 * (n - r.order))).toFinset, fun G hG th v => ?_⟩
  have hq : ∀ μ, A.exponent 1 0 μ = A.q μ := fun μ => by
    rw [exponent_one A, zero_add, AnArc.q_zero, sub_zero]
  have hq0 : ∀ μ, 0 ≤ A.q μ := fun μ => by
    have h1 := A.two_mul_q μ
    have h2 := A.be_self_nonneg μ
    linarith
  have hpwo : (Set.Ici (0 : ℤ)).IsPWO := bddBelow_Ici.isWF.isPWO
  have hsupp : (A.FSum 1 0 th v).support ⊆ Set.Ici 0 := by
    intro k hk
    rw [Set.mem_Ici]
    by_contra hlt
    exact hk (A.coeff_FSum_eq_zero 1 0 th v (by simpa using not_le.mp hlt))
  rw [HahnSeries.coeff_mul_right' hpwo hsupp]
  simp only [AnArc.coeff_FSum, Finset.mul_sum]
  rw [Finset.sum_sigma']
  refine Finset.sum_bij_ne_zero (fun a _ _ => a.2) ?_ ?_ ?_ ?_
  · rintro ⟨⟨i, k⟩, μ⟩ h₁ h₂
    rw [Finset.mem_sigma, Finset.mem_antidiagonal, AnArc.mem_level, hq] at h₁
    obtain ⟨⟨-, -, hik⟩, hμ⟩ := h₁
    have ho := HahnSeries.order_le_of_coeff_ne_zero (left_ne_zero_of_mul h₂)
    apply hG
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, ← A.two_mul_q]
    simp only at hμ hik ho ⊢
    linarith
  · rintro ⟨⟨i, k⟩, μ⟩ h₁ _ ⟨⟨i', k'⟩, μ'⟩ h₁' _ heq
    simp only at heq
    subst heq
    rw [Finset.mem_sigma, Finset.mem_antidiagonal, AnArc.mem_level, hq] at h₁ h₁'
    obtain ⟨⟨-, -, hik⟩, hμ⟩ := h₁
    obtain ⟨⟨-, -, hik'⟩, hμ'⟩ := h₁'
    simp only at hik hμ hik' hμ'
    have hk : k = k' := by rw [← hμ, ← hμ']
    subst hk
    have hi : i = i' := by omega
    subst hi
    rfl
  · intro μ _ hne
    refine ⟨⟨(n - A.q μ, A.q μ), μ⟩, ?_, hne, rfl⟩
    rw [Finset.mem_sigma, Finset.mem_antidiagonal, AnArc.mem_level, hq]
    exact ⟨⟨(HahnSeries.mem_support _ _).mpr (left_ne_zero_of_mul hne), Set.mem_Ici.mpr (hq0 μ), by simp⟩, rfl⟩
  · rintro ⟨⟨i, k⟩, μ⟩ h₁ _
    rw [Finset.mem_sigma, Finset.mem_antidiagonal, AnArc.mem_level, hq] at h₁
    obtain ⟨⟨-, -, hik⟩, hμ⟩ := h₁
    simp only at hik hμ ⊢
    rw [show i = n - A.q μ by omega]

theorem eq_FSum {f : A.V → ℂ⸨X⸩} (hf : ArcPts.IsComb A 1 Set.univ f) (θ : (Fin A.gB → ℂ) → ℂ)
    (h : ∀ (z : Fin A.gB → ℂ) (n : ℤ), ∃ (F : Finset A.X) (b : A.X → ℂ), 0 ∈ F ∧ b 0 = (if n = 0 then θ z else 0) ∧
      ∀ l : A.X →+ ℂ, (f (l, z)).coeff n = ∑ x ∈ F, b x * eTwoPi (l x)) (v : A.V) : f v = A.FSum 1 0 θ v := by
  classical
  obtain ⟨m, r, α, th, -, hfe⟩ := hf
  obtain ⟨s, ph, hfe'⟩ : ∃ (s : Fin m → ℂ⸨X⸩) (ph : Fin m → (Fin A.gB → ℂ) → ℂ),
      ∀ w, f w = ∑ i, s i * A.FSum 1 0 (ph i) w :=
    ⟨fun i => r i * HahnSeries.single (-A.q (α i)) ((A.psi (α i) : ℂ)⁻¹), fun i z => th i (z - A.ct (α i)),
      fun w => by
        rw [hfe w]
        exact Finset.sum_congr rfl fun i _ => by simp only [FSum_shift A (α i) (th i) w, mul_assoc]⟩
  have hq : ∀ μ, A.exponent 1 0 μ = A.q μ := fun μ => by
    rw [exponent_one A, zero_add, AnArc.q_zero, sub_zero]
  have hexp : ∀ n : ℤ, ∃ G : Finset A.X, 0 ∈ G ∧ A.level 1 0 n ⊆ G ∧ ∀ w : A.V,
      (f w).coeff n = ∑ μ ∈ G, ∑ i, (s i).coeff (n - A.q μ) * A.term 1 0 (ph i) μ w := by
    intro n
    choose G₀ hG₀ using fun i => coeff_mul_FSum A (s i) n
    have hsub : ∀ i, G₀ i ⊆ insert 0 (A.level 1 0 n ∪ Finset.univ.biUnion G₀) := fun i =>
      (Finset.subset_biUnion_of_mem G₀ (Finset.mem_univ i)).trans
        (Finset.subset_union_right.trans (Finset.subset_insert _ _))
    refine ⟨insert 0 (A.level 1 0 n ∪ Finset.univ.biUnion G₀), Finset.mem_insert_self _ _,
      fun μ hμ => Finset.mem_insert_of_mem (Finset.mem_union_left _ hμ), fun w => ?_⟩
    rw [hfe' w, HahnSeries.coeff_sum, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => hG₀ i _ (hsub i) (ph i) w
  have hkey : ∀ (z : Fin A.gB → ℂ) (n : ℤ), ∑ i, (s i).coeff n * ph i z = if n = 0 then θ z else 0 := by
    intro z n
    obtain ⟨G, hG0, -, hG⟩ := hexp n
    obtain ⟨F, b, hF0, hb0, hFb⟩ := h z n
    have hc := coeff_zero_eq A (F := F) (G := G) (b := b)
      (c := fun μ => (A.psi μ : ℂ) * ∑ i, (s i).coeff (n - A.q μ) * ph i (z + A.ct μ)) hF0 hG0 (fun l => by
        rw [← hFb l, hG (l, z)]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [AnArc.term, pow_one, one_smul, zero_add, map_zero, AnArc.e_zero]
        ring)
    rw [← hb0, hc]
    simp
  ext n
  obtain ⟨G, -, hlev, hG⟩ := hexp n
  have hK : ∀ (μ : A.X) (g : (Fin A.gB → ℂ) → ℂ),
      A.term 1 0 g μ v = A.term 1 0 (fun _ => 1) μ v * g (v.2 + A.ct μ) := by
    intro μ g
    simp only [AnArc.term, mul_one]
  have hterm : ∀ μ, ∑ i, (s i).coeff (n - A.q μ) * A.term 1 0 (ph i) μ v =
      if A.q μ = n then A.term 1 0 θ μ v else 0 := by
    intro μ
    calc ∑ i, (s i).coeff (n - A.q μ) * A.term 1 0 (ph i) μ v
        = A.term 1 0 (fun _ => 1) μ v * ∑ i, (s i).coeff (n - A.q μ) * ph i (v.2 + A.ct μ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [hK μ (ph i)]; ring
      _ = if A.q μ = n then A.term 1 0 θ μ v else 0 := by
          rw [hkey, hK μ θ]
          by_cases hμ : A.q μ = n
          · rw [if_pos (by omega), if_pos hμ]
          · rw [if_neg (by omega), if_neg hμ, mul_zero]
  rw [hG v, AnArc.coeff_FSum]
  simp only [hterm]
  rw [← Finset.sum_filter]
  congr 1
  ext μ
  simp only [Finset.mem_filter, AnArc.mem_level, hq]
  exact ⟨fun hμ => hμ.2, fun hμ => ⟨hlev (by rw [AnArc.mem_level, hq]; exact hμ), hμ⟩⟩

end GlobalTheory.ArcPts.WeightZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsBasisFSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory

theorem AnArc.FSum_sum_smul {O : Type} [CommRing O] [StarRing O] (A : AnArc O) (j : ℕ) [NeZero j] (α : A.X)
    {K : Type} (s : Finset K) (c : K → ℂ) (th : K → (Fin A.gB → ℂ) → ℂ) (v : A.V) :
    A.FSum j α (∑ i ∈ s, c i • th i) v = ∑ i ∈ s, HahnSeries.single 0 (c i) * A.FSum j α (th i) v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := A.FSum_smul j α 0 0 v
    rw [zero_smul, zero_smul] at h
    simpa using h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, A.FSum_add, ih, A.FSum_smul,
      HahnSeries.single_zero_mul_eq_smul]

theorem AnArc.exists_basis_FSum : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), AnFin A → ∀ (j : ℕ) [NeZero j], ∃ (n : ℕ) (α : Fin n → A.X) (th : Fin n → (Fin A.gB → ℂ) → ℂ) (T₀ : ℝ), (∀ i, th i ∈ A.Theta j (α i)) ∧ LinearIndependent ℂ⸨X⸩ (fun i v => A.FSum j (α i) (th i) v) ∧ (∀ w : ℂ, T₀ < w.im → LinearIndependent ℂ (fun i v => A.Sum j (α i) (th i) w v)) ∧ ∀ α', ∀ th' ∈ A.Theta j α', ∃ r : Fin n → ℂ⸨X⸩, (∀ i T, r i ∈ Conv.halfRing T) ∧ ∀ v, A.FSum j α' th' v = ∑ i, r i * A.FSum j (α i) (th i) v := by
  intro O _ _ A hA j _
  classical
  have hj : 1 ≤ j := Nat.one_le_iff_ne_zero.2 (NeZero.ne j)
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul A.X j hj
  obtain ⟨T₀, hT⟩ := A.exists_isConvLine
  have : ∀ c, Module.Finite ℂ (A.Theta j (e c)) := fun c => hA.1 j (e c) hj
  let b := fun c => Module.finBasis ℂ (A.Theta j (e c))
  let I := fun c => Fin (Module.finrank ℂ (A.Theta j (e c)))
  let t : ∀ c, I c → (Fin A.gB → ℂ) → ℂ := fun c i => b c i
  have ht : ∀ c, LinearIndependent ℂ (t c) := fun c =>
    (b c).linearIndependent.map' (A.Theta j (e c)).subtype (Submodule.ker_subtype _)
  have htm : ∀ c i, t c i ∈ A.Theta j (e c) := fun c i => (b c i).2
  have hrep : ∀ c c' y, e c = e c' + j • y → c = c' := fun c c' y h =>
    (he (e c)).unique ⟨0, by simp⟩ ⟨y, h⟩
  let s := (Fintype.equivFin (Σ c, I c)).symm
  refine ⟨_, fun i => e (s i).1, fun i => t (s i).1 (s i).2, T₀, fun i => htm _ _,
    (A.linearIndependent_FSum_sigma hrep ht).comp s s.injective, fun w hw =>
    (A.linearIndependent_Sum_sigma (NeZero.ne j) hrep ht w fun c i z =>
      AnArc.summable_term hT (NeZero.ne j) (htm c i) hw (0, z)).comp s s.injective, fun α' th' hth' => ?_⟩
  obtain ⟨c, ⟨m, hm⟩, -⟩ := he α'
  have hα : α' + j • (-m) = e c := by rw [hm]; simp
  have hmem := A.translate_mem_Theta hth' (-m)
  rw [hα] at hmem
  let x := (b c).repr ⟨_, hmem⟩
  have hx : (fun z => th' (z + A.ct (-m))) = ∑ i, x i • t c i := by
    have := congrArg Subtype.val ((b c).sum_repr ⟨_, hmem⟩)
    rw [Submodule.coe_sum] at this
    exact this.symm
  let u : ℂ⸨X⸩ := HahnSeries.single (A.exponent j α' (-m)) ((A.psi (-m) : ℂ) ^ j * eTwoPi (A.T (-m) α'))
  obtain ⟨r, hr1, hr0⟩ : ∃ r : ∀ c', I c' → ℂ⸨X⸩, (∀ i, r c i = u * HahnSeries.single 0 (x i)) ∧
      ∀ c', c' ≠ c → ∀ i, r c' i = 0 :=
    ⟨Pi.single (M := fun c' => I c' → ℂ⸨X⸩) c fun i => u * HahnSeries.single 0 (x i),
      fun i => by rw [Pi.single_eq_same], fun c' h i => by rw [Pi.single_eq_of_ne h]; rfl⟩
  refine ⟨fun i => r (s i).1 (s i).2, fun i T => ?_, fun v => ?_⟩
  · beta_reduce
    generalize s i = p
    obtain ⟨c', i'⟩ := p
    by_cases h : c' = c
    · subst h
      rw [hr1]
      exact mul_mem (Conv.single_mem_halfRing _ _ _) (Conv.single_mem_halfRing _ _ _)
    · rw [hr0 c' h]
      exact zero_mem _
  · rw [s.sum_comp (fun p : Σ c, I c => r p.1 p.2 * A.FSum j (e p.1) (t p.1 p.2) v), Fintype.sum_sigma,
      Finset.sum_eq_single c (fun c' _ h => by simp [hr0 c' h]) (by simp),
      A.FSum_eq_translate j α' th' (-m) v, hα, hx, A.FSum_sum_smul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hr1, _root_.mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCharacterRatioExpMul
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AbelianLetters

theorem exists_ratio_valR {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {ε : K → ℤ} (hL : L.IsLB) {φ φ' : K → (Sp A ⟶ X)} (e : φ = φ') (t : LB.Gen (LB.LinComb L φ ε))
    (t' : LB.Gen (LB.LinComb L φ' ε)) (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ a : Γ(Sp A, ⊤)ˣ, (∀ z J, Good L z J → val t (𝟙 _) z J = gm (𝟙 _) z ⊤ a * val t' (𝟙 _) z J) ∧
      ∀ j, ⊤ ≤ LB.wchart L φ j → valR (𝟙 (Sp A)) (LB.wchart L φ j) (t.s j).val =
        valR (𝟙 (Sp A)) ⊤ a.val * valR (𝟙 (Sp A)) (LB.wchart L φ' j) (t'.s j).val := by
  subst e
  obtain ⟨a, ha⟩ := TorusCoord.exists_ratio hL (fun _ _ _ => rfl) t ht t' ht'
  refine ⟨a, fun z J hJ => ha _ _ z J hJ, fun j hj => ?_⟩
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' hL (cpt A)
  apply toStkA_injective
  have hm : (𝟙 (Sp A) : Sp A ⟶ Sp A) (cpt A) ∈ LB.wchart L φ j := hj (x := cpt A) trivial
  rw [map_mul, toStkA_valR _ ⊤ _ le_rfl, toStkA_valR _ (LB.wchart L φ j) _ hj (t.s j),
    toStkA_valR _ (LB.wchart L φ j) _ hj (t'.s j), ← Units.val_mul,
    gen_trans ht _ _ hm (hJ.mem φ _), gen_trans ht' _ _ hm (hJ.mem φ _), mul_left_comm]
  exact congrArg (fun q => Units.val (_ * q)) (ha _ _ _ J hJ)

theorem exists_isRatio_mul [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ)
    (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (sB : ∀ Tt : Over (Sp ℂ), (Tt ⟶ D.P.A) → Out.GtPt D Tt)
    (hb : ∀ Tt b, (sB Tt b).b = b ^ n)
    (hadd : ∀ Tt b b', Out.GtPt.IsAdd (sB Tt b) (sB Tt b') (sB Tt (b * b')))
    (hpull : ∀ (Tt Tt' : Over (Sp ℂ)) (h : Tt' ⟶ Tt) b, Out.GtPt.IsPull h.left (sB Tt b) (sB Tt' (h ≫ b)))
    (hex : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) :
    ∃ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n (sB D.P.A (𝟙 _)) u ∧ (∀ x z, u x z ≠ 0) ∧
      ∀ x z z', u x (z + z') = u x z * u x z' := by
  have eb : ∀ z, (ex ((n : ℂ) • z)).b = (sB (Out.TF (R := ℂ) ℂ) (ex z).b).b := fun z => by
    rw [b_nsmul hex, hb]
  choose a ha hv using fun x z => exists_ratio_valR (A := ℂ) D.P.isLB
    (φ := Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b x)
    (φ' := Out.DegPre.gtφT D (Out.TF (R := ℂ) ℂ) (sB (Out.TF (R := ℂ) ℂ) (ex z).b).b x)
    (by rw [eb]; rfl) ((ex ((n : ℂ) • z)).s x) ((sB (Out.TF (R := ℂ) ℂ) (ex z).b).s x)
    ((ex _).isGen x) ((sB _ _).isGen x)
  have hev : ∀ c : Γ(Sp ℂ, ⊤), valR (𝟙 (Sp ℂ)) ⊤ c = HolHom.evalHom (𝟙 (Sp ℂ)) ⊤ le_rfl c := fun c =>
    HolHom.valR_eq _ _ _ c
  refine ⟨fun x z => valR (𝟙 (Sp ℂ)) ⊤ (a x z).val, fun x z j hj => ?_, fun x z => ?_, fun x z z' => ?_⟩
  · refine (hv x z j hj).trans (congrArg (_ * ·) ?_)
    have H := hpull D.P.A _ (ex z).b (𝟙 _)
    rw [Category.comp_id] at H
    exact valR_of_isPull H x j
  · exact (hev _).trans_ne ((a x z).isUnit.map _).ne_zero
  · have : a x (z + z') = a x z * a x z' := unit_ext fun w _ => by
      obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB w
      have e1 := (val_mul hJ _ _ _).symm.trans
        ((val_corr hJ ((hex ((n : ℂ) • z) ((n : ℂ) • z')).2 x) (𝟙 _)).trans (val_mul hJ _ _ _))
      have e2 := (val_mul hJ _ _ _).symm.trans
        ((val_corr hJ ((hadd _ (ex z).b (ex z').b).2 x) (𝟙 _)).trans (val_mul hJ _ _ _))
      have e3 : val (Out.DegPre.cubAt D ℂ (Out.DegPre.cF D ℂ x) (ex ((n : ℂ) • z)).b (ex ((n : ℂ) • z')).b) (𝟙 _) w J =
          val (Out.DegPre.cubAtT D _ (Out.DegPre.cT D _ x) (sB (Out.TF (R := ℂ) ℂ) (ex z).b).b
            (sB (Out.TF (R := ℂ) ℂ) (ex z').b).b) (𝟙 _) w J := by
        rw [eb, eb]; rfl
      rw [← smul_add] at e1
      rw [← b_add hex] at e2
      have key : ∀ {U : Type} [CommGroup U] {p q r c c' p' q' r' k₁ k₂ k₃ : U}, r * c = p * q → r' * c' = p' * q' →
          c = c' → p = k₁ * p' → q = k₂ * q' → r = k₃ * r' → k₃ = k₁ * k₂ := by
        intro U _ p q r c c' p' q' r' k₁ k₂ k₃ h₁ h₂ h₃ h₄ h₅ h₆
        rw [h₃, h₄, h₅, h₆, _root_.mul_assoc, h₂, _root_.mul_mul_mul_comm] at h₁
        exact mul_right_cancel h₁
      rw [map_mul]
      exact key e1 e2 e3 (ha x z w J hJ) (ha x z' w J hJ) (ha x (z + z') w J hJ)
    simp only [this, hev, Units.val_mul, map_mul]

end GlobalTheory.AbelianLetters
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEntireUnitAppellHumbertFrameRatio
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.FrameCompare

open GlobalTheory.PullHermitian

section Val

variable {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) {L : LB Y} {L' : LB X} (φ : X ⟶ Y)

abbrev ix (j : L.ι) (i : L'.ι) : (LB.div (L.pull φ) L').ι := (fun _ => j, i)

lemma ix_chart (j : L.ι) (i : L'.ι) (hj : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j) (hi : ⊤ ≤ x ⁻¹ᵁ L'.U i) :
    ⊤ ≤ x ⁻¹ᵁ (LB.div (L.pull φ) L').U (ix φ j i) :=
  inf_of x (wchart_of x L φ j hj) hi

lemma val_iso_pull (w : LB.Iso L' (L.pull φ)) (hw : w.IsGen) (j j' : L.ι) (i i' : L'.ι)
    (hj : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j')
    (hi : ⊤ ≤ x ⁻¹ᵁ L'.U i) (hi' : ⊤ ≤ x ⁻¹ᵁ L'.U i') :
    valAt' x _ (w.s (ix φ j i)).val * valAt' x (L'.U i ⊓ L'.U i') (L'.g i i').val =
      valAt' (x ≫ φ) (L.U j ⊓ L.U j') (L.g j j').val * valAt' x _ (w.s (ix φ j' i')).val := by
  have c := wchart_of x L φ j hj
  have c' := wchart_of x L φ j' hj'
  have h := unitVal_iso x w hw (fun _ => j) (fun _ => j') i i' c c' hi hi'
  have h3 := unitVal_linComb x L φ 1 j j' (inf_of x c c') (inf_of _ hj hj')
  replace h := h.trans (congrArg (fun a => a * _ * _) h3)
  rw [valAt'_eq_unitVal x (ix_chart x φ j i hj hi),
    valAt'_eq_unitVal x (ix_chart x φ j' i' hj' hi'),
    valAt'_eq_unitVal x (inf_of x hi hi'), valAt'_eq_unitVal _ (inf_of _ hj hj')]
  have h4 := congrArg Units.val h
  simp only [Units.val_mul, zpow_one, Units.val_inv_eq_inv_val] at h4
  refine (congrArg (· * _) h4).trans ?_
  field_simp

lemma val_ne_zero (w : LB.Iso L' (L.pull φ)) (j : L.ι) (i : L'.ι)
    (hj : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j) (hi : ⊤ ≤ x ⁻¹ᵁ L'.U i) :
    valAt' x _ (w.s (ix φ j i)).val ≠ 0 := by
  rw [valAt'_eq_unitVal x (ix_chart x φ j i hj hi)]
  exact Units.ne_zero _

end Val

theorem exists_entire_unit_automorphy :
    ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (X : Scheme.{0}) (L : LB X) (L' : LB A'.left), L.IsLB → L'.IsLB → ∀ (φ : A'.left ⟶ X) (w : LB.Iso L' (L.pull φ)), w.IsGen → ∀ (g g' : ℕ) (u : HolUnif A' L' g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∀ (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), (∀ z, (u.ex (F z)).left ≫ φ = e z) → ∀ (fr : L.ι → (Fin g → ℂ) → ℂ) (th : L.Sec) (θ : (Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L.U j}) → (∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.U j → fr j z ≠ 0) → (∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L.U j ⊓ L.U j') → fr j z = valAt' (e z) (L.U j ⊓ L.U j') (L.g j j').val * fr j' z) → (∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.U j → valAt' (e z) (L.U j) (th.f j) = θ z * fr j z) → ∃ ρ : (Fin g → ℂ) → ℂ, Differentiable ℂ ρ ∧ (∀ z, ρ z ≠ 0) ∧ ∀ (la : Fin g → ℂ) (l : u.Λ), F la = l → ∀ z, θ (z + la) * ρ (z + la) = χ l * Complex.exp (Real.pi * hermForm Hm (F z) l + Real.pi / 2 * hermForm Hm l l) * (θ z * ρ z) := by
  intro A' _ X L L' hL hL' φ w hw g g' u Hm χ hu e F he fr th θ hd hne hc hθ
  obtain rfl : e = fun z => (u.ex (F z)).left ≫ φ := funext fun z => (he z).symm
  have hFd : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  obtain ⟨r, hr, hrφ⟩ := exists_glue
    (fun p : L.ι × L'.ι => F ⁻¹' ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ L.U p.1)} ∩
      {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U p.2}))
    (fun p => ((u.hol _ 0).1.inter (u.hol _ 0).1).preimage hFd.continuous)
    (fun z => by
      obtain ⟨j, hj⟩ := exists_chart ((u.ex (F z)).left ≫ φ) hL
      obtain ⟨i, hi⟩ := exists_chart (u.ex (F z)).left hL'
      exact ⟨(j, i), hj, hi⟩)
    (fun p z => fr p.1 z / (valAt' (u.ex (F z)).left _ (w.s (ix φ p.1 p.2)).val * u.fr p.2 (F z)))
    (fun p => by
      have d1 := (u.hol _ (w.s (ix φ p.1 p.2)).val).2.comp
        (s := F ⁻¹' ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ L.U p.1)} ∩
          {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U p.2})) hFd.differentiableOn
        fun z hz => ix_chart _ φ _ _ hz.1 hz.2
      have d2 := (u.fr_hol p.2).comp
        (s := F ⁻¹' ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ L.U p.1)} ∩
          {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U p.2}))
        hFd.differentiableOn fun z hz => hz.2
      have d3 := (hd p.1).mono
        (s := F ⁻¹' ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ L.U p.1)} ∩
          {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U p.2})) fun z hz => hz.1
      simp only [div_eq_mul_inv]
      exact d3.mul ((d1.mul d2).inv fun z hz =>
        mul_ne_zero (val_ne_zero _ φ w _ _ hz.1 hz.2) (u.fr_ne p.2 _ hz.2)))
    (fun p q z hp hq => by
      have h := val_iso_pull (u.ex (F z)).left φ w hw p.1 q.1 p.2 q.2 hp.1 hq.1 hp.2 hq.2
      have h1 := hc p.1 q.1 z (inf_of _ hp.1 hq.1)
      have h2 := u.fr_compat p.2 q.2 (F z) (inf_of _ hp.2 hq.2)
      rw [div_eq_div_iff (mul_ne_zero (val_ne_zero _ φ w _ _ hp.1 hp.2) (u.fr_ne _ _ hp.2))
        (mul_ne_zero (val_ne_zero _ φ w _ _ hq.1 hq.2) (u.fr_ne _ _ hq.2)),
        h1, h2, ← _root_.mul_assoc (valAt' _ _ (w.s (ix φ p.1 p.2)).val), h]
      ring)
  have hchart : ∀ z, ∃ j i, ⊤ ≤ ((u.ex (F z)).left ≫ φ) ⁻¹ᵁ L.U j ∧
      ⊤ ≤ (u.ex (F z)).left ⁻¹ᵁ L'.U i := fun z => by
    obtain ⟨j, hj⟩ := exists_chart ((u.ex (F z)).left ≫ φ) hL
    obtain ⟨i, hi⟩ := exists_chart (u.ex (F z)).left hL'
    exact ⟨j, i, hj, hi⟩
  refine ⟨r, hr, fun z => ?_, fun la l hl z => ?_⟩
  · obtain ⟨j, i, hj, hi⟩ := hchart z
    rw [hrφ (j, i) z ⟨hj, hi⟩]
    exact div_ne_zero (hne _ _ hj) (mul_ne_zero (val_ne_zero _ φ w _ _ hj hi) (u.fr_ne _ _ hi))
  · obtain ⟨j, i, hj, hi⟩ := hchart z
    have hper : u.ex (F (z + la)) = u.ex (F z) := by
      rw [map_add, hl, u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
    have hj' : ⊤ ≤ ((u.ex (F (z + la))).left ≫ φ) ⁻¹ᵁ L.U j := by rwa [hper]
    have hi' : ⊤ ≤ (u.ex (F (z + la))).left ⁻¹ᵁ L'.U i := by rwa [hper]
    have h1 := hu.2.2.2 l i (F z) hi
    have t1 := hθ j z hj
    have t2 := hθ j (z + la) hj'
    have n1 := u.fr_ne _ _ hi
    have n2 := u.fr_ne _ _ hi'
    have n3 := val_ne_zero _ φ w _ _ hj hi
    rw [hrφ (j, i) z ⟨hj, hi⟩, hrφ (j, i) (z + la) ⟨hj', hi'⟩]
    simp only [hper] at t2 ⊢
    rw [← mul_div_assoc, ← mul_div_assoc, ← t1, ← t2]
    rw [map_add, hl] at n2 ⊢
    rw [h1] at n1 ⊢
    have n4 := left_ne_zero_of_mul n1
    simp only [hermForm]
    generalize χ l * Complex.exp _ = c at n4 ⊢
    generalize valAt' _ _ (w.s (ix φ j i)).val = a at n3 ⊢
    beta_reduce
    field_simp

end GlobalTheory.FrameCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FactorCommutatorEqOfNonvanishingStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factor_exponent_commutator_eq_of_quasiPeriodic : ∀ (g : ℕ) (θ ρ : (Fin g → ℂ) → ℂ) (la mu : Fin g → ℂ) (A₁ A₂ B₁ B₂ : (Fin g → ℂ) →ₗ[ℂ] ℂ) (a₁ a₂ b₁ b₂ : ℂ), Differentiable ℂ θ → θ ≠ 0 → Differentiable ℂ ρ → (∀ z, ρ z ≠ 0) → a₁ ≠ 0 → a₂ ≠ 0 → (∀ z, θ (z + la) = a₁ * Complex.exp (A₁ z) * θ z) → (∀ z, θ (z + mu) = a₂ * Complex.exp (A₂ z) * θ z) → (∀ z, θ (z + la) * ρ (z + la) = b₁ * Complex.exp (B₁ z) * (θ z * ρ z)) → (∀ z, θ (z + mu) * ρ (z + mu) = b₂ * Complex.exp (B₂ z) * (θ z * ρ z)) → B₁ mu - A₁ mu = B₂ la - A₂ la := by
  first | exact @GlobalTheory.factor_commutator_eq_of_nonvanishing | exact GlobalTheory.factor_commutator_eq_of_nonvanishing | (intros; apply GlobalTheory.factor_commutator_eq_of_nonvanishing <;> assumption)
end

