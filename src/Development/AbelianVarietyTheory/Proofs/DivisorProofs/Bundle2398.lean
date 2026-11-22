import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSymplecticLevelFamilyUniversalProper
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2272
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0567
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2352
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2335
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportingFormGapOffSmoothCone
section
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.Gap

section Bound

variable {X : Type} [AddCommGroup X] {m : ℕ} {a : Fin m → X}

theorem exists_abs_apply_le (ha : Submodule.span ℤ (Set.range a) = ⊤) (x y : X) :
    ∃ C : ℕ, ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → (∀ y, 0 ≤ β y y) →
      |β x y| ≤ C * ∑ i, β (a i) (a i) := by
  have hx : x ∈ Submodule.span ℤ (Set.range a) := ha ▸ Submodule.mem_top
  have hy : y ∈ Submodule.span ℤ (Set.range a) := ha ▸ Submodule.mem_top
  have hl : ∀ β : LinearMap.BilinForm ℤ X, (∀ y, 0 ≤ β y y) → 0 ≤ ∑ i, β (a i) (a i) :=
    fun β hp => Finset.sum_nonneg fun i _ => hp _
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      refine ⟨1, fun β hs hp => ?_⟩
      have h1 := hp (a i + a j)
      have h2 := hp (a i - a j)
      simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, hs (a j) (a i)] at h1 h2
      have h3 := Finset.single_le_sum (f := fun i => β (a i) (a i)) (fun i _ => hp _) (Finset.mem_univ i)
      have h4 := Finset.single_le_sum (f := fun i => β (a i) (a i)) (fun i _ => hp _) (Finset.mem_univ j)
      rw [abs_le]
      constructor <;> push_cast <;> linarith
    | zero => exact ⟨0, fun β _ _ => by simp⟩
    | add y z _ _ h1 h2 =>
      obtain ⟨C, hC⟩ := h1
      obtain ⟨C', hC'⟩ := h2
      refine ⟨C + C', fun β hs hp => ?_⟩
      rw [map_add, Nat.cast_add, add_mul]
      exact (abs_add_le _ _).trans (add_le_add (hC β hs hp) (hC' β hs hp))
    | smul n y _ h1 =>
      obtain ⟨C, hC⟩ := h1
      refine ⟨n.natAbs * C, fun β hs hp => ?_⟩
      rw [map_smul, smul_eq_mul, abs_mul, Nat.cast_mul, Int.natCast_natAbs, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC β hs hp) (abs_nonneg _)
  | zero => exact ⟨0, fun β _ _ => by simp⟩
  | add x z _ _ h1 h2 =>
    obtain ⟨C, hC⟩ := h1
    obtain ⟨C', hC'⟩ := h2
    refine ⟨C + C', fun β hs hp => ?_⟩
    rw [map_add, LinearMap.add_apply, Nat.cast_add, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (hC β hs hp) (hC' β hs hp))
  | smul n x _ h1 =>
    obtain ⟨C, hC⟩ := h1
    refine ⟨n.natAbs * C, fun β hs hp => ?_⟩
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, abs_mul, Nat.cast_mul, Int.natCast_natAbs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC β hs hp) (abs_nonneg _)

theorem exists_abs_lin_le [Module.Free ℤ X] [Module.Finite ℤ X] (ha : Submodule.span ℤ (Set.range a) = ⊤)
    (lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) :
    ∃ C : ℕ, ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → (∀ y, 0 ≤ β y y) →
      |lam β| ≤ C * ∑ i, β (a i) (a i) := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  let E : _ → _ → LinearMap.BilinForm ℤ X := fun i j => (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j)
  have hE : ∀ β : LinearMap.BilinForm ℤ X, β = ∑ i, ∑ j, β (b i) (b j) • E i j := fun β =>
    b.ext fun k => b.ext fun l => by
      simp [E, LinearMap.sum_apply, Finsupp.single_apply]
  choose C hC using exists_abs_apply_le ha
  refine ⟨∑ i, ∑ j, C (b i) (b j) * (lam (E i j)).natAbs, fun β hs hp => ?_⟩
  conv_lhs => rw [hE β]
  simp only [map_sum, map_smul, smul_eq_mul]
  push_cast
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, mul_right_comm]
  exact mul_le_mul_of_nonneg_right (hC _ _ β hs hp) (abs_nonneg _)

end Bound

section Fan

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem exists_ray_bound (hF : IsPolFanOn bar φ X) :
    ∃ M : ℕ, ∀ ρ : LinearMap.BilinForm ℤ X, IsCone bar φ ![ρ] → φ.evalZ ρ ≤ M := by
  obtain ⟨S, hS, h⟩ := hF.finite
  obtain ⟨M, hM⟩ := (hS.image fun β => φ.evalZ β).bddAbove
  obtain ⟨N, hN⟩ := exists_nat_ge M
  refine ⟨N, fun ρ hρ => ?_⟩
  obtain ⟨e, he⟩ := h 1 _ hρ
  have h1 := hM ⟨_, he 0, rfl⟩
  simp only [evalZ_pull φ (r := e.toLinearMap) e.surjective, Matrix.cons_val_zero] at h1
  exact h1.trans hN

theorem exists_cone_nat [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (hF : IsPolFanOn bar φ X)
    {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X) (hp : ∀ y, 0 ≤ β y y) :
    ∃ (s : ℕ) (δ : Fin s → LinearMap.BilinForm ℤ X) (n : Fin s → ℕ), IsCone bar φ δ ∧ β = ∑ i, n i • δ i := by
  have hB : toReal β ∈ psdCone bar X := by
    simpa using ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (by simp [hβ]) (by simp [hp]) (by simp)
  obtain ⟨m, γ, c, hγ, hc, hsum⟩ := hF.cover _ hB
  obtain ⟨nZ, hnZ⟩ := Cover.coeff_int hγ.mem hγ.basis hβ hsum
  have hn0 : ∀ i, 0 ≤ nZ i := fun i => by exact_mod_cast (hnZ i) ▸ hc i
  let n : Fin m → ℕ := fun i => (nZ i).toNat
  have hn : ∀ i, ((n i : ℤ) : ℝ) = c i := fun i => by simp [n, Int.toNat_of_nonneg (hn0 i), hnZ i]
  refine ⟨m, γ, n, hγ, LinearMap.ext₂ fun a b => ?_⟩
  have h1 := LinearMap.congr_fun₂ hsum a b
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, ← hn] at h1
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul]
  exact_mod_cast h1

end Fan

theorem exists_gap : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O) (d : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFanOn bar φ X → ∀ (r m : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (a : Fin m → X), IsCone bar φ γ → Supports bar φ d γ a → ∀ lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ j, 0 ≤ lam (γ j)) → ∀ K : ℤ, ∃ D₀ : ℕ, ∀ D, D₀ ≤ D → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (D * d : ℝ) * φ.evalZ β ≤ (D * ∑ i, β (a i) (a i) + lam β : ℤ)) ∧ ∀ (ρ : LinearMap.BilinForm ℤ X), IsCone bar φ ![ρ] → (∀ j, ρ ≠ γ j) → (D * d : ℝ) * φ.evalZ ρ + K ≤ (D * ∑ i, ρ (a i) (a i) + lam ρ : ℤ) := by
  intro O _ _ _ _ bar φ d X _ _ _ _ _ _ hF r m γ a hγ hS lam hlam K
  obtain ⟨C, hC⟩ := exists_abs_lin_le hS.span lam
  obtain ⟨M, hM⟩ := exists_ray_bound hF
  refine ⟨C + K.natAbs + C * d * M, fun D hD => ?_⟩
  have hray : ∀ ρ : LinearMap.BilinForm ℤ X, IsCone bar φ ![ρ] → (∀ j, ρ ≠ γ j) →
      (D * d : ℝ) * φ.evalZ ρ + (K.natAbs : ℕ) ≤ (D * ∑ i, ρ (a i) (a i) + lam ρ : ℤ) := by
    intro ρ hρ hne
    have hm : ρ ∈ balForms bar X := hρ.mem 0
    have hp : ∀ y, 0 ≤ ρ y y := hρ.nonneg 0
    obtain ⟨n, hn⟩ := hF.exists_nat hm hp
    have h1 := hS.le ρ hm hp
    have h2 : (d : ℝ) * φ.evalZ ρ ≠ (∑ i, ρ (a i) (a i) : ℤ) := fun he => by
      obtain ⟨k, c, hk, hc⟩ := hS.only ρ hm hp he
      obtain ⟨j, hj⟩ := intCone_face O bar φ X hF 1 r ![ρ] γ hρ hγ ![k] c (by simp [hk]) (by simpa using hc) 0
      exact hne j hj
    have h3 := hM ρ hρ
    have h4 := (abs_le.1 (hC ρ hm.1 hp)).1
    rw [hn] at h1 h2 h3 ⊢
    generalize ∑ i, ρ (a i) (a i) = L at *
    have h1' : (d : ℤ) * n ≤ L := by exact_mod_cast h1
    have h2' : (d : ℤ) * n ≠ L := by exact_mod_cast h2
    have h3' : (n : ℤ) ≤ M := by exact_mod_cast h3
    have hD' : (C : ℤ) + (K.natAbs : ℕ) + C * d * M ≤ D := by exact_mod_cast hD
    have h5 : 0 ≤ L - d * n - 1 := by omega
    have h6 : (C : ℤ) * d * n ≤ C * d * M := mul_le_mul_of_nonneg_left h3' (by positivity)
    have h7 : (0 : ℤ) ≤ C * d * M := by positivity
    have h8 : (0 : ℤ) ≤ (K.natAbs : ℕ) := by positivity
    have h9 : 0 ≤ ((D : ℤ) - C) * (L - d * n - 1) := mul_nonneg (by linarith) h5
    have : (D * d : ℤ) * n + (K.natAbs : ℕ) ≤ D * L + lam ρ := by nlinarith
    have h10 := (Int.cast_le (R := ℝ)).2 this
    rwa [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Int.cast_natCast,
      Int.cast_natCast] at h10
  refine ⟨fun β hβ hp => ?_, fun ρ hρ hne => le_trans ?_ (hray ρ hρ hne)⟩
  · obtain ⟨s, δ, n, hδ, rfl⟩ := exists_cone_nat hF hβ hp
    have hall : ∀ i, (D * d : ℝ) * φ.evalZ (δ i) ≤ (D * ∑ l, δ i (a l) (a l) + lam (δ i) : ℤ) := by
      intro i
      by_cases h : ∃ j, δ i = γ j
      · obtain ⟨j, hj⟩ := h
        rw [hj, mul_assoc, hS.eq j]
        have := hlam j
        exact_mod_cast (le_add_of_nonneg_right this)
      · push_neg at h
        have hc : IsCone bar φ ![δ i] := by
          have := hF.face _ _ δ ⟨fun _ : Fin 1 => i, fun _ _ _ => Subsingleton.elim _ _⟩ hδ
          convert this using 1
          funext u
          fin_cases u
          rfl
        exact le_trans (le_add_of_nonneg_right (Nat.cast_nonneg _)) (hray _ hc h)
    rw [intCone_evalZ_sum hδ.linear, Finset.mul_sum]
    have e : (D * ∑ l, (∑ i, n i • δ i) (a l) (a l) + lam (∑ i, n i • δ i) : ℤ) =
        ∑ i, (n i : ℤ) * (D * ∑ l, δ i (a l) (a l) + lam (δ i)) := by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_nsmul, nsmul_eq_mul, mul_add,
        Finset.sum_add_distrib, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e, Int.cast_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Int.cast_mul, Int.cast_natCast, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hall i) (Nat.cast_nonneg _)
  · have : (K : ℝ) ≤ (K.natAbs : ℕ) := by
      have h := (Int.cast_le (R := ℝ)).2 (Int.le_natAbs : K ≤ (K.natAbs : ℕ))
      rwa [Int.cast_natCast] at h
    linarith

end GlobalTheory.Poinc.Gap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticSimilitudeActionOnLevelFamily
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.UPel.HT.SympAct

theorem exists_smul_iff {h : ℕ} (M : ℕ) (w : Fin h ⊕ Fin h → ℤ) : (∃ c, w = M • c) ↔ reduceMod M w = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    funext i
    simp [reduceMod]
  · intro hw
    refine ⟨fun i => w i / M, ?_⟩
    funext i
    have hd : (M : ℤ) ∣ w i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (congrFun hw i)
    simp only [Pi.smul_apply, nsmul_eq_mul]
    rw [Int.mul_ediv_cancel' hd]

theorem lev_eq_of_reduce {h : ℕ} {T : Type*} [Monoid T] {M : ℕ} (hM : 0 < M) (lev : (Fin h ⊕ Fin h → ℤ) → T)
    (hadd : ∀ a b, lev (a + b) = lev a * lev b) (htor : ∀ a, lev a ^ M = 1) {x y : Fin h ⊕ Fin h → ℤ}
    (hxy : reduceMod M x = reduceMod M y) : lev x = lev y := by
  have hsm : ∀ (n : ℕ) c, lev ((n + 1) • c) = lev c ^ (n + 1) := by
    intro n c
    induction n with
    | zero => simp
    | succ n ih => rw [succ_nsmul, hadd, ih, ← pow_succ]
  obtain ⟨c, hc⟩ := (exists_smul_iff M (x - y)).2 (by
    funext i
    have e := congrFun hxy i
    simp only [reduceMod] at e
    simp only [reduceMod, Pi.sub_apply, Int.cast_sub, e, sub_self, Pi.zero_apply])
  have hx : x = y + M • c := by rw [← hc]; abel
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  rw [hx, hadd, hsm, htor, _root_.mul_one]

theorem omegaStd_cast {h : ℕ} (M : ℕ) (a b : Fin h ⊕ Fin h → ℤ) :
    ((omegaStd a b : ℤ) : ZMod M) = omegaMod M (reduceMod M a) (reduceMod M b) := by
  simp [omegaStd, omegaMod, reduceMod]

theorem zpow_eq_of_cast_eq {G : Type*} [Group G] {M : ℕ} (z : G) (hz : z ^ M = 1) {k l : ℤ}
    (hkl : (k : ZMod M) = l) : z ^ k = z ^ l := by
  obtain ⟨t, ht⟩ : (M : ℤ) ∣ k - l := (ZMod.intCast_eq_intCast_iff_dvd_sub l k M).1 hkl.symm
  have e : k = l + M * t := by linarith
  rw [e, zpow_add, zpow_mul, zpow_natCast, hz, one_zpow, _root_.mul_one]

theorem pow_eq_of_cast_eq {G : Type*} [Monoid G] {M : ℕ} (z : G) (hz : z ^ M = 1) {k l : ℕ}
    (hkl : (k : ZMod M) = l) : z ^ k = z ^ l := by
  rw [ZMod.natCast_eq_natCast_iff'] at hkl
  rw [← Nat.div_add_mod k M, ← Nat.div_add_mod l M, hkl, pow_add, pow_add, pow_mul, pow_mul, hz, one_pow, one_pow]

theorem mult_unique {h M : ℕ} (hh : 0 < h) (g : sympSimGrp h M) {n n' : ℕ} (hn : IsMultOf g n)
    (hn' : IsMultOf g n') : (n : ZMod M) = n' := by
  classical
  let e : Fin h ⊕ Fin h → ZMod M := Pi.single (Sum.inl ⟨0, hh⟩) 1
  let f : Fin h ⊕ Fin h → ZMod M := Pi.single (Sum.inr ⟨0, hh⟩) 1
  have hef : omegaMod M e f = 1 := by
    simp [omegaMod, e, f, Pi.single_apply]
  have := (hn e f).symm.trans (hn' e f)
  rw [hef] at this
  simpa using this

theorem isMultOf_mul {h M : ℕ} {a c : sympSimGrp h M} {n n' : ℕ} (ha : IsMultOf a n) (hc : IsMultOf c n') :
    IsMultOf (a * c) (n * n') := by
  intro x y
  change omegaMod M ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
    ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) x))
    ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
    ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) y)) = _
  rw [ha, hc]
  push_cast
  ring

theorem isMultOf_one {h M : ℕ} : IsMultOf (1 : sympSimGrp h M) 1 := by
  intro x y
  change omegaMod M x y = ((1 : ℕ) : ZMod M) * omegaMod M x y
  simp

theorem exists_mult {h M : ℕ} [NeZero M] (a : sympSimGrp h M) :
    ∃ n : ℕ, IsMultOf a n ∧ n.Coprime M ∧ (h = 0 → n = 1) := by
  by_cases hh : h = 0
  · subst hh
    exact ⟨1, fun x y => by simp [omegaMod], Nat.coprime_one_left _, fun _ => rfl⟩
  · obtain ⟨m, hm⟩ := a.2
    exact ⟨(m : ZMod M).val, fun x y => by rw [ZMod.natCast_zmod_val]; exact hm x y,
      ZMod.val_coe_unit_coprime m, fun h0 => absurd h0 hh⟩

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def idObjMap {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) : ObjMap o o (𝟙 S) :=
  { φ := 𝟙 _, φ₂ := 𝟙 _, cart := GlobalTheory.SiegLower.isGrpPullback_id o.A, sq := ⟨by simp, by simp⟩,
    act := fun c => by simp, pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB, eta := fun y => by simp }

theorem isSympLev_twist {b : Base D R} {N h M : ℕ} (hM : 0 < M) {X : Scheme.{0}} {s : X ⟶ Sp R}
    {s₁ : X ⟶ Sp (cycAway M)} (u : Obj b N s) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A))
    (hlev : IsSympLev u.P h M (zetaAway M) s₁ lev) (a : sympSimGrp h M) (n : ℕ) (ha : IsMultOf a n)
    (σ : cycAway M →+* cycAway M) (hσ : σ (zetaAway M) = zetaAway M ^ n) :
    IsSympLev u.P h M (zetaAway M) (s₁ ≫ spMap σ) (sympTwist a lev) := by
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨hadd, htor, hgeo⟩ := hlev
  have hres : ∀ {x y : Fin h ⊕ Fin h → ℤ}, reduceMod M x = reduceMod M y → lev x = lev y :=
    fun hxy => lev_eq_of_reduce hM lev hadd htor hxy
  have hred_add : ∀ x y : Fin h ⊕ Fin h → ℤ, reduceMod M (x + y) = reduceMod M x + reduceMod M y := by
    intro x y; funext i; simp [reduceMod]
  refine ⟨fun x y => ?_, fun x => htor _, ?_⟩
  · simp only [sympTwist]
    rw [← hadd]
    apply hres
    simp only [hred_add, reduceMod_liftMod, map_add]
  · intro k _ _ x β z hx hz
    obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : cycAway M →+* k, x ≫ s₁ = spMap β₀ :=
      ⟨(Spec.preimage (x ≫ s₁)).hom, by simp [spMap]⟩
    have hββ : β = β₀.comp σ := by
      have e : spMap β = spMap (β₀.comp σ) := by
        rw [← hx, ← Category.assoc, hβ₀, spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg CommRingCat.Hom.hom (Spec.map_inj.1 e)
    have hζ := isPrimitiveRoot_zetaAway hM.ne'
    let z₀ : kˣ := ((hζ.isUnit hM.ne').map β₀).unit
    have hz₀ : (z₀ : k) = β₀ (zetaAway M) := IsUnit.unit_spec _
    have hz' : z = z₀ ^ n := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hz, hββ, RingHom.comp_apply, hσ, map_pow, hz₀]
    have hz₀M : z₀ ^ M = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hz₀, ← map_pow, hζ.pow_eq_one, map_one, Units.val_one]
    obtain ⟨hker, hsurj, hweil⟩ := hgeo k x β₀ z₀ hβ₀ hz₀
    refine ⟨fun w => ?_, fun g hg => ?_, fun w v => ?_⟩
    · simp only [sympTwist]
      rw [hker, exists_smul_iff, exists_smul_iff, reduceMod_liftMod]
      exact LinearEquiv.map_eq_zero_iff _
    · obtain ⟨w, hw⟩ := hsurj g hg
      refine ⟨liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)).symm (reduceMod M w)), ?_⟩
      simp only [sympTwist]
      rw [reduceMod_liftMod, LinearEquiv.apply_symm_apply, ← hw]
      congr 1
      exact hres (reduceMod_liftMod _)
    · simp only [sympTwist]
      have key : z ^ (2 * omegaStd w v) = z₀ ^ (2 * omegaStd
          (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M w)))
          (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M v)))) := by
        rw [hz', ← zpow_natCast, ← zpow_mul]
        apply zpow_eq_of_cast_eq z₀ hz₀M
        push_cast
        rw [omegaStd_cast, omegaStd_cast, reduceMod_liftMod, reduceMod_liftMod, ha]
        ring
      rw [key]
      exact hweil _ _

theorem exists_sympActs : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P h M (zetaAway M) s₁ lev → HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev →
    ∃ ρ : sympSimGrp h M → (X ⟶ X), ρ 1 = 𝟙 X ∧ (∀ a c, ρ (a * c) = ρ a ≫ ρ c) ∧ SympActs s s₁ u lev ρ := by
  intro p _ D R _ b N h M hM X s s₁ u lev hlev huniv
  haveI : NeZero M := ⟨hM.ne'⟩
  have hζ := isPrimitiveRoot_zetaAway hM.ne'
  have hζM : zetaAway M ^ M = 1 := hζ.pow_eq_one
  have hadd := hlev.1
  have htor := hlev.2.1
  have hres : ∀ {x y : Fin h ⊕ Fin h → ℤ}, reduceMod M x = reduceMod M y → lev x = lev y :=
    fun hxy => lev_eq_of_reduce hM lev hadd htor hxy
  choose n hn hcop h0 using fun a : sympSimGrp h M => exists_mult a
  have hσex : ∀ a, ∃ σ : cycAway M →+* cycAway M, σ (zetaAway M) = zetaAway M ^ n a := fun a =>
    let ⟨σ, hσ⟩ := exists_cycAway_aut hM.ne' (hcop a); ⟨σ.toRingHom, hσ⟩
  choose σ hσ using hσex
  have hU : ∀ a, ∃! f : X ⟶ X, f ≫ s = s ∧ f ≫ s₁ = s₁ ≫ spMap (σ a) ∧
      ∃ m : ObjMap u u f, ∀ x, (sympTwist a lev x).left ≫ m.φ = f ≫ (lev x).left :=
    fun a => huniv X s (s₁ ≫ spMap (σ a)) u (sympTwist a lev)
      (isSympLev_twist hM u lev hlev a (n a) (hn a) (σ a) (hσ a))
  choose ρ hρ hρu using hU
  have hcons : ∀ a c, zetaAway M ^ n (a * c) = zetaAway M ^ (n a * n c) := by
    intro a c
    by_cases hh : h = 0
    · rw [h0 _ hh, h0 _ hh, h0 _ hh]
    · exact pow_eq_of_cast_eq _ hζM (mult_unique (Nat.pos_of_ne_zero hh) _ (hn _) (isMultOf_mul (hn a) (hn c)))
  have hone : zetaAway M ^ n 1 = zetaAway M := by
    by_cases hh : h = 0
    · rw [h0 _ hh, pow_one]
    · rw [pow_eq_of_cast_eq _ hζM (mult_unique (Nat.pos_of_ne_zero hh) _ (hn 1) isMultOf_one), pow_one]
  refine ⟨ρ, ?_, fun a c => ?_, fun a => ⟨(hρ a).1, ⟨n a, σ a, hn a, hσ a, (hρ a).2.1⟩, (hρ a).2.2⟩⟩
  · have hσ1 : σ 1 = RingHom.id _ := cycAway_hom_ext hM.ne' (by rw [hσ, hone]; rfl)
    refine (hρu 1 (𝟙 X) ⟨Category.id_comp _, ?_, ?_⟩).symm
    · rw [hσ1, Category.id_comp]
      simp [spMap]
    · refine ⟨idObjMap u, fun x => ?_⟩
      change (lev (liftMod (reduceMod M x))).left ≫ 𝟙 _ = 𝟙 X ≫ (lev x).left
      rw [Category.comp_id, Category.id_comp, hres (reduceMod_liftMod _)]
  · have hσmul : σ (a * c) = (σ a).comp (σ c) := cycAway_hom_ext hM.ne' (by
      rw [hσ, RingHom.comp_apply, hσ, map_pow, hσ, ← pow_mul, hcons])
    refine (hρu (a * c) (ρ a ≫ ρ c) ⟨?_, ?_, ?_⟩).symm
    · rw [Category.assoc, (hρ c).1, (hρ a).1]
    · rw [Category.assoc, (hρ c).2.1, ← Category.assoc, (hρ a).2.1, Category.assoc, hσmul, spMap, spMap, spMap,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · obtain ⟨ma, hma⟩ := (hρ a).2.2
      obtain ⟨mc, hmc⟩ := (hρ c).2.2
      refine ⟨ObjMapComp.comp ma mc, fun x => ?_⟩
      change (sympTwist (a * c) lev x).left ≫ ma.φ ≫ mc.φ = (ρ a ≫ ρ c) ≫ (lev x).left
      have e1 : sympTwist (a * c) lev x = sympTwist a lev
          (liftMod ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M x))) := by
        simp only [sympTwist, reduceMod_liftMod]
        rfl
      rw [e1, ← Category.assoc, hma, Category.assoc]
      change ρ a ≫ (sympTwist c lev x).left ≫ mc.φ = _
      rw [hmc, Category.assoc]

end GlobalTheory.UPel.HT.SympAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateThetaPullbackNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.TransNZ

open GlobalTheory.MBLow.TranslateSection GlobalTheory.MBLow.TrSec

theorem eq_projectionPullbackSection_of_inverseImage {S : Scheme.{0}} (P : PolAV S) (s : P.L.Sec)
    (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver S))) (h : IsPolAVSectionInverseImage P (baseOver S) s th) :
    th = thSec P s := by
  have key : ∀ j : Fin 1 → P.L.ι, th.f j = (thSec P s).f j := by
    intro j
    have hj : j = fun _ => j 0 := funext fun k => by rw [Subsingleton.elim k 0]
    rw [hj, h (j 0) (chart_le P _), projectionPullbackSectionBaseProduct_isInverseImage P s (j 0) (chart_le P _)]
  cases th; cases hth : thSec P s
  simp only [hth] at key
  congr
  exact funext key

end GlobalTheory.TransNZ

open GlobalTheory.MBLow.TranslateSection GlobalTheory.MBLow.TrSec in

theorem GlobalTheory.TransNZ.exists_ne : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : KeyIn K) (m : ℕ), Odd m → 3 ≤ m →
    ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)), (∀ z : baseOver (Sp K) ⟶ x.P.A, z ^ (m ^ 2) = 1 → ∃ i, pt i = z) →
    ∀ (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp K)))), IsPolAVSectionInverseImage x.P (baseOver (Sp K)) x.th th →
    ∀ (U : I → ThetaGrp x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))
      (t : I → LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))),
    (∀ i, SymLift x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) (pt i) (U i) ∧ Tr x.P x.rig m th (U i) (t i)) →
    ∃ i, (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i) : EA x.P (𝟙 (Sp K)) (m ^ 2)) ≠ 0 := by
  intro K _ _ _ x m hm hm3 I pt hpt th hth U t hUt
  have hm1 : 1 ≤ m := by omega
  obtain ⟨i₀, -⟩ := hpt 1 (one_pow _)
  obtain ⟨-, α, s₁, hα, -, hs₁, ht⟩ := hUt i₀
  obtain ⟨p₀⟩ : Nonempty (Sp K) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨a, -, ha⟩ := x.th_ne p₀
  have e := GlobalTheory.TransNZ.eq_projectionPullbackSection_of_inverseImage x.P x.th th hth
  have hp₁ := nonzero_thSec x.P x.th a ha
  rw [← e] at hp₁
  obtain ⟨q, hq⟩ := mulT_surjective x.P m hm1 ((λ_ x.P.A).inv.left.base a)
  have hq' := mem_nonzeroLocus_of_isTwistPull x.P.isLB _ _ _ _ _ α th s₁ hs₁ q (hq ▸ hp₁)
  obtain ⟨r, hr⟩ := translT_surjective x.P.A (U i₀).pt q
  have hr' := mem_nonzeroLocus_of_isTwistPull x.P.isLB _ _ _ _ _ (U i₀).φ s₁ (t i₀) ht r (hr ▸ hq')
  refine ⟨i₀, fun h0 => ?_⟩
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hr'
  have hz : (t i₀).f k = 0 := (GlobalTheory.UU.SecMod.eq_zero_iff_coord _).1 h0 k
  rw [hz, Scheme.basicOpen_zero] at hk
  exact hk
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitThetaKeyRuleOpenModelChartStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_thetaKeyRule_open_model_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsNoetherianRing O → IsOpenImmersion Y.j → 1 ≤ D.p + D.q → ∀ κ : KeyRule, IsKeyRule κ → ∀ M : GChart Y, ∃ (W₀ : Y.X.Opens) (f : Γ(Y.X, W₀)ˣ), (∀ x, x ∈ W₀ ↔ x ∈ M.U ∧ x ∈ Set.range Y.j) ∧ ∀ (K : Type) [Field K] [CharZero K] (z : Sp K ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ W₀) (hz' : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn K), KeyAt M z hz' x → ev z W₀ hz f.val = (κ K x : K) := by
  first | exact @GlobalTheory.KeyOpenModel.exists_unit_open | exact GlobalTheory.KeyOpenModel.exists_unit_open | (intros; apply GlobalTheory.KeyOpenModel.exists_unit_open <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVarietyCompactifyingConnectedComponentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_variety_compactifying_connected_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens), SmoothOfRelativeDimension D.dim (genStr Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → ∃ (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsOpenImmersion io ∧ Set.range io = compactOf Y U ∧ io ≫ genStr Y = B.str := by
  first | exact @GlobalTheory.CompactVar.exists_var | exact GlobalTheory.CompactVar.exists_var | (intros; apply GlobalTheory.CompactVar.exists_var <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDatumSeriesUnitTimesKernelSeriesStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatDatum_series_unit_times_kernel_series : FlatKer := by
  first | exact @GlobalTheory.BigOn.Exp.SerBase.flatKer_holds | exact GlobalTheory.BigOn.Exp.SerBase.flatKer_holds | (intros; apply GlobalTheory.BigOn.Exp.SerBase.flatKer_holds <;> assumption)
end

