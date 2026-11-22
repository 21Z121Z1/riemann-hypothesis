import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0578
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterPairingHarishChandraCuspidalMackey
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0375
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0550
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0373
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0378
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0599
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0600
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterValuesInjectiveLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0495
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0551
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0598
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0601

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterLabelRootOfHarishChandraConstituent
section
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

noncomputable section

namespace GlobalTheory.GLq.DetRoot

open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem ip_list_sum_left {G : Type} [Group G] [Fintype G] (L : List (G → ℂ)) (B : G → ℂ) :
    ip L.sum B = (L.map fun ρ => ip ρ B).sum := by
  induction L with
  | nil => simp [ip]
  | cons ρ L ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons, ← ih]
    unfold ip
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem list_nat_sum {G : Type} [Group G] [Fintype G] (L : List (G → ℂ)) (hL : ∀ ρ ∈ L, IsIrr ρ) (B : G → ℂ)
    (hB : IsChar B) : ∃ N : ℕ, (L.map fun ρ => ip ρ B).sum = N ∧ ∀ ρ ∈ L, ip ρ B ≠ 0 → N ≠ 0 := by
  induction L with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons ρ L ih =>
    obtain ⟨N, hN, hN0⟩ := ih (fun σ hσ => hL σ (List.mem_cons_of_mem _ hσ))
    obtain ⟨k, hk⟩ := GlobalTheory.GLq.LabelMul.ip_nat (hL ρ List.mem_cons_self) hB
    refine ⟨k + N, by simp [hN, hk], ?_⟩
    intro σ hσ h0
    rcases List.mem_cons.1 hσ with rfl | hσ
    · rw [hk] at h0
      have : k ≠ 0 := by exact_mod_cast h0
      omega
    · have := hN0 σ hσ h0
      omega

theorem ip_ne_zero_of_common {G : Type} [Group G] [Fintype G] {ψ A B : G → ℂ} (hψ : IsIrr ψ) (hA : IsChar A)
    (hB : IsChar B) (hψA : ip ψ A ≠ 0) (hψB : ip ψ B ≠ 0) : ip A B ≠ 0 := by
  obtain ⟨L, hL, rfl⟩ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion G A).1 hA
  rw [GlobalTheory.GLq.LabelMul.ip_sum_eq_count hψ L hL] at hψA
  have hm : ψ ∈ L := List.count_pos_iff.1 (Nat.pos_of_ne_zero (by exact_mod_cast hψA))
  obtain ⟨N, hN, hN0⟩ := list_nat_sum L hL B hB
  rw [ip_list_sum_left, hN]
  exact_mod_cast hN0 ψ hm hψB

theorem ip_add_ne_zero {G : Type} [Group G] [Fintype G] {ψ X Y : G → ℂ} (hψ : IsIrr ψ) (hX : IsChar X)
    (hY : IsChar Y) (h : ip ψ X ≠ 0) : ip ψ (X + Y) ≠ 0 := by
  rw [GlobalTheory.GLq.LabelMul.ip_add_right]
  obtain ⟨k, hk⟩ := GlobalTheory.GLq.LabelMul.ip_nat hψ hX
  obtain ⟨l, hl⟩ := GlobalTheory.GLq.LabelMul.ip_nat hψ hY
  rw [hk] at h
  have hk0 : k ≠ 0 := by exact_mod_cast h
  rw [hk, hl]
  exact_mod_cast (show k + l ≠ 0 by omega)

theorem isChar_hcL_cusp (K : List (Pc g)) (hK : ∀ p ∈ K, IsCusp p.2) (m : ℕ) (hm : degL K = m) :
    IsChar (hcL K m) :=
  (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g K K m hm.symm (fun p hp => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (hK p hp))).1

theorem ip_hc_left (m : ℕ) (ψ : Gn g (m + 1) → ℂ) (hψ : IsIrr ψ) (σ : Gn g m → ℂ) (hσ : IsIrr σ)
    (β : Gn g 1 → ℂ) (hβ : IsChar β) (K : List (Pc g)) (hK : ∀ p ∈ K, IsCusp p.2) (hd : degL K = m)
    (hσK : ip σ (hcL K m) ≠ 0) (h : ip ψ (hc m 1 σ β (m + 1)) ≠ 0) : ip ψ (hc m 1 (hcL K m) β (m + 1)) ≠ 0 := by
  obtain ⟨R, hR, he⟩ := GlobalTheory.GLq.LabelMul.exists_add_of_ip_ne_zero hσ (isChar_hcL_cusp K hK m hd) hσK
  rw [he, GlobalTheory.GLq.LabelMul.hc_add_left]
  have hc := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g m 1 (m + 1) rfl).1
  exact ip_add_ne_zero hψ (hc σ β (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hσ) hβ) (hc R β hR hβ) h

theorem ip_hc_right (m : ℕ) (ψ : Gn g (m + 1) → ℂ) (hψ : IsIrr ψ) (σ : Gn g m → ℂ) (hσ : IsIrr σ)
    (β : Gn g 1 → ℂ) (hβ : IsChar β) (K : List (Pc g)) (hK : ∀ p ∈ K, IsCusp p.2) (hd : degL K = m)
    (hσK : ip σ (hcL K m) ≠ 0) (h : ip ψ (hc 1 m β σ (m + 1)) ≠ 0) : ip ψ (hc 1 m β (hcL K m) (m + 1)) ≠ 0 := by
  obtain ⟨R, hR, he⟩ := GlobalTheory.GLq.LabelMul.exists_add_of_ip_ne_zero hσ (isChar_hcL_cusp K hK m hd) hσK
  rw [he, GlobalTheory.GLq.LabelMul.hc_add_right]
  have hc := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g 1 m (m + 1) (by omega)).1
  exact ip_add_ne_zero hψ (hc β σ hβ (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hσ)) (hc β R hβ hR) h

theorem eq_of_isCuspOf_det (L : LabelDatum g) (θ : (ZMod g)ˣ →* ℂˣ) (c : ZMod g) (h : GlobalTheory.GLp.IsCharLab L θ c)
    (P : (ZMod g)[X])
    (hP : IsCuspOf L P (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ))) : P = X - C c := by
  obtain ⟨⟨hm, -, h0, hdeg⟩, -, hf⟩ := hP
  have hPe : P = X - C (-P.coeff 0) := by
    rw [map_neg, sub_neg_eq_add]; exact hm.eq_X_add_C hdeg
  have hc'0 : -P.coeff 0 ≠ 0 := neg_ne_zero.2 h0
  obtain ⟨u, hu⟩ := GlobalTheory.GLq.LabelDet.gen_one_mem L
  let y : Gn g 1 := Units.map (Matrix.scalar (Fin 1) : ZMod g →+* Mt g 1).toMonoidHom u
  have hy00 : (y : Mt g 1) 0 0 = u := by simp [y]
  have hcp : (y : Mt g 1).charpoly = X - C ((y : Mt g 1) 0 0) := by
    simp [Matrix.charpoly, Matrix.det_fin_one]
  have hx : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (-P.coeff 0) ∈ Formalism.CyclotomicNorms.rootsBar P := by
    rw [hPe]; simp [Formalism.CyclotomicNorms.rootsBar]
  have hz : L.gen 1 ∈ Formalism.CyclotomicNorms.rootsBar (y : Mt g 1).charpoly := by
    rw [hcp, hy00, ← hu]; simp [Formalism.CyclotomicNorms.rootsBar]
  have hirr : Irreducible (y : Mt g 1).charpoly := by rw [hcp]; exact irreducible_X_sub_C _
  have key := hf _ hx y hirr _ hz
  have hxp : (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (-P.coeff 0)) ^ (g ^ 1 - 1) = 1 := by
    rw [← map_pow, pow_one, ZMod.pow_card_sub_one_eq_one hc'0, map_one]
  have hth := GlobalTheory.GLq.LabelDet.theta_gen_pow L hxp 1
  rw [pow_one, pow_one] at hth
  have hdet : Matrix.GeneralLinearGroup.det y = u := by ext; simp [y, Matrix.det_fin_one]
  simp only [hdet, Nat.sub_self, pow_zero, one_mul, Finset.sum_range_one, pow_one, hth] at key
  rw [h.2 u hu] at key
  have := L.teich_inj _ _ ((_root_.map_ne_zero _).2 h.1) ((_root_.map_ne_zero _).2 hc'0) key
  rw [hPe, (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective this]

end GlobalTheory.GLq.DetRoot

namespace GlobalTheory.GLq.DetRoot

open scoped Classical

theorem root_of_hc_det : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (ψ : Gn g (n + 1) → ℂ) (f : (ZMod g)[X]),
    IsIrr ψ → HasLabel L ψ f → ∀ (σ : Gn g n → ℂ), IsIrr σ → ∀ (θ : (ZMod g)ˣ →* ℂˣ) (c : ZMod g),
    GlobalTheory.GLp.IsCharLab L θ c →
    (ip ψ (hc n 1 σ (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (n + 1)) ≠ 0 → f.IsRoot c) ∧
    (ip ψ (hc 1 n (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) σ (n + 1)) ≠ 0 → f.IsRoot c) := by
  intro g _ L n ψ f hψ hL σ hσ θ c hlab
  obtain ⟨Q, hQ, hQd, rfl, hQi⟩ := hL
  obtain ⟨K, hK, hKd, hKi⟩ := GlobalTheory.GLq.SuppCusp.exists_cusp_list g n σ hσ
  subst hKd
  have hβI : IsIrr (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) :=
    GlobalTheory.GLq.LabelDet.isIrr_hom (θ.comp Matrix.GeneralLinearGroup.det)
  have hβC := GlobalTheory.GLq.LabelMul.isChar_of_isIrr hβI
  have hβcusp : IsCusp (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) :=
    ⟨one_pos, hβI, fun a h1 h2 => by omega⟩
  have hQc : ∀ p ∈ Q.map Prod.snd, IsCusp p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact (hQ q hq).2.1
  have hA := isChar_hcL_cusp _ hQc _ hQd

  have fin : ∀ K' : List (Pc g), (Q.map Prod.snd).Perm K' →
      (⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) ∈ K' →
      ((Q.map Prod.fst).prod).IsRoot c := by
    intro K' hp hm
    obtain ⟨⟨P, s⟩, hq, hs⟩ := List.mem_map.1 (hp.mem_iff.2 hm)
    dsimp only at hs
    subst hs
    have hP := eq_of_isCuspOf_det L θ c hlab P (hQ _ hq)
    have hdvd : P ∣ (Q.map Prod.fst).prod := List.dvd_prod (List.mem_map.2 ⟨_, hq, rfl⟩)
    exact Polynomial.IsRoot.dvd (by rw [hP]; exact root_X_sub_C.2 rfl) hdvd
  have hbc : ∀ p ∈ [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)], IsCusp p.2 := by
    intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact hβcusp
  have hKc := fun p hp => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (hK p hp)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h2 := ip_hc_left _ ψ hψ σ hσ _ hβC K hK rfl hKi h
    have e2 : hc (degL K) 1 (hcL K (degL K))
        (hcL [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)] 1) (degL K + 1) =
        hcL (K ++ [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)]) (degL K + 1) :=
      (GlobalTheory.GLq.LabelMul.hcL_append K _ hKc (fun p hp => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (hbc p hp))
        (degL K + 1) (by simp [degL])).symm
    rw [GlobalTheory.GLq.IpCuspProd.hcL_single 1 _ (GlobalTheory.GLq.IpCuspProd.isClass_of_isChar hβC)] at e2
    rw [e2] at h2
    have hKd' : degL (K ++ [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)]) =
        degL K + 1 := by simp [degL]
    have hB := isChar_hcL_cusp _ (fun p hp => by
      rcases List.mem_append.1 hp with hp | hp
      · exact hK p hp
      · exact hbc p hp) _ hKd'
    have hAB := ip_ne_zero_of_common hψ hA hB hQi h2
    refine fin (K ++ [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)]) ?_
      (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)))
    by_contra hn
    exact hAB ((GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp g _ _ _ hQd hKd' hQc (fun p hp => by
      rcases List.mem_append.1 hp with hp | hp
      · exact hK p hp
      · exact hbc p hp)).1 hn)
  · have h2 := ip_hc_right _ ψ hψ σ hσ _ hβC K hK rfl hKi h
    have e2 : hc 1 (degL K) (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (hcL K (degL K))
        (degL K + 1) =
        hcL ((⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) :: K) (degL K + 1) :=
      (hcL_cons (⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) K (degL K + 1)).symm
    rw [e2] at h2
    have hKd' : degL ((⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) :: K) =
        degL K + 1 := by simp [degL]; omega
    have hKc' : ∀ p ∈ (⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) :: K,
        IsCusp p.2 := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hβcusp
      · exact hK p hp
    have hB := isChar_hcL_cusp _ hKc' _ hKd'
    have hAB := ip_ne_zero_of_common hψ hA hB hQi h2
    refine fin ((⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) :: K) ?_
      List.mem_cons_self
    by_contra hn
    exact hAB ((GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp g _ _ _ hQd hKd' hQc hKc').1 hn)

end GlobalTheory.GLq.DetRoot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedOfPhiEquationDisc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_root_radii (l : ℕ) (hl : 2 ≤ l) (ρ₀ : ℝ≥0) (h0 : 0 < ρ₀) (h1 : ρ₀ < 1) :
    ∃ r : ℕ → ℝ≥0, r 0 = ρ₀ ∧ (∀ n, r (n + 1) ^ l = r n) ∧ (∀ n, ρ₀ ≤ r n) ∧ (∀ n, r n < 1) ∧
      ∀ ρ₁ : ℝ≥0, ρ₁ < 1 → ∃ n, ρ₁ ≤ r n := by
  have hl0 : l ≠ 0 := by omega
  let r : ℕ → ℝ≥0 := fun n => ρ₀ ^ (((l ^ n : ℕ) : ℝ)⁻¹)
  have hp : ∀ n, r n ^ (l ^ n) = ρ₀ := fun n => NNReal.rpow_inv_natCast_pow _ (pow_ne_zero _ hl0)
  have hlt : ∀ n, r n < 1 := fun n => by
    by_contra h
    have := one_le_pow₀ (not_lt.1 h) (n := l ^ n)
    rw [hp] at this
    exact absurd h1 (not_lt.2 this)
  refine ⟨r, by simpa using hp 0, fun n => ?_, fun n => ?_, hlt, fun ρ₁ h => ?_⟩
  · refine (pow_left_inj₀ zero_le zero_le (pow_ne_zero n hl0)).1 ?_
    rw [← pow_mul, ← pow_succ', hp, hp]
  · rw [← hp n]
    exact pow_le_of_le_one zero_le (hlt n).le (pow_ne_zero _ hl0)
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one h0 h
    refine ⟨n, le_of_lt (lt_of_pow_lt_pow_left₀ (l ^ n) zero_le ?_)⟩
    rw [hp]
    exact (pow_le_pow_of_le_one zero_le h.le (Nat.lt_pow_self (by omega)).le).trans_lt hn

theorem norm_l_pow_mul_disc (l : ℕ) [Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (k : ℕ)
    (y : Disc l u ρ) : ‖((l : ℕ) : Disc l u ρ) ^ k * y‖ = ‖y‖ / (l : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A u ρ).2.1, ih, div_div, pow_succ]

theorem exists_bounded_of_phi_equation : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ (φ : A →+* A), φ (s X) = s X ^ l → ∀ (Φ : Disc l (s X) bk.ρ₀ →+* Disc l (s X) bk.ρ₀), IsDiscMap φ Φ → ∀ (κ : Type) (c : κ → κ → A), (∀ i (n : ℕ), {j | c i j ∉ (bk.J ^ n).map s}.Finite) → ∀ (h : ℕ) (V : κ → Disc l (s X) bk.ρ₀), Filter.Tendsto V Filter.cofinite (nhds 0) → (∀ j, HasSum (fun i => Φ (V i) * toDisc l (s X) bk.ρ₀ (c i j)) (toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * V j)) → ∃ (k : ℕ) (v : κ → A), (∀ j, toDisc l (s X) bk.ρ₀ (v j) = (l : Disc l (s X) bk.ρ₀) ^ k * V j) ∧ ∀ n : ℕ, {j | v j ∉ (bk.J ^ n).map s}.Finite := by
  intro l hl K bk A _ s ι tb φ hφ Φ hΦ κ c hc h V hV hs
  obtain ⟨-, -, ⟨h0, h1, -⟩, -⟩ := GlobalTheory.T.breuilKisin_flat_radius_ideal_facts l K bk
  have hl2 := hl.out.two_le
  obtain ⟨r, r0, rs, rle, rlt, rlim⟩ := exists_root_radii l hl2 bk.ρ₀ h0 h1
  have rpos : ∀ n, 0 < r n := fun n => h0.trans_le (rle n)
  have hR : ∀ n, ∃ R : Disc l (s X) (r n) →+* Disc l (s X) bk.ρ₀, IsDiscMap (RingHom.id A) R := fun n =>
    GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd l A A (RingHom.id A) (s X) (s X) (r n) bk.ρ₀ 1 h0 (by simp) (by simpa using rle n)
  choose R hR using hR
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ j, ‖V j‖ ≤ C := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto_cofinite hV)
    exact ⟨max C 0, le_max_right _ _, fun j => (hC _ ⟨j, rfl⟩).trans (le_max_left _ _)⟩
  set m := bk.Ep.natDegree * h with hm
  have h0' : (0 : ℝ) < bk.ρ₀ := h0
  have key : ∀ n, ∃ U : κ → Disc l (s X) (r n), Filter.Tendsto U Filter.cofinite (nhds 0) ∧
      (∀ j, R n (U j) = V j) ∧ ∀ j, ‖U j‖ ≤ C * ((r n : ℝ) / bk.ρ₀) ^ m := by
    intro n
    induction n with
    | zero =>
      have gen : ∀ (ρ : ℝ≥0) (R₀ : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀), ρ = bk.ρ₀ →
          IsDiscMap (RingHom.id A) R₀ → ∃ U : κ → Disc l (s X) ρ, Filter.Tendsto U Filter.cofinite (nhds 0) ∧
          (∀ j, R₀ (U j) = V j) ∧ ∀ j, ‖U j‖ ≤ C * ((ρ : ℝ) / bk.ρ₀) ^ m := by
        rintro ρ R₀ rfl hR₀
        refine ⟨V, hV, fun j => ?_, fun j => ?_⟩
        · rw [hR₀.unique (isDiscMap_id l (s X) bk.ρ₀)]; rfl
        · rw [div_self h0'.ne', one_pow, mul_one]; exact hC j
      exact gen _ _ r0 (hR 0)
    | succ n ih =>
      obtain ⟨U, hU, hRU, hn⟩ := ih
      obtain ⟨U', hU', hRU', hn'⟩ := GlobalTheory.T.exists_phiContraction_disc_step l K bk A s ι tb φ hφ Φ hΦ κ c hc h V hs (r n) (r (n + 1))
        (rle n) (rlt n) (rs n) (R n) (R (n + 1)) (hR n) (hR (n + 1)) U _ (by positivity) hU hRU hn
      refine ⟨U', hU', hRU', fun j => ?_⟩
      have hp : (0 : ℝ) < r (n + 1) := rpos _
      have hle : (r n : ℝ) ≤ r (n + 1) * r (n + 1) := by
        have : r n ≤ r (n + 1) ^ 2 := by
          rw [← rs n]; exact pow_le_pow_of_le_one zero_le (rlt _).le hl2
        rw [← sq]; exact_mod_cast this
      refine le_of_mul_le_mul_left ((hn' j).trans ?_) (pow_pos hp m)
      rw [mul_left_comm, ← mul_pow, ← mul_div_assoc]
      gcongr
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (C * (1 / (bk.ρ₀ : ℝ)) ^ m)
    (show (1 : ℝ) < l by exact_mod_cast hl.out.one_lt)
  have hlk : (0 : ℝ) < (l : ℝ) ^ k := pow_pos (Nat.cast_pos.2 hl.out.pos) k
  have hv : ∀ j, ∃ a, toDisc l (s X) bk.ρ₀ a = (l : Disc l (s X) bk.ρ₀) ^ k * V j := fun j =>
    GlobalTheory.T.exists_base_eq_of_closedDisc_extends_norm_le_one l K bk A s ι tb bk.ρ₀ h0 h1 _ fun ρ₁ hρ₁ => by
      obtain ⟨n, hn⟩ := rlim ρ₁ hρ₁
      obtain ⟨U, -, hRU, hU⟩ := key n
      refine ⟨r n, R n, (l : Disc l (s X) (r n)) ^ k * U j, hn, rle n, rlt n, hR n, ?_, ?_⟩
      · rw [map_mul, map_pow, map_natCast, hRU]
      · rw [norm_l_pow_mul_disc, div_le_one hlk]
        refine (hU j).trans (le_trans ?_ hk.le)
        have : (r n : ℝ) ≤ 1 := (rlt n).le
        gcongr
  choose v hv using hv
  refine ⟨k, v, hv, fun n => ?_⟩
  obtain ⟨ε, hε, hJ⟩ := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk A s ι tb bk.ρ₀ h0 h1).2.1 n
  have ht : Filter.Tendsto (fun j => (l : Disc l (s X) bk.ρ₀) ^ k * V j) Filter.cofinite (nhds 0) := by
    simpa using hV.const_mul ((l : Disc l (s X) bk.ρ₀) ^ k)
  have he := Filter.eventually_cofinite.1 (ht.eventually (Metric.closedBall_mem_nhds 0 hε))
  refine he.subset fun j hj hj' => hj (hJ _ ?_)
  rw [hv]
  simpa using hj'

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescentSolutionLiftModPrismIdealStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descent_solution_lift_mod_prism_ideal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D), Cover h → IsPO h h p q → ∀ z : Fin d → C.A, (∀ i, p.f (z i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) i ∈ adI D ^ 1) → ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ 1) ∧ (fun i => p.f (z' i)) = (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z' j)) := by
  first | exact @GlobalTheory.BSP.lift_solution | exact GlobalTheory.BSP.lift_solution | (intros; apply GlobalTheory.BSP.lift_solution <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleOEBasisOfIsogenousLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_OE_basis_of_isogenous_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ'' : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Pre bk N d ρ) (f : Matrix (Fin d) (Fin d) (ℤ_[l])), f.det ≠ 0 → (∀ g, IsUnit (ρ'' g)) → (∀ g, f * ρ'' g = ρ g * f) → ∃ T'' P : Matrix (Fin d) (Fin d) (WCb l), IsUnit T'' ∧ (∀ i j, P i j ∈ bk.OE) ∧ zW f * T'' = F.T * P := by
  first | exact @GlobalTheory.EtBasis.main | exact GlobalTheory.EtBasis.main | (intros; apply GlobalTheory.EtBasis.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldElementRelativeApproxCompletionsStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_field_element_relative_approx_completions : ∀ (L : Type) [Field L] [NumberField L] (R : Finset (HeightOneSpectrum (𝓞 L))) (z : ∀ P : HeightOneSpectrum (𝓞 L), P.adicCompletion L), (∀ P ∈ R, z P ≠ 0) → ∃ k : Lˣ, ∀ P ∈ R, Valued.v (z P - algebraMap L (P.adicCompletion L) (k : L)) ≤ WithZero.exp (-1 : ℤ) * Valued.v (z P) := by
  first | exact @GlobalTheory.WeakApprox.exists_units_approx | exact GlobalTheory.WeakApprox.exists_units_approx | (intros; apply GlobalTheory.WeakApprox.exists_units_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteChosenSet
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial
  GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.OChoose

theorem placesOver_nonempty (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    (placesOver E p).Nonempty := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 E) := by
    intro hu
    have h1 := hu.map (Algebra.norm ℤ : 𝓞 E →* ℤ)
    rw [show ((p : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) by simp, Algebra.norm_algebraMap] at h1
    have h2 := Int.isUnit_iff_natAbs_eq.1 h1
    have h3 : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h2
    rcases Nat.pow_eq_one.1 h2 with h | h
    · exact hp.one_lt.ne' h
    · exact h3.ne' h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 E)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : ((p : ℕ) : 𝓞 E) ∈ M := hle (Ideal.subset_span rfl)
  refine ⟨⟨M, hM.isPrime, fun h => ?_⟩, hmem⟩
  rw [h, Ideal.mem_bot] at hmem
  exact hp.ne_zero (by exact_mod_cast hmem)

theorem exists_wild_inertia_cyclotomic_generator (D : D7) (i : D.nd.Loc) : ∃ g0, IsWildInertiaCyclotomicElement D.nd i g0 := by
  by_cases ht : ∃ k, D.nd.l i = D.host.g k
  · obtain ⟨k, hk⟩ := ht
    obtain ⟨g0, h1, h2, h3⟩ := GlobalTheory.T.exists_wildInertia_generating_cyclotomicValue D i k hk
    exact ⟨g0, ⟨h1, h2⟩, fun _ => h3⟩
  · obtain ⟨w, hw⟩ := placesOver_nonempty D.host.E (D.nd.l i) (D.nd.lPrime i).out
    obtain ⟨g, hg, hc⟩ := GlobalTheory.EpsInertia.epsAll D i w hw 1
    exact ⟨g, ⟨⟨w, hw, hg⟩, 1, by simpa using hc⟩, fun h => absurd h ht⟩

theorem exists_fin_roots {p : ℂ[X]} {t : ℕ} (hm : p.Monic) (hd : p.natDegree = t) :
    ∃ α : Fin t → ℂ, (∀ c, α c ∈ p.roots) ∧ p = ∏ c, (X - C (α c)) := by
  have hcard : Multiset.card p.roots = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hp := (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hcard).symm
  obtain ⟨l, hl⟩ : ∃ l : List ℂ, (l : Multiset ℂ) = p.roots := Quotient.exists_rep _
  have hlen : l.length = t := by rw [← hd, ← hcard, ← hl, Multiset.coe_card]
  subst hlen
  refine ⟨fun c => l.get c, fun c => hl ▸ Multiset.mem_coe.2 (List.get_mem l c), ?_⟩
  conv_lhs => rw [hp, ← hl]
  rw [Multiset.map_coe, Multiset.prod_coe]
  rw [← List.prod_ofFn]
  congr 1
  apply List.ext_get (by simp)
  intro n h1 h2
  simp

theorem blockPol_iota (D : D7) (i : D.nd.Loc) {rep : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))}
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.HidaSetting D.R.t (D.nd.T i) (D.nd.Z i) rep ρ (D.nd.chi i)) {π : D.nd.X i} {g0 : GE D.nd}
    {L : ℕ} {eB e1 X0 : D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)}
    (hc : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsChoice D.R.t (D.nd.T i) rep ρ (D.nd.chi i) π g0 L eB e1 X0) (x : D.nd.X i) :
    ((GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.blockPol (eB x) (X0 x)).map (iotaO D.nd D.naut i)).Monic ∧
      ((GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.blockPol (eB x) (X0 x)).map (iotaO D.nd D.naut i)).natDegree = D.R.t := by
  obtain ⟨hr, -, -, hX1, hX2, -⟩ := GlobalTheory.ConsExists.choice_facts hS.1 hS.2.2.2.1 hc
  obtain ⟨hm, hd⟩ := GlobalTheory.ConsExists.blockPol_monic (congrFun hc.1.2.2.1 x) (hr x) (congrFun hX1 x) (congrFun hX2 x)
  have hinj : Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.toFr (D.nd.O i)) :=
    IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))
  have hm' := Polynomial.monic_of_injective hinj hm
  rw [Polynomial.natDegree_map_eq_of_injective hinj] at hd
  exact ⟨hm'.map _, (hm'.natDegree_map _).trans hd⟩

theorem oChoose : GlobalTheory.TwSys.Cheb → ∀ (D : D7), SumRepresentations.Conclusion41 D → GlobalTheory.SplitCoef.OSplit D → ∀ i : D.nd.Loc,
    ZDecomp D.nd i → Live D.nd i → ∃ S : Finset ℂ, Chosen D.nd D.naut i ↑S := by
  intro hC D hP hO i hZ hL
  classical
  obtain ⟨rep, ρ, hG, hS⟩ := GlobalTheory.T.exists_decomposition_setting hC D hP hO i hZ hL
  obtain ⟨g0, hg0⟩ := exists_wild_inertia_cyclotomic_generator D i
  have hcont : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.RepCont D.nd i rep := fun x => (hG x).1
  have ha := (GlobalTheory.ConsExists.consExist D.nd i rep ρ (D.nd.O i) (D.nd.T i) rep ρ (D.nd.chi i) hcont
    (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.isEnlargement_self D.nd i rep ρ) hS).1
  have hch : ∀ π : D.nd.Z i, ∃ q : (D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)) ×
      (D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)) ×
      (D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)),
      GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsChoice D.R.t (D.nd.T i) rep ρ (D.nd.chi i) π g0 0 q.1 q.2.1 q.2.2 := fun π => by
    obtain ⟨eB, e1, X0, h⟩ := ha π π.2 g0 hg0.1 0
    exact ⟨(eB, e1, X0), h⟩
  choose q hq using hch
  refine ⟨Finset.univ.biUnion fun π : D.nd.Z i => Finset.univ.biUnion fun x : D.nd.X i =>
    ((GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.blockPol ((q π).1 x) ((q π).2.2 x)).map (iotaO D.nd D.naut i)).roots.toFinset,
    rep, ρ, hG, hS, fun π hπ => ?_⟩
  refine ⟨g0, 0, (q ⟨π, hπ⟩).1, (q ⟨π, hπ⟩).2.1, (q ⟨π, hπ⟩).2.2, hg0, hq ⟨π, hπ⟩, fun x => ?_⟩
  obtain ⟨hm, hd⟩ := blockPol_iota D i hS (hq ⟨π, hπ⟩) x
  obtain ⟨α, hα, he⟩ := exists_fin_roots hm hd
  refine ⟨α, fun c => Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨⟨π, hπ⟩, Finset.mem_univ _,
    Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _, Multiset.mem_toFinset.2 (hα c)⟩⟩), he⟩

end GlobalTheory.OChoose

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusMatrixMulEqEPowOfPeriodStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_matrix_mul_eq_E_pow_of_period : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (Y S' : Matrix (Fin d) (Fin d) (Ainf l)) (A : Matrix (Fin d) (Fin d) (bk.S)) (k M : ℕ), IsUnit (Y.map (inclW l)) → Y * S' = ((l : Ainf l) ^ k * τ ^ M) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → Y.map WittVector.frobenius = Y * A.map bk.ev → ∃ (b : ℕ) (A' : Matrix (Fin d) (Fin d) (bk.S)), A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) (bk.S)) := by
  first | exact @GlobalTheory.BSP.HeightAprime.main | exact GlobalTheory.BSP.HeightAprime.main | (intros; apply GlobalTheory.BSP.HeightAprime.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainMassOneCocompactLatticeStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ [MeasurableSpace G] [BorelSpace G], ∃ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1 := by
  first | exact @GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one | exact GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one | (intros; apply GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGenericConstituentHarishChandraCuspidalStatement
section
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generic_constituent_harishChandra_cuspidal : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (L : List (Pc g)) (n : ℕ), degL L = n → (∀ p ∈ L, IsCusp p.2) → ∃ ρ : Gn g n → ℂ, IsIrr ρ ∧ wh ψ ρ ≠ 0 ∧ ip ρ (hcL L n) ≠ 0 := by
  first | exact @GlobalTheory.GLq.GenericConstituent.exists_generic_constituent | exact GlobalTheory.GLq.GenericConstituent.exists_generic_constituent | (intros; apply GlobalTheory.GLq.GenericConstituent.exists_generic_constituent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantBasisDeRhamBreuilKisinStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_basis_deRham_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (C : Core l) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), F.IsDR → Y.map (inclW l) = inclW l τ ^ N • F.T → ∃ (B : Matrix (Fin d) (Fin d) (Per.BdRp l)) (Q : Matrix (Fin d) (Fin d) (Per.BdR l)), IsUnit B ∧ IsUnit Q ∧ (∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) (bk.S)), ∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l m) ∧ (algebraMap (Per.BdRp l) (Per.BdR l)) (aDp l (bk.ev bk.E * τ)) ^ N • Q = ((Y * F.A.map bk.ev).map (aDp l) * B).map (algebraMap (Per.BdRp l) (Per.BdR l)) ∧ ∀ g : ↥(GK K), (ρ g).map (Per.zD l) * Q.map (Per.σD (g : GQ l)) = Q := by
  first | exact @GlobalTheory.BKLim.InvBasis.exists_invariant_basis | exact GlobalTheory.BKLim.InvBasis.exists_invariant_basis | (intros; apply GlobalTheory.BKLim.InvBasis.exists_invariant_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsModificationOfFiltrationStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_modification_of_filtration_alt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (d : ℕ) (U U' : Matrix (Fin d) (Fin d) (Per.BdR l)), U * U' = 1 → ∀ (N m : ℕ) (k : Fin m → ℤ) (c : Matrix (Fin d) (Fin m) (↥(OL K))) (β : Matrix (Fin m) (Fin d) (Per.BdR l)), (∀ i, |k i| ≤ N) → (∀ r s, U r s ∈ Per.FilD l (-(N : ℤ))) → (∀ r i, (U * c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom))) r i ∈ Per.FilD l (k i)) → (∀ i j, β i j ∈ Per.FilD l (-k i)) → U * c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) * β = 1 → ∃ (c₂ : ℕ) (X X' : Matrix (Fin d) (Fin d) (bk.S)), X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, ∀ i j, BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (X'.map (BK.hf f) * X.map (BK.hf g)) i j) ∧ (∀ i j, (U * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j ∈ Per.FilD l N) ∧ (∀ i j, (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U') i j ∈ Per.FilD l N) := by
  first | exact @GlobalTheory.BKModif.exists_modification_of_filtration | exact GlobalTheory.BKModif.exists_modification_of_filtration | (intros; apply GlobalTheory.BKModif.exists_modification_of_filtration <;> assumption)
end

