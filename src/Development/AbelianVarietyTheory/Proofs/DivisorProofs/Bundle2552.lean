import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0955
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTranslateTermsJetsBounded
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow

theorem jc_bound_k (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V))
    (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C]
    (hC : CExt V (IsLocalRing.maximalIdeal V) C) (N : NumD C) (ν : NumOf D.toPre C N) (hν : ν.IntN)
    (q : QuadraticMap ℤ N.X ℝ) (hq : N.Int q) (k : ℕ) (hk1 : 1 ≤ k) (s : Fam D.toPre C k) (gm₀ : GtPt D.toPre (epsR V))
    (gm : GtPt D.toPre (TE V C)) (htan : GtTan gm₀) (hpull : GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm) :
    ∃ b : ℝ, ∀ α, ‖(jc ν s gm α).fst / ν.rg ^ k‖ ≤ b * Real.exp (-(q α / (k : ℝ))) ∧
      ‖(jc ν s gm α).snd / ν.rg ^ k‖ ≤ b * Real.exp (-(q α / (k : ℝ))) := by
  have H1 := GlobalTheory.T.familyTerm_translate_bound_functionalEquation V D C hC N ν hν q hq k hk1 s gm₀ gm htan hpull
  have H2 := GlobalTheory.T.translate_section_values_bounded_integral_tangent V D C hC N ν hν k hk1 s gm₀ gm htan hpull
  choose bb hbb using H2
  have hk0 : (0 : ℤ) < k := by exact_mod_cast hk1
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
  let bs := Module.Free.chooseBasis ℤ N.X
  let g : (Module.Free.ChooseBasisIndex ℤ N.X → Fin k) → N.X := fun c => ∑ i, ((c i : ℕ) : ℤ) • bs i
  let quo : N.X → N.X := fun χ => ∑ i, (bs.repr χ i / (k : ℤ)) • bs i
  let cOf : N.X → Module.Free.ChooseBasisIndex ℤ N.X → Fin k := fun χ i =>
    ⟨(bs.repr χ i % (k : ℤ)).toNat, by
      have h1 := Int.emod_nonneg (bs.repr χ i) hk0.ne'
      have h2 := Int.emod_lt_of_pos (bs.repr χ i) hk0
      omega⟩
  have hdec : ∀ χ, χ = g (cOf χ) + k • quo χ := by
    intro χ
    have e1 : ∀ i, (((cOf χ i : ℕ) : ℤ)) = bs.repr χ i % (k : ℤ) := fun i =>
      Int.toNat_of_nonneg (Int.emod_nonneg _ hk0.ne')
    have e2 : k • quo χ = ∑ i, ((k : ℤ) * (bs.repr χ i / (k : ℤ))) • bs i := by
      rw [← natCast_zsmul, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
    rw [e2]
    simp only [g, e1, ← Finset.sum_add_distrib, ← add_smul]
    conv_lhs => rw [← bs.sum_repr χ]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    have := Int.mul_ediv_add_emod (bs.repr χ i) (k : ℤ)
    linarith
  have hqk : ∀ a mu : N.X, q (a + k • mu) = q a + (k : ℝ) ^ 2 * q mu + (k : ℝ) * QuadraticMap.polar q mu a := by
    intro a mu
    have e1 : q (k • mu + a) = q (k • mu) + q a + QuadraticMap.polar q (k • mu) a := by
      simp only [QuadraticMap.polar]; ring
    have e2 : q (k • mu) = ((k : ℤ) * (k : ℤ)) • q mu := by
      rw [← natCast_zsmul]; exact QuadraticMap.map_smul q _ _
    have e3 : QuadraticMap.polar q (k • mu) a = (k : ℤ) • QuadraticMap.polar q mu a := by
      rw [← natCast_zsmul]; exact QuadraticMap.polar_smul_left q _ _ _
    rw [add_comm, e1, e2, e3, zsmul_eq_mul, zsmul_eq_mul]
    push_cast; ring
  have hexp : ∀ a mu : N.X, Real.exp (-((k : ℝ) * q mu + QuadraticMap.polar q mu a)) =
      Real.exp (q a / k) * Real.exp (-(q (a + k • mu) / k)) := by
    intro a mu
    rw [← Real.exp_add, hqk]
    congr 1
    field_simp
    ring
  let B : ℝ := ∑ c, max 0 (bb (g c) * Real.exp (q (g c) / k))
  have hB : ∀ c, bb (g c) * Real.exp (q (g c) / k) ≤ B := fun c =>
    (le_max_right _ _).trans (Finset.single_le_sum (f := fun c => max 0 (bb (g c) * Real.exp (q (g c) / k)))
      (fun _ _ => le_max_left _ _) (Finset.mem_univ c))
  refine ⟨‖ν.rg ^ k‖⁻¹ * B, fun α => ?_⟩
  have hα := hdec α
  obtain ⟨h1, h2⟩ := H1 (g (cOf α)) (quo α)
  obtain ⟨h3, h4⟩ := hbb (g (cOf α)) (quo α)
  have hE := hexp (g (cOf α)) (quo α)
  rw [← hα] at h1 h2 hE
  have key : ∀ x : ℝ, x ≤ Real.exp (-((k : ℝ) * q (quo α) + QuadraticMap.polar q (quo α) (g (cOf α)))) * bb (g (cOf α)) →
      x ≤ B * Real.exp (-(q α / k)) := by
    intro x hx
    refine hx.trans ?_
    rw [hE]
    calc Real.exp (q (g (cOf α)) / k) * Real.exp (-(q α / k)) * bb (g (cOf α)) =
        (bb (g (cOf α)) * Real.exp (q (g (cOf α)) / k)) * Real.exp (-(q α / k)) := by ring
      _ ≤ B * Real.exp (-(q α / k)) := mul_le_mul_of_nonneg_right (hB _) (Real.exp_pos _).le
  have hE0 := Real.exp_pos (-((k : ℝ) * q (quo α) + QuadraticMap.polar q (quo α) (g (cOf α))))
  have hr0 : 0 ≤ ‖ν.rg ^ k‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
  constructor
  · rw [norm_div, div_eq_mul_inv, mul_comm, _root_.mul_assoc]
    exact mul_le_mul_of_nonneg_left (key _ (h1.trans (mul_le_mul_of_nonneg_left h3 hE0.le))) hr0
  · rw [norm_div, div_eq_mul_inv, mul_comm, _root_.mul_assoc]
    exact mul_le_mul_of_nonneg_left (key _ (h2.trans (mul_le_mul_of_nonneg_left (max_le h3 h4) hE0.le))) hr0

theorem jc_bound : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ q, N.Int q → ∀ (m : ℕ), Odd m → ∀ (p : N.QT (m ^ 2)) (s : Fam D.toPre C (m ^ 2)) (f : N.X → N.A → C), ν.FamV s f → IsEvFam N m p f → ∀ (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∃ b : ℝ, ∀ α, ‖(jc ν s gm α).fst / ν.rg ^ (m ^ 2)‖ ≤ b * Real.exp (-(q α / (m : ℝ) ^ 2)) ∧ ‖(jc ν s gm α).snd / ν.rg ^ (m ^ 2)‖ ≤ b * Real.exp (-(q α / (m : ℝ) ^ 2)) := by
  intro V _ _ _ D C _ _ _ _ _ hC N ν hν q hq m hm p s f hf hev gm₀ gm htan hpull
  have hk1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  obtain ⟨b, hb⟩ := jc_bound_k V D C hC N ν hν q hq (m ^ 2) hk1 s gm₀ gm htan hpull
  refine ⟨b, fun α => ?_⟩
  have hcast : (((m ^ 2 : ℕ) : ℝ)) = (m : ℝ) ^ 2 := by push_cast; ring
  rw [← hcast]
  exact hb α

end GlobalTheory.MBLow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsFrameTwoLevels
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.DivDeep

open GlobalTheory.ThetaCompare

theorem torsFrame_two_levels {S : Scheme.{0}} (P : PolAV S) {T : Over S} {m M : ℕ}
    {rig rig' : LB.Gen (P.L.pull (eSec P.A))} {x : T ⟶ P.A} {τ τ'} (H : IsTorsFrame P rig m x τ)
    (H' : IsTorsFrame P rig' M x τ') {y : T.left} {J} (hJ : Good P.L y J) :
    (val τ (𝟙 _) y J / val τ' (𝟙 _) y J) ^ (m ^ 2 * M ^ 2) =
      (val rig T.hom y J / val rig' T.hom y J) ^ (m ^ 2 * M ^ 2) := by
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have := P.isAb.comm
  obtain ⟨α, hα⟩ := GlobalTheory.EmbLocal.exists_mulPull hG P m T
  obtain ⟨β, hβ⟩ := GlobalTheory.EmbLocal.exists_mulPull hG P M T
  have a := torsFrame_pow hG P hα H hJ
  have b := torsFrame_pow hG P hβ H' hJ
  have rα := Reg.two (y := y) (J := J) α hα (snd T P.A) (snd T P.A ^ m) rfl rfl
  have rβ := Reg.two (y := y) (J := J) β hβ (snd T P.A) (snd T P.A ^ M) rfl rfl
  have c := (((rα.pow hJ (M ^ 2)).mul hJ (rβ.pull hJ (snd T P.A ^ m))).mul hJ
    ((rβ.pow hJ (m ^ 2)).mul hJ (rα.pull hJ (snd T P.A ^ M))).inv).const hG P.isAb P.isLB hJ (fun U _ h => by
      simp only [SymLiftOdd.comp_pow', lift_snd, ← pow_mul, mul_comm M m]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]
      module) x 1
  simp only [SymLiftOdd.comp_pow', pt_snd, H.1, H'.1, one_pow] at c
  apply Additive.ofMul.injective
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_div] at a b c ⊢
  linear_combination (norm := module) (M ^ 2) • a - (m ^ 2) • b + c

theorem exists_cst {K : Type} [Field K] (z : Sp K) : ∃ c : K →+* (Sp K).presheaf.stalk z, Function.Injective c ∧
    ∀ a, gs (𝟙 (Sp K)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) = c a :=
  ⟨((Sp K).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom, RingHom.injective _,
    fun _ => gs_eq (𝟙 _) z ⊤ trivial _⟩

theorem same_ratio {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
    {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} {ρ : S.Real} {ε} {ρ' : S'.Real} {ε'} {lab : S.Gam → S'.Gam} {φ : Ω →+* Ω'}
    (h : Same ρ ε ρ' ε' lab φ) (a b : S.Gam) :
    ∃ k, 0 < k ∧ (S'.th (lab a) * φ (S.th b)) ^ k = (S'.th (lab b) * φ (S.th a)) ^ k := by
  obtain ⟨P₀, f, f', -, gp, gp', lb, lb', -, hw⟩ := h
  choose w hw hw' using hw
  have hs : ∀ x, w x ≫ P₀.A.hom = 𝟙 _ := fun x => by
    have e : (w x ≫ P₀.A.hom) ≫ spMap S'.R.val.toRingHom = 𝟙 _ ≫ spMap S'.R.val.toRingHom := by
      rw [Category.assoc, ← gp'.1.w, ← Category.assoc, hw', Category.assoc, Over.w, Category.id_comp]
      exact Category.comp_id _
    haveI : IsFractionRing S'.R Ω' := IsFractionRing.of_field _ _ fun x => by
      obtain ⟨a, ha, b, hb, e⟩ := S'.frac x
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩
    haveI : IsPreimmersion (spMap S'.R.val.toRingHom) :=
      IsPreimmersion.of_isLocalization (R := S'.R) (S := Ω') (nonZeroDivisors S'.R)
    exact (cancel_mono _).1 e
  let x : S.Gam → (baseOver (Sp Ω') ⟶ P₀.A) := fun a => Over.homMk (w a) (hs a)
  obtain ⟨rig, τ, -, hτ, ht⟩ := FrameMove.exists_move (T := baseOver (Sp S.R)) (T' := baseOver (Sp Ω'))
    (h := spMap (φ.comp S.R.val.toRingHom)) gp lb ((Category.comp_id _).trans (Category.id_comp _).symm) ρ.rig_gen
    (x := ρ.pt) (x' := x) hw ρ.fr_tors
  obtain ⟨rig', τ', -, hτ', ht'⟩ := FrameMove.exists_move (T := baseOver (Sp S'.R)) (T' := baseOver (Sp Ω'))
    (h := spMap S'.R.val.toRingHom) gp' lb' ((Category.comp_id _).trans (Category.id_comp _).symm) ρ'.rig_gen
    (x := fun a => ρ'.pt (lab a)) (x' := x) hw' (fun a => ρ'.fr_tors (lab a))
  obtain ⟨t, ht⟩ := ht 1 ρ.th₁
  obtain ⟨t', ht'⟩ := ht' 1 ρ'.th₁
  let z : Sp Ω' := IsLocalRing.closedPoint Ω'
  obtain ⟨V, hV, hθ⟩ := GlobalTheory.EmbLocal.exists_isGenSec_near GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny P₀ z
  obtain ⟨θ, hθ⟩ := hθ Ω' (𝟙 _) (by rintro _ ⟨v, rfl⟩; rw [Subsingleton.elim v z]; exact hV)
  obtain ⟨r, hr⟩ := hθ t
  obtain ⟨r', hr'⟩ := hθ t'
  obtain ⟨J, hJ⟩ := ConstFam.exists_good' (Z := (baseOver (Sp Ω')).left) P₀.isLB z
  obtain ⟨c, hc, hcv⟩ : ∃ c : Ω' →+* (baseOver (Sp Ω')).left.presheaf.stalk z, Function.Injective c ∧
      ∀ a, gs (𝟙 (Sp Ω')) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω')).inv.hom a) = c a := exists_cst z
  have pf : ∀ {B : Scheme.{0}} {A T : Over B} {L : LB A.left} (x : T ⟶ A)
      (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))),
      powFrame A L x τ 1 = τ := fun x τ => congrArg LB.Gen.mk (funext fun j => zpow_one (τ.s j))
  have v : ∀ a, gs (𝟙 (baseOver (Sp Ω')).left) z ⊤ r * sval (L := P₀.L) (φ := fun _ : Fin 1 => (snd (baseOver (Sp Ω')) P₀.A).left)
      (ε := fun _ => 1) θ (ptSecT P₀.A (x a)).left z J = c (φ (S.th a)) * (val (τ a) (𝟙 _) z J).val := fun a => by
    have e := (sval_smul hr (x a) hJ).symm.trans (ht a _ (by rw [pf]; exact ρ.th_val a) z J hJ)
    rw [pf] at e
    exact e.trans (congrArg (· * _) ((FrameMove.gs_spMap _ z _).trans (hcv _)))
  have v' : ∀ a, gs (𝟙 (baseOver (Sp Ω')).left) z ⊤ r' * sval (L := P₀.L) (φ := fun _ : Fin 1 => (snd (baseOver (Sp Ω')) P₀.A).left)
      (ε := fun _ => 1) θ (ptSecT P₀.A (x a)).left z J = c (S'.th (lab a)) * (val (τ' a) (𝟙 _) z J).val := fun a => by
    have e := (sval_smul hr' (x a) hJ).symm.trans (ht' a _ (by rw [pf]; exact ρ'.th_val (lab a)) z J hJ)
    rw [pf] at e
    exact e.trans (congrArg (· * _) ((FrameMove.gs_spMap _ z _).trans (hcv _)))
  have q := (torsFrame_two_levels P₀ (hτ a) (hτ' a) hJ).trans (torsFrame_two_levels P₀ (hτ b) (hτ' b) hJ).symm
  have p₁ : 0 < S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  have p₂ : 0 < S'.r * S'.N := Nat.mul_pos S'.r_pos (by have := S'.N_ge; omega)
  refine ⟨(S.r * S.N) ^ 2 * (S'.r * S'.N) ^ 2, by positivity, hc ?_⟩
  generalize (S.r * S.N) ^ 2 * (S'.r * S'.N) ^ 2 = k at q
  have va := v a
  have vb := v b
  have va' := v' a
  have vb' := v' b
  generalize val (τ a) (𝟙 _) z J = ua at *
  generalize val (τ b) (𝟙 _) z J = ub at *
  generalize val (τ' a) (𝟙 _) z J = ua' at *
  generalize val (τ' b) (𝟙 _) z J = ub' at *
  have e : c (S'.th (lab a) * φ (S.th b)) * (ua' * ub).val = c (S'.th (lab b) * φ (S.th a)) * (ub' * ua).val := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, _root_.mul_mul_mul_comm, ← va', ← vb, _root_.mul_mul_mul_comm (c _), ← vb', ← va]
    ring
  have q' : (ua' * ub) ^ k = (ub' * ua) ^ k := by
    apply Additive.ofMul.injective
    replace q := congrArg Additive.ofMul q
    simp only [ofMul_mul, ofMul_pow, ofMul_div] at q ⊢
    linear_combination (norm := module) -q
  have e' := congrArg (· ^ k) e
  simp only [mul_pow, ← Units.val_pow_eq_pow_val, q'] at e'
  rw [map_pow, map_pow]
  exact (Units.mul_left_inj _).1 e'

end GlobalTheory.Poinc.DivDeep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFamilySurjectiveIffGeometricPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

namespace GlobalTheory.TorsCount

variable {κ Q : Type} [Fintype κ] [Group Q]

theorem map_zero_of_add {L : Type} [AddCommGroup L] (e : L → Q) (hadd : ∀ a c, e (a + c) = e a * e c) :
    e 0 = 1 := by
  have h := hadd 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem map_sub_of_add {L : Type} [AddCommGroup L] (e : L → Q) (hadd : ∀ a c, e (a + c) = e a * e c)
    (a c : L) : e (a - c) = e a * (e c)⁻¹ := by
  have h := hadd (a - c) c
  rw [sub_add_cancel] at h
  rw [h, mul_inv_cancel_right]

def red (M : ℕ) (e : (κ → ℤ) → Q) (hpow : ∀ a, e a ^ M = 1) : (κ → ZMod M) → {g : Q // g ^ M = 1} :=
  fun c => ⟨e fun i => ((c i).val : ℤ), hpow _⟩

theorem exists_red (M : ℕ) [NeZero M] (e : (κ → ℤ) → Q) (hadd : ∀ a c, e (a + c) = e a * e c)
    (hker : ∀ a, e a = 1 ↔ ∃ c, a = M • c) (a : κ → ℤ) :
    ∃ c : κ → ZMod M, e (fun i => ((c i).val : ℤ)) = e a := by
  refine ⟨fun i => (a i : ZMod M), ?_⟩
  have h : e (a - fun i => (((a i : ZMod M)).val : ℤ)) = 1 := by
    refine (hker _).2 ⟨fun i => a i / (M : ℤ), funext fun i => ?_⟩
    simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, ZMod.val_intCast]
    have := Int.emod_add_mul_ediv (a i) (M : ℤ)
    linarith
  rw [map_sub_of_add e hadd, mul_inv_eq_one] at h
  exact h.symm

theorem red_injective (M : ℕ) [NeZero M] (e : (κ → ℤ) → Q) (hadd : ∀ a c, e (a + c) = e a * e c)
    (hpow : ∀ a, e a ^ M = 1) (hker : ∀ a, e a = 1 ↔ ∃ c, a = M • c) : Function.Injective (red M e hpow) := by
  intro c c' hcc
  have h1 : e (fun i => ((c i).val : ℤ)) = e (fun i => ((c' i).val : ℤ)) := congrArg Subtype.val hcc
  have h2 : e ((fun i => ((c i).val : ℤ)) - fun i => ((c' i).val : ℤ)) = 1 := by
    rw [map_sub_of_add e hadd, h1, mul_inv_cancel]
  obtain ⟨d, hd⟩ := (hker _).1 h2
  funext i
  have h3 := congrArg (fun x : κ → ℤ => ((x i : ℤ) : ZMod M)) hd
  simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val,
    Int.cast_mul, ZMod.natCast_self, zero_mul] at h3
  exact sub_eq_zero.1 h3

theorem card_tors (M : ℕ) (hM : 0 < M) (e : (κ → ℤ) → Q) (hadd : ∀ a c, e (a + c) = e a * e c)
    (hpow : ∀ a, e a ^ M = 1) (hker : ∀ a, e a = 1 ↔ ∃ c, a = M • c)
    (hon : ∀ g : Q, g ^ M = 1 → ∃ a, e a = g) : Nat.card {g : Q // g ^ M = 1} = M ^ Fintype.card κ := by
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  have hb : Function.Bijective (red M e hpow) := by
    refine ⟨red_injective M e hadd hpow hker, fun ⟨g, hg⟩ => ?_⟩
    obtain ⟨a, rfl⟩ := hon g hg
    obtain ⟨c, hc⟩ := exists_red M e hadd hker a
    exact ⟨c, Subtype.ext hc⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]

end GlobalTheory.TorsCount

namespace GlobalTheory.HTSympCover

theorem onto_tors_iff : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ S) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk y ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → (∀ a, e a = 1 ↔ ∃ c, a = M • c) → ((∀ g : Over.mk y ⟶ o.A, g ^ M = 1 → ∃ a, e a = g) ↔ (M = 1 ∨ 2 * h = Module.finrank ℤ D.La)) := by
  intro p _ D R _ b N h M hM hcop S t o k _ _ y e hadd hpow hker
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨β, hβ⟩ := GlobalTheory.LevCover.exists_spMap (y ≫ t)
  obtain ⟨I, -⟩ := o.geom k y β hβ
  haveI := D.freeLa
  haveI := D.finLa
  let B := Module.Free.chooseBasis ℤ D.La
  let ev' : (Module.Free.ChooseBasisIndex ℤ D.La → ℤ) → (Over.mk y ⟶ o.A) := fun a => I.ev M (B.equivFun.symm a)
  have hadd' : ∀ a c, ev' (a + c) = ev' a * ev' c := fun a c => by
    simp only [ev', map_add]
    exact I.add M _ _
  have hpow' : ∀ a, ev' a ^ M = 1 := fun a => (I.onto M hM hcop _).2 ⟨_, rfl⟩
  have hker' : ∀ a, ev' a = 1 ↔ ∃ c, a = M • c := fun a => by
    simp only [ev']
    rw [I.ker M hM hcop]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨B.equivFun c, by rw [← map_nsmul, ← hc, LinearEquiv.apply_symm_apply]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨B.equivFun.symm c, map_nsmul _ _ _⟩
  have hon' : ∀ g, g ^ M = 1 → ∃ a, ev' a = g := fun g hg => by
    obtain ⟨x, hx⟩ := (I.onto M hM hcop g).1 hg
    exact ⟨B.equivFun x, by simp only [ev', LinearEquiv.symm_apply_apply, hx]⟩
  have hcard := GlobalTheory.TorsCount.card_tors M hM ev' hadd' hpow' hker' hon'
  rw [← Module.finrank_eq_card_chooseBasisIndex] at hcard
  have hinj := GlobalTheory.TorsCount.red_injective M e hadd hpow hker
  have hdom : Nat.card (Fin h ⊕ Fin h → ZMod M) = M ^ (2 * h) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_sum, Fintype.card_fin, two_mul]
  rcases Nat.lt_or_ge M 2 with hM2 | hM2
  · have h1 : M = 1 := by omega
    subst h1
    simp only [true_or, iff_true]
    intro g hg
    rw [pow_one] at hg
    exact ⟨0, by rw [hg]; exact GlobalTheory.TorsCount.map_zero_of_add e hadd⟩
  · have hMne : M ≠ 1 := by omega
    simp only [hMne, false_or]
    haveI : Finite {g : Over.mk y ⟶ o.A // g ^ M = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    constructor
    · intro hon
      have hb : Function.Bijective (GlobalTheory.TorsCount.red M e hpow) := by
        refine ⟨hinj, fun ⟨g, hg⟩ => ?_⟩
        obtain ⟨a, rfl⟩ := hon g hg
        obtain ⟨c, hc⟩ := GlobalTheory.TorsCount.exists_red M e hadd hker a
        exact ⟨c, Subtype.ext hc⟩
      have h2 := Nat.card_eq_of_bijective _ hb
      rw [hcard, hdom] at h2
      exact Nat.pow_right_injective hM2 h2
    · intro hr g hg
      have hs : Function.Surjective (GlobalTheory.TorsCount.red M e hpow) :=
        (hinj.bijective_of_nat_card_le (by rw [hcard, hdom, hr])).2
      obtain ⟨c, hc⟩ := hs ⟨g, hg⟩
      exact ⟨_, congrArg Subtype.val hc⟩

end GlobalTheory.HTSympCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFibrePointTransferFixedModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TorsionTransfer

theorem pow_left_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (g : T.left ⟶ S)
    (hg : T.hom ≫ f = g) (x : T ⟶ G') (x₀ : Over.mk g ⟶ G) (hx : x₀.left = x.left ≫ φ) (n : ℕ) :
    (x₀ ^ n).left = (x ^ n).left ≫ φ := by
  subst hg
  have e : x₀ = pushHom h T x := Over.OverMorphism.ext hx
  rw [e, ← map_pow]
  rfl

theorem torsion_transfer : ∀ (V₁ : Type) [CommRing V₁] (X : Over (Sp V₁)) [GrpObj X] (K : Type) [Field K] (ev : V₁ →+* K)
  (Z : Over (Sp K)) [GrpObj Z] (ψ : ((Over.pullback (spMap ev)).obj X).left ⟶ Z.left),
  IsGrpPullback ((Over.pullback (spMap ev)).obj X) Z (𝟙 _) ψ →
  ∀ (K₀ : Type) [Field K₀] (e : K₀ →+* K) (Y : Over (Sp K₀)) [GrpObj Y] (φ : Z.left ⟶ Y.left),
  IsGrpPullback Z Y (spMap e) φ →
  ∀ (n : ℕ) (y : Over.mk (spMap ev) ⟶ X), y ^ n = 1 →
  ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj X).left, q ≫ pullback.fst X.hom (spMap ev) = y.left →
    q ≫ pullback.snd X.hom (spMap ev) = 𝟙 _ →
    ∃ y' : Over.mk (spMap e) ⟶ Y, y' ^ n = 1 ∧ y'.left = q ≫ ψ ≫ φ := by
  intro V₁ _ X _ K _ ev Z _ ψ hψ K₀ _ e Y _ φ hφ n y hy q hq hs
  let P := (Over.pullback (spMap ev)).obj X
  let T0 : Over (Sp K) := Over.mk (𝟙 (Sp K))
  have hqP : q ≫ P.hom = T0.hom := hs
  let qq : T0 ⟶ P := Over.homMk q hqP
  have hP := isGrpPullback_pullback X (spMap ev)

  have h1 := pow_left_of_isGrpPullback hP T0 (spMap ev) (Category.id_comp _) qq y hq.symm n
  have h0 := pow_left_of_isGrpPullback hP T0 (spMap ev) (Category.id_comp _) qq y hq.symm 0
  rw [hy] at h1
  rw [pow_zero, pow_zero] at h0
  have hqn : (qq ^ n).left = (1 : T0 ⟶ P).left := by
    apply pullback.hom_ext
    · exact h1.symm.trans h0
    · exact (Over.w (qq ^ n)).trans (Over.w (1 : T0 ⟶ P)).symm

  have hzw : (q ≫ ψ) ≫ Z.hom = T0.hom := by
    have w := hψ.1.w
    rw [Category.assoc, w, Category.comp_id]; exact hs
  let zz : T0 ⟶ Z := Over.homMk (q ≫ ψ) hzw
  have k1 := pow_left_of_isGrpPullback hψ T0 (𝟙 _) (Category.comp_id _) qq zz rfl n
  have k0 := pow_left_of_isGrpPullback hψ T0 (𝟙 _) (Category.comp_id _) qq zz rfl 0
  rw [pow_zero, pow_zero] at k0
  have hzn : (zz ^ n).left = (1 : T0 ⟶ Z).left := by
    rw [k1, hqn]; exact k0.symm

  have hyw : (q ≫ ψ ≫ φ) ≫ Y.hom = spMap e := by
    have w := hφ.1.w
    rw [Category.assoc, Category.assoc, w, ← Category.assoc ψ, ← Category.assoc q, ← Category.assoc q, hzw]
    exact Category.id_comp _
  refine ⟨Over.homMk (q ≫ ψ ≫ φ) hyw, ?_, rfl⟩
  have m1 := pow_left_of_isGrpPullback hφ T0 (spMap e) (Category.id_comp _) zz (Over.homMk (q ≫ ψ ≫ φ) hyw)
    (by simp [zz]) n
  have m0 := pow_left_of_isGrpPullback hφ T0 (spMap e) (Category.id_comp _) zz (Over.homMk (q ≫ ψ ≫ φ) hyw)
    (by simp [zz]) 0
  rw [pow_zero, pow_zero] at m0
  apply Over.OverMorphism.ext
  rw [m1, hzn, m0]

end GlobalTheory.TorsionTransfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointAlgebraicModel
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem torsion_of_complex_is_algebraic : ∀ (A₀ : Over (Sp Qb)) [GrpObj A₀] (A : Over (Sp ℂ)) [GrpObj A] (p : A.left ⟶ A₀.left) (g n : ℕ),
    IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p →
    1 ≤ n → ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ^ n = 1 →
    ∃ c : 𝟙_ (Over (Sp Qb)) ⟶ A₀, x.left ≫ p = spMap (algebraMap Qb ℂ) ≫ c.left := by
  intro A₀ _ A _ p g n hA₀ hg hp hn x hx
  set t : Sp ℂ ⟶ Sp Qb := spMap (algebraMap Qb ℂ) with ht
  have hM := GlobalTheory.abMulN_holds
  have : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  have hSub : Subsingleton (Sp Qb) := inferInstanceAs (Subsingleton (PrimeSpectrum Qb))
  have : Flat t := inferInstance
  have : Surjective t := ⟨fun _ => ⟨(default : PrimeSpectrum ℂ), Subsingleton.elim _ _⟩⟩
  have : Epi t := Flat.epi_of_flat_of_surjective _
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA₀ hp
  have hdim : SmoothOfRelativeDimension g A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hp.1 hg
  obtain ⟨e, he⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hp (𝟙 (Sp ℂ)) t (Category.id_comp t).symm
  have hnQ : ((n : ℕ) : Qb) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hnC : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h₁ := hM Qb A₀ g n hA₀ hg hnQ
  have h₂ := hM ℂ A g n hA hdim hnC
  have hl : (toUnit (Over.mk t)).left = t := by simpa using Over.w (toUnit (Over.mk t))
  let r : {c : 𝟙_ (Over (Sp Qb)) ⟶ A₀ // c ^ n = 1} → {y : 𝟙_ (Over (Sp ℂ)) ⟶ A // y ^ n = 1} := fun c =>
    ⟨e.symm (toUnit (Over.mk t) ≫ c.1), by
      change e.symm _ ^ n = 1
      rw [← map_pow, ← MonObj.comp_pow, c.2, MonObj.comp_one, map_one]⟩
  have hr : Function.Injective r := fun a b h => Subtype.ext (Over.OverMorphism.ext ((cancel_epi t).1 (by
    have h' := congrArg (fun q => (e q.1).left) h
    simpa only [r, MulEquiv.apply_symm_apply, Over.comp_left, hl] using h')))
  have : Finite {y : 𝟙_ (Over (Sp ℂ)) ⟶ A // y ^ n = 1} := GlobalTheory.Published.AbMulNSt.finite hM hA hdim hnC
  obtain ⟨c, hc⟩ := ((Nat.bijective_iff_injective_and_card r).2 ⟨hr, h₁.trans h₂.symm⟩).2 ⟨x, hx⟩
  refine ⟨c.1, ?_⟩
  have h3 : e x = toUnit (Over.mk t) ≫ c.1 := by
    have hx' : e.symm (toUnit (Over.mk t) ≫ c.1) = x := congrArg Subtype.val hc
    rw [← hx', MulEquiv.apply_symm_apply]
  rw [← he x, h3, Over.comp_left, hl]

end GlobalTheory.RealMult
end

