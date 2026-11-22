import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3543
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3541
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3429
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3169
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3185
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3324
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3538
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3448
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2718
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3475
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3539
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3526
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3540
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectionMatrixInvariantBasis
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatInvLift

theorem rsT_of_le' {Z : Scheme.{0}} {O₀ O : Z.Opens} (h : O ≤ O₀) (s : Γ(Z, O₀)) : rsT s O = resG Z h s := dif_pos h

theorem rsT_rsT' {Z : Scheme.{0}} {O₀ O₁ O₂ : Z.Opens} (h₁ : O₁ ≤ O₀) (h₂ : O₂ ≤ O₁) (s : Γ(Z, O₀)) :
    rsT (rsT s O₁) O₂ = rsT s O₂ := by
  rw [rsT_of_le' h₁, rsT_of_le' h₂, rsT_of_le' (h₂.trans h₁), ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem rsT_pbT' {Z X : Scheme.{0}} (m : Z ⟶ X) {O₀ : X.Opens} {O₁ O₂ : Z.Opens} (h₁ : O₁ ≤ m ⁻¹ᵁ O₀) (h₂ : O₂ ≤ O₁)
    (s : Γ(X, O₀)) : rsT (pbT m s O₁) O₂ = pbT m s O₂ := by
  rw [rsT_of_le' h₂]
  unfold pbT
  rw [dif_pos h₁, dif_pos (h₂.trans h₁), ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem rsT_constFn' {R : Type} [CommRing R] {Z : Scheme.{0}} (p : Z ⟶ Sp R) {O₀ O : Z.Opens} (h : O ≤ O₀) (a : R) :
    rsT (constFn p O₀ a) O = constFn p O a := by
  rw [rsT_of_le' h]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := O₀) (fun _ _ => trivial) (homOfLE h).op)

theorem rsT_field {Z : Scheme.{0}} {δ : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)} (hδ : IsField ⊤ δ) {O₀ O : Z.Opens}
    (h : O ≤ O₀) (s : Γ(Z, O₀)) : rsT (δ O₀ s) O = δ O (rsT s O) := by
  rw [rsT_of_le' h, rsT_of_le' h, hδ.2.2 O₀ O h le_top s]

theorem rsT_add' {Z : Scheme.{0}} {O₀ : Z.Opens} (s t : Γ(Z, O₀)) (O : Z.Opens) : rsT (s + t) O = rsT s O + rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_sub' {Z : Scheme.{0}} {O₀ : Z.Opens} (s t : Γ(Z, O₀)) (O : Z.Opens) : rsT (s - t) O = rsT s O - rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_mul' {Z : Scheme.{0}} {O₀ : Z.Opens} (s t : Γ(Z, O₀)) (O : Z.Opens) : rsT (s * t) O = rsT s O * rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_sum' {Z : Scheme.{0}} {O₀ : Z.Opens} {K : Type} (S : Finset K) (s : K → Γ(Z, O₀)) (O : Z.Opens) :
    rsT (∑ b ∈ S, s b) O = ∑ b ∈ S, rsT (s b) O := by
  unfold rsT; split_ifs <;> simp

end GlobalTheory.HeatInvLift

open GlobalTheory.HeatInvLift

namespace GlobalTheory.HeatInvLift

theorem exists_invLift_symmKS : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ D : Derivation ℤ R R,
  ∃ (Θ : Matrix (Fin n) (Fin n) R) (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left),
    Θᵀ = Θ ∧ ⨆ i, V i = ⊤ ∧ (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) ∧ (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) ∧
    (∀ i (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f,
      IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f)) ∧
    ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f =
      ∑ a, ∑ b, constFn Y.H.hom W (Θ a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd D
  obtain ⟨J, V, j, d₀, hc, hle, hl₀, hw₀⟩ := GlobalTheory.T.exists_torusInvariant_derivationLifts_raynaudCover R Dd O oa Y D
  obtain ⟨z, hzc, hzw, hz⟩ := GlobalTheory.T.difference_invariantLifts_isWeightZeroCechCocycle R Dd O oa Y n v dd hdd D J V d₀ hl₀ hw₀
  have H := fun a => GlobalTheory.T.exists_weightZeroCocycle_eq_logDerivative_comb_add_coboundary R Dd O oa Y n v dd hdd J V j hc hle (z a) (hzc a) (hzw a)
  choose c y hyw hy using H
  have hA := fun i => GlobalTheory.T.torusInvariantLift_add_invariantCombination R Dd O oa Y n v dd hdd D (V i) (d₀ i) (fun a => y a i) (hl₀ i) (hw₀ i) (fun a => hyw a i)
  have hrel : ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f,
      (d₀ i W f + ∑ a, rsT (y a i) W * dd a W f) - (d₀ i' W f + ∑ a, rsT (y a i') W * dd a W f) =
        ∑ a, ∑ b, constFn Y.H.hom W (Matrix.of c a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f := by
    intro i i' W hW f
    rw [add_sub_add_comm, hz i i' W hW f]
    have hU : Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ≤
        Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i')) :=
      fun x hx => ⟨hle i hx.1, hle i' hx.2⟩
    have key : ∀ a, rsT (z a i i') W = ∑ b, constFn Y.H.hom W (c a b) *
        dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W + (rsT (y a i') W - rsT (y a i) W) := by
      intro a
      rw [hy a i i', rsT_add', rsT_sub', rsT_rsT' inf_le_right hW, rsT_rsT' inf_le_left hW]
      congr 1
      rw [rsT_sum']
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [rsT_mul', rsT_constFn' _ hW]
      congr 1
      unfold dlg
      rw [rsT_mul', rsT_field (hdd b).1 hW, rsT_pbT' _ hU hW, rsT_pbT' _ hU hW]
    simp only [key, Matrix.of_apply, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul]
    ring
  obtain ⟨Θ, hs, hΘ⟩ := GlobalTheory.T.exists_symmetric_kodairaSpencer_invariantLifts R Dd O oa Y n v dd hdd D J V j
    (fun i W f => d₀ i W f + ∑ a, rsT (y a i) W * dd a W f) hc hle (fun i => (hA i).1) (fun i => (hA i).2)
    (Matrix.of c) hrel
  exact ⟨Θ, J, V, j, _, hs, hc, hle, fun i => (hA i).1, fun i => (hA i).2, hΘ⟩

end GlobalTheory.HeatInvLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNsmulEndomorphismPreservesCompletio
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.DenEnd

variable {p : ℕ} [Fact p.Prime]

theorem inAf_mem (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, fun v => by rw [map_one]; exact one_mem _, rfl⟩

theorem smul_mem (D : Datum p) {a : AfP p} (ha : IsIntAf a) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) :
    a • v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, x, hc, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * c, x, fun w => ?_, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hc w)
    · rw [TensorProduct.smul_tmul', smul_eq_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem exists_nsmul_mem (D : Datum p) (v : AfP p ⊗[ℚ] VQ D) : ∃ d : ℕ, 0 < d ∧ d • v ∈ LaHat D := by
  have hadd : ∀ u w : AfP p ⊗[ℚ] VQ D, (∃ d : ℕ, 0 < d ∧ d • u ∈ LaHat D) → (∃ d : ℕ, 0 < d ∧ d • w ∈ LaHat D) →
      ∃ d : ℕ, 0 < d ∧ d • (u + w) ∈ LaHat D := by
    rintro u w ⟨d, hd, hu⟩ ⟨e, he, hw⟩
    refine ⟨d * e, Nat.mul_pos hd he, ?_⟩
    have : (d * e) • (u + w) = e • (d • u) + d • (e • w) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm e d]
    rw [this]
    exact add_mem (nsmul_mem hu _) (nsmul_mem hw _)
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩
  | add u w hu hw => exact hadd u w hu hw
  | tmul a w =>
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨1, one_pos, by rw [TensorProduct.tmul_zero, smul_zero]; exact zero_mem _⟩
    | add u w hu hw => rw [TensorProduct.tmul_add]; exact hadd _ _ hu hw
    | tmul q x =>
      obtain ⟨d, hd, h⟩ := GlobalTheory.DenAway.exists_nat_adele (q • a)
      refine ⟨d, hd, AddSubgroup.subset_closure ⟨(d : AfP p) * (q • a), x, h, ?_⟩⟩
      have e : q ⊗ₜ[ℤ] x = q • ((1 : ℚ) ⊗ₜ[ℤ] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [e, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', nsmul_eq_mul]

theorem isIntAf_inv : IsIntAf (algebraMap ℚ (AfP p) (p : ℚ)⁻¹) := by
  intro v
  rw [AlgHom.commutes, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.1.valuation ℚ (algebraMap ℤ ℚ (p : ℤ)) = 1 := by
    refine le_antisymm (v.1.valuation_le_one _) (not_lt.1 fun h => v.2 ?_)
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem] at h
    have hm : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp Fact.out).irreducible
    exact (hm.eq_of_le v.1.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h)).symm
  have h2 : Valued.v (algebraMap ℚ (v.1.adicCompletion ℚ) (p : ℚ)⁻¹) = v.1.valuation ℚ (p : ℚ)⁻¹ :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 _
  rw [h2, map_inv₀]
  simp only [eq_intCast, Int.cast_natCast] at h1
  rw [h1, inv_one]

theorem exists_coprime_nsmul_mem (D : Datum p) (v : AfP p ⊗[ℚ] VQ D) :
    ∃ t : ℕ, 0 < t ∧ t.Coprime p ∧ t • v ∈ LaHat D := by
  obtain ⟨d, hd, h⟩ := exists_nsmul_mem D v
  obtain ⟨k, t, ht, hdt⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' p (Fact.out : p.Prime).ne_one
  have ht0 : 0 < t := Nat.pos_of_ne_zero fun h => ht (h ▸ dvd_zero p)
  refine ⟨t, ht0, ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 ht).symm, ?_⟩
  have hint : IsIntAf (algebraMap ℚ (AfP p) (p : ℚ)⁻¹ ^ k) := fun u => by
    rw [map_pow]; exact pow_mem (isIntAf_inv u) k
  have hm := smul_mem D hint h
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  convert hm using 1
  rw [hdt, ← map_pow, algebraMap_smul, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  push_cast
  rw [inv_pow, ← _root_.mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp), _root_.one_mul]

theorem exists_coprime_nsmul_map_mem : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p)
    (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), ∃ j : ℕ, 0 < j ∧ j.Coprime p ∧ ∀ v ∈ LaHat D, j • A v ∈ LaHat D := by
  intro p _ D A
  have := D.freeLa
  have := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  choose t ht0 htc ht using fun i => exists_coprime_nsmul_mem D (A (inAf D (b i)))
  refine ⟨∏ i, t i, Finset.prod_pos fun i _ => ht0 i, Nat.Coprime.prod_left fun i _ => htc i, ?_⟩
  have hbase : ∀ x : D.La, (∏ i, t i) • A (inAf D x) ∈ LaHat D := by
    intro x
    have hx : x ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem t (Finset.mem_univ i)
      rw [hk, mul_comm, mul_smul]
      exact nsmul_mem (ht i) k
    | zero =>
      have : inAf D 0 = 0 := by simp [inAf]
      rw [this, map_zero, smul_zero]; exact zero_mem _
    | add y z _ _ hy hz =>
      have : inAf D (y + z) = inAf D y + inAf D z := by simp only [inAf, TensorProduct.tmul_add]
      rw [this, map_add, smul_add]; exact add_mem hy hz
    | smul c y _ hy =>
      have : inAf D (c • y) = c • inAf D y := by
        simp only [inAf, TensorProduct.tmul_smul]
      rw [this, map_zsmul, smul_comm]; exact zsmul_mem hy c
  intro v hv
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    have e : a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) = a • inAf D x := by
      rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [e, map_smul, smul_comm]
    exact smul_mem D ha (hbase x)
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, smul_neg]; exact neg_mem hx

end GlobalTheory.LKGeo.DenEnd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeeperPointIntegralClosureStalkStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deeperPoint_integralClosure_stalk : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra; ∃ (z₂ : 𝔗.X₂.M.Z) (j₂ : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ →+* 𝔗.X₂.M.Z.presheaf.stalk z₂), 𝔗.p z₂ = z₁ ∧ (∀ b, 𝔗.X₂.M.stalkHom z₂ (j₂ b) = b) ∧ ((maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap j₂).IsMaximal ∧ (∀ x : 𝔗.X₂.Ω₁, (∀ w, 𝔗.p w = z₁ → x ∈ 𝔗.X₂.M.O w) → x ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁) ∧ (∀ σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁, (∀ b b' : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁, (b' : 𝔗.X₂.Ω₁) = σ b → (j₂ b ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂) ↔ j₂ b' ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂))) → ∃ σ₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ ≃+* 𝔗.X₂.M.Z.presheaf.stalk z₂, ∀ x, 𝔗.X₂.M.stalkHom z₂ (σ₂ x) = σ (𝔗.X₂.M.stalkHom z₂ x)) ∧ ∀ (V : Type) [CommRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (V' : Type) [CommRing V'] (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), Function.Injective ev → Function.Injective io → 𝔗.Ext ev io ev₂ → Function.Injective ev₂ := by
  first | exact @GlobalTheory.GSep.Tower.exists_point_integralClosure_stalk | exact GlobalTheory.GSep.Tower.exists_point_integralClosure_stalk | (intros; apply GlobalTheory.GSep.Tower.exists_point_integralClosure_stalk <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorMulIntegralUnitFiniteAdelesAwayP
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.AfUnitSplit

theorem isInt_add' {p : ℕ} {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a + b) := fun v => by
  rw [map_add]; exact add_mem (ha v) (hb v)

theorem isInt_sub' {p : ℕ} {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a - b) := fun v => by
  rw [map_sub]; exact sub_mem (ha v) (hb v)

theorem isInt_mul' {p : ℕ} {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a * b) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

theorem isInt_intCast' {p : ℕ} (k : ℤ) : IsIntAf (k : AfP p) := fun v => by
  rw [map_intCast]; exact intCast_mem _ k

theorem exists_dvd_mul_unit : ∀ (p : ℕ) [Fact p.Prime] (a b : AfP p) (K : ℕ), 0 < K → K.Coprime p → IsIntAf a →
    IsIntAf b → a * b = (K : AfP p) → ∃ (c : ℕ) (ε ε' : AfP p), c.Coprime p ∧ c ∣ K ∧ IsIntAf ε ∧ IsIntAf ε' ∧
      ε * ε' = 1 ∧ a = (c : AfP p) * ε := by
  intro p _ a b K hK hKp ha hb hab
  obtain ⟨m₀, β, hβ, e⟩ := LaHatMod.exists_int_add_mul K hK hKp a ha
  have hgpos : 0 < Int.gcd m₀ (K : ℤ) := Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast hK.ne')
  obtain ⟨g, a₀, K₀, hg, hcop, hm, hKe⟩ := Int.exists_gcd_one' hgpos
  have hgK : g ∣ K := by
    have : (g : ℤ) ∣ (K : ℤ) := ⟨K₀, by rw [hKe]; ring⟩
    exact_mod_cast this
  have hgp : g.Coprime p := Nat.Coprime.coprime_dvd_left hgK hKp
  have hbez : (1 : ℤ) = a₀ * Int.gcdA a₀ K₀ + K₀ * Int.gcdB a₀ K₀ := by
    rw [← Int.gcd_eq_gcd_ab, hcop]; rfl
  set s := Int.gcdA a₀ K₀
  set t := Int.gcdB a₀ K₀
  have hbez' : (1 : AfP p) = (a₀ : AfP p) * s + (K₀ : AfP p) * t := by
    have := congrArg (Int.cast : ℤ → AfP p) hbez; push_cast at this; exact this
  have hKc : (K : AfP p) = (K₀ : AfP p) * (g : AfP p) := by
    have := congrArg (Int.cast : ℤ → AfP p) hKe; push_cast at this; exact this
  have hmc : (m₀ : AfP p) = (a₀ : AfP p) * (g : AfP p) := by
    have := congrArg (Int.cast : ℤ → AfP p) hm; push_cast at this; exact this
  have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  set u := algebraMap ℚ (AfP p) (g : ℚ)⁻¹
  have hu : (g : AfP p) * u = 1 := by
    rw [← map_natCast (algebraMap ℚ (AfP p)), ← map_mul, mul_inv_cancel₀ hgq, map_one]
  have ha' : a = (g : AfP p) * ((a₀ : AfP p) + (K₀ : AfP p) * β) := by
    rw [e, hmc, hKc]; ring
  have hεb : ((a₀ : AfP p) + (K₀ : AfP p) * β) * b = (K₀ : AfP p) := by
    linear_combination (-(((a₀ : AfP p) + (K₀ : AfP p) * β) * b - (K₀ : AfP p))) * hu + u * hab
      - u * b * ha' + u * hKc
  refine ⟨g, (a₀ : AfP p) + (K₀ : AfP p) * β, (s : AfP p) - b * ((s : AfP p) * β - t), hgp, hgK,
    isInt_add' (isInt_intCast' _) (isInt_mul' (isInt_intCast' _) hβ),
    isInt_sub' (isInt_intCast' _) (isInt_mul' hb (isInt_sub' (isInt_mul' (isInt_intCast' _) hβ) (isInt_intCast' _))),
    ?_, ha'⟩
  linear_combination (-((s : AfP p) * β - t)) * hεb - hbez'

end GlobalTheory.AfUnitSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierGluingLocalTuplesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_effectiveCartier_gluing_localTuples : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (ι : ℕ) (K : Type) [Fintype K] (Jk : K → Type) [∀ k, Fintype (Jk k)] (t : ∀ k, Jk k → X₁.Ω₁), (∀ k j, t k j ≠ 0) → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE), X₁.S.admitted Y U₀ → (∀ k, Nonempty (Jk k) → Y.HasDiv (t k)) → (∀ x : Y.Z, ∃ k, ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ (∀ j, UOrdGe Y T ξ (t k j) a) ∧ ∃ j, UOrdEq Y T ξ (t k j) a) → ∃ D : GlobalTheory.EffCartierData Y.Z, (∀ y ∈ D.idealSheaf.support, y ∉ U₀) ∧ ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a} := by
  first | exact @GlobalTheory.UPoinc.UGlue.exists_effCartier_of_locTuples | exact GlobalTheory.UPoinc.UGlue.exists_effCartier_of_locTuples | (intros; apply GlobalTheory.UPoinc.UGlue.exists_effCartier_of_locTuples <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCoverLinkedThetaSystems
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
open GlobalTheory.UCovSep

namespace GlobalTheory.UCovSep

set_option maxHeartbeats 1000000 in

theorem exists_linked_cov : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (Y : Scheme.{0}) (q : Y ⟶ Xo.XF c), j₀ ≤ j ∧ IsFinite q ∧ Surjective q ∧ ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z) (yM : Sp K ⟶ X₁.M.Z), GlobalTheory.GSep.ULink C X₁ act u π ∧ X₁.S.r * X₁.S.N = (n ^ j) ^ 2 ∧ (∃ (U : C.Z.Opens) (g' : X₁.M.Z ⟶ U.toScheme), IsFinite g' ∧ g' ≫ U.ι = π ∧ Set.range (pullback.fst C.z (spMap C.b)) ⊆ (U : Set C.Z)) ∧ yM ≫ π = y' ≫ q ≫ C.i ∧ ∀ a ∈ X₁.S.R, a ∈ X₁.M.O (yM (closedPoint K)) := by
  intro E _ _ _ H Dw hpq l Xo c C n hn ho j₀
  classical
  haveI : Finite (genericPoints (Xo.XF c)) := (GlobalTheory.T.genericPoints_finite_unitaryModuli_coefficientField E H Dw l Xo c).to_subtype
  letI : Fintype (genericPoints (Xo.XF c)) := Fintype.ofFinite _
  choose g₀ hA using fun τ : genericPoints (Xo.XF c) => GlobalTheory.T.exists_levelStructure_normalModel_unitaryModuliPoint E H Dw hpq l Xo c C τ.1 n hn ho
  choose k j₁ hk _hB hj₁ big using fun τ : genericPoints (Xo.XF c) =>
    GlobalTheory.UPoinc.GSetup.exists_big_level (g₀ τ) n hn.two_le 0
  set J := j₀ + ∑ τ, (k τ + j₁ τ) + 1 with hJ
  have hkJ : ∀ τ, k τ + j₁ τ + j₀ + 1 ≤ J := fun τ => by
    have := Finset.single_le_sum (f := fun τ => k τ + j₁ τ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ)
    omega
  choose o₁ Ω i₁ i₂ i₃ i₄ ze uτ A₁ lev M U g hAg hun hx hUO hpt hMn hMp hgf hrange using fun τ => hA τ (4 * J)
  obtain ⟨Y, q, hqf, hqs, hY⟩ := GlobalTheory.T.exists_finite_surjective_cover_from_opens (Xo.XF c) C.Z C.i (genericPoints (Xo.XF c)) (fun τ => (M τ).Z) U g hgf
    (fun τ => by
      rintro _ ⟨x, rfl⟩
      exact hrange τ ⟨C.iF x, rfl⟩)
    (fun x => by
      obtain ⟨τ, hτ, hsp⟩ := GlobalTheory.exists_mem_genericPoints_specializes x
      refine ⟨⟨τ, hτ⟩, (M ⟨τ, hτ⟩).pt (closedPoint (Ω ⟨τ, hτ⟩)), ?_⟩
      have h₁ : (g ⟨τ, hτ⟩ ≫ (U ⟨τ, hτ⟩).ι) ((M ⟨τ, hτ⟩).pt (closedPoint (Ω ⟨τ, hτ⟩))) = C.i τ := by
        refine (congrArg (fun χ : Sp (Ω ⟨τ, hτ⟩) ⟶ C.Z => χ (closedPoint (Ω ⟨τ, hτ⟩))) (hpt ⟨τ, hτ⟩)).trans ?_
        exact congrArg C.i (hx ⟨τ, hτ⟩ (closedPoint (Ω ⟨τ, hτ⟩)))
      rw [h₁]
      exact hsp.map C.i.continuous)
  refine ⟨J, Y, q, by omega, hqf, hqs, fun K _ y' => ?_⟩
  obtain ⟨t, yM, hyM⟩ := hY K y'
  letI := i₁ t
  letI := i₂ t
  letI := i₃ t
  haveI := i₄ t
  obtain ⟨R, P, act, u, 𝔭, hRfg, hfr, hPg, hS, ⟨levR⟩, hact, hUA, hu, h𝔭, hreg𝔭⟩ :=
    GlobalTheory.T.exists_local_spread_universal_abelian_scheme E H Dw hpq l Xo c C (o₁ t) (Ω t) (M t) (g t ≫ (U t).ι) (uτ t) (hMn t) (hpt t)
      (A₁ t) (n ^ (4 * J)) (ze t) (by rw [Nat.cast_pow]; exact (hun t).pow _) (hUO t) (lev t) K yM (y' ≫ q)
      (by rw [Category.assoc]; simpa only [Category.assoc] using hyM)
  have e : (n ^ (2 * J - 2 * k t) * (n ^ k t) ^ 2) ^ 2 = n ^ (4 * J) := by
    rw [← pow_mul, ← pow_add, ← pow_mul]
    congr 1
    have := hkJ t
    omega
  obtain ⟨S, ρ, hR, φ, hreg, -, hN, hr, hgS, hpb, hL, -⟩ := GlobalTheory.T.exists_thetaSystem_realisation_regular_at_prime (o₁ t) (Ω t) R hRfg hfr 𝔭 h𝔭 P n (k t)
    (2 * J - 2 * k t) (ze t) hn ho (hk t) (by have := hkJ t; omega) (hun t) hS (e ▸ levR)
  obtain ⟨act', hact', -, hUA'⟩ := GlobalTheory.T.unitaryAction_baseChange_subalgebra E H Dw l Xo c (o₁ t) (Ω t) R S.R hR P ρ.P φ hpb hL act u hact hUA
  have hu' : spMap (ratHull S.R).val.toRingHom ≫ spMap (Subalgebra.inclusion (ratHull_mono hR)).toRingHom ≫ u = uτ t := by
    rw [← hu, ← Category.assoc, ← Spec.map_comp]; rfl
  have hgen : ∀ w, (spMap (ratHull S.R).val.toRingHom ≫ spMap (Subalgebra.inclusion (ratHull_mono hR)).toRingHom ≫ u) w ∈
      genericPoints (Xo.XF c) := fun w => by rw [hu', hx t w]; exact t.2
  have hptS : (M t).pt ≫ (g t ≫ (U t).ι) =
      spMap (ratHull S.R).val.toRingHom ≫ (spMap (Subalgebra.inclusion (ratHull_mono hR)).toRingHom ≫ u) ≫ C.i := by
    rw [hpt t, ← hu', Category.assoc]
  have hbig : S.Big := big t _ (by have := hkJ t; omega) (o₁ t) (Ω t) S (hgS.trans (hPg.trans (hAg t))) hN hr
  let X₁ : GlobalTheory.GSep.GSet :=
    { o₁ := o₁ t, Ω₁ := Ω t, S := S, ρ := ρ, big := hbig, M := M t, normal := hMn t, projM := hMp t,
      div := C.thetaInt (o₁ t) (Ω t) S ρ _ hUA'.uOver hgen (M t) (g t ≫ (U t).ι)
        (hMn t) hptS }
  refine ⟨X₁, act', spMap (Subalgebra.inclusion (ratHull_mono hR)).toRingHom ≫ u, g t ≫ (U t).ι, yM,
    ⟨hact', hUA', hgen, hptS⟩, ?_, ⟨U t, g t, hgf t, rfl, hrange t⟩, by simpa only [Category.assoc] using hyM, ?_⟩
  · show S.r * S.N = _
    rw [hr, hN, ← pow_mul, ← pow_add, ← pow_mul]
    congr 1
    have := hkJ t
    omega
  · intro a ha
    obtain ⟨a', b', hb', rfl⟩ := hreg a ha
    exact hreg𝔭 a' b' hb'

end GlobalTheory.UCovSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtSqrtUniformiserCompleteDvrStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_ext_sqrt_uniformiser_complete_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsPrincipalIdealRing V → ∀ ϖ : V, Irreducible ϖ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (t : V'), IsCN V' ∧ IsPrincipalIdealRing V' ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧ t ^ 2 = f ϖ := by
  first | exact @GlobalTheory.USep.exists_finite_ext_sq_eq_uniformiser | exact GlobalTheory.USep.exists_finite_ext_sq_eq_uniformiser | (intros; apply GlobalTheory.USep.exists_finite_ext_sq_eq_uniformiser <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGeneratorTranslationBundleMonomialStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralGenerator_translationBundle_monomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → ∀ (y : P.D.toPre.X) (N : ℕ), 1 ≤ N → ∃ (Nv : Fin m → ℕ) (uR : LB.Gen (LB.LinComb P.D.toPre.P.L (Sum.elim (P.D.toPre.famφB (0 + N • y)) (fun i => (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ≫ P.D.toPre.famφB 0 i)) (DegPre.deltaε N))), uR.IsGen ∧ ∀ (u : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.deltaφ P.D.toPre (FractionRing (ChartRing k m d)) N 0 y) (DegPre.deltaε N))), u.IsGen → LB.Gen.Corr P.D.toPre.P.L _ _ _ _ (LB.pullGen P.D.toPre.P.L _ _ u (DegPre.zF P.D.toPre (FractionRing (ChartRing k m d))).left) (DegPre.famMult P.D.toPre (FractionRing (ChartRing k m d)) N y 0) → ∀ (z : (DegPre.BF P.D.toPre (FractionRing (ChartRing k m d))).left) (J : ((DegPre.BF P.D.toPre (FractionRing (ChartRing k m d))).left ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι), Good P.D.toPre.P.L z J → (val u (𝟙 _) z J).val = gs ((DegPre.prB P.D.toPre (FractionRing (ChartRing k m d))).left ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ Nv i)) * (val uR (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d))).left z J).val := by
  first | exact @GlobalTheory.ShiftGen.exists_integral_gen_monomial | exact GlobalTheory.ShiftGen.exists_integral_gen_monomial | (intros; apply GlobalTheory.ShiftGen.exists_integral_gen_monomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralHodgeBundleGeneratorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_hodgeBundle_generator : ∀ (S' : Scheme.{0}) (g : ℕ) (G : Over S') [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (y : Sp (FractionRing R) ⟶ S') (α : pullback G₁.hom (jK R) ⟶ G.left), IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α → ∃ e₀ : LB.Gen ((hodge G g).pull y), e₀.IsGen ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) → ∀ χ' : Sp W ⟶ S', spMap gam ≫ y = jK W ≫ χ' → ∃ e₀' : LB.Gen ((hodge G g).pull χ'), e₀'.IsGen ∧ ∀ (z : Sp (FractionRing W)) (J : (Sp (FractionRing W) ⟶ S') → (hodge G g).ι), Good (hodge G g) z J → val (L := hodge G g) (φ := fun _ : PUnit => y) (ε := fun _ => 1) e₀ (spMap gam) z J = val (L := hodge G g) (φ := fun _ : PUnit => χ') (ε := fun _ => 1) e₀' (jK W) z J := by
  first | exact @GlobalTheory.HodgeFrameGen.exists_integral_hodgeGen | exact GlobalTheory.HodgeFrameGen.exists_integral_hodgeGen | (intros; apply GlobalTheory.HodgeFrameGen.exists_integral_hodgeGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelTorsionPointOfComesFromBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelTorsionPoint_of_comesFromBase : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ y : P.D.toPre.X, ∃ p₀ : QkPt P.D.toPre (FractionRing R) l.M', p₀.y = y := by
  first | exact @GlobalTheory.DivSol.exists_qkPt_of_divFrom | exact GlobalTheory.DivSol.exists_qkPt_of_divFrom | (intros; apply GlobalTheory.DivSol.exists_qkPt_of_divFrom <;> assumption)
end

