import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniqueIsConnOfLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1640
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerLinEMulE
section
set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.CrysConn

namespace GlobalTheory.PDA

variable {B : Type} [CommRing B]

def PDPoly.derVal (Q : PDPoly B) : ℕ → Q.P
  | 0 => 0
  | n + 1 => Q.e n

def PDPoly.derLin (Q : PDPoly B) : Q.P →ₗ[B] Q.P := Q.e.constr B Q.derVal

theorem PDPoly.derLin_e (Q : PDPoly B) (n : ℕ) : Q.derLin (Q.e n) = Q.derVal n := by
  simp [PDPoly.derLin, Module.Basis.constr_basis]

theorem PDPoly.derLin_e_succ (Q : PDPoly B) (n : ℕ) : Q.derLin (Q.e (n + 1)) = Q.e n := Q.derLin_e (n + 1)

theorem PDPoly.derLin_e_zero (Q : PDPoly B) : Q.derLin (Q.e 0) = 0 := Q.derLin_e 0

theorem PDPoly.derLin_e_mul_e (Q : PDPoly B) (m n : ℕ) :
    Q.derLin (Q.e m * Q.e n) = Q.e m * Q.derLin (Q.e n) + Q.e n * Q.derLin (Q.e m) := by
  rcases m with _ | a
  · rw [Q.derLin_e_zero, Q.e_zero]; simp
  rcases n with _ | b
  · rw [Q.derLin_e_zero, Q.e_zero]; simp
  rw [Q.derLin_e_succ, Q.derLin_e_succ, Q.e_mul, Q.e_mul, Q.e_mul, ← nsmul_eq_mul, map_nsmul,
    show a + 1 + (b + 1) = (a + b + 1) + 1 by omega, Q.derLin_e_succ, show a + 1 + b = a + b + 1 by omega,
    show b + 1 + a = a + b + 1 by omega, Nat.choose_succ_succ' (a + b + 1) a,
    Nat.choose_symm_of_eq_add (show a + b + 1 = (b + 1) + a by omega)]
  push_cast
  rw [nsmul_eq_mul]
  push_cast
  ring

theorem PDPoly.derLin_mul (Q : PDPoly B) (x y : Q.P) :
    Q.derLin (x * y) = x * Q.derLin y + y * Q.derLin x := by
  have h2 : ∀ x n, Q.derLin (x * Q.e n) = x * Q.derLin (Q.e n) + Q.e n * Q.derLin x := fun x n ↦ by
    have := Q.e.ext (f₁ := Q.derLin ∘ₗ LinearMap.mulRight B (Q.e n))
      (f₂ := LinearMap.mulRight B (Q.derLin (Q.e n)) + LinearMap.mulLeft B (Q.e n) ∘ₗ Q.derLin)
      (fun m ↦ by simpa using Q.derLin_e_mul_e m n)
    simpa using LinearMap.congr_fun this x
  have := Q.e.ext (f₁ := Q.derLin ∘ₗ LinearMap.mulLeft B x)
    (f₂ := LinearMap.mulLeft B x ∘ₗ Q.derLin + LinearMap.mulRight B (Q.derLin x))
    (fun n ↦ by simpa using h2 x n)
  simpa using LinearMap.congr_fun this y

def PDPoly.der (Q : PDPoly B) : Derivation B Q.P Q.P :=
  Derivation.mk' Q.derLin fun x y ↦ by simpa [smul_eq_mul] using Q.derLin_mul x y

theorem PDPoly.der_apply (Q : PDPoly B) (x : Q.P) : Q.der x = Q.derLin x := rfl

end GlobalTheory.PDA

namespace GlobalTheory.PDA

variable {B : Type} [CommRing B]

theorem PDPoly.der_dpow_succ {J : Ideal B} (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) (n : ℕ) {a : Q.P} (ha : a ∈ Q.ext J) :
    Q.der (η.dpow (n + 1) a) = η.dpow n a * Q.der a := by
  set D := Q.der
  let P : Q.P → Prop := fun a ↦ ∀ n, D (η.dpow n a) = dpPred η n a • D a
  have hzero : P 0 := fun n ↦ by
    cases n with
    | zero => simp [η.dpow_zero (Q.ext J).zero_mem]
    | succ n => simp [dpow_eval_zero _ n.succ_ne_zero]
  have hadd : ∀ a ∈ Q.ext J, ∀ b ∈ Q.ext J, P a → P b → P (a + b) := fun a ha b hb iha ihb n ↦ by
    have iha : ∀ n, D (η.dpow n a) = dpPred η n a • D a := iha
    have ihb : ∀ n, D (η.dpow n b) = dpPred η n b • D b := ihb
    simp only [η.dpow_add ha hb, map_sum, D.leibniz, iha, ihb, smul_smul, Finset.sum_add_distrib,
      ← Finset.sum_smul, sum_dpow_mul_dpPred η ha hb, sum_dpow_mul_dpPred' η ha hb, map_add, smul_add]
    exact add_comm _ _
  have hmul : ∀ r, ∀ a ∈ Q.ext J, P a → P (r * a) := fun r a ha hP n ↦ by
    cases n with
    | zero => simp [η.dpow_zero (Ideal.mul_mem_left _ r ha), dpPred]
    | succ m =>
      have hm := hP (m + 1)
      have hs := dpPred_mul_self η ha (m + 1)
      simp only [dpPred, smul_eq_mul] at hm hs ⊢
      rw [η.dpow_mul ha, η.dpow_mul ha, D.leibniz, D.leibniz, D.leibniz_pow, hm]
      simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
      push_cast at hs ⊢
      linear_combination (-(r ^ m * D r)) * hs
  have hspan : ∀ s : Set Q.P, s ⊆ Q.ext J → (∀ x ∈ s, P x) → ∀ a ∈ Ideal.span s, P a := by
    intro s hs hP a ha
    have hle : Ideal.span s ≤ Q.ext J := Ideal.span_le.2 hs
    induction ha using Submodule.span_induction with
    | mem x hx => exact hP x hx
    | zero => exact hzero
    | add x y hx hy ihx ihy => exact hadd x (hle hx) y (hle hy) ihx ihy
    | smul r x hx ih => exact hmul r x (hle hx) ih
  have hJ : ∀ x ∈ J.map (algebraMap B Q.P), P x := by
    refine hspan _ ?_ ?_
    · rintro _ ⟨j, hj, rfl⟩; exact Q.algebraMap_mem_ext hj
    · rintro _ ⟨j, hj, rfl⟩ n
      rw [h.dp.2 j hj, Derivation.map_algebraMap, Derivation.map_algebraMap, smul_zero]
  have he1 := Q.e_one_mem_ext J
  have hA : ∀ x ∈ Q.aug, P x := by
    refine hspan _ ?_ ?_
    · rintro _ ⟨k, rfl⟩; exact Ideal.mem_sup_right (Q.e_succ_mem_aug k)
    · rintro _ ⟨k, rfl⟩ n
      cases n with
      | zero => simp [η.dpow_zero (Ideal.mem_sup_right (Q.e_succ_mem_aug k)), dpPred]
      | succ m =>
        have c1 : η.dpow (m + 1) (Q.e (k + 1)) =
            (Nat.uniformBell (m + 1) (k + 1) : Q.P) * Q.e ((m * (k + 1) + k) + 1) := by
          rw [← h.var (k + 1), η.dpow_comp (by omega) he1, h.var, show (m + 1) * (k + 1) = m * (k + 1) + k + 1 by ring]
        have c2 : dpPred η (m + 1) (Q.e (k + 1)) * Q.e k =
            (Nat.uniformBell (m + 1) (k + 1) : Q.P) * Q.e (m * (k + 1) + k) := by
          have := dpPred_dpow η he1 (m + 1) (n := k + 1) (by omega)
          rw [h.var, show dpPred η (k + 1) (Q.e 1) = Q.e k from h.var k,
            show (m + 1) * (k + 1) = m * (k + 1) + k + 1 by ring,
            show dpPred η (m * (k + 1) + k + 1) (Q.e 1) = Q.e (m * (k + 1) + k) from h.var _] at this
          exact this
        rw [c1, D.leibniz, D.map_natCast, smul_zero, add_zero, smul_eq_mul, smul_eq_mul, Q.der_apply,
          Q.der_apply, Q.derLin_e_succ, Q.derLin_e_succ, c2]
  have hall : ∀ x ∈ Q.ext J, P x := fun x hx ↦ by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    exact hadd y (Ideal.mem_sup_left hy) z (Ideal.mem_sup_right hz) (hJ y hy) (hA z hz)
  simpa [dpPred, smul_eq_mul] using hall a ha (n + 1)

theorem PDPoly.exists_der (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B)
    (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) :
    Q.IsStd δ η → ∃ D : Derivation R Q.P Q.P, (∀ b, D (algebraMap B Q.P b) = 0) ∧
      (∀ n, D (Q.e (n + 1)) = Q.e n) ∧ ∀ n, ∀ a ∈ Q.ext J, D (η.dpow (n + 1) a) = η.dpow n a * D a := by
  intro h
  refine ⟨Q.der.restrictScalars R, fun b ↦ ?_, fun n ↦ ?_, fun n a ha ↦ ?_⟩
  · rw [Derivation.restrictScalars_apply, Derivation.map_algebraMap]
  · rw [Derivation.restrictScalars_apply, Q.der_apply, Q.derLin_e_succ]
  · simp only [Derivation.restrictScalars_apply]
    exact Q.der_dpow_succ δ η h n ha

end GlobalTheory.PDA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsoIsometric
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoSeq

open GlobalTheory.VBExt (AdaptedChart)

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}
  {S S' : ShortComplex X.Modules} {r s : ℕ}

theorem f_inv (e₁ : S.X₁ ≅ S'.X₁) (e₂ : S.X₂ ≅ S'.X₂) (he : e₁.hom ≫ S'.f = S.f ≫ e₂.hom) :
    S'.f ≫ e₂.inv = e₁.inv ≫ S.f := by
  rw [Iso.comp_inv_eq, Category.assoc, ← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

def homThird (hS : S.ShortExact) (e₁ : S.X₁ ≅ S'.X₁) (e₂ : S.X₂ ≅ S'.X₂)
    (he : e₁.hom ≫ S'.f = S.f ≫ e₂.hom) : S.X₃ ⟶ S'.X₃ :=
  (Limits.CokernelCofork.IsColimit.desc' hS.gIsCokernel (e₂.hom ≫ S'.g) (by
    rw [← Category.assoc, ← he, Category.assoc, S'.zero, Limits.comp_zero])).1

theorem g_homThird (hS : S.ShortExact) (e₁ : S.X₁ ≅ S'.X₁) (e₂ : S.X₂ ≅ S'.X₂)
    (he : e₁.hom ≫ S'.f = S.f ≫ e₂.hom) : S.g ≫ homThird hS e₁ e₂ he = e₂.hom ≫ S'.g :=
  (Limits.CokernelCofork.IsColimit.desc' hS.gIsCokernel _ _).2

def isoThird (hS : S.ShortExact) (hS' : S'.ShortExact) (e₁ : S.X₁ ≅ S'.X₁) (e₂ : S.X₂ ≅ S'.X₂)
    (he : e₁.hom ≫ S'.f = S.f ≫ e₂.hom) : S.X₃ ≅ S'.X₃ where
  hom := homThird hS e₁ e₂ he
  inv := homThird hS' e₁.symm e₂.symm (f_inv e₁ e₂ he).symm
  hom_inv_id := Limits.Cofork.IsColimit.hom_ext hS.gIsCokernel (by
    change S.g ≫ _ ≫ _ = S.g ≫ 𝟙 _
    rw [← Category.assoc, g_homThird, Category.assoc, g_homThird, Iso.symm_hom,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id])
  inv_hom_id := Limits.Cofork.IsColimit.hom_ext hS'.gIsCokernel (by
    change S'.g ≫ _ ≫ _ = S'.g ≫ 𝟙 _
    rw [← Category.assoc, g_homThird, Category.assoc, g_homThird, Iso.symm_hom,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id])

theorem g_isoThird (hS : S.ShortExact) (hS' : S'.ShortExact) (e₁ : S.X₁ ≅ S'.X₁)
    (e₂ : S.X₂ ≅ S'.X₂) (he : e₁.hom ≫ S'.f = S.f ≫ e₂.hom) :
    S.g ≫ (isoThird hS hS' e₁ e₂ he).hom = e₂.hom ≫ S'.g :=
  g_homThird hS e₁ e₂ he

variable (e₁ : S.X₁ ≅ S'.X₁) (e₂ : S.X₂ ≅ S'.X₂) (e₃ : S.X₃ ≅ S'.X₃)
  (he : e₁.hom ≫ S'.f = S.f ≫ e₂.hom) (hg : S.g ≫ e₃.hom = e₂.hom ≫ S'.g)

include hg in

theorem app_g (U : X.Opens) (x : Γ(S.X₂, U)) :
    S'.g.app U (e₂.hom.app U x) = e₃.hom.app U (S.g.app U x) := by
  have := congr(($(hg)).app U x)
  simpa [Scheme.Modules.Hom.comp_app] using this.symm

include he in

theorem app_f (U : X.Opens) (x : Γ(S.X₁, U)) :
    S'.f.app U (e₁.hom.app U x) = e₂.hom.app U (S.f.app U x) := by
  have := congr(($(he)).app U x)
  simpa [Scheme.Modules.Hom.comp_app] using this

def mapChart (a : AdaptedChart S r s) : AdaptedChart S' r s where
  U := a.U
  e i := e₁.hom.app a.U (a.e i)
  t i := e₂.hom.app a.U (a.t i)
  he := a.he.map_iso e₁.hom
  ht := by
    have := a.ht.map_iso e₃.hom
    convert this using 2 with i
    exact app_g e₂ e₃ hg _ _

include he in

theorem mapChart_frame (a : AdaptedChart S r s) (j : Fin r ⊕ Fin s) :
    (mapChart e₁ e₂ e₃ hg a).frame j = e₂.hom.app a.U (a.frame j) := by
  rcases j with j | j
  · exact app_f e₁ e₂ he _ _
  · rfl

theorem mapChart_quot (a : AdaptedChart S r s) :
    (mapChart e₁ e₂ e₃ hg a).quot = a.quot.map e₃ := by
  simp only [AdaptedChart.quot, Chart.map, mapChart, Chart.mk.injEq, true_and]
  exact heq_of_eq (funext fun i => app_g e₂ e₃ hg _ _)

end GlobalTheory.IsoSeq

namespace GlobalTheory.IsoSeq

open GlobalTheory.VBExt (AdaptedChart)

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}
  {S S' : ShortComplex X.Modules} {r s : ℕ}
  {e₁ : S.X₁ ≅ S'.X₁} {e₂ : S.X₂ ≅ S'.X₂} {e₃ : S.X₃ ≅ S'.X₃}
  (he : e₁.hom ≫ S'.f = S.f ≫ e₂.hom) (hg : S.g ≫ e₃.hom = e₂.hom ≫ S'.g)
  {h : VMetric p S.X₂ (r + s)} {h' : VMetric p S'.X₂ (r + s)}

include he in

theorem gram_mapChart (hI : h.IsIsometry h' e₂) (σ : k →+* ℂ) (a : AdaptedChart S r s)
    {y : CxPts p σ} (hy : y ∈ ptsIn p σ a.U) :
    (h'.met σ).gram (mapChart e₁ e₂ e₃ hg a).frame y = (h.met σ).gram a.frame y := by
  ext i j
  simp only [Met.gram, Matrix.of_apply, mapChart_frame e₁ e₂ e₃ he hg]
  exact hI σ a.U _ _ y hy

include he hg in

theorem quot_isIsometry (hS : S.ShortExact) (hS' : S'.ShortExact) (h₁ : IsVB S.X₁ r)
    (h₃ : IsVB S.X₃ s) (h₁' : IsVB S'.X₁ r) (h₃' : IsVB S'.X₃ s) (hI : h.IsIsometry h' e₂) :
    (h.quot hS h₁ h₃).IsIsometry (h'.quot hS' h₁' h₃') e₃ := by
  rw [VMetric.isIsometry_iff]
  refine VMetric.ext (funext fun σ => Met.ext_of_exists fun y => ?_)
  obtain ⟨a, ha⟩ := Met.exists_adapted hS h₁ h₃ y
  refine ⟨(mapChart e₁ e₂ e₃ hg a).quot, ha, ?_⟩
  change ((h'.met σ).quot hS' h₁' h₃').G _ y = (((h.met σ).quot hS h₁ h₃).map e₃).G _ y
  rw [Met.quot_G _ hS' h₁' h₃' (mapChart e₁ e₂ e₃ hg a) ha, mapChart_quot e₁ e₂ e₃ hg,
    Met.map_G _ _ _ ha, Met.quot_G _ hS h₁ h₃ a ha, gram_mapChart he hg hI σ a ha]

include he hg in

theorem bcMeas_eq (hS : S.ShortExact) (hS' : S'.ShortExact) (h₁ : IsVB S.X₁ r)
    (h₃ : IsVB S.X₃ s) (h₁' : IsVB S'.X₁ r) (h₃' : IsVB S'.X₃ s) (H : h.IsCInf) (H' : h'.IsCInf)
    (hI : h.IsIsometry h' e₂) (σ : k →+* ℂ) :
    (h.met σ).bcMeas hS h₁ h₃ = (h'.met σ).bcMeas hS' h₁' h₃' := by
  refine part_congr fun c y hy => ?_
  obtain ⟨a, ha⟩ := Met.exists_adapted hS h₁ h₃ y
  refine (Met.bcDens_eq_of_gram hS hS' h₁ h₃ h₁' h₃' (H σ) (H' σ) a (mapChart e₁ e₂ e₃ hg a) c c hy hy
    ha ha rfl ?_).symm
  filter_upwards [(ChartGlue.isOpen_over c.e (isOpen_ptsIn a.U)).mem_nhds
    (ChartGlue.mem_over c.e hy ha)] with v hv
  exact gram_mapChart he hg hI σ a hv.2

end GlobalTheory.IsoSeq

namespace GlobalTheory

theorem isometric_detQuot_and_bcInt_eq_of_iso : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (S S' : ShortComplex X.Modules) (r s : ℕ) (h : VMetric p S.X₂ (r + s)) (h' : VMetric p S'.X₂ (r + s)) (H : h.IsCInf) (H' : h'.IsCInf) (hS : S.ShortExact) (hS' : S'.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (h₁' : IsVB S'.X₁ r) (h₃' : IsVB S'.X₃ s) (e₁ : S.X₁ ≅ S'.X₁) (e₂ : S.X₂ ≅ S'.X₂), e₁.hom ≫ S'.f = S.f ≫ e₂.hom → h.IsIsometry h' e₂ → (VMetric.det (H.quot hS h₁ h₃)).Isometric (VMetric.det (H'.quot hS' h₁' h₃')) ∧ h.bcInt hS h₁ h₃ = h'.bcInt hS' h₁' h₃' := by
  intro k _ X p S S' r s h h' H H' hS hS' h₁ h₃ h₁' h₃' e₁ e₂ he hI
  have hg := IsoSeq.g_isoThird hS hS' e₁ e₂ he
  refine ⟨GlobalTheory.CurveDens.det_isometric_of_isIsometry k X p _ _ s _ _ (H.quot hS h₁ h₃) (H'.quot hS' h₁' h₃')
    (IsoSeq.isoThird hS hS' e₁ e₂ he) (IsoSeq.quot_isIsometry he hg hS hS' h₁ h₃ h₁' h₃' hI), ?_⟩
  exact finsum_congr fun σ => by
    rw [IsoSeq.bcMeas_eq he hg hS hS' h₁ h₃ h₁' h₃' H H' hI σ]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaSumRationalPairInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

namespace GlobalTheory.DiagThetaRatInv

theorem dot_elim {R : Type} [CommRing R] {κ : Type} [Fintype κ] (x : κ ⊕ κ → R) (v : κ → R) :
    x ⬝ᵥ Sum.elim v (-v) = ∑ i, (x (Sum.inl i) - x (Sum.inr i)) * v i := by
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, mul_neg, sub_mul,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]
  simp only [add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem schr_diag {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (u v : κ → R) (Φ : (κ ⊕ κ → R) → ℂ) (x : κ ⊕ κ → R) :
    GlobalTheory.WeilM.schr ψ (Sum.elim u u, Sum.elim v (-v)) Φ x =
      ψ (∑ i, (x (Sum.inl i) - x (Sum.inr i)) * v i) * Φ (x + Sum.elim u u) := by
  simp only [GlobalTheory.WeilM.schr]
  rw [dot_elim, dot_elim]
  simp

theorem diag_theta_rat_inv : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ]
    (Φ : (κ ⊕ κ → AF F) → ℂ), ∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w : (κ → AF F) × (κ → AF F),
      GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim (γ + w).1 (γ + w).1, Sum.elim (γ + w).2 (-(γ + w).2)) Φ) =
        GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ) := by
  intro F _ _ ψ hψ κ _ Φ γ hγ w
  obtain ⟨a, b, rfl⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff γ).1 hγ
  simp only [GlobalTheory.WeilM.thetaSum]
  rw [← (Equiv.subRight (Sum.elim a a)).tsum_eq]
  congr 1
  funext η
  rw [schr_diag, schr_diag]
  simp only [Equiv.subRight_apply, Prod.fst_add, Prod.snd_add]
  have h1 : (∑ i, (algebraMap F (AF F) ((η - Sum.elim a a) (Sum.inl i)) -
        algebraMap F (AF F) ((η - Sum.elim a a) (Sum.inr i))) * ((fun i => algebraMap F (AF F) (b i)) + w.2) i) =
      algebraMap F (AF F) (∑ i, (η (Sum.inl i) - η (Sum.inr i)) * b i) +
        ∑ i, (algebraMap F (AF F) (η (Sum.inl i)) - algebraMap F (AF F) (η (Sum.inr i))) * w.2 i := by
    rw [map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, map_sub, map_mul]
    ring
  have h2 : (fun i => algebraMap F (AF F) ((η - Sum.elim a a) i)) +
        Sum.elim ((fun i => algebraMap F (AF F) (a i)) + w.1) ((fun i => algebraMap F (AF F) (a i)) + w.1) =
      (fun i => algebraMap F (AF F) (η i)) + Sum.elim w.1 w.1 := by
    funext j
    cases j <;> simp <;> abel
  rw [h1, h2, AddChar.map_add_eq_mul, hψ.2.2.1, one_mul]

end GlobalTheory.DiagThetaRatInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtReprPullbackHolomorphicFderiv
section
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm

variable {n : ℕ}

theorem differentiableAt_repr_map_toLin' {M : V n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ} {v : V n}
    (hM : ∀ i j, DifferentiableAt ℝ (fun w => M w i j) v) (γ : Alt n) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun w => (bas n).repr (ExteriorAlgebra.map (Matrix.toLin' (M w)) γ) S) v := by
  induction γ using ExteriorAlgebra.induction generalizing S with
  | algebraMap r =>
    simp only [AlgHom.commutes]
    exact differentiableAt_const _
  | ι x =>
    simp only [ExteriorAlgebra.map_apply_ι]
    let ℓ : (Fin n ⊕ Fin n → ℂ) →ₗ[ℂ] ℂ :=
      Finsupp.lapply S ∘ₗ (bas n).repr.toLinearMap ∘ₗ ExteriorAlgebra.ι ℂ
    have hu : DifferentiableAt ℝ (fun w => Matrix.toLin' (M w) x) v := by
      simp only [Matrix.toLin'_apply]
      refine differentiableAt_pi.2 fun i => ?_
      simp only [mulVec, dotProduct]
      exact DifferentiableAt.fun_sum fun j _ => (hM i j).mul_const _
    exact ((LinearMap.toContinuousLinearMap ℓ).restrictScalars ℝ).differentiableAt.comp v hu
  | mul a b ha hb =>
    have e : (fun w => (bas n).repr (ExteriorAlgebra.map (Matrix.toLin' (M w)) (a * b)) S) = fun w =>
        ∑ p : Finset (Fin (n + n)) × Finset (Fin (n + n)), (bas n).repr (ExteriorAlgebra.map (Matrix.toLin' (M w)) a) p.1 *
          (bas n).repr (ExteriorAlgebra.map (Matrix.toLin' (M w)) b) p.2 * (bas n).repr (bas n p.1 * bas n p.2) S :=
      funext fun w => by rw [map_mul, FormMul.repr_mul]
    rw [e]
    exact DifferentiableAt.fun_sum fun p _ => ((ha p.1).mul (hb p.2)).mul_const _
  | add a b ha hb =>
    simp only [map_add, Finsupp.add_apply]
    exact (ha S).add (hb S)

theorem differentiableAt_repr_pull_fderiv : ∀ {n : ℕ} {φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n}
    {v : ReciprocityTheory.L2DbarEstimates.V n}, ContDiffAt ℂ 2 φ v → ∀ (γ : GlobalTheory.CxForm.Alt n) (S : Finset (Fin (n + n))),
    DifferentiableAt ℝ (fun w => (GlobalTheory.CxForm.bas n).repr (GlobalTheory.CxForm.pull (fderiv ℂ φ w) γ) S) v := by
  intro n φ v h γ S
  have hd : DifferentiableAt ℂ (fderiv ℂ φ) v :=
    (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he (b a : Fin n) : DifferentiableAt ℝ (fun w => fderiv ℂ φ w (coordVec b) a) v :=
    (((EuclideanSpace.proj a : V n →L[ℂ] ℂ).differentiableAt).comp v
      (hd.clm_apply (differentiableAt_const (coordVec b)))).restrictScalars ℝ
  have hc (b a : Fin n) : DifferentiableAt ℝ (fun w => conj (fderiv ℂ φ w (coordVec b) a)) v :=
    Complex.conjCLE.differentiableAt.comp v (he b a)
  refine differentiableAt_repr_map_toLin' (M := fun w => fromBlocks (of fun b a => fderiv ℂ φ w (coordVec b) a) 0 0
    (of fun b a => conj (fderiv ℂ φ w (coordVec b) a))) ?_ γ S
  rintro (i | i) (j | j)
  · simpa only [fromBlocks_apply₁₁, of_apply] using he i j
  · simp only [fromBlocks_apply₁₂, Matrix.zero_apply]; exact differentiableAt_const _
  · simp only [fromBlocks_apply₂₁, Matrix.zero_apply]; exact differentiableAt_const _
  · simpa only [fromBlocks_apply₂₂, of_apply] using hc i j

end GlobalTheory.CxForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceSmallOfFunctionFieldEmbedsRatFunc
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.SmallPf

theorem exists_dim (F : Type) [Field F] {Z : Scheme.{0}} [IsIntegral Z] (f : Z ⟶ Sp F) [LocallyOfFiniteType f] :
    ∃ d : ℕ, topologicalKrullDim Z = d := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint Z)) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨d, h₁, -⟩ := GlobalTheory.OpenDim.ringKrullDim_affineOpen F f hU ⟨_, hxU⟩
  refine ⟨d, ?_⟩
  rw [← GlobalTheory.OpenDim.topologicalKrullDim_open F f U ⟨_, hxU⟩, ← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec

theorem main : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ j : W.Z.functionField →+* RatFunc Y.Fn, j.comp W.α₁ = algebraMap Y.Fn (RatFunc Y.Fn) → W.Small := by
  intro F _ Y W j hj
  have hp := W.proj
  have hlft : LocallyOfFiniteType (W.p₁ ≫ Y.str) := by
    obtain ⟨N, i, hi, hcomp⟩ := hp
    haveI : IsProper (PSpace.str F N) := isProper_str F N
    rw [← hcomp]; infer_instance
  obtain ⟨d, hd⟩ := exists_dim F (W.p₁ ≫ Y.str)
  have hY : Y.X.fromSpecStalk (genericPoint Y.X) ≫ Y.str = spMap (algebraMap F Y.Fn) := (ratOf Y).pt_s
  have hZ : W.Z.fromSpecStalk (genericPoint W.Z) ≫ W.p₁ ≫ Y.str = spMap (W.α₁.comp (algebraMap F Y.Fn)) := by
    have h1 : spMap W.α₁ ≫ Y.X.fromSpecStalk (genericPoint Y.X) = W.Z.fromSpecStalk (genericPoint W.Z) ≫ W.p₁ :=
      specMap_functionFieldMap W.p₁
    rw [← Category.assoc, ← h1, Category.assoc, hY]
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap F Y.Fn)) (CommRingCat.ofHom W.α₁)).symm
  have t₁ := GlobalTheory.FunctionFieldTrdeg.trdeg_functionField_eq F Y.X Y.str Y.dim Y.isProjOver Y.topologicalKrullDim_eq _ hY
  have t₂ := GlobalTheory.FunctionFieldTrdeg.trdeg_functionField_eq F W.Z _ d W.proj hd _ hZ
  have t₃ := @GlobalTheory.T.trdeg_le_succ_of_embedding_ratFunc F Y.Fn W.Z.functionField _ _ _ (algebraMap F Y.Fn).toAlgebra
    (W.α₁.comp (algebraMap F Y.Fn)).toAlgebra W.α₁ j Y.dim rfl hj t₁
  rw [t₂] at t₃
  have : d ≤ Y.dim + 1 := by exact_mod_cast t₃
  unfold Dbl.Small
  rw [hd]
  exact_mod_cast this

end GlobalTheory.FlagPush.SmallPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenspaceDimensionOfUniformizationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenspace_dimension_of_uniformization : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL (D' : PLat D.O D.inv) t Q e, UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → ∀ τ : Fin D.a → (D.F →+* ℂ), (∀ i (c : 𝓞 D.F), τ i (c : D.F) = σ (b.t i c)) → (∀ i, Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i)) = D.m) ∧ ∀ u : Fin D.g → ℂ, ρ (algebraMap (𝓞 D.F) D.O D.ω) *ᵥ u = σ b.ρ • u → u ∈ ⨆ i, eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i) := by
  first | exact @GlobalTheory.UPel.HT.LieType.lieEigen_rank_cover | exact GlobalTheory.UPel.HT.LieType.lieEigen_rank_cover | (intros; apply GlobalTheory.UPel.HT.LieType.lieEigen_rank_cover <;> assumption)
end

