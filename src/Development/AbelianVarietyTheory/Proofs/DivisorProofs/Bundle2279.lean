import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsValueEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0119
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0020
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleDescentGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingSectionOfIsolatedNonKltPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_sec_sep_of_lcCut : GlobalTheory.Published.NadelVanishingPair → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (ρ d : ℚ) (x x' : X), M.IsLB → IsEffQDiv Δ → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → QNum p N d D → d < ρ → IsClosed ({x} : Set X) → x ≠ x' → LcCut p n (Δ + D) x 0 → ¬ KltAt p n (Δ + D) x' → ∃ s : M.Sec, x ∈ nonzeroLocus s ∧ x' ∉ nonzeroLocus s := by
  intro hNadel X _ _ _ p n hp hn
  letI := algebraΓOfHom p
  intro M Δ m G N D ρ d x x' hM hΔ hm hG hN hdeg hD hdρ hx hxx' hlc hx'
  haveI hNoeth : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  obtain ⟨-, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  obtain ⟨m', D₀, hm', hD₀, rfl, hDn⟩ := hD

  have hq0 : 0 < ρ - d := sub_pos.2 hdρ
  set a : ℕ := (ρ - d).num.toNat with ha_def
  set b : ℕ := (ρ - d).den with hb_def
  have hb : 0 < b := (ρ - d).den_pos
  have hnum : 0 < (ρ - d).num := Rat.num_pos.2 hq0
  have ha : ((a : ℤ) : ℚ) = (ρ - d).num := by
    rw [ha_def, Int.toNat_of_nonneg hnum.le]
  have ha1 : 1 ≤ a := by omega
  have hab : ρ - d = (a : ℚ) / b := by
    have e := Rat.num_div_den (ρ - d)
    rw [← ha, Int.cast_natCast] at e
    exact e.symm
  have hpS : IsProjOver (strHom ℂ X) := by rwa [strHom_eq (f := p) fun _ => rfl]
  have hNa : IsAmpleLB (lbPow N a) := (isAmpleLB_pow_iff hN.isLB ha1).2 hN
  have hdeg' : ∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) =
      interNumRed ℂ C ![toLB (m' • G + m • D₀)] / ((m * m' : ℕ) : ℚ) +
        interNumRed ℂ C ![lbPow N a] / (b : ℚ) := by
    intro C hC
    have e := hC.interNumRed_of_cls_eq_add hH (isLB_toLB (m' • G + m • D₀))
      (isLB_lbPow (isLB_toLB G) m') (isLB_lbPow (isLB_toLB D₀) m)
      (by rw [cls_lbPow (isLB_toLB G), cls_lbPow (isLB_toLB D₀), ← toPic_apply, ← toPic_apply,
        ← toPic_apply, map_add, map_nsmul, map_nsmul])
    rw [hC.interNumRed_lbPow hH (isLB_toLB G), hC.interNumRed_lbPow hH (isLB_toLB D₀)] at e
    have h1 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have h2 : (m' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm'.ne'
    have h3 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
    have hD' := hDn C hC
    rw [div_eq_iff h2] at hD'
    rw [hdeg C hC, e, hC.interNumRed_lbPow hH hN.isLB a, show ρ = d + a / b by linarith]
    push_cast
    rw [hD']
    field_simp
    ring
  obtain ⟨J, hJ, hvan⟩ := hNadel X p n hp hn M (Δ + qWeil D₀ m') (m * m') (m' • G + m • D₀) b
    (lbPow N a) hM (isEffQDiv_add_of_isQCart X p hp Δ _ hΔ ⟨m', D₀, hm', hD₀, rfl⟩)
    (Nat.mul_pos hm hm') (isLogCanonicalMultiple_add_qWeil X p n Δ m m' G D₀ hm hm' hG) hb
    hNa.isNef (IsAmpleLB.isBig ℂ X hpS _ hNa) hdeg'
  have hxJ : x ∈ J.support := (hJ x).2 hlc.2.1
  have hx'J : x' ∈ J.support := (hJ x').2 hx'
  obtain ⟨U, hxU, hU⟩ := exists_open_inter_eq_singleton_of_no_generisation X (J.support : Set X) x
    J.support.isClosed hx hxJ fun z hz hzx => by
      by_contra hne
      obtain ⟨e, -, he, h1⟩ := closure_point_topologicalKrullDim X n z hn
      have h0 := hlc.2.2 z hzx ((hJ z).1 hz)
      have he1 := h1 x hzx (Ne.symm hne)
      rw [he] at h0
      have : e ≤ 0 := by exact_mod_cast h0
      omega
  obtain ⟨s, hs1, hs2⟩ := exists_sec_mem_nonzeroLocus_of_isolated_zero_else ℂ X p hp M hM J x U hx
    hxU hU (hvan 1 one_pos)
  exact ⟨s, hs1, hs2 x' hx'J (Ne.symm hxx')⟩

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevel
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegLower

theorem weilIs_lower_field {K : Type} [Field K] [IsAlgClosed K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) {n d : ℕ} (hd : d ≠ 0) {T : Over (Sp K)} {x y : T ⟶ A}
    {c : Γ(T.left, ⊤)ˣ} (hx : x ^ (n * d) = 1) (hy : y ^ (n * d) = 1)
    (h : Out.WeilIs A L ((n * d : ℕ) : ℤ) x y c) : Out.WeilIs A L n (x ^ d) (y ^ d) (c ^ d) := by
  obtain ⟨r, hr⟩ := DVR.exists_gen_of_isLB_local (V := K) (L.pull (eSec A)) (pull_isLB hL _)
  let M : RigLB A := ⟨L, r, hL, hr⟩
  obtain ⟨t, ht⟩ := AbLaw.CubeProj.exists_gen_theta_abelianVariety globalFns_holds K A hA
    (AbelianProjective.isProjBy_of_isAbelianScheme K A hA) L hL
  obtain ⟨t', ht', hn⟩ := AbLaw.Cube.exists_normalised hL t ht
  let cub : CubicalStr A M := AbLaw.Cube.cubicalOfNormalised globalFns_holds hA M t' ht' hn
  have hx' : (x ^ d) ^ n = 1 := by rw [← pow_mul, mul_comm, hx]
  have hy' : (y ^ d) ^ n = 1 := by rw [← pow_mul, mul_comm, hy]
  obtain ⟨w, hw⟩ := exists_weil cub hx' hy'
  have h₁ : Out.WeilIs A L n (x ^ d) (y ^ d) w := (weilIs_iff cub globalFns_holds hA hx' hy' hw w).2 rfl
  have h' := CommPairing.weilIs_symm hL h
  have hp : ∀ j : ℕ, Out.WeilIs A L ((n * d : ℕ) : ℤ) (y ^ (j + 1)) x (c⁻¹ ^ (j + 1)) := fun j => by
    induction j with
    | zero => rwa [zero_add, pow_one, pow_one]
    | succ j ih => rw [pow_succ, pow_succ c⁻¹]; exact SiegelTypings.weilIs_mul hA hL ih h'
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
  have h₂ := CommPairing.weilIs_symm hL (hp j)
  rw [inv_pow, inv_inv, Nat.cast_mul] at h₂
  rw [PairingLevels.weilIs_value_eq globalFns_holds hA hL ht h₂ h₁]
  exact h₁

variable {h N : ℕ} {B' : Type} [CommRing B'] {ζ' : B'} {S : Scheme.{0}} {s' : S ⟶ Sp B'}

theorem weilIs_lower (C : SiegPre h N ζ' s') {K : Type} [Field K] [IsAlgClosed K] (p : Sp K ⟶ S) {n d : ℕ} (hd : d ≠ 0) :
    ∀ (x y : Over.mk p ⟶ C.A) (u : Kˣ), x ^ (n * d) = 1 → y ^ (n * d) = 1 →
      Out.WeilIs C.A C.diag ((n * d : ℕ) : ℤ) x y (unitOn u) →
      Out.WeilIs C.A C.diag n (x ^ d) (y ^ d) (unitOn (u ^ d)) := by
  obtain ⟨c, φ, φ₂, pb, sq, iso, -⟩ := (siegPre_pullback h N B' ζ' S _ s' _ p C rfl).1
  have key : ∀ q : Sp K ⟶ S, q = 𝟙 _ ≫ p → ∀ (x y : Over.mk q ⟶ C.A) (u : Kˣ), x ^ (n * d) = 1 → y ^ (n * d) = 1 →
      Out.WeilIs C.A C.diag ((n * d : ℕ) : ℤ) x y (unitOn u) →
      Out.WeilIs C.A C.diag n (x ^ d) (y ^ d) (unitOn (u ^ d)) := by
    rintro q rfl x y u hx hy H
    let e := ObjPull.pushEquiv pb (Over.mk (𝟙 (Sp K)))
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    have tr := fun (k : ℤ) (a b : Over.mk (𝟙 (Sp K)) ⟶ c.A) (v : Γ(Sp K, ⊤)ˣ) =>
      weilIs_grpPullback_of_comm S _ C.A c.A p φ C.diag c.diag (pull_isLB C.isLB _) (pull_isLB c.isLB _) pb
        (SiegelPull.diag_iso sq iso) (Over.mk (𝟙 _)) k a b (e a) (e b) v rfl rfl
    have hx' : x ^ (n * d) = 1 := e.injective ((map_pow e _ _).trans (hx.trans (map_one e).symm))
    have hy' : y ^ (n * d) = 1 := e.injective ((map_pow e _ _).trans (hy.trans (map_one e).symm))
    have H' := (tr _ _ _ _).1 (weilIs_lower_field c.ab (pull_isLB c.isLB _) hd hx' hy' ((tr _ _ _ _).2 H))
    rw [map_pow, map_pow] at H'
    have e' : unitOn (u ^ d) = unitOn u ^ d := map_pow _ _ _
    rw [e']
    exact H'
  exact key p (Category.id_comp p).symm

def lower (C : SiegPre h N ζ' s') {n d : ℕ} (hN : N = n * d) (h0 : N ≠ 0) {B : Type} [CommRing B] {ζ : B} (j : B →+* B')
    (hj : j ζ = ζ' ^ d) : SiegPre h n ζ (s' ≫ spMap j) where
  A := C.A
  ab := C.ab
  P := C.P
  isLB := C.isLB
  rig₁ := C.rig₁
  rig₂ := C.rig₂
  symm := C.symm
  lev a := C.lev a ^ d
  lev_add a b := by rw [C.lev_add, mul_pow]
  lev_tors a := by rw [← pow_mul, mul_comm, ← hN, C.lev_tors]
  geom k _ _ x β z hx hz := by
    have hn : n ≠ 0 := fun e => h0 (by rw [hN, e, zero_mul])
    have hd : d ≠ 0 := fun e => h0 (by rw [hN, e, mul_zero])
    obtain ⟨β', hβ'⟩ : ∃ β' : B' →+* k, x ≫ s' = spMap β' :=
      ⟨(Spec.preimage (x ≫ s')).hom, (Spec.map_preimage _).symm⟩
    have hβ : β = β'.comp j := by
      have e : Spec.map (CommRingCat.ofHom β) = Spec.map (CommRingCat.ofHom (β'.comp j)) := by
        refine hx.symm.trans ?_
        rw [← Category.assoc, hβ']
        exact (Spec.map_comp _ _).symm
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
    have hz' : (z : k) = β' ζ' ^ d := by rw [hz, hβ, RingHom.comp_apply, hj, map_pow]
    have hu : β' ζ' ≠ 0 := fun e => z.ne_zero (by rw [hz', e, zero_pow hd])
    have ez : z = Units.mk0 _ hu ^ d := Units.ext (by rw [hz', Units.val_pow_eq_pow_val, Units.val_mk0])
    obtain ⟨g₁, g₂, g₃⟩ := C.geom k x β' (Units.mk0 _ hu) hβ' rfl
    refine ⟨fun a => ?_, fun g hg => ?_, fun a b => ?_⟩
    · rw [← SiegelTypings.lev_nsmul, g₁]
      refine exists_congr fun b => ?_
      rw [hN, mul_comm, mul_smul]
      exact (smul_right_injective _ hd).eq_iff
    · obtain ⟨a, rfl⟩ := g₂ g ((congrArg (g ^ ·) hN).trans (by rw [pow_mul, hg, one_pow]))
      rw [← MonObj.comp_pow, ← SiegelTypings.lev_nsmul, g₁] at hg
      obtain ⟨b, hb⟩ := hg
      rw [hN, mul_smul] at hb
      exact ⟨b, by rw [smul_right_injective _ hn hb, SiegelTypings.lev_nsmul]⟩
    · have t : ∀ a, (toUnit (Over.mk x) ≫ C.lev a) ^ (n * d) = 1 := fun a => by
        rw [← MonObj.comp_pow, ← hN, C.lev_tors, MonObj.comp_one]
      have H := weilIs_lower C x hd _ _ _ (t a) (t b) (by rw [← hN]; exact g₃ a b)
      have e : (Units.mk0 _ hu ^ d) ^ (2 * omegaStd a b) = (Units.mk0 _ hu ^ (2 * omegaStd a b)) ^ d := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
      show Out.WeilIs C.A C.diag n (toUnit (Over.mk x) ≫ C.lev a ^ d) (toUnit (Over.mk x) ≫ C.lev b ^ d)
        (unitOn (z ^ (2 * omegaStd a b)))
      rw [ez, e, MonObj.comp_pow, MonObj.comp_pow]
      exact H

theorem isGrpPullback_id (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨(IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback (𝟙 G.left) G.hom G.hom (𝟙 S)),
    fun T x y x₀ y₀ hx hy => ?_⟩
  refine Eq.trans ?_ (Category.comp_id _).symm
  exact mul_left_congr (b := T.hom) (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _))
    (hy.trans (Category.comp_id _))

theorem lbIso_pull_id {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L (L.pull (𝟙 X)) :=
  (LBIso.chartPull (Geo.Tor.chartPullPull L (𝟙 _) (𝟙 _) rfl) (chartPullId L) (lbIso_refl hL)).symm

theorem exists_lower : ∀ (h n N : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (j : B →+* B')
    (S : Scheme.{0}) (s' : S ⟶ Sp B') (C : SiegPre h N ζ' s'), N ≠ 0 → IsUnit (N : B') → n ∣ N → j ζ = ζ' ^ (N / n) →
    ∃ c : SiegPre h n ζ (s' ≫ spMap j), SRel C c (N / n) 1 (𝟙 S) ∧ SRel c C 1 (N / n) (𝟙 S) := by
  intro h n N B B' _ _ ζ ζ' j S s' C h0 _ hn hj
  have sq : IsSquare (G' := C.A) (G := C.A) (𝟙 _) (𝟙 _) := ⟨by simp, by simp⟩
  refine ⟨lower C (Nat.mul_div_cancel' hn).symm h0 j hj,
    ⟨𝟙 _, isGrpPullback_id C.A, ⟨𝟙 _, sq, lbIso_pull_id C.isLB⟩, fun a => ?_⟩,
    ⟨𝟙 _, isGrpPullback_id C.A, ⟨𝟙 _, sq, lbIso_pull_id C.isLB⟩, fun a => ?_⟩⟩
  · rw [pow_one]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · rw [pow_one]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

end GlobalTheory.SiegLower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectOfGaloisDescendedData
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelGaloisDescent

open GlobalTheory.CechPic

variable {S : Scheme.{0}}

theorem eta_lift_one_id (A : Over S) [GrpObj A] : η[A] ≫ lift (1 : A ⟶ A) (𝟙 A) = η[A ⊗ A] := by
  ext <;> simp [Hom.one_def]

theorem eta_lift_id_one (A : Over S) [GrpObj A] : η[A] ≫ lift (𝟙 A) (1 : A ⟶ A) = η[A ⊗ A] := by
  ext <;> simp [Hom.one_def]

theorem eta_swap (A : Over S) [GrpObj A] : η[A ⊗ A] ≫ lift (snd A A) (fst A A) = η[A ⊗ A] := by
  ext <;> simp

theorem eq_zero_of_cart (hG : Out.GlobalFnsSt) {S' : Scheme.{0}} (π : S' ⟶ S) [Flat π] [Surjective π]
    [QuasiCompact π] {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) {B : Over S'} {φ : B.left ⟶ A.left}
    (hp : IsPullback φ B.hom A.hom π) (c : Pic A.left) (h₀ : pull (eSec A) c = 0) (h₁ : pull φ c = 0) : c = 0 := by
  refine TripleDescent.eq_zero_of_pull hG π hA c h₀ ?_
  have e : (TripleDescent.fibreProj A π).left = hp.isoPullback.inv ≫ φ := by
    simp [TripleDescent.fibreProj]
  rw [e, pull_comp, h₁, map_zero]

end GlobalTheory.SiegelGaloisDescent

namespace GlobalTheory

open SiegelDescent SiegelGaloisDescent CechPic

theorem exists_siegPre_of_galois_descended_data : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (X Y : Scheme.{0}) (π : X ⟶ Y) (s : X ⟶ Sp o) (sY : Y ⟶ Sp o) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (c : SiegPre h M ζ s) (A₀ : Over Y) [GrpObj A₀] (φ : c.A.left ⟶ A₀.left) (φ₂ : (G2 c.A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left) (lev₀ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y) ⟶ A₀)), s = π ≫ sY → IsGaloisCover Ga ρ π → IsAbelianScheme A₀ → IsGrpPullback c.A A₀ π φ → IsSquare φ φ₂ → P₀.IsLB → LBIso c.P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → (∀ a, (c.lev a).left ≫ φ = π ≫ (lev₀ a).left) → ∃ c₀ : SiegPre h M ζ sY, SiegPB c c₀ π := by
  intro h M o _ ζ X Y π s sY Ga _ ρ c A₀ _ φ φ₂ P₀ lev₀ hs hGal ab hp sq hP₀ hw ht hlev
  haveI := ab.comm
  have gf : Out.GlobalFnsSt := abelianSchemeLaws_all.1.globalFns
  haveI : IsFinite π := hGal.fin
  haveI : Etale π := hGal.etale
  haveI : Surjective π := hGal.onto
  haveI : Epi π := Flat.epi_of_flat_of_surjective π
  have hφ : φ ≫ A₀.hom = c.A.hom ≫ π := hp.1.w
  have one := one_comp hp c.A A₀ φ hφ
  have idφ : (𝟙 c.A : c.A ⟶ c.A).left ≫ φ = φ ≫ (𝟙 A₀ : A₀ ⟶ A₀).left := by simp
  have ab₂ := AbelianSchemeGerms.isAbelianScheme_tensor A₀ A₀ ab ab
  have hp₂ := isPullback_square hp.1 φ₂ sq
  have clsP : cls c.P c.isLB = pull φ₂ (cls P₀ hP₀) := by
    rw [← cls_pull hP₀ φ₂ (pull_isLB hP₀ _)]
    exact (cls_eq_iff _ _).2 hw
  have P₀e : pull (eSec (G2 A₀)) (cls P₀ hP₀) = 0 := by
    rw [← cls_pull hP₀ _ (pull_isLB hP₀ _)]
    exact (cls_eq_zero_iff _).2 ht
  have rig : ∀ (a : c.A ⟶ c.A ⊗ c.A) (a₀ : A₀ ⟶ A₀ ⊗ A₀), a.left ≫ φ₂ = φ ≫ a₀.left →
      η[A₀] ≫ a₀ = η[A₀ ⊗ A₀] → (∃ t : (c.P.pull a.left).Gen, t.IsGen) →
      ∃ t : (P₀.pull a₀.left).Gen, t.IsGen := by
    intro a a₀ e e₀ hta
    have e₀' : eSec A₀ ≫ a₀.left = eSec (G2 A₀) := congrArg (fun q => q.left) e₀
    refine (cls_eq_zero_iff (pull_isLB hP₀ _)).1 ?_
    rw [cls_pull hP₀ _ (pull_isLB hP₀ _)]
    refine eq_zero_of_cart gf π ab hp.1 _ ?_ ?_
    · rw [← pull_comp, e₀', P₀e]
    · rw [← pull_comp, ← e, pull_comp, ← clsP, ← cls_pull c.isLB _ (pull_isLB c.isLB _)]
      exact (cls_eq_zero_iff _).2 hta
  have symm : LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) := by
    have esw : eSec (G2 A₀) ≫ (lift (snd A₀ A₀) (fst A₀ A₀)).left = eSec (G2 A₀) :=
      congrArg (fun q => q.left) (eta_swap A₀)
    have swsq := lift_square sq sq.2.symm sq.1.symm
    refine (cls_eq_iff hP₀ (pull_isLB hP₀ _)).1 (sub_eq_zero.1 (eq_zero_of_cart gf π ab₂ hp₂ _ ?_ ?_))
    · rw [map_sub, cls_pull hP₀ _ (pull_isLB hP₀ _), ← pull_comp, esw, P₀e, sub_zero]
    · rw [map_sub, cls_pull hP₀ _ (pull_isLB hP₀ _), ← pull_comp, ← swsq, pull_comp, ← clsP,
        ← cls_pull c.isLB _ (pull_isLB c.isLB _), sub_eq_zero]
      exact (cls_eq_iff _ _).2 c.symm
  have diag : LBIso (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left) ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ) :=
    lbIso_square c.isLB hP₀ hw (lift_square sq idφ idφ)

  obtain ⟨ρl, hρ⟩ := exists_liftHom hp (𝟙_ _) (𝟙_ _) π
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  have ρlev : ∀ a, ρl (lev₀ a) = c.lev a := fun a => (hρ _ _).2 (hlev a)
  have ρinj : Function.Injective ρl := fun x y e =>
    Over.OverMorphism.ext ((cancel_epi π).1 (((hρ x _).1 rfl).symm.trans ((hρ y _).1 e.symm)))
  refine ⟨{ A := A₀, ab := ab, P := P₀, isLB := hP₀
            rig₁ := rig _ _ (lift_square sq one idφ) (eta_lift_one_id A₀) c.rig₁
            rig₂ := rig _ _ (lift_square sq idφ one) (eta_lift_id_one A₀) c.rig₂
            symm := symm, lev := lev₀
            lev_add := fun a b => ρinj (by rw [map_mul, ρlev, ρlev, ρlev, c.lev_add])
            lev_tors := fun a => ρinj (by rw [map_pow, ρlev, c.lev_tors, map_one])
            geom := ?_ }, φ, φ₂, hp, sq, hw, hlev⟩
  intro k _ _ x β z hx hz
  obtain ⟨y, hy⟩ := exists_lift_pt π x
  obtain ⟨g₁, g₂, g₃⟩ := c.geom k y β z (by rw [hs, ← Category.assoc, hy, hx]) hz
  obtain ⟨σ, hσ⟩ := exists_liftHom hp (Over.mk y) (Over.mk x) (𝟙 _) ((Category.id_comp _).trans hy.symm)
  have σinj : Function.Injective σ := fun u v e => Over.OverMorphism.ext (by
    simpa using ((hσ u _).1 rfl).symm.trans ((hσ v _).1 e.symm))
  have pt : ∀ a, (toUnit (Over.mk y) ≫ c.lev a).left ≫ φ = (toUnit (Over.mk x) ≫ lev₀ a).left := fun a => by
    change (y ≫ (c.lev a).left) ≫ φ = x ≫ (lev₀ a).left
    rw [Category.assoc, hlev, ← Category.assoc, hy]
  have σlev : ∀ a, σ (toUnit _ ≫ lev₀ a) = toUnit _ ≫ c.lev a := fun a =>
    (hσ _ _).2 ((pt a).trans (Category.id_comp _).symm)
  refine ⟨fun a => ?_, fun g hg => ?_, fun a b => ?_⟩
  · rw [← g₁ a, ← σlev, map_eq_one_iff σ σinj]
  · obtain ⟨a, ha⟩ := g₂ (σ g) (by rw [← map_pow, hg, map_one])
    exact ⟨a, σinj ((σlev a).trans ha)⟩
  · have hD := pull_isLB hP₀ (lift (𝟙 A₀) (𝟙 A₀)).left
    have H := (weilIs_grpPullback_of_comm _ _ A₀ c.A π φ _ _ hD (pull_isLB c.isLB _) hp diag _ _ _ _
      (pushPt hφ _) (pushPt hφ _) _ rfl rfl).1 (g₃ a b)
    exact weilIs_congr hy _ _ _ _ _ _ (pt a) (pt b) _ H

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothConeInteriorDefiniteBalancedForm
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.Cover

open Matrix

theorem isPosDef_toReal_of_pos {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {β : LinearMap.BilinForm ℤ X} (hs : ∀ y z, β y z = β z y) (hp : ∀ x, x ≠ 0 → 0 < β x x) :
    IsPosDef (toReal β) := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  let GZ : Matrix (Module.Free.ChooseBasisIndex ℤ X) (Module.Free.ChooseBasisIndex ℤ X) ℤ := fun i j => β (b i) (b j)
  let G : Matrix (Module.Free.ChooseBasisIndex ℤ X) (Module.Free.ChooseBasisIndex ℤ X) ℝ := GZ.map (Int.cast : ℤ → ℝ)
  have hval : ∀ v : Module.Free.ChooseBasisIndex ℤ X → ℤ,
      β (∑ i, v i • b i) (∑ i, v i • b i) = v ⬝ᵥ (GZ *ᵥ v) := fun v => by
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, dotProduct, mulVec, GZ,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hx : ∀ v : Module.Free.ChooseBasisIndex ℤ X → ℤ, v ≠ 0 → ∑ i, v i • b i ≠ 0 := fun v hv h0 =>
    hv (funext fun i => Fintype.linearIndependent_iff.1 b.linearIndependent v h0 i)
  have hcast : ∀ c : Module.Free.ChooseBasisIndex ℤ X → ℤ,
      (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ)) = ((c ⬝ᵥ (GZ *ᵥ c) : ℤ) : ℝ) := fun c => by
    simp [dotProduct, mulVec, G]
  have hG : G.IsHermitian := Matrix.IsHermitian.ext fun i j => by
    show star ((β (b j) (b i) : ℤ) : ℝ) = ((β (b i) (b j) : ℤ) : ℝ)
    rw [star_trivial, hs]
  have hpsd : G.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hG ?_
    intro x
    have hd : DenseRange (Pi.map (fun (_ : Module.Free.ChooseBasisIndex ℤ X) (q : ℚ) => (q : ℝ))) :=
      DenseRange.piMap (fun _ => Rat.denseRange_cast)
    rw [star_trivial]
    refine hd.induction_on (p := fun y => 0 ≤ y ⬝ᵥ (G *ᵥ y)) x ?_ ?_
    · refine isClosed_le continuous_const ?_
      simp only [dotProduct, mulVec]
      fun_prop
    · intro q
      obtain ⟨⟨d, hd0⟩, hq⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
      choose c hc using hq
      have hd1 : (d : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hd0
      have e : (fun i => (c i : ℝ)) = (d : ℝ) • Pi.map (fun (_ : Module.Free.ChooseBasisIndex ℤ X) (q : ℚ) => (q : ℝ)) q := by
        funext i
        have h1 : (c i : ℚ) = (d : ℚ) * q i := by simpa using hc i
        have h2 : ((c i : ℚ) : ℝ) = (((d : ℚ) * q i : ℚ) : ℝ) := by rw [h1]
        simpa using h2
      have h3 : (0 : ℝ) ≤ (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ)) := by
        rw [hcast]
        by_cases hc0 : c = 0
        · simp [hc0]
        · rw [← hval]; exact_mod_cast (hp _ (hx c hc0)).le
      rw [e, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
        ← mul_assoc] at h3
      exact (mul_nonneg_iff_of_pos_left (mul_self_pos.mpr hd1)).mp h3
  have hdef : ∀ c : Module.Free.ChooseBasisIndex ℤ X → ℝ, c ≠ 0 → 0 < c ⬝ᵥ (G *ᵥ c) := by
    intro c hc
    have h0 := hpsd.dotProduct_mulVec_nonneg c
    rw [star_trivial] at h0
    refine h0.lt_of_ne fun h1 => ?_
    have h2 : G *ᵥ c = 0 := by
      have := (hpsd.dotProduct_mulVec_zero_iff c).1
      rw [star_trivial] at this
      exact this h1.symm
    have h3 : G.det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨c, hc, h2⟩
    have h4 : GZ.det = 0 := by
      have : ((GZ.det : ℤ) : ℝ) = G.det := (Int.castRingHom ℝ).map_det GZ
      exact_mod_cast this.trans h3
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h4
    have := hp _ (hx v hv)
    rw [hval, hv0, dotProduct_zero] at this
    exact lt_irrefl _ this
  refine (isPosDef_iff_basis b _).2 fun c hc => (hdef c hc).trans_eq ?_
  have hGij : ∀ i j, G i j = ((β (b i) (b j) : ℤ) : ℝ) := fun _ _ => rfl
  simp only [dotProduct, mulVec, hGij, toReal_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.Poinc.Cover

namespace GlobalTheory.Poinc.Cover

theorem coeff_int {O : Type} [CommRing O] {bar : O → O} {X : Type} [AddCommGroup X] [Module O X] {m : ℕ}
    {γ : Fin m → LinearMap.BilinForm ℤ X} (hmem : ∀ i, γ i ∈ balForms bar X)
    (hb : IsPartOfBasis fun i => (⟨γ i, hmem i⟩ : balForms bar X)) {β : LinearMap.BilinForm ℤ X}
    (hβ : β ∈ balForms bar X) {c : Fin m → ℝ} (hs : toReal β = ∑ i, c i • toReal (γ i)) :
    ∃ n : Fin m → ℤ, ∀ i, c i = n i := by
  classical
  obtain ⟨k, bb, hbb⟩ := hb
  refine ⟨fun i => bb.coord (Sum.inl i) ⟨β, hβ⟩, fun i => ?_⟩
  let v : Option (Fin m) → balForms bar X := fun o => o.elim ⟨β, hβ⟩ fun i => ⟨γ i, hmem i⟩
  let w : Option (Fin m) → ℝ := fun o => o.elim (-1) c
  have h : ∑ o, w o • toReal ((balForms bar X).subtype (v o)) = 0 := by
    rw [Fintype.sum_option]
    simp only [w, v, Option.elim, Submodule.subtype_apply]
    rw [← hs]; simp
  have := sum_mul_eq_zero_of_sum_toReal (j := (balForms bar X).subtype) Subtype.val_injective
    (bb.coord (Sum.inl i)) h
  rw [Fintype.sum_option] at this
  simp only [w, v, Option.elim] at this
  have hc : ∀ i' : Fin m, bb.coord (Sum.inl i) ⟨γ i', hmem i'⟩ = if i' = i then 1 else 0 := fun i' => by
    rw [show (⟨γ i', hmem i'⟩ : balForms bar X) = bb (Sum.inl i') from (hbb i').symm, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h' : i' = i
    · simp [h']
    · simp [h', Ne.symm h']
  simp only [hc] at this
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at this
  linarith

theorem exists_cone : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFanOn bar φ X →
    ∀ β ∈ balForms bar X, (∀ x, x ≠ 0 → 0 < β x x) → ∃ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (k : ℕ)
      (c : Fin r → ℕ), IsCone bar φ γ ∧ 0 < k ∧ (∀ j, 0 < c j) ∧ k • β = ∑ j, c j • γ j := by
  intro O _ bar φ X _ _ _ _ _ _ hF β hβ hp
  classical
  have hB : toReal β ∈ psdCone bar X :=
    (isPosDef_toReal_of_pos hβ.1 hp).mem_psdCone (toReal_mem hβ)
  obtain ⟨m, γ, c, hγ, hc, hsum⟩ := hF.cover _ hB
  obtain ⟨nZ, hnZ⟩ := coeff_int hγ.mem hγ.basis hβ hsum
  have hn0 : ∀ i, 0 ≤ nZ i := fun i => by exact_mod_cast (hnZ i) ▸ hc i
  let n : Fin m → ℕ := fun i => (nZ i).toNat
  have hn : ∀ i, ((n i : ℤ) : ℝ) = c i := fun i => by simp [n, Int.toNat_of_nonneg (hn0 i), hnZ i]
  have heq : β = ∑ i, n i • γ i := LinearMap.ext₂ fun a b => by
    have h1 := LinearMap.congr_fun₂ hsum a b
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, ← hn] at h1
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul]
    exact_mod_cast h1
  let S : Finset (Fin m) := Finset.univ.filter fun i => n i ≠ 0
  let e := S.orderEmbOfFin rfl
  refine ⟨S.card, fun j => γ (e j), 1, fun j => n (e j), hF.face _ _ γ e.toEmbedding hγ, one_pos,
    fun j => Nat.pos_of_ne_zero (Finset.mem_filter.1 (S.orderEmbOfFin_mem rfl j)).2, ?_⟩
  rw [one_smul, heq]
  have h2 : ∑ i ∈ S, n i • γ i = ∑ i, n i • γ i :=
    Finset.sum_filter_of_ne fun i _ h => fun h0 => h (by rw [h0, zero_smul])
  have h3 := Finset.sum_map (Finset.univ : Finset (Fin S.card)) e.toEmbedding fun i => n i • γ i
  rw [Finset.map_orderEmbOfFin_univ S rfl] at h3
  rw [← h2, h3]
  rfl

end GlobalTheory.Poinc.Cover
end
end

