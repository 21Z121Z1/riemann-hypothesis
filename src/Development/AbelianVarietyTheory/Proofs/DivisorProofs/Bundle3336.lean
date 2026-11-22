import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3193
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3327
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2224
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2437
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3328
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2495
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParallelWeightInvertibleSection
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatUnit
open GlobalTheory.FlatLine

theorem val_sum_nonneg {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
    {la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)} {v : R → EReal} (hv : Formalism.L2.Pj.IsVal la v) {ι : Type}
    (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, 0 ≤ v (f i)) : 0 ≤ v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hv.zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (le_min (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))) (hv.add _ _)

theorem val_nsmul_nonneg {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
    {la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)} {v : R → EReal} (hv : Formalism.L2.Pj.IsVal la v) (n : ℕ) {f : R}
    (h : 0 ≤ v f) : 0 ≤ v (n • f) := by
  have := val_sum_nonneg hv (Finset.range n) (fun _ => f) (fun _ _ => h)
  simpa [Finset.sum_const, Finset.card_range] using this

theorem pnorm_sum_le {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) {ι : Type} (s : Finset ι) (P : ι → ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ)
    (y : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) : X.pnorm la (∑ i ∈ s, P i) y ≤ ∑ i ∈ s, X.pnorm la (P i) y := by
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ =>
    Real.rpow_nonneg (norm_nonneg _) _)
  rw [Finset.sum_apply]
  exact norm_sum_le _ _

theorem exists_flat_unit : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ N : ℕ, 0 < N ∧ ∀ w : GlobalTheory.AllWt.Psi T.Q.H → ℤ, ∃ (φ φ' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), φ ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) (GlobalTheory.FlatLine.parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) ∧ t ≠ 0 ∧ φ * φ' = t • 1 ∧ (∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v φ') ∧ ∀ σ, GoodEmb Y.d.c₂ σ → ∀ kk, ∃ C : ℝ, ∀ y ∈ ((Y.U σ).X kk).dom, ((Y.U σ).X kk).pnorm (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) (GlobalTheory.FlatLine.parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) kk) (rdU (Y.U σ) φ kk) y ≤ C := by
  intro hP D T j Y e o hY hE
  obtain ⟨N, hN, hA⟩ := GlobalTheory.T.exists_flat_weight_invertible_pair hP D T j Y e o hY hE
  refine ⟨N, hN, fun w => ?_⟩
  classical
  let G : Psi T.Q.H → WTZ D.host.E := fun τ => wtOf (T.Q.Dw j) ((N : ℤ) • flatWt (T.Q.Dw j) τ) 0
  let φw : GlobalTheory.AllWt.Weight (T.Q.Dw j) →+ WTZ D.host.E :=
    { toFun := fun la => wtOf (T.Q.Dw j) la 0, map_zero' := GlobalTheory.AllWt.wtOf_zero,
      map_add' := fun a b => wtOf_add' a b }
  have hsum : wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0 = ∑ τ, (-w τ) • G τ := by
    rw [parWt_eq_sum]
    show φw _ = _
    rw [map_sum]
    refine Finset.sum_congr (Finset.eq_univ_of_forall fun x => by simp) fun τ _ => ?_
    show φw _ = (-w τ) • φw _
    rw [map_zsmul, map_zsmul, smul_smul]
    congr 1; ring
  have hpair : ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) τ, ∃ s t : Rul Y.d.Xo₂ Y.d.c₂, (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (G τ)) ∧ t ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (G τ)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (G τ) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(G τ)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • t) := fun Z τ => by
    obtain ⟨s, i, h⟩ := hA Z τ
    exact ⟨s, i, h, GlobalTheory.T.flat_weight_pair_product_unit hP D T j Y e o hY hE (N : ℤ) Z τ s i h⟩
  have hZ : ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂), ∃ s t : Rul Y.d.Xo₂ Y.d.c₂, (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)) ∧ t ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • t) := fun Z => by
    obtain ⟨s, t, h⟩ := GlobalTheory.T.exists_boundedUnit_sum_component _ _ _ _ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (xiR D) Z (Psi T.Q.H) G
      (fun τ => GlobalTheory.AllWt.even_wtOf _ _) (hpair Z) (fun τ => -w τ)
    refine ⟨s, t, ?_⟩
    rw [hsum]
    exact h
  choose s t hst using hZ
  haveI := CompFin.finite_comp Y.d.Xo₂ Y.d.c₂
  haveI := Fintype.ofFinite (Comp Y.d.Xo₂ Y.d.c₂)
  choose m hm hv using fun Z => (hst Z).2
  have hsZ : ∀ Z, s Z ∈ GlobalTheory.AllWt.suppOn Z := fun Z => by
    rw [← (hst Z).1.2.2.1, mul_comm]; exact GlobalTheory.AllWt.mul_mem_suppOn _ (idem_mem_suppOn Z)
  have htZ : ∀ Z, t Z ∈ GlobalTheory.AllWt.suppOn Z := fun Z => by
    rw [← (hst Z).1.2.2.2.1, mul_comm]; exact GlobalTheory.AllWt.mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hM0 : ((∏ Z, m Z : ℕ) : Y.d.c₂.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun Z _ => (hm Z).ne')
  refine ⟨∑ Z, s Z, ((∏ Z, m Z : ℕ) : Y.d.c₂.F) • ∑ Z, t Z, ((∏ Z, m Z : ℕ) : Y.d.c₂.F),
    Submodule.sum_mem _ fun Z _ => (hst Z).1.1, hM0, ?_, ?_, ?_⟩
  · rw [mul_smul_comm, Finset.sum_mul_sum]
    have hd : ∑ Z, ∑ Z', s Z * t Z' = ∑ Z, idem Z := Finset.sum_congr rfl fun Z _ => by
      rw [Finset.sum_eq_single Z]
      · exact (hst Z).1.2.2.2.2.1
      · intro Z' _ hne
        rw [← (hst Z).1.2.2.1, ← (hst Z').1.2.2.2.1, mul_mul_mul_comm, idem_mul_idem_of_ne (Ne.symm hne),
          zero_mul]
      · intro h; exact absurd (Finset.mem_univ Z) h
    rw [hd, sum_idem]
  · intro la' v hv'
    have hV := isVal_valSet la' v hv'
    rw [Finset.smul_sum]
    refine val_sum_nonneg hV _ _ fun Z _ => ?_
    rcases mem_valOn_or (Z := Z) hv' with h | h
    · have hsplit : ((∏ Z, m Z : ℕ) : Y.d.c₂.F) • t Z =
          (∏ Z' ∈ Finset.univ.erase Z, m Z') • ((m Z : Y.d.c₂.F) • t Z) := by
        rw [← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ Z), Nat.cast_mul, mul_comm, mul_smul]
        exact Nat.cast_smul_eq_nsmul Y.d.c₂.F _ _
      rw [hsplit]
      exact val_nsmul_nonneg hV _ (hv Z la' v h).2
    · rw [h _ (Submodule.smul_mem _ _ (htZ Z))]
      exact le_top
  · intro σ hσ kk
    choose C hC using fun Z => (hst Z).1.2.2.2.2.2 σ hσ
    have hL := GlobalTheory.AllWt.lieFacZ_pos (Dw := T.Q.Dw j) (xiR D)
      (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)
    refine ⟨∑ Z, max (C Z) 0 / GlobalTheory.AllWt.lieFacZ (T.Q.Dw j) (xiR D)
      (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0), fun y hy => ?_⟩
    have e1 : rdU (Y.U σ) (∑ Z, s Z) kk = ∑ Z, rdU (Y.U σ) (s Z) kk := by
      rw [map_sum, Finset.sum_apply]
    rw [e1]
    refine (pnorm_sum_le _ _ _ _ y).trans (Finset.sum_le_sum fun Z _ => ?_)
    by_cases hz : (⟨kk, y⟩ : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((Y.U σ).X k).Ψ D.R.r) ∈ framesOn (Y.U σ) Z
    · rw [le_div_iff₀ hL]
      have h1 := (hC Z ⟨kk, y⟩ hz).1
      calc _ = GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)
            (s Z) ⟨kk, y⟩ := by unfold GlobalTheory.AllWt.homN GlobalTheory.AllWt.ptN; ring
        _ ≤ C Z := h1
        _ ≤ max (C Z) 0 := le_max_left _ _
    · have h0 : rdU (Y.U σ) (s Z) kk y = 0 := GlobalTheory.AllWt.rdU_eq_zero (Y.U σ) (hsZ Z) hz
      have : ((Y.U σ).X kk).pnorm (GlobalTheory.AllWt.modelWt (Y.U σ)
          (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) kk) (rdU (Y.U σ) (s Z) kk) y = 0 := by
        unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm; rw [h0, norm_zero, zero_mul]
      rw [this]
      exact div_nonneg (le_max_right _ _) hL.le

end GlobalTheory.FlatUnit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationSectionBasisPullbackAffine
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.SecBasisPull

open GlobalTheory.VVRank GlobalTheory.EmbPull GlobalTheory.ThetaReal

theorem eq_zero_of_smul_eq_zero (hS : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) {T : Over S}
    [IsAffine T.left] {t : LB.Sec (LPow P.A P.L 1 T)} (ht : IsGenSec P.A P.L 1 t) (r : Γ(T.left, ⊤))
    (hr : r • (SecM.ofSec P.A t : SecM P.A P.L 1 T) = 0) : r = 0 := by
  let I : Ideal Γ(T.left, ⊤) := Submodule.comap (LinearMap.toSpanSingleton Γ(T.left, ⊤) Γ(T.left, ⊤) r) ⊥
  have memI : ∀ a, a ∈ I ↔ a * r = 0 := fun a => by
    simp [I, LinearMap.toSpanSingleton_apply, smul_eq_mul]
  have key : ∀ p : T.left, ∃ g ∈ I, p ∈ T.left.basicOpen g := fun p => by
    obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl (T.hom p)
    haveI hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
    obtain ⟨g, hg, hp⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := T.hom ⁻¹ᵁ V) ⟨p, hV⟩ trivial
    let W := T.left.basicOpen g
    let l : overRes W ⟶ overRes (T := baseOver S) V := Over.homMk
      (IsOpenImmersion.lift V.ι (W.ι ≫ T.hom) (by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        exact hg y.2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
    have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen g
    haveI : IsAffine (overRes W).left := hW
    obtain ⟨c, -⟩ := exists_basis P 1 b hb (overRes W) l
    let σ := (overResι W).left.appTop.hom
    let k₀ : Fin (1 ^ P.g) := @default _ hq.toInhabited
    obtain ⟨n, u, hu⟩ := exists_pow_extend_secM P 1 g (c k₀)
    obtain ⟨e, he⟩ := ht (SecM.toSec P.A u)
    have hue : u = e • SecM.ofSec P.A t := Subtype.ext (funext he)
    obtain ⟨d, hd⟩ : ∃ d, pullM P.A P.L 1 (overResι W) (SecM.ofSec P.A t) = d • c k₀ := by
      have := c.sum_repr (pullM P.A P.L 1 (overResι W) (SecM.ofSec P.A t))
      rw [Fintype.sum_unique] at this
      exact ⟨_, this.symm⟩
    have coef : ∀ x y : Γ((overRes W).left, ⊤), x • c k₀ = y • c k₀ → x = y := fun x y h => by
      have := congrArg (fun v => c.repr v k₀) h
      simp only [LinearEquiv.map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
        smul_eq_mul, _root_.mul_one] at this
      exact this
    have e1 : σ (g ^ n) = σ e * d := coef _ _ (by
      rw [← hu, hue, LinearMap.map_smulₛₗ, hd, smul_smul])
    have e2 : σ r * d = 0 := coef _ _ (by
      rw [← smul_smul, ← hd, ← LinearMap.map_smulₛₗ, hr, map_zero, zero_smul])
    have e3 : σ (r * g ^ n) = 0 := by rw [map_mul, e1, mul_left_comm, e2, mul_zero]
    have e4 := (congrArg (fun q => q.hom (r * g ^ n)) (Scheme.Opens.ι_appTop W)).symm.trans e3
    obtain ⟨m, hm⟩ := GlobalTheory.AffineThickening.exists_pow_mul_eq_zero (isAffineOpen_top T.left) _ g (r * g ^ n)
      (Scheme.Opens.ι_image_top W) e4
    refine ⟨g ^ (m + n), (memI _).2 (by rw [pow_add, _root_.mul_assoc, mul_comm (g ^ n), hm]), ?_⟩
    rw [Scheme.mem_basicOpen_top] at hp ⊢
    rw [map_pow]
    exact hp.pow _
  have hI : Ideal.span (I : Set Γ(T.left, ⊤)) = ⊤ :=
    (isAffineOpen_top T.left).self_le_iSup_basicOpen_iff.1 fun p _ => by
      obtain ⟨g, hg, hp⟩ := key p
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨g, hg⟩, hp⟩
  rw [Ideal.span_eq, Ideal.eq_top_iff_one] at hI
  simpa using (memI 1).1 hI

theorem univBasis_of_isGenSec (hS : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) {T : Over S} [IsAffine T.left]
    {th : LB.Sec (LPow P.A P.L 1 T)} (hth : IsGenSec P.A P.L 1 th) :
    UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th) := by
  intro T' _ h
  have hg := isGenSec_pullS P hS h hth
  let t' : SecM P.A P.L 1 T' := SecM.ofSec P.A (pullS P.A 1 h th)
  let l := LinearMap.toSpanSingleton Γ(T'.left, ⊤) (SecM P.A P.L 1 T') t'
  have inj : Function.Injective l := (injective_iff_map_eq_zero l).2 fun r hr =>
    eq_zero_of_smul_eq_zero hS P hg r (by simpa only [l, LinearMap.toSpanSingleton_apply] using hr)
  have surj : Function.Surjective l := fun s => by
    obtain ⟨r, hr⟩ := hg (SecM.toSec P.A s)
    exact ⟨r, Subtype.ext (funext fun j => (hr j).symm)⟩
  let E := LinearEquiv.ofBijective l ⟨inj, surj⟩
  refine ⟨(Module.Basis.singleton (Fin 1) Γ(T'.left, ⊤)).map E, fun i => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.singleton_apply]
  show l 1 = _
  rw [LinearMap.toSpanSingleton_apply, one_smul]
  rfl

end GlobalTheory.SecBasisPull
end

open GlobalTheory.SecBasisPull GlobalTheory.ThetaReal in

theorem GlobalTheory.SecBasisPull.exists_secBasis_pull : ∀ {R R' : Type} [CommRing R] [CommRing R'] (P : PolAV (Sp R)) (P' : PolAV (Sp R')) (f : R →+* R') (ψ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A (spMap f) ψ → LBIso P'.L (P.L.pull ψ) → ∀ th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R))), IsSecBasis _ (fun _ : Fin 1 => th) → ∃ th' : LB.Sec (LPow P'.A P'.L 1 (baseOver (Sp R'))), IsSecBasis _ (fun _ : Fin 1 => th') := by
  intro R R' _ _ P P' f ψ hp hw th hth
  obtain ⟨-, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  haveI : IsAffine (baseOver (Sp R)).left := inferInstanceAs (IsAffine (Sp R))
  haveI : IsAffine (baseOver (Sp R')).left := inferInstanceAs (IsAffine (Sp R'))
  have hgen : IsGenSec P.A P.L 1 th := fun s => by
    obtain ⟨r, hr, -⟩ := hth s
    exact ⟨r 0, fun j => (hr j).trans (Fin.sum_univ_one _)⟩
  have hU := univBasis_of_isGenSec hL₂.secBaseChangeAny P hgen
  obtain ⟨b, hb⟩ := GlobalTheory.UnivBasisMove.univBasis_move _ _ (spMap f) P P' ψ hp hw 1 (Fin 1) (baseOver (Sp R)) (spMap f)
    (Category.comp_id _) _ hU
  obtain ⟨c, -⟩ := hb.exists_basis
  refine ⟨SecM.toSec P'.A (c 0), fun s => ?_⟩
  have e : ∀ i : Fin 1, c i = c 0 := fun i => congrArg c (Subsingleton.elim _ _)
  have := existsUnique_of_basis c s
  simp only [e] at this
  exact this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedExtensionOfSeriesPair
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

noncomputable section

namespace GlobalTheory.Katz

theorem exists_rigMap (p : ℕ) (k : Type) [Field k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d) :
    ∃ ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] G.RigExt,
      (∀ s w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n s) →
        (∀ n, u.1 n = ∑ i, w i • dUnit k (c.x n i)) → ρ (s, w) = G.rigMk (z, u)) := by
  classical
  let L : MvPowerSeries (Fin d ⊕ Fin d) k →ₗ[k] (∀ n, G.A n ⊗[k] G.A n) :=
    LinearMap.pi fun n => (c.ev₂ n).toLinearMap
  let S : Submodule k (MvPowerSeries (Fin d ⊕ Fin d) k) := G.cocycles.comap L
  let T₀ : S →ₗ[k] G.cocycles := L.restrict (fun x hx => hx)
  obtain ⟨T, hT⟩ := LinearMap.exists_extend T₀
  have hU := (GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates p k d G c).1
  let U : (Fin d → k) →ₗ[k] G.omega :=
    { toFun := fun w => ⟨fun n => ∑ i, w i • dUnit k (c.x n i), hU w⟩
      map_add' := fun a b => Subtype.ext (funext fun n => by
        simp [add_smul, Finset.sum_add_distrib])
      map_smul' := fun r a => Subtype.ext (funext fun n => by
        simp [Finset.smul_sum, smul_smul]) }
  refine ⟨G.rigMk ∘ₗ T.prodMap U, fun s w z u hz hu => ?_⟩
  have hs : s ∈ S := by
    change L s ∈ G.cocycles
    have : L s = z.1 := funext fun n => (hz n).symm
    rw [this]; exact z.2
  have h1 : T s = z := by
    have := LinearMap.congr_fun hT ⟨s, hs⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this]
    exact Subtype.ext (funext fun n => (hz n).symm)
  have h2 : U w = u := Subtype.ext (funext fun n => (hu n).symm)
  simp [h1, h2]

end GlobalTheory.Katz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaRealisationLabelPermOfRingEndo
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
open Classical

namespace GlobalTheory.Poinc

theorem labelHom_of_comp_eq : ∀ {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₁ : ThetaSys o₁ Ω₁) (S₂ : ThetaSys o₂ Ω₂) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (om : S₁.R →+* S₂.R) (φ : ρ₂.P.A.left ⟶ ρ₁.P.A.left), IsGrpPullback ρ₂.P.A ρ₁.P.A (spMap om) φ → ∀ τ : S₂.R →+* S₂.R, τ.comp om = om → ∃ gl : S₂.Gam →+ S₂.Gam, ∀ a, (ρ₂.pt (gl a)).left ≫ φ = spMap τ ≫ (ρ₂.pt a).left ≫ φ := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ S₁ S₂ ρ₁ ρ₂ om φ hφ τ hτ
  have hsp : spMap τ ≫ spMap om = spMap om := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    conv_rhs => rw [← hτ]
    rfl
  let B := baseOver (Sp S₂.R)
  let push : (B ⟶ ρ₂.P.A) → (Over.mk (B.hom ≫ spMap om) ⟶ ρ₁.P.A) := fun x =>
    Over.homMk (x.left ≫ φ) (by rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w x]; rfl)
  have push_mul : ∀ x y, push (x * y) = push x * push y := fun x y =>
    Over.OverMorphism.ext (hφ.2 B x y (push x) (push y) rfl rfl).symm
  have push_inj : ∀ x y, push x = push y → x = y := fun x y e =>
    Over.OverMorphism.ext (hφ.1.hom_ext (congrArg (fun z => z.left) e) (by rw [Over.w x, Over.w y]))
  let V : Over.mk (B.hom ≫ spMap om) ⟶ Over.mk (B.hom ≫ spMap om) :=
    Over.homMk (spMap τ) (by show spMap τ ≫ 𝟙 _ ≫ spMap om = 𝟙 _ ≫ spMap om; rw [Category.id_comp, hsp])
  have wa : ∀ a, (spMap τ ≫ (ρ₂.pt a).left ≫ φ) ≫ ρ₁.P.A.hom = 𝟙 _ ≫ spMap om := fun a => by
    rw [Category.assoc, Category.assoc, hφ.1.w, ← Category.assoc (ρ₂.pt a).left, Over.w (ρ₂.pt a)]
    show spMap τ ≫ 𝟙 _ ≫ spMap om = _
    simp only [Category.id_comp]; exact hsp
  let s : S₂.Gam → (B ⟶ ρ₂.P.A) := fun a =>
    Over.homMk (hφ.1.lift (spMap τ ≫ (ρ₂.pt a).left ≫ φ) (𝟙 _) (wa a)) (hφ.1.lift_snd _ _ _)
  have hs : ∀ a, (s a).left ≫ φ = spMap τ ≫ (ρ₂.pt a).left ≫ φ := fun a => hφ.1.lift_fst _ _ _
  have push_s : ∀ a, push (s a) = V ≫ push (ρ₂.pt a) := fun a => Over.OverMorphism.ext (hs a)
  have s_add : ∀ a b, s (a + b) = s a * s b := fun a b => push_inj _ _ (by
    rw [push_s, ρ₂.pt_add, push_mul, MonObj.comp_mul, push_mul, push_s, push_s])
  let sH : Multiplicative S₂.Gam →* (B ⟶ ρ₂.P.A) := MonoidHom.mk' (fun a => s a.toAdd) (fun a b => s_add _ _)
  let ptH : Multiplicative S₂.Gam →* (B ⟶ ρ₂.P.A) := MonoidHom.mk' (fun a => ρ₂.pt a.toAdd) (fun a b => ρ₂.pt_add _ _)
  have hn : ∀ a : S₂.Gam, (S₂.r * S₂.N) • a = 0 := fun a => funext fun i => by
    rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]; rfl
  have tors : ∀ (F : Multiplicative S₂.Gam →* (B ⟶ ρ₂.P.A)) (a : S₂.Gam),
      F (Multiplicative.ofAdd a) ^ (S₂.r * S₂.N) = 1 := fun F a => by
    rw [← map_pow, ← ofAdd_nsmul, hn, ofAdd_zero, map_one]
  have ex : ∀ a, ∃ b, ρ₂.pt b = s a := fun a =>
    GlobalTheory.torsionSection_eq_labelled_of_isDomain S₂.R ρ₂.P (S₂.r * S₂.N) S₂.Gam ρ₂.pt
      (fun K _ _ x z hz => (ρ₂.pt_bij K x z hz).exists) (s a) (tors sH a)
  let K := AlgebraicClosure Ω₂
  let j : S₂.R →+* K := (algebraMap Ω₂ K).comp S₂.R.val.toRingHom
  have inj : ∀ b b', ρ₂.pt b = ρ₂.pt b' → b = b' := by
    intro b b' e
    obtain ⟨c, -, hc⟩ := ρ₂.pt_bij K (spMap j)
      ((Over.homMk (spMap j) (by simp) : Over.mk (spMap j) ⟶ baseOver (Sp S₂.R)) ≫ ρ₂.pt b)
      (by rw [← MonObj.comp_pow, show ρ₂.pt b ^ (S₂.r * S₂.N) = 1 from tors ptH b, MonObj.comp_one])
    exact (hc b rfl).trans (hc b' (by rw [e])).symm
  refine ⟨AddMonoidHom.mk' (fun a => Classical.choose (ex a)) (fun a b => inj _ _ ?_), fun a => ?_⟩
  · rw [ρ₂.pt_add, Classical.choose_spec (ex (a + b)), Classical.choose_spec (ex a), Classical.choose_spec (ex b),
      s_add]
  · show (ρ₂.pt (Classical.choose (ex a))).left ≫ φ = _
    rw [Classical.choose_spec (ex a)]
    exact hs a

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaRealisationLabelsOfGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.PullLab

open GlobalTheory.Poinc.DeepLab

theorem exists_lab_of_isGrpPullback : ∀ {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₁ : ThetaSys o₁ Ω₁) (S₂ : ThetaSys o₂ Ω₂) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (om : S₁.R →+* S₂.R) (φ : ρ₂.P.A.left ⟶ ρ₁.P.A.left) (d : ℕ), IsGrpPullback ρ₂.P.A ρ₁.P.A (spMap om) φ → S₂.r * S₂.N = S₁.r * S₁.N * d → ∃ lam : S₁.Gam →+ S₂.Gam, (∀ a, (ρ₂.pt (lam a)).left ≫ φ = spMap om ≫ (ρ₁.pt a).left) ∧ ∀ a', ∃ a, lam a = d • a' := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ S₁ S₂ ρ₁ ρ₂ om φ d hpb hd
  let K := AlgebraicClosure Ω₂
  let x₀ : Sp K ⟶ Sp S₂.R := spMap (algebraMap Ω₂ K) ≫ spMap S₂.R.val.toRingHom
  let U : Over.mk ((baseOver (Sp S₂.R)).hom ≫ spMap om) ⟶ baseOver (Sp S₁.R) := Over.homMk (spMap om) (by simp)
  let V₂ : Over.mk x₀ ⟶ baseOver (Sp S₂.R) := Over.homMk x₀ (by simp)
  let p₁ : Multiplicative S₁.Gam →* (baseOver (Sp S₁.R) ⟶ ρ₁.P.A) :=
    MonoidHom.mk' (fun a => ρ₁.pt (Multiplicative.toAdd a)) fun a b => ρ₁.pt_add _ _
  let p₂ : Multiplicative S₂.Gam →* (baseOver (Sp S₂.R) ⟶ ρ₂.P.A) :=
    MonoidHom.mk' (fun a => ρ₂.pt (Multiplicative.toAdd a)) fun a b => ρ₂.pt_add _ _
  have hbij : Function.Bijective (pushHom hpb (baseOver (Sp S₂.R))) :=
    ⟨pushHom_injective hpb _, pushHom_surjective hpb _⟩
  let e := MulEquiv.ofBijective (pushHom hpb (baseOver (Sp S₂.R))) hbij
  let σ : Multiplicative S₁.Gam →* (baseOver (Sp S₂.R) ⟶ ρ₂.P.A) := e.symm.toMonoidHom.comp ((preHom U).comp p₁)
  have hσ : ∀ a, pushHom hpb _ (σ a) = U ≫ ρ₁.pt (Multiplicative.toAdd a) := fun a =>
    e.apply_symm_apply (U ≫ ρ₁.pt (Multiplicative.toAdd a))
  have hσl : ∀ a, (σ a).left ≫ φ = spMap om ≫ (ρ₁.pt (Multiplicative.toAdd a)).left := fun a =>
    congrArg (fun q => q.left) (hσ a)
  have hσL : ∀ a : S₁.Gam, σ (Multiplicative.ofAdd a) ^ (S₂.r * S₂.N) = 1 := by
    intro a
    rw [hd, pow_mul, map_pow_self, one_pow]
  have uniq : ∀ z : baseOver (Sp S₂.R) ⟶ ρ₂.P.A, z ^ (S₂.r * S₂.N) = 1 →
      ∃! b : S₂.Gam, p₂ (Multiplicative.ofAdd b) = z := by
    intro z hz
    obtain ⟨b, hb⟩ := GlobalTheory.torsionSection_eq_labelled_of_isDomain S₂.R ρ₂.P (S₂.r * S₂.N) S₂.Gam ρ₂.pt
      (fun K _ _ x z hz => (ρ₂.pt_bij K x z hz).exists) z hz
    refine ⟨b, hb, fun b' hb' => ?_⟩
    have h2 : (V₂ ≫ z) ^ (S₂.r * S₂.N) = 1 := by
      have h3 := congrArg (preHom V₂) hz
      rwa [map_pow, map_one] at h3
    exact (ρ₂.pt_bij K x₀ (V₂ ≫ z) h2).unique (congrArg (V₂ ≫ ·) hb') (congrArg (V₂ ≫ ·) hb)
  obtain ⟨lam, hlam⟩ := exists_lab _ p₂ σ uniq hσL
  have hpt : ∀ a, (ρ₂.pt (lam a)).left ≫ φ = spMap om ≫ (ρ₁.pt a).left := fun a => by
    have h4 := hσl (Multiplicative.ofAdd a)
    rw [← hlam a] at h4
    exact h4
  refine ⟨lam, hpt, fun a' => ?_⟩
  set y := d • a' with hy
  have hyL : p₂ (Multiplicative.ofAdd y) ^ (S₁.r * S₁.N) = 1 := by
    rw [← map_pow, ← ofAdd_nsmul, hy, smul_smul, ← hd, nsmul_self_eq_zero, ofAdd_zero, map_one]
  let T₀ : Over (Sp S₂.R) := Over.mk x₀
  let V₁ : Over.mk (x₀ ≫ spMap om) ⟶ baseOver (Sp S₁.R) := Over.homMk (x₀ ≫ spMap om) (by simp)
  let z₁ : Over.mk (x₀ ≫ spMap om) ⟶ ρ₁.P.A := pushHom hpb T₀ (V₂ ≫ ρ₂.pt y)
  have hz₁ : z₁ ^ (S₁.r * S₁.N) = 1 := by
    have h0 : (V₂ ≫ ρ₂.pt y) ^ (S₁.r * S₁.N) = 1 := by
      have h3 := congrArg (preHom V₂) hyL
      rwa [map_pow, map_one] at h3
    show (pushHom hpb T₀) _ ^ _ = 1
    rw [← map_pow, h0, map_one]
  obtain ⟨a, ha, -⟩ := ρ₁.pt_bij K (x₀ ≫ spMap om) z₁ hz₁
  refine ⟨a, ?_⟩
  have hpush : pushHom hpb T₀ (V₂ ≫ ρ₂.pt (lam a)) = V₁ ≫ ρ₁.pt a := by
    apply Over.OverMorphism.ext
    show (V₂ ≫ ρ₂.pt (lam a)).left ≫ φ = (V₁ ≫ ρ₁.pt a).left
    simp only [Over.comp_left, Category.assoc, V₂, V₁, Over.homMk_left]
    rw [hpt]
  have h1 : V₂ ≫ ρ₂.pt (lam a) = V₂ ≫ ρ₂.pt y := pushHom_injective hpb T₀ (hpush.trans ha)
  have h2 : (V₂ ≫ ρ₂.pt y) ^ (S₂.r * S₂.N) = 1 := by
    have h3 := congrArg (preHom V₂) (map_pow_self _ p₂ y)
    rwa [map_pow, map_one] at h3
  exact (ρ₂.pt_bij K x₀ _ h2).unique h1 rfl

end GlobalTheory.Poinc.PullLab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHopfAlgebraEqRangeMulKernelStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_hopfAlgebra_eq_range_mul_kernel : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A] [IsCocomm k A] [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (f : C →ₐc[k] A), Module.finrank k A = Module.finrank k (LinearMap.range (f : C →ₐ[k] A).toLinearMap) * Module.finrank k (A ⧸ kerIdeal f) := by
  first | exact @GlobalTheory.Dieu.finrank_eq_range_mul_ker | exact GlobalTheory.Dieu.finrank_eq_range_mul_ker | (intros; apply GlobalTheory.Dieu.finrank_eq_range_mul_ker <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotKernelIdealEqBeyondExponentStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_quot_kernelIdeal_eq_beyond_exponent : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G Q : PDivGroup p k) (m n : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G), q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G → m ≤ n → Module.finrank k (G.A n ⧸ kerIdeal (q.app n)) = Module.finrank k (G.A m ⧸ kerIdeal (q.app m)) := by
  first | exact @GlobalTheory.Dieu.finrank_quot_kerIdeal_eq | exact GlobalTheory.Dieu.finrank_quot_kerIdeal_eq | (intros; apply GlobalTheory.Dieu.finrank_quot_kerIdeal_eq <;> assumption)
end

