import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2154
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsProductCuspFormNeZeroArchSupNormBounds
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0008
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0041
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0102
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1595
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2235
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2444
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2488
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2401

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroScalarWeightCuspFormComponent
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.ScalarCusp

theorem bdd_of_definite {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (hp : X.p0 = 0 ∨ X.p0 = r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) :
    ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C := by
  obtain ⟨R, hR⟩ := GlobalTheory.orthonormal_frames_bounded_of_definite r X hp
  let K : Set (Frame X.Ψ r) := {x | X.IsOrtho x}
  have hKd : K ⊆ X.dom := fun x hx => PIW.FdPA.orthonormal_domain r X x hx
  have hKc : IsClosed K := by
    have e : K = ⋂ τ : X.Ψ, {x : Frame X.Ψ r | gram τ.1 X.Gm (mat x τ) =
        Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)} := by
      ext x; simp [K, Data.IsOrtho]
    rw [e]
    refine isClosed_iInter fun τ => isClosed_eq ?_ continuous_const
    unfold gram hermC col mat
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.of_apply]
    fun_prop
  have hKb : Bornology.IsBounded K := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨max R 0, fun x hx => ?_⟩
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun τ => ?_
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun a => ?_
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun b => ?_
    exact (hR x hx τ a b).trans (le_max_left _ _)
  obtain ⟨C, hC⟩ := (Metric.isCompact_of_isClosed_isBounded hKc hKb).exists_bound_of_continuousOn
    (hP.1.continuousOn.mono hKd)
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨b, hb, ho⟩ := (orthonormalFlagTranslate_holds r X).1 x hx
  rw [← (orthonormalFlagTranslate_holds r X).2.1 la P hP.2.1 x hx b hb,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit X la P (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho X ho)]
  exact hC _ ho

end GlobalTheory.ScalarCusp

namespace GlobalTheory.ScalarCusp

theorem exists_scalar_cusp_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (Z : Comp Xo c), ∃ n₀ : ℕ, 0 < n₀ ∧ Even n₀ ∧ ∃ f₀ ∈ cusp Xo c U 0 n₀, ∃ z ∈ framesOn (U σ) Z, rdU (U σ) f₀ z.1 z.2 ≠ 0 := by
  intro E _ _ _ H Dw l Xo c r U x hL σ hσ Z
  have hU := hL.unf σ hσ
  have hr : r = Dw.p + Dw.q := hU.1
  obtain ⟨k, hk⟩ := GlobalTheory.FlatCore.framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ
  by_cases hdef : Dw.p = 0 ∨ Dw.q = 0
  · obtain ⟨z, hz⟩ := GlobalTheory.FlatLine.framesOn_nonempty hU Z
    have hz' : z.1 = k ∧ z.2 ∈ ((U σ).X z.1).dom := by rw [hk] at hz; exact hz
    obtain ⟨n, hn, he, f, hf, hne⟩ :=
      GlobalTheory.Reg.exists_even_sec_evR_ne_zero E H Dw l Xo c σ ((U σ).un z.1 ⟨z.2, hz'.2⟩)
    have hD : Dom (0 : (E →+* ℂ) × ℕ → ℕ) n := ⟨fun τ i i' _ => le_rfl, he⟩
    refine ⟨n, hn, he, f, ?_, z, hz, ?_⟩
    · rw [mem_cusp]
      refine ⟨hf, fun σ' hσ' => holCusp_mem_holSub _ _ fun j => ?_⟩
      have hU' := hL.unf σ' hσ'
      have hs := hU'.2.2.2.2.1 0 n hD f hf j
      obtain ⟨τ0⟩ : Nonempty ((U σ').X j).Ψ := by
        obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
        by_cases h : τ ∈ ((U σ').X j).Ψ
        · exact ⟨⟨τ, h⟩⟩
        · exact ⟨⟨_, not_not.mp (fun h' => h ((((U σ').X j).cmType τ).mpr h'))⟩⟩
      have hp0 : ((U σ').X j).p0 = 0 ∨ ((U σ').X j).p0 = r := by
        rw [(hU'.2.1 j).1]; omega
      exact GlobalTheory.BoundedCusp.mem_SS_of_definite _ _ τ0 hp0 _ ⟨hs, bdd_of_definite _ hp0 _ _ hs⟩
    · have e : rdU (U σ) f z.1 z.2 = toC (evR Xo c f ((U σ).un z.1 ⟨z.2, hz'.2⟩)) := dif_pos hz'.2
      rw [e]
      exact hne
  · push_neg at hdef
    have hp : 1 ≤ Dw.p := Nat.one_le_iff_ne_zero.2 hdef.1
    have hq : 1 ≤ Dw.q := Nat.one_le_iff_ne_zero.2 hdef.2
    by_cases hrun : ∃ m : ℕ, 1 ≤ m ∧ m ^ 4 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E ∧ (ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 2 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧ 16 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧ (Dw.p ≤ m ∨ Dw.q ≤ m)
    · obtain ⟨m, hm1, hm4, hf2, hrd, hpm⟩ := hrun
      have hr2 : 2 ≤ r := by omega
      have hf1 : 1 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E := le_trans (Nat.one_le_pow _ _ hm1) hm4
      have hfr : 2 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r := by nlinarith
      obtain ⟨q', R0, -, -, hrunOK⟩ := GlobalTheory.RunParametersBound.exists_run_bound E r m hfr hm1 hm4 hf2 hrd
      have hT : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c
      obtain ⟨i, J, _, cf, xs, f, hi, -, -, -, hf, -, hnz, -⟩ :=
        GlobalTheory.EtaAn.exists_etaRule_cusp_ne_zero_bounds E H Dw l Xo c r (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) σ
          (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 (hL.unf σ hσ)) hσ hT hr2 5 (by decide)
          (by norm_num) 1 q' m R0 hrunOK hpm
      obtain ⟨y, hy, hne⟩ := hnz k
      have hf' : f ∈ cusp Xo c U 0 (2 * 5 ^ 4 * r * i) := hf
      refine ⟨2 * 5 ^ 4 * r * i, by positivity, ⟨5 ^ 4 * r * i, by ring⟩, f, hf', ⟨k, y⟩, ?_, hne⟩
      rw [hk]
      exact ⟨rfl, hy⟩
    · exact GlobalTheory.T.exists_scalar_cuspForm_indefinite_unitaryShimura E H Dw l Xo c r U x hL hp hq hrun σ hσ Z

end GlobalTheory.ScalarCusp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionOfFiniteFreeBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FlatGenDescent

variable {X X' : Scheme.{0}}

theorem isUnit_gs_iff {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (h : f z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs f z U a) ↔ f z ∈ X.basicOpen a := by
  rw [gs_eq f z U h, ← Scheme.mem_basicOpen Z _ z h, ← Scheme.preimage_basicOpen]
  rfl

theorem exists_mul {M : LB X} (hM : M.IsLB) (u : LB.Sec M) (v : LB.Sec (AbLaw.pw M (-1))) :
    ∃ a : Γ(X, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (k : M.ι), r z ∈ M.U k →
      gs r z ⊤ a = gs r z (M.U k) (u.f k) * gs r z (M.U k) (v.f k) := by
  obtain ⟨a, ha, -⟩ := X.sheaf.existsUnique_gluing' M.U ⊤ (fun k => homOfLE le_top) hM.cover.ge
    (fun k => (show Γ(X, M.U k) from u.f k) * (show Γ(X, M.U k) from v.f k))
    (fun k l => fn_ext (V := M.U k ⊓ M.U l) fun y hy => by
      refine (gs_res (𝟙 X) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X) y inf_le_right hy _).symm)
      refine (gs_mul (𝟙 X) y _ hy.1 _ _).trans (Eq.trans ?_ (gs_mul (𝟙 X) y _ hy.2 _ _).symm)
      have h₁ := FlatSec.gs_sec_trans u (𝟙 X) y hy.1 hy.2
      have h₂ : gs (𝟙 X) y (M.U k) (v.f k) = (gm (𝟙 X) y (M.U k ⊓ M.U l) (M.g k l ^ (-1 : ℤ))).val *
          gs (𝟙 X) y (M.U l) (v.f l) := FlatSec.gs_sec_trans v (𝟙 X) y (k := k) (l := l) hy.1 hy.2
      rw [h₁, h₂, map_zpow, zpow_neg_one, _root_.mul_mul_mul_comm, Units.mul_inv, _root_.one_mul])
  refine ⟨a, fun Z r z k hk => ?_⟩
  exact (gs_res r z le_top hk a).symm.trans ((congrArg (gs r z (M.U k)) (ha k)).trans (gs_mul r z _ hk _ _))

def invSec (M : LB X) (π : X' ⟶ X) (t : LB.Gen (M.pull π)) (ht : t.IsGen) : LB.Sec ((AbLaw.pw M (-1)).pull π) :=
  genSec (M := (AbLaw.pw M (-1)).pull π) ⟨fun j => (t.s j)⁻¹⟩ fun i j => by
    have h := congrArg (·⁻¹) (ht i j)
    simp only [mul_inv, ← map_inv] at h
    refine h.trans (congrArg₂ (· * ·) ?_ rfl)
    show (∏ _k : PUnit, (res _ (pullU π _ (M.g _ _))) ^ (1 : ℤ))⁻¹ =
      ∏ _k : PUnit, (res _ (pullU π _ (M.g _ _ ^ (-1 : ℤ)))) ^ (1 : ℤ)
    rw [Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, map_zpow, map_zpow, zpow_neg_one]

theorem exists_sec_of_flat {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (hg : g.Flat) [CompactSpace X]
    [QuasiSeparatedSpace X] (f : X ⟶ Sp R) (π : X' ⟶ X) (f' : X' ⟶ Sp R') (H : IsPullback π f' f (spMap g))
    (M : LB X) (hM : M.IsLB) (t : LB.Gen (M.pull π)) (ht : t.IsGen) (m : Ideal Γ(X, ⊤)) (hm : m.IsMaximal) :
    ∃ u : LB.Sec M, ∀ z : X', (∀ a ∈ m, π z ∉ X.basicOpen a) → π z ∈ nonzeroLocus u := by
  classical
  obtain ⟨n, c, u, hu⟩ := FlatSec.exists_comb_of_flat R R' g hg X f X' π f' H M hM (genSec t ht)
  obtain ⟨n', c', v, hv⟩ := FlatSec.exists_comb_of_flat R R' g hg X f X' π f' H _ (AbLaw.isLB_pw hM (-1))
    (invSec M π t ht)
  choose a ha using fun i j => exists_mul hM (u i) (v j)
  by_cases hne : ∃ i j, a i j ∉ m
  · obtain ⟨i, j, hij⟩ := hne
    refine ⟨u i, fun z hz => ?_⟩
    obtain ⟨k, hk⟩ := exists_chart hM (π z)
    obtain ⟨y, x, hx, e⟩ := hm.exists_inv hij
    have e' := congrArg (gs π z ⊤) e
    rw [gs_add π z ⊤ trivial, gs_mul π z ⊤ trivial, gs_eq π z ⊤ trivial 1, map_one, map_one] at e'
    have hxu : ¬ IsUnit (gs π z ⊤ x) := fun h => hz x hx ((isUnit_gs_iff π z ⊤ trivial x).1 h)
    have hu1 : IsUnit (gs π z ⊤ y * gs π z ⊤ (a i j)) :=
      (IsLocalRing.isUnit_or_isUnit_of_add_one e').resolve_right hxu
    have hu2 := isUnit_of_mul_isUnit_right hu1
    rw [ha i j X' π z k hk] at hu2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, (isUnit_gs_iff π z _ hk _).1 (isUnit_of_mul_isUnit_left hu2)⟩
  · push_neg at hne
    refine ⟨⟨fun _ => 0, fun _ _ => by simp⟩, fun z hz => False.elim ?_⟩
    obtain ⟨k, hk⟩ := exists_chart hM (π z)
    have hz' : z ∈ (M.pull π).U (fun _ => k) := mem_pull.2 hk
    have h₁ : (gm (𝟙 X') z ((M.pull π).U (fun _ => k)) (t.s fun _ => k)).val = _ :=
      (gs_unit (𝟙 X') z _ hz' _).symm.trans (hu z k hk)
    have h₂ : (gm (𝟙 X') z ((M.pull π).U (fun _ => k)) (t.s fun _ => k)⁻¹).val = _ :=
      (gs_unit (𝟙 X') z _ hz' _).symm.trans (hv z k hk)
    have h₃ := congrArg₂ (· * ·) h₁ h₂
    rw [map_inv, Units.mul_inv, Finset.sum_mul_sum] at h₃
    apply (IsLocalRing.maximalIdeal.isMaximal (X'.presheaf.stalk z)).ne_top
    rw [Ideal.eq_top_iff_one, h₃]
    refine Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun j _ => ?_
    rw [_root_.mul_mul_mul_comm]
    refine Ideal.mul_mem_left _ _ ?_
    have h₄ : ¬ IsUnit (gs π z ⊤ (a i j)) := fun h => hz _ (hne i j) ((isUnit_gs_iff π z ⊤ trivial _).1 h)
    rw [ha i j X' π z k hk] at h₄
    exact h₄

theorem flat_of_basis {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (d : ℕ) (b : Fin d → R')
    (h : ∀ r' : R', ∃! c : Fin d → R, r' = ∑ l, g (c l) * b l) : g.Flat := by
  let _ : Algebra R R' := g.toAlgebra
  have hb : Function.Bijective (Fintype.linearCombination R b) := by
    rw [Function.bijective_iff_existsUnique]
    intro r'
    refine (existsUnique_congr fun c => ?_).1 (h r')
    rw [Fintype.linearCombination_apply, eq_comm]
    rfl
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective _ hb).symm

theorem exists_sec_of_free : ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (d : ℕ) (b : Fin d → R'), (∀ r' : R', ∃! c : Fin d → R, r' = ∑ l, g (c l) * b l) → ∀ (Z Z' : Scheme.{0}) (k' : Z' ⟶ Z) (f : Z ⟶ Sp R) (f' : Z' ⟶ Sp R'), IsPullback k' f' f (spMap g) → ∀ (O : Z.Opens), IsCompact (O : Set Z) → IsQuasiSeparated (O : Set Z) → ∀ (L : LB Z), L.IsLB → ∀ σ : LB.Gen ((L.pull k').pull (k' ⁻¹ᵁ O).ι), σ.IsGen → ∀ m : Ideal Γ(Z, O), m.IsMaximal → ∃ u : LB.Sec (L.pull O.ι), ∀ z : (k' ⁻¹ᵁ O).toScheme, (∀ a ∈ m, k' ((k' ⁻¹ᵁ O).ι z) ∉ Z.basicOpen a) → ∀ z₀ : O.toScheme, O.ι z₀ = k' ((k' ⁻¹ᵁ O).ι z) → z₀ ∈ nonzeroLocus u := by
  intro R R' _ _ g d b hb Z Z' k' f f' H O hO hO' L hL σ hσ m hm
  haveI : CompactSpace O.toScheme := isCompact_iff_compactSpace.mp hO
  haveI : QuasiSeparatedSpace O.toScheme := (isQuasiSeparated_iff_quasiSeparatedSpace _ O.isOpen).mp hO'
  have H' : IsPullback (k' ∣_ O) ((k' ⁻¹ᵁ O).ι ≫ f') (O.ι ≫ f) (spMap g) :=
    (isPullback_morphismRestrict k' O).paste_vert H
  obtain ⟨t₁, h₁⟩ := gen_chartPull (chartPullIn L (fun _ : PUnit => k') (fun _ => 1) (k' ⁻¹ᵁ O).ι) σ hσ
  obtain ⟨t, ht⟩ := gen_chartPull (chartPullOut L (fun _ : PUnit => O.ι) (fun _ => 1) (k' ∣_ O) _
    fun _ => (morphismRestrict_ι k' O).symm) t₁ h₁
  let e : Γ(O.toScheme, ⊤) ≃+* Γ(Z, O) := O.topIso.commRingCatIsoToRingEquiv
  haveI := hm
  obtain ⟨u, hu⟩ := exists_sec_of_flat g (flat_of_basis g d b hb) (O.ι ≫ f) (k' ∣_ O) _ H' (L.pull O.ι)
    (LB.isLB_pull hL _) t ht (m.comap e) (Ideal.comap_isMaximal_of_surjective e e.surjective)
  refine ⟨u, fun z hz z₀ hz₀ => ?_⟩
  have hc : O.ι ((k' ∣_ O) z) = k' ((k' ⁻¹ᵁ O).ι z) := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  obtain rfl : z₀ = (k' ∣_ O) z := O.ι.injective (hz₀.trans hc.symm)
  refine hu z fun a ha h => hz (e a) ha ?_
  rw [← hc]
  have := O.ι_image_basicOpen_topIso_inv (e a)
  rw [← this]
  exact ⟨_, (show _ ∈ O.toScheme.basicOpen (O.topIso.inv.hom (e a)) from (e.symm_apply_apply a).symm ▸ h), rfl⟩

end GlobalTheory.FlatGenDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalArithmeticVarietyModelProjectiveSpac
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NormalModel

open TopologicalSpace

theorem exists_normal_model : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (D m : ℕ) (y : Fin (m + 1) → Ω) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (ψ : Ω →+* X.functionField),
    (g ≫ PSpace.str (𝓞 K) m = p ∧ IsArithVar p D ∧ Function.Bijective ψ ∧
      (∀ a : 𝓞 K, ψ (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) =
          ψ (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i)) →
    ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (p' : X' ⟶ Sp (𝓞 K)) (g' : X' ⟶ PSpace (𝓞 K) m) (ψ' : Ω →+* X'.functionField),
      g' ≫ PSpace.str (𝓞 K) m = p' ∧ IsArithVar p' D ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' ∧ Function.Bijective ψ' ∧
      (∀ a : 𝓞 K, ψ' (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p' ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g').ι) (h : genericPoint X' ∈ ((ProjSpace.O1 (𝓞 K) m).pull g').U i),
        ψ' (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g').f i) =
          ψ' (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g').f i) := by
  intro K Ω _ _ _ _ D m y X _ p g ψ ⟨hgp, hX, hψ, hK, hy⟩
  obtain ⟨W, hne, hn⟩ := GlobalTheory.T.exists_nonempty_normal_open_arithmeticVariety (𝓞 K) X p D hX
  have := hX.finite
  have : IsFinite (spMap (Int.castRingHom (𝓞 K))) :=
    (IsFinite.SpecMap_iff _).2 (by
      have : (Int.castRingHom (𝓞 K)) = algebraMap ℤ (𝓞 K) := RingHom.ext_int _ _
      change (Int.castRingHom (𝓞 K)).Finite
      rw [this]
      exact RingHom.finite_algebraMap.2 hX.finite)
  have hs : IsProjOver (p ≫ spMap (Int.castRingHom (𝓞 K))) := by
    obtain ⟨h₁, h₂⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hX.isProjOver
    exact (isProjOver_iff_isProper_and_exists_isAmpleLB _).2 ⟨inferInstance, h₂⟩
  have := hX.flat
  obtain ⟨Y, ν, e, hν, hnY, -, hfl, hpb, hd⟩ :=
    GraphClosure.exists_normalisation_of_locallyClosed ℤ X W.toScheme
      (p ≫ spMap (Int.castRingHom (𝓞 K))) W (𝟙 _) hs inferInstance hn inferInstance
  have he : IsOpenImmersion e := MorphismProperty.of_isPullback hpb.flip inferInstance
  have : Nonempty W.toScheme := hne.to_subtype
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  have : IsIntegral Y := by
    have := GlobalTheory.IsNormalScheme.of_pred hnY
    have h := ((IrreducibleSpace.isIrreducible_univ W.toScheme).image _
      e.continuous.continuousOn).closure
    rw [Set.image_univ, hd.closure_eq] at h
    have : IrreducibleSpace Y := (irreducibleSpace_def _).2 h
    exact isIntegral_of_irreducibleSpace_of_isReduced Y
  have hfac : e ≫ ν = W.ι := by rw [hpb.w, Category.id_comp]
  have hoi : IsOpenImmersion (e ≫ ν) := by rw [hfac]; infer_instance
  have hg : e (genericPoint _) = genericPoint Y := genericPoint_eq_of_isOpenImmersion _
  have hgen : ν (genericPoint Y) = genericPoint X := by
    rw [← hg, ← Scheme.Hom.comp_apply]
    exact genericPoint_eq_of_isOpenImmersion _
  have hdeg : ν.residueDegree (genericPoint Y) ≠ 0 := by
    intro h0
    have h1 := CurveDegreesCompare.residueDegree_comp e ν (genericPoint _)
    rw [CurveDegreesCompare.residueDegree_of_isOpenImmersion, hg, h0, zero_mul] at h1
    exact one_ne_zero h1
  have hproj : IsProjOver (ν ≫ p) := isProjOver_comp_of_isFinite ν hX.isProjOver
  have hflat : Flat ((ν ≫ p) ≫ spMap (Int.castRingHom (𝓞 K))) := by rwa [Category.assoc]
  have har : IsArithVar (ν ≫ p) D := ⟨hX.isDomain, hX.finite, ‹_›, hproj, hflat,
    DimCover.topologicalKrullDim_eq (𝓞 K) X Y p (ν ≫ p) D hX hproj hflat ν rfl hgen hdeg⟩

  have hη : ν (genericPoint Y) ⤳ genericPoint X := specializes_of_eq hgen
  have hWη : W.ι (genericPoint W.toScheme) ⤳ genericPoint X :=
    specializes_of_eq (genericPoint_eq_of_isOpenImmersion _)
  have heη : e (genericPoint W.toScheme) ⤳ genericPoint Y := specializes_of_eq hg
  have hbij : Function.Bijective (SmallSec.fnMap ν hη) := by
    refine ⟨(SmallSec.fnMap ν hη).injective, fun u => ?_⟩
    obtain ⟨t, ht⟩ := SmallSec.fnMap_surjective W.ι hWη (SmallSec.fnMap e heη u)
    refine ⟨t, (SmallSec.fnMap e heη).injective ?_⟩
    rw [← ht, ← ProjSpace.fnMap_comp e ν heη hη (ProjSpace.comp_genericPoint_specializes _ _ heη hη)]
    exact ProjSpace.fnMap_congr hfac _ _ t
  refine ⟨Y, ‹_›, ν ≫ p, ν ≫ g, (SmallSec.fnMap ν hη).comp ψ, by rw [Category.assoc, hgp], har, hnY,
    hbij.comp hψ, fun a => ?_, fun k l i h => ?_⟩
  · have e₁ : ν.app ⊤ (algX p ⊤ a) = algX (ν ≫ p) ⊤ a := by
      simp [algX, Scheme.Hom.appLE]
      rfl
    rw [RingHom.comp_apply, hK, SmallSec.fnMap_fnOf ν hη _ (Opens.mem_top _), e₁]
    rfl
  · have hX' : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i := (pull_U _ g i).ge (by
      have h' : ν (genericPoint Y) ∈ g ⁻¹ᵁ (ProjSpace.O1 (𝓞 K) m).U (i PUnit.unit) :=
        (pull_U _ (ν ≫ g) i).le h
      rw [hgen] at h'
      exact h')
    have key (a : Fin (m + 1)) : fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m a) (ν ≫ g)).f i) =
        SmallSec.fnMap ν hη (fnOf _ hX' ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m a) g).f i)) := by
      have h₁ : genericPoint Y ∈ (ν ≫ g) ⁻¹ᵁ (ProjSpace.O1 (𝓞 K) m).U (i PUnit.unit) :=
        (pull_U _ (ν ≫ g) i).le h
      have h₂ : genericPoint X ∈ g ⁻¹ᵁ (ProjSpace.O1 (𝓞 K) m).U (i PUnit.unit) :=
        (pull_U _ g i).le hX'
      change fnOf _ h (resG Y _ _) = SmallSec.fnMap ν hη (fnOf _ hX' (resG X _ _))
      rw [fnOf_resG, fnOf_resG, SmallSec.fnMap_fnOf ν hη h₂ h₁, Scheme.Hom.comp_app]
      rfl
    rw [RingHom.comp_apply, RingHom.comp_apply, key, key, ← map_mul, ← map_mul, hy k l i hX']

end GlobalTheory.NormalModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOddPrimeIsUnitOfCompleteNormalCharZeroBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem exists_odd_prime_isUnit_of_base :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : R) := by
  intro R _ _ _ _
  by_cases h3 : IsUnit ((3 : ℕ) : R)
  · exact ⟨3, Nat.prime_three, ⟨1, rfl⟩, h3⟩
  by_cases h5 : IsUnit ((5 : ℕ) : R)
  · exact ⟨5, by norm_num, ⟨2, rfl⟩, h5⟩
  exfalso
  have m3 : ((3 : ℕ) : R) ∈ maximalIdeal R := (mem_maximalIdeal _).2 h3
  have m5 : ((5 : ℕ) : R) ∈ maximalIdeal R := (mem_maximalIdeal _).2 h5
  have m2 : ((5 : ℕ) : R) - ((3 : ℕ) : R) ∈ maximalIdeal R := Ideal.sub_mem _ m5 m3
  have m1 : ((3 : ℕ) : R) - (((5 : ℕ) : R) - ((3 : ℕ) : R)) ∈ maximalIdeal R := Ideal.sub_mem _ m3 m2
  have e : ((3 : ℕ) : R) - (((5 : ℕ) : R) - ((3 : ℕ) : R)) = 1 := by push_cast; ring
  rw [e] at m1
  exact (mem_maximalIdeal _).1 m1 isUnit_one

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenEtaleRestrictOfUniversallyClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem exists_open_etale_restrict_of_universallyClosed : ∀ (X P' T : Scheme.{0}) (a : X ⟶ P') (W1 : P'.Opens) (c : (a ⁻¹ᵁ W1).toScheme ⟶ T) (x : P'), UniversallyClosed a → x ∈ W1 → (∀ z : (a ⁻¹ᵁ W1).toScheme, ((a ⁻¹ᵁ W1).ι ≫ a) z = x → ∃ U : (a ⁻¹ᵁ W1).toScheme.Opens, z ∈ U ∧ Etale (U.ι ≫ c)) → ∃ W : P'.Opens, W ≤ W1 ∧ x ∈ W ∧ ∀ hle : a ⁻¹ᵁ W ≤ a ⁻¹ᵁ W1, Etale (X.homOfLE hle ≫ c) := by
  intro X P' T a W1 c x ha hx hloc
  have hEt : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
  let S : Set (a ⁻¹ᵁ W1).toScheme := {z | ∃ U : (a ⁻¹ᵁ W1).toScheme.Opens, z ∈ U ∧ Etale (U.ι ≫ c)}
  have hS : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    rintro z ⟨U, hz, hU⟩
    exact ⟨U, fun y hy => ⟨U, hy, hU⟩, U.isOpen, hz⟩
  let Z : Set X := ((a ⁻¹ᵁ W1).ι '' S)ᶜ
  have hZ : IsClosed Z := ((a ⁻¹ᵁ W1).ι.isOpenEmbedding.isOpenMap _ hS).isClosed_compl
  have haZ : IsClosed (a '' Z) := a.isClosedMap _ hZ
  refine ⟨W1 ⊓ ⟨(a '' Z)ᶜ, haZ.isOpen_compl⟩, inf_le_left, ⟨hx, ?_⟩, ?_⟩
  · rintro ⟨z, hzZ, hzx⟩
    apply hzZ
    have hz1 : z ∈ a ⁻¹ᵁ W1 := by
      show a z ∈ W1
      rw [hzx]; exact hx
    have hι : (a ⁻¹ᵁ W1).ι ⟨z, hz1⟩ = z := Scheme.Opens.ι_apply _ _
    refine ⟨⟨z, hz1⟩, hloc ⟨z, hz1⟩ ?_, hι⟩
    exact (Scheme.Hom.comp_apply _ _ _).trans (by rw [hι]; exact hzx)
  · intro hle
    have hcov : ∀ w : (a ⁻¹ᵁ (W1 ⊓ ⟨(a '' Z)ᶜ, haZ.isOpen_compl⟩)).toScheme,
        ∃ U : (a ⁻¹ᵁ W1).toScheme.Opens, X.homOfLE hle w ∈ U ∧ Etale (U.ι ≫ c) := by
      intro w
      have hw : a w.1 ∉ a '' Z := w.2.2
      have hw' : w.1 ∉ Z := fun h => hw ⟨w.1, h, rfl⟩
      simp only [Z, Set.mem_compl_iff, not_not] at hw'
      obtain ⟨s, ⟨U, hsU, hU⟩, hs⟩ := hw'
      refine ⟨U, ?_, hU⟩
      have : X.homOfLE hle w = s :=
        Subtype.ext ((Scheme.homOfLE_apply hle w).trans (hs.symm.trans (Scheme.Opens.ι_apply _ s)))
      rw [this]; exact hsU
    choose U hwU hU using hcov
    refine IsZariskiLocalAtSource.of_iSup_eq_top (fun w => (X.homOfLE hle) ⁻¹ᵁ (U w)) ?_ fun w => ?_
    · rw [eq_top_iff]
      intro w _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨w, hwU w⟩
    · rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι (X.homOfLE hle) (le_refl ((X.homOfLE hle) ⁻¹ᵁ U w)), Category.assoc]
      haveI : IsOpenImmersion ((X.homOfLE hle).resLE (U w) ((X.homOfLE hle) ⁻¹ᵁ U w) le_rfl) := by
        have h2 : IsOpenImmersion ((X.homOfLE hle).resLE (U w) ((X.homOfLE hle) ⁻¹ᵁ U w) le_rfl ≫ (U w).ι) := by
          rw [Scheme.Hom.resLE_comp_ι]; infer_instance
        exact IsOpenImmersion.of_comp _ (U w).ι
      exact IsZariskiLocalAtSource.comp (hU w) _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenPreimageEqBaseChangeSqZeroAugmentationStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_preimage_eq_baseChange_sqZero_augmentation : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) → ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → ∀ U : X₁.Opens, ∃ V : X₀.Opens, pr ⁻¹ᵁ V = U := by
  first | exact @GlobalTheory.SqZeroBC.preimage_surj | exact GlobalTheory.SqZeroBC.preimage_surj | (intros; apply GlobalTheory.SqZeroBC.preimage_surj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenRangeEqInterPreimageEtaleUnivOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isOpen_range_of_etale_of_universallyOpen_comp {Y Z T : Scheme.{0}} (i' : Z ⟶ Y) (h : Y ⟶ T)
    [Etale h] (hu : UniversallyOpen (i' ≫ h)) : IsOpen (Set.range i') := by
  have s_open : IsOpenImmersion (pullback.lift (𝟙 Z) i' (by simp) : Z ⟶ pullback (i' ≫ h) h) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (pullback_lift_diagonal_isPullback i' h) inferInstance
  have e : Set.range i' = (pullback.snd (i' ≫ h) h) '' Set.range (pullback.lift (𝟙 Z) i' (by simp) : Z ⟶ pullback (i' ≫ h) h) := by
    rw [← Set.range_comp]
    congr 1
    ext z
    rw [Function.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_snd]
  rw [e]
  exact (pullback.snd (i' ≫ h) h).isOpenMap _ (pullback.lift (𝟙 Z) i' _).isOpenEmbedding.isOpen_range

theorem exists_opens_range_eq_of_etale {X B T Z : Scheme.{0}} (c : X ⟶ B) (j : T ⟶ B) (i : Z ⟶ X) (φ : Z ⟶ T)
    (hc : Etale c) (hj : IsPreimmersion j) (hφ : UniversallyOpen φ) (w : i ≫ c = φ ≫ j) :
    ∃ W : X.Opens, Set.range i = (W : Set X) ∩ c ⁻¹' Set.range j := by
  let i' : Z ⟶ pullback c j := pullback.lift i φ w
  have hi' : i' ≫ pullback.snd c j = φ := pullback.lift_snd _ _ _
  have ho : IsOpen (Set.range i') :=
    isOpen_range_of_etale_of_universallyOpen_comp i' (pullback.snd c j) (by rw [hi']; exact hφ)
  have hemb := IsPreimmersion.isEmbedding (pullback.fst c j)
  obtain ⟨U, hU, hpre⟩ := hemb.isInducing.isOpen_iff.1 ho
  refine ⟨⟨U, hU⟩, ?_⟩
  have hr : Set.range i = (pullback.fst c j) '' Set.range i' := by
    rw [← Set.range_comp]
    congr 1
    ext z
    rw [Function.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
  rw [hr, ← hpre, Set.image_preimage_eq_inter_range, Scheme.Pullback.range_fst]
  rfl

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqLogDerivationExtendLocalizationAwStatement
section
open GlobalTheory.LogDerProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_smul_eq_logDerivation_extend_localizationAway : ∀ {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R) [IsLocalization.Away f S] (φ : k →+* R), φ.FiniteType → ∀ (J : Ideal R) (n : (logSub ((algebraMap R S).comp φ) (J.map (algebraMap R S))).restrictScalars R), ∃ x : logSub φ J × Submonoid.powers f, x.2 • n = res (S := S) f φ J x.1 := by
  first | exact @GlobalTheory.LogDerProj.exists_pow_smul_eq_res | exact GlobalTheory.LogDerProj.exists_pow_smul_eq_res | (intros; apply GlobalTheory.LogDerProj.exists_pow_smul_eq_res <;> assumption)
end

