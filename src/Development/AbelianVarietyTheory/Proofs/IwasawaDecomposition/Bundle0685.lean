import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsExtendResidue
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0283
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0492
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsStdFStdLvC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CorrespondenceDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0645
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0671
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0053
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0668
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFormEqOneAddMul
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocM

theorem exists_form_eq_one_add_mul {O M : Type} [CommRing O] [IsDomain O] [IsDedekindDomain O] [AddCommGroup M]
    [Module O M] [Module.Projective O M] [Nontrivial M] {q : O} (hq0 : q ≠ 0) :
    ∃ (g : M →ₗ[O] O) (x : M) (t : O), g x = 1 + q * t := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O M)
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : M)
  have hsx : s x₀ ≠ 0 := fun h => hx₀ (by simpa [h] using (LinearMap.congr_fun hs x₀).symm)
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hsx
  set g₀ : M →ₗ[O] O := Finsupp.lapply i ∘ₗ s with hg₀
  have hg₀x : g₀ x₀ ≠ 0 := by simpa [hg₀] using hi
  by_cases hq : IsUnit q
  · obtain ⟨u, rfl⟩ := hq
    exact ⟨g₀, x₀, ↑u⁻¹ * (g₀ x₀ - 1), by rw [← mul_assoc, Units.mul_inv, one_mul]; ring⟩
  set J : Ideal O := LinearMap.range g₀ with hJ
  have hJ0 : J ≠ ⊥ := fun h => hg₀x (by
    have : g₀ x₀ ∈ J := LinearMap.mem_range_self _ _
    rwa [h, Ideal.mem_bot] at this)
  have h0 : Ideal.span {q} * J ≠ ⊥ := mul_ne_zero (by simpa using hq0) hJ0
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (I := Ideal.span {q} * J) (J := J) Ideal.mul_le_right h0
  have haJ : a ∈ J := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  obtain ⟨x, hx⟩ := LinearMap.mem_range.1 haJ
  obtain ⟨J', hJ'⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 haJ)
  have hcop : Ideal.span {q} ⊔ J' = ⊤ := by
    apply mul_left_cancel₀ hJ0
    rw [Ideal.mul_sup, Ideal.mul_top, mul_comm J, ← hJ', ha]
  obtain ⟨y, hy, c, hc, hyc⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : O) ∈ Ideal.span {q} ⊔ J')
  obtain ⟨t', rfl⟩ := Ideal.mem_span_singleton'.1 hy
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hq
    have hJ'0 : J' = ⊥ := by
      have h1 : J * J' = ⊥ := by rw [← hJ', Ideal.span_singleton_eq_bot]
      exact (mul_eq_zero.1 h1).resolve_left hJ0
    rw [hJ'0, sup_bot_eq, Ideal.span_singleton_eq_top] at hcop
    exact hcop
  have hmem : ∀ z, (c • g₀) z ∈ LinearMap.range (LinearMap.mulLeft O a) := by
    intro z
    have : g₀ z * c ∈ Ideal.span {a} := hJ' ▸ Ideal.mul_mem_mul (LinearMap.mem_range_self g₀ z) hc
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨w, by rw [LinearMap.mulLeft_apply, mul_comm, hw, LinearMap.smul_apply, smul_eq_mul, mul_comm]⟩
  let e := LinearEquiv.ofInjective (LinearMap.mulLeft O a) (mul_right_injective₀ ha0)
  let g : M →ₗ[O] O := e.symm.toLinearMap ∘ₗ (c • g₀).codRestrict _ hmem
  have hg : ∀ z, a * g z = c * g₀ z := fun z => by
    set w := e.symm ⟨_, hmem z⟩ with hw
    have h1 : ((e w) : O) = (c • g₀) z := by rw [hw, e.apply_symm_apply]
    have h2 : ((e w) : O) = a * w := LinearEquiv.ofInjective_apply _ _
    show a * w = c * g₀ z
    rw [← h2, h1, LinearMap.smul_apply, smul_eq_mul]
  refine ⟨g, x, -t', mul_left_cancel₀ ha0 ?_⟩
  rw [hg, hx]
  linear_combination a * hyc

theorem exists_isCompl_equiv_quot {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (I : Ideal O)
    (ψ : M →ₗ[O] O ⧸ I) (x : M) (hx : ψ x = 1) (hIx : ∀ r ∈ I, r • x = 0) :
    ∃ l : Submodule O M, (∃ l', IsCompl l l') ∧ Nonempty (l ≃ₗ[O] O ⧸ I) := by
  let σ : (O ⧸ I) →ₗ[O] M := Submodule.liftQ I (LinearMap.toSpanSingleton O M x) fun r hr => by
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    exact hIx r hr
  have hσ : ∀ u, ψ (σ u) = u := by
    intro u
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective u
    show ψ (σ (Submodule.Quotient.mk r)) = _
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, map_smul, hx, Algebra.smul_def, mul_one]
    rfl
  have hinj : Function.Injective σ := Function.LeftInverse.injective hσ
  let f : M →ₗ[O] LinearMap.range σ := (σ ∘ₗ ψ).codRestrict _ fun m => LinearMap.mem_range_self σ _
  refine ⟨LinearMap.range σ, ⟨_, LinearMap.isCompl_of_proj (f := f) ?_⟩, ⟨(LinearEquiv.ofInjective σ hinj).symm⟩⟩
  rintro ⟨_, u, rfl⟩
  exact Subtype.ext (congrArg σ (hσ u))

theorem nonempty_sum1 :
    ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p), Nonempty ct.Sum1 := by
  intro D A N j S κ p ct
  have := S.Dw.proj
  have : Nontrivial S.Dw.La := Module.nontrivial_of_finrank_pos (R := 𝓞 D.host.E)
    (by rw [S.Dw.rank, S.rank_eq]; exact lt_of_lt_of_le two_pos S.two_le)
  have hp0 : (p : 𝓞 D.host.E) ≠ 0 := by exact_mod_cast ct.hp.ne_zero
  obtain ⟨g, x, t, hg⟩ := exists_form_eq_one_add_mul (M := S.Dw.La) hp0
  let P : Submodule (𝓞 D.host.E) S.Dw.La := Ideal.span {(p : 𝓞 D.host.E)} • ⊤
  let ψ : ct.LaP →ₗ[𝓞 D.host.E] 𝓞 D.host.E ⧸ Ideal.span {(p : 𝓞 D.host.E)} :=
    P.liftQ ((Ideal.span {(p : 𝓞 D.host.E)}).mkQ ∘ₗ g) (Submodule.smul_le.2 fun r hr n _ => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, map_smul,
        smul_eq_mul]
      exact Ideal.mul_mem_right _ _ hr)
  have hx : ψ (Submodule.Quotient.mk x) = 1 := by
    show Submodule.Quotient.mk (g x) = (1 : 𝓞 D.host.E ⧸ Ideal.span {(p : 𝓞 D.host.E)})
    exact (Submodule.Quotient.eq _).2 (by
      rw [hg, add_sub_cancel_left]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hIx : ∀ r ∈ Ideal.span {(p : 𝓞 D.host.E)}, r • (Submodule.Quotient.mk x : ct.LaP) = 0 := by
    intro r hr
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  obtain ⟨l, hl, he⟩ := exists_isCompl_equiv_quot _ ψ _ hx hIx
  exact ⟨⟨l, hl, he⟩⟩

end GlobalTheory.LocM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKerTie
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Mem.Top.Bl.WPt.exists_kerTie : ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K), EntC q.x.ker → ∃ t : Formalism.L2.Ker.KerEntTied q.O.ex, KPin q t ∧ GlobalTheory.Svd.StdAt q.w.I q.w.l q.w.l0 q.Z q.O t ∧ GlobalTheory.Pdv.StdRd q.w.I q.w.l q.Z t := by
  intro 𝒮 K q hE
  obtain ⟨B, f, T, w, Z, O, x⟩ := q
  obtain ⟨L, gatT, Gx, Gy, Kc, X, cX, ex⟩ := O
  obtain ⟨lev, th, th_io, cmp, lat, tw, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def, errX, err, nch, nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ := ex
  obtain ⟨isOver, forced, Wt, pin, coh, vol, col, what₂, rx, hlev, herrX, n, nx, sx, ker0, ker_eq, kT, div, thT, obj, ox, real, dsig_eq, gaugeG, good⟩ := x
  simp only [ofObj, extraObj] at ker_eq
  cases ker_eq
  obtain ⟨t1, s1, o1, e1, a1, p1⟩ := TC.kerEntTied_true_ent w.I w.ok w.pins w.l Z L col.Gt Gx Gy Kc X cX
    ⟨lev, th, th_io, col.cmp, lat, w.tw Z, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def, errX, err, nch,
      nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ kT.O kT.E div.Qp kT.std
    kT.unf kT.ok kT.served
  obtain ⟨t, s, r, p, o, e⟩ := GlobalTheory.Core.DefKer.stdRd_keep w.I w.ok w.l Z t1 ((StdModel.stdKer_iff w.I w.l Z t1).2 s1)
  have ha : t.Adapted := by
    unfold Formalism.L2.Ker.KerEntTied.Adapted at a1 ⊢
    rw [o, e]
    exact a1
  have hc : GlobalTheory.Pdv.IsEntC t := by
    unfold GlobalTheory.Pdv.IsEntC
    rw [o, e, o1, e1]
    exact hE
  exact ⟨t, ⟨s, o.trans o1, heq_of_eq (e.trans e1), ha, p⟩, ⟨w.ok, w.pins, pin.isTw, pin.jets, rfl, s, hc, ha, p⟩, r⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelWithRatio
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.HTLine

attribute [local instance] Over.cartesianMonoidalCategory

theorem princ_of_finite (X : Scheme.{0}) [IsLocallyNoetherian X] (p : ℕ) {T : Type} [Finite T] (U : T → X.Opens)
    (m : T → ℕ) (A : ∀ j, Fin (m j) → Γ(X, U j)) (hU : ∀ j, IsAffineOpen (U j))
    (hA : ∀ j, (p : Γ(X, U j)) ∈ (Ideal.span (Set.range (A j))).radical) :
    ∃ J : X.IdealSheafData, (∀ x ∈ J.support, x ∉ X.basicOpen (p : Γ(X, ⊤))) ∧
      ∀ (W W' : Scheme.{0}) (b : W ⟶ X) (ν : W' ⟶ W), ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap b) →
        ∀ (w : W') (j : T), (ν ≫ b) w ∈ U j → ∃ (V : W'.Opens) (hV : V ≤ (ν ≫ b) ⁻¹ᵁ U j), w ∈ V ∧ IsAffineOpen V ∧
          ∃ k, ∀ k', ((ν ≫ b).appLE (U j) V hV).hom (A j k) ∣ ((ν ≫ b).appLE (U j) V hV).hom (A j k') := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin T
  obtain ⟨J, hJ, hP⟩ := GlobalTheory.T.exists_ideal_sheaf_away_from_p X p n (fun i => U (e.symm i)) (fun i => m (e.symm i)) (fun i => A (e.symm i))
    (fun i => hU _) (fun i => hA _)
  refine ⟨J, hJ, fun W W' b ν hC w j hw => ?_⟩
  obtain ⟨i, rfl⟩ := e.symm.surjective j
  exact hP W W' b ν hC w i hw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem mem_basicOpen_p (hp : p ≠ 0) (Z : Mdl Y i₀) {x : Z.X} (hx : x ∈ Z.opn) :
    x ∈ Z.X.basicOpen (p : Γ(Z.X, ⊤)) := by
  rw [← Z.cover] at hx
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hx
  have hu : IsUnit (p : Γ(Z.X, (Z.U a).1)) := by
    have e : (p : Γ(Z.X, (Z.U a).1)) = Z.alg a (p : Z.i.c.F) := (map_natCast _ _).symm
    rw [e]
    refine (IsUnit.mk0 _ ?_).map _
    intro h0
    have : ((p : Z.i.c.F) : ℂ) = 0 := by rw [h0]; rfl
    exact hp (by exact_mod_cast this)
  have h1 : x ∈ Z.X.basicOpen (p : Γ(Z.X, (Z.U a).1)) := by
    rw [Scheme.basicOpen_of_isUnit _ hu]; exact ha
  have e2 : (p : Γ(Z.X, (Z.U a).1)) = (Z.X.presheaf.map (homOfLE le_top).op).hom (p : Γ(Z.X, ⊤)) :=
    (map_natCast _ _).symm
  rw [e2, Scheme.basicOpen_res] at h1
  exact h1.2

theorem norm_valF_le_one {Z : Mdl Y i₀} (y : Z.Pt) {U : Z.X.Opens} (hU : IsAffineOpen U) (hy : ⊤ ≤ y.z ⁻¹ᵁ U)
    (s : Γ(Z.X, U)) : ‖valF y.gen U s‖ ≤ 1 ∧ ⊤ ≤ y.gen ⁻¹ᵁ U := by
  obtain ⟨χ, hχ⟩ := Pull.exists_fromSpec hU y.z hy
  have hg : spMap ((intO ↥y.C.S).subtype.comp χ) ≫ hU.fromSpec = y.gen := by
    rw [Mdl.Pt.gen, ← hχ, ← Category.assoc, spMap, spMap, spMap, ← Spec.map_comp]; rfl
  refine ⟨?_, Pull.le_of_fromSpec hU hg⟩
  rw [← hg, Pull.valF_fromSpec]
  exact (χ s).2

theorem span_eq_single {R : Type} [CommRing R] {m : ℕ} (A : Fin m → R) (k : Fin m) (hk : ∀ k', A k ∣ A k') :
    Ideal.span (Set.range A) = Ideal.span (Set.range ![A k]) := by
  rw [Matrix.range_cons, Matrix.range_empty, Set.union_empty]
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono (Set.singleton_subset_iff.2 ⟨k, rfl⟩))
  rintro _ ⟨k', rfl⟩
  exact Ideal.mem_span_singleton.2 (hk k')

theorem norm_eq_single {Z : Mdl Y i₀} (y : Z.Pt) {U : Z.X.Opens} (hU : IsAffineOpen U) (hy : ⊤ ≤ y.z ⁻¹ᵁ U) {m : ℕ}
    (A : Fin m → Γ(Z.X, U)) (k : Fin m) (hk : ∀ k', A k ∣ A k') :
    ‖fun j => valF y.gen U (A j)‖ = ‖fun j => valF y.gen U (![A k] j)‖ := by
  have e1 : (fun j => valF y.gen U (![A k] j)) = fun _ : Fin 1 => valF y.gen U (A k) := by
    funext j; rw [Matrix.cons_val_fin_one]
  rw [e1, pi_norm_const]
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_) (norm_le_pi_norm (fun j => valF y.gen U (A j)) k)
  obtain ⟨d, hd⟩ := hk j
  have h := norm_valF_le_one y hU hy d
  rw [hd, Pull.valF_mul h.2, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) h.1

theorem ratioAt_single {Z : Mdl Y i₀} {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {U : Z.X.Opens} (hU : IsAffineOpen U) {m m' : ℕ}
    {A : Fin m → Γ(Z.X, U)} {B : Fin m' → Γ(Z.X, U)} (h : RatioAt Z st U A B) (k₁ : Fin m) (hk₁ : ∀ k, A k₁ ∣ A k)
    (k₂ : Fin m') (hk₂ : ∀ k, B k₂ ∣ B k) : RatioAt Z st U ![A k₁] ![B k₂] := by
  obtain ⟨hA, hB, hr⟩ := h
  refine ⟨span_eq_single A k₁ hk₁ ▸ hA, span_eq_single B k₂ hk₂ ▸ hB, fun y a φ hφ hy => ?_⟩
  rw [hr y a φ hφ hy, norm_eq_single y hU hy A k₁ hk₁, norm_eq_single y hU hy B k₂ hk₂]

theorem exists_pRatio : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → N2 Y → ∀ (Z : Mdl Y i₀) st (x : Letter Dw), letterOf Dw st = some x → (∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) → HasRatio Z st → ∃ (Z' : Mdl Y i₀) (f : Z'.X ⟶ Z.X), Z'.i = Z.i ∧ Z'.ty = Z.ty ∧ IsMap Z' Z f ∧ HasPRatio Z' st := by
  intro hHT E _ _ _ H Dw Xo p W Y i₀ hp hW hN2 Z st x hx hty hR
  haveI := GlobalTheory.LocM.Diag.isLocallyNoetherian hp hW Z
  haveI : CompactSpace Z.X := by
    have := GlobalTheory.LocM.SharedLaws.isProper_toroidalModel_structureMap Z
    exact QuasiCompact.compactSpace_of_compactSpace Z.s
  choose U m m' A B hzU hUa hRat using hR
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun z => (U z : Set Z.X)) fun z => (U z).isOpen.mem_nhds (hzU z)
  let pt : (t ⊕ t) → Z.X := Sum.elim Subtype.val Subtype.val
  let mm : (t ⊕ t) → ℕ := Sum.elim (fun z => m z.1) (fun z => m' z.1)
  let AA : ∀ j, Fin (mm j) → Γ(Z.X, U (pt j)) := fun j =>
    Sum.rec (motive := fun j => Fin (mm j) → Γ(Z.X, U (pt j))) (fun z => A z.1) (fun z => B z.1) j
  obtain ⟨J, hJ, hP⟩ := princ_of_finite Z.X p (fun j => U (pt j)) mm AA (fun j => hUa (pt j))
    (by rintro (z | z); exacts [(hRat z.1).1, (hRat z.1).2.1])
  have hJ' : ∀ y ∈ J.support, y ∉ Z.opn := fun y hy ho => hJ y hy (mem_basicOpen_p hp.ne_zero Z ho)
  obtain ⟨Z', hi, hty', X', b, ν, hbl, -, hmap⟩ := GlobalTheory.ProjBlowup.exists_isNBlow hp hW Z ⟨J, hJ'⟩
  refine ⟨Z', ν ≫ b, hi, hty', hmap, fun z' => ?_⟩
  have hmem : (ν ≫ b) z' ∈ ⋃ z ∈ t, (U z : Set Z.X) := by rw [ht]; exact Set.mem_univ _
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨z, hz, hfz⟩ := hmem
  obtain ⟨V₁, hV₁, hz₁, -, k₁, hk₁⟩ := hP X' Z'.X b ν hbl.1 z' (Sum.inl ⟨z, hz⟩) hfz
  obtain ⟨V₂, hV₂, hz₂, -, k₂, hk₂⟩ := hP X' Z'.X b ν hbl.1 z' (Sum.inr ⟨z, hz⟩) hfz
  obtain ⟨V, hVa', hzV, hVle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z'.X.isBasis_affineOpens)
    (show z' ∈ V₁ ⊓ V₂ from ⟨hz₁, hz₂⟩)
  have hVa : IsAffineOpen V := hVa'
  have hVU : V ≤ (ν ≫ b) ⁻¹ᵁ U z := hVle.trans (inf_le_left.trans hV₁)
  have hres : ∀ (V' : Z'.X.Opens) (hV' : V' ≤ (ν ≫ b) ⁻¹ᵁ U z) (hle : V ≤ V') (s : Γ(Z.X, U z)),
      ((ν ≫ b).appLE (U z) V hVU).hom s =
        (Z'.X.presheaf.map (homOfLE hle).op).hom (((ν ≫ b).appLE (U z) V' hV').hom s) := by
    intro V' hV' hle s
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have hR' := GlobalTheory.T.letter_section_on_map hHT E H Dw Xo p W Y i₀ hp hW hN2 Z Z' (ν ≫ b) hmap hty st x hx (U z) (m z) (m' z)
    (A z) (B z) (hRat z) V hVU
  refine ⟨V, _, _, hzV, hVa, ratioAt_single hVa hR' k₁ (fun k => ?_) k₂ (fun k => ?_)⟩
  · rw [hres V₁ hV₁ (hVle.trans inf_le_left), hres V₁ hV₁ (hVle.trans inf_le_left)]
    exact map_dvd _ (hk₁ k)
  · rw [hres V₂ hV₂ (hVle.trans inf_le_right), hres V₂ hV₂ (hVle.trans inf_le_right)]
    exact map_dvd _ (hk₂ k)

end GlobalTheory.HTLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvr
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.MonPeriods

theorem exists_isMonomial_levelOne : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {W : Type}
    [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (t : SAB H (Sp W))
    (P : PELUnif (maximalIdeal W) t), ∃ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] := by
  intro E _ _ _ H W _ _ _ hW ϖ hϖ t P
  obtain ⟨hdvr, hcomp, hchar⟩ := hW
  haveI := hdvr
  haveI := hcomp
  haveI := hchar
  letI := H.starRing
  choose Q hQ using QForm.exists_QVal hϖ P.D
  have hQ' : QForm.IsQ P.D.toPre ϖ Q := hQ
  have hex : ∀ χ, ∃ r, PsiCoord P.D.toPre χ r := fun χ =>
    ((GlobalTheory.PsiCoordLocal.main W P.D inferInstance χ).1).imp fun _ h => h.1
  have hv : ∀ χ, HasVal ϖ (algebraMap W (FractionRing W) (hex χ).choose) (Q χ) := fun χ =>
    GlobalTheory.ValForm.hasVal_coord (hQ χ) (hex χ).choose_spec
  have h0 : ∀ a, 0 ≤ Q a := fun a => by
    by_cases ha : a = 0
    · rw [ha, QForm.Q_zero hϖ P.D hQ']
    · exact zero_le_one.trans (QForm.Q_pos hϖ P.D hQ' ha)
  have hbal : ∀ (x : 𝓞 E) a b, QForm.bOf P.D.toPre Q (x • a) b = QForm.bOf P.D.toPre Q a (H.bar x • b) := by
    intro x a b
    obtain ⟨u, hu⟩ := GlobalTheory.PeriodBalance.coord_balance P.D.toPre P.oD x a b (hex (x • a + b)).choose_spec
      (hex (x • a)).choose_spec (hex b).choose_spec (hex (a + H.bar x • b)).choose_spec (hex a).choose_spec
      (hex (H.bar x • b)).choose_spec
    have h1 := hasVal_mul_unit (GlobalTheory.ValForm.hasVal_mul hϖ (GlobalTheory.ValForm.hasVal_mul hϖ (hv (x • a + b)) (hv a))
      (hv (H.bar x • b))) u
    have h2 := GlobalTheory.ValForm.hasVal_mul hϖ (GlobalTheory.ValForm.hasVal_mul hϖ (hv (a + H.bar x • b)) (hv (x • a))) (hv b)
    rw [← map_mul, _root_.mul_comm, hu] at h1
    have := hasVal_unique hϖ h1 h2
    simp only [QForm.bOf]
    linarith
  let be : LinearMap.BilinForm ℤ P.D.toPre.X :=
    LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ P.D hQ' a b)
      (fun a a' b => by simp only [map_add, AddMonoidHom.add_apply])
      (fun c a b => by simp only [map_zsmul, AddMonoidHom.smul_apply, smul_eq_mul])
      (fun a b b' => by simp only [map_add])
      (fun c a b => by simp only [map_zsmul, smul_eq_mul])
  have hbe : ∀ a b, be a b = QForm.bOf P.D.toPre Q a b := fun _ _ => rfl
  refine ⟨be, ⟨fun y z => ?_, fun a y z => ?_, fun y z => by simp⟩, fun y => ?_⟩
  · rw [hbe, hbe, QForm.bOf_comm]
  · rw [hbe, hbe]
    exact hbal a y z
  · obtain ⟨u, hu⟩ := hv y
    set r := (hex y).choose with hr
    have hn : (((Q y).toNat : ℕ) : ℤ) = Q y := Int.toNat_of_nonneg (h0 y)
    have e : r = ↑u * ϖ ^ (Q y).toNat := by
      apply IsFractionRing.injective W (FractionRing W)
      rw [hu, map_mul, map_pow, _root_.mul_comm, ← zpow_natCast, hn]
    refine ⟨u, fun _ => (Q y).toNat, fun i => ?_, ?_⟩
    · fin_cases i
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [hbe, ← QForm.two_Q_eq hϖ P.D hQ', hn]
    · have hc : PsiCoord P.D.toPre y r := (hex y).choose_spec
      rw [e] at hc
      simpa using hc

end GlobalTheory.MonPeriods
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosDefBalancedRealFormCmFieldStatement
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_posDef_balanced_realForm_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], ∃ B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, B ∈ realForms H.bar X ∧ IsPosDef B := by
  first | exact @GlobalTheory.DefForm.exists_posDef_realForm | exact GlobalTheory.DefForm.exists_posDef_realForm | (intros; apply GlobalTheory.DefForm.exists_posDef_realForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealIndependentBasisLatticeFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_real_independent_basis_lattice_family : ∀ (n g : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (b₀ : Fin n → ℂ), IsLatFam B K → b₀ ∈ B → ∃ (r : ℕ) (b : Fin r → Fin g → ℂ), IsLatBasis (K b₀) b := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.exists_isLatBasis_of_isLatFam | exact GlobalTheory.ShFam.Hor.LogCh.exists_isLatBasis_of_isLatFam | (intros; apply GlobalTheory.ShFam.Hor.LogCh.exists_isLatBasis_of_isLatFam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiAbelianPolarizedStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semi_abelian_polarized : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Y.X), IsCN R → Set.range ξ ⊆ Set.range Y.j → ∃ (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), PolAt t (jK R) ∧ ThetaNZ t.G t.PP.L ∧ ∀ x, x ∈ abLocus t.G := by
  first | exact @GlobalTheory.GenFan.Tri.exists_sab | exact GlobalTheory.GenFan.Tri.exists_sab | (intros; apply GlobalTheory.GenFan.Tri.exists_sab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSiegelReducedBasisOfPosDefFormStatement
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelReduced_basis_of_posDef_form : ∀ (n : ℕ) (Y : Type) [AddCommGroup Y] (b₀ : Module.Basis (Fin n) ℤ Y) (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ), (∀ y z, B y z = B z y) → IsPosDef B → ∃ (b : Module.Basis (Fin n) ℤ Y) (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u ∧ (∀ i, 0 < d i) ∧ ∀ i j, B (b i) (b j) = gram d u i j := by
  first | exact @GlobalTheory.RedTh.RedBasis.exists_siegel_basis | exact GlobalTheory.RedTh.RedBasis.exists_siegel_basis | (intros; apply GlobalTheory.RedTh.RedBasis.exists_siegel_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSiegelReductionOrthogonalStatement
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegel_reduction_orthogonal : ∀ (s m : ℕ) (d₁ : Fin s → ℝ) (u₁ : Matrix (Fin s) (Fin s) ℝ) (d₂ : Fin m → ℝ) (u₂ : Matrix (Fin m) (Fin m) ℝ), IsSiegel d₁ u₁ → IsSiegel d₂ u₂ → (∀ i, 0 < d₁ i) → (∀ i, 0 < d₂ i) → ∃ (t : ℝ) (d d' : Fin (s + m) → ℝ) (u : Matrix (Fin (s + m)) (Fin (s + m)) ℝ), 0 < t ∧ IsSiegel d u ∧ IsSiegel d' u ∧ (∀ i, 0 < d' i) ∧ (∀ i j : Fin s, gram d u (Fin.castAdd m i) (Fin.castAdd m j) = 0 ∧ gram d' u (Fin.castAdd m i) (Fin.castAdd m j) = t * gram d₁ u₁ i j) ∧ (∀ (i : Fin s) (j : Fin m), gram d u (Fin.castAdd m i) (Fin.natAdd s j) = 0 ∧ gram d u (Fin.natAdd s j) (Fin.castAdd m i) = 0 ∧ gram d' u (Fin.castAdd m i) (Fin.natAdd s j) = 0 ∧ gram d' u (Fin.natAdd s j) (Fin.castAdd m i) = 0) ∧ ∀ i j : Fin m, gram d u (Fin.natAdd s i) (Fin.natAdd s j) = gram d₂ u₂ i j ∧ gram d' u (Fin.natAdd s i) (Fin.natAdd s j) = gram d₂ u₂ i j := by
  first | exact @GlobalTheory.RedTh.siegelData_glue_scaled | exact GlobalTheory.RedTh.siegelData_glue_scaled | (intros; apply GlobalTheory.RedTh.siegelData_glue_scaled <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionCubicalWeilOneComplexPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_toricTorsion_cubicalWeil_one_complexPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (y : Sp ℂ ⟶ X) (g N : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)), 0 < N → IsExpAt t y e → Function.Surjective e → IsHolTo Set.univ (fun w => (e w).left) → ∃ T : Set (Over.mk y ⟶ t.G), (∀ τ ∈ T, τ ^ N = 1) ∧ (∀ τ ∈ T, ∀ x : Over.mk y ⟶ t.G, x ^ N = 1 → GlobalTheory.UU.CubWeil t.cub N τ x 1) ∧ Nat.card {p : Over.mk y ⟶ t.G // p ^ N = 1} * Nat.card T = N ^ (2 * g) := by
  first | exact @GlobalTheory.exists_toric_torsion_cubWeil_one_of_exp | exact GlobalTheory.exists_toric_torsion_cubWeil_one_of_exp | (intros; apply GlobalTheory.exists_toric_torsion_cubWeil_one_of_exp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformisationBaseChangeWithCoordinates
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.UnifCoordPull

theorem exists_unif_psiCoord : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN R → IsCN V → ∀ ψ : R →+* V, IsLocalHom ψ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (W : Set (Sp R)), IsOpen W → (∀ y, PsiUnitOn D.toPre y W) → (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) ∈ W → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap ψ) β → IsAbelianScheme ((Over.pullback (jK V)).obj G') → Rigidified ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → Out.Sym ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → RelAmple ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → KTriv ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → ∃ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (ε : D'.toPre.X ≃+ D.toPre.X), LBIso (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) (U'.LG.L.pull (pullback.fst G'.hom (jK V))) ∧ ∀ y r, PsiCoord D.toPre (ε y) r → ∃ u : Vˣ, PsiCoord D'.toPre y (u * ψ r) := by
  intro R _ _ _ V _ _ _ hR hV ψ hψl G _ _ hG D A U W hWo hψ hker G' _ _ β hpb hab hrig hsym hamp hkt
  obtain ⟨-, -, -, h4, -⟩ := GlobalTheory.firstFiveLaws
  have aR := admissibleBase_of_completeNormalLocalCharZero hR
  have aV := admissibleBase_of_completeNormalLocalCharZero hV
  have hI : (maximalIdeal R).map ψ ≤ maximalIdeal V :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (map_mem_nonunits_iff ψ a).2 ha
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso hpb (isGrpPullback_pullback G (spMap ψ))
  subst hbc

  have := hG.smooth
  have := hG.geomConnected
  have : ConnectedSpace (Sp R) := inferInstanceAs (ConnectedSpace (PrimeSpectrum R))
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace G.hom G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected G.hom (Classical.arbitrary _)
  have hgA := GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre
  have hgK := (isGrpPullback_pullback G' (jK V)).comp hpb
  have dA : d = A.g := H1.dim_unique _ ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hgA.1 hd)
    A.smoothDim (eSec A.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R)))
  have hdK : SmoothOfRelativeDimension A.g ((Over.pullback (jK V)).obj G').hom :=
    dA ▸ (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hgK.1 hd
  have he := GlobalTheory.PolBaseChange.eSec_comm hpb
  let A' : PolAV (Sp (FractionRing V)) :=
    { A := (Over.pullback (jK V)).obj G'
      isAb := hab
      g := A.g
      smoothDim := hdK
      L := U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ bc.hom.left ≫ pullback.fst G.hom (spMap ψ))
      isLB := pull_isLB U.LG.isLB _
      rigid := hrig
      sym := hsym
      ample := hamp
      ktriv := hkt }
  have eAm : IsMonHom (Iso.refl A'.A).hom := show IsMonHom (𝟙 A'.A) from inferInstance
  have wA : ∃ wA : LB.Iso (A'.L.pull (Iso.refl A'.A).hom.left)
      (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ψ))), wA.IsGen := by
    have k : LBIso (A'.L.pull (𝟙 _)) (U.LG.L.pull (𝟙 _ ≫ pullback.fst G'.hom (jK V) ≫ bc.hom.left ≫
        pullback.fst G.hom (specOf ψ))) :=
      ⟨GlobalTheory.Proof.TautologicalModel.taut U.LG.L _ (𝟙 _), GlobalTheory.Proof.TautologicalModel.taut_isGen U.LG.isLB _ _⟩
    rw [Category.id_comp] at k
    exact k
  let L' : RigLB G' := ⟨U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (spMap ψ)),
    rigPullOf (G' := G') (G := G) (bc.hom.left ≫ pullback.fst G.hom (spMap ψ)) (spMap ψ) he U.LG.L U.LG.rig, pull_isLB U.LG.isLB _,
    GlobalTheory.Proof.TautologicalModel.rigPullOf_isGen (G' := G') (G := G) (bc.hom.left ≫ pullback.fst G.hom (spMap ψ)) (spMap ψ) he U.LG.L U.LG.rig U.LG.rigGen⟩
  obtain ⟨wL, gL, rL⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (spMap ψ) G G' _ he U.LG L'
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB U.LG.isLB _))
  have hgen : (specOf ψ).base (genericPoint (Spec (CommRingCat.of V))) ∈ (⟨W, hWo⟩ : (Sp R).Opens) := by
    have : (specOf ψ).base (genericPoint (Spec (CommRingCat.of V))) =
        (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) := by
      rw [genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext rfl
    rw [this]; exact hker
  obtain ⟨D', hD, U', hLG, -, -⟩ := h4.unifBaseChange R V _ _ aR aV ψ hI D A G hG U ⟨W, hWo⟩
    (GlobalTheory.PelCoordPull.nonempty_psiOn D.toPre ⟨W, hWo⟩ ⟨_, hker⟩ hψ) hgen G' bc mbc A' rfl (Iso.refl _) eAm wA
    L' wL he gL rL
  refine ⟨D', A', U', hD.xe, ?_, fun y r hr => GlobalTheory.PelCoordPull.psiCoord_pull hD y r hr⟩
  rw [hLG]
  exact LBIso.symm ⟨GlobalTheory.Proof.TautologicalModel.taut U.LG.L _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen U.LG.isLB _ _⟩

end GlobalTheory.UnifCoordPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformizationAbelianStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformization_abelian : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)), IsCN R → PolAt t (jK R) → ThetaNZ t.G t.PP.L → (∀ x, x ∈ abLocus t.G) → ∃ P : PELUnif (maximalIdeal R) t, P.TorsionIso ∧ Subsingleton P.D.toPre.X := by
  first | exact @GlobalTheory.GenFan.exists_pelUnif_torsionIso_subsingleton_of_abLocus | exact GlobalTheory.GenFan.exists_pelUnif_torsionIso_subsingleton_of_abLocus | (intros; apply GlobalTheory.GenFan.exists_pelUnif_torsionIso_subsingleton_of_abLocus <;> assumption)
end

