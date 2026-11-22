import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0024
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0022
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2547
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2548
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTrivialisationOfBalancedBimultiplicativ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2549
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0624
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFlagHodgeIndexVanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonOfNotNonempty
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section

namespace GlobalTheory.SqGlue

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom s) =
      (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem subsingleton_of_not_nonempty {X : Scheme.{0}} {W : X.Opens} (h : ¬ Nonempty W) : Subsingleton Γ(X, W) := by
  have e : W = ⊥ := by
    ext x
    simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hx => h ⟨⟨x, hx⟩⟩
  subst e
  infer_instance

theorem res_cancel {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} (hW : W ≤ V) {a : Γ(X, V)} (ha : a ≠ 0)
    {b c : Γ(X, W)} (h : b * (X.presheaf.map (homOfLE hW).op).hom a = c * (X.presheaf.map (homOfLE hW).op).hom a) :
    b = c := by
  by_cases hn : Nonempty W
  · refine mul_right_cancel₀ (fun h0 => ha ?_) h
    apply map_injective_of_isIntegral X (homOfLE hW)
    rw [h0, map_zero]
  · exact (subsingleton_of_not_nonempty hn).elim _ _

theorem exists_unit_of_locally {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} (hW : W ≤ V) (s : Γ(X, W))
    {t : Γ(X, V)} (ht : t ≠ 0)
    (h : ∀ x ∈ W, ∃ (O : X.Opens) (hO : O ≤ W), x ∈ O ∧ ∃ u : Γ(X, O)ˣ,
      (X.presheaf.map (homOfLE hO).op).hom s = (u : Γ(X, O)) * (X.presheaf.map (homOfLE (hO.trans hW)).op).hom t) :
    ∃ c : Γ(X, W)ˣ, s = (c : Γ(X, W)) * (X.presheaf.map (homOfLE hW).op).hom t := by
  choose O hO hx u hu using fun x : W => h x.1 x.2
  have hcov : W ≤ iSup O := fun x hxW => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxW⟩, hx _⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf O (fun x => (u x : Γ(X, O x))) := by
    intro x y
    refine res_cancel (W := O x ⊓ O y) (inf_le_left.trans ((hO x).trans hW)) ht ?_
    have e₁ := congrArg (X.presheaf.map (homOfLE (inf_le_left : O x ⊓ O y ≤ O x)).op).hom (hu x)
    have e₂ := congrArg (X.presheaf.map (homOfLE (inf_le_right : O x ⊓ O y ≤ O y)).op).hom (hu y)
    rw [map_mul, res_res, res_res] at e₁ e₂
    exact e₁.symm.trans e₂
  obtain ⟨c, hc, -⟩ := X.sheaf.existsUnique_gluing' O W (fun x => homOfLE (hO x)) hcov
    (fun x => (u x : Γ(X, O x))) hcomp
  have hc' : ∀ x, (X.presheaf.map (homOfLE (hO x)).op).hom c = (u x : Γ(X, O x)) := hc
  have hunit : IsUnit (c : Γ(X, W)) := by
    refine X.toRingedSpace.isUnit_of_isUnit_germ W c fun x hxW => ?_
    have e := X.presheaf.germ_res_apply (homOfLE (hO ⟨x, hxW⟩)) x (hx ⟨x, hxW⟩) c
    have e' := (u ⟨x, hxW⟩).isUnit.map (X.presheaf.germ (O ⟨x, hxW⟩) x (hx ⟨x, hxW⟩)).hom
    rw [← hc'] at e'
    exact e ▸ e'
  refine ⟨hunit.unit, ?_⟩
  refine X.sheaf.eq_of_locally_eq' O W (fun x => homOfLE (hO x)) hcov _ _ fun x => ?_
  change (X.presheaf.map (homOfLE (hO x)).op).hom s = (X.presheaf.map (homOfLE (hO x)).op).hom _
  rw [map_mul, res_res, IsUnit.unit_spec, hc', hu x]

theorem app_res {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} {O : X.Opens} (hU : U' ≤ U) (hO : O ≤ f ⁻¹ᵁ U')
    (s : Γ(Y, U)) :
    (X.presheaf.map (homOfLE (hO.trans (f.preimage_mono hU))).op).hom ((f.app U).hom s) =
      (X.presheaf.map (homOfLE hO).op).hom ((f.app U').hom ((Y.presheaf.map (homOfLE hU).op).hom s)) := by
  rw [← res_res (f.preimage_mono hU) hO]
  congr 1
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

def resU {X : Scheme.{0}} {A B : X.Opens} (h : B ≤ A) (u : Γ(X, A)ˣ) : Γ(X, B)ˣ :=
  Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom u

@[simp] theorem coe_resU {X : Scheme.{0}} {A B : X.Opens} (h : B ≤ A) (u : Γ(X, A)ˣ) :
    (resU h u : Γ(X, B)) = (X.presheaf.map (homOfLE h).op).hom u := rfl

theorem pow_ne_zero' {X : Scheme.{0}} [IsIntegral X] {V : X.Opens} {a : Γ(X, V)} (ha : a ≠ 0) (n : ℕ) : a ^ n ≠ 0 := by
  by_cases hn : Nonempty V
  · exact pow_ne_zero n ha
  · exact (ha ((subsingleton_of_not_nonempty hn).elim _ _)).elim

end GlobalTheory.SqGlue

open GlobalTheory.SqGlue in

theorem GlobalTheory.SqGlue.main : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (L2 : LB G₁.left), L2.IsLB → ∀ (h : L2.Sec) (Lθ : LB (pullback G₁.hom (jK R'))) (θ : Lθ.Sec), (∀ j i, ∃ w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i)ˣ, ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i)) * ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G₁.hom (jK R')).app (L2.U j)).hom (h.f j))) → ∀ (Ix : Type) (V : Ix → G₁.left.Opens) (a : ∀ k, Γ(G₁.left, V k)), (∀ k, a k ≠ 0) → (∀ k j, ∃ u : Γ(G₁.left, V k ⊓ L2.U j)ˣ, (G₁.left.presheaf.map (homOfLE inf_le_right).op).hom (h.f j) = (u : Γ(G₁.left, V k ⊓ L2.U j)) * (G₁.left.presheaf.map (homOfLE inf_le_left).op).hom (a k) ^ 2) → (∀ k l, ∃ c : Γ(G₁.left, V k ⊓ V l)ˣ, (G₁.left.presheaf.map (homOfLE inf_le_left).op).hom (a k) ^ 2 = (c : Γ(G₁.left, V k ⊓ V l)) * (G₁.left.presheaf.map (homOfLE inf_le_right).op).hom (a l) ^ 2) ∧ (∀ k i, ∃ w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ V k ⊓ Lθ.U i)ˣ, ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ V k ⊓ Lθ.U i)) * ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G₁.hom (jK R')).app (V k)).hom (a k)) ^ 2) := by
  intro R' _ _ _ _ G₁ _ _ hsemi L2 hL h Lθ θ hθ Ix V a hne hu
  haveI : Smooth G₁.hom := hsemi.smooth
  haveI : GeometricallyConnected G₁.hom := hsemi.geomConnected
  haveI : IsIntegral G₁.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G₁
  haveI : IsIntegral (pullback G₁.hom (jK R')) := GlobalTheory.isIntegral_pullback_of_smooth G₁.hom (jK R')
  have hcov : ∀ x : G₁.left, ∃ j, x ∈ L2.U j := fun x => by
    have : x ∈ (⊤ : G₁.left.Opens) := trivial
    rw [← hL.cover] at this
    exact TopologicalSpace.Opens.mem_iSup.1 this
  set f := pullback.fst G₁.hom (jK R') with hf
  refine ⟨fun k l => ?_, fun k i => ?_⟩
  · refine (exists_unit_of_locally inf_le_right
      ((G₁.left.presheaf.map (homOfLE (inf_le_left : V k ⊓ V l ≤ V k)).op).hom (a k) ^ 2)
      (pow_ne_zero' (hne l) 2) fun x hx => ?_).imp fun c hc => by rwa [map_pow] at hc
    obtain ⟨j, hj⟩ := hcov x
    obtain ⟨uk, huk⟩ := hu k j
    obtain ⟨ul, hul⟩ := hu l j
    have hk : V k ⊓ V l ⊓ L2.U j ≤ V k ⊓ L2.U j := inf_le_inf_right _ inf_le_left
    have hl : V k ⊓ V l ⊓ L2.U j ≤ V l ⊓ L2.U j := inf_le_inf_right _ inf_le_right
    have e1 := congrArg (G₁.left.presheaf.map (homOfLE hk).op).hom huk
    have e2 := congrArg (G₁.left.presheaf.map (homOfLE hl).op).hom hul
    rw [map_mul, map_pow, res_res, res_res] at e1 e2
    have e : (resU hk uk : Γ(G₁.left, V k ⊓ V l ⊓ L2.U j)) *
        (G₁.left.presheaf.map (homOfLE (hk.trans inf_le_left)).op).hom (a k) ^ 2 =
        (resU hl ul : Γ(G₁.left, V k ⊓ V l ⊓ L2.U j)) *
        (G₁.left.presheaf.map (homOfLE (hl.trans inf_le_left)).op).hom (a l) ^ 2 := by
      rw [coe_resU, coe_resU, ← e1, ← e2]
    refine ⟨V k ⊓ V l ⊓ L2.U j, inf_le_left, ⟨hx, hj⟩, (resU hk uk)⁻¹ * resU hl ul, ?_⟩
    rw [map_pow, res_res, map_pow, Units.val_mul, _root_.mul_assoc, ← e, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  · have ht : (f.app (V k)).hom (a k) ≠ 0 := fun h0 =>
      hne k (GlobalTheory.ExpInt.generic_app_injective G₁ (V k) (h0.trans (map_zero _).symm))
    refine (exists_unit_of_locally inf_le_left
      ((((pullback G₁.hom (jK R')).presheaf.map (homOfLE (inf_le_right : f ⁻¹ᵁ V k ⊓ Lθ.U i ≤ Lθ.U i)).op).hom
        (θ.f i)) ^ 2) (pow_ne_zero' ht 2) fun y hy => ?_).imp fun c hc => by rwa [map_pow] at hc
    obtain ⟨j, hj⟩ := hcov (f.base y)
    obtain ⟨uk, huk⟩ := hu k j
    obtain ⟨w, hw⟩ := hθ j i
    have hO₁ : f ⁻¹ᵁ (V k ⊓ L2.U j) ⊓ Lθ.U i ≤ f ⁻¹ᵁ L2.U j ⊓ Lθ.U i :=
      inf_le_inf_right _ (f.preimage_mono inf_le_right)
    have hO₂ : f ⁻¹ᵁ (V k ⊓ L2.U j) ⊓ Lθ.U i ≤ f ⁻¹ᵁ (V k ⊓ L2.U j) := inf_le_left
    have hO₃ : f ⁻¹ᵁ (V k ⊓ L2.U j) ⊓ Lθ.U i ≤ f ⁻¹ᵁ V k ⊓ Lθ.U i :=
      inf_le_inf_right _ (f.preimage_mono inf_le_left)
    have e1 := congrArg ((pullback G₁.hom (jK R')).presheaf.map (homOfLE hO₁).op).hom hw
    rw [map_mul, map_pow, res_res, res_res] at e1
    rw [app_res f (inf_le_right : V k ⊓ L2.U j ≤ L2.U j) hO₂, huk, map_mul, map_mul, map_pow, map_pow,
      ← app_res f (inf_le_left : V k ⊓ L2.U j ≤ V k) hO₂] at e1
    refine ⟨_, hO₃, ⟨⟨hy.1, hj⟩, hy.2⟩, resU hO₁ w * resU hO₂ (Units.map (f.app (V k ⊓ L2.U j)).hom.toMonoidHom uk), ?_⟩
    rw [map_pow, res_res, map_pow, e1, Units.val_mul, coe_resU, coe_resU, Units.coe_map, _root_.mul_assoc]
    rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumComponentDegreesDivLeLatticeSlope
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop

namespace GlobalTheory.CovSum

theorem two_le_rdE (D : D7) : 2 ≤ D.host.rdE := by
  have h1 : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.rdE :=
    (UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1
  have hq : (2 : ℝ) ≤ D.host.q := by
    have := D.host.qd_big.1
    exact_mod_cast (by omega : 2 ≤ D.host.q)
  have hd : (2 : ℝ) ≤ D.host.d := by
    have := D.host.qd_big.2
    exact_mod_cast (by omega : 2 ≤ D.host.d)
  have h4 : (2 : ℝ) ≤ Real.sqrt ((D.host.q : ℝ) * D.host.d) := by
    rw [Real.le_sqrt' (by norm_num)]; nlinarith
  linarith

theorem log_two_le (D : D7) (K : Type) [Field K] [NumberField K] (φ : D.host.E →+* K) :
    Real.log 2 ≤ Formalism.HN.logDisc K / (Module.finrank ℚ K : ℝ) := by
  letI : Algebra D.host.E K := φ.toAlgebra
  refine le_trans ?_ (GlobalTheory.FieldSize.log_finrank_rootDiscr_le_of_tower D.host.E K).2
  have h := Real.log_le_log (by norm_num) (two_le_rdE D)
  have hpos : (0 : ℝ) < |((discr D.host.E : ℤ) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero D.host.E)
  unfold Formalism.BasicNotions.Host.rdE at h
  rw [Real.log_rpow (by simpa using hpos)] at h
  simpa [div_eq_inv_mul] using h

theorem slope_sq_nonneg_of_rk_zero {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (hL : L.FG)
    (h0 : Formalism.HN.rkK L = 0) (hK : Real.log 2 ≤ Formalism.HN.logDisc K / (Module.finrank ℚ K : ℝ)) : 0 ≤ slope_sq N L := by
  letI : StarRing K := starRingOfComm
  unfold slope_sq
  split_ifs with h
  · obtain ⟨-, h2, -⟩ := Formalism.HN.plLat K V _ h.some.2.1.1 h.some.2.1.2 (fun v => (h.some.2.2 v).1) L hL
    rw [h0, mul_zero] at h2
    unfold Formalism.HN.rk at h2
    unfold Formalism.HN.muDef Formalism.HN.slope Formalism.F.slope
    rw [h2]
    simp only [Nat.cast_zero, div_zero, mul_zero]
    linarith
  · exact le_rfl

theorem isComplexData {D : D7} (T : Core D) (hQ : T.Q.Pins) {j : ℕ} (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) :
    GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => D.sp.W j) Y.dict := by
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by rw [h.lev.1.2.1, hQ.2.1.1]
  refine ⟨h.lev.2, fun σ hσ => ⟨h.unf σ hσ, ?_, (GlobalTheory.FinalJoin2.volPairEx_and_finVol D (D.sp.W j) (D.sp.W_sig j)).2,
    h.xiAbs σ hσ⟩⟩
  obtain ⟨th, hr, h1, h2⟩ := h.dictU σ hσ
  exact ⟨Y.Kf, th, hr, hM ▸ h.levelK, h1, h2⟩

theorem sum_deg_div_le_mu : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ g τ k, ‖dmin ((Y.U σ).X (Y.dict σ g).1).Gm (Y.dict σ g).2 τ k‖ = 1) → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((Y.U σ).X k)) → ∀ (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)), Y.GoodAt (wtOf (T.Q.Dw j) la 0) → Finite (Comp Y.d.Xo₂ Y.d.c₂) → (∀ Z, GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0)) → 2 * ((∑ᶠ Z, Y.degC la Z) / ∑ᶠ Z, Y.rkC la Z) ≤ Y.mu (wtOf (T.Q.Dw j) la 0) := by
  intro D T j Y e o hT _ hY _ _ la hG hfin _
  obtain ⟨h1, h2⟩ := GlobalTheory.T.componentDegrees_sum_le_total_degree D _ _ _ _ _ _ Y.U (fun _ => D.sp.W j) Y.dict (isComplexData _ hT.pins Y hY) _ hG
  have h3 : (∑ᶠ Z, Y.rkC la Z) = (rankW Y.U (wtOf (T.Q.Dw j) la 0) : ℝ) := by
    haveI := Fintype.ofFinite (Comp Y.d.Xo₂ Y.d.c₂)
    rw [h1, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Nat.cast_sum]
  rw [h3]
  rcases Nat.eq_zero_or_pos (rankW Y.U (wtOf (T.Q.Dw j) la 0)) with h0 | h0
  · rw [h0, Nat.cast_zero, div_zero, mul_zero]
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    exact slope_sq_nonneg_of_rk_zero _ _ hG.2.1 h0 (log_two_le D _ (τ.codRestrict Y.d.c₂.F (Y.d.c₂.conj τ)))
  · have hp : (0 : ℝ) < rankW Y.U (wtOf (T.Q.Dw j) la 0) := by exact_mod_cast h0
    rw [degW_eq] at h2
    rw [← mul_div_assoc, div_le_iff₀ hp]
    change 2 * (∑ᶠ Z, degOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0)) ≤
      slopeW_sq Y.U (xiR D) (fun _ => D.sp.W j) Y.dict (wtOf (T.Q.Dw j) la 0) * _
    linarith

end GlobalTheory.CovSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfRangeSupSmulTopEqTop
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem surjective_of_range_sup_smul_top_eq_top (R : Type) [CommRing R] (M : Type 1)
    [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (f : M →ₗ[R] N)
    (h : ∀ I : Ideal R, I.IsMaximal → LinearMap.range f ⊔ I • (⊤ : Submodule R N) = ⊤) :
    Function.Surjective f := by
  set S := LinearMap.range f

  have key : ∀ I : Ideal R, I.IsMaximal → ¬ Module.annihilator R (N ⧸ S) ≤ I := by
    intro I hI hle
    have hle' : (⊤ : Submodule R (N ⧸ S)) ≤ I • (⊤ : Submodule R (N ⧸ S)) := by
      have h1 := congrArg (Submodule.map S.mkQ) (h I hI)
      rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h1
      have h2 : Submodule.map S.mkQ S = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨x, hx, rfl⟩
        simpa [Submodule.mem_bot] using (Submodule.Quotient.mk_eq_zero S).mpr hx
      rw [h2, bot_sup_eq] at h1
      rw [h1]
    obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I ⊤
      (Module.Finite.fg_top) hle'
    have hrA : r ∈ Module.annihilator R (N ⧸ S) :=
      Module.mem_annihilator.mpr fun m => hr m trivial
    have hrI : r ∈ I := hle hrA
    have h1I : (1 : R) ∈ I := by
      have := I.sub_mem hrI hr1
      simpa using this
    exact hI.ne_top ((Ideal.eq_top_iff_one I).mpr h1I)
  have htop : Module.annihilator R (N ⧸ S) = ⊤ := by
    by_contra hne
    obtain ⟨I, hI, hle⟩ := Ideal.exists_le_maximal _ hne
    exact key I hI hle
  have hS : S = ⊤ := by
    rw [eq_top_iff]
    intro n _
    have h1 : (1 : R) ∈ Module.annihilator R (N ⧸ S) := htop ▸ Submodule.mem_top
    have h2 := Module.mem_annihilator.mp h1 (S.mkQ n)
    rw [one_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
    exact h2
  exact LinearMap.range_eq_top.mp hS

example : ∀ (R : Type) [CommRing R] (M : Type 1) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N] (f : M →ₗ[R] N), (∀ I : Ideal R, I.IsMaximal → LinearMap.range f ⊔ I • (⊤ : Submodule R N) = ⊤) → Function.Surjective f := @surjective_of_range_sup_smul_top_eq_top

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfSurjectiveOnPointsStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_of_surjective_on_points : ∀ (A X : Over (Sp ℂ)) [GrpObj A] [GrpObj X] (ψ : A ⟶ X), IsAbelianScheme A → IsAbelianScheme X →
    (∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ X, ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ ψ = y) → Surjective ψ.left := by
  first | exact @GlobalTheory.ComplexAbVarSurj.surjective_of_surjective_points | exact GlobalTheory.ComplexAbVarSurj.surjective_of_surjective_points | (intros; apply GlobalTheory.ComplexAbVarSurj.surjective_of_surjective_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricOfLineBundleIsoPullGroupHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem sym_of_lbIso_pull_hom : ∀ (S : Scheme.{0}) (H H' : Over S) [GrpObj H] [GrpObj H'] (f : H ⟶ H'), IsMonHom f →
    ∀ (N : LB H'.left) (M : LB H.left), N.IsLB → M.IsLB → Out.Sym H' N → LBIso (N.pull f.left) M → Out.Sym H M := by
  intro S H H' _ _ f hf N M hN hM hs hiso s
  obtain ⟨U, hU, t, ht⟩ := hs s
  refine ⟨U, hU, ?_⟩
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  have hw' := (isGen_iff w).1 hw
  obtain ⟨n, hn⟩ : ∃ n : (H.hom ⁻¹ᵁ U).toScheme ⟶ (H'.hom ⁻¹ᵁ U).toScheme,
      n ≫ (H'.hom ⁻¹ᵁ U).ι = (H.hom ⁻¹ᵁ U).ι ≫ f.left :=
    ⟨IsOpenImmersion.lift _ ((H.hom ⁻¹ᵁ U).ι ≫ f.left) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q y.1 ∈ U) (Over.w f)).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
  have hi : (GrpObj.inv : H ⟶ H).left ≫ f.left = f.left ≫ (GrpObj.inv : H' ⟶ H').left :=
    congrArg (fun q => q.left) (GrpObj.inv_hom f)
  let ψ : Fin 2 → ((H.hom ⁻¹ᵁ U).toScheme ⟶ H.left) :=
    ![(H.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : H ⟶ H).left, (H.hom ⁻¹ᵁ U).ι]
  obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame N (fun k => ψ k ≫ f.left) _ ![1, -1] n (fun k => by
    fin_cases k
    · show ((H.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : H ⟶ H).left) ≫ f.left =
        n ≫ (H'.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : H' ⟶ H').left
      rw [← Category.assoc n, hn, Category.assoc, Category.assoc, hi]
    · show (H.hom ⁻¹ᵁ U).ι ≫ f.left = n ≫ (H'.hom ⁻¹ᵁ U).ι
      rw [hn])) t ht
  exact exists_down hw' hN hM (φ' := ψ) c₂ h₂

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPullbackGeneratorEvenValueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricPullbackGenerator_even_value : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) (f : D₀.P.A ⟶ D₀.P.A) [IsMonHom f]
    (uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ f) GlobalTheory.UTau0.w0ε)), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ (T : Over (Sp R)) (x : T ⟶ D₀.P.A) (z : T.left) (J : (T.left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D₀.P.L z J →
      val uw x⁻¹.left z J * val D₀.sym x.left z J * cubV D₀.cub z J (x ≫ f) (x ≫ f)⁻¹ x⁻¹ =
        val uw x.left z J * cubV D₀.cub z J x x⁻¹ (x ≫ f) := by
  first | exact @GlobalTheory.UTau0.uw_even_val | exact GlobalTheory.UTau0.uw_even_val | (intros; apply GlobalTheory.UTau0.uw_even_val <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPullbackGeneratorSecondDifferenceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricPullbackGenerator_second_difference : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) (f g : D₀.P.A ⟶ D₀.P.A) [IsMonHom f] [IsMonHom g],
    padd D₀.P.A f g = 𝟙 D₀.P.A →
    ∀ uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ f) GlobalTheory.UTau0.w0ε), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ u : LB.Gen (LB.LinComb D₀.P.L (rosatiφ D₀.P.A f g) rosatiε), u.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ u (zero2 D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ (T : Over (Sp R)) (x x' : T ⟶ D₀.P.A) (z : T.left) (J : (T.left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D₀.P.L z J →
      val uw (x * x').left z J * cubV D₀.cub z J (x' ≫ f) (x' ≫ g) x =
        val uw x.left z J * val uw x'.left z J * val u (lift x x').left z J *
          cubV D₀.cub z J (x ≫ f) (x' ≫ f) x * cubV D₀.cub z J (x ≫ f) (x' ≫ f) x' *
          cubV D₀.cub z J x x' ((x ≫ f) * (x' ≫ f)) := by
  first | exact @GlobalTheory.UTau0.SecondDiff.uw_second_diff | exact GlobalTheory.UTau0.SecondDiff.uw_second_diff | (intros; apply GlobalTheory.UTau0.SecondDiff.uw_second_diff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTrivialisationOfBalancedBimultiplicativStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_trivialisation_of_balanced_bimultiplicative : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B →
    ∀ (M : RigLB B) (cub : CubicalStr B M) (O : Type) [CommRing O] [StarRing O] (act : RingAct B O),
    (∀ a : O, RosatiAdj B M.L (act.act a) (act.act (star a))) →
    ∀ (X : Type) [AddCommGroup X] [Module O X] (c : X → (𝟙_ (Over (Sp R)) ⟶ B)), (∀ y y', c (y + y') = c y * c y') →
    (∀ (a : O) (y : X), c (a • y) = c y ≫ act.act a) → ∀ w0 : O, w0 + star w0 = 1 →
    ∀ τ : ∀ y z : X, LB.Gen (LB.LinComb M.L (GlobalTheory.PolDeg.lamPts (c y) (c z)) GlobalTheory.PolDeg.negε), GlobalTheory.UTau0.BalTau M cub act c τ →
    ∃ τ' : ∀ y z : X, LB.Gen (LB.LinComb M.L (GlobalTheory.PolDeg.lamPts (c y) (c z)) GlobalTheory.PolDeg.negε), GlobalTheory.UTau0.BalTau M cub act c τ' ∧
      ∀ y z p J, Good M.L p J → val (τ' y z) (𝟙 _) p J = val (τ' z y) (𝟙 _) p J := by
  first | exact @GlobalTheory.SymTau.symm_of_bal | exact GlobalTheory.SymTau.symm_of_bal | (intros; apply GlobalTheory.SymTau.symm_of_bal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelTwistBySimilitudeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticLevel_twist_by_similitude : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (T : Over S) (t₁ : T.left ⟶ Sp (cycAway M))
    (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)), SympCond o h M T t₁ lv →
    ∀ (a : sympSimGrp h M) (n : ℕ) (σ : cycAway M →+* cycAway M), IsMultOf a n →
      σ (zetaAway M) = zetaAway M ^ n → SympCond o h M T (t₁ ≫ spMap σ) (sympTwist a lv) := by
  first | exact @GlobalTheory.HTSympCover.sympCond_twist | exact GlobalTheory.HTSympCover.sympCond_twist | (intros; apply GlobalTheory.HTSympCover.sympCond_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzPeriodsOfTangent
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

variable {E : Type} [Field E] [NumberField E] {I : Type} {𝔠 : FracId (FR E)} {R : Subring ℂ}

theorem sz_period_of_tangent {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} {φ : I → E →+* ℂ} {L : Set E}
    {X₀ : Obj (FR E) 𝔠 (Sp R)} {X : Obj (FR E) 𝔠 (Sp ℂ)} {U : Unif φ L 0 X} {p : X.A.left ⟶ X₀.A.left} {i : I}
    {e : X₀.Lie →ₗ[R] R} {a Ω : ℂ} {r : ℝ} (hR : IsPlaceRing E l lam R) (he : IsPeriodGen X₀ U p i e a)
    {v : X₀.Lie} {v' : X.Lie} {W : Fin (Module.finrank ℚ (FR E)) → ℂ} (hv : Obj.LieCorr R.subtype p v v')
    (hW : U.u.IsDiff W v'.hom) (hW0 : W (U.e.symm i) ≠ 0) (hs : Sz l lam r ((W (U.e.symm i) * Ω)⁻¹)) :
    Sz l lam r (a / Ω) := by
  have h := he v v' W hv hW
  have ha : a / Ω = ((e v : R) : ℂ) * (W (U.e.symm i) * Ω)⁻¹ := by
    rw [h, _root_.mul_inv, div_eq_mul_inv,
      show a * W (U.e.symm i) * ((W (U.e.symm i))⁻¹ * Ω⁻¹) = a * Ω⁻¹ * (W (U.e.symm i) * (W (U.e.symm i))⁻¹) by ring,
      mul_inv_cancel₀ hW0, _root_.mul_one]
  rw [ha]
  simpa using GlobalTheory.LatValRam.sz_mul (hR.2.1 _ (e v).2) hs

end GlobalTheory.LatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFlagHodgeIndexVanishingStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_flag_hodge_index_vanishing : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (ι : Type) [Fintype ι] [DecidableEq ι] (X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → X ≫ Xo.s = sOf c _ → spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x → ∀ N : ι → GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, (∀ k, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c (Pi.single k (1 : K))).toRingHom ≫ X) (N k)) → ∀ M : ι → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) (∑ k, M k • N k) := by
  first | exact @GlobalTheory.FlagTan.isKS_dir_sum | exact GlobalTheory.FlagTan.isKS_dir_sum | (intros; apply GlobalTheory.FlagTan.isKS_dir_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateStatementHoldsStatement
section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_statement_holds : TateSt := by
  first | exact @GlobalTheory.FlatModel.tateSt | exact GlobalTheory.FlatModel.tateSt | (intros; apply GlobalTheory.FlatModel.tateSt <;> assumption)
end

