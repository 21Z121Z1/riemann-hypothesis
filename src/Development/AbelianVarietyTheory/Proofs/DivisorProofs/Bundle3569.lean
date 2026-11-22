import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTwistOfLowers
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3523
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3557
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3553
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0742
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3558
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2559
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3564
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3068
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceUniqueLiftAnyField
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3559
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3560

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjectMapsOfDualNumberIdentifications
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.EpsObj

theorem act_comm_eps : ∀ (k : Type) [Field k] {S : Scheme.{0}} (G' : Over (Sp (DualNumber k))) [GrpObj G'], IsAbelianScheme G' → ∀ (G : Over S) [GrpObj G] (g₂ : Sp (DualNumber k) ⟶ S) (φ₁ φ₂ : G'.left ⟶ G.left), IsGrpPullback G' G g₂ φ₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ G'.left) (y : Z ⟶ Sp k), x ≫ G'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ φ₁ = x ≫ φ₂) → ∀ (u : G' ⟶ G') [IsMonHom u] (v : G ⟶ G) [IsMonHom v], u.left ≫ φ₁ = φ₁ ≫ v.left → u.left ≫ φ₂ = φ₂ ≫ v.left := GlobalTheory.T.commutes_of_commutes_dualNumber_agree_closed

theorem sec_eps : ∀ (k : Type) [Field k] {S : Scheme.{0}} (G' : Over (Sp (DualNumber k))) [GrpObj G'], IsAbelianScheme G' → ∀ (G : Over S) [GrpObj G] (g₁ g₂ : Sp (DualNumber k) ⟶ S) (φ₁ φ₂ : G'.left ⟶ G.left), IsGrpPullback G' G g₂ φ₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ G'.left) (y : Z ⟶ Sp k), x ≫ G'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ φ₁ = x ≫ φ₂) → spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ g₁ = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ g₂ → ∀ (n : ℕ), (n : k) ≠ 0 → ∀ (σ : 𝟙_ (Over S) ⟶ G), σ ^ n = 1 → ∀ (x : 𝟙_ (Over (Sp (DualNumber k))) ⟶ G'), x ^ n = 1 → x.left ≫ φ₁ = g₁ ≫ σ.left → x.left ≫ φ₂ = g₂ ≫ σ.left := GlobalTheory.T.dualNumber_torsionSection_lies_over_second_map

theorem spMap_comp_eps {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem eta_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (p : Obj D l bb s) (a : D.La) (n : ℕ) :
    p.eta a ^ n = p.eta (n • a) := by
  induction n with
  | zero =>
    have h := p.eta_add 0 0
    rw [add_zero] at h
    rw [pow_zero, zero_smul]
    exact (mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)).symm
  | succ n ih => rw [pow_succ, ih, succ_nsmul, p.eta_add]

theorem etaA_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (p : Obj D l bb s) (a : D.La) (n : ℕ) :
    p.etaA a ^ n = p.etaA (n • a) := by
  induction n with
  | zero =>
    have h := p.etaA_add 0 0
    rw [add_zero] at h
    rw [pow_zero, zero_smul]
    exact (mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)).symm
  | succ n ih => rw [pow_succ, ih, succ_nsmul, p.etaA_add]

theorem eta_pow_M {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (p : Obj D l bb s) (a : D.La) :
    p.eta a ^ l.M = 1 := by
  rw [eta_pow]
  apply p.eta_ker
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := Ideal.subset_span rfl
    rw [← l.prod] at this
    first | exact Ideal.mul_le_left this | exact Ideal.mul_le_right this
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul hM Submodule.mem_top

theorem etaA_pow_A {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (p : Obj D l bb s) (a : D.La) :
    p.etaA a ^ l.A = 1 := by
  rw [etaA_pow]
  exact p.etaA_ker a

theorem exists_objMaps : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} (c : Coeff l) (W : Type) [CommRing W] (b : c.F →+* W) (o : LowObj D' c b) (k : Type) [Field k] (f : W →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ o.t.G.left), IsGrpPullback B' o.t.G (spMap f) π₁ → IsGrpPullback B' o.t.G (spMap (GlobalTheory.RigChart.constHom f)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → LBIso (o.t.PP.L.pull π₁) (o.t.PP.L.pull π₂) → ∃ (o' : LowObj D' c (f.comp b)) (m₁ : ObjMap o' o (spMap f)) (m₂ : ObjMap o' o (spMap (GlobalTheory.RigChart.constHom f))) (io : o'.t.G.left ≅ B'.left), io.hom ≫ B'.hom = o'.t.G.hom ∧ m₁.toSABMap.φ = io.hom ≫ π₁ ∧ m₂.toSABMap.φ = io.hom ≫ π₂ := by
  intro E _ _ _ H D' l c W _ b o k _ f B' _ π₁ π₂ h₁ h₂ h0 hL
  have hlow : lowMap c (f.comp b) = spMap f ≫ lowMap c b := by
    unfold lowMap
    rw [RingHom.comp_assoc, spMap_comp_eps]
  obtain ⟨o', ⟨m₀⟩⟩ : ∃ o' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) (lowMap c (f.comp b)),
      Nonempty (ObjMap o' o (spMap f)) := by
    rw [hlow]
    exact GlobalTheory.LevelGroup.pull_univ o (spMap f)
  let io : o'.t.G.left ≅ B'.left := IsPullback.isoIsPullback _ _ m₀.cart.1 h₁.1
  have io₁ : io.hom ≫ π₁ = m₀.toSABMap.φ := IsPullback.isoIsPullback_hom_fst _ _ _ _
  have io₂ : io.hom ≫ B'.hom = o'.t.G.hom := IsPullback.isoIsPullback_hom_snd _ _ _ _
  have hio : IsGrpPullback o'.t.G B' (𝟙 _) io.hom :=
    IsGrpPullback.cancel h₁ (by rw [Category.id_comp, io₁]; exact m₀.cart) (by rw [io₂, Category.comp_id])
  have hψc : IsGrpPullback o'.t.G o.t.G (spMap (GlobalTheory.RigChart.constHom f)) (io.hom ≫ π₂) := by
    have := hio.comp h₂
    rwa [Category.id_comp] at this
  have h0' : ∀ (Z : Scheme.{0}) (x : Z ⟶ o'.t.G.left) (y : Z ⟶ Sp k),
      x ≫ o'.t.G.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom →
        x ≫ m₀.toSABMap.φ = x ≫ io.hom ≫ π₂ := by
    intro Z x y hx
    rw [← io₁, ← Category.assoc, ← Category.assoc]
    exact h0 Z (x ≫ io.hom) y (by rw [Category.assoc, io₂, hx])
  have hA' : IsAbelianScheme o'.t.G :=
    ⟨o'.t.semi.comm, o'.t.semi.smooth, o'.proper, o'.t.semi.geomConnected⟩
  have hact : ∀ a, (o'.t.act.act a).left ≫ io.hom ≫ π₂ = (io.hom ≫ π₂) ≫ (o.t.act.act a).left := fun a => by
    haveI := o'.t.act.hom a
    haveI := o.t.act.hom a
    exact act_comm_eps k o'.t.G hA' o.t.G _ _ _ hψc h0' (o'.t.act.act a) (o.t.act.act a) (m₀.act a)
  have hLB : LBIso o'.t.PP.L (o.t.PP.L.pull (io.hom ≫ π₂)) := by
    obtain ⟨w, hw, -⟩ := m₀.lin
    have e₁ : LBIso o'.t.PP.L (o.t.PP.L.pull (io.hom ≫ π₁)) := by
      rw [io₁]
      exact ⟨w, hw⟩
    have e₂ : LBIso (o.t.PP.L.pull (io.hom ≫ π₁)) (o.t.PP.L.pull (io.hom ≫ π₂)) :=
      GlobalTheory.GenSpread.lbIso_pull_comp io.hom rfl rfl hL
    exact LBIso.trans o'.t.PP.isLB (pull_isLB o.t.PP.isLB _) (pull_isLB o.t.PP.isLB _) e₁ e₂
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_sabMap_of_grpPullback_respecting_action_bundle o'.t o.t (spMap (GlobalTheory.RigChart.constHom f)) (io.hom ≫ π₂) o.proper hψc hact hLB
  have hg : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap f =
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (GlobalTheory.RigChart.constHom f) := by
    rw [← spMap_comp_eps, ← spMap_comp_eps]
    congr 1
  have hunit : ∀ n : ℕ, 0 < n → (n : k) ≠ 0 := by
    intro n hn
    have := ((baseKA (LowDat.lowLevel l)).unit n hn).map
      (((TrivSqZeroExt.fstHom k k k).toRingHom.comp (f.comp b)).comp
        (IntermediateField.inclusion (LowDat.ka_le l c)).toRingHom)
    rw [map_natCast] at this
    exact this.ne_zero
  have hsec : ∀ (σ : 𝟙_ (Over (Sp W)) ⟶ o.t.G) (x : 𝟙_ (Over (Sp (DualNumber k))) ⟶ o'.t.G) (n : ℕ), 0 < n →
      σ ^ n = 1 → x ^ n = 1 → x.left ≫ m₀.toSABMap.φ = spMap f ≫ σ.left →
        x.left ≫ io.hom ≫ π₂ = spMap (GlobalTheory.RigChart.constHom f) ≫ σ.left :=
    fun σ x n hn hσ hx hx₁ => sec_eps k o'.t.G hA' o.t.G _ _ _ _ hψc h0' hg n (hunit n hn) σ hσ x hx hx₁
  have hMpos : 0 < (LowDat.lowLevel l).M := by have := (LowDat.lowLevel l).three_le; omega
  let m₂ : ObjMap o' o (spMap (GlobalTheory.RigChart.constHom f)) :=
    { toSABMap := m
      eta := fun a => by
        show (o'.eta a).left ≫ m.φ = _
        rw [hm]
        exact hsec _ _ _ hMpos (eta_pow_M o a) (eta_pow_M o' a) (m₀.eta a)
      etaA := fun a => by
        show (o'.etaA a).left ≫ m.φ = _
        rw [hm]
        exact hsec _ _ _ (LowDat.lowLevel l).A_pos (etaA_pow_A o a) (etaA_pow_A o' a) (m₀.etaA a) }
  exact ⟨o', m₀, m₂, io, io₂, io₁.symm, hm⟩

end GlobalTheory.UCanon.EpsObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeTransversalIsotropicStatement
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_opposite_transversal_isotropic : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → Cois D y n → ∀ Z Z₀ : Submodule (𝓞 E) D.La, IsOpp D Z Z₀ →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X →
    ∃ Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' ∧ ∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e := by
  first | exact @GlobalTheory.LowFilt.exists_opp_transv | exact GlobalTheory.LowFilt.exists_opp_transv | (intros; apply GlobalTheory.LowFilt.exists_opp_transv <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodsMonomialFamilyCoordsOverBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.Periods

theorem inv_eq_unit_mul {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R)
    (g : D.X → (FractionRing R)ˣ) {y : D.X} {r : R} (hr : Formalism.L2.Pj.PsiCoord D y r)
    (hU : PsiUnitOn (GlobalTheory.PolDeg.rescale D g) y Set.univ) :
    ∃ u : Rˣ, (((g y)⁻¹ : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ u * algebraMap R _ r := by
  obtain ⟨v, hv⟩ := GlobalTheory.LocM.FJ.MultiData.exists_unit_psiCoord (GlobalTheory.TauTwist.rescale D g) y hU
  obtain ⟨x, ⟨j, h, hj, rfl⟩, e⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D y r).1 hr
  obtain ⟨x', hx', e'⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff (GlobalTheory.TauTwist.rescale D g) y _).1 hv
  have h₁ : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsPsiCoord (GlobalTheory.TauTwist.rescale D g) y (g y * GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal (D.psi y) j h) := by
    refine ⟨j, h, hj, ?_⟩
    dsimp only [GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal, GlobalTheory.TauTwist.rescale, GlobalTheory.TauTwist.withPsi, ReciprocityTheory.ChartRestriction.G.DVR.scaleGen]
    rw [map_mul, map_mul, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.res_res]
    congr 1
    ext
    show (g y : FractionRing R) = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom
      (((Sp (FractionRing R)).presheaf.map (𝟙 _)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (g y : FractionRing R)))
    rw [CategoryTheory.Functor.map_id]
    exact ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply _).symm
  obtain ⟨u, hu⟩ := h₁.unique hx'
  have k := congrArg Units.val hu
  rw [Units.val_mul, Units.val_mul, e, e'] at k
  have k' : (g y : FractionRing R) * algebraMap R _ r = algebraMap R _ ((u * v : Rˣ) : R) := by
    rw [k, Units.val_mul, map_mul]; rfl
  refine ⟨(u * v)⁻¹, ?_⟩
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [mul_left_comm, k', ← map_mul, Units.inv_mul, map_one]

theorem exists_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V) (D' : Datum H) (L : LowBase D' c) (θ₀ : L.W →+* V) (e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (β : C.P.D.toPre.P.A.left ⟶ L.D.P.A.left), IsGrpPullback C.P.D.toPre.P.A L.D.P.A (spMap θ₀) β → (letI := H.starRing; ∀ a : 𝓞 E, (C.P.oD.onB.act a).left ≫ β = β ≫ (L.oa.onB.act a).left) → LBIso C.P.D.toPre.P.L (L.D.P.L.pull β) → (∀ y, (C.P.D.toPre.c y).left ≫ β = spMap θ₀ ≫ (L.D.c (l.M' • e y)).left) → ∀ (N : ℕ) (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar L.D.X)), (∀ i, C.δ i = pull e.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X)) → ∃ s : Fin C.m ⊕ Fin N → V, (∀ i, Associated (s (.inl i)) (C.s i)) ∧ (∀ j, IsUnit (s (.inr j))) ∧ DivFrom L C.P.D.toPre C.P.oD θ₀ s (fun k => (ε k : LinearMap.BilinForm ℤ L.D.X)) e := by
  intro E _ _ _ H Dw l Xo c φ V _ _ _ hV hk C D' L θ₀ e β hβ hact hL hc N ε hε
  letI := H.starRing
  obtain ⟨-, hbm, hgen, o₀, ho₀, hw₀⟩ := GlobalTheory.T.degenerationDataNsmulRescale_keeps_laws L.W L.D (𝓞 E) L.oa H.w0 l.M' L.even L.bimult L.w0 L.gen
  letI : Module (𝓞 E) (mulDeg L.D l.M').X := L.mod
  obtain ⟨g, hD, q, hxe, hpr, hU, qs, qa, qb, hg⟩ := GlobalTheory.T.degData_differ_by_symmBalancedForm_of_psi_tau (H := H) θ₀ (mulDeg L.D l.M') o₀ C.P.D.toPre C.P.oD e β
    hbm hgen hw₀ C.P.D.tau_bimult C.P.w0 hβ (fun a => by rw [ho₀]; exact hact a) hL hc
  have hM : IsUnit ((l.M' : ℕ) : V) := by
    have h1 : IsUnit ((l.M' : ℕ) : c.F) := (Nat.cast_ne_zero.2 (level_pos l).ne').isUnit
    simpa using h1.map C.b
  obtain ⟨s, hs₁, hs₂, hs⟩ := GlobalTheory.T.exists_unit_coords_balancedSymmetric_roots H L.D.X V hV.1.2.2.2 hk l.M' hM C.m N ε C.s C.s_ne_zero
    (fun a b => q (e.symm a) (e.symm b)) (fun a b => qs _ _) (fun a a' b => by simp only [map_add, qa])
    (fun x a b => by simp only [map_smul, qb]) (fun y => by
      obtain ⟨y, rfl⟩ := e.surjective y
      obtain ⟨u, n, hn, hco⟩ := C.mono y
      obtain ⟨v, hv⟩ := inv_eq_unit_mul _ g hco (hU y)
      refine ⟨v * u, ?_⟩
      rw [map_smul, e.symm_apply_apply, ← hg, hv, Units.val_mul, map_mul, map_mul, map_prod, _root_.mul_assoc]
      congr 2
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_pow, ← zpow_natCast]
      congr 1
      have h1 := apply_self_eq_two_mul ((balForms_eq_levelForms H L.D.X).le (ε (.inl i)).2) (e y)
      have h2 := hn i
      rw [LinearMap.smul_apply, LinearMap.smul_apply, hε, pull_apply, LinearEquiv.coe_coe, h1, smul_eq_mul] at h2
      linarith)
  refine ⟨s, hs₁, hs₂, g, hD, fun y => ?_, hxe, fun x => ?_⟩
  · rw [hg, ← hs, map_smul, e.symm_apply_apply]
  · have := hact x
    rw [← hpr] at this
    exact this.trans (Category.assoc _ _ _)

end GlobalTheory.UCanon.Periods
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedSymmetricCubicalBundleExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rigidified_symmetric_cubicalBundle_extension : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∃ (PP : RigLB G) (cub : CubicalStr G PP), PP.IsSymmetric ∧ ∃ cm : CubeMap tF.G G, cm.F = e ∧ cm.e = j ∧ cm.IsPullCubical tF.cub cub := by
  first | exact @GlobalTheory.BundleExt.exists_rigLB_cubical_symm | exact GlobalTheory.BundleExt.exists_rigLB_cubical_symm | (intros; apply GlobalTheory.BundleExt.exists_rigLB_cubical_symm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaClassSumTermsRootsOfUnityStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaClassSum_terms_rootsOfUnity : (∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∃ t : (Fin 8 → c.T.D.toPre.X) → X₁.S.HH X₁.M z₁ → PadicAlgCl p, (∀ μ κ, ‖t μ κ‖ ≤ Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ (∀ μ, ∃ κ, ‖t μ κ‖ = Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset (Fin 8 → c.T.D.toPre.X), ∀ S : Finset (Fin 8 → c.T.D.toPre.X), (∀ μ ∈ S, ∀ u, CongMod D.m (μ u) (ν u)) → (∀ μ ∈ S₀, (∀ u, CongMod D.m (μ u) (ν u)) → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (U κ * GSum.part D z₁ z₂ a κ) - ∑ μ ∈ S, t μ κ‖ ≤ δ) := by
  first | exact @GlobalTheory.Poinc.GSum.terms_and_sums | exact GlobalTheory.Poinc.GSum.terms_and_sums | (intros; apply GlobalTheory.Poinc.GSum.terms_and_sums <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaMemberThroughModelPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.Thru

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_stalkHom {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (z : M.Z) :
    spMap (M.stalkHom z) ≫ M.Z.fromSpecStalk z = M.pt := by
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) M.pt
  have h2 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (M.pt_specializes (IsLocalRing.closedPoint Ω) z)
  refine Eq.trans ?_ h1
  rw [← h2, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem isFractionRing_stalk {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (z : M.Z) :
    letI : Algebra (M.Z.presheaf.stalk z) Ω := (M.stalkHom z).toAlgebra
    IsFractionRing (M.Z.presheaf.stalk z) Ω := by
  letI : Algebra (M.Z.presheaf.stalk z) Ω := (M.stalkHom z).toAlgebra
  have : FaithfulSMul (M.Z.presheaf.stalk z) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (M.stalkHom_injective z)
  refine IsFractionRing.of_field _ _ fun x => ?_
  obtain ⟨a, b, -, hx⟩ := IsFractionRing.div_surjective (A := M.O z) x
  refine ⟨(M.stalkEquiv z).symm a, (M.stalkEquiv z).symm b, ?_⟩
  have h : ∀ c : M.O z, algebraMap (M.Z.presheaf.stalk z) Ω ((M.stalkEquiv z).symm c) = c := fun c => by
    change M.stalkHom z _ = _
    rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
  rw [h, h, ← hx]
  rfl

theorem exists_cdvr_thru {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] [CharZero Ω]
    (M : RatModel o Ω) (z : M.Z) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (φ : M.Z.presheaf.stalk z →+* V)
      (e : Ω →+* FractionRing V), IsAdicComplete (maximalIdeal V) V ∧ CharZero V ∧ IsLocalHom φ ∧
      (∀ r, e (M.stalkHom z r) = algebraMap V (FractionRing V) (φ r)) ∧
      jK V ≫ spMap φ ≫ M.Z.fromSpecStalk z = spMap e ≫ M.pt := by
  letI : Algebra (M.Z.presheaf.stalk z) Ω := (M.stalkHom z).toAlgebra
  haveI := isFractionRing_stalk M z
  haveI : CharZero (M.Z.presheaf.stalk z) := (M.stalkHom z).charZero
  haveI := M.lft
  haveI : IsLocallyNoetherian (Sp o) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of o)))
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  obtain ⟨V₀, _, _, _, φ₀, ⟨hdvr, hcpl, hchar⟩, hinj₀, hmax⟩ :=
    GlobalTheory.ClosedPol.exists_cdvr (M.Z.presheaf.stalk z) (maximalIdeal _)
  have hl : IsLocalHom φ₀ := ((IsLocalRing.local_hom_TFAE φ₀).out 0 4).2 hmax
  have hg₀ : Function.Injective ((algebraMap V₀ (FractionRing V₀)).comp φ₀) :=
    (IsFractionRing.injective V₀ (FractionRing V₀)).comp hinj₀
  let emb : Ω →+* FractionRing V₀ := IsFractionRing.lift (A := M.Z.presheaf.stalk z) hg₀
  have hemb : ∀ r, emb (M.stalkHom z r) = algebraMap V₀ (FractionRing V₀) (φ₀ r) := fun r =>
    IsFractionRing.lift_algebraMap (A := M.Z.presheaf.stalk z) hg₀ r
  refine ⟨V₀, inferInstance, inferInstance, hdvr, φ₀, emb, hcpl, hchar, hl, hemb, ?_⟩
  rw [← spMap_stalkHom, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [show jK V₀ = spMap (algebraMap V₀ (FractionRing V₀)) from rfl, spMap_spMap, spMap_spMap]
  congr 1
  ext r
  exact (hemb r).symm

theorem exists_gMem_of_trait : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), GlobalTheory.GSep.ZHAbove X₁ Y πY → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → CharZero V → ∀ (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), IsLocalHom ev → ∀ (ξ : Sp V ⟶ Y.Z) (e : X₁.Ω₁ →+* FractionRing V), ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ → jK V ≫ ξ = spMap e ≫ Y.pt → ∃ (X : Type) (_ : AddCommGroup X) (t : X → V) (δ : I → X → X), Nonempty (GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) := by
  intro I X₁ z₁ act hact Y πY hY V _ _ _ hcpl hchar ev hev ξ e hξ hjξ
  obtain ⟨U₀, EE, ⟨O⟩, hO, -, hhom, -⟩ := hY
  have hπ : Y.pt ≫ πY = X₁.M.pt :=
    hhom.trans ((congrArg (· ≫ X₁.M.pt) (Spec.map_id _)).trans (Category.id_comp _))
  obtain ⟨ψ, hψ, hψL, hψE⟩ := GlobalTheory.T.zarhinModel_genericFibre_isPullback_thetaSystem X₁ Y U₀ EE O hO
  have hab : (ξ ⁻¹' abLocus O.G).Nonempty := by
    refine ⟨jK V (closedPoint (FractionRing V)), ?_⟩
    have e1 : ξ (jK V (closedPoint (FractionRing V))) = Y.pt (spMap e (closedPoint (FractionRing V))) :=
      congrArg (fun f : Sp (FractionRing V) ⟶ Y.Z => f (closedPoint (FractionRing V))) hjξ
    rw [Set.mem_preimage, e1]
    exact GlobalTheory.Mum.CoverPull.pt_mem_abLocus _ _ X₁.S X₁.ρ Y U₀ EE hO O _
  obtain ⟨D, A, U, β, hβ, hβL, hβE⟩ := GlobalTheory.T.exists_uniformisation_at_completeTrait_of_model X₁ Y U₀ EE O V hcpl hchar ξ e hjξ hab
  have hpt : jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ = spMap e ≫ X₁.M.pt := by
    rw [← hξ, ← Category.assoc, hjξ, Category.assoc, hπ]
  have hend : ∀ a, ∃ E : EndU U.toUnifPre, E.aA.left ≫ (β ≫ ψ) = (β ≫ ψ) ≫ (act a).left := by
    intro a
    obtain ⟨F, hF, hFψ⟩ := hψE (act a) (hact a)
    obtain ⟨E, hE⟩ := hβE F hF
    refine ⟨E, ?_⟩
    rw [← Category.assoc, hE, Category.assoc, hFψ, Category.assoc]
  choose E hE using hend
  have hV : IsCN V := ⟨inferInstance, inferInstance, hcpl, hchar⟩
  have hpsi : ∀ mu : D.toPre.X, ∃ r : V, Formalism.L2.Pj.PsiCoord D.toPre mu r := fun mu => by
    obtain ⟨r, hr, -⟩ := (PsiCoordLocal.main V D hV.2.1 mu).1
    exact ⟨r, hr⟩
  choose t ht using hpsi
  obtain ⟨wl, hwl⟩ := LBIso.trans A.isLB (pull_isLB (pull_isLB O.L.isLB _) _) (pull_isLB X₁.ρ.P.isLB _) hβL
    (lbIso_pull_comp hψL β)
  refine ⟨D.toPre.X, inferInstance, t, fun a => (E a).h, ⟨{
    cn := hV
    loc := hev
    reg := fun a _ => ?_
    yK := e.comp X₁.S.R.val.toRingHom
    yK_eq := fun a => ?_
    D := D
    e₈ := AddEquiv.refl _
    G := (Over.pullback ξ).obj O.G
    semi := IsSemiAbelian.pullback _ _ O.semi
    A := A
    U := U
    φ := β ≫ ψ
    cart := (hβ.comp hψ).congr (spMap_spMap e X₁.S.R.val.toRingHom) rfl
    wl := wl
    wl_gen := hwl
    equiv := fun a => ⟨E a, hE a, fun _ => rfl⟩
    psi := fun mu => ⟨1, by simpa using ht mu⟩ }⟩⟩
  · rw [hpt]
    change a ∈ X₁.M.O (X₁.M.pt ((spMap e) (closedPoint (FractionRing V))))
    rw [X₁.M.pt_apply, RatModel.O_genericPoint]
    trivial
  · rw [hpt, GlobalTheory.FieldPts.val_spMap, RatModel.val_pt]
    rfl

theorem exists_gMem_thru : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), GlobalTheory.GSep.ZHAbove X₁ Y πY → ∀ y : Y.Z, πY y = z₁ → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (_ : IsDiscreteValuationRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) (_ : AddCommGroup X) (t : X → V) (δ : I → X → X) (𝔫 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (ξ : Sp V ⟶ Y.Z), ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ∧ ξ (closedPoint V) = y ∧ Function.Injective ev := by
  intro I X₁ z₁ act hact Y πY hY y hy
  subst hy
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  obtain ⟨V, _, _, hdvr, φ₀, emb, hcpl, hchar, hl₀, -, hptY⟩ := exists_cdvr_thru Y y
  have hπ : Y.pt ≫ πY = X₁.M.pt := by
    obtain ⟨-, -, -, -, -, hhom, -⟩ := hY
    refine Eq.trans hhom ?_
    exact (congrArg (· ≫ X₁.M.pt) (Spec.map_id _)).trans (Category.id_comp _)
  let s : X₁.M.Z.presheaf.stalk (πY y) →+* Y.Z.presheaf.stalk y := (πY.stalkMap y).hom
  have hs : spMap s ≫ X₁.M.Z.fromSpecStalk (πY y) = Y.Z.fromSpecStalk y ≫ πY :=
    Scheme.SpecMap_stalkMap_fromSpecStalk πY
  haveI hsl : IsLocalHom s := inferInstanceAs (IsLocalHom (πY.stalkMap y).hom)
  let ev : X₁.M.Z.presheaf.stalk (πY y) →+* V := φ₀.comp s
  have hξ : (spMap φ₀ ≫ Y.Z.fromSpecStalk y) ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y) := by
    rw [Category.assoc, ← hs, ← Category.assoc, spMap_spMap]
  have hjξ : jK V ≫ spMap φ₀ ≫ Y.Z.fromSpecStalk y = spMap emb ≫ Y.pt := hptY
  have hpt' : jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y) = spMap emb ≫ X₁.M.pt := by
    calc jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y) = jK V ≫ (spMap φ₀ ≫ Y.Z.fromSpecStalk y) ≫ πY := by rw [hξ]
      _ = (jK V ≫ spMap φ₀ ≫ Y.Z.fromSpecStalk y) ≫ πY := by simp only [Category.assoc]
      _ = (spMap emb ≫ Y.pt) ≫ πY := by rw [hjξ]
      _ = spMap emb ≫ X₁.M.pt := by rw [Category.assoc, hπ]
  have hinj : Function.Injective ev := by
    have h1 : spMap ((algebraMap V (FractionRing V)).comp ev) ≫ X₁.M.Z.fromSpecStalk (πY y) =
        spMap (emb.comp (X₁.M.stalkHom (πY y))) ≫ X₁.M.Z.fromSpecStalk (πY y) := by
      rw [← spMap_spMap (algebraMap V (FractionRing V)) ev, ← spMap_spMap emb (X₁.M.stalkHom (πY y)), Category.assoc,
        Category.assoc, spMap_stalkHom]
      exact hpt'
    have h2 := (cancel_mono _).1 h1
    have h3 : (algebraMap V (FractionRing V)).comp ev = emb.comp (X₁.M.stalkHom (πY y)) :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
    intro a b hab
    apply X₁.M.stalkHom_injective
    apply emb.injective
    have ha := RingHom.congr_fun h3 a
    have hb := RingHom.congr_fun h3 b
    simp only [RingHom.comp_apply] at ha hb
    rw [← ha, ← hb, hab]
  obtain ⟨X, _, t, δ, ⟨𝔫⟩⟩ := exists_gMem_of_trait I X₁ (πY y) act hact Y πY hY V hcpl hchar ev
    (RingHom.isLocalHom_comp _ _) _ emb hξ hjξ
  refine ⟨V, inferInstance, inferInstance, inferInstance, hdvr, ev, X, inferInstance, t, δ, 𝔫,
    spMap φ₀ ≫ Y.Z.fromSpecStalk y, hξ, ?_, hinj⟩
  change Y.Z.fromSpecStalk y (spMap φ₀ (closedPoint V)) = y
  have : spMap φ₀ (closedPoint V) = closedPoint (Y.Z.presheaf.stalk y) := IsLocalRing.comap_closedPoint φ₀
  rw [this]
  exact Scheme.fromSpecStalk_closedPoint

end GlobalTheory.GSep.Thru
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSectionNormalisedUnitAtTraits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_theta_unit_at_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ Φ : IntFam (maximalIdeal R) D.toPre (m ^ 2) → SecK C.P.L.L C.α (m ^ 2), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) → ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ θ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u θ F₁ := by
  intro R _ _ _ hR D C m hm Φ hΦ F₁
  obtain ⟨θ₀, hθ₀⟩ := GlobalTheory.T.exists_polarisationSection_ratio_integralThetaFamily R hR D C F₁
  obtain ⟨r, t, hr, ht, h⟩ := GlobalTheory.T.thetaExpansionScalars_ratio_odd_mul R hR D C m hm Φ hΦ F₁ θ₀ hθ₀
  have hr' : algebraMap R (FractionRing R) r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale (scal C.A.A.hom
    (algebraMap R (FractionRing R) t / algebraMap R (FractionRing R) r)) θ₀, fun W _ _ _ T => ?_⟩
  obtain ⟨a, b, v, ha, hb, hE, hv⟩ := h W T
  exact ⟨v, GlobalTheory.T.trait_expansionScalar_rescale_degreeOne R hR D C F₁ θ₀ r t _ hr (div_mul_cancel₀ _ hr') W T a b v ha hb hE hv⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankBalancedSymmIntBilinFormsEqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_balancedSymmIntBilinForms_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X], Module.finrank ℤ (balForms H.bar X) = Module.finrank ℚ E / 2 * Module.finrank (𝓞 E) X * Module.finrank (𝓞 E) X := by
  first | exact @GlobalTheory.BalRank.finrank_balForms | exact GlobalTheory.BalRank.finrank_balForms | (intros; apply GlobalTheory.BalRank.finrank_balForms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatementStatement
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_degree_statement : GlobalTheory.Published.ScholzeWeinsteinB → Hypotheses2 → FlatDeg := by
  first | exact @GlobalTheory.CovTop.FlatDegProof.flatDeg | exact GlobalTheory.CovTop.FlatDegProof.flatDeg | (intros; apply GlobalTheory.CovTop.FlatDegProof.flatDeg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPointRigidBoundaryFamilyOfRigidCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPointRigidBoundaryFamily_of_rigidCoordinates : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (C : MonoFam Xo c φ R), HasRigidCoords C → PointRigid C := by
  first | exact @GlobalTheory.PtRigid.pointRigid_of_hasRigidCoords | exact GlobalTheory.PtRigid.pointRigid_of_hasRigidCoords | (intros; apply GlobalTheory.PtRigid.pointRigid_of_hasRigidCoords <;> assumption)
end

