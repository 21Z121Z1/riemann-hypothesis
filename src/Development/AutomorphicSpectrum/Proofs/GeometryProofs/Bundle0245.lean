import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.QQuasiCompact
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusToAbelianVarietyConst
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0242
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0119
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0047
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0243
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0010
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientOfPowerFns
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.AbQ

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open GlobalTheory.CechPic
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_desc {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] (T : TorusExtension G)
    {Y : Over (Sp k)} [GrpObj Y] (f : G ⟶ Y) [IsMonHom f] (hf : T.i ≫ f = 1) :
    ∃ f' : T.B ⟶ Y, T.q ≫ f' = f := by
  letI := T.grpB
  have := T.q_hom
  have := T.q_flat
  have := T.q_surjective
  have := T.q_quasiCompact
  have : EffectiveEpi T.q := GlobalTheory.CosetQuotient.effectiveEpi_of_left T.q
  refine ⟨EffectiveEpi.desc T.q f fun {Z} g₁ g₂ e => ?_, EffectiveEpi.fac _ _ _⟩
  have h : (g₁ * g₂⁻¹) ≫ T.q = toUnit Z ≫ η[T.B] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel]
    rfl
  have h₁ : T.isKernel.lift _ _ h ≫ T.i = g₁ * g₂⁻¹ := T.isKernel.lift_fst _ _ h
  have h₂ : g₁ = (T.isKernel.lift _ _ h ≫ T.i) * g₂ := by rw [h₁, inv_mul_cancel_right]
  rw [h₂, MonObj.mul_comp, Category.assoc, hf, MonObj.comp_one, _root_.one_mul]

theorem i_comp_eq_one {k : Type} [Field k] [IsAlgClosed k] {G : Over (Sp k)} [GrpObj G] (T : TorusExtension G)
    {B : Over (Sp k)} [GrpObj B] (hB : IsAbelianScheme B) (f : G ⟶ B) [IsMonHom f] : T.i ≫ f = 1 := by
  letI := T.addCommGroup
  have := T.free
  have := T.finite
  have := T.i_hom
  obtain ⟨b, hb⟩ := GlobalTheory.splitTorus_to_abelian_const k T.X B hB (T.i ≫ f)
  have e : (η[splitTorus (Sp k) T.X]) ≫ T.i ≫ f = η[B] := IsMonHom.one_hom _
  rw [hb] at e
  have e' : b = η[B] := by
    rw [← e, ← Category.assoc, toUnit_unique (η[splitTorus (Sp k) T.X] ≫ toUnit _) (𝟙 _), Category.id_comp]
  rw [hb, e']
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_act {k : Type} [Field k] [IsAlgClosed k] {G : Over (Sp k)} [GrpObj G] {O : Type} [CommRing O]
    (a : OAct O G) (T : TorusExtension G) :
    letI := T.grpB
    ∃ b : OAct O T.B, ∀ r, a.act r ≫ T.q = T.q ≫ b.act r := by
  letI := T.grpB
  have hB := T.isAbelian
  have := T.q_hom
  have := T.q_flat
  have := T.q_surjective
  have := T.q_quasiCompact
  have : EffectiveEpi T.q := GlobalTheory.CosetQuotient.effectiveEpi_of_left T.q
  have canc : ∀ {Y : Over (Sp k)} (f f' : T.B ⟶ Y), T.q ≫ f = T.q ≫ f' → f = f' := fun f f' h =>
    (cancel_epi T.q).1 h
  have hact : ∀ r, ∃ f' : T.B ⟶ T.B, T.q ≫ f' = a.act r ≫ T.q := fun r => by
    have := a.hom r
    exact exists_desc T _ (i_comp_eq_one T hB _)
  choose α hα using hact
  refine ⟨{ act := α, hom := fun r => GlobalTheory.abelianSchemeLaws_all.1.rigidity _ T.B T.B hB hB _ ?_,
            one := canc _ _ (by rw [hα, a.one, Category.id_comp, Category.comp_id]),
            mul := fun r s => canc _ _ (by
              rw [hα, a.mul, ← Category.assoc T.q, hα, Category.assoc, Category.assoc, hα]),
            add := fun r s => canc _ _ (by rw [hα, a.add, MonObj.mul_comp, MonObj.comp_mul, hα, hα]) },
    fun r => (hα r).symm⟩
  have := a.hom r
  rw [← IsMonHom.one_hom T.q, Category.assoc, hα, ← Category.assoc, IsMonHom.one_hom]

theorem adj_quot {k : Type} [Field k] [IsAlgClosed k] {H : Host E} (tK : SAB H (Sp k)) (T : TorusExtension tK.G)
    (M : LB T.B.left) (hM : M.IsLB) (hbun : LBIso tK.PP.L (M.pull T.q.left)) :
    letI := T.grpB
    ∀ (act : OAct (𝓞 E) T.B), (∀ r, tK.act.act r ≫ T.q = T.q ≫ act.act r) → ∀ a,
      LBIso (cubeLB T.B ![fst T.B T.B ≫ act.act a, snd T.B T.B] M)
        (cubeLB T.B ![fst T.B T.B, snd T.B T.B ≫ act.act (H.bar a)] M) := by
  letI := T.grpB
  have hB := T.isAbelian
  haveI := hB.comm
  have := T.q_hom
  intro act hact a
  have := act.hom a
  have := act.hom (H.bar a)
  have hL := tK.PP.isLB
  set l := cls tK.PP.L hL with hl
  set m := cls M hM with hm
  have hqm : pull T.q.left m = l := ((cls_eq_iff hL (pull_isLB hM _)).2 hbun).symm
  have lamq : ∀ {Z : Over (Sp k)} (u v : Z ⟶ tK.G), lam m (u ≫ T.q) (v ≫ T.q) = lam l u v := fun u v => by
    rw [← lam_pull, hqm]
  have adjG : ∀ {Z : Over (Sp k)} (u v : Z ⟶ tK.G),
      lam l (u ≫ tK.act.act a) v = lam l u (v ≫ tK.act.act (H.bar a)) := by
    intro Z u v
    have h := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (tK.adj a)
    have h' := congrArg (pull (lift u v).left)
      ((cls_cube_two hL _ _ _).symm.trans (h.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'
  let D : ∀ {Z : Over (Sp k)}, (Z ⟶ T.B) → (Z ⟶ T.B) → Pic Z.left := fun x y =>
    lam m (x ≫ act.act a) y - lam m x (y ≫ act.act (H.bar a))
  have Dpull : ∀ {Z Z' : Over (Sp k)} (h : Z' ⟶ Z) (x y : Z ⟶ T.B), pull h.left (D x y) = D (h ≫ x) (h ≫ y) := by
    intro Z Z' h x y
    simp only [D, map_sub, pull_lam, Category.assoc]
  have Dq : ∀ {Z : Over (Sp k)} (u v : Z ⟶ tK.G), D (u ≫ T.q) (v ≫ T.q) = 0 := by
    intro Z u v
    have e₁ : (u ≫ T.q) ≫ act.act a = (u ≫ tK.act.act a) ≫ T.q := by
      rw [Category.assoc, Category.assoc, hact]
    have e₂ : (v ≫ T.q) ≫ act.act (H.bar a) = (v ≫ tK.act.act (H.bar a)) ≫ T.q := by
      rw [Category.assoc, Category.assoc, hact]
    simp only [D]
    rw [e₁, e₂, lamq, lamq, adjG, sub_self]
  have D1l : ∀ {Z : Over (Sp k)} (y : Z ⟶ T.B), D 1 y = 0 := by
    intro Z y
    simp only [D]
    rw [MonObj.one_comp, lam_one_left, lam_one_left, sub_self]
  have D1r : ∀ {Z : Over (Sp k)} (x : Z ⟶ T.B), D x 1 = 0 := by
    intro Z x
    simp only [D]
    rw [MonObj.one_comp, lam_one_right, lam_one_right, sub_self]
  have hGs := tK.semi
  have one_q : ∀ {Z : Over (Sp k)}, (1 : Z ⟶ tK.G) ≫ T.q = 1 := fun {Z} => MonObj.one_comp _
  have c₁ : D (fst T.B tK.G) (snd T.B tK.G ≫ T.q) = 0 := by
    refine GlobalTheory.T.picard_class_trivial_by_seesaw k tK.G hGs T tK.G hGs.smooth hGs.geomConnected η[tK.G] _ ?_ ?_
    · have e₁ : lift (fst tK.G tK.G ≫ T.q) (snd tK.G tK.G) ≫ fst T.B tK.G = fst tK.G tK.G ≫ T.q := lift_fst _ _
      have e₂ : lift (fst tK.G tK.G ≫ T.q) (snd tK.G tK.G) ≫ snd T.B tK.G ≫ T.q = snd tK.G tK.G ≫ T.q := by
        rw [← Category.assoc, lift_snd]
      rw [Dpull, e₁, e₂]
      exact Dq _ _
    · have e₁ : lift (𝟙 T.B) (toUnit T.B ≫ η[tK.G]) ≫ fst T.B tK.G = 𝟙 T.B := lift_fst _ _
      have e₂ : lift (𝟙 T.B) (toUnit T.B ≫ η[tK.G]) ≫ snd T.B tK.G ≫ T.q = 1 := by
        rw [← Category.assoc, lift_snd]
        exact one_q
      rw [Dpull, e₁, e₂]
      exact D1r _
  have Dr : ∀ {Z : Over (Sp k)} (x : Z ⟶ T.B) (v : Z ⟶ tK.G), D x (v ≫ T.q) = 0 := by
    intro Z x v
    have h := congrArg (pull (lift x v).left) c₁
    have e₂ : lift x v ≫ snd T.B tK.G ≫ T.q = v ≫ T.q := by rw [← Category.assoc, lift_snd]
    rw [Dpull, map_zero, lift_fst, e₂] at h
    exact h
  have c₂ : D (snd T.B T.B) (fst T.B T.B) = 0 := by
    refine GlobalTheory.T.picard_class_trivial_by_seesaw k tK.G hGs T T.B hB.smooth hB.geomConnected η[T.B] _ ?_ ?_
    · have e₁ : lift (fst tK.G T.B ≫ T.q) (snd tK.G T.B) ≫ fst T.B T.B = fst tK.G T.B ≫ T.q := lift_fst _ _
      have e₂ : lift (fst tK.G T.B ≫ T.q) (snd tK.G T.B) ≫ snd T.B T.B = snd tK.G T.B := lift_snd _ _
      rw [Dpull, e₁, e₂]
      exact Dr _ _
    · have e₁ : lift (𝟙 T.B) (toUnit T.B ≫ η[T.B]) ≫ fst T.B T.B = 𝟙 T.B := lift_fst _ _
      have e₂ : lift (𝟙 T.B) (toUnit T.B ≫ η[T.B]) ≫ snd T.B T.B = 1 := lift_snd _ _
      rw [Dpull, e₁, e₂]
      exact D1l _
  have c₃ : D (fst T.B T.B) (snd T.B T.B) = 0 := by
    have h := congrArg (pull (lift (snd T.B T.B) (fst T.B T.B)).left) c₂
    rw [Dpull, map_zero, lift_fst, lift_snd] at h
    exact h
  have h₁ : (cubeLB T.B ![fst T.B T.B ≫ act.act a, snd T.B T.B] M).IsLB := LB.isLB_linComb hM _ _
  have h₂ : (cubeLB T.B ![fst T.B T.B, snd T.B T.B ≫ act.act (H.bar a)] M).IsLB := LB.isLB_linComb hM _ _
  refine (cls_eq_iff h₁ h₂).1 ?_
  rw [cls_cube_two hM, cls_cube_two hM]
  exact sub_eq_zero.1 c₃

theorem exists_abQuot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X),
    PowFns t → ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X),
    GeomPF t x → Nonempty (AbQuot t x) := by
  intro E _ _ _ H X t _ k _ _ p _ _ x ⟨T, M, hM, hK, hbun⟩
  obtain ⟨PP', cub', sym', adj', prim', m, hm⟩ := sabPull Out.CubePf.cubePull x t
  let tK : SAB H (Sp k) := ⟨_, IsSemiAbelian.pullback x t.G t.semi, OAct.pullback x t.G t.act, PP', cub', sym', adj', prim'⟩
  obtain ⟨w, hw, -, -⟩ := m.lin
  have hiso : LBIso PP'.L (t.PP.L.pull (pullback.fst t.G.hom x)) := by
    rw [← hm]
    exact ⟨w, hw⟩
  letI := T.grpB
  have hB := T.isAbelian
  haveI := hB.comm
  have hq := T.q_hom
  have hP₀ := pull_isLB t.PP.isLB (pullback.fst t.G.hom x)
  have hqL := pull_isLB hM T.q.left
  have hbun' : LBIso tK.PP.L (M.pull T.q.left) := LBIso.trans PP'.isLB hP₀ hqL hiso hbun
  obtain ⟨act, hact⟩ := exists_act tK.act T
  have hadj := adj_quot tK T M hM hbun' act hact
  obtain ⟨PP, cub, hsym, hPP, hlam, hprim, hadjP⟩ := GlobalTheory.PrimNorm.exists_primitive_normalisation GlobalTheory.globalFns_holds
    E H _ T.B act M hB hM (GlobalTheory.exists_gen_theta_of_isAbelianScheme k T.B hB M hM) hadj
  have hP' := PP.isLB
  have hL : tK.PP.L.IsLB := PP'.isLB
  have hqm : pull T.q.left (cls M hM) = cls tK.PP.L hL := ((cls_eq_iff hL hqL).2 hbun').symm
  have hpull : pull T.q.left (cls PP.L hP') = cls tK.PP.L hL := by
    have h := (cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 tK.prim
    have h' := (cls_eq_iff hP' (LB.isLB_linComb hM _ _)).2 hPP
    have e : cls tK.PP.L hL = lam (cls tK.PP.L hL) (𝟙 _) (tK.act.act H.w0) := h.trans (cls_cube_two hL _ _ _)
    have e' : cls PP.L hP' = lam (cls M hM) (𝟙 _) (act.act H.w0) := h'.trans (cls_cube_two hM _ _ _)
    rw [e', pull_lam, ← hact, Category.comp_id, ← Category.id_comp T.q, ← Category.assoc, Category.comp_id,
      ← lam_pull, hqm, ← e]
  have hfin : LBIso tK.PP.L (PP.L.pull T.q.left) := by
    rw [← cls_eq_iff hL (pull_isLB hP' _), cls_pull hP', hpull]
  have hK' : Out.KTriv T.B PP.L := GlobalTheory.CM.kTriv_of_lamEq _ T.B M PP.L hM hP'
    (by simp only [GlobalTheory.CM.LamEq, Category.comp_id]; exact hlam) hK
  exact ⟨{ tB := ⟨T.B, GlobalTheory.isSemiAbelian_of_isAbelianScheme T.B hB, act, PP, cub, hsym, hadjP, hprim⟩
           proper := hB.proper
           ktriv := hK'
           Ch := T.X
           acg := T.addCommGroup
           free := T.free
           fin := T.finite
           q := T.q
           q_hom := hq
           q_flat := T.q_flat
           q_surjective := T.q_surjective
           q_quasiCompact := T.q_quasiCompact
           i := T.i
           i_hom := T.i_hom
           isKernel := T.isKernel
           act_q := hact
           bun := LBIso.trans hP₀ hL (pull_isLB hP' _) (LBIso.symm hiso) hfin }⟩

end GlobalTheory.CompanionTheory.Ar.AbQ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHolomorphicStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_chart_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : BdryChart Xo σ n a), IsHolTo (punct n a 1) C.pt := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isHolTo_pt | exact GlobalTheory.CompanionTheory.Ar.Flat.isHolTo_pt | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isHolTo_pt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmImageUniqueLatticeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_image_unique_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (a : PureType.lat hP (sgnRt H b)), (∃! u, X.IsImage b a u) ∧ ∀ u, X.IsImage b a u → IsTanAt Xo.univ.t.G _ u ∧ IsDerivAt0 (fun s => (FU.ex i P s).left) ((Z b).z • P a) (spMap (dualMap (algebraMap X.K ℂ)) ≫ u.left) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.cm_image_unique_lattice | exact GlobalTheory.CompanionTheory.Relay.cm_image_unique_lattice | (intros; apply GlobalTheory.CompanionTheory.Relay.cm_image_unique_lattice <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CubicalWeilPairingIsoInvariant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.CubIso

section Local
variable {X Y Z : Scheme.{0}} {A B : LB X}

def isoGerm (w : LB.Iso A B) (f : Y ⟶ X) (y : Y) (j : B.ι) (k : A.ι) : (Y.presheaf.stalk y)ˣ :=
  gm f y (B.U j ⊓ A.U k) (w.s (j, k))

theorem isoGerm_trans {w : LB.Iso A B} (hw : w.IsGen) (f : Y ⟶ X) (y : Y) {j j' : B.ι} {k k' : A.ι}
    (hj : f y ∈ B.U j) (hj' : f y ∈ B.U j') (hk : f y ∈ A.U k) (hk' : f y ∈ A.U k') :
    isoGerm w f y j k = gm f y _ (B.g j j') * (gm f y _ (A.g k k'))⁻¹ * isoGerm w f y j' k' := by
  have hm : f y ∈ B.U j ⊓ A.U k ⊓ (B.U j' ⊓ A.U k') := ⟨⟨hj, hk⟩, hj', hk'⟩
  have h := congrArg (gm f y (B.U j ⊓ A.U k ⊓ (B.U j' ⊓ A.U k'))) (hw (j, k) (j', k'))
  have e : gm f y (B.U j ⊓ A.U k ⊓ (B.U j' ⊓ A.U k')) ((LB.div B A).g (j, k) (j', k')) =
      gm f y _ (B.g j j') * (gm f y _ (A.g k k'))⁻¹ := by
    show gm f y _ (res _ (B.g j j') * (res _ (A.g k k'))⁻¹) = _
    rw [map_mul, map_inv, gm_res f y _ hm, gm_res f y _ hm]
  exact (gm_res f y _ hm _).symm.trans (h.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) e (gm_res f y _ hm _))))

variable {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem prod_isoGerm_trans {w : LB.Iso A B} (hw : w.IsGen) (r : Z ⟶ Y) (z : Z) {p p' : K → B.ι} {q q' : K → A.ι}
    (hp : r z ∈ LB.wchart B φ p) (hp' : r z ∈ LB.wchart B φ p') (hq : r z ∈ LB.wchart A φ q)
    (hq' : r z ∈ LB.wchart A φ q') :
    ∏ k, isoGerm w (r ≫ φ k) z (p k) (q k) ^ ε k =
      trF (L := B) φ ε r z p p' * (trF (L := A) φ ε r z q q')⁻¹ * ∏ k, isoGerm w (r ≫ φ k) z (p' k) (q' k) ^ ε k := by
  rw [trF, trF, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [isoGerm_trans hw (r ≫ φ k) z (Set.mem_iInter.1 hp k) (Set.mem_iInter.1 hp' k) (Set.mem_iInter.1 hq k)
    (Set.mem_iInter.1 hq' k), mul_zpow, mul_zpow, _root_.inv_zpow]

theorem exists_ratio (hA : A.IsLB) (hB : B.IsLB) {w : LB.Iso A B} (hw : w.IsGen) {a : LB.Gen (LB.LinComb A φ ε)}
    {b : LB.Gen (LB.LinComb B φ ε)} (ha : a.IsGen) (hb : b.IsGen) :
    ∃ v : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → B.ι) (q : K → A.ι),
      r z ∈ LB.wchart B φ p → r z ∈ LB.wchart A φ q →
      gm r z (LB.wchart B φ p) (b.s p) = gm r z ⊤ v * (∏ k, isoGerm w (r ≫ φ k) z (p k) (q k) ^ ε k) *
        gm r z (LB.wchart A φ q) (a.s q) := by
  let Wc : (K → B.ι) × (K → A.ι) → Y.Opens := fun P => LB.wchart B φ P.1 ⊓ LB.wchart A φ P.2
  have le : ∀ P k, Wc P ≤ φ k ⁻¹ᵁ (B.U (P.1 k) ⊓ A.U (P.2 k)) := fun P k =>
    le_inf (inf_le_left.trans (LB.wchart_le B φ P.1 k)) (inf_le_right.trans (LB.wchart_le A φ P.2 k))
  let I : ∀ P, Γ(Y, Wc P)ˣ := fun P => res (inf_le_left : Wc P ≤ LB.wchart B φ P.1) (b.s P.1) *
    (res (inf_le_right : Wc P ≤ LB.wchart A φ P.2) (a.s P.2))⁻¹ *
    (∏ k, res (le P k) (pullU (φ k) _ (w.s (P.1 k, P.2 k))) ^ ε k)⁻¹
  have hI : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) P, r z ∈ Wc P → gm r z (Wc P) (I P) =
      gm r z (LB.wchart B φ P.1) (b.s P.1) * (gm r z (LB.wchart A φ P.2) (a.s P.2))⁻¹ *
        (∏ k, isoGerm w (r ≫ φ k) z (P.1 k) (P.2 k) ^ ε k)⁻¹ := by
    intro Z r z P hz
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _)
      ((map_inv _ _ ).trans (congrArg _ (gm_res r z _ hz _))))) ((map_inv _ _).trans (congrArg _ ?_)))
    refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
    exact (gm_res r z (le P k) hz _).trans (gm_pull r (φ k) z _ (le P k hz) _)
  obtain ⟨v, hv⟩ := glue_unit ⊤ Wc (fun _ => le_top) (fun x _ => by
      choose p hp using fun k => exists_chart hB (φ k x)
      choose q hq using fun k => exists_chart hA (φ k x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(p, q), Set.mem_iInter.2 hp, Set.mem_iInter.2 hq⟩) I (fun P Q x hx => by
      rw [hI _ _ x P hx.1, hI _ _ x Q hx.2, gen_trans hb (𝟙 Y) x hx.1.1 hx.2.1, gen_trans ha (𝟙 Y) x hx.1.2 hx.2.2,
        prod_isoGerm_trans hw (𝟙 Y) x hx.1.1 hx.2.1 hx.1.2 hx.2.2]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  refine ⟨v, fun Z r z p q hp hq => ?_⟩
  have hz : r z ∈ Wc (p, q) := ⟨hp, hq⟩
  have e := (gm_res r z (le_top : Wc (p, q) ≤ ⊤) hz v).symm.trans ((congrArg (gm r z (Wc (p, q))) (hv (p, q))).trans
    (hI Z r z (p, q) hz))
  rw [e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem appTop_eq_one (r : Z ⟶ Y) (v : Γ(Y, ⊤)ˣ) (h : ∀ z, gm r z ⊤ v = 1) : r.appTop.hom v.val = 1 := by
  have e : Units.map r.appTop.hom.toMonoidHom v = 1 :=
    unit_ext fun z _ => by rw [← gm_top r z v, h z, map_one]
  exact congrArg Units.val e

end Local

section Cube
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L₁ L₂ : RigLB G}

theorem exists_cube_ratio {w : LB.Iso L₁.L L₂.L} (hw : w.IsGen) (c₁ : CubicalStr G L₁) (c₂ : CubicalStr G L₂) :
    ∃ v : Γ((G ⊗ G ⊗ G).left, ⊤)ˣ, ∀ (T : Over S) (z : T.left) (J₁ : (T.left ⟶ G.left) → L₁.L.ι)
      (J₂ : (T.left ⟶ G.left) → L₂.L.ι), Good L₁.L z J₁ → Good L₂.L z J₂ →
      ∀ (W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ), (∀ x, W x = isoGerm w x.left z (J₂ x.left) (J₁ x.left)) →
      ∀ a b d : T ⟶ G, cubV c₂ z J₂ a b d * W (a * b) * W (a * d) * W (b * d) * W 1 =
        gm (lift a (lift b d)).left z ⊤ v * (W (a * b * d) * W a * W b * W d) * cubV c₁ z J₁ a b d := by
  obtain ⟨v, hv⟩ := exists_ratio (φ := thφ G (x3 G)) (ε := thε) (a := c₁.t) (b := c₂.t) L₁.isLB L₂.isLB hw
    c₁.isGen c₂.isGen
  refine ⟨v, fun T z J₁ J₂ h₁ h₂ W hW a b d => ?_⟩
  have e := hv T.left (lift a (lift b d)).left z (fun I => J₂ ((lift a (lift b d)).left ≫ thφ G (x3 G) I))
    (fun I => J₁ ((lift a (lift b d)).left ≫ thφ G (x3 G) I)) (h₂.mem _ _) (h₁.mem _ _)
  have f := prod_cub a b d (fun q => isoGerm w q z (J₂ q) (J₁ q))
  have e' : cubV c₂ z J₂ a b d = gm (lift a (lift b d)).left z ⊤ v *
      (∏ I : thK.{0}, isoGerm w ((lift a (lift b d)).left ≫ thφ G (x3 G) I) z
        (J₂ ((lift a (lift b d)).left ≫ thφ G (x3 G) I)) (J₁ ((lift a (lift b d)).left ≫ thφ G (x3 G) I)) ^ thε I) *
      cubV c₁ z J₁ a b d := e
  rw [e', f, hW, hW, hW, hW, hW, hW, hW, hW]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem cube_ratio_faces {w : LB.Iso L₁.L L₂.L} (c₁ : CubicalStr G L₁) (c₂ : CubicalStr G L₂)
    {v : Γ((G ⊗ G ⊗ G).left, ⊤)ˣ}
    (hv : ∀ (T : Over S) (z : T.left) (J₁ : (T.left ⟶ G.left) → L₁.L.ι)
      (J₂ : (T.left ⟶ G.left) → L₂.L.ι), Good L₁.L z J₁ → Good L₂.L z J₂ →
      ∀ (W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ), (∀ x, W x = isoGerm w x.left z (J₂ x.left) (J₁ x.left)) →
      ∀ a b d : T ⟶ G, cubV c₂ z J₂ a b d * W (a * b) * W (a * d) * W (b * d) * W 1 =
        gm (lift a (lift b d)).left z ⊤ v * (W (a * b * d) * W a * W b * W d) * cubV c₁ z J₁ a b d)
    (T : Over S) (x y : T ⟶ G) :
    (lift (1 : T ⟶ G) (lift x y)).left.appTop.hom v.val = 1 ∧
      (lift x (lift (1 : T ⟶ G) y)).left.appTop.hom v.val = 1 ∧
      (lift x (lift y (1 : T ⟶ G))).left.appTop.hom v.val = 1 := by
  refine ⟨appTop_eq_one _ v fun z => ?_, appTop_eq_one _ v fun z => ?_, appTop_eq_one _ v fun z => ?_⟩
  all_goals
    obtain ⟨J₁, h₁⟩ := exists_good_pt L₁.isLB z
    obtain ⟨J₂, h₂⟩ := exists_good_pt L₂.isLB z
  · have e := hv T z J₁ J₂ h₁ h₂ _ (fun _ => rfl) 1 x y
    rw [(isCub_cubV c₁ h₁).face, (isCub_cubV c₂ h₂).face] at e
    simp only [_root_.one_mul, _root_.mul_one] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · have e := hv T z J₁ J₂ h₁ h₂ _ (fun _ => rfl) x 1 y
    rw [(isCub_cubV c₁ h₁).face₂, (isCub_cubV c₂ h₂).face₂] at e
    simp only [_root_.one_mul, _root_.mul_one] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · have e := hv T z J₁ J₂ h₁ h₂ _ (fun _ => rfl) x y 1
    rw [(isCub_cubV c₁ h₁).face₃, (isCub_cubV c₂ h₂).face₃] at e
    simp only [_root_.one_mul, _root_.mul_one] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'

end Cube

theorem cubWeil_of_lbIso : ∀ (G : Over (Sp ℂ)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → TorusExtension G → ∀ (L₁ L₂ : RigLB G) (c₁ : CubicalStr G L₁) (c₂ : CubicalStr G L₂), LBIso L₁.L L₂.L → ∀ (N : ℕ) (x y : 𝟙_ (Over (Sp ℂ)) ⟶ G) (ζ : Γ(Sp ℂ, ⊤)ˣ), CubWeil c₁ N x y ζ → CubWeil c₂ N x y ζ := by
  intro G _ _ hs te L₁ L₂ c₁ c₂ hiso N x y ζ h
  obtain ⟨w, hw⟩ := hiso
  obtain ⟨v, hv⟩ := exists_cube_ratio hw c₁ c₂
  have hone := GlobalTheory.T.cubical_triple_trivial ℂ G hs te v (cube_ratio_faces c₁ c₂ hv)
  refine ⟨h.1, h.2.1, fun z J₂ h₂ => ?_⟩
  obtain ⟨J₁, h₁⟩ := exists_good_pt L₁.isLB z
  let W : (𝟙_ (Over (Sp ℂ)) ⟶ G) → _ := fun a => isoGerm w a.left z (J₂ a.left) (J₁ a.left)
  refine cubN_ratio_twist (MonoidHom.id _) W (fun a b d => ?_) h.1 h.2.1 (h.2.2 z J₁ h₁)
  have e := hv _ z J₁ J₂ h₁ h₂ W (fun _ => rfl) a b d
  have g : gm (lift a (lift b d)).left z ⊤ v = 1 := by
    rw [gm_top]
    have : Units.map (lift a (lift b d)).left.appTop.hom.toMonoidHom v = 1 := Units.ext (hone a b d)
    rw [this, map_one]
  rw [g, _root_.one_mul] at e
  exact e

end GlobalTheory.CompanionTheory.Ar.CubIso
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExpChartCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exp_chart_coordinates : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ), IsAbelianScheme A → Out.RelAmple A L → SmoothOfRelativeDimension g A.hom → ∃ u : HolUnif A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩ : LB A.left) g, ∃ (U : A.left.Opens) (t : Fin g → Γ(A.left, U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(A.left, U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) → (∀ i, D (t i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex w).left U (t i)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AVExp.exists_holUnif | exact GlobalTheory.CompanionTheory.Ar.AVExp.exists_holUnif | (intros; apply GlobalTheory.CompanionTheory.Ar.AVExp.exists_holUnif <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSqrtNegDiscPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sqrt_neg_disc_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ 𝔐.X), ∃ ρ : L, ρ ^ 2 = -(H.d : L) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k), DetCond D 𝔐.t.act (spMap g ≫ z) (g ρ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PointDet.detCond_at_point | exact GlobalTheory.CompanionTheory.Ar.PointDet.detCond_at_point | (intros; apply GlobalTheory.CompanionTheory.Ar.PointDet.detCond_at_point <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExpDerivativeLieStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_exp_derivative_lie : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ) (b : Fin n → ℂ), b ∈ B → ∀ u : Fin g → R, IsDerivAt0 (fun z => (e.ex b z).left) (fun c => ψ b (u c)) (spMap (dualMap (ψ b)) ≫ (M.pt u).left) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrameDeriv.isDerivAt0_frame_section | exact GlobalTheory.CompanionTheory.Ar.Flat.FrameDeriv.isDerivAt0_frame_section | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrameDeriv.isDerivAt0_frame_section <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPurePeriodsSpan
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ggeo

theorem point_numberField_of_finiteIndex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (n : ℕ), 0 < n → (∀ y : (FU.Di i).La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) → ∃ (K₁ : IntermediateField ℚ ℂ) (hk : KA l ≤ K₁) (y : Sp K₁ ⟶ Xo.X), FiniteDimensional ℚ K₁ ∧ y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i P :=
  @PositivityTheory.Xgf.family_pure_periods_span

end GlobalTheory.CompanionTheory.Ggeo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeLinearEquivStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_lattice_linear_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (z : Sp ℂ ⟶ X) (g g' : ℕ) (Λ Λ' : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (R : RiemLat E g Λ) (R' : RiemLat E g' Λ') (A₀ : Type) (x : A₀ → Fin g → ℂ) (x' : A₀ → Fin g' → ℂ) (v : A₀ → (epsAt z ⟶ t.G)), FibreLatVec t z R x v → FibreLatVec t z R' x' v → ∃ φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ), φ '' Set.range R.P = Set.range R'.P ∧ (∀ p q, R'.ip (φ p) (φ q) = R.ip p q) ∧ (∀ a p, φ (R.B a p) = R'.B a (φ p)) ∧ ∀ i, φ (x i) = x' i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FibreUnique.exists_linearEquiv_of_fibreLatVec | exact GlobalTheory.CompanionTheory.Ar.Cusp.FibreUnique.exists_linearEquiv_of_fibreLatVec | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FibreUnique.exists_linearEquiv_of_fibreLatVec <;> assumption)
end

