import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0014
import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.WeilBound.CoreStatements.HodgeTatePoints.FarsharpA
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.IBIsKernel

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.CgUnif
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Cg

theorem lbIso_refl {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _))).trans ?_
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  exact (mul_right_comm _ _ _).trans (mul_inv_eq_of_eq_mul (a.trans b.symm))

theorem unif_pf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (_ : PELUnif (IsLocalRing.maximalIdeal R) t), GeomPF t (spMap (IsLocalRing.residue R)) := by
  intro E _ _ _ H R _ _ _ t P
  let I := IsLocalRing.maximalIdeal R
  let D := P.D.toPre
  let c := P.U.toUnifPre.gt 0
  let g : Sp (IsLocalRing.ResidueField R) ⟶ Sp (R ⧸ I ^ (0 + 1)) :=
    spMap (Ideal.Quotient.factor (show I ^ (0 + 1) ≤ I by simp))
  have hg : g ≫ Out.thick R I 0 = spMap (IsLocalRing.residue R) := by
    exact (Spec.map_comp _ _).symm.trans (congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun _ => rfl)))
  obtain ⟨eG, mG, hG⟩ := grpPullback_iso (isGrpPullback_pullback t.G (spMap (IsLocalRing.residue R)))
    (((isGrpPullback_pullback (Out.thickObj R I 0 t.G) g).comp (isGrpPullback_pullback t.G _)).congr hg rfl)
  obtain ⟨eB, mB, hB⟩ := grpPullback_iso (isGrpPullback_pullback D.P.A (spMap (IsLocalRing.residue R)))
    (((isGrpPullback_pullback (Out.thickObj R I 0 D.P.A) g).comp (isGrpPullback_pullback D.P.A _)).congr hg rfl)
  obtain ⟨eT, mT, -⟩ := GlobalTheory.TorusExtBaseChange.exists_splitTorus_iso g (AddEquiv.refl D.X)
  have := c.q_hom
  have := c.i_hom
  obtain ⟨q, i, hq, hf, hs, ha, hi, hk, hqc, -⟩ := GlobalTheory.TorusExtBaseChange.exists_extension g eT eG eB c.i c.q
    c.q_flat c.q_surj c.q_affine c.isKernel
  have hM := pull_isLB D.P.isLB (pullback.fst D.P.A.hom (spMap (IsLocalRing.residue R)))
  refine ⟨{ X := D.X
            free := D.freeX
            finite := D.finX
            B := (Over.pullback (spMap (IsLocalRing.residue R))).obj D.P.A
            isAbelian := Out.TLinPf.isAb_pullback _ _ D.P.isAb
            q := q
            q_hom := hq
            q_flat := hf
            q_surjective := hs
            q_quasiCompact := inferInstance
            i := i
            i_hom := hi
            isKernel := hk }, D.P.L.pull (pullback.fst D.P.A.hom (spMap (IsLocalRing.residue R))), hM, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := lbIso_refl hM
    exact kTriv_pull (isGrpPullback_pullback D.P.A _) D.P.isLB hM ((isGen_iff w).1 hw) D.P.ktriv
  · have h0 : LBIso (P.U.toUnifPre.LG.L.pull (Out.fstG I 0 t.G).left) (D.P.L.pull c.pG.left) :=
      ⟨P.U.toUnifPre.w 0, P.U.toUnifPre.w_gen 0⟩
    rw [show P.U.toUnifPre.LG = t.PP from P.bundle] at h0
    refine h0.chartPull (h := eG.hom.left ≫ pullback.fst (Out.thickObj R I 0 t.G).hom g)
      (chartPullSame _ _ _ _ _ fun _ => ?_) (chartPullLinComb _ _ _ _ _ _ fun _ => ?_)
    · rw [Category.assoc]; exact hG.symm
    · show q.left ≫ _ = _ ≫ c.q.left ≫ pullback.fst D.P.A.hom (Out.thick R I 0)
      rw [← hB, ← Category.assoc _ c.q.left, ← hqc]
      simp only [Category.assoc]

end PositivityTheory.HtPt.Cg
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.Farsharp
section
noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace PositivityTheory.HtPt.Farsharp

variable (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
  (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O)
  (hp : v (p : C) < 1)

include hv hp in

theorem smul_dUnit_mem (A : Type) [CommRing A] [Bialgebra O A] [IsCocomm O A] [Module.Finite O A]
    [Module.Projective O A] (hfin : {u : A | IsGroupLikeElem O u}.Finite) (q : O) (hq : q ≠ 0)
    (M : Submodule O (Cot O A)) (hM : ∀ u, IsGroupLikeElem O u → dUnit O u ∈ M)
    (hqM : ∀ y, q • y ∈ M) (κ : O) (hκ : v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C))
    (y : Cot O A) : κ • y ∈ M := by
  have : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  have : ValuationRing O := by
    refine @ValuationRing.mk O _ _ ⟨fun a b => ?_⟩
    rcases le_total (v (algebraMap O C a)) (v (algebraMap O C b)) with h | h
    · obtain ⟨c, hc⟩ := hv.dvd_iff_le.2 h
      exact ⟨c, Or.inr hc.symm⟩
    · obtain ⟨c, hc⟩ := hv.dvd_iff_le.2 h
      exact ⟨c, Or.inl hc.symm⟩
  let ε := counitAlgHom O A
  let π : A →ₗ[O] A := LinearMap.id - Algebra.linearMap O A ∘ₗ ε.toLinearMap
  have hπ : ∀ a, π a = a - algebraMap O A (ε a) := fun _ => rfl
  let μ : A ⊗[O] A →ₗ[O] A := LinearMap.mul' O A ∘ₗ TensorProduct.map π π
  have hμ : ∀ a b, μ (a ⊗ₜ b) = π a * π b := fun a b => by simp [μ]
  let N : Submodule O A := Submodule.span O {u : A | IsGroupLikeElem O u} ⊔
    (LinearMap.range μ ⊔ LinearMap.range (q • (LinearMap.id : A →ₗ[O] A)))
  have hN : N.FG := (Submodule.fg_span hfin).sup ((Submodule.fg_range _).sup (Submodule.fg_range _))
  have hNM : N ≤ M.comap (AugCot.d ε) := by
    refine sup_le (Submodule.span_le.2 hM) (sup_le ?_ ?_)
    · rintro _ ⟨t, rfl⟩
      induction t with
      | zero => simp
      | tmul a b =>
        have h0 : ∀ a, ε (π a) = 0 := fun a => by rw [hπ]; simp
        rw [Submodule.mem_comap, hμ, AugCot.d_mul, h0, h0, zero_smul, zero_smul, add_zero]
        exact zero_mem _
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
    · rintro _ ⟨a, rfl⟩
      rw [Submodule.mem_comap, LinearMap.smul_apply, map_smul]
      exact hqM _
  obtain ⟨a, rfl⟩ := AugCot.d_surjective _ y
  rw [← map_smul]
  refine hNM (mem_of_forall_dvd N hN hq
    (fun a => Submodule.mem_sup_right (Submodule.mem_sup_right ⟨a, rfl⟩)) _ fun φ hφ => ?_)
  have hu : ∀ u : A, IsGroupLikeElem O u → q ∣ φ u := fun u hu =>
    hφ u (Submodule.mem_sup_left (Submodule.subset_span hu))
  rw [map_smul]
  refine dvd_mul_of_val p C v O hv hp A q hq φ (fun a b => ?_) hu κ hκ a
  have h1 := hφ _ (Submodule.mem_sup_right (Submodule.mem_sup_left ⟨a ⊗ₜ b, rfl⟩))
  have h2 := (hu 1 IsGroupLikeElem.one).mul_left (ε a * ε b)
  have h3 : μ (a ⊗ₜ b) = a * b - ε a • b - ε b • a + (ε a * ε b) • (1 : A) := by
    rw [hμ, hπ, hπ]
    simp only [Algebra.smul_def, map_mul]
    ring
  rw [h3, map_add, map_sub, map_sub, map_smul, map_smul, map_smul] at h1
  exact (dvd_add_left h2).1 h1

include hv hp in

theorem smul_mem_range_dlogLinear [Algebra ℤ_[p] O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    (G : PDivGroup p O) (κ : O) (hκ : v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C)) (w : G.omega) :
    κ • w ∈ LinearMap.range (dlogLinear G) := by
  have hpp : p.Prime := Fact.out
  have : IsIntegrallyClosedIn O C := isIntegrallyClosedIn_iff.2
    ⟨hv.hom_inj, fun hx => hv.exists_of_le_one (hv.mem_of_integral hx)⟩
  have := G.dual.finite_tate C
  have hp0 : (p : O) ≠ 0 := fun h => by
    have h1 := congrArg (algebraMap O C) h
    rw [map_natCast, map_zero] at h1
    exact Nat.cast_ne_zero.2 hpp.ne_zero h1
  have : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  have key : ∀ κ : O, v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C) → ∀ n (y : Cot O (G.A n)),
      κ • y ∈ (LinearMap.range (dlogLinear G)).map (lev G n) := fun κ hκ n y => by
    have hch : ∀ u (hu : IsGroupLikeElem O u),
        charFun O (G.A n) (toConv (evalPoint u hu)) = u := fun u hu =>
      CartierDual.eq_of_forall_apply (R := O) fun φ => apply_charFun _ φ
    have : Finite (CartierDual O (G.A n) →ₐ[O] O) :=
      Nat.finite_of_card_ne_zero ((G.dual.natCard_pts_eq C n).trans_ne (pow_ne_zero _ hpp.ne_zero))
    refine smul_dUnit_mem p C v O hv hp (G.A n)
      ((Set.finite_range fun χ : CartierDual O (G.A n) →ₐ[O] O =>
        charFun O (G.A n) (toConv χ)).subset fun u hu => ⟨_, hch u hu⟩)
      ((p : O) ^ n) (pow_ne_zero _ hp0) _ (fun u hu => ?_)
      (fun y => by rw [pow_smul_cot]; exact zero_mem _) κ hκ y
    obtain ⟨χ, hχ⟩ := G.dual.pt_surjective C n (evalPoint u hu)
    refine ⟨dlog G χ, ⟨1 ⊗ₜ χ, by rw [dlogLinear_tmul, one_smul]⟩, ?_⟩
    rw [lev_apply, dlog_val, ← hch u hu, ← hχ]
    rfl
  refine smul_mem_of_levels G _ (Submodule.fg_range _) κ (key κ hκ) (key p ?_) w
  rw [map_natCast]
  exact pow_le_of_le_one zero_le hp.le (Nat.sub_pos_of_lt hpp.one_lt).ne'

theorem hodgeTateCokerSharp : GlobalTheory.CompanionTheory.Ar.HT.HodgeTateCokerSharp := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO G κ hκ w
  obtain ⟨z, hz⟩ := smul_mem_range_dlogLinear p C v O hv hp G.dual κ hκ w
  rw [← hz]
  clear hz
  induction z with
  | zero => simp
  | tmul c χ =>
    obtain ⟨t, rfl⟩ := (tateCongr O G.bidual).surjective χ
    exact ⟨c ⊗ₜ t, rfl⟩
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

end PositivityTheory.HtPt.Farsharp
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.LbIsoPullPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace PositivityTheory.HtPt.Cf

def PF {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] (L : LB G.left) : Prop :=
  ∃ (T : TorusExtension G) (M : LB T.B.left),
    letI := T.grpB
    M.IsLB ∧ Out.KTriv T.B M ∧ LBIso L (M.pull T.q.left)

def teBC {k k₂ : Type} [Field k] [Field k₂] (f : Sp k₂ ⟶ Sp k) {G : Over (Sp k)} [GrpObj G]
    (T : TorusExtension G) : TorusExtension ((Over.pullback f).obj G) :=
  letI := T.grpB
  letI := T.addCommGroup
  haveI := T.q_hom
  haveI := T.i_hom
  { X := T.X
    addCommGroup := T.addCommGroup
    free := T.free
    finite := T.finite
    B := (Over.pullback f).obj T.B
    isAbelian :=
      { comm := by have := T.isAbelian.comm; infer_instance
        smooth := by have := T.isAbelian.smooth; show Smooth (pullback.snd _ _); infer_instance
        proper := by have := T.isAbelian.proper; show IsProper (pullback.snd _ _); infer_instance
        geomConnected := by
          have := T.isAbelian.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
    q := Out.GtBCPf.qB f T.q
    q_hom := inferInstance
    q_flat := Out.GtBCPf.qB_flat f T.q T.q_flat
    q_surjective := Out.GtBCPf.qB_surj f T.q T.q_surjective
    q_quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact) (Out.GtBCPf.qB_sq f T.q) T.q_quasiCompact
    i := Out.GtBCPf.iB f T.X T.i
    i_hom := Out.GtBCPf.iB_hom f T.X T.i
    isKernel := Out.GtBCPf.iB_isKernel f T.X T.q T.i T.isKernel }

theorem lbIso_refl {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ?_))
  refine (congrArg₂ (· * ·) (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show _ * _ * gm (𝟙 X) y (L.U q.1 ⊓ L.U q.2) (L.g q.1 q.2) = gm (𝟙 X) y (L.U p.1 ⊓ L.U p.2) (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem lbIso_pull_pull {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) (g : Z ⟶ Y) (h : Z ⟶ X)
    (e : g ≫ F = h) : LBIso (L.pull h) ((L.pull F).pull g) :=
  LBIso.chartPull (chartPullId _) (chartPullLinComb L F (fun _ : PUnit => g) (fun _ => h) (fun _ => 1) (𝟙 Z)
    fun _ => e.trans (Category.id_comp _).symm) (lbIso_refl (pull_isLB hL h))

theorem pf_pull {k k₂ : Type} [Field k] [Field k₂] (f : Sp k₂ ⟶ Sp k) {G : Over (Sp k)} [GrpObj G]
    {G₂ : Over (Sp k₂)} [GrpObj G₂] {φ : G₂.left ⟶ G.left} (h : IsGrpPullback G₂ G f φ) {L : LB G.left}
    {L₂ : LB G₂.left} (hL : L.IsLB) (hL₂ : L₂.IsLB) (w : LBIso L₂ (L.pull φ)) (H : PF G L) : PF G₂ L₂ := by
  obtain ⟨T, M, hM, hK, hi⟩ := H
  let := T.grpB
  obtain ⟨e, he, hφ⟩ := grpPullback_iso (isGrpPullback_pullback G f) h
  have hM₂ := pull_isLB hM (pullback.fst T.B.hom f)
  obtain ⟨u, hu⟩ := lbIso_refl hM₂
  have hK₂ := kTriv_pull (isGrpPullback_pullback T.B f) hM hM₂ ((isGen_iff u).1 hu) hK
  refine ⟨torusExtOfIso e (teBC f T), M.pull (pullback.fst T.B.hom f), hM₂, hK₂, ?_⟩
  have hc : (e.inv ≫ Out.GtBCPf.qB f T.q).left ≫ pullback.fst T.B.hom f = φ ≫ T.q.left := by
    rw [Over.comp_left, Category.assoc, Out.GtBCPf.qB_h, ← hφ, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      e.inv_hom_id, Over.id_left, Category.id_comp]
  exact LBIso.trans hL₂ (pull_isLB hL φ) (pull_isLB hM₂ _) w
    (LBIso.chartPull (chartPullPull L φ φ rfl) (chartPullLinComb M (pullback.fst T.B.hom f)
      (fun _ : PUnit => (e.inv ≫ Out.GtBCPf.qB f T.q).left) (fun _ => T.q.left) (fun _ => 1) φ fun _ => hc) hi)

theorem geompf_bc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0), (∀ (k k₂ : Type) [Field k] [Field k₂] (f : k →+* k₂) (x : Sp k ⟶ X0), GeomPF t x → GeomPF t (spMap f ≫ x)) ∧ ∀ (X₂ : Scheme.{0}) (t₂ : SAB H X₂) (f : X₂ ⟶ X0) (_ : SABMap t₂ t f) (k : Type) [Field k] (x : Sp k ⟶ X₂), GeomPF t₂ x ↔ GeomPF t (x ≫ f) := by
  intro E _ _ _ H X0 t
  have hL := t.PP.isLB
  refine ⟨fun k k₂ _ _ f x h => ?_, fun X₂ t₂ f m k _ x => ?_⟩
  · let φ : pullback t.G.hom (spMap f ≫ x) ⟶ pullback t.G.hom x :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap f) (by rw [Category.assoc, pullback.condition])
    have e : φ ≫ pullback.fst t.G.hom x = pullback.fst _ _ := pullback.lift_fst _ _ _
    have hg : IsGrpPullback ((Over.pullback (spMap f ≫ x)).obj t.G) ((Over.pullback x).obj t.G) (spMap f) φ :=
      (isGrpPullback_pullback t.G x).cancel ((isGrpPullback_pullback t.G _).congr rfl e.symm) (pullback.lift_snd _ _ _)
    exact pf_pull (spMap f) hg (pull_isLB hL _) (pull_isLB hL _) (lbIso_pull_pull hL _ φ _ e) h
  · have hL₂ := t₂.PP.isLB
    have h₁ := (isGrpPullback_pullback t₂.G x).comp m.cart
    have h₂ := isGrpPullback_pullback t.G (x ≫ f)
    obtain ⟨w, hw, -⟩ := m.lin
    have w₁ : LBIso (t₂.PP.L.pull (pullback.fst t₂.G.hom x)) ((t.PP.L.pull m.cm.F).pull (pullback.fst t₂.G.hom x)) :=
      LBIso.chartPull (chartPullPull _ _ _ rfl) (chartPullPull _ _ _ rfl) ⟨w, hw⟩
    have w₂ := LBIso.trans (pull_isLB hL₂ _) (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) w₁
      (lbIso_pull_pull hL m.cm.F (pullback.fst t₂.G.hom x) _ rfl).symm
    constructor
    · intro h
      obtain ⟨e, he, hφ⟩ := grpPullback_iso h₂ h₁
      refine pf_pull (𝟙 _) (isGrpPullback_of_iso e) (pull_isLB hL₂ _) (pull_isLB hL _) ?_ h
      refine LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL₂ _) _)
        (lbIso_pull_pull hL _ e.hom.left _ hφ) ?_
      exact LBIso.chartPull (chartPullPull _ _ _ rfl) (chartPullPull _ _ _ rfl) w₂.symm
    · intro h
      obtain ⟨e, he, hφ⟩ := grpPullback_iso h₁ h₂
      refine pf_pull (𝟙 _) (isGrpPullback_of_iso e) (pull_isLB hL _) (pull_isLB hL₂ _) ?_ h
      exact LBIso.trans (pull_isLB hL₂ _) (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) w₂
        (lbIso_pull_pull hL _ e.hom.left _ hφ)

theorem exists_common {X₂ X0 : Scheme.{0}} (f : X₂ ⟶ X0) (z : X₂) {k : Type} [Field k] (x : Sp k ⟶ X0)
    (hx : x (IsLocalRing.closedPoint k) = f z) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (y : Sp Ω ⟶ X₂) (a : k →+* Ω),
      y (IsLocalRing.closedPoint Ω) = z ∧ y ≫ f = spMap a ≫ x := by
  obtain ⟨s, hs, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := x) z _ hx.symm
  let P := pullback f x
  let Ω := AlgebraicClosure (P.residueField s)
  let r : Sp Ω ⟶ P := spMap (algebraMap (P.residueField s) Ω) ≫ P.fromSpecResidueField s
  have hr : r (IsLocalRing.closedPoint Ω) = s := Scheme.fromSpecResidueField_apply s _
  refine ⟨Ω, inferInstance, inferInstance, r ≫ pullback.fst f x, (Spec.preimage (r ≫ pullback.snd f x)).hom, ?_, ?_⟩
  · exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (pullback.fst f x) hr).trans hs)
  · show _ = Spec.map (Spec.preimage (r ≫ pullback.snd f x)) ≫ x
    rw [Spec.map_preimage, Category.assoc r, Category.assoc r, pullback.condition]

theorem fibpf_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (X₂ : Scheme.{0}) (t₂ : SAB H X₂) (f : X₂ ⟶ X0) (_ : SABMap t₂ t f) (z : X₂), FibPF t₂ z ↔ FibPF t (f z) := by
  intro E _ _ _ H X0 t X₂ t₂ f m z
  constructor
  · rintro ⟨k, _, _, x, rfl, h⟩
    exact ⟨k, _, inferInstance, x ≫ f, Scheme.Hom.comp_apply _ _ _, ((geompf_bc E H X0 t).2 X₂ t₂ f m k x).1 h⟩
  · rintro ⟨k, _, _, x, hx, h⟩
    obtain ⟨Ω, _, _, y, a, hy, e⟩ := exists_common f z x hx
    exact ⟨Ω, _, inferInstance, y, hy,
      ((geompf_bc E H X0 t).2 X₂ t₂ f m Ω y).2 (e ▸ (geompf_bc E H X0 t).1 k Ω a x h)⟩

end PositivityTheory.HtPt.Cf
end
end

