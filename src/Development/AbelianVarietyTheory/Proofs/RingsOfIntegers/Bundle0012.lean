import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.CartesianLiftThreeCompProjection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0015
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0016
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtDvdOfSecIsMul
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace WeightDvd

theorem gs_comp_stalkMap {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [← gs_pull r g z U h, gs_stalkMap r z _ h]
  exact congrArg _ ((gs_pull (𝟙 Y) g (r z) U h a).trans (by rw [Category.id_comp]))

theorem appLE_dvd {P T : Scheme.{0}} [IsAffine P] (p : P ⟶ T) (W : T.Opens) (e : ⊤ ≤ p ⁻¹ᵁ W) (u v : Γ(T, W))
    (h : ∀ w ∈ W, gs (𝟙 T) w W u ∣ gs (𝟙 T) w W v) : (p.appLE W ⊤ e).hom u ∣ (p.appLE W ⊤ e).hom v := by
  rw [← Ideal.mem_span_singleton, (isAffineOpen_top P).mem_ideal_iff]
  intro z hz
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  have k : ∀ c : Γ(T, W), (P.presheaf.germ ⊤ z hz).hom ((p.appLE W ⊤ e).hom c) =
      (p.stalkMap z).hom (gs (𝟙 T) (p z) W c) := fun c =>
    ((gs_eq (𝟙 P) z ⊤ hz _).symm.trans (gs_appLE p W ⊤ e (𝟙 P) z hz c)).trans
      ((by rw [Category.id_comp] : gs (𝟙 P ≫ p) z W c = gs p z W c).trans (gs_stalkMap p z W (e hz) c))
  have := map_dvd (p.stalkMap z).hom (h (p z) (e hz))
  rw [← k, ← k] at this
  exact this

theorem dvd_of_sum {S : Scheme.{0}} (X : Type) [AddCommGroup X] (Y : Over S) {V : Y.left.Opens} (hV : IsAffineOpen V)
    (s : Finset X) (a : Γ(Y.left, V)) (h : X → Γ(Y.left, V))
    (hs : ∀ w : (splitTorus S X ⊗ Y).left, (snd (splitTorus S X) Y).left w ∈ V →
      gs (snd (splitTorus S X) Y).left w V a ∣
        ∑ χ ∈ s, gs (𝟙 _) w ⊤ (TorusInj.chiP X Y χ) * gs (snd (splitTorus S X) Y).left w V (h χ)) :
    ∀ χ ∈ s, a ∣ h χ := by
  intro χ₀ hχ₀
  have k : ∀ (w : (splitTorus S X ⊗ Y).left) (hw : (snd (splitTorus S X) Y).left w ∈ V) (c : Γ(Y.left, V)),
      gs (𝟙 _) w ((snd (splitTorus S X) Y).left ⁻¹ᵁ V) (((snd (splitTorus S X) Y).left.app V).hom c) =
        gs (snd (splitTorus S X) Y).left w V c := fun w hw c =>
    (gs_pull (𝟙 _) _ w V hw c).trans (by rw [Category.id_comp])
  have H := appLE_dvd (TorusInj.pt (X := X) hV) _ (TorusInj.pt_le hV) (((snd (splitTorus S X) Y).left.app V).hom a)
    (∑ χ ∈ s, ((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE le_top).op).hom (TorusInj.chiP X Y χ) *
      ((snd (splitTorus S X) Y).left.app V).hom (h χ)) fun w hw => by
      rw [k w hw, gs_fsum (𝟙 _) w _ hw]
      refine (hs w hw).trans (dvd_of_eq (Finset.sum_congr rfl fun χ _ => ?_))
      rw [gs_mul (𝟙 _) w _ hw, k w hw, gs_res (𝟙 _) w _ hw]
  have H' : TorusInj.ev hV (((snd (splitTorus S X) Y).left.app V).hom a) ∣ TorusInj.ev hV
      (∑ χ ∈ s, ((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE le_top).op).hom (TorusInj.chiP X Y χ) *
      ((snd (splitTorus S X) Y).left.app V).hom (h χ)) :=
    map_dvd (Scheme.ΓSpecIso (TorusInj.GA (X := X) (V := V))).hom.hom H
  simp only [map_sum, map_mul, TorusInj.ev_chi, TorusInj.ev_snd, AddMonoidAlgebra.single_mul_single,
    add_zero, _root_.one_mul] at H'
  obtain ⟨g, hg⟩ := H'
  have hc := congrArg (fun f => f.coeff χ₀) hg
  rw [TorusInj.coeff_sum_single X s _ χ₀ hχ₀] at hc
  refine ⟨g.coeff χ₀, hc.trans ?_⟩
  simp

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)

theorem val_act (β : D.toPre.X) (w : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left) {J}
    (hJ : Good D.toPre.P.L w J) :
    (val (tG U e β) (WeightPf.act (U.gt e)).left w J).val =
      gs (𝟙 _) w ⊤ (TorusInj.chiP D.toPre.X (thickObj R I e G) β) *
        (val (tG U e β) (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left w J).val := by
  have E := val_corr hJ ((U.gt e).t_weight β) (𝟙 _)
  rw [val_mul hJ, val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at E
  refine (congrArg Units.val E).trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) ?_ rfl))
  have hm := hJ.mem (L := D.toPre.P.L) (K := PEmpty) (Y := (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left)
    PEmpty.elim (𝟙 _)
  exact (congrArg Units.val (gm_rp₁ (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left w ⊤ _ _ hm
    (charUnit _ D.toPre.X β))).trans ((gs_unit _ w ⊤ trivial _).symm.trans
      ((gs_pull (𝟙 _) (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left w ⊤ trivial _).trans
        (by rw [Category.id_comp])).symm)

theorem dvd_on_group (r : R) (σ τ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (hσ : SecIsMul G.hom r σ τ)
    (hE : U.ExpandsAt e k σ f) (α : D.toPre.X) (y : (thickObj R I e G).left) (J) (hJ : Good D.toPre.P.L y J) :
    cst (pGl U e ≫ D.toPre.P.A.hom) y r ∣ sval (f α) (pGl U e) y J := by
  classical
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f hE
  by_cases hα : α ∉ S
  · have := (hS _ (𝟙 _) y J hJ).1 α hα
    rw [Category.id_comp] at this
    rw [this]
    exact dvd_zero _
  push Not at hα
  let jf : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun β a => J (pGl U e ≫ D.toPre.famφB β a)
  let jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun β a => J (Oφl U e β a)
  have hy : y ∈ S.inf (fun β => pGl U e ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β) ⊓
      LB.wchart D.toPre.P.L (Oφl U e β) (jt β)) :=
    mem_finf S _ _ fun β _ => ⟨hJ.mem (D.toPre.famφB β) (pGl U e), Set.mem_iInter.2 fun a => hJ _⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVW⟩ := ((thickObj R I e G).left.isBasis_affineOpens).exists_subset_of_mem_open hy
    (S.inf (fun β => pGl U e ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β) ⊓
      LB.wchart D.toPre.P.L (Oφl U e β) (jt β))).2
  have hVW' : V ≤ S.inf (fun β => pGl U e ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β) ⊓
      LB.wchart D.toPre.P.L (Oφl U e β) (jt β)) := hVW
  have hVf : ∀ β ∈ S, V ≤ pGl U e ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β) :=
    fun β hβ => hVW'.trans ((Finset.inf_le hβ).trans inf_le_left)
  have hVt : ∀ β ∈ S, V ≤ LB.wchart D.toPre.P.L (Oφl U e β) (jt β) :=
    fun β hβ => hVW'.trans ((Finset.inf_le hβ).trans inf_le_right)
  have ex : ∀ β ∈ S, ∃ c : Γ((thickObj R I e G).left, V), ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (thickObj R I e G).left) (z : Z),
      ρ z ∈ V → gs ρ z V c = gs (ρ ≫ pGl U e) z (LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β)) ((f β).f (jf β)) *
        (gm ρ z (LB.wchart D.toPre.P.L (Oφl U e β) (jt β)) ((tG U e β).s (jt β))).val := fun β hβ =>
    ⟨((pGl U e).appLE _ V (hVf β hβ)).hom ((f β).f (jf β)) * (res (hVt β hβ) ((tG U e β).s (jt β))).val,
      fun Z ρ z hz => (gs_mul ρ z V hz _ _).trans (congrArg₂ (· * ·) (gs_appLE _ _ V _ ρ z hz _)
        ((gs_unit ρ z V hz _).trans (congrArg Units.val (gm_res ρ z _ hz _))))⟩
  choose! c hc using ex
  have hpG := WeightPf.act_left_pG (U.gt e)
  have hb : pGl U e ≫ D.toPre.P.A.hom = fGl I G e ≫ G.hom :=
    (Over.w (U.gt e).pG).trans (Over.w (fstG I e G)).symm
  have H := dvd_of_sum D.toPre.X (thickObj R I e G) hV S (constFn (pGl U e ≫ D.toPre.P.A.hom) V r) c (fun w hw => by
    choose d hd using fun ψ : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left ⟶ D.toPre.P.A.left =>
      exists_chart D.toPre.P.isLB (ψ w)
    let J₂ : ((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι := fun ψ =>
      if ψ w ∈ D.toPre.P.L.U (J ((WeightPf.sec (D := D.toPre) (G := G) (I := I) (e := e)).left ≫ ψ)) then
        J ((WeightPf.sec (D := D.toPre) (G := G) (I := I) (e := e)).left ≫ ψ) else d ψ
    have hJ₂ : Good D.toPre.P.L w J₂ := fun ψ => by
      by_cases h : ψ w ∈ D.toPre.P.L.U (J ((WeightPf.sec (D := D.toPre) (G := G) (I := I) (e := e)).left ≫ ψ))
      · simpa only [J₂, if_pos h] using h
      · simpa only [J₂, if_neg h] using hd ψ
    have eJ : ∀ φ : (thickObj R I e G).left ⟶ D.toPre.P.A.left,
        φ ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left w) ∈ D.toPre.P.L.U (J φ) →
        J₂ ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ φ) = J φ := fun φ h => by
      have e₁ : (WeightPf.sec (D := D.toPre) (G := G) (I := I) (e := e)).left ≫
          (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ φ = φ := by
        rw [← Category.assoc, WeightPf.sec_left_snd, Category.id_comp]
      simp only [J₂, e₁]
      exact if_pos h
    obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB (fGl I G e ((WeightPf.act (U.gt e)).left w))
    have E := (hS _ (WeightPf.act (U.gt e)).left w J₂ hJ₂).2 jL hL
    have hs : sv U k σ ((WeightPf.act (U.gt e)).left ≫ fGl I G e) w jL =
        cst (((WeightPf.act (U.gt e)).left ≫ fGl I G e) ≫ G.hom) w r *
          sv U k τ ((WeightPf.act (U.gt e)).left ≫ fGl I G e) w jL :=
      secIsMul_gs hσ _ w (fun _ => jL) (Set.mem_iInter.2 fun _ => hL)
    have e₂ : ((WeightPf.act (U.gt e)).left ≫ fGl I G e) ≫ G.hom =
        (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ pGl U e ≫ D.toPre.P.A.hom := by
      rw [Category.assoc, ← hb, ← Category.assoc, hpG, Category.assoc]
    rw [hs, e₂, mul_left_comm] at E
    refine (dvd_of_eq (gs_constFn _ V _ w hw r)).trans ((Dvd.intro _ E).trans
      (dvd_of_eq (Finset.sum_congr rfl fun β hβ => ?_)))
    rw [hc β hβ _ _ w hw, val_act U e β w hJ₂, mul_left_comm, hpG,
      sval_of (f β) _ w J₂ (jf β) (fun a => by
        rw [Category.assoc]; exact eJ _ (Set.mem_iInter.1 (hVf β hβ hw) a)),
      val_of (tG U e β) _ w J₂ (jt β) (fun a => eJ _ (Set.mem_iInter.1 (hVt β hβ hw) a))]) α hα
  obtain ⟨g, hg⟩ := H
  have E := hc α hα _ (𝟙 _) y hyV
  rw [hg, gs_mul (𝟙 _) y V hyV, gs_constFn _ V (𝟙 _) y hyV, Category.id_comp, Category.id_comp] at E
  exact (Units.dvd_mul_right).1 (Dvd.intro _ E)

end WeightDvd

theorem expandsAt_dvd_of_secIsMul : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ) (r : R) (σ τ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), SecIsMul G.hom r σ τ → U.ExpandsAt e k σ f → ∀ (α : D.toPre.X) (x : (thickObj R I e D.toPre.P.A).left) (J), Geo.Tor.Good D.toPre.P.L x J → Geo.Tor.cst ((fstG I e D.toPre.P.A).left ≫ D.toPre.P.A.hom) x r ∣ Geo.Tor.sval (f α) (fstG I e D.toPre.P.A).left x J := by
  intro R _ _ I D A G _ _ U e k r σ τ f hσ hE α x J hJ
  have := (U.gt e).q_flat
  obtain ⟨y, rfl⟩ := (U.gt e).q_surj.surj x
  choose J' hJ' using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have H := WeightDvd.dvd_on_group U e k r σ τ f hσ hE α y J' hJ'
  have hm := hJ.mem (D.toPre.famφB α) (fstG I e D.toPre.P.A).left
  have e₁ := WeightDvd.gs_comp_stalkMap (U.gt e).q.left (fstG I e D.toPre.P.A).left y _ hm
    ((f α).f fun a => J ((fstG I e D.toPre.P.A).left ≫ D.toPre.famφB α a))
  have e₂ := WeightDvd.gs_comp_stalkMap (U.gt e).q.left ((fstG I e D.toPre.P.A).left ≫ D.toPre.P.A.hom) y ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
  have e₃ := sec_trans (f α) (pGl U e) y hm (Good.mem hJ' (D.toPre.famφB α) (pGl U e))
  refine dvd_descend (U.gt e).q.left y ?_
  exact (dvd_of_eq e₂.symm).trans ((H.mul_left _).trans (dvd_of_eq (e₃.symm.trans e₁)))

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HasGenPull
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullGenG

theorem hasGen_one {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) :
    HasGen Lr.L (lf (Finsupp.single (1 : G ⟶ G) 1)) := by
  have h0 := (HasGen.of_gen (L := Lr.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) Lr.rig Lr.rigGen).pull G.hom
  have e1 : (1 : G ⟶ G).left = G.hom ≫ eSec G := rfl
  convert h0 using 1
  rw [lf_single, e1]
  simp [fsum, Finsupp.mapDomain_single]

theorem hasGen_pull {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) (cub : CubicalStr G Lr)
    {O : Type} [CommRing O] [StarRing O] (ra : RingAct G O) (w0 a : O) (N : ℕ) (hN : a * star a = (N : O))
    (hadj : Geo.Tor.LBIso (cubeLB G ![fst G G ≫ ra.act a, snd G G] Lr.L)
      (cubeLB G ![fst G G, snd G G ≫ ra.act (star a)] Lr.L))
    (hprim : Geo.Tor.LBIso Lr.L (cubeLB G ![𝟙 G, ra.act w0] Lr.L)) (k : ℕ) :
    HasGen Lr.L (fsum (K := Fin 2) ![𝟙 G.left, (ra.act a).left] ![((k * N : ℕ) : ℤ), -(k : ℤ)]) := by
  have := ra.hom w0
  obtain ⟨uR, huR⟩ := GlobalTheory.NormRos.exists_gen_rosati Lr.isLB (ra.act a) (ra.act (star a)) hadj
  obtain ⟨⟨ρ, hρ, -⟩, -⟩ := GlobalTheory.JetSer.exists_unique_normPrim S G Lr (ra.act w0) hprim
  have hP : HasGen Lr.L (fsum (GlobalTheory.JetSer.primφ (ra.act w0)) GlobalTheory.JetSer.primε) := HasGen.of_gen ρ hρ
  have h1 := hasGen_one Lr
  obtain ⟨uΨ, huΨ⟩ := HasGen.gen Lr.isLB (h1.sub hP) (K' := Fin 4)
    ![(padd G (𝟙 _) (ra.act w0)).left, 𝟙 G.left, (ra.act w0).left, (toUnit G ≫ η[G]).left] ![1, -2, -1, 2] (by
      unfold GlobalTheory.JetSer.primφ GlobalTheory.JetSer.primε
      have e1 : toUnit G ≫ η[G] = (1 : G ⟶ G) := rfl
      rw [padd_eq_mul, e1, lf_single]
      classical
      ext x
      simp [fsum, Fin.sum_univ_succ, Finsupp.single_apply]
      split_ifs <;> omega)
  have hM := hasGen_pullMul ra w0 a N hN uΨ huΨ uR huR cub.t cub.isGen
  have h2 := (hM.zsmul (-(k : ℤ))).add (h1.zsmul ((k : ℤ) * ((N : ℤ) - 1)))
  convert h2 using 1
  classical
  simp only [lf_add, lf_sub, lf_smul, lf_single]
  ext x
  simp [fsum, Fin.sum_univ_succ, Finsupp.single_apply]
  split_ifs <;> ring

theorem exists_norm {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) (f : G ⟶ G) [IsMonHom f]
    (k N : ℕ) (hN1 : 1 ≤ N)
    (h : HasGen Lr.L (fsum (K := Fin 2) ![𝟙 G.left, f.left] ![((k * N : ℕ) : ℤ), -(k : ℤ)])) :
    ∃ u : LB.Gen (LB.LinComb Lr.L (K := Fin 2) ![gK, endK f ≫ gK] ![((k * N : ℕ) : ℤ), -(k : ℤ)]), u.IsGen ∧
      LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u unitK)
        (LB.pullGen Lr.L _ _ (GeneratorPullback.powGen Lr.L _ _ Lr.rig (k * (N - 1))) (jK V)) := by
  have hc : endK f ≫ gK = gK ≫ f.left := by
    unfold endK gK
    exact pullback.lift_fst _ _ _
  have hu : unitK ≫ gK = jK V ≫ eSec G := by
    unfold unitK gK
    exact pullback.lift_fst _ _ _
  have hs : unitK ≫ pullback.snd G.hom (jK V) = 𝟙 _ := by
    unfold unitK
    exact pullback.lift_snd _ _ _
  have he : eSec G ≫ f.left = eSec G := by
    show (η[G] ≫ f).left = η[G].left
    rw [IsMonHom.one_hom]
  obtain ⟨t, ht⟩ := HasGen.gen Lr.isLB (h.pull gK) ![gK, endK f ≫ gK] ![((k * N : ℕ) : ℤ), -(k : ℤ)] (by
    rw [hc]
    simp only [fsum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Finsupp.mapDomain_add, Finsupp.mapDomain_single, Category.comp_id])
  refine exists_normalized_to Lr.isLB _ _ t ht (pullback.snd G.hom (jK V)) unitK hs _ _ _
    (pullGen_isGen_of_isGen _ _ _ (powGen_isGen_of_isGen _ Lr.rigGen _) _) ?_
  have hv : unitK ≫ endK f ≫ gK = jK V ≫ eSec G := by
    rw [hc, ← Category.assoc, hu, Category.assoc, he]
  simp only [fsum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hu, hv]
  rw [Fintype.sum_unique, ← Finsupp.single_add]
  congr 1
  push_cast [Nat.cast_sub hN1]
  ring

theorem main : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ k : ℕ, ∃ u : LB.Gen (LB.LinComb P.U.LG.L (K := Fin 2) ![gK, endK (t.act.act a) ≫ gK] ![((k * N : ℕ) : ℤ), -(k : ℤ)]), u.IsGen ∧ LB.Gen.Corr P.U.LG.L _ _ _ _ (LB.pullGen P.U.LG.L _ _ u unitK) (LB.pullGen P.U.LG.L _ _ (GeneratorPullback.powGen P.U.LG.L _ _ P.U.LG.rig (k * (N - 1))) (jK V)) := by
  intro hG V _ _ _ E _ _ _ H t P a N hN hN0
  letI := H.starRing
  intro k
  have := t.act.hom a
  rw [P.bundle]
  exact exists_norm t.PP (t.act.act a) k N hN0
    (hasGen_pull t.PP t.cub t.act.toRingAct H.w0 a N hN (t.adj a) t.prim k)

end GlobalTheory.PullGenG
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ImportsBis
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ExpandsFracLinear

open GlobalTheory.ExpandsLinear

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k n : ℕ) (c : Fin n → FractionRing R) (s : Fin n → U.SecK k) (E : Fin n → Fam D.toPre (FractionRing R) k) (s₀ : U.SecK k), (∀ l, U.Expands k (s l) (E l)) → (∀ jj, s₀.f jj = ∑ l, resTop _ (scal (pullback.snd G.hom (jK R)) (c l)) * (s l).f jj) → U.Expands k s₀ (∑ l, c l • E l) := by
  intro R _ _ I D A G _ _ U k n c s E s₀ hE hs
  simp only [UnifPre.Expands] at hE ⊢
  choose r hr σ f h1 h2 h3 using hE
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) (Finset.univ : Finset (Fin n))
    (fun l => c l / algebraMap R (FractionRing R) (r l))
  choose a ha using fun l => hb l (Finset.mem_univ l)
  have hc : ∀ l, algebraMap R (FractionRing R) (a l) * algebraMap R (FractionRing R) (r l) =
      algebraMap R (FractionRing R) (b : R) * c l := by
    intro l
    have hrl : algebraMap R (FractionRing R) (r l) ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap R (FractionRing R))]
      exact fun h => hr l (IsFractionRing.injective R (FractionRing R) h)
    rw [ha l, Algebra.smul_def]
    field_simp
  refine ⟨b, nonZeroDivisors.ne_zero b.2, secComb (fun l => scal G.hom (a l)) σ,
    fun α => secComb (fun l => scal D.toPre.P.A.hom (a l)) (fun l => f l α), ?_, ?_, ?_⟩
  · exact secScal_comb (algebraMap R (FractionRing R)) U.LG.L _ _ _ _ (pullback.fst G.hom (jK R))
      (pullback.snd G.hom (jK R)) _ G.hom rfl pullback.condition s σ r a b c hc h1 s₀ hs
  · intro α
    refine secScal_comb (algebraMap R (FractionRing R)) D.toPre.P.L _ _ _ _ (D.toPre.prB (FractionRing R)).left
      (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left _ D.toPre.P.A.hom ?_ ?_ (fun l => (E l).s α)
      (fun l => f l α) r a b c hc (fun l => h2 l α) _ ?_
    · have hh := (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).symm
      unfold DegPre.BF TF at *
      rw [hh]
      congr 1
      show jFK (FractionRing R) ≫ jK R = _
      unfold jFK jK
      rw [← Spec.map_comp]
      rfl
    · exact Over.w (D.toPre.prB (FractionRing R))
    · intro j
      rw [fam_sum_f]
      simp only [smul_f]
      rfl
  · intro e
    exact expandsAt_linear R I D A G U k e n a σ f _ _ (fun l => h3 l e) (fun j => rfl) (fun α j => rfl)

end GlobalTheory.ExpandsFracLinear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsMonHomOfComm
section
namespace GlobalTheory.PowMap

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

variable {S : Scheme.{0}}

noncomputable def powHom {G B : Over S} (q : G ⟶ B) : ∀ n : ℕ, powObj G n ⟶ powObj B n
  | 0 => 𝟙 (𝟙_ (Over S))
  | n + 1 => (q ⊗ₘ powHom q n : G ⊗ powObj G n ⟶ B ⊗ powObj B n)

theorem powHom_pr {G B : Over S} (q : G ⟶ B) :
    ∀ (n : ℕ) (i : Fin n), powHom q n ≫ powPr B i = powPr G i ≫ q
  | 0, i => i.elim0
  | n + 1, i => by
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tensorHom_fst q (powHom q n)
    · show (q ⊗ₘ powHom q n) ≫ snd _ _ ≫ powPr B i = (snd _ _ ≫ powPr G i) ≫ q
      rw [tensorHom_snd_assoc, powHom_pr q n i, Category.assoc]

theorem prop_powHom (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {G B : Over S} (q : G ⟶ B) (hq : P q.left) : ∀ n : ℕ, P (powHom q n).left
  | 0 => P.id_mem S
  | n + 1 => by
    have ih := prop_powHom P q hq n
    show P (q ⊗ₘ powHom q n).left
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := P) hq ih (Over.w q).symm (Over.w (powHom q n)).symm

theorem prop_of_comm (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {G' G B' B : Over S} [GrpObj G'] [GrpObj G] [GrpObj B'] [GrpObj B] {j : ℕ} (p : IsPowGrp G' G j)
    (pB : IsPowGrp B' B j) (q : G ⟶ B) (q' : G' ⟶ B') (h : ∀ i, q' ≫ pB.pr i = p.pr i ≫ q)
    (hq : P q.left) : P q'.left := by
  let e : G' ≅ powObj G j := p.lim.conePointUniqueUpToIso (powIsLimit G j)
  let f : B' ≅ powObj B j := pB.lim.conePointUniqueUpToIso (powIsLimit B j)
  have he : ∀ i, e.hom ≫ powPr G i = p.pr i := fun i =>
    p.lim.conePointUniqueUpToIso_hom_comp (powIsLimit G j) ⟨i⟩
  have hf : ∀ i, f.inv ≫ pB.pr i = powPr B i := fun i =>
    pB.lim.conePointUniqueUpToIso_inv_comp (powIsLimit B j) ⟨i⟩
  have hq' : q' = e.hom ≫ powHom q j ≫ f.inv := by
    refine pB.lim.hom_ext fun ⟨i⟩ => ?_
    show q' ≫ pB.pr i = (e.hom ≫ powHom q j ≫ f.inv) ≫ pB.pr i
    rw [h, Category.assoc, Category.assoc, hf, powHom_pr, ← Category.assoc, he]
  have i1 : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have i2 : IsIso f.inv.left := inferInstanceAs (IsIso ((Over.forget _).map f.inv))
  rw [hq', Over.comp_left, Over.comp_left, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
  exact prop_powHom P q hq j

theorem isMonHom_of_comm {G' G B' B : Over S} [GrpObj G'] [GrpObj G] [GrpObj B'] [GrpObj B] {j : ℕ}
    (p : IsPowGrp G' G j) (pB : IsPowGrp B' B j) (q : G ⟶ B) (q' : G' ⟶ B')
    (h : ∀ i, q' ≫ pB.pr i = p.pr i ≫ q) (hq : IsMonHom q) : IsMonHom q' := by
  refine ⟨pB.lim.hom_ext fun ⟨i⟩ => ?_, pB.lim.hom_ext fun ⟨i⟩ => ?_⟩
  · have := p.hom i
    have := pB.hom i
    show (η ≫ q') ≫ pB.pr i = η ≫ pB.pr i
    rw [Category.assoc, h, IsMonHom.one_hom, IsMonHom.one_hom]
  · have := p.hom i
    have := pB.hom i
    show (μ ≫ q') ≫ pB.pr i = ((q' ⊗ₘ q') ≫ μ) ≫ pB.pr i
    rw [Category.assoc, Category.assoc, h, IsMonHom.mul_hom, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, h]

theorem main : ∀ (S : Scheme.{0}) (G' G B' B : Over S) [GrpObj G'] [GrpObj G] [GrpObj B'] [GrpObj B] (j : ℕ) (p : IsPowGrp G' G j) (pB : IsPowGrp B' B j) (q : G ⟶ B), ∃ q' : G' ⟶ B', (∀ i, q' ≫ pB.pr i = p.pr i ≫ q) ∧ (IsMonHom q → IsMonHom q') ∧ (Flat q.left → Flat q'.left) ∧ (Surjective q.left → Surjective q'.left) ∧ (QuasiCompact q.left → QuasiCompact q'.left) ∧ (IsAffineHom q.left → IsAffineHom q'.left) := by
  intro S G' G B' B _ _ _ _ j p pB q
  have h : ∀ i, pB.lim.lift (Fan.mk G' fun i => p.pr i ≫ q) ≫ pB.pr i = p.pr i ≫ q := fun i =>
    pB.lim.fac (Fan.mk G' fun i => p.pr i ≫ q) ⟨i⟩
  exact ⟨_, h, isMonHom_of_comm p pB q _ h, prop_of_comm @Flat p pB q _ h,
    prop_of_comm @Surjective p pB q _ h, prop_of_comm @QuasiCompact p pB q _ h,
    prop_of_comm @IsAffineHom p pB q _ h⟩

end GlobalTheory.PowMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPowGrpBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isPowGrp_baseChange : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) (p : IsPowGrp G' G j), ∃ p' : IsPowGrp ((Over.pullback f).obj G') ((Over.pullback f).obj G) j, ∀ i, p'.pr i = (Over.pullback f).map (p.pr i) := by
  intro S S' f G' G _ _ j p
  refine ⟨⟨fun i => (Over.pullback f).map (p.pr i), fun i => ?_, ?_⟩, fun i => rfl⟩
  · haveI := p.hom i
    infer_instance
  · exact isLimitFanMkObjOfIsLimit (Over.pullback f) _ _ p.lim

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.QuasiCompactGeomConnectedPow
section
namespace GlobalTheory.PowGrp

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

theorem quasiCompact_geomConnected_pow : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) (p : IsPowGrp G' G j), (QuasiCompact G.hom → QuasiCompact G'.hom) ∧ (Smooth G.hom → GeometricallyConnected G.hom → GeometricallyConnected G'.hom) := by
  intro S G' G _ _ j p
  refine ⟨prop_of_isPowGrp @QuasiCompact p, fun hs hc => ?_⟩
  obtain ⟨e, he, hw⟩ := exists_iso_powObj p
  have := geomConnected_powObj G j
  have := smooth_isMultiplicative
  have : Smooth (powObj G j).hom := prop_powObj @Smooth G hs j
  have := geomConnected_of_isIso e
  rw [hw]
  exact GeometricallyConnected.comp _ _

end GlobalTheory.PowGrp
end

