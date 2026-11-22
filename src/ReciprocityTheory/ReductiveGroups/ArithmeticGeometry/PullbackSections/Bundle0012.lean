import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0042
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0002
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RegTiePfA
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

section Calc

variable {X Y Z : Scheme.{0}}

theorem sval_zCast {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {k₁ k₂ : ℤ} (h : k₁ = k₂)
    (F : LB.Sec (LPow A L k₁ T)) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    sval (zCast A h F) r z J = sval F r z J := by
  subst h
  rfl

def pull1 (L : LB X) (h : Y ⟶ X) (s : LB.Sec L) : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => h) (fun _ => 1)) :=
  thfPull1 L (F := 𝟙 X) h (Category.comp_id h) (thfPull L (𝟙 X) s)

theorem gs_pull1 (L : LB X) (h : Y ⟶ X) (s : LB.Sec L) (r : Z ⟶ Y) (z : Z) (j : Fin 1 → L.ι)
    (hz : r z ∈ LB.wchart L (fun _ : Fin 1 => h) j) :
    gs r z _ ((pull1 L h s).f j) = gs (r ≫ h) z (L.U (j 0)) (s.f (j 0)) := by
  simp only [pull1, thfPull1, thfPull]
  refine Eq.trans (gs_appLE h _ _ _ r z ?_ _) ?_
  · exact hz
  refine Eq.trans (gs_appLE (𝟙 X) _ _ _ (r ≫ h) z ?_ _) ?_
  · exact chart_le_pullback_open L h (Category.comp_id h) j hz
  rw [Category.comp_id]

def secOne (L : LB X) (s : LB.Sec L) : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)) :=
  pull1 L (𝟙 X) s

theorem plain_le (L : LB X) (i : L.ι) : L.U i ≤ (𝟙 X) ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) := by
  intro y hy
  exact Set.mem_iInter.mpr fun _ => hy

def plainOf (L : LB X) (σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1))) : LB.Sec L where
  f i := (Scheme.Hom.appLE (𝟙 X) _ _ (plain_le L i)).hom (σ.f (fun _ => i))
  compat i j := fn_ext fun y hy => by
    have m₁ : (𝟙 X ≫ 𝟙 X) y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) := plain_le L i hy.1
    have m₂ : (𝟙 X ≫ 𝟙 X) y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j) := plain_le L j hy.2
    have g : gm (𝟙 X ≫ 𝟙 X) y _ ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)).g (fun _ => i) (fun _ => j)) =
        gm (𝟙 X) y (L.U i ⊓ L.U j) (L.g i j) :=
      (gm_linComb L _ _ (𝟙 X ≫ 𝟙 X) y _ _ m₁ m₂).trans (by simp only [Fin.prod_univ_one, zpow_one, Category.comp_id])
    refine (gs_res _ y _ hy _).trans ((gs_appLE (𝟙 X) _ _ _ (𝟙 _) y hy.1 _).trans ((gs_compat σ (𝟙 X ≫ 𝟙 X) y m₁ m₂).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans (congrArg Units.val g.symm))
        ((gs_res _ y _ hy _).trans (gs_appLE (𝟙 X) _ _ _ (𝟙 _) y hy.2 _)))))))

theorem gs_plainOf (L : LB X) (σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1))) (y : X) (i : L.ι)
    (hy : y ∈ L.U i) :
    gs (𝟙 X) y (L.U i) ((plainOf L σ).f i) =
      gs (𝟙 X) y (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i)) (σ.f (fun _ => i)) := by
  simp only [plainOf]
  refine Eq.trans (gs_appLE (𝟙 X) _ _ _ (𝟙 X) y ?_ _) ?_
  · exact hy
  rw [Category.comp_id]

theorem gs_resTop (r : Z ⟶ X) (z : Z) {U : X.Opens} (hz : r z ∈ U) (a : Γ(X, ⊤)) :
    gs r z U (resG X (le_top : U ≤ ⊤) a) = gs r z ⊤ a := by
  exact gs_res r z le_top hz a

theorem secOne_gen {S : Type} [CommRing S] (G : Over (Sp S)) (L : LB G.left) (θ : LB.Sec L)
    (hθ : ∀ σ : LB.Sec L, ∃! a : S, ∀ i, σ.f i = resG G.left le_top ((G.hom).appTop.hom (toΓ S a)) * θ.f i) :
    ∀ σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ))),
      ∃! a : S, ∀ i, σ.f i = resG G.left le_top ((G.hom).appTop.hom (toΓ S a)) * (secOne L θ).f i := by
  show ∀ σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 1)),
    ∃! a : S, ∀ i, σ.f i = resG G.left le_top ((G.hom).appTop.hom (toΓ S a)) * (secOne L θ).f i
  have e3 : ∀ (i : L.ι) (y : G.left)
      (hy : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 1)).U (fun _ => i)),
      gs (𝟙 G.left) y _ ((secOne L θ).f (fun _ => i)) = gs (𝟙 G.left) y (L.U i) (θ.f i) := by
    intro i y hy
    refine (gs_pull1 L (𝟙 _) θ (𝟙 _) y (fun _ => i) hy).trans ?_
    rw [Category.comp_id]
  intro σ
  obtain ⟨a, ha, huniq⟩ := hθ (plainOf L σ)
  refine ⟨a, ?_, fun b hb => huniq b ?_⟩
  · rintro (j : Fin 1 → L.ι)
    obtain ⟨i, rfl⟩ : ∃ i : L.ι, j = fun _ => i := ⟨j 0, funext fun k => by rw [Subsingleton.elim k 0]⟩
    refine fn_ext fun y hy => ?_
    have hyi : y ∈ L.U i := LB.wchart_le L _ (fun _ : Fin 1 => i) 0 hy
    rw [gs_mul _ y _ hy, gs_resTop _ y hy, e3 i y hy]
    refine (gs_plainOf L σ y i hyi).symm.trans ?_
    rw [ha i, gs_mul _ y _ hyi, gs_resTop _ y hyi]
  · intro i
    refine fn_ext fun y hyi => ?_
    have hy : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 1)).U (fun _ => i) := plain_le L i hyi
    rw [gs_mul _ y _ hyi, gs_resTop _ y hyi]
    refine (gs_plainOf L σ y i hyi).trans ?_
    show gs (𝟙 G.left) y ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 1)).U (fun _ => i))
      (σ.f (fun _ => i)) = _
    rw [hb (fun _ => i), gs_mul _ y _ hy, gs_resTop _ y hy, e3 i y hy]

theorem gs_isoMaps {L M : LB X} {w : LB.Iso L M} {s : LB.Sec L} {s' : LB.Sec M} (h : IsoMaps w s s') (r : Z ⟶ X)
    (z : Z) (i : M.ι) (k : L.ι) (hi : r z ∈ M.U i) (hk : r z ∈ L.U k) :
    gs r z (M.U i) (s'.f i) = (gv w r z i k).val * gs r z (L.U k) (s.f k) := by
  unfold Formalism.L2.Pj.IsoMaps at h
  have hV : r z ∈ M.U i ⊓ L.U k := ⟨hi, hk⟩
  have h' := congrArg (gs r z (M.U i ⊓ L.U k)) (h i k)
  rw [gs_res r z _ hV, gs_mul _ z _ hV, gs_res r z _ hV] at h'
  rw [h']
  congr 1
  exact gs_unit _ z _ hV _

end Calc

theorem thetaTie : ThetaTieSt := by
  intro E _ _ _ H Dw l Xo c Tc io y I
  let _ := io.toAlgebra
  let A := Xo.univ.t.G
  let θK : LB.Sec (LPow I.t'.G I.t'.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp Tc.Fr)))) :=
    pull1 I.t'.PP.L (snd (𝟙_ (Over (Sp Tc.Fr))) I.t'.G).left I.σ
  have gθK : ∀ (Z : Scheme.{0}) (zp : Z ⟶ (𝟙_ (Over (Sp Tc.Fr)) ⊗ I.t'.G).left) (z : Z)
      (J' : (Z ⟶ I.t'.G.left) → I.t'.PP.L.ι), Good I.t'.PP.L z J' →
      sval θK zp z J' = gs (zp ≫ (snd (𝟙_ (Over (Sp Tc.Fr))) I.t'.G).left) z
        (I.t'.PP.L.U (J' (zp ≫ (snd (𝟙_ (Over (Sp Tc.Fr))) I.t'.G).left)))
        (I.σ.f (J' (zp ≫ (snd (𝟙_ (Over (Sp Tc.Fr))) I.t'.G).left))) :=
    fun Z zp z J' hJ' => gs_pull1 I.t'.PP.L _ I.σ zp z _ (hJ'.mem _ zp)
  refine ⟨secOne I.G.PP.L I.θ, secOne_gen I.G.G I.G.PP.L I.θ I.θgen, θK, ?_, ?_⟩
  · intro Z r zp zp' h1 h2 h3 z J J' hJ hJ'
    let a0 : Over.mk (I.t'.G.hom ≫ y.x) ⟶ Over.mk y.x := Over.homMk I.t'.G.hom rfl
    let b0 : Over.mk (I.t'.G.hom ≫ y.x) ⟶ A := Over.homMk I.m1.φ I.m1.cart.1.w
    let g0 : I.t'.G.left ⟶ Gx y.x := (lift a0 b0).left
    have g0f : g0 ≫ (fst (Over.mk y.x) A).left = I.t'.G.hom := congrArg (fun q => q.left) (lift_fst a0 b0)
    have g0s : g0 ≫ (snd (Over.mk y.x) A).left = I.m1.φ := congrArg (fun q => q.left) (lift_snd a0 b0)
    have hzp : zp = r ≫ g0 := by
      apply pullback.hom_ext
      · show zp ≫ (fst (Over.mk y.x) A).left = (r ≫ g0) ≫ (fst (Over.mk y.x) A).left
        rw [Category.assoc, g0f, h2]
      · show zp ≫ (snd (Over.mk y.x) A).left = (r ≫ g0) ≫ (snd (Over.mk y.x) A).left
        rw [Category.assoc, g0s, h1]
    subst hzp
    have hj : ∀ j : PUnit → Xo.univ.t.PP.L.ι,
        (Xo.univ.t.PP.L.pull I.m1.φ).U j ≤ g0 ⁻¹ᵁ (PPx y.x).U (fun _ => j PUnit.unit) := fun j y' hy' =>
      Set.mem_iInter.2 fun _ => (congrArg (fun q => q y' ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) g0s).mpr (mem_pull.1 hy')
    have mJ : r z ∈ (Xo.univ.t.PP.L.pull I.m1.φ).U (fun _ => J (r ≫ I.m1.φ)) := mem_pull.2 (hJ (r ≫ I.m1.φ))
    have mK : r z ∈ I.t'.PP.L.U (J' (r ≫ 𝟙 _)) := by simpa using hJ' (r ≫ 𝟙 _)
    have e1 : sval (zCast A Nat.cast_one.symm y.s) (r ≫ g0) z J =
        gs (r ≫ g0) z _ (y.s.f (fun _ => J (r ≫ I.m1.φ))) := by
      rw [sval_zCast]
      exact sval_of (L := Xo.univ.t.PP.L) (φ := fun _ : Fin 1 => (snd (Over.mk y.x) A).left) (ε := fun _ => 1) y.s
        (r ≫ g0) z J (fun _ => J (r ≫ I.m1.φ)) (fun _ => by rw [Category.assoc, g0s])
    have e2 : gs (r ≫ g0) z _ (y.s.f (fun _ => J (r ≫ I.m1.φ))) =
        gs r z _ (I.s1.f (fun _ => J (r ≫ I.m1.φ))) := by
      rw [I.gen1 g0 g0s g0f _ (hj _)]
      erw [gs_appLE g0 _ _ (hj _) r z mJ]
    erw [e1, e2, gs_isoMaps I.maps1 r z _ _ mJ mK, gθK Z zp' z J' hJ', h3, pow_one, Category.comp_id]
  · intro Z r zp h3 z J J' hJ hJ'
    have mJ : r z ∈ (I.G.PP.L.pull I.m2.φ).U (fun _ => J (r ≫ I.m2.φ)) := mem_pull.2 (hJ (r ≫ I.m2.φ))
    have mK : r z ∈ I.t'.PP.L.U (J' (r ≫ 𝟙 _)) := by simpa using hJ' (r ≫ 𝟙 _)
    have hpl : (I.G.PP.L.pull I.m2.φ).U (fun _ => J (r ≫ I.m2.φ)) ≤ I.m2.φ ⁻¹ᵁ I.G.PP.L.U (J (r ≫ I.m2.φ)) :=
      fun _ hy' => mem_pull.1 hy'
    have e1 : sval (secOne I.G.PP.L I.θ) (r ≫ I.m2.φ) z J =
        gs (r ≫ I.m2.φ) z (I.G.PP.L.U (J (r ≫ I.m2.φ))) (I.θ.f (J (r ≫ I.m2.φ))) := by
      erw [sval_of _ _ z J (fun _ => J (r ≫ I.m2.φ)) (fun _ => by rw [Category.comp_id])]
      rw [secOne]
      erw [gs_pull1 _ _ _ _ z _ (plain_le _ _ (hJ (r ≫ I.m2.φ)))]
      rw [Category.comp_id]
    have e2 : gs (r ≫ I.m2.φ) z (I.G.PP.L.U (J (r ≫ I.m2.φ))) (I.θ.f (J (r ≫ I.m2.φ))) =
        gs r z _ (I.θ2.f (fun _ => J (r ≫ I.m2.φ))) := by
      rw [I.pull _ hpl]
      erw [gs_appLE I.m2.φ _ _ hpl r z mJ]
    erw [e1, e2, gs_isoMaps I.maps2 r z _ _ mJ mK, gθK Z zp z J' hJ', h3, pow_one, Category.comp_id]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ShortPlace
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

def ShortPlaceASt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j),
    g ∈ T.toTop.sh j w → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.toTop.PtA j la),
      (∀ p ∈ ({2, D.host.q, D.host.d, D.host.g 0, D.host.g 1, (T.dδ j w.n).pd} : Finset ℕ),
        ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)) → 0 ≤ vAtV y g

def ShortSeriesRamifiedPlaceTwo : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j),
    g ∈ T.toTop.sh j w → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.toTop.PtA j la),
      (((2 : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
      (((-(((vLa la ((2 : ℕ) : T.Q.c.F) : ℤ) : ℝ) *
          ((D.R.e : ℝ) + 1 - (2 : ℝ)⁻¹ ^ D.R.e) * (DF w : ℝ) / 2)) : ℝ) : EReal) ≤ vAtV y g

def ShortPlaceBqdSt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j),
    g ∈ T.toTop.sh j w → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.toTop.PtA j la) (p : ℕ),
      p ∈ ({D.host.q, D.host.d} : Finset ℕ) → ((p : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
      (((-(((vLa la (p : T.Q.c.F) : ℤ) : ℝ) * (1 / 2) * (DF w : ℝ) / 2)) : ℝ) : EReal) ≤ vAtV y g

def ShortPlaceCSt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j),
    g ∈ T.toTop.sh j w → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.toTop.PtA j la) (i : Fin 2)
      (πE : 𝓞 D.host.E) (τ : D.host.E →+* ℂ),
      InPsi T.Q.H τ → πE * T.Q.H.bar πE = (D.host.g i : 𝓞 D.host.E) →
      T.Q.l.Mb ≤ Ideal.span {T.Q.H.bar πE} → ((D.host.g i : 𝓞 T.Q.c.F) ∈ la.asIdeal) → D.host.g i ≠ D.host.q →
      (((-(((vLa la (embK T.Q.c τ πE) : ℤ) : ℝ) * ((∑ t, ∑ k, w.aP t k : ℕ) : ℝ) +
          ((vLa la (embK T.Q.c τ (T.Q.H.bar πE)) : ℤ) : ℝ) * ((∑ t, ∑ k, w.aM t k : ℕ) : ℝ) +
          ((vLa la ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) : ℤ) : ℝ) * (D.R.f * D.R.r * w.n : ℕ))) : ℝ) : EReal) ≤
        vAtV y g

def ShortPlaceDSt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j),
    g ∈ T.toTop.sh j w → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.toTop.PtA j la),
      (((T.dδ j w.n).pd : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
      (((-(((vLa la ((T.dδ j w.n).pd : T.Q.c.F) : ℤ) : ℝ) *
          ((DF w : ℝ) + 2 * D.R.f * D.R.r * w.n))) : ℝ) : EReal) ≤ vAtV y g

def ThcAssemblySt : Prop :=
  ∀ (D : D7) (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) (s : 𝓞 T.Q.c.F) (w : WeightFamilies.Wt D j),
    s ≠ 0 →
    (∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.toTop.PtA j la) (g : T.toTop.R j), g ∈ T.toTop.sh j w →
      (((-(((vLa la ((s : T.Q.c.F) * ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) ^ (D.R.f * D.R.r * w.n)) : ℤ) : ℝ))) : ℝ)
        : EReal) ≤ vAtV y g) →
    (recPJ hF.p j hj).Thc s w ≤ (recB hF.p.toLawsCore).Mlat j w

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ShortValDesc
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

section Expr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def shortExpr (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) : S :=
  algebraMap c.F S (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ *
      ((N : c.F) ^ P.totalDegree)⁻¹) *
    ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F S (w q) *
      ∑ i, ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F q i b) (colOf m b)

def ShortData {n : ℕ} (Λ : GenLat E n) (N : ℕ) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) : Prop :=
  (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo y.x z ∧
    (∀ q b, tp q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b)) ∧
    ∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z i b) (tp q b) (F q i b)

end Expr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def ShortValDescSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y0 : FrPt Xo c S) (K : Type) [Field K] [Algebra c.F K]
      (φ : S →ₐ[c.F] K) (y : FrPt Xo c K), FrMap φ y0 y →
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M →
        ∀ (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ a →
        ∀ v0 v, ShortValAt Xo c nab w Λ β N P y0 v0 → ShortValAt Xo c nab w Λ β N P y v → φ v0 = v

def ShortValFinExtSt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j)
    (Λ : GenLat D.host.E w.n) (N : ℕ) (x0 : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
    g ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → Λ.Unimod → badN D ≠ 0 → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ j w.n).l₂.M →
    Λ.LevOK N (T.dδ j w.n).l₂.M → AdmX (l := T.Q.l) (decide (w.n = D.R.nV)) x0 → P ∈ harmL T.Q.c Λ (wtA w) →
    IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 P g →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io), yI.IsAlg →
    ∃ (T' : CDVR) (iT : Tc.Fr →+* T'.Fr) (e' : ℕ), 0 < e' ∧
      (∀ a : Tc.Fr, a ≠ 0 → vV T'.V (iT a) = (e' : ℤ) * vV Tc.V a) ∧
      ∃ (io₂ : (T.dδ j w.n).c₂.F →+* T'.Fr), (∀ (a : (T.dδ j w.n).c₂.F) (b : T.Q.c.F), (a : ℂ) = b → io₂ a = iT (io b)) ∧
      ∃ (yI₂ : IntFr (T.dδ j w.n).Xo₂ (T.dδ j w.n).c₂ T' io₂), yI₂.IsAlg ∧
        letI := io.toAlgebra
        letI := (iT.comp io).toAlgebra
        letI := io₂.toAlgebra
        ∃ (yI' : IntFr (T.Q.Xo j) T.Q.c T' (iT.comp io)) (φ : Tc.Fr →ₐ[T.Q.c.F] T'.Fr), φ.toRingHom = iT ∧
          FrMap φ yI.1 yI'.1 ∧ FrOver (T.dδ j w.n) yI₂.1 yI'.1 ∧
        ∃ (z : Fin (Λ.zCard N ((T.Q.Dw j).p + (T.Q.Dw j).q)) → Fin w.n →
              (ptO (T.dδ j w.n).Xo₂ yI₂.1.x ⟶ (T.dδ j w.n).Xo₂.univ.t.G))
          (tp : (Fin w.n → LevQ (T.Q.Dw j) (T.dδ j w.n).l₂) → Fin w.n →
              (ptO (T.dδ j w.n).Xo₂ yI₂.1.x ⟶ (T.dδ j w.n).Xo₂.univ.t.G))
          (F : (Fin w.n → LevQ (T.Q.Dw j) (T.dδ j w.n).l₂) → Fin (Λ.zCard N ((T.Q.Dw j).p + (T.Q.Dw j).q)) → Fin w.n →
              LB.Sec (LPow (T.dδ j w.n).Xo₂.univ.t.G (T.dδ j w.n).Xo₂.univ.t.PP.L ((N : ℤ) ^ 2)
                (ptO (T.dδ j w.n).Xo₂ yI₂.1.x))),
          ShortData Λ N yI₂.1 z tp F ∧
          iT (evI yI g) = evI yI₂ (T.dδ j w.n).cδ *
            shortExpr (T.dδ j w.n).nab₂ ((T.dδ j w.n).w x0) Λ ((T.dδ j w.n).eF (betaH (Dw := T.Q.Dw j) T.Q.c Λ)) N
              (MvPolynomial.map ((T.dδ j w.n).eF : T.Q.c.F →+* (T.dδ j w.n).c₂.F) P) yI₂.1 F

def FinExtRootShortSt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (n : ℕ) (Λ : GenLat D.host.E n) (N : ℕ),
    Λ.Unimod → badN D ≠ 0 → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ j n).l₂.M → Λ.LevOK N (T.dδ j n).l₂.M →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io), yI.IsAlg →
    ∃ (T' : CDVR) (iT : Tc.Fr →+* T'.Fr) (e' : ℕ), 0 < e' ∧
      (∀ a : Tc.Fr, a ≠ 0 → vV T'.V (iT a) = (e' : ℤ) * vV Tc.V a) ∧
      ∃ (io₂ : (T.dδ j n).c₂.F →+* T'.Fr), (∀ (a : (T.dδ j n).c₂.F) (b : T.Q.c.F), (a : ℂ) = b → io₂ a = iT (io b)) ∧
      ∃ (yI₂ : IntFr (T.dδ j n).Xo₂ (T.dδ j n).c₂ T' io₂), yI₂.IsAlg ∧
        letI := io.toAlgebra
        letI := (iT.comp io).toAlgebra
        letI := io₂.toAlgebra
        ∃ (yI' : IntFr (T.Q.Xo j) T.Q.c T' (iT.comp io)) (φ : Tc.Fr →ₐ[T.Q.c.F] T'.Fr), φ.toRingHom = iT ∧
          FrMap φ yI.1 yI'.1 ∧ FrOver (T.dδ j n) yI₂.1 yI'.1 ∧
          ∃ (z : Fin (Λ.zCard N ((T.Q.Dw j).p + (T.Q.Dw j).q)) → Fin n →
                (ptO (T.dδ j n).Xo₂ yI₂.1.x ⟶ (T.dδ j n).Xo₂.univ.t.G))
            (tp : (Fin n → LevQ (T.Q.Dw j) (T.dδ j n).l₂) → Fin n →
                (ptO (T.dδ j n).Xo₂ yI₂.1.x ⟶ (T.dδ j n).Xo₂.univ.t.G))
            (F : (Fin n → LevQ (T.Q.Dw j) (T.dδ j n).l₂) → Fin (Λ.zCard N ((T.Q.Dw j).p + (T.Q.Dw j).q)) → Fin n →
                LB.Sec (LPow (T.dδ j n).Xo₂.univ.t.G (T.dδ j n).Xo₂.univ.t.PP.L ((N : ℤ) ^ 2)
                  (ptO (T.dδ j n).Xo₂ yI₂.1.x))),
            ShortData Λ N yI₂.1 z tp F

def FrOverBCSt {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) : Prop :=
  ∀ (k k' : Type) [Field k] [Field k'] [Algebra c.F k] [Algebra d.c₂.F k] [Algebra c.F k'] [Algebra d.c₂.F k']
    (κ₁ : k →ₐ[c.F] k') (κ₂ : k →ₐ[d.c₂.F] k'), (κ₁ : k →+* k') = κ₂ →
    ∀ (y₂ : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k) (y₂' : FrPt d.Xo₂ d.c₂ k') (y' : FrPt Xo c k'),
      FrOver d y₂ y → FrMap κ₁ y y' → FrMap κ₂ y₂ y₂' → FrOver d y₂' y'

def HarmLMapSt {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) : Prop :=
  ∀ (Λ : GenLat E n) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ a →
    MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈ harmL d.c₂ Λ a

def ShortExprIndepSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab →
    ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ}
      (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M →
      ∀ (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ a →
      ∀ (z z' : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
        (tp tp' : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
        (F F' : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
          LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))),
        ShortData Λ N y z tp F → ShortData Λ N y z' tp' F' →
          shortExpr nab w Λ β N P y F = shortExpr nab w Λ β N P y F'

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanInst
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

theorem indepToC_comp {K : Type*} [Field K] {σ : K →+* ℂ} {C C' : Type*} [AddCommGroup C] [Module K C]
    [AddCommGroup C'] [Module K C'] {W : Type*} [AddCommGroup W] [Module ℂ W] (J : C →ₛₗ[σ] W)
    (hJ : IndepToC J) (ι : C' →ₗ[K] C) (hι : Function.Injective ι) : IndepToC (J.comp ι) := by
  intro n b hb
  exact hJ n (fun i => ι (b i)) (hb.map' ι (LinearMap.ker_eq_bot.mpr hι))

variable {D : D7} {T : Top D}

def jRec (j : ℕ) (ka : WeightFamilies.Wt D j) :
    cutR T.C j ka →ₛₗ[T.σ₀] FDSec (T.U j T.σ₀).X :=
  (rdC (T.U j) T.σ₀ (wtA ka) ka.n).comp (Submodule.inclusion (cutR_le T.C j ka))

set_option synthInstance.maxHeartbeats 400000 in
theorem spanAt_rec (h : LawsP T) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka : WeightFamilies.Wt D j)
    (hJ : JInjRd T j (wtA ka) ka.n) (A : Set (FDSec (T.U j T.σ₀).X))
    (hG : holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA ka) ka.n) ≤ Submodule.span ℂ A)
    (hA : A ⊆ Submodule.span ℂ (jRec (T := T) j ka ''
      (((recX h) j h1 h2).shortTh ka : Set ((recB h.toLawsCore).Cusp j ka)))) :
    SpanAt ((recX h) j h1 h2) ka :=
  spanAt_of_chain ((recX h) j h1 h2) ka (jRec (T := T) j ka)
    (indepToC_comp _ hJ _ (Submodule.inclusion_injective _))
    (holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA ka) ka.n)) A
    (fun _ => rdC_mem_holSub0 T.good_σ₀ (wtA ka) ka.n _) hG hA

def GminFDSt : Prop :=
  ∀ (D : D7) (T : Full D) (_h : LawsFull T) (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j), badN D ≠ 0 →
    LastPos (T.Q.Dw j) (wtA ka) → 8 * D.R.f * D.R.r + 4 ≤ ka.n → Even ka.n →
    holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA ka) ka.n) ≤
      Submodule.span ℂ (rdU (T.U j T.σ₀) '' T.sh j ka)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.WtRedPf
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def WtRed : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S]
    (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y

theorem wtRed_of (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    (hA : AllTest Xo c) (hW : WtField Xo c) (hB : FrBCFieldSt Xo c) : WtRed Xo c := by
  intro a n f hf S _ _ _ t y y' hb
  have hN := evNat_of Xo c hWD hA
  rw [← sub_eq_zero]
  set d := evR Xo c f y' - wchar (ex Dw a n) t * evR Xo c f y with hd
  have hP : ∀ P : Ideal S, P.IsPrime → d ∈ P := by
    intro P hPp
    have := hPp
    let ρ : S →+* FractionRing (S ⧸ P) := (algebraMap (S ⧸ P) (FractionRing (S ⧸ P))).comp (Ideal.Quotient.mk P)
    let _ : Algebra c.F (FractionRing (S ⧸ P)) := (ρ.comp (algebraMap c.F S)).toAlgebra
    let φ : S →ₐ[c.F] FractionRing (S ⧸ P) := { ρ with commutes' := fun _ => rfl }
    obtain ⟨z, hz⟩ := hB S y (FractionRing (S ⧸ P)) φ
    obtain ⟨z', hz'⟩ := hB S y' (FractionRing (S ⧸ P)) φ
    have hbz := frBorBC (Xo := Xo) (c := c) S (FractionRing (S ⧸ P)) φ t y y' z z' hb hz hz'
    have e1 := hN f hf.1 S (FractionRing (S ⧸ P)) φ y z hz
    have e2 := hN f hf.1 S (FractionRing (S ⧸ P)) φ y' z' hz'
    have e3 := hW a n f hf (FractionRing (S ⧸ P)) _ z z' (hA _ z) (hA _ z') hbz
    have hw : φ (wchar (ex Dw a n) t) = wchar (ex Dw a n) (fun i => Units.map (φ : S →* FractionRing (S ⧸ P)) (t i)) := by
      simp only [wchar, map_prod, map_pow, Units.coe_map, MonoidHom.coe_coe]
    have h0 : φ d = 0 := by
      rw [hd, map_sub, map_mul, ← e1, ← e2, e3, hw, sub_self]
    have h1 : algebraMap (S ⧸ P) (FractionRing (S ⧸ P)) (Ideal.Quotient.mk P d) = 0 := h0
    have h2 : Ideal.Quotient.mk P d = 0 :=
      (IsFractionRing.injective (S ⧸ P) (FractionRing (S ⧸ P))) (by rw [h1, map_zero])
    exact Ideal.Quotient.eq_zero_iff_mem.mp h2
  have hnil : d ∈ nilradical S := by
    rw [nilradical_eq_sInf]
    exact Submodule.mem_sInf.mpr fun Q hQ => hP Q hQ
  exact IsReduced.eq_zero d (mem_nilradical.mp hnil)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

