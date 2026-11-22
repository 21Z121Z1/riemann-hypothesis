import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0040
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.AdelicContinuousOfUniform
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section BC

theorem bcSp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def bcPm {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) : Gx (spMap ψ ≫ x) ⟶ Gx x :=
  pullback.lift (pullback.fst (Over.mk (spMap ψ ≫ x)).hom Xo.univ.t.G.hom ≫ spMap ψ)
    (pullback.snd (Over.mk (spMap ψ ≫ x)).hom Xo.univ.t.G.hom)
    (by rw [Category.assoc]; exact pullback.condition)

theorem bcPm_snd {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    bcPm ψ x ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := by
  rw [Over.snd_left, Over.snd_left]
  exact pullback.lift_snd _ _ _

theorem bcPm_fst {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    bcPm ψ x ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left ≫ spMap ψ := by
  rw [Over.fst_left, Over.fst_left]
  exact pullback.lift_fst _ _ _

theorem appLE_comp_pullback {A B C : Scheme.{0}} (P : A ⟶ B) (q : B ⟶ C) (q' : A ⟶ C) (hq : P ≫ q = q') (W : C.Opens)
    (V1 : B.Opens) (V2 : A.Opens) (h1 : V1 ≤ q ⁻¹ᵁ W) (h2 : V2 ≤ P ⁻¹ᵁ V1) (h3 : V2 ≤ q' ⁻¹ᵁ W) (u : Γ(C, W)) :
    (P.appLE V1 V2 h2).hom ((q.appLE W V1 h1).hom u) = (q'.appLE W V2 h3).hom u := by
  subst hq
  rw [← CommRingCat.comp_apply]
  first
    | rw [Scheme.Hom.appLE_comp_appLE]
    | rw [Scheme.appLE_comp_appLE]

theorem ppxG {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i j : Fin 1 → Xo.univ.t.PP.L.ι) :
    (((PPx x).g i j : Γ(Gx x, (PPx x).U i ⊓ (PPx x).U j))) =
      ((snd (Over.mk x) Xo.univ.t.G).left.appLE (Xo.univ.t.PP.L.U (i 0) ⊓ Xo.univ.t.PP.L.U (j 0))
        ((PPx x).U i ⊓ (PPx x).U j)
        (fun p hp => ⟨Set.mem_iInter.1 hp.1 0, Set.mem_iInter.1 hp.2 0⟩)).hom
        (Xo.univ.t.PP.L.g (i 0) (j 0) : Γ(Xo.univ.t.G.left, _)) := by
  simp only [PPx, ReciprocityTheory.ChartRestriction.G.Out.LPow, LB.LinComb, Fin.prod_univ_one, zpow_one]
  rfl

def bcS {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) (s : LB.Sec (PPx x)) :
    LB.Sec (PPx (spMap ψ ≫ x)) where
  f i := ((bcPm ψ x).appLE _ _ (ppx_le_cov (bcPm ψ x) (bcPm_snd ψ x) i)).hom (s.f i)
  compat i j := by
    have hi := ppx_le_cov (bcPm ψ x) (bcPm_snd ψ x) i
    have hj := ppx_le_cov (bcPm ψ x) (bcPm_snd ψ x) j
    have hij : (PPx (spMap ψ ≫ x)).U i ⊓ (PPx (spMap ψ ≫ x)).U j ≤
        bcPm ψ x ⁻¹ᵁ ((PPx x).U i ⊓ (PPx x).U j) := fun p hp => ⟨hi hp.1, hj hp.2⟩
    have e := congrArg ((bcPm ψ x).appLE _ _ hij).hom (s.compat i j)
    rw [map_mul] at e
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
      Scheme.Hom.map_appLE] at e
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map]
    rw [e]
    congr 1
    refine (congrArg (fun w => ((bcPm ψ x).appLE _ _ hij).hom w) (ppxG x i j)).trans
      (Eq.trans ?_ (ppxG (spMap ψ ≫ x) i j).symm)
    exact appLE_comp_pullback _ _ _ (bcPm_snd ψ x) _ _ _ _ _ _ _

theorem bcTan {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsTanAt x v) :
    IsTanAt (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ v) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1, ← Category.assoc, ← Category.assoc, bcSp, bcSp]
    congr 2
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · rw [← Category.assoc, bcSp]
    have e : (TrivSqZeroExt.fstHom T T T).toRingHom.comp (dualMap ψ) =
        ψ.comp (TrivSqZeroExt.fstHom S S S).toRingHom :=
      RingHom.ext fun a => by simp [dualMap]
    rw [e, ← bcSp, Category.assoc, h2]
    first
      | exact congrArg CommaMorphism.left (comp_one (Over.homMk (U := Over.mk (spMap ψ ≫ x)) (V := Over.mk x) (spMap ψ) rfl) : _)
      | exact congrArg CommaMorphism.left (Hom.comp_one (Over.homMk (U := Over.mk (spMap ψ ≫ x)) (V := Over.mk x) (spMap ψ) rfl) : _)
      | exact congrArg CommaMorphism.left (MonObj.comp_one (Over.homMk (U := Over.mk (spMap ψ ≫ x)) (V := Over.mk x) (spMap ψ) rfl) : _)
      | exact congrArg CommaMorphism.left (Mon_Class.comp_one (Over.homMk (U := Over.mk (spMap ψ ≫ x)) (V := Over.mk x) (spMap ψ) rfl) : _)
      | simp [Hom.one_def]

theorem bcEig {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (τ : E →+* ℂ) {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsEigAt c τ v) :
    IsEigAt c τ (spMap (dualMap ψ.toRingHom) ≫ v) := by
  intro a
  rw [Category.assoc, h a, ← Category.assoc, ← Category.assoc, bcSp, bcSp]
  congr 2
  refine RingHom.ext fun d => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl, smul_eq_mul, map_mul, AlgHom.commutes]

theorem bcOver {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    {x : Sp S ⟶ Xo.X} (h : x ≫ Xo.s = sOf c S) : (spMap ψ.toRingHom ≫ x) ≫ Xo.s = sOf c T := by
  rw [Category.assoc, h]
  unfold sOf
  rw [bcSp]
  congr 1
  ext a
  simp

variable (Xo c) in

def BasBC (σ : c.F →+* ℂ) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ) (τ : E →+* ℂ)
    (w : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left),
    IsTanAt (spMap ψ.toRingHom ≫ y.x) w → IsEigAt c τ w →
      ∃! a : Fin (Dw.mult τ) → CAt σ,
        IsCombAt (spMap ψ.toRingHom ≫ y.x) (fun i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i) a w

variable (Xo c) in

def GenBC (σ : c.F →+* ℂ) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ) (s' : LB.Sec (PPx (spMap ψ.toRingHom ≫ y.x))),
    ∃! a : CAt σ, ∀ i, s'.f i = scal (spMap ψ.toRingHom ≫ y.x) a i * (bcS ψ.toRingHom y.x y.s).f i

def bcPt {σ : c.F →+* ℂ} (hB : BasBC Xo c σ) (hG : GenBC Xo c σ) (p : TRing c.F) (y : FrPt Xo c p.R)
    (ψ : p.R →ₐ[c.F] CAt σ) : FrPt Xo c (CAt σ) where
  x := spMap ψ.toRingHom ≫ y.x
  x_over := bcOver ψ y.x_over
  u τ i := spMap (dualMap ψ.toRingHom) ≫ y.u τ i
  tan τ i := bcTan ψ.toRingHom (y.tan τ i)
  eig τ i := bcEig ψ τ (y.eig τ i)
  basis τ w hw he := hB p y ψ τ w hw he
  s := bcS ψ.toRingHom y.x y.s
  gen s' := hG p y ψ s'

end BC

section Loc

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

def LocSplit (V : HSp D) (Kf : Subgroup (GA D V)) : Prop :=
  ∀ g₀ : GA D V, ∃ N ∈ 𝓝 g₀, ∃ a : GA D V → GA D V, ContinuousOn a N ∧ a g₀ = 1 ∧
    ∀ g ∈ N, a g ∈ GinfC V ∧ ∃ k ∈ Kf, g = g₀ * a g * k

def ArchCont (V : HSp D) {X : Comp → Data E r}
    (th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) : Prop :=
  ∀ k τ, Continuous (archM V (th k τ))

def locFr (V : HSp D) {X : Comp → Data E r} (dict : GA D V → Σ k, Frame (X k).Ψ r)
    (th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hr : V.rank = r)
    (x0 : ∀ k, Frame (X k).Ψ r) (a : GA D V → GA D V) (g₀ g : GA D V) : Frame (X (dict g₀).1).Ψ r :=
  rmul (dict g₀).2 (archMat V th hr x0 (a g) (dict g₀).1)

end Loc

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CoreJExistsAt
section
noncomputable section

namespace Formalism.L2.Pj.V3

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open MeasureTheory
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rows

variable {D : D7}

structure PkgRows (hN : N1c) (Q : Par D) (hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) (hI : InfPlaceEx D) (j : ℕ)
    (hj : InR D j) (hIo : IotaEx Q j hj) (σ : Q.c.F →+* ℂ) (hσ : GoodEmb Q.c σ) (χ : (AE D)ˣ →* Circle) : Prop where
  modelEx : ModelEx hN Q hpq j hj σ hσ (relabType_of Q.c σ hσ (Q.Dw j))
  frameEx : FrameEx modelEx
  cover : CoverU (unfJ frameEx)
  fibre : FibreU (unfJ frameEx)

  holFD : HolomorphicSectionsFinDim (unfJ frameEx)
  genus : GenusEx (unfJ frameEx) (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) (iotaJ hIo) (letE (Q.Dw j))
    (famJ hN Q hpq j σ hσ (relabType_of Q.c σ hσ (Q.Dw j))) id (modelsJ modelEx).φ (thJ hI (modelsJ modelEx).X) (x0J modelEx)

  dictU : DictIsUnif (D.sp.W j) (dictOf genus) (kfW (D.sp.W j) (D.host.g 0 * D.host.g 1))
    (thJ hI (modelsJ modelEx).X) (D.sp.W_rank j hj.1 hj.2)

  unitFr : ∀ g τ i, ‖dmin ((unfJ frameEx).X (dictOf genus g).1).Gm (dictOf genus g).2 τ i‖ = 1
  adelCont : AdelCont (D.sp.W j) (dictOf genus) (muOf (D.sp.W j) χ)

  latZ : σ = Q.c.F.val.toRingHom → FJ.LatZ (unfJ frameEx).X (WeightFamilies.rho D j)
  cuNe : σ = Q.c.F.val.toRingHom → FJ.CuNeF (unfJ frameEx).X (WeightFamilies.rho D j)
  expo : σ = Q.c.F.val.toRingHom → FJ.ExpoMatch (unfJ frameEx).X 1 (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1)

end Rows

section Collected

variable {D : D7}

def pkgJ {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q} {hI : InfPlaceEx D} {j : ℕ}
    {hj : InR D j} {hIo : IotaEx Q j hj} {σ : Q.c.F →+* ℂ} {hσ : GoodEmb Q.c σ} {χ : (AE D)ˣ →* Circle}
    (P : PkgRows hN Q hpq hI j hj hIo σ hσ χ) : PkgT Q j σ :=
  ⟨unfJ P.frameEx, dictOf P.genus, muOf (D.sp.W j) χ⟩

structure PkgOK2 (Q : Par D) (j : ℕ) (σ : Q.c.F →+* ℂ) (p : PkgT Q j σ) : Prop where
  unf : IsUnf p.1
  unTest : ∀ k x, FromTest (K := Q.c.F) (fun S _ _ => FrPt (Q.Xo j) Q.c S) (fun φ y z => FrMap φ y z) (p.1.un k x)
  chi1 : ∀ k la γ, (p.1.X k).χ la γ = 1
  dictU : ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
    DictIsUnif (D.sp.W j) p.2.1 (kfW (D.sp.W j) (D.host.g 0 * D.host.g 1)) th hr
  xiAbs : ∀ k (τ : D.host.E →+* ℂ), ‖τ (p.1.X k).ξ0‖ = xiR D
  muUnit : MuUnit (D.sp.W j) p.2.1 p.2.2
  muCont : Continuous p.2.2
  holFD : HolomorphicSectionsFinDim p.1
  adelAut : AdelAut (D.sp.W j) p.2.1 p.2.2
  latZ : σ = Q.c.F.val.toRingHom → FJ.LatZ p.1.X (WeightFamilies.rho D j)
  cuNe : σ = Q.c.F.val.toRingHom → FJ.CuNeF p.1.X (WeightFamilies.rho D j)
  expo : σ = Q.c.F.val.toRingHom → FJ.ExpoMatch p.1.X 1 (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1)

theorem pkgJ_ok {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q} {hI : InfPlaceEx D} {j : ℕ}
    {hj : InR D j} {hIo : IotaEx Q j hj} {σ : Q.c.F →+* ℂ} {hσ : GoodEmb Q.c σ} {χ : (AE D)ˣ →* Circle}
    (P : PkgRows hN Q hpq hI j hj hIo σ hσ χ) (hA : AllTest (Q.Xo j) Q.c) (hX : XiConst D)
    (hWt : WtC (Q.Xo j) Q.c σ) (hmu : MuUnit (D.sp.W j) (dictOf P.genus) (muOf (D.sp.W j) χ) ∧ Continuous (muOf (D.sp.W j) χ)) :
    PkgOK2 Q j σ (pkgJ P) where
  unf := isUnf_unfOf _ _ _ _ P.frameEx.choose_spec.1 P.modelEx.choose_spec.1 P.cover P.fibre
    (readSecU_of _ _ _ _ P.frameEx.choose_spec P.modelEx.choose_spec.1 hWt)
  unTest := unTest_of hA _
  chi1 := P.modelEx.choose_spec.1.chi
  dictU := ⟨_, _, fun _ τ => ((hI : ∀ τ : D.host.E →+* ℂ, ∃ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ,
    Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) τ.1).choose_spec, P.dictU⟩
  xiAbs := fun k τ =>
    (congrArg (fun z => ‖τ z‖) (P.modelEx.choose_spec.2 k).2).trans (by rw [map_neg, norm_neg]; exact hX τ)
  muUnit := hmu.1
  muCont := hmu.2
  holFD := P.holFD
  adelAut := adelAut_of P.modelEx.choose_spec.1.chi P.dictU hmu.1 P.adelCont
  latZ := P.latZ
  cuNe := P.cuNe
  expo := P.expo

end Collected

section J

variable {D : D7}

structure PkgOKJ (Q : Par D) (j : ℕ) (σ : Q.c.F →+* ℂ) (χ : (AE D)ˣ →* Circle)
    (ι₀ : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) (p : PkgT Q j σ)
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) : Prop where
  ok : PkgOK2 Q j σ p
  muVal : MuVal (D.sp.W j) χ p.2.2
  modelW : ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr (p.1.X k)
  familyUniformisationBasePointOrthogonal : ∀ k, IsOrthogonalFrame (p.1.X k) x₀
  adPin : ∃ (hr : (D.sp.W j).rank = D.R.r) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((Q.Dw j).mult τ))
    (F : FamilyUnif (Q.Xo j) (σ.comp (IntermediateField.inclusion Q.c.le).toRingHom) (fun i => relab Q.c σ (e i).1))
    (ik : p.1.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (p.1.X k).Λ)
    (th : ∀ k, (p.1.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    let ι := LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀
    LatEmb (D.sp.W j) ι ∧ LatIsom (D.sp.W j) (Q.Dw j).EF ι ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
      DictLat p.1 (D.sp.W j) hr p.2.1 ι e F ik φ th x₀

theorem pkgJ_okJ {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q} {hI : InfPlaceEx D} {j : ℕ}
    {hj : InR D j} {hIo : IotaEx Q j hj} {σ : Q.c.F →+* ℂ} {hσ : GoodEmb Q.c σ} {χ : (AE D)ˣ →* Circle}
    (P : PkgRows hN Q hpq hI j hj hIo σ hσ χ) (hA : AllTest (Q.Xo j) Q.c) (hX : XiConst D)
    (hWt : WtC (Q.Xo j) Q.c σ) (R : MuRows (D.sp.W j) χ) :
    PkgOKJ Q j σ χ hIo.choose (pkgJ P) (x0J P.modelEx) where
  ok := pkgJ_ok P hA hX hWt (muOK_of R P.unitFr)
  muVal := muVal_muOf R.detRoot R.chiWD
  modelW := ⟨_, P.modelEx.choose_spec.2⟩
  familyUniformisationBasePointOrthogonal := fun k => by
    have hB := P.modelEx.choose_spec.1
    have hW := P.modelEx.choose_spec.2
    refine base_frame_orthonormal_of_eq (Finset.ext fun τ => ((hB.type _).2 τ).trans ((hB.type k).2 τ).symm)
      ((hW _).1.trans (hW k).1.symm) ((hB.type _).1.trans (hB.type k).1.symm)
  adPin := ⟨D.sp.W_rank j hj.1 hj.2, _, letE (Q.Dw j), famJ hN Q hpq j σ hσ (relabType_of Q.c σ hσ (Q.Dw j)), id, (modelsJ P.modelEx).φ,
    thJ hI (modelsJ P.modelEx).X, hIo.choose_spec.1, hIo.choose_spec.2,
    fun _ τ => ((hI : ∀ τ : D.host.E →+* ℂ, ∃ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ,
      Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) τ.1).choose_spec,
    dictLat_unfOf _ _ _ _ P.frameEx.choose_spec.1 P.modelEx.choose_spec.1 P.genus⟩

structure LawsJRest (hN : N1c) (Q : Par D) (hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q)
    (chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle) : Prop extends BaseRows Q where
  pkg : ∀ j (hj : InR D j) σ (hσ : GoodEmb Q.c σ), PkgRows hN Q hpq (infPlaceEx_holds D) j hj (iota j hj) σ hσ (chiW j σ)
  muRows : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → MuRows (D.sp.W j) (chiW j σ)

  muConj : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → MuConj Q.c.F.val.toRingHom σ (chiW j Q.c.F.val.toRingHom) (chiW j σ)

  intAll : ∀ j, InR D j → IntAll (Q.Xo j) Q.c

  kfHalf : ∀ j, InR D j → KfHalf (D.sp.W j) (kfW (D.sp.W j) (D.host.g 0 * D.host.g 1)) Q.l.M
    (Q.l.Mb.map (Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E))

variable {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q}
  {chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle}

open Classical in

def iotaOf (L : LawsJRest hN Q hpq chiW) (j : ℕ) : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E) :=
  if hj : InR D j then (L.iota j hj).choose else 0

theorem pkgExJ (L : LawsJRest hN Q hpq chiW) (j : ℕ) (σ : Q.c.F →+* ℂ) :
    ∃ q : PkgT Q j σ × ((D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ),
      ∀ hj : InR D j, GoodEmb Q.c σ → PkgOKJ Q j σ (chiW j σ) (L.iota j hj).choose q.1 q.2 := by
  by_cases hj : InR D j
  · by_cases hσ : GoodEmb Q.c σ
    · exact ⟨(pkgJ (L.pkg j hj σ hσ), x0J (L.pkg j hj σ hσ).modelEx), fun _ _ =>
        pkgJ_okJ (L.pkg j hj σ hσ) (L.allTest j hj) (xiConst_holds D) (L.wtC j hj σ hσ) (L.muRows j hj σ hσ)⟩
    · exact ⟨(Classical.choice (L.dataAll j σ), fun _ => 1), fun _ h => absurd h hσ⟩
  · exact ⟨(Classical.choice (L.dataAll j σ), fun _ => 1), fun h => absurd h hj⟩

def pkgOfJ (L : LawsJRest hN Q hpq chiW) (j : ℕ) (σ : Q.c.F →+* ℂ) :
    PkgT Q j σ × ((D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) :=
  (pkgExJ L j σ).choose

def coreJOf (L : LawsJRest hN Q hpq chiW) : CoreJ D where
  toCore := coreOfP Q (fun j σ => (pkgOfJ L j σ).1) L.half.choose
  cE _ _ _ := 1
  chiW := chiW
  x₀ j σ := (pkgOfJ L j σ).2
  iota := iotaOf L

end J

section At

variable (D : D7) (hF : OFull D) (hz : OZeta D) (hN : N1ab) (l : Level (hostOfRecord D))
  (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1)

end At

end Formalism.L2.Pj.V3
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CurveComp
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def evCAlg (hG : GenFrEx Xo c) (hT : GenFromTest Xo c hG) (Z : Comp Xo c) : Rul Xo c →ₐ[c.F] Om Z where
  toFun := evC hG Z
  map_one' := evalAt_one _ _ (genFr hG Z) (hT Z)
  map_mul' f g := evalAt_mul _ _ f g (genFr hG Z)
  map_zero' := evalAt_zero _ _ (genFr hG Z)
  map_add' f g := evalAt_add _ _ f g (genFr hG Z)
  commutes' a := by
    show evC hG Z (algebraMap c.F (Rul Xo c) a) = algebraMap c.F (Om Z) a
    rw [Algebra.algebraMap_eq_smul_one]
    show evalAt _ _ (a • (1 : Rul Xo c)) (genFr hG Z) = _
    rw [evalAt_smul, evalAt_one _ _ _ (hT Z), mul_one]

lemma evCAlg_apply (hG : GenFrEx Xo c) (hT : GenFromTest Xo c hG) (Z : Comp Xo c) (f : Rul Xo c) :
    evCAlg hG hT Z f = evC hG Z f := rfl

end Gen

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) (Ω : Type) [CommRing Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)

abbrev RZ : Type := Kp X la N ⊗[X.Kl la] (X.Kl la ⊗[B.KO] Ω)

def rzMap : Rp X la N →ₐ[Kp X la N] RZ X la N Ω :=
  Algebra.TensorProduct.map (AlgHom.id _ _) (Algebra.TensorProduct.map (AlgHom.id _ _) gF)

lemma rzMap_emb (F : X.Forms) :
    rzMap X la N Ω gF (emb X la N F) = (1 : Kp X la N) ⊗ₜ ((1 : X.Kl la) ⊗ₜ gF F) := by
  show Algebra.TensorProduct.map (AlgHom.id _ _) (Algebra.TensorProduct.map (AlgHom.id _ _) gF)
      ((1 : Kp X la N) ⊗ₜ[X.Kl la] ((1 : X.Kl la) ⊗ₜ[B.KO] F)) = _
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
  rfl

variable {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

abbrev RZs : Type := Localization.Away (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))

def lwZ : Lw X la w →+* RZs X la N Ω gF w :=
  Localization.awayMap (rzMap X la N Ω gF).toRingHom (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)

lemma lwZ_alg (r : Rp X la N) :
    lwZ X la N Ω gF w (algebraMap (Rp X la N) (Lw X la w) r) =
      algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF r) := by
  show (Localization.awayMap (rzMap X la N Ω gF).toRingHom (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))
      (algebraMap (Rp X la N) (Localization.Away (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)) r) = _
  exact IsLocalization.map_eq _ _

def phiZ : ↥(Frac0 X la w) →ₐ[Kp X la N] RZs X la N Ω gF w where
  toRingHom := (lwZ X la N Ω gF w).comp (Frac0 X la w).val.toRingHom
  commutes' k := by
    show lwZ X la N Ω gF w (algebraMap (Kp X la N) (Lw X la w) k) = _
    rw [IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w), lwZ_alg, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]

lemma phiZ_apply (x : ↥(Frac0 X la w)) : phiZ X la N Ω gF w x = lwZ X la N Ω gF w (x : Lw X la w) := rfl

end Rec

section Inst

variable {D : D7} {T : Top D} (j : ℕ)
  (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) (Z : Comp (T.Q.Xo j) T.Q.c)

def formsEvR : AddMonoidAlgebra (T.R j) (Deg D j) →ₐ[T.Q.c.F] Om Z :=
  AddMonoidAlgebra.liftNCAlgHom (evCAlg hG hT Z) 1 (fun _ _ => Commute.all _ _)

lemma formsEvR_single (d : Deg D j) (f : T.R j) :
    formsEvR j hG hT Z (AddMonoidAlgebra.single d f) = evC hG Z f := by
  show AddMonoidAlgebra.liftNC (((evCAlg hG hT Z : T.R j →+* Om Z)) : T.R j →+ Om Z)
      ((1 : Multiplicative (Deg D j) →* Om Z) : Multiplicative (Deg D j) → Om Z) (AddMonoidAlgebra.single d f) = _
  rw [AddMonoidAlgebra.liftNC_single]
  simp [evCAlg_apply]

end Inst

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.FullExists
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Full (D : D7) : Type 1 extends Top D where
  cE : ∀ (j : ℕ) (σ : Q.c.F →+* ℂ), (U j σ).Comp → ℂ
  chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle
  x₀ : ℕ → (Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ
  iota : ∀ j : ℕ, (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)
  xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ
  half₂ : Ideal (𝓞 D.host.E)

variable {D : D7}

def Full.J (T : Full D) : CoreJ D :=
  { toCore := T.toTop.toCore, cE := T.cE, chiW := T.chiW, x₀ := T.x₀, iota := T.iota }

def Full.XiVal (T : Full D) (j n : ℕ) : Prop :=
  ∃ (hr : (T.V j T.σ₀).rank = D.R.r) (U₂ : _) (dict₂ : _),
    CXiVal (T.V j T.σ₀) hr T.σ₀ (Tup := Unit) (fun _ => T.dδ j n) U₂ dict₂
      (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) (T.x₀ j T.σ₀) fun _ => T.xi

structure LawsFull (T : Full D) : Prop where
  p : LawsP T.toTop
  j : LawsJ T.J
  sh : LawsSh T.toTop

  canon : T.Q.Canon

  lvA : ∀ j, InR D j → ∀ n, (T.dδ j n).l₂.A = 1

  halfI : ∀ j, InR D j → ∀ n, (T.dδ j n).I = T.half₂

  shUniq : ∀ j, InR D j → ∀ n (_ : StarRing (𝓞 D.host.E)) (nab' : NabV (T.dδ j n).Xo₂ (T.dδ j n).c₂),
    IsNab (T.dδ j n).Xo₂ (T.dδ j n).c₂ nab' → ∀ a, Dom a n →
      shortGen (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV a n { T.dδ j n with nab₂ := nab' } =
        shortGen (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV a n (T.dδ j n)

  xiVal : ∀ j, InR D j → ∀ n, T.XiVal j n

def FullExists (D : D7) (pb : Fin 2 → IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.K)) (chi₀ : ℕ → (AE D)ˣ →* Circle)
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (I : Ideal (𝓞 D.host.E)) : Prop :=
  ∃ T : Full D, LawsFull T ∧ T.pb = pb ∧ (∀ j, T.chiW j T.σ₀ = chi₀ j) ∧ T.xi = xi ∧ T.half₂ = I

end Formalism.L2.Pj
end
end

