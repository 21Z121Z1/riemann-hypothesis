import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.BcField
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem spMap_comp_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

def bcPm {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    Gx (spMap ψ ≫ x) ⟶ Gx x :=
  ((Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ x) ⟶ Over.mk x) ▷ Xo.univ.t.G).left

theorem bcPm_snd {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    bcPm ψ x ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := by
  rw [bcPm, ← Over.comp_left, whiskerRight_snd]

theorem bcPm_fst {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    bcPm ψ x ≫ (fst (Over.mk x) Xo.univ.t.G).left =
      (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left ≫ spMap ψ := by
  rw [bcPm, ← Over.comp_left, whiskerRight_fst, Over.comp_left]
  rfl

variable (Xo c)

def BcGenSt : Prop :=
  ∀ (p : TRing c.F) (T : Type) [Field T] [Algebra c.F T] (ψ : p.R →ₐ[c.F] T) (y : FrPt Xo c p.R),
    ∃ s' : LB.Sec (PPx (spMap ψ.toRingHom ≫ y.x)),
      (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι)
        (h : (PPx (spMap ψ.toRingHom ≫ y.x)).U i ≤ bcPm ψ.toRingHom y.x ⁻¹ᵁ (PPx y.x).U i),
        ((bcPm ψ.toRingHom y.x).appLE _ _ h).hom (y.s.f i) = s'.f i) ∧
      ∀ s'' : LB.Sec (PPx (spMap ψ.toRingHom ≫ y.x)), ∃! a : T,
        ∀ i, s''.f i = scal (spMap ψ.toRingHom ≫ y.x) a i * s'.f i

def BcLieSt : Prop :=
  ∀ (p : TRing c.F) (T : Type) [Field T] [Algebra c.F T] (ψ : p.R →ₐ[c.F] T) (y : FrPt Xo c p.R)
    (τ : E →+* ℂ) (w : Sp (DualNumber T) ⟶ Xo.univ.t.G.left),
    IsTanAt (spMap ψ.toRingHom ≫ y.x) w → IsEigAt c τ w →
    ∃! a : Fin (Dw.mult τ) → T,
      IsCombAt (spMap ψ.toRingHom ≫ y.x) (fun i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i) a w

variable {Xo c}

theorem dualMap_comp_alg {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp ψ := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (TrivSqZeroExt.fstHom T T T).toRingHom.comp (dualMap ψ) = ψ.comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  refine RingHom.ext fun x => ?_
  simp [dualMap]

theorem dualMap_comp_epsMul {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (dualMap ψ) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap, epsMul, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map, smul_eq_mul, mul_comm]

theorem tan_bc {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) :
    IsTanAt (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ v) := by
  refine ⟨?_, ?_⟩
  · simp only [Category.assoc, hv.1]
    simp only [← Category.assoc, spMap_comp_spMap, dualMap_comp_alg]
  · have h1 : (Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ x) ⟶ Over.mk x) ≫
        (1 : Over.mk x ⟶ Xo.univ.t.G) = 1 := by simp
    rw [← h1, Over.comp_left]
    show _ = spMap ψ ≫ (1 : Over.mk x ⟶ Xo.univ.t.G).left
    rw [← hv.2]
    simp only [← Category.assoc, spMap_comp_spMap, fst_comp_dualMap]

theorem eig_bc {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (τ : E →+* ℂ) {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsEigAt c τ v) :
    IsEigAt c τ (spMap (dualMap ψ.toRingHom) ≫ v) := by
  intro a
  rw [Category.assoc, hv a]
  simp only [← Category.assoc, spMap_comp_spMap, dualMap_comp_epsMul, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, AlgHom.commutes]

def bcPt (hG : BcGenSt Xo c) (hL : BcLieSt Xo c) (p : TRing c.F) {T : Type} [Field T] [Algebra c.F T]
    (ψ : p.R →ₐ[c.F] T) (y : FrPt Xo c p.R) : FrPt Xo c T where
  x := spMap ψ.toRingHom ≫ y.x
  x_over := by
    rw [Category.assoc, y.x_over]
    unfold sOf
    rw [spMap_comp_spMap, ← RingHom.comp_assoc]
    congr 2
    ext r
    simp
  u τ i := spMap (dualMap ψ.toRingHom) ≫ y.u τ i
  tan τ i := tan_bc ψ.toRingHom (y.tan τ i)
  eig τ i := eig_bc ψ τ (y.eig τ i)
  basis τ w hw he := hL p T ψ y τ w hw he
  s := (hG p T ψ y).choose
  gen := (hG p T ψ y).choose_spec.2

theorem frMap_bcPt (hG : BcGenSt Xo c) (hL : BcLieSt Xo c) (p : TRing c.F) {T : Type} [Field T]
    [Algebra c.F T] (ψ : p.R →ₐ[c.F] T) (y : FrPt Xo c p.R) : FrMap ψ y (bcPt hG hL p ψ y) := by
  exact ⟨rfl, fun _ _ => rfl, bcPm ψ.toRingHom y.x, bcPm_snd _ _, bcPm_fst _ _,
    (hG p T ψ y).choose_spec.1⟩

theorem bcEx_of (hG : BcGenSt Xo c) (hL : BcLieSt Xo c) (σ : c.F →+* ℂ) : BCEx Xo c σ := by
  intro p y ψ
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  exact ⟨_, frMap_bcPt (T := CAt σ) hG hL p ψ y⟩

variable (Xo c) in

def BcGenRSt : Prop :=
  ∀ (p : TRing c.F) (T : Type) [CommRing T] [Algebra c.F T] (ψ : p.R →ₐ[c.F] T) (y : FrPt Xo c p.R),
    ∃ s' : LB.Sec (PPx (spMap ψ.toRingHom ≫ y.x)),
      (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι)
        (h : (PPx (spMap ψ.toRingHom ≫ y.x)).U i ≤ bcPm ψ.toRingHom y.x ⁻¹ᵁ (PPx y.x).U i),
        ((bcPm ψ.toRingHom y.x).appLE _ _ h).hom (y.s.f i) = s'.f i) ∧
      ∀ s'' : LB.Sec (PPx (spMap ψ.toRingHom ≫ y.x)), ∃! a : T,
        ∀ i, s''.f i = scal (spMap ψ.toRingHom ≫ y.x) a i * s'.f i

variable (Xo c) in

def BcLieRSt : Prop :=
  ∀ (p : TRing c.F) (T : Type) [CommRing T] [Algebra c.F T] (ψ : p.R →ₐ[c.F] T) (y : FrPt Xo c p.R)
    (τ : E →+* ℂ) (w : Sp (DualNumber T) ⟶ Xo.univ.t.G.left),
    IsTanAt (spMap ψ.toRingHom ≫ y.x) w → IsEigAt c τ w →
    ∃! a : Fin (Dw.mult τ) → T,
      IsCombAt (spMap ψ.toRingHom ≫ y.x) (fun i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i) a w

def bcPtR (hG : BcGenRSt Xo c) (hL : BcLieRSt Xo c) (p : TRing c.F) {T : Type} [CommRing T] [Algebra c.F T]
    (ψ : p.R →ₐ[c.F] T) (y : FrPt Xo c p.R) : FrPt Xo c T where
  x := spMap ψ.toRingHom ≫ y.x
  x_over := by
    rw [Category.assoc, y.x_over]
    unfold sOf
    rw [spMap_comp_spMap, ← RingHom.comp_assoc]
    congr 2
    ext r
    simp
  u τ i := spMap (dualMap ψ.toRingHom) ≫ y.u τ i
  tan τ i := tan_bc ψ.toRingHom (y.tan τ i)
  eig τ i := eig_bc ψ τ (y.eig τ i)
  basis τ w hw he := hL p T ψ y τ w hw he
  s := (hG p T ψ y).choose
  gen := (hG p T ψ y).choose_spec.2

theorem frMap_bcPtR (hG : BcGenRSt Xo c) (hL : BcLieRSt Xo c) (p : TRing c.F) {T : Type} [CommRing T]
    [Algebra c.F T] (ψ : p.R →ₐ[c.F] T) (y : FrPt Xo c p.R) : FrMap ψ y (bcPtR hG hL p ψ y) := by
  exact ⟨rfl, fun _ _ => rfl, bcPm ψ.toRingHom y.x, bcPm_snd _ _, bcPm_fst _ _,
    (hG p T ψ y).choose_spec.1⟩

theorem bcGenSt_of_R (h : BcGenRSt Xo c) : BcGenSt Xo c := by
  intro p T _ _ ψ y
  exact h p T ψ y

theorem bcLieSt_of_R (h : BcLieRSt Xo c) : BcLieSt Xo c := by
  intro p T _ _ ψ y τ w hw he
  exact h p T ψ y τ w hw he

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.UnifAt
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

def sabMapCast {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} {t' : SAB H S'}
    {t : SAB H S} {f f' : S' ⟶ S} (m : SABMap t' t f) (h : f = f') : SABMap t' t f' := h ▸ m

theorem sabMapCast_φ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f f' : S' ⟶ S} (m : SABMap t' t f) (h : f = f') : (sabMapCast m h).φ = m.φ := by
  subst h
  rfl

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem unifAtInt_of_model (hE : ExtVStatement) (hC : Out.CubePullSt) (Y : Model Xo c β) (h3 : Y.N3) (T : CDVR)
    (io : c.F →+* T.Fr) (b : O →+* T.V) (hb : (algebraMap T.V T.Fr).comp b = io.comp β)
    (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y)
    (hS : ∃ S : SplitExt (Sp (IsLocalRing.ResidueField T.V)),
      S.IsGt ((Over.pullback (spMap (IsLocalRing.residue T.V))).obj I.G.G)) :
    ∃ P : PELUnif (IsLocalRing.maximalIdeal T.V) I.G, P.TorsionIso := by
  let _ := io.toAlgebra
  have hcond : y.x ≫ Xo.s = spMap io ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [y.x_over]
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let z : Sp T.Fr ⟶ Xo.XF c := pullback.lift y.x (spMap io) hcond
  have hzs : z ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
  have hzf : z ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _
  have hx : z ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b := by
    show z ≫ (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hzs]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hb]
  obtain ⟨yt, h1, -⟩ := extPt Y T b z hx

  obtain ⟨PP', cub, sym, adj, prim, mP, -⟩ := sabPull hC yt Y.t
  let tP : SAB H (Sp T.V) := ⟨(Over.pullback yt).obj Y.t.G, IsSemiAbelian.pullback _ Y.t.G Y.t.semi,
    OAct.pullback _ Y.t.G Y.t.act, PP', cub, sym, adj, prim⟩
  let mP' : SABMap tP Y.t yt := mP

  obtain ⟨mF, -⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Y.oF.t I.t' (pullback.fst _ _) z Y.m0.toSABMap
    (sabMapCast I.m1 hzf.symm)
  obtain ⟨mJ, -⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t I.t' (Y.jQ ≫ pullback.fst _ _) z Y.m mF
  have hj : z ≫ Y.jQ ≫ pullback.fst _ _ = Out.jK T.V ≫ yt := h1.symm
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t tP I.t' yt (Out.jK T.V) mP' (sabMapCast mJ hj)

  have hprop : IsProper I.t'.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) I.m1.cart.1 Xo.univ.proper
  obtain ⟨ψ, -⟩ := hE E H T.V inferInstance I.G tP I.t' hprop I.m2 mK
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ Y.t tP I.G yt (𝟙 _) mP' ψ
  let n' : SABMap I.G Y.t yt := sabMapCast n (Category.id_comp yt)

  have habs : (yt ⁻¹' abLocus Y.t.G).Nonempty := by
    obtain ⟨pt⟩ : Nonempty (Sp T.Fr) := inferInstance
    refine ⟨Out.jK T.V pt, ?_⟩
    have hz : Y.jQ (z pt) ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨_, rfl⟩
    have h2 : yt (Out.jK T.V pt) = (pullback.fst Y.s (spMap β)) (Y.jQ (z pt)) := by
      rw [← Scheme.Hom.comp_apply, h1]
      show (z ≫ Y.jQ ≫ pullback.fst _ _) pt = _
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    rw [Set.mem_preimage, h2]
    exact hz
  obtain ⟨P, -, hP⟩ := h3 T.V inferInstance inferInstance inferInstance yt I.G n' habs hS
  exact ⟨P, hP⟩

end Model

def UnifAtIntLaSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j)
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    ((T.Q.l.M : 𝓞 T.Q.c.F) ∉ la.asIdeal) →
    ∀ I : IntData (T.Q.Xo j) T.Q.c Tc io yI.1,
      (∃ S : SplitExt (Sp (IsLocalRing.ResidueField Tc.V)),
        S.IsGt ((Over.pullback (spMap (IsLocalRing.residue Tc.V))).obj I.G.G)) →
      ∃ P : PELUnif (IsLocalRing.maximalIdeal Tc.V) I.G, P.TorsionIso

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

