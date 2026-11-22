import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IndepPts
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

theorem spMap_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (ψ.comp φ) = spMap ψ ≫ spMap φ := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem dualMap_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) := RingHom.ext fun x => by ext <;> simp [dualMap]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem frMap_refl {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    FrMap (AlgHom.id c.F S) y y := by
  have e : dualMap (AlgHom.id c.F S).toRingHom = RingHom.id _ :=
    RingHom.ext fun x => by ext <;> simp [dualMap]
  refine ⟨?_, ?_, 𝟙 _, ?_, ?_, ?_⟩
  · rw [spMap_algHom_id, Category.id_comp]
  · intro τ i
    rw [e]
    simp [spMap]
  · exact Category.id_comp _
  · rw [spMap_algHom_id]
    simp
  · intro i h
    rw [show Scheme.Hom.appLE (𝟙 (Gx y.x)) _ _ h = Scheme.Hom.app (𝟙 (Gx y.x)) ((PPx y.x).U i) from
      (Scheme.Hom.app_eq_appLE _).symm, Scheme.Hom.id_app]
    rfl

theorem frMap_trans {S T U : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U]
    [Algebra c.F U] (φ : S →ₐ[c.F] T) (ψ : T →ₐ[c.F] U) {y : FrPt Xo c S} {z : FrPt Xo c T} {w : FrPt Xo c U}
    (h₁ : FrMap φ y z) (h₂ : FrMap ψ z w) : FrMap (ψ.comp φ) y w := by
  have hc : (ψ.comp φ).toRingHom = ψ.toRingHom.comp φ.toRingHom := rfl
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  refine ⟨?_, ?_, pm2 ≫ pm1, ?_, ?_, ?_⟩
  · rw [hx2, hx1, hc, spMap_comp, Category.assoc]
  · intro τ i
    rw [hu2, hu1, hc, dualMap_comp, spMap_comp, Category.assoc]
  · rw [Category.assoc, hs1, hs2]
  · rw [Category.assoc, hf1, ← Category.assoc, hf2, Category.assoc, ← spMap_comp, hc]
  · intro i h
    have hb1 : ∀ p, (snd (Over.mk y.x) Xo.univ.t.G).left.base (pm1.base p) =
        (snd (Over.mk z.x) Xo.univ.t.G).left.base p := fun p => by
      rw [← hs1]; rfl
    have hb2 : ∀ p, (snd (Over.mk z.x) Xo.univ.t.G).left.base (pm2.base p) =
        (snd (Over.mk w.x) Xo.univ.t.G).left.base p := fun p => by
      rw [← hs2]; rfl
    have h1 : (PPx z.x).U i ≤ pm1 ⁻¹ᵁ (PPx y.x).U i := by
      intro p hp
      change p ∈ (⋂ k, (snd (Over.mk z.x) Xo.univ.t.G).left.base ⁻¹' ((Xo.univ.t.PP.L.U (i k)) : Set _)) at hp
      change pm1.base p ∈ (⋂ k, (snd (Over.mk y.x) Xo.univ.t.G).left.base ⁻¹' ((Xo.univ.t.PP.L.U (i k)) : Set _))
      simp only [Set.mem_iInter, Set.mem_preimage] at hp ⊢
      intro k
      rw [hb1]
      exact hp k
    have h2 : (PPx w.x).U i ≤ pm2 ⁻¹ᵁ (PPx z.x).U i := by
      intro p hp
      change p ∈ (⋂ k, (snd (Over.mk w.x) Xo.univ.t.G).left.base ⁻¹' ((Xo.univ.t.PP.L.U (i k)) : Set _)) at hp
      change pm2.base p ∈ (⋂ k, (snd (Over.mk z.x) Xo.univ.t.G).left.base ⁻¹' ((Xo.univ.t.PP.L.U (i k)) : Set _))
      simp only [Set.mem_iInter, Set.mem_preimage] at hp ⊢
      intro k
      rw [hb2]
      exact hp k
    rw [← Scheme.Hom.appLE_comp_appLE pm2 pm1 _ _ _ h1 h2]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    rw [ha1 i h1, ha2 i h2]

theorem faithfullyFlat_id (S : Type) [CommRing S] : (RingHom.id S).FaithfullyFlat := by
  show Module.FaithfullyFlat S S
  exact Module.FaithfullyFlat.self S

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeB
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X)

def cpθ : ChartPull (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)) (PPx x) (gxU x) :=
  (PullOf.lin (K := Fin 1) Xo.univ.t.PP.L (snd (Over.mk x) Xo.univ.t.G).left).cp
    (PullOf.lin (K := PUnit) Xo.univ.t.PP.L (pullback.fst Xo.univ.t.G.hom x)) (gxU x) (gxU_snd x)

def cpV : ChartPull (PPx x) (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)) (gxV x) :=
  (PullOf.lin (K := PUnit) Xo.univ.t.PP.L (pullback.fst Xo.univ.t.G.hom x)).cp
    (PullOf.lin (K := Fin 1) Xo.univ.t.PP.L (snd (Over.mk x) Xo.univ.t.G).left) (gxV x) (gxV_fst x)

def cpσ : ChartPull ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)).pull
      (pullback.fst (pullback.snd Xo.univ.t.G.hom x) (spMap ψ)))
    (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)) (pullback.fst _ (spMap ψ)) :=
  chartPullPull _ _ _ rfl

def cpU' : ChartPull ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)).pull
      (pullback.fst (pullback.snd Xo.univ.t.G.hom x) (spMap ψ))) (PPx (spMap ψ ≫ x)) (bcU ψ x) :=
  (PullOf.lin (K := Fin 1) Xo.univ.t.PP.L (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left).cp
    ((PullOf.lin (K := PUnit) Xo.univ.t.PP.L (pullback.fst Xo.univ.t.G.hom x)).pull _) (bcU ψ x) (bcU_snd ψ x)

def cpV' : ChartPull (PPx (spMap ψ ≫ x)) ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)).pull
      (pullback.fst (pullback.snd Xo.univ.t.G.hom x) (spMap ψ))) (bcV ψ x) :=
  ((PullOf.lin (K := PUnit) Xo.univ.t.PP.L (pullback.fst Xo.univ.t.G.hom x)).pull _).cp
    (PullOf.lin (K := Fin 1) Xo.univ.t.PP.L (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left) (bcV ψ x)
    (bcV_snd' ψ x)

def cpS : ChartPull (PPx (spMap ψ ≫ x)) (PPx x) (bcPm ψ x) :=
  cpSame Xo.univ.t.PP.L (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left)
    (fun _ => (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left) (fun _ => 1) (bcPm ψ x) (fun _ => bcPm_snd ψ x)

def tA : SAB H (Sp S) := sabT ReciprocityTheory.ChartRestriction.G.Out.proved_CubePullSt x Xo.univ.t
def mA : SABMap (tA x) Xo.univ.t x := sabM ReciprocityTheory.ChartRestriction.G.Out.proved_CubePullSt x Xo.univ.t

def tB : SAB H (Sp T) := sabT ReciprocityTheory.ChartRestriction.G.Out.proved_CubePullSt (spMap ψ) (tA x)
def mB : SABMap (tB ψ x) (tA x) (spMap ψ) := sabM ReciprocityTheory.ChartRestriction.G.Out.proved_CubePullSt (spMap ψ) (tA x)

def θA (s0 : LB.Sec (PPx x)) : LB.Sec (tA x).PP.L := secCP (cpθ x) s0

def σB (s0 : LB.Sec (PPx x)) : LB.Sec (tB ψ x).PP.L := secCP (cpσ ψ x) (θA x s0)

theorem hθ_of (s0 : LB.Sec (PPx x)) (hgen : ∀ s' : LB.Sec (PPx x), ∃! a : S, ∀ i, s'.f i = scal x a i * s0.f i)
    (σ : LB.Sec (tA x).PP.L) : ∃ a : S, ∀ i, σ.f i = constFn (tA x).G.hom _ a * (θA x s0).f i := by
  obtain ⟨a, ha, -⟩ := hgen (secCP (cpV x) σ)
  refine ⟨a, (sec_eq_iff _ σ (θA x s0) a).2 fun i q hq => ?_⟩
  have hJ : gxU x q ∈ (PPx x).U (fun _ => i PUnit.unit) := (cpθ x).le i hq
  have h2 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_of_id (gxU x) q hJ ((scal_eq_iff x _ _ a).1 ha _ (gxU x q) hJ)
  rw [gs_secCP (cpV x) σ (gxU x) q _ hJ, gxU_gxV, gxU_fst] at h2
  have e3 : gs (𝟙 _) q ((tA x).PP.L.U i) ((θA x s0).f i) =
      gs (gxU x) q ((PPx x).U (fun _ => i PUnit.unit)) (s0.f (fun _ => i PUnit.unit)) :=
    (gs_secCP (cpθ x) s0 (𝟙 _) q i hq).trans (by rw [Category.id_comp]; rfl)
  rw [e3]
  exact h2

theorem hσ_of (s0 : LB.Sec (PPx x)) (y : (tB ψ x).G.left) (j : PUnit → Xo.univ.t.PP.L.ι)
    (k : PUnit → PUnit → Xo.univ.t.PP.L.ι) (hj : (mB ψ x).φ y ∈ (tA x).PP.L.U j) (hk : y ∈ (tB ψ x).PP.L.U k) :
    gs (mB ψ x).φ y _ ((θA x s0).f j) =
      (gw (idIso ((tA x).PP.L.pull (mB ψ x).φ)) (𝟙 _) y j k).val * gs (𝟙 _) y _ ((σB ψ x s0).f k) := by
  have hk' : (mB ψ x).φ y ∈ (tA x).PP.L.U (k PUnit.unit) := mem_pull.1 hk
  have e1 := gm_pull_g (tA x).PP.L (mB ψ x).φ (𝟙 _) y (fun _ => j) k (mem_pull.2 hj) hk
  rw [Category.id_comp] at e1
  have e2 : gs (𝟙 _) y ((tB ψ x).PP.L.U k) ((σB ψ x s0).f k) =
      gs (mB ψ x).φ y ((tA x).PP.L.U (k PUnit.unit)) ((θA x s0).f (k PUnit.unit)) :=
    (gs_secCP (cpσ ψ x) (θA x s0) (𝟙 _) y k hk).trans (by rw [Category.id_comp]; rfl)
  rw [e2, gs_compat (θA x s0) (mB ψ x).φ y hj hk']
  exact congrArg (· * _) (congrArg Units.val e1.symm)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GermExCut
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

def TruncatedIntegralChartExists : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io), yI.IsAlg →
      ∃ C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI,
        Formalism.MainNotions.ModuliIntegralCharts.H1.FrTrunc C.I.G (𝟙 (Sp Tc.V)) (chD C.ch) C.xT C.eT

def SecTie {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Tc : CDVR} {io : c.F →+* Tc.Fr} {yI : IntFr Xo c Tc io}
    (I : IntData Xo c Tc io yI.1) (k : ℕ)
    (F : letI := io.toAlgebra; LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo yI.1.x)))
    (σ : LB.Sec (LB.LinComb I.G.PP.L (K := Fin 1) (fun _ => 𝟙 I.G.G.left) (fun _ => (k : ℤ)))) : Prop :=
  letI := io.toAlgebra
  ∃ σt : LB.Sec (LB.LinComb I.t'.PP.L (K := Fin 1) (fun _ => 𝟙 I.t'.G.left) (fun _ => (k : ℤ))),
    (∀ (Z : Scheme.{0}) (r : Z ⟶ I.t'.G.left) (zp : Z ⟶ Gx yI.1.x),
      zp ≫ (snd (Over.mk yI.1.x) Xo.univ.t.G).left = r ≫ I.m1.φ →
      zp ≫ (fst (Over.mk yI.1.x) Xo.univ.t.G).left = r ≫ I.t'.G.hom →
      ∀ (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι)
        (J' : (Z ⟶ I.t'.G.left) → I.t'.PP.L.ι), Good Xo.univ.t.PP.L z J → Good I.t'.PP.L z J' →
        sval (show LB.Sec (LB.LinComb Xo.univ.t.PP.L (K := Fin 1)
            (fun _ => (snd (ptO Xo yI.1.x) Xo.univ.t.G).left) (fun _ => (k : ℤ))) from F) zp z J =
          ((gv I.w1 r z (fun _ => J (r ≫ I.m1.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval σt r z J') ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ I.t'.G.left) (z : Z) (J : (Z ⟶ I.G.G.left) → I.G.PP.L.ι)
      (J' : (Z ⟶ I.t'.G.left) → I.t'.PP.L.ι), Good I.G.PP.L z J → Good I.t'.PP.L z J' →
      sval σ (r ≫ I.m2.φ) z J =
        ((gv I.w2 r z (fun _ => J (r ≫ I.m2.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval σt r z J'

def FrameTieSt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] : Prop :=
  ∀ (Tc : CDVR) (io : c.F →+* Tc.Fr) (yI : IntFr Xo c Tc io) (C : IntegralChartA3 Xo c Tc io yI),
    letI := io.toAlgebra
    ∃ x' : ∀ m, jOG (𝟙 (Sp Tc.Fr)) (chD C.ch) m 1 ⟶ C.I.t'.G,
      (∀ m, (x' m).left ≫ C.I.m1.φ = (C.ch.x m).left) ∧
      (∀ m, (x' m).left ≫ C.I.m2.φ =
        spMap (jetCoef (algebraMap Tc.V Tc.Fr) (Fin 1 × Fin (chD C.ch)) m) ≫ (C.xT m).left) ∧
      ∃ eL' : ∀ m, LB.Gen (LB.LinComb C.I.t'.PP.L (K := Fin 1) (fun _ => (x' m).left) (fun _ => (1 : ℤ))),
        ∀ (m : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (jOG (𝟙 (Sp Tc.Fr)) (chD C.ch) m 1).left) (z : Z)
          (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) (J' : (Z ⟶ C.I.t'.G.left) → C.I.t'.PP.L.ι)
          (J'' : (Z ⟶ C.I.G.G.left) → C.I.G.PP.L.ι),
          Good Xo.univ.t.PP.L z J → Good C.I.t'.PP.L z J' → Good C.I.G.PP.L z J'' →
          val (eL yI.1 C.ch.d C.ch.x C.ch.B.A.act C.ch.e C.ch.wP m) r z J =
            gv C.I.w1 (r ≫ (x' m).left) z (fun _ => J ((r ≫ (x' m).left) ≫ C.I.m1.φ))
              (J' ((r ≫ (x' m).left) ≫ 𝟙 _)) * val (eL' m) r z J' ∧
          val (eLG C.I.G (𝟙 (Sp Tc.V)) (chD C.ch) C.xT C.actT C.eT C.wPT m)
              (r ≫ spMap (jetCoef (algebraMap Tc.V Tc.Fr) (Fin 1 × Fin (chD C.ch)) m)) z J'' =
            gv C.I.w2 (r ≫ (x' m).left) z (fun _ => J'' ((r ≫ (x' m).left) ≫ C.I.m2.φ))
              (J' ((r ≫ (x' m).left) ≫ 𝟙 _)) * val (eL' m) r z J'

def zCast {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {k₁ k₂ : ℤ} (h : k₁ = k₂)
    (F : LB.Sec (LPow A L k₁ T)) : LB.Sec (LPow A L k₂ T) := h ▸ F

theorem natCast_sq (M : ℕ) : ((M : ℤ) ^ 2) = ((M ^ 2 : ℕ) : ℤ) := (Nat.cast_pow M 2).symm

def SplitModel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Tc : CDVR} {io : c.F →+* Tc.Fr} {yI : IntFr Xo c Tc io}
    (I : IntData Xo c Tc io yI.1) : Prop :=
  ∃ S : SplitExt (Sp (IsLocalRing.ResidueField Tc.V)),
    S.IsGt ((Over.pullback (spMap (IsLocalRing.residue Tc.V))).obj I.G.G)

def RegTieSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
      ((T.Q.l.M : 𝓞 T.Q.c.F) ∉ la.asIdeal) →
    ∀ (I : IntData (T.Q.Xo j) T.Q.c Tc io yI.1), SplitModel I → ∀ (x : (T.Q.Dw j).La),
      letI := io.toAlgebra
      ∀ (F : LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L ((T.Q.l.M : ℤ) ^ 2)
        (ptO (T.Q.Xo j) yI.1.x))),
      IsVtOver (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP T.Q.l.M (KilledBy (T.Q.Xo j) (T.Q.l.Mb ^ 2)) yI.1.s
        (levPt (T.Q.Xo j) yI.1.x x) F →
      ∃ σ : LB.Sec (LB.LinComb I.G.PP.L (K := Fin 1) (fun _ => 𝟙 I.G.G.left)
          (fun _ => ((T.Q.l.M ^ 2 : ℕ) : ℤ))),
        SecTie I (T.Q.l.M ^ 2) (zCast (T.Q.Xo j).univ.t.G (natCast_sq T.Q.l.M) F) σ

def GermTieSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io)
      (C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI),
      Formalism.MainNotions.ModuliIntegralCharts.H1.FrTrunc C.I.G (𝟙 (Sp Tc.V)) (chD C.ch) C.xT C.eT →
    ∀ (k : ℕ),
      letI := io.toAlgebra
      ∀ (F : LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L (k : ℤ) (ptO (T.Q.Xo j) yI.1.x)))
        (σ : LB.Sec (LB.LinComb C.I.G.PP.L (K := Fin 1) (fun _ => 𝟙 C.I.G.G.left) (fun _ => (k : ℤ)))),
        SecTie C.I k F σ →
        ∃ g : Germ.PS Tc.Fr 1 (chD C.ch),
          IsGerm yI.1 C.ch.d C.ch.x C.ch.B.A.act C.ch.e C.ch.wP k F g ∧ IsIntPS Tc g

def GermChartSplitFibre : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
      ((T.Q.l.M : 𝓞 T.Q.c.F) ∉ la.asIdeal) →
      (∀ I : IntData (T.Q.Xo j) T.Q.c Tc io yI.1, SplitModel I) → ∀ {n : ℕ} (x : Fin n → (T.Q.Dw j).La),
      letI := io.toAlgebra
      ∀ (F : Fin n → LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L ((T.Q.l.M : ℤ) ^ 2)
        (ptO (T.Q.Xo j) yI.1.x))),
      (∀ b, IsVtOver (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP T.Q.l.M (KilledBy (T.Q.Xo j) (T.Q.l.Mb ^ 2)) yI.1.s
        (levPt (T.Q.Xo j) yI.1.x (x b)) (F b)) →
      ∃ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI) (g : Fin n → Germ.PS Tc.Fr 1 (chD C.ch)),
        (∀ b, IsGerm yI.1 C.ch.d C.ch.x C.ch.B.A.act C.ch.e C.ch.wP (T.Q.l.M ^ 2)
          (zCast (T.Q.Xo j).univ.t.G (natCast_sq T.Q.l.M) (F b)) (g b)) ∧ ∀ b, IsIntPS Tc (g b)

theorem germ_chart_split_fibre_exists (hT : TruncatedIntegralChartExists) (hR : RegTieSt) (hG : GermTieSt) : GermChartSplitFibre := by
  intro D T h j hj _ hstar Tc io yI e la ho hy hM hsplit n x F hV
  obtain ⟨C, hC⟩ := hT D T h j hj hstar Tc io yI hy
  letI := io.toAlgebra
  choose σ hσ using fun b => hR D T h j hj hstar Tc io yI e la ho hy hM C.I (hsplit C.I) (x b) (F b) (hV b)
  choose g hg hgI using fun b => hG D T h j hj hstar Tc io yI C hC (T.Q.l.M ^ 2)
    (zCast (T.Q.Xo j).univ.t.G (natCast_sq T.Q.l.M) (F b)) (σ b) (hσ b)
  exact ⟨C, g, hg, hgI⟩

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JInjRdOf
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

open Classical in

theorem rdU_apply_dom {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (f : Rul Xo c) (k : U.Comp) (x : (U.X k).dom) : rdU U f k x.1 = toC (evR Xo c f (U.un k x)) := by
  show (if h : x.1 ∈ (U.X k).dom then toC (evR Xo c f (U.un k ⟨x.1, h⟩)) else 0) = _
  rw [dif_pos x.2]

theorem rel_of_frames {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (hU3 : ∀ y : FrPt Xo c (CAt σ), ∃ k, ∃ x : (U.X k).dom, ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k x) y)
    (hT : ∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x))
    (hF : WtField Xo c) {m : ℕ} (fs : Fin m → Rul Xo c) (hfs : ∀ i, fs i ∈ sec Xo c a n) (g : Fin m → ℂ)
    (hrel : ∀ k (x : (U.X k).dom), ∑ i, g i * toC (evR Xo c (fs i) (U.un k x)) = 0)
    (z : FrPt Xo c (CAt σ)) (hz : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z) :
    ∑ i, g i * toC (evR Xo c (fs i) z) = 0 := by
  obtain ⟨k, x, t, hbor⟩ := hU3 z
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  have hv : ∀ i, evR Xo c (fs i) z = wchar (ex Dw a n) t * evR Xo c (fs i) (U.un k x) :=
    fun i => hF a n (fs i) (hfs i) (CAt σ) t _ z (hT k x) hz hbor
  calc ∑ i, g i * toC (evR Xo c (fs i) z)
      = ∑ i, g i * (toC (wchar (ex Dw a n) t) * toC (evR Xo c (fs i) (U.un k x))) :=
        Finset.sum_congr rfl fun i _ => by rw [hv i]; rfl
    _ = toC (wchar (ex Dw a n) t) * ∑ i, g i * toC (evR Xo c (fs i) (U.un k x)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by rw [hrel k x, mul_zero]

end Frames

theorem jInjRd_of_wt {D : D7} (T : Top D) (hM : LawsM T.toCore) {j : ℕ} (hj : InR D j)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (hA : BCEx (T.Q.Xo j) T.Q.c T.σ₀) (hF : WtField (T.Q.Xo j) T.Q.c) :
    JInjRd T j a n := by
  intro m b hb
  have hU : IsUnf (T.U j T.σ₀) := hM.unf j hj T.σ₀ T.good_σ₀
  have hb' := hb.map' (cusp (T.Q.Xo j) T.Q.c (T.U j) a n).subtype (Submodule.ker_subtype _)
  have hfs : ∀ i, (⇑(cusp (T.Q.Xo j) T.Q.c (T.U j) a n).subtype ∘ b) i ∈ sec (T.Q.Xo j) T.Q.c a n :=
    fun i => cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) a n (b i).2
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hrel : ∀ k (x : ((T.U j T.σ₀).X k).dom),
      ∑ i, g i * toC (evR (T.Q.Xo j) T.Q.c ((⇑(cusp (T.Q.Xo j) T.Q.c (T.U j) a n).subtype ∘ b) i)
        ((T.U j T.σ₀).un k x)) = 0 := by
    intro k x
    have h := congrFun (congrFun hg k) x.1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← rdU_apply_dom (T.U j T.σ₀) _ k x]; rfl
  have hall := rel_of_frames (T.U j T.σ₀) hU.2.2.1 (hM.unTest j hj T.σ₀ T.good_σ₀) hF _ hfs g hrel
  let _ : Algebra T.Q.c.F ℂ := T.σ₀.toAlgebra
  have hc := indep_of_complex (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S)
    (fun φ y z => FrMap φ y z) (hM.evalWD j hj) (fun p φ y => hA p y φ)
    _ (fun i => (hfs i).1) hb' g (fun z hz => hall z hz)
  intro i
  exact congrFun hc i

theorem jInjRd_of_bcex {D : D7} (T : Top D) (hM : LawsM T.toCore) {j : ℕ} (hj : InR D j)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (hA : BCEx (T.Q.Xo j) T.Q.c T.σ₀) (hD : BorDesc (T.Q.Xo j) T.Q.c) : JInjRd T j a n :=
  jInjRd_of_wt T hM hj a n hA (wtField_of hD)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeD
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S] {x : Sp S ⟶ Xo.X}

theorem tv_sum {κ : Type} (s : Finset κ) (f : κ → TanM x Xo.univ.t.G) : tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => first | rfl | simp [tv]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, tv_add, ih]

variable {c}

def tvOf {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) : TanM x Xo.univ.t.G :=
  mkT (ovT (t := Xo.univ.t) hv) (smT_zero_ovT hv)

theorem tv_tvOf {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) : tv (tvOf hv) = ovT (t := Xo.univ.t) hv := rfl

variable (c) in
theorem eigAt_iff {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) (τ : E →+* ℂ) :
    IsEigAt c τ v ↔ IsEigV (actR (x0 := x) (S := S) Xo.univ.t.act) (embK c τ) (tvOf hv) := by
  refine (isEigAt_iff (c := c) τ (ovT (t := Xo.univ.t) hv)).trans ?_
  constructor
  · intro h a
    apply tanM_ext
    show tv (tvOf hv) ≫ Xo.univ.t.act.act a = _
    rw [tv_smul, tv_tvOf]
    exact h a
  · intro h a
    have h2 := congrArg tv (h a)
    change tv (tvOf hv) ≫ Xo.univ.t.act.act a = _ at h2
    rw [tv_smul, tv_tvOf] at h2
    exact h2

theorem combAt_iff {m : ℕ} (u : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hu : ∀ i, IsTanAt x (u i))
    (cf : Fin m → S) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hw : IsTanAt x w) :
    IsCombAt x u cf w ↔ tvOf hw = ∑ i, cf i • tvOf (hu i) := by
  have e1 : tv (∑ i, cf i • tvOf (hu i)) = combT x (fun j => ovT (t := Xo.univ.t) (hu j)) cf := by
    rw [tv_sum]
    simp only [tv_smul, tv_tvOf]
    rfl
  have key := isCombAtG_iff Xo.univ.t x (fun j => ovT (t := Xo.univ.t) (hu j)) cf w
  constructor
  · intro h
    apply tanM_ext
    rw [e1, tv_tvOf]
    exact Over.OverMorphism.ext (key.1 h).symm
  · intro h
    have h2 := congrArg tv h
    rw [e1, tv_tvOf] at h2
    exact key.2 (by rw [← h2]; rfl)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceBoundOddRamifiedOfCharts
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

def vdP (D : D7) (p : ℕ) : ℝ := if p = 2 then (D.R.e : ℝ) + 1 - (2 : ℝ)⁻¹ ^ D.R.e else 1 / 2

def ChartValueRamified : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)]
    (nab : NabV (T.Q.Xo j) T.Q.c), IsNab (T.Q.Xo j) T.Q.c nab →
    ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
    P ∈ harmA T.Q.c (wtA w) w.n → ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
      ∀ p ∈ ({2, D.host.q, D.host.d} : Finset ℕ), ((p : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
      IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI →
      (((-(((vLa la (p : T.Q.c.F) : ℤ) : ℝ) * vdP D p * (DF w : ℝ) / 2)) : ℝ) : EReal) ≤ nval Tc.V e (evI yI f)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIntegralUnramifiedOfCharts
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

def ChartValueUnramified : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)]
    (nab : NabV (T.Q.Xo j) T.Q.c), IsNab (T.Q.Xo j) T.Q.c nab →
    ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
    P ∈ harmA T.Q.c (wtA w) w.n → ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
      (∀ p ∈ ({2, D.host.q, D.host.d, D.host.g 0, D.host.g 1} : Finset ℕ), ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)) →
      IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI → 0 ≤ nval Tc.V e (evI yI f)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

