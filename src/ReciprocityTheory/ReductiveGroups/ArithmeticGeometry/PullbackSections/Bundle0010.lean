import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.AnChart
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

def taylorPS {g : ℕ} (θ : (Fin g → ℂ) → ℂ) : MvPowerSeries (Fin 1 × Fin g) ℂ :=
  fun m => (∏ j : Fin g, (Nat.factorial (m ((0 : Fin 1), j)) : ℂ))⁻¹ *
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.monomial m (1 : ℂ)) (fun p : Fin 1 × Fin g => (Pi.single p.2 1 : Fin g → ℂ))
      θ 0

def AnChartSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)] (σ : T.Q.c.F →+* ℂ),
    GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (xf : ((T.U j σ).X k).dom),
    (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm xf.1 τ' i'‖ = 1) →
    ∀ (nab : NabV (T.Q.Xo j) T.Q.c), IsNab (T.Q.Xo j) T.Q.c nab →
    ∀ (W : UnfAt (T.U j σ) k xf) (Wu : UnitAt W),
      letI : Algebra ℚ (CAt σ) := inferInstanceAs (Algebra ℚ ℂ)
      ∃ (C : ChartAt (T.Q.Xo j) T.Q.c ((T.U j σ).un k xf)) (hd : C.d = W.g),
        C.h = 0 ∧
        (∀ i, C.B.G.F i = (MvPowerSeries.X (R := CAt σ) ((0 : Fin 2), i) + MvPowerSeries.X (R := CAt σ) ((1 : Fin 2), i))) ∧
        (∀ (τ : D.host.E →+* ℂ) (i : Fin ((T.Q.Dw j).mult τ)) (i' : Fin C.d),
          C.uvec ⟨τ, i⟩ i' = if Fin.cast hd i' = W.e.symm ⟨τ, i⟩ then 1 else 0) ∧
        ∀ (kk : ℕ) (F : LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L kk
            (ptO (T.Q.Xo j) ((T.U j σ).un k xf).x))) (θF : (Fin W.g → ℂ) → ℂ),
          IsFrRd W Wu kk F θF →
          IsGerm ((T.U j σ).un k xf) C.d C.x C.B.A.act C.e C.wP kk F
            (MvPowerSeries.rename (fun p : Fin 1 × Fin W.g => (p.1, Fin.cast hd.symm p.2)) (taylorPS θF))

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ChartValueIntegralGood
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

def ChartValueIntegralGood : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → ∀
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    (∀ p ∈ ({2, D.host.q, D.host.d} : Finset ℕ), ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)) →
    ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI) (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
      (P : MvPolynomial (LtN (T.Q.Dw j) n) Tc.Fr), P ∈ FFV (Dw := T.Q.Dw j) Tc a n →
      ∀ f : Fin n → Germ.PS Tc.Fr 1 (chD C.ch), (∀ b, IsIntPS Tc (f b)) →
        letI := io.toAlgebra
        0 ≤ nval Tc.V e (∑ mo ∈ P.support, P.coeff mo *
          ∏ b, C.ch.B.nabVal Tc.Fr C.ch.h T.Q.H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1))

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ExistsFieldOfFf
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem appLE_congr {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U)
    (hg : V ≤ g ⁻¹ᵁ U) : f.appLE U V hf = g.appLE U V hg := by
  subst e
  rfl

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeC
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X)

theorem key_fwd (s0 : LB.Sec (PPx x)) (s'' : LB.Sec (PPx (spMap ψ ≫ x))) (a : T)
    (h : ∀ i, (secCP (cpU' ψ x) s'' : LB.Sec (tB ψ x).PP.L).f i = constFn (tB ψ x).G.hom _ a * (σB ψ x s0).f i) :
    ∀ i, s''.f i = scal (spMap ψ ≫ x) a i * (secCP (cpS ψ x) s0).f i := by
  rw [sec_eq_iff] at h
  rw [scal_eq_iff]
  intro J yy hy
  have hp : bcV ψ x yy ∈ (tB ψ x).PP.L.U (fun _ _ => J 0) := (cpV' ψ x).le J hy
  have h1 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_of_id (bcV ψ x) yy hp (h _ _ hp)
  have A1 : gs (bcV ψ x) yy ((tB ψ x).PP.L.U (fun _ _ => J 0))
        ((secCP (cpU' ψ x) s'' : LB.Sec (tB ψ x).PP.L).f (fun _ _ => J 0)) =
      gs (𝟙 _) yy ((PPx (spMap ψ ≫ x)).U (fun _ => J 0)) (s''.f (fun _ => J 0)) :=
    (gs_secCP (cpU' ψ x) s'' (bcV ψ x) yy _ hp).trans (by rw [bcV_bcU]; rfl)
  have hp2 : (bcV ψ x ≫ pullback.fst _ _) yy ∈
      (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)).U (fun _ => J 0) := (cpσ ψ x).le _ hp
  have A2 : gs (bcV ψ x) yy ((tB ψ x).PP.L.U (fun _ _ => J 0)) ((σB ψ x s0).f (fun _ _ => J 0)) =
      gs (bcPm ψ x) yy ((PPx x).U (fun _ => J 0)) (s0.f (fun _ => J 0)) :=
    (gs_secCP (cpσ ψ x) (θA x s0) (bcV ψ x) yy _ hp).trans
      ((gs_secCP (cpθ x) s0 _ yy _ hp2).trans (by rw [Category.assoc, bcV_gxU]; rfl))
  have A3 : bcV ψ x ≫ (tB ψ x).G.hom = (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := bcV_snd ψ x
  rw [A1, A2, A3] at h1
  have hJ : (fun _ : Fin 1 => J 0) = J := funext fun k => by rw [Subsingleton.elim k 0]
  rw [hJ] at h1
  have e4 : gs (𝟙 _) yy ((PPx (spMap ψ ≫ x)).U J) ((secCP (cpS ψ x) s0).f J) =
      gs (bcPm ψ x) yy ((PPx x).U J) (s0.f J) :=
    (gs_secCP (cpS ψ x) s0 (𝟙 _) yy J hy).trans (by rw [Category.id_comp]; rfl)
  exact h1.trans (congrArg _ e4.symm)

theorem key_bwd (s0 : LB.Sec (PPx x)) (s'' : LB.Sec (PPx (spMap ψ ≫ x))) (a : T)
    (h : ∀ i, s''.f i = scal (spMap ψ ≫ x) a i * (secCP (cpS ψ x) s0).f i) :
    ∀ i, (secCP (cpU' ψ x) s'' : LB.Sec (tB ψ x).PP.L).f i = constFn (tB ψ x).G.hom _ a * (σB ψ x s0).f i := by
  rw [scal_eq_iff] at h
  rw [sec_eq_iff]
  intro i q hq
  have hq' : bcU ψ x q ∈ (PPx (spMap ψ ≫ x)).U (fun _ => i PUnit.unit PUnit.unit) := (cpU' ψ x).le i hq
  have h1 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_of_id (bcU ψ x) q hq' (h _ _ hq')
  rw [bcU_fst] at h1
  have B0 : gs (𝟙 _) q ((tB ψ x).PP.L.U i) ((secCP (cpU' ψ x) s'' : LB.Sec (tB ψ x).PP.L).f i) =
      gs (bcU ψ x) q ((PPx (spMap ψ ≫ x)).U (fun _ => i PUnit.unit PUnit.unit))
        (s''.f (fun _ => i PUnit.unit PUnit.unit)) :=
    (gs_secCP (cpU' ψ x) s'' (𝟙 _) q i hq).trans (by rw [Category.id_comp]; rfl)
  have B1 : gs (bcU ψ x) q ((PPx (spMap ψ ≫ x)).U (fun _ => i PUnit.unit PUnit.unit))
        ((secCP (cpS ψ x) s0).f (fun _ => i PUnit.unit PUnit.unit)) =
      gs (𝟙 _) q ((tB ψ x).PP.L.U i) ((σB ψ x s0).f i) := by
    refine (gs_secCP (cpS ψ x) s0 (bcU ψ x) q _ hq').trans ?_
    rw [bcU_bcPm]
    exact ((gs_secCP (cpσ ψ x) (θA x s0) (𝟙 _) q i hq).trans
      ((gs_secCP (cpθ x) s0 _ q _ ((cpσ ψ x).le i hq)).trans (by rfl))).symm
  exact B0.trans (h1.trans (congrArg _ B1))

theorem genBC_frame (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt)
    {K : Type} [Field K] (ρ : S →+* K) (s0 : LB.Sec (PPx x))
    (hgen : ∀ s' : LB.Sec (PPx x), ∃! a : S, ∀ i, s'.f i = scal x a i * s0.f i) (s'' : LB.Sec (PPx (spMap ρ ≫ x))) :
    ∃! a : K, ∀ i, s''.f i = scal (spMap ρ ≫ x) a i * (secCP (cpS ρ x) s0).f i := by
  obtain ⟨a, ha, hu⟩ := gen_baseChange hS hT Xo.univ (mA x) (θA x s0) (hθ_of x s0 hgen) ρ (mB ρ x)
    (w := idIso ((tA x).PP.L.pull (mB ρ x).φ)) (σB ρ x s0) (hσ_of ρ x s0) (secCP (cpU' ρ x) s'')
  exact ⟨a, key_fwd ρ x s0 s'' a ha, fun a' ha' => hu a' (key_bwd ρ x s0 s'' a' ha')⟩

theorem bcGenSt_of (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt)
    (c : Coeff l) : BcGenSt Xo c := by
  intro p K _ _ ψ' y
  exact ⟨secCP (cpS ψ'.toRingHom y.x) y.s, fun i h => rfl, genBC_frame y.x hS hT ψ'.toRingHom y.s y.gen⟩

theorem bcEx_of_laws (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt)
    (c : Coeff l) (hL : BcLieSt Xo c) (σ : c.F →+* ℂ) : BCEx Xo c σ :=
  bcEx_of (bcGenSt_of hS hT c) hL σ

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeE
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]

theorem tvOf_tv {x : Sp S ⟶ Xo.X} (n : TanM x Xo.univ.t.G) :
    tvOf (isTanAtG_of (t := Xo.univ.t) (x0 := x) (tv n) (tv_mem n)) = n := by
  apply tanM_ext
  first
    | rfl
    | exact Over.OverMorphism.ext rfl
    | (ext; rfl)
    | (ext1; simp [tvOf, tv, mkT])
    | simp [tvOf, tv, mkT]

theorem eig_coords (y : FrPt Xo c S) (τ : E →+* ℂ) (n : TanM y.x Xo.univ.t.G)
    (hn : IsEigV (actR (x0 := y.x) (S := S) Xo.univ.t.act) (embK c τ) n) :
    ∃! a : Fin (Dw.mult τ) → S, n = ∑ i, a i • tvOf (y.tan τ i) := by
  have hw := isTanAtG_of (t := Xo.univ.t) (x0 := y.x) (tv n) (tv_mem n)
  have hE := (eigAt_iff c hw τ).2 (by rw [tvOf_tv]; exact hn)
  obtain ⟨a, ha, huniq⟩ := y.basis τ _ hw hE
  refine ⟨a, ?_, fun a' h' => huniq a' ((combAt_iff (y.u τ) (y.tan τ) a' hw).2 ?_)⟩
  · have h1 := (combAt_iff (y.u τ) (y.tan τ) a hw).1 ha
    rw [tvOf_tv] at h1
    exact h1
  · rw [tvOf_tv]
    exact h'

theorem eig_comb {x : Sp S ⟶ Xo.X} (τ : E →+* ℂ) {m : ℕ} (v : Fin m → TanM x Xo.univ.t.G)
    (hv : ∀ i, IsEigV (actR (x0 := x) (S := S) Xo.univ.t.act) (embK c τ) (v i)) (a : Fin m → S) :
    IsEigV (actR (x0 := x) (S := S) Xo.univ.t.act) (embK c τ) (∑ i, a i • v i) := by
  intro b
  rw [map_sum]
  refine (Finset.sum_congr rfl fun i _ => ?_).trans Finset.smul_sum.symm
  rw [map_smul, hv i b]
  exact smul_comm _ _ _

def fullB (y : FrPt Xo c S) : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → TanM y.x Xo.univ.t.G :=
  fun k => tvOf (y.tan k.1 k.2)

theorem fullB_eig (y : FrPt Xo c S) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    IsEigV (actR (x0 := y.x) (S := S) Xo.univ.t.act) (embK c τ) (fullB y ⟨τ, i⟩) :=
  (eigAt_iff c (y.tan τ i) τ).1 (y.eig τ i)

theorem fullB_basis (y : FrPt Xo c S) (m : TanM y.x Xo.univ.t.G) :
    ∃! a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → S, m = ∑ k, a k • fullB y k := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := actR (x0 := y.x) (S := S) Xo.univ.t.act
  have hsum : ∑ τ, proj ρ (embK c) α τ m = m := by
    have := congrArg (fun e : Module.End S (TanM y.x Xo.univ.t.G) => e m) (sum_proj ρ (embK c) α hinj)
    simpa [LinearMap.sum_apply] using this
  have hE : ∀ τ, IsEigV ρ (embK c τ) (proj ρ (embK c) α τ m) := fun τ =>
    eig_of_alpha ρ (embK c) α hN τ (proj_eig_alpha ρ (embK c) α hinj f hf hfs τ m)
  choose a ha hu using fun τ => eig_coords y τ (proj ρ (embK c) α τ m) (hE τ)
  refine ⟨fun k => a k.1 k.2, ?_, fun b hb => ?_⟩
  · show m = ∑ k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), a k.1 k.2 • fullB y k
    rw [Fintype.sum_sigma]
    conv_lhs => rw [← hsum]
    exact Finset.sum_congr rfl fun τ _ => ha τ
  · have hb' : m = ∑ k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), b k • fullB y k := hb
    rw [Fintype.sum_sigma] at hb'
    funext k
    obtain ⟨τ, i⟩ := k
    have hn := proj_sum_eig ρ (embK c) α hinj (fun τ => ∑ i, b ⟨τ, i⟩ • fullB y ⟨τ, i⟩)
      (fun τ => eig_comb τ _ (fun i => fullB_eig y τ i) _) τ
    rw [← hb'] at hn
    have := hu τ (fun i => b ⟨τ, i⟩) hn
    exact congrFun this i

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RdIndepOf
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem rdIndep_of_wt (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ)
    (hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (hAT : AllTest Xo c)
    (hU : IsUnf (U σ)) (hA : BCEx Xo c σ) (hF : WtField Xo c) : RdIndep Xo c U σ := by
  intro a k _ n b hb hli
  have hT : ∀ kk x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((U σ).un kk x) := by
    intro kk x
    letI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
    exact hAT (CAt σ) ((U σ).un kk x)
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hrel : ∀ kk (x : ((U σ).X kk).dom), ∑ i, g i * toC (evR Xo c (b i) ((U σ).un kk x)) = 0 := by
    intro kk x
    have h := congrFun (congrFun hg kk) x.1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [← rdU_apply_dom (U σ) _ kk x]
  have hall := rel_of_frames (U σ) hU.2.2.1 hT hF b hb g hrel
  let _ : Algebra c.F ℂ := σ.toAlgebra
  have hc := indep_of_complex (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) hW
    (fun p φ y => hA p y φ) b (fun i => (hb i).1) hli g (fun z hz => hall z hz)
  intro i
  exact congrFun hc i

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RegTie
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

section Comparison₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]

def SecTieK {t : SAB H (Sp V)} {tK : SAB H (Sp (FractionRing V))} (m : SABMap tK t (Out.jK V))
    (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)) (k : ℕ)
    (F : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V))))))
    (σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ)))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ tK.G.left) (zp : Z ⟶ (𝟙_ (Over (Sp (FractionRing V))) ⊗ tK.G).left),
    zp ≫ (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left = r →
    ∀ (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) (J' : (Z ⟶ tK.G.left) → tK.PP.L.ι),
      Good t.PP.L z J → Good tK.PP.L z J' →
      sval σ (r ≫ m.φ) z J = ((gv w r z (fun _ => J (r ≫ m.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval F zp z J'

end Comparison₂

def RegUnifSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ θ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((1 : ℕ) : ℤ))),
      (∀ σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((1 : ℕ) : ℤ))),
        ∃! a : V, ∀ i, σ.f i = resG t.G.left le_top ((t.G.hom).appTop.hom (toΓ V a)) * θ.f i) →
    ∀ (M : ℕ), IsUnit (M : V) →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (θK : LB.Sec (LPow tK.G tK.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))), SecTieK m w 1 θK θ →
    ∀ (t₀ : 𝟙_ (Over (Sp (FractionRing V))) ⟶ tK.G)
      (F : LB.Sec (LPow tK.G tK.PP.L ((M : ℤ) ^ 2) (𝟙_ (Over (Sp (FractionRing V)))))),
      IsVtOver tK.G tK.PP M (fun u => u ^ (M ^ 2) = 1) (zCast tK.G (Nat.cast_one) θK) t₀ F →
      ∃ σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((M ^ 2 : ℕ) : ℤ))),
        SecTieK m w (M ^ 2) (zCast tK.G (natCast_sq M) F) σ

section Move

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def TieMv {X₀ : Scheme.{0}} {t₀ : SAB H X₀} {K : Type} [Field K] {x : Sp K ⟶ X₀} {tK : SAB H (Sp K)}
    (m1 : SABMap tK t₀ x) (w1 : LB.Iso tK.PP.L (t₀.PP.L.pull m1.φ)) (k : ℕ)
    (F : LB.Sec (LPow t₀.G t₀.PP.L (k : ℤ) (Over.mk x)))
    (FK : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp K))))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ tK.G.left) (zp : Z ⟶ (Over.mk x ⊗ t₀.G).left)
    (zp' : Z ⟶ (𝟙_ (Over (Sp K)) ⊗ tK.G).left),
    zp ≫ (snd (Over.mk x) t₀.G).left = r ≫ m1.φ → zp ≫ (fst (Over.mk x) t₀.G).left = r ≫ tK.G.hom →
    zp' ≫ (snd (𝟙_ (Over (Sp K))) tK.G).left = r →
    ∀ (z : Z) (J : (Z ⟶ t₀.G.left) → t₀.PP.L.ι) (J' : (Z ⟶ tK.G.left) → tK.PP.L.ι),
      Good t₀.PP.L z J → Good tK.PP.L z J' →
      sval F zp z J = ((gv w1 r z (fun _ => J (r ≫ m1.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval FK zp' z J'

end Move

def VtMoveSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X₀ : Scheme.{0}) (t₀ : SAB H X₀)
    (K : Type) [Field K] (x : Sp K ⟶ X₀) (tK : SAB H (Sp K)) (m1 : SABMap tK t₀ x)
    (w1 : LB.Iso tK.PP.L (t₀.PP.L.pull m1.φ)), RigIso m1 w1 →
    ∀ (N : ℕ) (ok : (Over.mk x ⟶ t₀.G) → Prop) (s : LB.Sec (LPow t₀.G t₀.PP.L 1 (Over.mk x)))
      (tt : Over.mk x ⟶ t₀.G) (F : LB.Sec (LPow t₀.G t₀.PP.L ((N : ℤ) ^ 2) (Over.mk x))),
      IsVtOver t₀.G t₀.PP N ok s tt F → (∀ u, ok u → u ^ (N ^ 2) = 1) →
    ∀ sK : LB.Sec (LPow tK.G tK.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp K)))),
      TieMv m1 w1 1 (zCast t₀.G Nat.cast_one.symm s) sK →
      ∃ (ttK : 𝟙_ (Over (Sp K)) ⟶ tK.G) (FK : LB.Sec (LPow tK.G tK.PP.L ((N : ℤ) ^ 2) (𝟙_ (Over (Sp K))))),
        IsVtOver tK.G tK.PP N (fun u => u ^ (N ^ 2) = 1) (zCast tK.G Nat.cast_one sK) ttK FK ∧
        TieMv m1 w1 (N ^ 2) (zCast t₀.G (natCast_sq N) F) (zCast tK.G (natCast_sq N) FK)

def ThetaTieSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (Tc : CDVR) (io : c.F →+* Tc.Fr) (y : letI := io.toAlgebra; FrPt Xo c Tc.Fr)
    (I : IntData Xo c Tc io y),
    letI := io.toAlgebra
    ∃ θ : LB.Sec (LB.LinComb I.G.PP.L (K := Fin 1) (fun _ => 𝟙 I.G.G.left) (fun _ => ((1 : ℕ) : ℤ))),
      (∀ σ : LB.Sec (LB.LinComb I.G.PP.L (K := Fin 1) (fun _ => 𝟙 I.G.G.left) (fun _ => ((1 : ℕ) : ℤ))),
        ∃! a : Tc.V, ∀ i, σ.f i = resG I.G.G.left le_top ((I.G.G.hom).appTop.hom (toΓ Tc.V a)) * θ.f i) ∧
      ∃ θK : LB.Sec (LPow I.t'.G I.t'.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp Tc.Fr)))),
        TieMv I.m1 I.w1 1 (zCast Xo.univ.t.G Nat.cast_one.symm y.s) θK ∧ SecTieK I.m2 I.w2 1 θK θ

section Restrict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}

def gsec (G : Over S) : G.left ⟶ (𝟙_ (Over S) ⊗ G).left := (lift (toUnit G) (𝟙 G)).left

theorem gsec_snd (G : Over S) : gsec G ≫ (snd (𝟙_ (Over S)) G).left = 𝟙 _ := by
  rw [gsec, ← Over.comp_left, lift_snd, Over.id_left]

theorem exists_restrict (t : SAB H S) (a : ℤ) (F : LB.Sec (LPow t.G t.PP.L a (𝟙_ (Over S)))) :
    ∃ σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => a)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
        sval σ r z J = sval F (r ≫ gsec t.G) z J := by
  have hF : FormEq (Sum.elim (fun k => gsec t.G ≫ (fun _ : Fin 1 => (snd (𝟙_ (Over S)) t.G).left) k)
      (PEmpty.elim : PEmpty → _)) (Sum.elim (fun _ : Fin 1 => a) (PEmpty.elim : PEmpty → ℤ))
      (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => a) := by
    intro U _ h
    have e := gsec_snd t.G
    simp only [Fintype.prod_sum_type, Sum.elim_inl, e, Finset.univ_eq_empty, Finset.prod_empty, _root_.mul_one]
  obtain ⟨σ, hσ⟩ := exists_sec t.PP.isLB hF
    (pullMulSec (F : LB.Sec (LB.LinComb t.PP.L (fun _ : Fin 1 => (snd (𝟙_ (Over S)) t.G).left) (fun _ => a)))
      (gsec t.G) (LB.oneGen t.PP.L) (fun _ _ => by dsimp only [LB.oneGen]; erw [map_one, map_one, _root_.mul_one]; simp [LB.LinComb]; rfl))
  refine ⟨σ, fun Z r z J hJ => ?_⟩
  refine (hσ Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ r z hJ).trans ?_)
  rw [val_one, Units.val_one, _root_.mul_one]

end Restrict

theorem isUnit_natCast_of_overLa {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} (Tc : CDVR)
    {io : K →+* Tc.Fr} {e : ℕ} (ho : OverLa la Tc.V io e) {M : ℕ} (hM : (M : 𝓞 K) ∉ la.asIdeal) :
    IsUnit (M : Tc.V) := by
  have h1 : la.valuation K (M : K) = 1 := by
    have e1 : (M : K) = algebraMap (𝓞 K) K (M : 𝓞 K) := by simp
    rw [e1, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hM
  have h2 := ho.2 (M : K)
  rw [vLa, h1, WithZero.log_one, neg_zero, mul_zero, map_natCast] at h2
  have e2 : ((M : ℕ) : Tc.Fr) = algebraMap Tc.V Tc.Fr (M : Tc.V) := by simp
  rw [e2, vV, valV, HeightOneSpectrum.valuation_of_algebraMap, neg_eq_zero] at h2
  have hne : (IsDiscreteValuationRing.maximalIdeal Tc.V).intValuation (M : Tc.V) ≠ 0 := by
    refine HeightOneSpectrum.intValuation_ne_zero _ _ ?_
    intro h0
    apply hM
    have : M = 0 := by exact_mod_cast h0
    rw [this, Nat.cast_zero]; exact la.asIdeal.zero_mem
  have h3 : (IsDiscreteValuationRing.maximalIdeal Tc.V).intValuation (M : Tc.V) = 1 := by
    rw [← WithZero.exp_log hne, h2, WithZero.exp_zero]
  rw [HeightOneSpectrum.intValuation_eq_one_iff] at h3
  by_contra hu
  exact h3 ((IsLocalRing.mem_maximalIdeal _).2 hu)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThValDescIn
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def FrBCFieldSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (K : Type) [Field K] [Algebra c.F K]
    (ψ : S →ₐ[c.F] K), ∃ z : FrPt Xo c K, FrMap ψ y z

def ThExprBCSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab →
    ∀ (S S' : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] [CommRing S'] [Algebra c.F S'] [Algebra ℚ S']
      (ψ : S →ₐ[c.F] S') (y : FrPt Xo c S) (y' : FrPt Xo c S'), FrMap ψ y y' →
      ∀ (h : ptO Xo y'.x ⟶ ptO Xo y.x), h.left = spMap ψ.toRingHom →
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      ∀ (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x)))
        (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y'.x))),
        (∀ b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _)
          (F b) (F' b)) →
        ψ (thExpr Xo c nab y P F) = thExpr Xo c nab y' P F'

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

