import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThValFinExtSplit
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0002
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.VtMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtPull

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBCFrameR
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}

theorem genBC_frameR (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) {S K : Type} [CommRing S]
    [CommRing K] (x : Sp S ⟶ Xo.X) (ρ : S →+* K) (s0 : LB.Sec (PPx x))
    (hgen : ∀ s' : LB.Sec (PPx x), ∃! a : S, ∀ i, s'.f i = scal x a i * s0.f i) (s'' : LB.Sec (PPx (spMap ρ ≫ x))) :
    ∃! a : K, ∀ i, s''.f i = scal (spMap ρ ≫ x) a i * (secCP (cpS ρ x) s0).f i := by
  obtain ⟨a, ha, hu⟩ := gen_baseChangeR hS hT Xo.univ (mA x) (θA x s0) (hθ_of x s0 hgen) ρ (mB ρ x)
    (w := idIso ((tA x).PP.L.pull (mB ρ x).φ)) (σB ρ x s0) (hσ_of ρ x s0) (secCP (cpU' ρ x) s'')
  exact ⟨a, key_fwd ρ x s0 s'' a ha, fun a' ha' => hu a' (key_bwd ρ x s0 s'' a' ha')⟩

theorem bcGenR (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) (c : Coeff l) :
    BcGenRSt Xo c := fun _ _ _ _ ψ y =>
  ⟨secCP (cpS ψ.toRingHom y.x) y.s, fun _ _ => rfl, genBC_frameR hS hT y.x ψ.toRingHom y.s y.gen⟩

theorem bcLieAll (c : Coeff l) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (τ : E →+* ℂ) (w : Sp (DualNumber T) ⟶ Xo.univ.t.G.left)
    (hw : IsTanAt (spMap ψ.toRingHom ≫ y.x) w) (he : IsEigAt c τ w) : ∃! a : Fin (Dw.mult τ) → T,
      IsCombAt (spMap ψ.toRingHom ≫ y.x) (fun i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i) a w := by
  let x := spMap ψ.toRingHom ≫ y.x
  have tn : ∀ τ i, IsTanAt x (spMap (dualMap ψ.toRingHom) ≫ y.u τ i) := fun τ i => tan_bc ψ.toRingHom (y.tan τ i)
  refine eig_basis_of_full (fun τ i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i) tn (fun τ i => eig_bc ψ τ (y.eig τ i))
    (fun m => ?_) τ w hw he
  have h := hS (Xo := Xo) x
  choose u' hu' using fun i => push_surj h (tv (tvOf (tn (eB Dw i).1 (eB Dw i).2)))
  have := Xo.univ.t.semi.smooth
  have : Smooth ((Over.pullback y.x).obj Xo.univ.t.G).hom := show Smooth (pullback.snd _ _) from inferInstance
  have gp := Chart.isGrpPullback_factor y.x (spMap ψ.toRingHom) h
  have bs : IsLieBasis u' := Chart.frameLieBCR _ (uS_basis y) ψ.toRingHom gp (fun a b v hv => push_inj h (by
      have := smT_add x _ ((isTangent_iff h v).1 ((Chart.isTan_iff _).1 hv)) a b
      rw [← push_scK h, ← push_scK h, ← push_scK h, ← map_mul] at this
      exact this)) (fun i => (isTangent_iff h _).2 (by rw [hu']; exact tv_mem _)) fun i => by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc]
      exact (congrArg (fun q => q.left) (hu' i)).trans (congrArg (_ ≫ ·) (congrArg (fun q => q.left) (push_uS y i)).symm)
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Over.w (u' i), Category.assoc]
      refine Eq.trans ?_ (congrArg (_ ≫ ·) (Over.w (uS y i)).symm)
      exact (spMap_comp_spMap _ _).trans ((congrArg spMap (dualMap_comp_alg _).symm).trans (spMap_comp_spMap _ _).symm)
  obtain ⟨p, hp⟩ := push_surj h (tv m)
  have key : ∀ a, IsLieComb a u' p ↔ m = ∑ k, a ((eB Dw).symm k) • tvOf (tn k.1 k.2) := fun a => by
    rw [isLieComb_iff h, hp, ← (eB Dw).sum_comp]
    simp only [Equiv.symm_apply_apply, hu']
    exact ⟨fun q => tanM_ext (q.trans (by rw [tv_sum]; rfl)), fun q => (congrArg tv q).trans (by rw [tv_sum]; rfl)⟩
  obtain ⟨a, ha, hu⟩ := bs.2 p ((isTangent_iff h p).2 (by rw [hp]; exact tv_mem m))
  refine ⟨fun k => a ((eB Dw).symm k), (key a).1 ha, fun b hb => ?_⟩
  have := hu (fun i => b (eB Dw i)) ((key _).2 (by simpa using hb))
  funext k; rw [← this]; simp

theorem bcLieR (c : Coeff l) : BcLieRSt Xo c := fun _ _ _ _ ψ y => bcLieAll c ψ y

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HarmonicValueSplitOfExtension
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

def HarmonicValueAfterExtension : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)]
    (nab : NabV (T.Q.Xo j) T.Q.c), IsNab (T.Q.Xo j) T.Q.c nab →
    ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
    P ∈ harmA T.Q.c (wtA w) w.n → ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
      ((T.Q.l.M : 𝓞 T.Q.c.F) ∉ la.asIdeal) →
      ∃ (T' : CDVR) (iT : Tc.Fr →+* T'.Fr) (e' : ℕ) (yI' : IntFr (T.Q.Xo j) T.Q.c T' (iT.comp io)),
        OverLa la T'.V (iT.comp io) e' ∧ yI'.IsAlg ∧
        letI := (iT.comp io).toAlgebra
        ∃ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' (iT.comp io) yI')
          (F : Fin w.n → LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L ((T.Q.l.M : ℤ) ^ 2)
            (ptO (T.Q.Xo j) yI'.1.x)))
          (g : Fin w.n → Germ.PS T'.Fr 1 (chD C.ch)),
          (∀ b, IsVtOver (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP T.Q.l.M (KilledBy (T.Q.Xo j) (T.Q.l.Mb ^ 2))
            yI'.1.s (levPt (T.Q.Xo j) yI'.1.x (x b)) (F b)) ∧
          (∀ b, IsGerm yI'.1 C.ch.d C.ch.x C.ch.B.A.act C.ch.e C.ch.wP (T.Q.l.M ^ 2)
            (zCast (T.Q.Xo j).univ.t.G (natCast_sq T.Q.l.M) (F b)) (g b)) ∧
          (∀ b, IsIntPS T' (g b)) ∧
          iT (evI yI f) = (iT.comp io) (((T.Q.l.M : T.Q.c.F) ^ P.totalDegree)⁻¹) *
            ∑ mo ∈ (P.map (iT.comp io)).support, (P.map (iT.comp io)).coeff mo *
              ∏ b, C.ch.B.nabVal T'.Fr C.ch.h T.Q.H.w0 (T.Q.l.M ^ 2) (g b) C.ch.uvec
                (MvPolynomial.monomial (colOf mo b) 1)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeI
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem dualMapR_eq {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') :
    ReciprocityTheory.ChartRestriction.G.Chart.dualMapR φ = dualMap φ := RingHom.ext fun _ => rfl

section BC

variable {S T : Type} [CommRing S] [Algebra c.F S] [Field T] [Algebra c.F T] (ψ : S →ₐ[c.F] T) (y : FrPt Xo c S)

theorem hw0 (i : Fin (Fintype.card (IxB Dw))) :
    (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ψ.toRingHom) ≫ (uS y i).left) ≫
      ((Over.pullback y.x).obj Xo.univ.t.G).hom = (epsR T).hom ≫ spMap ψ.toRingHom := by
  rw [Category.assoc, Over.w (uS y i)]
  show spMap _ ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap _
  rw [spMap_comp_spMap, spMap_comp_spMap, dualMapR_eq, dualMap_comp_alg]

def uT (i : Fin (Fintype.card (IxB Dw))) :
    epsR T ⟶ (Over.pullback (spMap ψ.toRingHom)).obj ((Over.pullback y.x).obj Xo.univ.t.G) :=
  Over.homMk (pullback.lift (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ψ.toRingHom) ≫ (uS y i).left) (epsR T).hom
    (hw0 ψ y i)) (pullback.lift_snd _ _ _)

end BC

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.VtMoveSym
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.VtMove

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

section Transl

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S}

theorem translPt_one' : translPt A (1 : T ⟶ A) = snd T A := by
  rw [translPt_eq, MonObj.comp_one, _root_.one_mul]

theorem transl_translPt (y x : T ⟶ A) :
    (translT A y).left ≫ (translPt A x).left = (translPt A (y * x)).left := by
  rw [← Over.comp_left]
  congr 1
  simp only [translPt_eq, translT, MonObj.comp_mul, lift_snd, lift_fst_assoc]
  rw [_root_.mul_left_comm, ← _root_.mul_assoc]

theorem transl_pow_succ (x : T ⟶ A) (j : ℕ) :
    (translT A (x ^ j)).left ≫ (translPt A x).left = (translPt A (x ^ (j + 1))).left := by
  rw [transl_translPt, pow_succ]

theorem transl_inv_translPt (x : T ⟶ A) : (translT A x⁻¹).left ≫ (translPt A x).left = (snd T A).left := by
  rw [transl_translPt, inv_mul_cancel, translPt_one']

theorem negT_snd' : (negT A T).left ≫ (snd T A).left = (snd T A ≫ (GrpObj.inv : A ⟶ A)).left := by
  rw [← Over.comp_left, negT, lift_snd]

theorem negT_translPt (x : T ⟶ A) :
    (negT A T).left ≫ (translPt A x).left = (translT A x⁻¹).left ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  have e1 : negT A T ≫ translPt A x = (fst T A ≫ x) * (snd T A)⁻¹ := by
    rw [translPt_eq, MonObj.comp_mul, negT, lift_fst_assoc, lift_snd]
    rfl
  have e2 : translT A x⁻¹ ≫ snd T A ≫ (GrpObj.inv : A ⟶ A) = (fst T A ≫ x) * (snd T A)⁻¹ := by
    rw [← Category.assoc, translT, lift_snd, translPt_eq]
    show ((fst T A ≫ x⁻¹) * snd T A)⁻¹ = _
    rw [mul_inv, GrpObj.comp_inv, inv_inv]
  rw [e1, e2]

end Transl

section Move

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] [IsCommMonObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left}

include hp hτ in
theorem inv_rel {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : x.left ≫ φ = τ ≫ x₀.left) :
    (x⁻¹).left ≫ φ = τ ≫ (x₀⁻¹).left := by
  show (x ≫ GrpObj.inv).left ≫ φ = τ ≫ (x₀ ≫ GrpObj.inv).left
  rw [push_inv hp x, push_eq hp τ hτ hx]
  try rfl

theorem symLift_move (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen) {k : ℤ} {n : ℕ}
    {x₀ : T₀ ⟶ G} {θ₀ : ThetaGrp G L₀ k T₀} (h₀ : SymLift G L₀ k n x₀ θ₀) (hn : x₀ ^ n = 1) {x : T ⟶ A}
    (hx : x.left ≫ φ = τ ≫ x₀.left) :
    ∃ θ : ThetaGrp A L₁ k T, SymLift A L₁ k n x θ ∧
      PMaps w ![(snd T A).left, (translPt A θ.pt).left] ![(snd T₀ G).left, (translPt G θ₀.pt).left] ![k, -k]
        θ.φ θ₀.φ (psiO hp τ hτ).left := by
  obtain rfl := h₀.pt_eq
  obtain ⟨θ, rfl, hm⟩ := exists_theta_move hp τ hτ hL₀ hL₁ w hw k x θ₀ hx.symm
  have hxn : θ.pt ^ n = 1 := pow_eq_one hp τ hτ hx hn
  have hc : ∀ i, (![(snd T A).left, (translPt A θ.pt).left] : Fin 2 → _) i ≫ φ =
      (psiO hp τ hτ).left ≫ (![(snd T₀ G).left, (translPt G θ₀.pt).left] : Fin 2 → _) i := fun i => by
    fin_cases i
    · exact (psi_snd hp τ hτ).symm
    · exact (psi_tr hp τ hτ θ.pt θ₀.pt hx.symm).symm
  obtain ⟨nu₀, gnu₀, cnu₀⟩ := h₀.sym
  have hcn : ∀ i, (![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] : Fin 2 → _) i ≫ φ =
      (psiO hp τ hτ).left ≫ (![(snd T₀ G).left, (snd T₀ G ≫ (GrpObj.inv : G ⟶ G)).left] : Fin 2 → _) i := fun i => by
    fin_cases i
    · exact (psi_snd hp τ hτ).symm
    · exact snd_inv_push hp τ hτ
  obtain ⟨nu, gnu, hmn⟩ := exists_gen_move hL₀ hL₁ w ((isGen_iff w).1 hw) _ _ ![k, -k] (psiO hp τ hτ).left hcn nu₀ gnu₀
  refine ⟨θ, ⟨rfl, ?_, nu, gnu, ?_⟩, hm⟩
  · refine corr_of_val hL₁ fun y J hJ => ?_
    choose J₀ hJ₀ using fun χ : (T ⊗ A).left ⟶ G.left => exists_chart hL₀ (χ y)
    have hG : Good L₀ y J₀ := hJ₀
    obtain ⟨g, hg⟩ : ∃ g : ℕ → ((T ⊗ A).left.presheaf.stalk y)ˣ, ∀ j, g j =
        gw w (translPt A (θ.pt ^ j)).left y (J₀ ((translPt A (θ.pt ^ j)).left ≫ φ)) (J (translPt A (θ.pt ^ j)).left) ^ k :=
      ⟨_, fun _ => rfl⟩
    have key : ∀ j : ℕ, val θ₀.φ ((psiO hp τ hτ).left ≫ (translT G (θ₀.pt ^ j)).left) y J₀ =
        g j / g (j + 1) * val θ.φ (𝟙 _ ≫ (translT A (θ.pt ^ j)).left) y J := fun j => by
      rw [← psi_transl hp τ hτ _ _ (pow_rel hp τ hτ hx j).symm, val_pmaps w hc hm _ y J₀ J hG hJ, Category.id_comp]
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [transl_snd, transl_pow_succ, zpow_neg, div_eq_mul_inv, hg, hg]
    have c := val_corr hG h₀.pow_eq (psiO hp τ hτ).left
    rw [val_powGenT θ₀ n _ y hG, val_one] at c
    rw [val_powGenT θ n _ y hJ, val_one]
    rw [Fin.prod_univ_eq_prod_range (fun j => val θ₀.φ ((psiO hp τ hτ).left ≫ (translT G (θ₀.pt ^ j)).left) y J₀)] at c
    rw [Fin.prod_univ_eq_prod_range (fun j => val θ.φ (𝟙 _ ≫ (translT A (θ.pt ^ j)).left) y J)]
    simp only [key, Finset.prod_mul_distrib, Finset.prod_range_div'] at c
    have gn : g n = g 0 := by rw [hg, hg, hxn, pow_zero]
    rwa [gn, div_self', _root_.one_mul] at c
  · refine corr_of_val hL₁ fun y J hJ => ?_
    choose J₀ hJ₀ using fun χ : (T ⊗ A).left ⟶ G.left => exists_chart hL₀ (χ y)
    have hG : Good L₀ y J₀ := hJ₀
    have c := val_corr hG cnu₀ (psiO hp τ hτ).left
    rw [val_symGen θ₀ nu₀ _ y hG, val_one] at c
    rw [val_symGen θ nu _ y hJ, val_one]
    have v1 := val_pmaps w hc hm (translT A θ.pt⁻¹).left y J₀ J hG hJ
    have v2 := val_pmaps w hcn hmn (𝟙 _) y J₀ J hG hJ
    have v3 := val_pmaps w hc hm (negT A T).left y J₀ J hG hJ
    have v4 := val_pmaps w hcn hmn (translT A θ.pt⁻¹).left y J₀ J hG hJ
    simp only [Category.id_comp] at v2 ⊢
    rw [← psi_transl hp τ hτ θ.pt⁻¹ θ₀.pt⁻¹ (inv_rel hp τ hτ hx).symm, ← negT_push hp τ hτ, v1, v2, v3, v4] at c
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at c
    rw [transl_inv_translPt, negT_snd', negT_translPt] at c
    apply Additive.ofMul.injective
    have b := congrArg Additive.ofMul c
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one, zpow_neg] at b ⊢
    linear_combination (norm := abel) b

end Move

end ReciprocityTheory.ChartRestriction.G.PullbackSections.VtMove
end
end

