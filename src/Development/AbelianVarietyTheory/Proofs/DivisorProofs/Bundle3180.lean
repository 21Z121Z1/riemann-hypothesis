import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2974
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2785
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3139
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2787
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0660
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0798
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0898
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3115
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0121
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2858
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3144
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2823

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothLiftDegreeOneComparisonRelation
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.CrysCmp

theorem exists_compatibleFormsCocycle_deRhamClass {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (c : FirstDeRham s) :
    ∃ (f₀ : Z1 (O (dp0 R) s)) (k₀ : (KK (dp0 R) s).Z1), k₀.1.1 = f₀.1 ∧ H1.mk _ f₀ = c := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  have hb := (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res R ⊥ (dp0 R) X s X (𝟙 X)).1.1.2
  have hfe : ((f.1, fun _ ↦ PUnit.unit) : (Cx.single (KK (dp0 R) s).M0).T1) ∈ (Cx.single (KK (dp0 R) s).M0).Z1 := by
    refine AddMonoidHom.mem_ker.2 (Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)))
    funext T T' T'' φ ψ
    change mp (O (dp0 R) s) ψ (f.1 _ _ φ) - f.1 _ _ (φ ≫ ψ) + f.1 _ _ ψ = 0
    rw [f.2 φ ψ]; abel
  obtain ⟨q, hq⟩ := hb (QuotientAddGroup.mk ⟨_, hfe⟩)
  obtain ⟨k₀, rfl⟩ := QuotientAddGroup.mk_surjective q
  have hq' := QuotientAddGroup.eq.1 ((QuotientAddGroup.map_mk _ _ _ _ k₀).symm.trans hq)
  rw [AddSubgroup.mem_addSubgroupOf] at hq'
  obtain ⟨g, hg⟩ := hq'
  have hk := AddMonoidHom.mem_ker.1 k₀.2
  let f₀ : Z1 (O (dp0 R) s) := ⟨k₀.1.1, fun T T' T'' φ ψ ↦ by
    have := congrFun (congrFun (congrFun (congrFun (congrFun (congrArg Prod.fst hk) T) T') T'') φ) ψ
    change mp (O (dp0 R) s) ψ (k₀.1.1 _ _ φ) - k₀.1.1 _ _ (φ ≫ ψ) + k₀.1.1 _ _ ψ = 0 at this
    change k₀.1.1 _ _ (φ ≫ ψ) = mp (O (dp0 R) s) ψ (k₀.1.1 _ _ φ) + k₀.1.1 _ _ ψ
    linear_combination (norm := abel1) -this⟩
  refine ⟨f₀, k₀, rfl, ?_⟩
  rw [H1.mk_eq_mk]
  refine ⟨-g, ?_⟩
  funext T T' φ
  have := congrFun (congrFun (congrFun (congrArg Prod.fst hg) T) T') φ
  change g T' - mp (O (dp0 R) s) φ (g T) = -(k₀.1.1 T T' φ) + f.1 T T' φ at this
  change -g T' - mp (O (dp0 R) s) φ (-g T) = k₀.1.1 T T' φ - f.1 T T' φ
  rw [map_neg]
  linear_combination (norm := abel1) -this

section Theta

variable {D : Data} (Λ : Lift D) (m : IsMor (dp0 D.R) D.s D.κ D.t (RingHom.id D.R) D.i)

def thAlg (U : AffOp D.X) : Sec D.s U.unop.1 →ₐ[D.R] (m.obj (Λ.L.obj U)).B :=
  { (Λ.e U : Sec D.s U.unop.1 →+* (Λ.L.obj U).B) with commutes' := fun r ↦ (Λ.e U).commutes r }

def theta (U : AffOp D.X) :
    Thick.triv (Sec D.s U.unop.1) (affPt D.s U.unop) (affPt_w D.s U.unop) ⟶ m.obj (Λ.L.obj U) :=
  Thick.trivHom (thAlg Λ m U) (Λ.pt U)

end Theta

theorem key4 {G : Type} [AddCommGroup G] (A B C E : G) (h : A + B = C + E) : E - A = B - C := by
  rw [sub_eq_sub_iff_add_eq_add, add_comm E C, ← h, add_comm]

theorem lift_rel1_pull1_cmp1 : ∀ (D : Data) (Λ : Lift D) (m : IsMor (dp0 D.R) D.s D.κ D.t (RingHom.id D.R) D.i) (c : FirstDeRham D.s), Λ.Rel1 (m.pull1 c) (cmp1 D.s c) := by
  intro D Λ m c
  obtain ⟨f₀, k₀, hk, rfl⟩ := exists_compatibleFormsCocycle_deRhamClass D.s c
  let k := (morMap m).z1 k₀
  let k' := ((KK D.κ D.t).resMap Λ.L).p1 k.1
  have hk' : k' ∈ ((KK D.κ D.t).res Λ.L).Z1 := (((KK D.κ D.t).resMap Λ.L).z1 k).2
  obtain ⟨w, hw, -⟩ := ((GlobalTheory.T.compatibleFormsCochains_eq_deRhamCochains_smoothLift).1 D Λ).1 k'
  have hwZ : w ∈ cechDeRhamTotalCocyclesOne (OAff D.s) := ((((GlobalTheory.T.compatibleFormsCochains_eq_deRhamCochains_smoothLift).1 D Λ).2.2 k' w hw).1.1 hk')
  refine ⟨k, m.coef.pullbackOneCocycle f₀, ⟨w, hwZ⟩, rfl, ?_, ?_, hw⟩

  · rw [comparison_mk, Hyp1.mk_eq_mk]
    refine ⟨fun U ↦ (Λ.e U).symm (ev f₀ (theta Λ m U)), Tot1.ext (fun U V a ↦ ?_) (fun U ↦ ?_)⟩
    · change (Λ.e V).symm (ev f₀ (theta Λ m V)) - Sec.res D.s (leOfHom a.unop) ((Λ.e U).symm (ev f₀ (theta Λ m U))) =
        w.1 U V a - (cmpZZ D.s f₀).1.1 U V a
      apply (Λ.e V).injective
      have h1 : Λ.e V (w.1 U V a) = ev f₀ (m.functor.map (Λ.L.map a)) := by
        refine (hw.1 U V a).symm.trans ?_
        change k₀.1.1 _ _ _ = _
        rw [hk]; rfl
      have h2 := Λ.nat a ((Λ.e U).symm (ev f₀ (theta Λ m U)))
      erw [AlgEquiv.apply_symm_apply] at h2
      have sq := ev_sq f₀ (theta Λ m U) (m.functor.map (Λ.L.map a))
          (Thick.trivHom (hx := affPt_w D.s U.unop) (T := Thick.triv _ _ (affPt_w D.s V.unop))
            (Sec.res D.s (leOfHom a.unop)) (affPt_res D.s (leOfHom a.unop))) (theta Λ m V)
          (by intro c; exact (Λ.nat a c).symm)
      rw [map_sub, map_sub, h1, cmpZZ_f]
      erw [AlgEquiv.apply_symm_apply]
      change _ - Λ.e V (mp (OAff D.s) a _) = _
      rw [h2]
      exact key4 _ _ _ _ sq
    · change KaehlerDifferential.D D.R (Sec D.s U.unop.1) ((Λ.e U).symm (ev f₀ (theta Λ m U))) =
        w.2 U - connForm f₀ (affPt D.s U.unop) (affPt_w D.s U.unop)
      have hrel : rel D.R (Λ.L.obj U).δ = ⊥ :=
        (GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base).2 D.R (Λ.L.obj U).B (Λ.L.obj U).J (Λ.L.obj U).δ D.I D.κ (Λ.L.obj U).dp (Λ.gen U).le
      have inj : ∀ x y : Ω[(Λ.L.obj U).B⁄D.R],
          (Submodule.Quotient.mk x : K1 D.R (Λ.L.obj U).δ) = Submodule.Quotient.mk y → x = y := by
        intro x y h
        rw [Submodule.Quotient.eq] at h
        have h' : ι1 (x - y) ∈ rel D.R (Λ.L.obj U).δ := h
        rw [hrel, Ideal.mem_bot, map_sub, sub_eq_zero] at h'
        exact (ExteriorAlgebra.ι_inj _ _ _).1 h'
      have hk0 := AddMonoidHom.mem_ker.1 k₀.2
      have hcoc := congrFun (congrFun (congrFun (congrArg (fun x ↦ x.2.1) hk0) _) _) (theta Λ m U)
      have hc := GlobalTheory.T.compatibleFormsCocycle_form_eq_connectionForm D.R D.X D.s k₀ f₀ hk (Sec D.s U.unop.1) (affPt D.s U.unop) (affPt_w D.s U.unop)
      have e1 : k₀.1.2 (m.obj (Λ.L.obj U)) = km1 (SemiHom.of_algHom (theta Λ m U).φ) (theta Λ m U).dp (k₀.1.2 _) +
          kd0 D.R (m.obj (Λ.L.obj U)).δ (ev f₀ (theta Λ m U)) := by
        have : k₀.1.2 (m.obj (Λ.L.obj U)) - km1 (SemiHom.of_algHom (theta Λ m U).φ) (theta Λ m U).dp (k₀.1.2 _) -
            kd0 D.R (m.obj (Λ.L.obj U)).δ (k₀.1.1 _ _ (theta Λ m U)) = 0 := hcoc
        rw [hk] at this
        exact sub_eq_zero.1 ((sub_sub _ _ _).symm.trans this)
      rw [hc, divPowerCompatOneFormMap_mk, divPowerCompatFunctionDifferential_apply, ← Submodule.Quotient.mk_add] at e1
      have e2 := hw.2 U
      change km1 (morSemi m (Λ.L.obj U)) (morDP m (Λ.L.obj U)) (k₀.1.2 (m.obj (Λ.L.obj U))) = _ at e2
      rw [e1] at e2
      erw [divPowerCompatOneFormMap_mk] at e2
      have e3 := inj _ _ e2
      have e3' : (Λ.semi U).m1 (w.2 U) = (Λ.semi U).m1 (connForm f₀ (affPt D.s U.unop) (affPt_w D.s U.unop)) +
          KaehlerDifferential.D D.R (Λ.L.obj U).B (ev f₀ (theta Λ m U)) := by
        rw [← e3, map_add]
        congr 1
        · exact SemiHom.oneFormMap_comp_oneFormMap _ _ _ (fun _ ↦ rfl) _
        · exact SemiHom.m1_D _ _
      have semiInv : SemiHom (RingHom.id D.R) ((Λ.e U).symm : (Λ.L.obj U).B →+* Sec D.s U.unop.1) :=
        fun r b ↦ map_smul (Λ.e U).symm r b
      have linv : ∀ ω, semiInv.m1 ((Λ.semi U).m1 ω) = ω := fun ω ↦
        (SemiHom.oneFormMap_comp_oneFormMap (Λ.semi U) semiInv (SemiHom.of_algHom (AlgHom.id D.R (Sec D.s U.unop.1)))
          (fun b ↦ (Λ.e U).symm_apply_apply b) ω).trans (SemiHom.oneFormMap_eq_self_of_id _ (fun _ ↦ rfl) ω)
      have e5 := congrArg semiInv.m1 e3'
      rw [map_add, linv, linv] at e5
      rw [e5, add_sub_cancel_left]
      exact (SemiHom.m1_D semiInv _).symm
  · funext T T' φ
    change k₀.1.1 _ _ (m.functor.map φ) = f₀.1 _ _ (m.functor.map φ)
    rw [hk]

end GlobalTheory.PDForm.CrysCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisFrameMapStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_basis_frame_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (R : Type) [CommRing R] [IsDomain R] (ξ : Sp R ⟶ Y.X) (g : ℕ)
    (e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)), IsTanBasis Y.t ξ e →
    ∀ (P' : GlobalTheory.HTMap.FP Y.t ξ (p ^ n)) (κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ) (b : P'.Bˣ), P'.Gl κ b →
    ∀ x0 : R →+* 𝓞_ℂ_[p], P'.Full ((IsLocalRing.maximalIdeal 𝓞_ℂ_[p]).comap x0) →
    ∀ (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left),
      PtOn Y (spMap x0 ≫ ξ) yy P π ψ → GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.LevelReduction P → ∀ tt : P.T,
      (∀ (β : P'.B →+* 𝓞_ℂ_[p]) (w : Sp 𝓞_ℂ_[p] ⟶ Y.t.G.left), P'.At x0 w β →
        ∀ z : GlobalTheory.ChTor.Pts P.A.A, z.left ≫ P.gen ≫ π = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ w →
          algebraMap 𝓞_ℂ_[p] ℂ_[p] (β b) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p])) →
    ∀ hvec : Fin g → 𝓞_ℂ_[p],
      (∀ (k : Fin g) (β : P'.B →+* DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})),
        P'.At ((algebraMap 𝓞_ℂ_[p] (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))).comp x0)
          (spMap (dualMap (Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))) ≫ spMap (dualMap x0) ≫ e k) β →
        (β b).snd = Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) (hvec k)) →
    ∀ (k : Fin g) (x : LieG P.Gt), ITie P π x (spMap (dualMap x0) ≫ e k) →
      hvec k + (P.al₀ tt).1 x ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n} := by
  first | exact @GlobalTheory.FinPartAt.levelHT_at_point | exact GlobalTheory.FinPartAt.levelHT_at_point | (intros; apply GlobalTheory.FinPartAt.levelHT_at_point <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTorsionCount
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.HtGen.PointDet

attribute [local instance] Over.cartesianMonoidalCategory

theorem pairDet_eq_sum {C J : Type} [CommRing C] {g m k : ℕ} (h : J → Fin g → C) (a : Fin m → Fin g → C)
    (hk : k ≤ m) (σ : Fin k → J) :
    pairDet h a hk σ = ∑ s : Fin k → Fin g, (∏ i, h (σ i) (s i)) * minor a hk s := by
  classical
  have hM : (Matrix.of fun r l : Fin k => ∑ i, h (σ r) i * a (Fin.castLE hk l) i) =
      fun r => ∑ i, h (σ r) i • (fun l : Fin k => a (Fin.castLE hk l) i) := by
    ext r l; simp [Finset.sum_apply]
  unfold pairDet
  rw [hM]
  change Matrix.detRowAlternating.toMultilinearMap _ = _
  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  congr 1
  unfold minor
  rw [← Matrix.det_transpose]
  rfl

theorem sum_extend {C : Type} [CommRing C] {m k : ℕ} (hk : k ≤ m) (cf : Fin k → C) (f : Fin m → C) :
    ∑ l', (fun l' : Fin m => if hl : (l' : ℕ) < k then cf ⟨l', hl⟩ else 0) l' * f l' =
      ∑ l : Fin k, cf l * f (Fin.castLE hk l) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _ (fun l' hl' => ?_) (fun l => ?_)
  · have : ¬ (l' : ℕ) < k := fun hl => hl' ⟨⟨l', hl⟩, Fin.ext rfl⟩
    simp [this]
  · simp

theorem sum_comb_extend {C : Type} [CommRing C] {g m k : ℕ} (hk : k ≤ m) (cf : Fin k → C) (hh : Fin g → C)
    (a : Fin m → Fin g → C) :
    ∑ i, hh i * (∑ l', (fun l' : Fin m => if hl : (l' : ℕ) < k then cf ⟨l', hl⟩ else 0) l' • a l') i =
      ∑ l : Fin k, cf l * ∑ i, hh i * a (Fin.castLE hk l) i := by
  rw [← sum_extend hk cf (fun l' => ∑ i, hh i * a l' i)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l' _ => Finset.sum_congr rfl fun i _ => by ring

theorem pairDet_htLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (p : ℕ) [Fact p.Prime] (x : Sp ↥(intO ℂ_[p]) ⟶ X) (g g' : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)) (e' : Fin g' → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)), IsTanBasis t x e → IsTanBasis t x e' → ∀ (N : ℕ) (c : Fin N → TorsChar t x (p ^ 2)) (h : Fin N → Fin g → ↥(intO ℂ_[p])) (h' : Fin N → Fin g' → ↥(intO ℂ_[p])), (∀ c' : TorsChar t x (p ^ 2), ∃ j, Agree c' (c j)) → (∀ j, DlogIs t p 2 (c j) e (h j)) → (∀ j, DlogIs t p 2 (c j) e' (h' j)) → ∀ (m k : ℕ) (hk : k ≤ m) (u : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (a : Fin m → Fin g → ℂ_[p]) (a' : Fin m → Fin g' → ℂ_[p]), LinearIndependent ℂ_[p] a → (∀ l, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) (a l) (u l)) → (∀ l, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e' i) (a' l) (u l)) → ∀ ν : ℝ, ν = ∏ l : Fin k, GlobalTheory.ShFam.Pad.grNorm t (spMap (intO ℂ_[p]).subtype ≫ x) (latHT t p (spMap (intO ℂ_[p]).subtype ≫ x)) u (Fin.castLE hk l) → (∀ l, 0 < GlobalTheory.ShFam.Pad.grNorm t (spMap (intO ℂ_[p]).subtype ≫ x) (latHT t p (spMap (intO ℂ_[p]).subtype ≫ x)) u l) ∧ (∀ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ‖ ≤ ν) ∧ (∃ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ‖ = ν) ∧ ∀ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ - pairDet (fun j i => (h' j i : ℂ_[p])) a' hk σ‖ < ν := by
  intro E _ _ _ H X _ t hX p _ x g g' e e' he he' N c h h' hall hdl hdl' m k hk u a a' ha hu hu' ν hν0
  set xC := spMap (intO ℂ_[p]).subtype ≫ x with hxC
  have heC := GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t (intO ℂ_[p]).subtype he
  have hlat := fun b w hw => GlobalTheory.T.tangent_basis_torsion_chars E H X t hX p x g e he N c h hall hdl b w hw
  have hut : ∀ l, IsTanAtG t xC (u l) := fun l => GlobalTheory.LineNorm.Chart.comb_tan heC.1 (hu l)
  have hgr := fun l => GlobalTheory.LineNorm.WedgeMax.grNorm_eq t heC.1
    (P := fun b => ∀ j, ‖∑ i, (h j i : ℂ_[p]) * b i‖ ≤ 1) (fun b w hw => (hlat b w hw).1) hu l
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hker : ∀ cc : Fin g → ℂ_[p], (∀ j, ∑ i, (h j i : ℂ_[p]) * cc i = 0) → cc = 0 := by
    intro cc hcc
    by_contra hne
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    have hi' : cc i ≠ 0 := by simpa using hi
    obtain ⟨y, hy⟩ := NormedField.exists_one_lt_norm ℂ_[p]
    obtain ⟨w, -, hw⟩ := GlobalTheory.LineNorm.WedgeMax.exists_comb t heC.1 ((y / ((p : ℂ_[p]) * cc i)) • cc)
    have hmem := (hlat _ w hw).1.2 fun j => by
      have : ∑ i', (h j i' : ℂ_[p]) * ((y / ((p : ℂ_[p]) * cc i)) • cc) i' =
          (y / ((p : ℂ_[p]) * cc i)) * ∑ i', (h j i' : ℂ_[p]) * cc i' := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [this, hcc j]; simp
    have h1 := (hlat _ w hw).2 hmem i
    have : (p : ℂ_[p]) * ((y / ((p : ℂ_[p]) * cc i)) • cc) i = y := by
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
      try ring
    rw [this] at h1
    linarith
  obtain ⟨hpos, hprod⟩ := GlobalTheory.T.successive_minima_positive_norms ℂ_[p] g (Fin N) (fun j i => (h j i : ℂ_[p])) hker m a ha _ hgr
  have hν : ν = ⨆ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ‖ := by
    rw [hν0, hprod k hk]
    congr 1
    ext σ
    rw [pairDet_eq_sum]
  have hνpos : 0 < ν := hν0 ▸ Finset.prod_pos fun l _ => hpos _
  have hne : Nonempty (Fin k → Fin N) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    rw [Real.iSup_of_isEmpty] at hν
    linarith
  have hle : ∀ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ‖ ≤ ν := fun σ =>
    hν ▸ le_ciSup (f := fun σ => ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ‖) (Finite.bddAbove_range _) σ
  have hex : ∃ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ‖ = ν := hν ▸ exists_eq_ciSup_of_finite
  refine ⟨hpos, hle, hex, fun σ => ?_⟩
  have hclose : ∀ cf : Fin k → ℂ_[p], (∀ j, ‖∑ l, cf l * ∑ i, (h j i : ℂ_[p]) * a (Fin.castLE hk l) i‖ ≤ 1) →
      ∀ j, ‖∑ l, cf l * ((∑ i, (h j i : ℂ_[p]) * a (Fin.castLE hk l) i) -
        ∑ i, (h' j i : ℂ_[p]) * a' (Fin.castLE hk l) i)‖ < 1 := by
    intro cf hcf j
    obtain ⟨w, -, hw⟩ := GlobalTheory.LineNorm.WedgeMax.exists_comb t hut
      (fun l' : Fin m => if hl : (l' : ℕ) < k then cf ⟨l', hl⟩ else 0)
    have hwe := GlobalTheory.LineNorm.Chart.comb_comb heC.1 hu hw
    have hwe' := GlobalTheory.LineNorm.Chart.comb_comb (GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t (intO ℂ_[p]).subtype he').1 hu' hw
    have hmem := (hlat _ w hwe).1.2 fun j' => by
      rw [sum_comb_extend]; exact hcf j'
    have h1 := GlobalTheory.T.tangent_basis_change_torsion E H X t hX p x g g' e e' he he' (c j) (h j) (h' j) (hdl j) (hdl' j) _ _ w hwe hwe' hmem
    rw [sum_comb_extend, sum_comb_extend, ← Finset.sum_sub_distrib] at h1
    simpa only [mul_sub] using h1
  exact GlobalTheory.T.determinant_perturbation_bound ℂ_[p] (Fin N) k (fun j l => ∑ i, (h j i : ℂ_[p]) * a (Fin.castLE hk l) i)
    (fun j l => ∑ i, (h' j i : ℂ_[p]) * a' (Fin.castLE hk l) i) ν hνpos hle hex hclose σ

end GlobalTheory.HtGen.PointDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudeGeometricPointsOfGenericDvr
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.HTGeomExt

variable {p : ℕ} [Fact p.Prime] {D : Datum p}

theorem tateIsoO_transport {k k' : Type} [Field k] [Field k'] {Q Q' : Type} [Group Q] [Group Q']
    {act : D.O → Q → Q} {act' : D.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → k'ˣ → Prop}
    (I : TateIsoO D k Q act e) (r : Q →* Q') (hact : ∀ c q, r (act c q) = act' c (r q))
    (hbij : ∀ n, 0 < n → n.Coprime p → Set.BijOn r {y : Q | y ^ n = 1} {y : Q' | y ^ n = 1})
    (ζ' : ℕ → k'ˣ) (hprim : ∀ n, 0 < n → n.Coprime p → IsPrimitiveRoot (ζ' n) n)
    (hpow : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ζ' (n * m) ^ m = ζ' n)
    (hisom : ∀ n, 0 < n → n.Coprime p → ∀ x y,
      e' n (r (I.ev n x)) (r (I.ev n y)) (ζ' n ^ (2 * D.EF x y))) :
    ∃ I' : TateIsoO D k' Q' act' e', ∀ n x, I'.ev n x = r (I.ev n x) := by
  have htor : ∀ n, 0 < n → n.Coprime p → ∀ x, I.ev n x ^ n = 1 :=
    fun n h1 h2 x => (I.onto n h1 h2 _).2 ⟨x, rfl⟩
  refine ⟨
    { ζ := ζ'
      ζ_prim := hprim
      ζ_pow := hpow
      ev := fun n x => r (I.ev n x)
      add := fun n x y => by simp only [I.add, map_mul]
      lin := fun n c x => by simp only [I.lin, hact]
      ker := fun n h1 h2 x => ?_
      onto := fun n h1 h2 q => ?_
      tower := fun n m h1 h2 h3 x => by simp only [← map_pow, I.tower n m h1 h2 h3]
      isom := hisom }, fun n x => rfl⟩
  · rw [← I.ker n h1 h2 x]
    constructor
    · intro h
      refine (hbij n h1 h2).injOn (htor n h1 h2 x) (show (1 : Q) ^ n = 1 from one_pow n) ?_
      rw [h, map_one]
    · intro h
      show r (I.ev n x) = 1
      rw [h, map_one]
  · constructor
    · intro hq
      obtain ⟨y, hy, rfl⟩ := (hbij n h1 h2).surjOn hq
      obtain ⟨x, hx⟩ := (I.onto n h1 h2 y).1 hy
      exact ⟨x, by rw [hx]⟩
    · rintro ⟨x, rfl⟩
      show r (I.ev n x) ^ n = 1
      rw [← map_pow, htor n h1 h2 x, map_one]

end GlobalTheory.HTGeomExt

namespace GlobalTheory.HTGeomExt

theorem tateIsoO_geom_of_generic : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (gm : R →+* W) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (act : OActN D.O G) (P : LB (G2 G).left), P.IsLB → ∀ (y : D.La → (𝟙_ (Over (Sp W)) ⟶ G)), (∀ x x', y (x + x') = y x * y x') → (∀ (k : Type) [Field k] [IsAlgClosed k] (β : L →+* k), ∃ I : TateIsoO D k (Over.mk (spMap (β.comp (algebraMap W L))) ⟶ G) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) n g g' (unitOn z)), ∀ x, toUnit _ ≫ y x = I.ev N x) → ∀ (k : Type) [Field k] [IsAlgClosed k] (β : W →+* k), ∃ I : TateIsoO D k (Over.mk (spMap β) ⟶ G) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) n g g' (unitOn z)), ∀ x, toUnit _ ≫ y x = I.ev N x := by
  intro p _ D R _ b N W L _ _ _ _ _ _ gm G _ _ hab act P hP y hy hgen k _ _ β
  obtain ⟨V, j, h, hj, hx⟩ := GlobalTheory.T.geometric_point_dvr_factors_valuation_subring_closure W L k (spMap β)
  have hunit : ∀ n : ℕ, n.Coprime p → IsUnit (n : V) := fun n hn => by
    simpa using (b.unit n hn).map (j.comp gm)
  obtain ⟨r, hr1, hr2, hr3, hr4⟩ := GlobalTheory.T.exists_reduction_points_abelianScheme_valuationRing V (AlgebraicClosure L) k h (Sp W) G hab (spMap j)
  have hs : spMap ((algebraMap V (AlgebraicClosure L)).comp j) =
      spMap (algebraMap V (AlgebraicClosure L)) ≫ spMap j := by
    dsimp only [spMap]
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hg := hgen (AlgebraicClosure L) (algebraMap L (AlgebraicClosure L))
  rw [← hj, hs] at hg
  obtain ⟨I, hI⟩ := hg
  rw [hx]
  have hz : ∀ n, ∃ z : Vˣ, 0 < n → n.Coprime p →
      (algebraMap V (AlgebraicClosure L) (z : V) = (I.ζ n : AlgebraicClosure L) ∧
        IsPrimitiveRoot (Units.map (h : V →* k) z) n) := by
    intro n
    by_cases hn : 0 < n ∧ n.Coprime p
    · obtain ⟨z, ⟨hz1, hz2⟩, -⟩ := valuationRing_rootOfUnity_lift_reduce V (AlgebraicClosure L) k h n
        (hunit n hn.2) (I.ζ n) (I.ζ_prim n hn.1 hn.2).pow_eq_one
      exact ⟨z, fun _ _ => ⟨hz1, hz2 (I.ζ_prim n hn.1 hn.2)⟩⟩
    · exact ⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ hn⟩
  choose z hz using hz
  have hzU : ∀ n, 0 < n → n.Coprime p →
      Units.map (algebraMap V (AlgebraicClosure L) : V →* AlgebraicClosure L) (z n) = I.ζ n :=
    fun n h1 h2 => Units.ext (hz n h1 h2).1
  have hinj : Function.Injective (algebraMap V (AlgebraicClosure L)) :=
    IsFractionRing.injective V (AlgebraicClosure L)
  have hLb := LB.isLB_pull hP (lift (𝟙 G) (𝟙 G)).left
  have hpow : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p →
      Units.map (h : V →* k) (z (n * m)) ^ m = Units.map (h : V →* k) (z n) := by
    intro n m h1 h2 h3
    have hn : n.Coprime p := Nat.Coprime.coprime_dvd_left (Dvd.intro m rfl) h3
    rw [← map_pow]
    congr 1
    apply Units.ext
    apply hinj
    rw [Units.val_pow_eq_pow_val, map_pow, (hz _ (Nat.mul_pos h1 h2) h3).1, (hz n h1 hn).1,
      ← Units.val_pow_eq_pow_val, I.ζ_pow n m h1 h2 h3]
  have hisom : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x x', Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) n (r (I.ev n x)) (r (I.ev n x'))
      (unitOn (Units.map (h : V →* k) (z n) ^ (2 * D.EF x x'))) := by
    intro n h1 h2 x x'
    have hi := I.isom n h1 h2 x x'
    rw [← hzU n h1 h2, ← map_zpow] at hi
    have ho := hr4 _ hLb n (hunit n h2) _ _ (z n ^ (2 * D.EF x x'))
      ((I.onto n h1 h2 _).2 ⟨x, rfl⟩) ((I.onto n h1 h2 _).2 ⟨x', rfl⟩) hi
    rw [map_zpow] at ho
    exact ho
  obtain ⟨I', hI'⟩ := tateIsoO_transport (act' := fun c g => g ≫ act.act c)
    (e' := fun n g g' z => Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) n g g' (unitOn z)) I r (fun c q => hr2 (act.act c) q)
    (fun n _ h2 => hr3 n (hunit n h2)) (fun n => Units.map (h : V →* k) (z n))
    (fun n h1 h2 => (hz n h1 h2).2) hpow hisom
  refine ⟨I', fun x => ?_⟩
  rw [hI', ← hI x]
  refine (hr1 (toUnit _ ≫ y x) _ _ ?_ ?_).symm
  · rw [Over.comp_left, Over.comp_left]
    exact Category.assoc _ _ _
  · rw [Over.comp_left, Over.comp_left]
    exact Category.assoc _ _ _

end GlobalTheory.HTGeomExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataPsiPosTendstoZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorDegenerationData_psi_pos_tendsto_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) → IsLimit (Fan.mk D'.P.A pr) → ∀ (xe : D'.X ≃+ (Fin r → Q.X)), (∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) → ∀ (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), w.IsGen → (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → Q.IsPos (maximalIdeal R) → (∀ χ : D'.X, χ ≠ 0 → D'.PsiIn χ (maximalIdeal R)) ∧ ∀ n : ℕ, {χ : D'.X | ¬ D'.PsiIn χ (maximalIdeal R ^ n)}.Finite := by
  first | exact @GlobalTheory.Mum.TensPol.psi_pos_tendsto | exact GlobalTheory.Mum.TensPol.psi_pos_tendsto | (intros; apply GlobalTheory.Mum.TensPol.psi_pos_tendsto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantLeCommonBoundMonomial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep.DivBound

theorem theta_pow_le : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ))), (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) → (∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1) → ∀ c : WithZero (Multiplicative ℤ), (∀ b, ν (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) ≤ c) → ∀ a, ∃ w : Fin 8 → X, 𝔪.YY a w ∧ ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) ^ ((X₁.S.r * X₁.S.N) ^ 2) ≤ c ^ ((X₁.S.r * X₁.S.N) ^ 2) * ν (algebraMap V (FractionRing V) (mono W t δ w)) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 ν h1 h2 c hc a
  obtain ⟨yy1, -, yy3, -⟩ := GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V ev X m t δ 𝔪
  by_cases hm : maximalIdeal V = ⊥
  · obtain ⟨w, hw⟩ := yy1 a
    refine ⟨w, hw, ?_⟩
    have hu : IsUnit (mono W t δ w) := by
      by_contra hn
      exact 𝔪.mono_ne_zero w ((Submodule.mem_bot V).1 (hm ▸ (mem_maximalIdeal _).2 hn))
    have h1' : ν (algebraMap V (FractionRing V) (mono W t δ w)) = 1 := by
      refine le_antisymm (h1 _) ?_
      have e : ν (algebraMap V (FractionRing V) (mono W t δ w)) * ν (algebraMap V (FractionRing V) (hu.unit⁻¹ : Vˣ)) = 1 := by
        rw [← map_mul, ← map_mul, hu.mul_val_inv, map_one, map_one]
      calc (1 : WithZero (Multiplicative ℤ)) = _ := e.symm
        _ ≤ ν (algebraMap V (FractionRing V) (mono W t δ w)) * 1 := mul_le_mul' le_rfl (h1 _)
        _ = _ := _root_.mul_one _
    rw [h1', _root_.mul_one]
    exact pow_le_pow_left' (hc a) _
  · obtain ⟨V', _, _, _, _, j, k, hcn, hj, hjl, hk, hν⟩ := GlobalTheory.DivBound.exists_cdvr_valuation_le V 𝔪.cn ν h1 h2 hm
    obtain ⟨𝔫, hyk, hyy⟩ := GlobalTheory.Poinc.Sep.MemBC.uMem_baseChange_values g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 V' j k hcn hj hjl hk
    obtain ⟨b, hb⟩ := GlobalTheory.Poinc.IntTerm.DvrScale.exists_dvd_pow g n F W Z i X₁ z₁ act V' (j.comp ev) X m (fun i => j (t i)) δ 𝔫
    obtain ⟨w, r, hw, he⟩ := hb a
    obtain ⟨mu, hmu⟩ := yy1 a
    have hn3 := (GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V' (j.comp ev) X m (fun i => j (t i)) δ 𝔫).2.2.1
    have hw' : 𝔪.YY a w := (yy3 a mu w hmu).2 ((hn3 a mu w (hyy a mu hmu)).1 hw)
    refine ⟨w, hw', ?_⟩
    have hmono : mono W (fun i => j (t i)) δ w = j (mono W t δ w) := by
      simp [mono, map_prod, map_pow]
    have key := hν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2))
      (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) * algebraMap V (FractionRing V) (mono W t δ w))
      ⟨r, by rw [map_pow, ← hyk, he, map_mul, map_pow, ← hyk, hk, hmono]; ring⟩
    rw [map_pow, map_mul, map_pow] at key
    exact key.trans (mul_le_mul' (pow_le_pow_left' (hc b) _) le_rfl)

end GlobalTheory.Poinc.Sep.DivBound
end

