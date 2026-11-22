import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0769
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3433
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0800
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3434
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3396
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3436
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3400
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3377
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceTensorPowerIntegralClosur
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem hInv_of_finite_over_aic (q : ℕ) [NeZero q] (d : ℕ) (hH : (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R))
    (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D] (hq : IsUnit (q : D))
    (hd : ringKrullDim D ≤ d) (T : Type) [CommRing T] [IsDomain T] [Algebra D T]
    [Algebra.IsIntegral D T] (hT : AIC T) (hTq : HInv q T) (E : Type) [CommRing E] [Algebra D E]
    [Algebra.IsIntegral D E] (ι : T →ₐ[D] E) (F : Finset E)
    (hF : Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤) : HInv q E := by
  have hlow := GlobalTheory.T.etaleHomotopyInvariant_integral_killed_of_lowerDim q d hH D hq hd
  have hqE : IsUnit (q : E) := by simpa using hq.map (algebraMap D E)
  set X : Finset (E →ₐ[D] T) := (GlobalTheory.T.finite_retractions_of_adjoin_finset_integral_domain D T E ι F hF).toFinset with hX
  have hXid : ∀ χ ∈ X, χ.comp ι = AlgHom.id D T := fun χ hχ => by simpa [hX] using hχ
  obtain ⟨s, hs0, hs⟩ := GlobalTheory.T.exists_ne_zero_isNilpotent_mul_finite_inf_fg_ideals D E (E →ₐ[D] T) X (fun χ => RingHom.ker χ)
    (fun χ hχ => GlobalTheory.T.ker_retraction_fg_of_adjoin_finset D T E ι F hF χ (hXid χ hχ))
    (fun Q hQ hQc => by
      obtain ⟨χ, hχι, hχQ⟩ := GlobalTheory.T.exists_retraction_of_monicPolynomialsHaveRoots D T E hT ι Q hQ hQc
      have hmem : χ ∈ X := by simpa [hX] using hχι
      rw [← hχQ]
      exact iInf₂_le χ hmem)
  set I : Ideal E := ⨅ χ ∈ X, RingHom.ker χ with hI
  set J : Ideal E := Ideal.span {algebraMap D E s} with hJ
  have hIJ : I ⊓ J ≤ nilradical E := by
    intro y hy
    obtain ⟨hyI, hyJ⟩ := Ideal.mem_inf.mp hy
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hyJ
    obtain ⟨m, hm⟩ := hs _ hyI
    refine ⟨2 * m, ?_⟩
    calc (a * algebraMap D E s) ^ (2 * m)
        = a ^ m * (algebraMap D E s * (a * algebraMap D E s)) ^ m := by ring
      _ = 0 := by rw [hm, mul_zero]
  have hJs : ∀ K : Ideal E, J ≤ K → algebraMap D (E ⧸ K) s = 0 := by
    intro K hK
    rw [IsScalarTower.algebraMap_apply D E (E ⧸ K), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hK (Ideal.mem_span_singleton_self _)
  exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q E I J hIJ hqE (GlobalTheory.T.hInv_quot_iInf_ker_retractions q D T E hq hTq hlow ι X hXid)
    (hlow (E ⧸ J) s hs0 (hJs J le_rfl)) (hlow (E ⧸ (I ⊔ J)) s hs0 (hJs _ le_sup_right))

def subalgebraOfSubringEquiv {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) :
    S ≃+* subalgebraOfSubring S.toSubring where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem hInv_tensorPower_integralClosure : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → ∀ k : ℕ, HInv q (PiTensorProduct D (fun _ : Fin (k + 1) => integralClosure D (AlgebraicClosure (FractionRing D)))) := by
  intro q _ d hH D _ _ _ hq hd k
  have hqDp : IsUnit (q : integralClosure D (AlgebraicClosure (FractionRing D))) := by
    simpa using hq.map (algebraMap D (integralClosure D (AlgebraicClosure (FractionRing D))))
  have hTq := GlobalTheory.T.etaleHomotopyInvariance_absolutelyIntegrallyClosed q _ (GlobalTheory.T.monicPolynomialsHaveRoots_integralClosure_algClosure D) hqDp
  have hqS : ∀ F, IsUnit (q : firstAndFinite D (integralClosure D (AlgebraicClosure (FractionRing D))) k F) :=
    fun F => by simpa using hq.map (algebraMap D (firstAndFinite D (integralClosure D (AlgebraicClosure (FractionRing D))) k F))
  refine GlobalTheory.T.hInv_of_directed_union_subalgebras q _ (Finset (integralClosure D (AlgebraicClosure (FractionRing D))))
    (fun F => subalgebraOfSubring (firstAndFinite D (integralClosure D (AlgebraicClosure (FractionRing D))) k F).toSubring)
    ?_ ?_ ?_ ?_
  · intro F G hFG x hx
    rw [mem_subalgebraOfSubring] at hx ⊢
    exact Algebra.adjoin_mono (Set.union_subset_union_right _
      (Set.iUnion_mono fun i => Set.image_mono (Finset.coe_subset.mpr hFG))) hx
  · intro x
    obtain ⟨F, hF⟩ := GlobalTheory.T.exists_finset_mem_tensorPowerFirstFactorAdjoinFinset D _ k x
    exact ⟨F, (mem_subalgebraOfSubring).mpr hF⟩
  · intro F
    simpa using (hqS F).map (subalgebraOfSubringEquiv (firstAndFinite D (integralClosure D (AlgebraicClosure (FractionRing D))) k F))
  · intro F
    haveI := GlobalTheory.T.tensorPowerFirstFactorAdjoinFinset_isIntegral D (integralClosure D (AlgebraicClosure (FractionRing D))) k F
    obtain ⟨F', hF'⟩ := GlobalTheory.T.tensorPowerFirstFactorAdjoinFinset_fg_over_first D (integralClosure D (AlgebraicClosure (FractionRing D))) k F
    exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ (subalgebraOfSubringEquiv _)
      (hInv_of_finite_over_aic q d hH D hq hd _ (GlobalTheory.T.monicPolynomialsHaveRoots_integralClosure_algClosure D) hTq _ (firstIncl D _ k F) F' hF')

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemePullbackAdjointEndomorphismStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedSubscheme_pullback_adjoint_endomorphism_pair : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (f f' : A ⟶ A), IsMonHom f → IsMonHom f' → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ' : A'.left ⟶ A.left) (φ₂' : (A' ⊗ A').left ⟶ (A ⊗ A).left) (g g' : A' ⟶ A'), IsGrpPullback A' A t φ' → IsSquare φ' φ₂' → g.left ≫ φ' = φ' ≫ f.left → g'.left ≫ φ' = φ' ≫ f'.left → (LBIso ((Q.pull φ₂').pull (lift (fst A' A' ≫ g) (snd A' A')).left) ((Q.pull φ₂').pull (lift (fst A' A') (snd A' A' ≫ g')).left) ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  first | exact @GlobalTheory.EndLoc.exists_closed_adj | exact GlobalTheory.EndLoc.exists_closed_adj | (intros; apply GlobalTheory.EndLoc.exists_closed_adj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonSemiAbelianPullbackTwoUnitaryTraitsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_semiAbelian_pullback_two_unitary_traits : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (T T' : UTrait Xo c) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (f : T.V →+* W)
    (f' : T'.V →+* W) (fK : FractionRing T.V →+* FractionRing W) (fK' : FractionRing T'.V →+* FractionRing W),
    GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → Function.Injective f → Function.Injective f' → IsLocalHom f →
    IsLocalHom f' → (∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) →
    (∀ a, fK' (algebraMap T'.V _ a) = algebraMap W _ (f' a)) → spMap fK ≫ T.y = spMap fK' ≫ T'.y →
    ∃ tW : SAB H (Sp W), Nonempty (SABMap tW T.t (spMap f)) ∧ Nonempty (SABMap tW T'.t (spMap f')) := by
  first | exact @GlobalTheory.UPoinc.TraitUniq.exists_common_pull | exact GlobalTheory.UPoinc.TraitUniq.exists_common_pull | (intros; apply GlobalTheory.UPoinc.TraitUniq.exists_common_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedHeatConnectionOnAbelianFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn
open GlobalTheory.KS.GlueDer (rsT_eq res_app pre_mono)
open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_sub)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConn

theorem exists_descData : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) (ν : R), (∀ a, IsField ⊤ (dd a)) → (∀ a V r, dd a V (constFn Y.H.hom V r) = 0) → (∀ a α V f, IsWt Y α V f → IsWt Y α V (dd a V f)) → IsBasic Y h → ∃ (V : h.J → Q.P.A.left.Opens) (E : h.J → Fld Q.P.A.left) (P : ∀ i, Γ(Q.P.A.left, V i)), (∀ i, h.W i = Y.q.left ⁻¹ᵁ V i) ∧ (∀ i, IsLift Q.P.A D (V i) (E i)) ∧ (∀ i V', V' ≤ V i → ∀ f, (Y.q.left.app V').hom (E i V' f) = GlobalTheory.HeatConn.dE h ν i _ ((Y.q.left.app V').hom f)) ∧ ∀ i, (Y.q.left.app (V i)).hom (P i) = rsT (GlobalTheory.HeatConn.pE h ν i) (Y.q.left ⁻¹ᵁ V i) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h ν hfield hconst hwt hB
  choose V hV using fun i => (hB i).1
  have hlift : ∀ i, IsLift Y.H D (Y.q.left ⁻¹ᵁ V i) (dE h ν i) := fun i => by
    rw [← hV i]
    refine ⟨isField_dE h ν hfield i, fun O hO r => ?_⟩
    show h.d i O _ + constFn Y.H.hom O ν * ∑ a, constFn Y.H.hom O (h.u a) * dd a O (constFn Y.H.hom O r) = _
    simp only [hconst, mul_zero, Finset.sum_const_zero, add_zero]
    exact (h.lift i).2 O hO r
  have hwt0 : ∀ i (V' : Q.P.A.left.Opens), V' ≤ V i → ∀ f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V') f →
      IsWt Y 0 (Y.q.left ⁻¹ᵁ V') (dE h ν i _ f) := by
    intro i V' hV' f hf
    exact WtAlg.isWt_add ((hB i).2.2.2 0 V' ((GlobalTheory.KS.GlueDer.pre_mono _ hV').trans (hV i).ge) f hf)
      (WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ ν)
        (WtAlg.isWt_sum _ _ fun a _ => WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ _) (hwt a 0 _ f hf)))
  choose E hE hq using fun i => AbConst.exists_desc Y (V i) (dE h ν i) D (hlift i) (hwt0 i)
  have hP : ∀ i, ∃ a, (Y.q.left.app (V i)).hom a = rsT (pE h ν i) (Y.q.left ⁻¹ᵁ V i) := fun i => by
    refine AbConst.exists_app_eq Y ?_
    have hw : IsWt Y 0 (h.W i) (pE h ν i) :=
      WtAlg.isWt_add (hB i).2.1 (WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ ν) (hB i).2.2.1)
    have tr : ∀ (W : Y.H.left.Opens) (s : Γ(Y.H.left, W)), W = Y.q.left ⁻¹ᵁ V i → IsWt Y 0 W s →
        IsWt Y 0 _ (rsT s (Y.q.left ⁻¹ᵁ V i)) := by
      rintro W s rfl hs
      rwa [WtAlg.rsT_self]
    exact tr _ _ (hV i) hw
  choose P hP using hP
  exact ⟨V, E, P, hV, hE, hq, hP⟩

theorem exists_glue_desc : ∀ {R K : Type} [CommRing R] [Field K] (G : Over (Sp R)) (A₀ : Over (Sp K)) (m₀ : A₀.left ⟶ G.left) (φ : R →+* K), m₀ ≫ G.hom = A₀.hom ≫ spMap φ → ∀ (D : R → R) {I : Type} (V : I → G.left.Opens), ⨆ i, V i = ⊤ → ∀ (E : I → Fld G.left), (∀ i, IsLift G D (V i) (E i)) → (∀ i i' O, O ≤ V i ⊓ V i' → ∀ f, (m₀.app O).hom (E i O f) = (m₀.app O).hom (E i' O f)) → ∃ ed : ∀ W : G.left.Opens, Γ(G.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom G.hom m₀ (fun r => φ (D r)) ⊤ ed ∧ ∀ i U, U ≤ V i → ∀ f, ed U f = (m₀.app U).hom (E i U f) := by
  intro R K _ _ G A₀ m₀ φ hm D I V hV E hE hc
  have hW : ∀ y, ∃ i, m₀ y ∈ V i := fun y => by
    have hy : m₀ y ∈ ⨆ i, V i := by rw [hV]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hy
  have he : ∀ i, GlobalTheory.KS.LocDerK A₀.hom G.hom m₀ (fun r => φ (D r)) (V i) (fun W f => (m₀.app W).hom (E i W f)) := by
    intro i
    refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h' hW f => ?_, fun W hW r => ?_⟩
    · rw [(hE i).1.1 W hW, map_add]
    · rw [(hE i).1.2.1 W hW, map_add, map_mul, map_mul]
    · rw [(hE i).1.2.2 W W' h' hW, GlobalTheory.KS.GlueDer.rsT_eq (GlobalTheory.KS.GlueDer.pre_mono m₀ h'), GlobalTheory.KS.GlueDer.res_app m₀ h']
    · rw [(hE i).2 W hW, GlobalTheory.KS.GlueDer.app_const φ _ _ m₀ hm]
  obtain ⟨ed, hed, hchar⟩ := GlobalTheory.InteriorKS.glue_along A₀.hom G.hom m₀ (fun r => φ (D r)) V hW
    (fun i W f => (m₀.app W).hom (E i W f)) he fun i i' O hO f => hc i i' O hO f
  refine ⟨ed, hed, fun i U hU f => hchar U f _ fun i' => ?_⟩
  have h1 := (he i).res U (U ⊓ V i') inf_le_left hU f
  rw [GlobalTheory.KS.GlueDer.rsT_eq (GlobalTheory.KS.GlueDer.pre_mono m₀ inf_le_left)] at h1
  rw [← h1]
  exact hc i i' _ (le_inf (inf_le_left.trans hU) inf_le_right) _

theorem connK_transition : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] {φ : R →+* K} {e : ℕ} {ν : R} {A₀ : Over (Sp K)} [GrpObj A₀] {m₀ : A₀.left ⟶ Q.P.A.left}, GlobalTheory.HeatConn.IsFibre Y h φ e ν A₀ m₀ → ∀ {V : h.J → Q.P.A.left.Opens} {ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)} {pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)}, GlobalTheory.HeatConn.IsDesc Y h ν m₀ V ed pb → (∀ i, V i ≤ Q.P.L.U (h.j i)) → ∀ (i i' : h.J), ed (V i ⊓ V i') (rsT (Q.P.L.g (h.j i) (h.j i')).val (V i ⊓ V i')) = pbT m₀ (Q.P.L.g (h.j i) (h.j i')).val (m₀ ⁻¹ᵁ (V i ⊓ V i')) * (rsT (pb i') (m₀ ⁻¹ᵁ (V i ⊓ V i')) - rsT (pb i) (m₀ ⁻¹ᵁ (V i ⊓ V i'))) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF V ed pb hD hV i i'
  have he0 : e ≠ 0 := by
    rintro rfl
    have := hF.inv
    rw [Nat.cast_zero, mul_zero] at this
    exact zero_ne_one this
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he0
  have hUL : V i ⊓ V i' ≤ Q.P.L.U (h.j i) ⊓ Q.P.L.U (h.j i') := inf_le_inf (hV i) (hV i')
  refine ext_lift Y m₀ fun Z a b w z hz => ?_
  have hz' : (a ≫ Y.q.left) z ∈ V i ⊓ V i' := by rw [w]; exact hz
  have haΩ : a z ∈ Y.q.left ⁻¹ᵁ (V i ⊓ V i') := hz'
  have hΩW : Y.q.left ⁻¹ᵁ (V i ⊓ V i') ≤ h.W i ⊓ h.W i' := by
    rw [hD.1 i, hD.1 i']; exact le_inf (pre_mono _ inf_le_left) (pre_mono _ inf_le_right)
  have hΩL : Y.q.left ⁻¹ᵁ (V i ⊓ V i') ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h.j i) ⊓ Q.P.L.U (h.j i')) := pre_mono _ hUL
  have hG : (Y.q.left.app (V i ⊓ V i')).hom (rsT (Q.P.L.g (h.j i) (h.j i')).val (V i ⊓ V i')) =
      pbT Y.q.left (Q.P.L.g (h.j i) (h.j i')).val (Y.q.left ⁻¹ᵁ (V i ⊓ V i')) := by
    rw [rsT_eq hUL, ← res_app Y.q.left hUL (pre_mono _ hUL), pbT, dif_pos hΩL]; rfl
  have hz1 : (b ≫ m₀) z ∈ V i := hz.1
  have hz2 : (b ≫ m₀) z ∈ V i' := hz.2
  rw [hD.2.1 Z a b w z i _ inf_le_left hz, hG, gs_mul b z _ hz, gs_sub b z _ hz, gs_pbT b m₀ z (pre_mono _ hUL) hz,
    gs_rsT b z (pre_mono m₀ inf_le_right) hz, gs_rsT b z (pre_mono m₀ inf_le_left) hz, hD.2.2 Z a b w z i' hz2,
    hD.2.2 Z a b w z i hz1, ← w, ← gs_pbT a Y.q.left z hΩL haΩ, ← gs_rsT a z (hΩW.trans inf_le_right) haΩ,
    ← gs_rsT a z (hΩW.trans inf_le_left) haΩ]
  simp only [gs_eq_gsH a z _ haΩ]
  set π := gsH a z _ haΩ
  set G := pbT Y.q.left (Q.P.L.g (h.j i) (h.j i')).val (Y.q.left ⁻¹ᵁ (V i ⊓ V i'))
  have hΘ : ∀ a' b', π (constFn Y.H.hom _ (h.Θ a' b')) = 0 := fun a' b' => by
    rw [← gs_eq_gsH, hF.gs_const w z _ haΩ, hF.symb, cst_eq_cstH, map_zero]
  have hpow : ∀ (m : ℕ) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ (V i ⊓ V i'))),
      dE h ν i _ (f ^ (m + 1)) = ((m + 1 : ℕ) : Γ(Y.H.left, Y.q.left ⁻¹ᵁ (V i ⊓ V i'))) * f ^ m * dE h ν i _ f := by
    intro m f
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, (isField_dE h ν hF.field i).2.1 _ (hΩW.trans inf_le_left), ih]
      push_cast; ring
  have e1 := congrArg π (h.glue (k + 1) i i' _ hΩW 1)
  rw [_root_.mul_one, map_op h ν (k + 1) hF.inv i _ (hΩW.trans inf_le_left) π hΘ, map_mul,
    map_op h ν (k + 1) hF.inv i' _ (hΩW.trans inf_le_right) π hΘ, hpow,
    AbConst.isField_one (isField_dE h ν hF.field i') (hΩW.trans inf_le_right)] at e1
  simp only [map_mul, map_pow, map_natCast, map_one, map_zero, zero_add, _root_.mul_one] at e1
  have h2 : IsUnit (2 : Z.presheaf.stalk z) := by
    simpa only [map_ofNat] using (two_ne_zero (α := K)).isUnit.map (cstH (b ≫ A₀.hom) z)
  have hk : IsUnit (((k + 1 : ℕ)) : Z.presheaf.stalk z) := by
    simpa only [map_natCast] using
      (Nat.cast_ne_zero.2 (Nat.succ_ne_zero k) : ((k + 1 : ℕ) : K) ≠ 0).isUnit.map (cstH (b ≫ A₀.hom) z)
  have hGu : IsUnit G := by
    simp only [G, pbT, dif_pos hΩL]; exact (Units.isUnit _).map _
  have hc : IsUnit (2 * ((k + 1 : ℕ) : Z.presheaf.stalk z) ^ 2 * π G ^ k) := (h2.mul (hk.pow 2)).mul ((hGu.map π).pow k)
  refine hc.mul_left_cancel ?_
  push_cast at e1 ⊢
  linear_combination e1

theorem exists_connK_desc : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∃ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb ∧ IsDesc Y h ν m₀ V ed pb := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF
  have := (AbConst.surjective_q Y).1
  obtain ⟨V, E, P, hW, hE, hq, hP⟩ := exists_descData Y h ν hF.field hF.const hF.wt hF.basic
  have hm : m₀ ≫ Q.P.A.hom = A₀.hom ≫ spMap φ := hF.pull.1.w
  have hcov : ⨆ i, V i = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨y, rfl⟩ := Y.q.left.surjective x
    have hy : y ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    rw [hW] at hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  have hVL : ∀ i, V i ≤ Q.P.L.U (h.j i) := fun i x hx => by
    obtain ⟨y, rfl⟩ := Y.q.left.surjective x
    have hy : y ∈ h.W i := by rw [hW]; exact hx
    exact h.le i hy
  have hc : ∀ i i' O, O ≤ V i ⊓ V i' → ∀ f, (m₀.app O).hom (E i O f) = (m₀.app O).hom (E i' O f) := by
    intro i i' O hO f
    refine ext_lift Y m₀ fun Z a b w z hz => ?_
    have hz' : (a ≫ Y.q.left) z ∈ O := by rw [w]; exact hz
    rw [gs_pull b m₀ z O hz, gs_pull b m₀ z O hz, ← w, ← gs_pull a Y.q.left z O hz', ← gs_pull a Y.q.left z O hz',
      hq i O (hO.trans inf_le_left), hq i' O (hO.trans inf_le_right)]
    refine hF.dE_agree w z i i' _ ?_ hz' _
    rw [hW i, hW i']
    exact le_inf (GlobalTheory.KS.GlueDer.pre_mono _ (hO.trans inf_le_left)) (GlobalTheory.KS.GlueDer.pre_mono _ (hO.trans inf_le_right))
  obtain ⟨ed, hed, hedE⟩ := exists_glue_desc Q.P.A A₀ m₀ φ hm D V hcov E hE hc
  let pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i) := fun i => (m₀.app (V i)).hom (P i)
  have hD : IsDesc Y h ν m₀ V ed pb := by
    refine ⟨hW, fun Z a b w z i U hU hz f => ?_, fun Z a b w z i hz => ?_⟩
    · have hz' : (a ≫ Y.q.left) z ∈ U := by rw [w]; exact hz
      rw [hedE i U hU f, gs_pull b m₀ z U hz, ← w, ← gs_pull a Y.q.left z U hz', hq i U hU f]
    · have hz' : (a ≫ Y.q.left) z ∈ V i := by rw [w]; exact hz
      show gs b z _ ((m₀.app (V i)).hom (P i)) = _
      rw [gs_pull b m₀ z (V i) hz, ← w, ← gs_pull a Y.q.left z (V i) hz', hP i]
      exact GlobalTheory.KS.DlogPol.gs_rsT a z (hW i).ge hz' _
  exact ⟨V, ed, pb, ⟨hed, hcov, hVL, fun i i' => connK_transition Y h hF hD hVL i i'⟩, hD⟩

end GlobalTheory.HeatConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualOneFormsInvariantFieldsAffineOpen
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.GcDual

def cHom {K : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K) (W : X.Opens) : K →+* Γ(X, W) :=
  (p.appLE ⊤ W (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem coeffs_zero {K : Type} [Field K] (P₀ : Out.PolAV (Sp K)) (n : ℕ)
    (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left)
    (hd : ∀ a, IsInv P₀.A (v a) (dd a)) (W : P₀.A.left.Opens) (hW : IsAffineOpen W)
    {C : Type} [CommRing C] (ψ : Γ(P₀.A.left, W) →+* C) (c : Fin n → C)
    (hc : ∀ f, ∑ a, c a * ψ (dd a W f) = 0) : c = 0 := by
  haveI := P₀.smoothDim
  haveI : Smooth P₀.A.hom := SmoothOfRelativeDimension.smooth P₀.g _
  letI : Algebra K C := (ψ.comp (cHom P₀.A.hom W)).toAlgebra
  obtain ⟨x, hx, ex⟩ := exists_evalPt_eq hW ψ
  have hxp : x ≫ P₀.A.hom = (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := K) C).hom := by
    refine (eq_spMap_of_evalPt _ (algebraMap K C) fun a => ?_).trans rfl
    rw [← evalPt_constFn P₀.A.hom x W hx, ex]
    rfl
  let y : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := K) C ⟶ P₀.A := Over.homMk x hxp
  obtain ⟨c₀, -, hu⟩ := GlobalTheory.VertCoeffRing.existsUnique_coeff_alg (GlobalTheory.VertCoeffRing.isLieBasis_tvE v)
    (fun B _ _ e he z O h => GlobalTheory.VertCoeffRing.evalPt_lieExp v dd hd B e he z O h) y hW hx (fun _ => 0)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ => rfl)
  have h1 := hu c (fun f => by simpa [y, ex] using (hc f).symm)
  have h2 := hu 0 (fun f => by simp)
  rw [h1, h2]

end GlobalTheory.GcDual

namespace GlobalTheory.GcDual

variable {A : Type} [CommRing A] {n : ℕ}

theorem mem_smul_top_of_forall_mem (I : Ideal A) (x : Fin n → A) (hx : ∀ b, x b ∈ I) :
    x ∈ I • (⊤ : Submodule A (Fin n → A)) := by
  rw [← Finset.univ_sum_single x]
  refine Submodule.sum_mem _ fun b _ => ?_
  have : Pi.single b (x b) = x b • (Pi.single b 1 : Fin n → A) := by
    rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
  rw [this]
  exact Submodule.smul_mem_smul (hx b) trivial

theorem eq_top_of_forall_maximal (M : Submodule A (Fin n → A))
    (h : ∀ m : Ideal A, m.IsMaximal → ∀ x, x ∈ M ⊔ m • (⊤ : Submodule A (Fin n → A))) : M = ⊤ := by
  have hQ : ∀ m : Ideal A, m.IsMaximal → ∃ r : A, r - 1 ∈ m ∧ ∀ q : (Fin n → A) ⧸ M, r • q = 0 := by
    intro m hm
    have hle : (⊤ : Submodule A ((Fin n → A) ⧸ M)) ≤ m • ⊤ := by
      intro q _
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective M q
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (h m hm x)
      have hz' : M.mkQ z ∈ m • (⊤ : Submodule A ((Fin n → A) ⧸ M)) := by
        have : m • (⊤ : Submodule A (Fin n → A)) ≤ (m • (⊤ : Submodule A ((Fin n → A) ⧸ M))).comap M.mkQ :=
          Submodule.smul_le.2 fun r hr t _ => by
            rw [Submodule.mem_comap, map_smul]
            exact Submodule.smul_mem_smul hr trivial
        exact this hz
      have e : Submodule.Quotient.mk (p := M) (y + z) = M.mkQ z := by
        rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero M).2 hy, zero_add]; rfl
      rw [e]; exact hz'
    obtain ⟨r, hr, hr'⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m ⊤
      (Module.Finite.fg_top) hle
    exact ⟨r, hr, fun q => hr' q trivial⟩
  have h1 : ∀ q : (Fin n → A) ⧸ M, q = 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨q₀, hq₀⟩ := hne
    let I : Ideal A := Module.annihilator A ((Fin n → A) ⧸ M)
    have hI : I ≠ ⊤ := by
      intro hI
      have : (1 : A) ∈ I := hI ▸ Submodule.mem_top
      exact hq₀ (by simpa using Module.mem_annihilator.1 this q₀)
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨r, hr, hr'⟩ := hQ m hm
    have hrI : r ∈ I := Module.mem_annihilator.2 hr'
    have : (1 : A) ∈ m := by
      have := m.sub_mem (hIm hrI) hr
      simpa using this
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 this)
  rw [eq_top_iff]
  intro x _
  exact (Submodule.Quotient.mk_eq_zero M).1 (h1 _)

end GlobalTheory.GcDual

namespace GlobalTheory.GcDual

theorem span_eq_top {K : Type} [Field K] (P₀ : Out.PolAV (Sp K)) (n : ℕ)
    (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left)
    (hd : ∀ a, IsInv P₀.A (v a) (dd a)) (W : P₀.A.left.Opens) (hW : IsAffineOpen W) :
    Submodule.span Γ(P₀.A.left, W) (Set.range fun f : Γ(P₀.A.left, W) => fun b => dd b W f) = ⊤ := by
  set M := Submodule.span Γ(P₀.A.left, W) (Set.range fun f : Γ(P₀.A.left, W) => fun b => dd b W f) with hM
  refine eq_top_of_forall_maximal M fun m hm x => ?_
  haveI := hm
  letI : Field (Γ(P₀.A.left, W) ⧸ m) := Ideal.Quotient.field m
  let π : Γ(P₀.A.left, W) →+* Γ(P₀.A.left, W) ⧸ m := Ideal.Quotient.mk m
  let S : Submodule (Γ(P₀.A.left, W) ⧸ m) (Fin n → Γ(P₀.A.left, W) ⧸ m) :=
    Submodule.span _ (Set.range fun f : Γ(P₀.A.left, W) => fun b => π (dd b W f))
  have hS : S = ⊤ := by
    by_contra hS
    obtain ⟨φ, hφ0, hφ⟩ := S.exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hS)
    classical
    let c : Fin n → Γ(P₀.A.left, W) ⧸ m := fun b => φ fun j => if b = j then 1 else 0
    have hc := coeffs_zero P₀ n v dd hd W hW π c fun f => by
      have := hφ (Submodule.subset_span ⟨f, rfl⟩)
      rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ] at this
      simpa [c, smul_eq_mul, mul_comm] using this
    apply hφ0
    refine LinearMap.ext fun z => ?_
    rw [LinearMap.pi_apply_eq_sum_univ]
    have : ∀ i, φ (fun j => if i = j then 1 else 0) = 0 := fun i => congrFun hc i
    simp [this]
  have lift : ∀ y ∈ S, ∃ x₀ ∈ M, (fun b => π (x₀ b)) = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, rfl⟩ := hy
      exact ⟨fun b => dd b W f, Submodule.subset_span ⟨f, rfl⟩, rfl⟩
    | zero => exact ⟨0, M.zero_mem, by ext; simp⟩
    | add y y' _ _ h h' =>
      obtain ⟨x₀, hx₀, rfl⟩ := h
      obtain ⟨x₁, hx₁, rfl⟩ := h'
      exact ⟨x₀ + x₁, M.add_mem hx₀ hx₁, by ext; simp⟩
    | smul s y _ h =>
      obtain ⟨x₀, hx₀, rfl⟩ := h
      obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective s
      exact ⟨s' • x₀, M.smul_mem s' hx₀, by ext; simp [π]⟩
  obtain ⟨x₀, hx₀, e⟩ := lift (fun b => π (x b)) (hS ▸ Submodule.mem_top)
  have hk : x - x₀ ∈ m • (⊤ : Submodule Γ(P₀.A.left, W) (Fin n → Γ(P₀.A.left, W))) :=
    mem_smul_top_of_forall_mem m _ fun b => by
      rw [Pi.sub_apply, ← Ideal.Quotient.eq]
      exact (congrFun e b).symm
  have : x = x₀ + (x - x₀) := by abel
  rw [this]
  exact Submodule.add_mem_sup hx₀ hk

theorem exists_dual_forms : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ W : P₀.A.left.Opens, IsAffineOpen W → ∀ a : Fin n, ∃ (N : ℕ) (g f : Fin N → Γ(P₀.A.left, W)), ∀ b, ∑ i, g i * dd b W (f i) = if a = b then 1 else 0 := by
  intro K _ _ P₀ n v dd hd W hW a
  have hmem : (Pi.single a 1 : Fin n → Γ(P₀.A.left, W)) ∈
      Submodule.span Γ(P₀.A.left, W) (Set.range fun f : Γ(P₀.A.left, W) => fun b => dd b W f) := by
    rw [span_eq_top P₀ n v dd hd W hW]; exact Submodule.mem_top
  obtain ⟨N, g, u, hu⟩ := Submodule.mem_span_set'.1 hmem
  refine ⟨N, g, fun i => (u i).2.choose, fun b => ?_⟩
  have h := congrFun hu b
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  have e : ∀ i, dd b W ((u i).2.choose) = (u i : Fin n → Γ(P₀.A.left, W)) b :=
    fun i => congrFun (u i).2.choose_spec b
  simp only [e]
  rw [h, Pi.single_apply]
  by_cases hab : a = b
  · subst hab; simp
  · rw [if_neg (Ne.symm hab), if_neg hab]

end GlobalTheory.GcDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreDerivationOfTwoDualNumberPullbacksStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibre_derivation_of_two_dualNumber_pullbacks : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∃ d : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.A.hom m₀ (fun r => (ρ r).snd) ⊤ d ∧ (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (d W f) (π₂ ⁻¹ᵁ W)) := by
  first | exact @GlobalTheory.KS.TwoPull.exists_locDerK_of_two_pullbacks | exact GlobalTheory.KS.TwoPull.exists_locDerK_of_two_pullbacks | (intros; apply GlobalTheory.KS.TwoPull.exists_locDerK_of_two_pullbacks <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousSwapRegularStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homogeneous_swap_regular : ArCalc → ∃ G, Homog G ∧ SwapReg G := by
  first | exact @GlobalTheory.CovTest.SwapLine.swapReg_exists | exact GlobalTheory.CovTest.SwapLine.swapReg_exists | (intros; apply GlobalTheory.CovTest.SwapLine.swapReg_exists <;> assumption)
end

