import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1563
import Development.AbelianVarietyTheory.Definitions.Uniformization.InKLbPowIffPowEqOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1564
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LiftFormsMainTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1475
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1574
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1360
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1357
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfPowEqOneOfGeometric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel GlobalTheory.UPel.HeckeImage

namespace GlobalTheory.TorsionRigid

theorem eq_one_of_pow_eq_one_of_geometric : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (m : ℕ), 0 < m → IsUnit ((m : Γ(S, ⊤))) → ∀ (T : Over S) (x : T ⟶ A), x ^ m = 1 → (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (q : Sp κ ⟶ T.left), (Over.homMk q rfl : Over.mk (q ≫ T.hom) ⟶ T) ≫ x = 1) → x = 1 := by
  intro S A _ _ hA m _ hm T x hx hgeo
  let f := (ReciprocityTheory.ChartRestriction.G.Out.mulA A m).left
  haveI : FormallyUnramified f := GlobalTheory.formallyUnramified_mulA S A m hm
  haveI : Smooth A.hom := hA.smooth
  have hfA : f ≫ A.hom = A.hom := Over.w _
  haveI : LocallyOfFiniteType (f ≫ A.hom) := by rw [hfA]; infer_instance
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f A.hom
  have hpow : ∀ y : T ⟶ A, y ≫ ReciprocityTheory.ChartRestriction.G.Out.mulA A m = y ^ m := fun y => by
    simp [ReciprocityTheory.ChartRestriction.G.Out.mulA, MonObj.comp_pow]
  have hf : x.left ≫ f = (1 : T ⟶ A).left ≫ f := by
    have e1 := congrArg CommaMorphism.left (hpow x)
    have e2 := congrArg CommaMorphism.left (hpow 1)
    simp only [Over.comp_left] at e1 e2
    rw [e1, e2, hx, one_pow]
  let p : T.left ⟶ pullback f f := pullback.lift x.left (1 : T ⟶ A).left hf
  have hr : Set.range p ⊆ Set.range (pullback.diagonal f) := by
    rintro _ ⟨t, rfl⟩
    let κ : Type := AlgebraicClosure (T.left.residueField t)
    let q : Sp κ ⟶ T.left :=
      Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) κ)) ≫ T.left.fromSpecResidueField t
    have hq : (Over.homMk q rfl : Over.mk (q ≫ T.hom) ⟶ T) ≫ x = (Over.homMk q rfl : Over.mk (q ≫ T.hom) ⟶ T) ≫ 1 := by
      rw [hgeo κ q, MonObj.comp_one]
    have hq' : q ≫ x.left = q ≫ (1 : T ⟶ A).left := by
      have h0 := congrArg (fun h => h.left) hq
      simp only [Over.comp_left, Over.homMk_left] at h0
      exact h0
    have e : q ≫ p = (q ≫ x.left) ≫ pullback.diagonal f := by
      refine pullback.hom_ext ?_ ?_
      · simp only [p, Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
      · simp only [p, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, hq']
    refine ⟨(q ≫ x.left) (IsLocalRing.closedPoint κ), ?_⟩
    have hqt : q (IsLocalRing.closedPoint κ) = t :=
      Scheme.fromSpecResidueField_apply t _
    have e2 : p (q (IsLocalRing.closedPoint κ)) =
        pullback.diagonal f ((q ≫ x.left) (IsLocalRing.closedPoint κ)) :=
      congrArg (fun h => h (IsLocalRing.closedPoint κ)) e
    rw [hqt] at e2
    exact e2.symm
  let g := IsOpenImmersion.lift (pullback.diagonal f) p hr
  have hg := IsOpenImmersion.lift_fac (pullback.diagonal f) p hr
  have h1 : x.left = g := by
    have h0 := congrArg (· ≫ pullback.fst f f) hg
    simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, p, pullback.lift_fst] at h0
    exact h0.symm
  have h2 : (1 : T ⟶ A).left = g := by
    have h0 := congrArg (· ≫ pullback.snd f f) hg
    simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, p, pullback.lift_snd] at h0
    exact h0.symm
  exact Over.OverMorphism.ext (h1.trans h2.symm)

end GlobalTheory.TorsionRigid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowOfBaseChangeEqPowPrincipalAbelianCMTripleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_pow_of_baseChange_eq_pow_principalAbelianCMTriple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (A B : PAT H (Sp (𝓞 K))) (A' B' : PAT H (Sp (𝓞 K'))) (mA : SABMap A'.t A.t (spMap (RingOfIntegers.mapRingHom j)))
    (mB : SABMap B'.t B.t (spMap (RingOfIntegers.mapRingHom j))) (g : A.t.G ⟶ B.t.G) (f' : A'.t.G ⟶ B'.t.G) (n : ℕ),
    0 < n → Serre.IsLinearHom A.t.act B.t.act g → Serre.IsLinearHom A'.t.act B'.t.act f' →
    (f' ^ n).left ≫ mB.φ = mA.φ ≫ g.left →
    ∃ f : A.t.G ⟶ B.t.G, Serre.IsLinearHom A.t.act B.t.act f ∧ f ^ n = g ∧ f'.left ≫ mB.φ = mA.φ ≫ f.left := by
  first | exact @GlobalTheory.eq_pow_of_baseChange_eq_pow | exact GlobalTheory.eq_pow_of_baseChange_eq_pow | (intros; apply GlobalTheory.eq_pow_of_baseChange_eq_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaValuesCoefficientExists
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.GalLift.BaseDatum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def along {K X Z : Type} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup Z] [Module ℂ Z] {s s' : K →+* ℂ} (h : s = s')
    (f : X →ₛₗ[s] Z) : X →ₛₗ[s'] Z where
  toFun := f
  map_add' := f.map_add
  map_smul' a x := by rw [← h]; exact f.map_smulₛₗ a x

theorem ext_val {G Γ W K M : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [Field K] [NumberField K] [StarRing K] [AddCommGroup M] [Module K M] {ι : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ₀ ρ J χ)
    (c₀ : M →ₛₗ[σ₀] W) (e : S.V ≃ₗ[K] M) (he : ∀ x, P.coef x = c₀ (e x))
    (hact : ∀ γ, ∃ T : M → M, ∀ v, c₀ (T v) = ρ γ (c₀ v))
    (hχ : ∀ k, ∃ y, σ₀ y = ((χ k : ℂˣ) : ℂ)) (f : S.Cl → S.V) (h : G) : ∃ v, P.ext f h = c₀ v := by
  obtain ⟨T, hT⟩ := hact (P.decG h)
  obtain ⟨y, hy⟩ := hχ (P.decK h)
  refine ⟨y • T (e (f (P.decC h))), ?_⟩
  rw [map_smulₛₗ, hT, hy, ← he]
  rfl

theorem pair_val {G Γ W K M : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [Field K] [NumberField K] [StarRing K] [AddCommGroup M] [Module K M] {ι : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ₀ ρ J χ)
    (c₀ : M →ₛₗ[σ₀] W) (e : S.V ≃ₗ[K] M) (he : ∀ x, P.coef x = c₀ (e x))
    (pr : M → M → K) (hp : ∀ x x', pr (e x) (e x') = S.pair x x') (v w : M) :
    inner ℂ (c₀ v) (c₀ w) = σ₀ (pr v w) := by
  have h := P.coef_pair (e.symm v) (e.symm w)
  rw [he, he, ← hp] at h
  simpa only [LinearEquiv.apply_symm_apply] using h

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

include R in
theorem realisation_embedding_eq_baseEmbedding : D.what₂.embLL = sg0 D A := (sgAt_mk _ R.hv0).symm

theorem isEtaConj_base (hL : R.toLevCh.Is A.μ0) (hV : EtaVals R) : IsEtaConj (sg0 D A) R.eta R.eta :=
  ⟨hL.eta.1, GlobalTheory.EtaConjExist.unram_of_chrEq hL.eta R.C.isEta.unr, fun P e he x hx =>
    (hV P e he x hx).imp fun y hy => ⟨hy, (RingHom.congr_fun (realisation_embedding_eq_baseEmbedding R) y).symm.trans hy⟩⟩

set_option maxHeartbeats 2000000 in
theorem isConjForms_base {F : Face D A} (hC : R.Char F) {gramR c0R c0L} (hT : Comparison₂ R gramR c0R c0L) :
    IsConjForms R i (sg0 D A) (c0L i) (R.cV i) (along (realisation_embedding_eq_baseEmbedding R) (c0L i)) (R.HV i A.μ0)
      (along (realisation_embedding_eq_baseEmbedding R) (R.jV i A.μ0)) := by
  have h1 := hT.coefL i A.μ0
  obtain ⟨e, -, he, hp, -⟩ := h1
  have hχ := GlobalTheory.ConjForms.levChar_mem R hC.lev hC.grp.chiW i
  have hact : ∀ γ : GQ (Vc D i), ∃ T : VsV D i D.what₂.LL → VsV D i D.what₂.LL,
      ∀ v, c0L i (T v) = (R.cV i).coef.ρ γ (c0L i v) := fun γ =>
    (GlobalTheory.ConjForms.exists_ratMat (Vc D i) γ).elim fun γE hγ =>
      ⟨rhoVr (labLL D) (lamV D i) γE, (hT.mapL i).1 γ γE hγ⟩
  refine ⟨hC.models.cV i, (hT.mapL i).1, (hT.mapL i).2.1, (hT.mapL i).2.2, fun a b => ?_,
    ⟨_, fun k => (hχ k).imp fun y hy => ⟨hy, (RingHom.congr_fun (realisation_embedding_eq_baseEmbedding R) y).symm.trans hy⟩, hC.models.HV i A.μ0⟩,
    fun x h => ?_⟩
  · exact (pair_val (R.B.L i A.μ0).pres (c0L i) e he (fun v w => pairVr (labLL D) (lamV D i) (gramV D i) v w) hp _ _).trans
      (RingHom.congr_fun (realisation_embedding_eq_baseEmbedding R) _)
  · exact (ext_val (R.B.L i A.μ0).pres (c0L i) e he hact hχ _ h).imp fun v hv =>
      ⟨(congrFun (hC.models.jV i A.μ0 x) h).trans hv, (congrFun (hC.models.jV i A.μ0 x) h).trans hv⟩

theorem places_base (hL : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ :=
  Finset.eq_empty_iff_forall_notMem.2 fun PP hPP =>
    (hL.Q_ram A.μ0 PP).2 (Or.inl hPP) (by rw [hL.xi_base]; exact fun _ _ => rfl)

theorem mu_base (hL : R.toLevCh.Is A.μ0) (j : ℕ) : R.toLevCh.mu A.μ0 j = R.mu0 j := by
  have hxi : R.xi A.μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0))
  exact (congrArg (R.mu0 j * ·) hxi).trans (mul_one _)

theorem omegaQ_empty {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : omegaQ ∅ r ξ k y = 1 := by
  unfold omegaQ
  rw [dif_pos (by simp)]
  simp

theorem isThPVecOf_empty {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS sT ΛS ΛT βS βT}
    {Pg Q : Finset (Pl D.host.E)} (hQ : Q = ∅) {ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    {f₀ f : WO S T → ℂ} (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f) :
    IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg ∅ ξ' f₀ f := by
  subst hQ
  unfold IsThPVecOf at h ⊢
  simp only [omegaQ_empty] at h ⊢
  exact h

include R in
theorem deltaConj_base : deltaConj i (sg0 D A) = RealDat.Delta i := by
  have hl : lab (sg0 D A) = id := by
    rw [← realisation_embedding_eq_baseEmbedding R]; exact funext GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.lab_base
  unfold deltaConj
  rw [hl]
  rfl

set_option maxHeartbeats 2000000 in
theorem isConjLift_base {F : Face D A} (hC : R.Char F) :
    IsConjLift R i (sg0 D A) (R.mu0 ((i : ℕ) + 1)) R.eta (R.cV i) (R.HV i A.μ0) (R.thG i A.μ0) := by
  have h1 := hC.thP.thF i A.μ0
  obtain ⟨thP, h2, h3⟩ := h1
  have hω : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (R.toLevCh.mu A.μ0 ((i : ℕ) + 1))
      (R.toLevCh.mu A.μ0 ((i : ℕ) + 1) * R.eta⁻¹) (R.ωP i A.μ0) := hC.thP.ωP i A.μ0
  rw [mu_base R hC.lev] at hω
  have hio := hC.thP.ioP i A.μ0
  rw [← deltaConj_base R i] at hio
  refine ⟨R.ωP i A.μ0, R.vacP i, R.vP i A.μ0, onb (R.MW i (sg0 D A)), R.ioP i, thP, hω,
    isThPVecOf_empty (places_base R hC.lev) _ (hC.thP.vP i A.μ0),
    fun τ => GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.isONBasis_onb _ τ _ (hC.models.order i τ), hC.thP.pt_theta i A.μ0, hio, h2, fun x v => ?_⟩
  exact (congrArg (fun w : MMap (R.MW i (sg0 D A)) => w fun ρ => v ρ) (hC.thP.thG i A.μ0 x)).trans
    (congrArg (R.eWf i (sg0 D A)) (h3 x v))

theorem isConjDatum_base : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → EtaVals R → ∃ (c₁ : VsV D i D.what₂.LL →ₛₗ[sg0 D A] (R.cV i).W) (j : A.fam.amb.FL i A.μ0 →ₛₗ[sg0 D A] (R.HV i A.μ0).H), IsConjDatum R i (sg0 D A) (c0L i) (R.mu0 ((i : ℕ) + 1)) R.eta (R.cV i) c₁ (R.HV i A.μ0) j (R.thG i A.μ0) ∧ ∀ x, j x = R.jV i A.μ0 x := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ hC fw i gramR c0R c0L hT hV
  have hg := (overK_iff_good T R F κw v₀ hC fw i (sg0 D A)).1 fun x _ => (RingHom.congr_fun (realisation_embedding_eq_baseEmbedding R) _).symm
  have h1 := fw.chiR i (sg0 D A) hg
  have h2 := h1.2.2.2.2 (congrArg (·.comp (algebraMap T.Q.c.F D.what₂.LL)) (realisation_embedding_eq_baseEmbedding R).symm)
  exact ⟨along (realisation_embedding_eq_baseEmbedding R) (c0L i), along (realisation_embedding_eq_baseEmbedding R) (R.jV i A.μ0),
    ⟨Eq.subst (motive := ChiAt R i (sg0 D A)) h2 h1, isEtaConj_base R hC.lev hV, isConjForms_base R i hC hT,
      isConjLift_base R i hC⟩, fun _ => rfl⟩

end GlobalTheory.GalLift.BaseDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinateNearGenericPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_coordinate_near_generic_point : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], IsArithVar p 1 → ∃ (U : X.Opens) (x : Fin 1 → Γ(X, U)), IsAffineOpen U ∧ genericPoint X ∈ U ∧ (MvPolynomial.eval₂Hom (algX p U) x).Etale := by
  first | exact @GlobalTheory.GenericEtale.exists_etale_coord_surface | exact GlobalTheory.GenericEtale.exists_etale_coord_surface | (intros; apply GlobalTheory.GenericEtale.exists_etale_coord_surface <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalIntegralPointsMemOpenSubgroupDefiStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_localIntegralPoints_mem_openSubgroup_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (L : Subgroup (finU E n)), IsOpen (L : Set (finU E n)) → ∀ᶠ w in cofinite, ∀ x : UA E n, x ∈ locU n w → cLoc w x ∈ GlobalTheory.LFun.KGL w n → ∀ h : x ∈ finU E n, (⟨x, h⟩ : finU E n) ∈ L := by
  first | exact @GlobalTheory.BCT.GlobLev.eventually_locU_mem | exact GlobalTheory.BCT.GlobLev.eventually_locU_mem | (intros; apply GlobalTheory.BCT.GlobLev.eventually_locU_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleCoordinatesGenericPoint
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

namespace GlobalTheory.GenericCoords

theorem exists_affine_etale_coords : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} {D : ℕ}, IsArithVar p D → ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧
      ∃ t : Fin D → Γ(X, U), (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) t).Etale := by
  intro k _ X _ p D h
  obtain ⟨U, t, hU, hη, he⟩ := GlobalTheory.GenericEtale.exists_etale_coords h
  exact ⟨U, hU, hη, t, he⟩

end GlobalTheory.GenericCoords
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineGaloisCoverDualNumberEpiStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_galois_cover_dual_number_epi : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ Y), ∃ (R'' : Type) (_ : CommRing R'') (g₁ : R' →+* R'') (x'' : Sp R'' ⟶ X) (d₁ : DualNumber R' →+* DualNumber R''), x'' ≫ π = spMap g₁ ≫ x ∧ d₁.comp (algebraMap R' (DualNumber R')) = (algebraMap R'' (DualNumber R'')).comp g₁ ∧ (TrivSqZeroExt.fstHom R'' R'' R'').toRingHom.comp d₁ = g₁.comp (TrivSqZeroExt.fstHom R' R' R').toRingHom ∧ (∀ r : R', d₁.comp (epsScaleR r) = (epsScaleR (g₁ r)).comp d₁) ∧ Epi (spMap d₁) := by
  first | (exact @GlobalTheory.DualCover.exists_dualCover) | (exact GlobalTheory.DualCover.exists_dualCover) | (intros; apply GlobalTheory.DualCover.exists_dualCover  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineRingHomPairOfSpecializesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel GlobalTheory.UPelLevel
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_ring_hom_pair_of_specializes : ∀ {X : Scheme.{0}} {k k' : Type} [Field k] [Field k'] (x : Sp k ⟶ X) (x' : Sp k' ⟶ X) (u : Sp k) (u' : Sp k'), x'.base u' ⤳ x.base u → ∃ (B : Type) (_ : CommRing B) (g : B →+* k) (g' : B →+* k') (ρ : Sp B ⟶ X), RingHom.ker g' ≤ RingHom.ker g ∧ spMap g ≫ ρ = x ∧ spMap g' ≫ ρ = x' := by
  first | exact @GlobalTheory.exists_ringHom_pair_of_specializes | exact GlobalTheory.exists_ringHom_pair_of_specializes | (intros; apply GlobalTheory.exists_ringHom_pair_of_specializes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchGlue
section
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.IwLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

open Classical in

theorem exists_arch_glue (x : ∀ w : InfinitePlace F, GArch σ J w) (s : Finset (InfinitePlace F)) :
    ∃ q : GAd σ J, (∀ v, proj σ J v q = 1) ∧ ∀ w, projArch σ J w q = if w ∈ s then x w else 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, fun v => map_one _, fun w => by simp⟩
  | insert w s hw ih =>
    obtain ⟨q, h1, h2⟩ := ih
    refine ⟨embArch σ J w (x w) * q, fun v => by simp [h1 v], fun u => ?_⟩
    by_cases e : u = w
    · subst e; simp [h2 u, hw]
    · rw [map_mul, projArch_embArch_ne σ J e, one_mul, h2 u]; simp [Finset.mem_insert, e]

open Classical in

theorem exists_fin_glue (x : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), GLoc σ J v)
    (s : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) :
    ∃ q : GAd σ J, (∀ w, projArch σ J w q = 1) ∧ ∀ v, proj σ J v q = if v ∈ s then x v else 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, fun w => map_one _, fun v => by simp⟩
  | insert v s hv ih =>
    obtain ⟨q, h1, h2⟩ := ih
    refine ⟨emb σ J v (x v) * q, fun w => by simp [h1 w], fun u => ?_⟩
    by_cases e : u = v
    · subst e; simp [h2 u, hv]
    · rw [map_mul, proj_emb_ne σ J e, one_mul, h2 u]; simp [Finset.mem_insert, e]

theorem inv_mul_eq_smul {R : Type} [CommRing R] {m k : ℕ} (M : GL (Fin m) R) (X : Matrix (Fin m) (Fin k) R) (l : Rˣ)
    (h : M.1 * X = l.1 • X) : (M⁻¹).1 * X = (l⁻¹).1 • X := by
  have e : (M⁻¹).1 * (M.1 * X) = X := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [h, Matrix.mul_smul] at e
  calc (M⁻¹).1 * X = (l⁻¹).1 • (l.1 • ((M⁻¹).1 * X)) := by
        rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    _ = (l⁻¹).1 • X := by rw [e]

omit [NumberField F] [NumberField E] in

theorem first_cols {r : ℕ} (A B : Matrix (Fin n) (Fin (r + 1)) E) :
    cT (σ : E →+* E) (A.submatrix id (fun _ : Fin 1 => 0)) * J * B.submatrix id (fun _ : Fin 1 => 0) =
      (cT (σ : E →+* E) A * J * B).submatrix (fun _ => 0) (fun _ => 0) := by
  ext i j; simp [cT, Matrix.mul_apply]

end GlobalTheory.IwLine

namespace GlobalTheory.IwLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem yx_of_xy (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (x y : Matrix (Fin n) (Fin 1) E)
    (h : cT (σ : E →+* E) x * J * y = 1) : cT (σ : E →+* E) y * J * x = 1 := by
  have hs : ∀ z : E, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hσ.2.2.2, hσ.2.2.2, star_star])
  have key : (cT (σ : E →+* E) y * J * x) 0 0 = σ ((cT (σ : E →+* E) x * J * y) 0 0) := by
    simp only [cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, AlgHom.coe_toRingHom, hs,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← hJ.1 l k, hs]; ring
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0, key, h]
  simp

end GlobalTheory.IwLine

namespace GlobalTheory.IwLine

open Classical in

theorem iwasawa_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ (x : Matrix (Fin n) (Fin 1) E), x = X.submatrix id (fun _ => 0) → ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), IsAdapted σ J X Y L a → (∀ g, ∃ p, ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x ∧ ∃ k ∈ levelAll σ J L a, g = p * k) ∧ ∃ h : GAd σ J → ℝ, ∀ p, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l := by
  intro F E _ _ _ _ _ σ hσ hun n J hJ r X Y hW x hx L a hA
  haveI : Submodule.IsLattice E L := hA.lat
  set y : Matrix (Fin n) (Fin 1) E := Y.submatrix id (fun _ => 0) with hy
  have hxx : cT (σ : E →+* E) x * J * x = 0 := by
    rw [hx, first_cols, hW.xx]; rfl
  have hyy : cT (σ : E →+* E) y * J * y = 0 := by
    rw [hy, first_cols, hW.yy]; rfl
  have hxy : cT (σ : E →+* E) x * J * y = 1 := by
    rw [hx, hy, first_cols, hW.xy]; ext i j; simp [Matrix.one_apply, Subsingleton.elim i j]
  have hyx : cT (σ : E →+* E) y * J * x = 1 := yx_of_xy σ J hσ hJ x y hxy
  have loc : ∀ v (g : GLoc σ J v), ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ g = q * k ∧
      ∃ β : GL (Fin 1) (Fv F v ⊗[F] E),
        (matHom _ σ J q).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1 := fun v g =>
    if hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v then
      GlobalTheory.T.hyperbolic_pair_lattice_local_split F E σ hσ n J hJ x y hxx hyy hxy hyx L hA.lat v hs (hA.dual v) g
    else GlobalTheory.T.isotropic_vector_lattice_local F E σ hσ hun n J hJ x y hxx hyx L hA.lat v hs (hA.dual v) g
  have iw : ∀ g : GAd σ J, ∃ p, ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x ∧
      ∃ k ∈ levelAll σ J L a, g = p * k := by
    intro g
    choose pf kf hkf hf βf hβf using fun v => loc v (proj σ J v g)
    choose pa ka hka ha βa hβa using fun w => GlobalTheory.T.archimedean_iwasawa_majorant_frame F E σ hσ n J hJ x y hxx hyx a hA.maj w (projArch σ J w g)
    have hS := eventually_proj_mem_stabLoc σ J L g
    set S := (Filter.eventually_cofinite.1 hS).toFinset with hSdef
    obtain ⟨qa, qa1, qa2⟩ := exists_arch_glue σ J pa Finset.univ
    obtain ⟨qf, qf1, qf2⟩ := exists_fin_glue σ J pf S
    have pa' : ∀ w, projArch σ J w (qa * qf) = pa w := fun w => by
      rw [map_mul, qa2 w, qf1 w, mul_one, if_pos (Finset.mem_univ w)]
    have pf' : ∀ v, proj σ J v (qa * qf) = if v ∈ S then pf v else 1 := fun v => by
      rw [map_mul, qa1 v, qf2 v, one_mul]
    obtain ⟨l, hl⟩ := GlobalTheory.T.parabolic_archimedean_eigenvector F E σ n J x (cT (σ : E →+* E) y * J) hyx (qa * qf)
      (fun w => ⟨βa w, by rw [pa' w]; exact hβa w⟩) (fun v => by
        rw [pf' v]
        split_ifs
        · exact ⟨βf v, hβf v⟩
        · exact ⟨1, by simp⟩)
    refine ⟨qa * qf, l, hl, (qa * qf)⁻¹ * g, mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩,
      (mul_inv_cancel_left (qa * qf) g).symm⟩
    · rw [map_mul, map_inv, pf' v]
      split_ifs with h
      · rw [hf v, inv_mul_cancel_left]; exact hkf v
      · rw [inv_one, one_mul]
        by_contra hc
        exact h ((Set.Finite.mem_toFinset _).2 hc)
    · rw [map_mul, map_inv, pa' w, ha w, inv_mul_cancel_left]
      exact hka w
  refine ⟨iw, fun g => (absE F E (iw g).choose_spec.choose : ℝ), fun p l hp k hk => ?_⟩
  obtain ⟨hp', k', hk', e⟩ := (iw (p * k)).choose_spec.choose_spec
  set p' := (iw (p * k)).choose
  set l' := (iw (p * k)).choose_spec.choose
  have hK : p'⁻¹ * p ∈ levelAll σ J L a := by
    have : p'⁻¹ * p = k' * k⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, e, inv_mul_cancel_left]
    rw [this]; exact mul_mem hk' (inv_mem hk)
  have hm : (matHom _ σ J (p'⁻¹ * p)).1 * adMat F x = (l * l'⁻¹).1 • adMat F x := by
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, hp, Matrix.mul_smul, map_inv,
      inv_mul_eq_smul _ _ _ hp', smul_smul, Units.val_mul]
  have h1 := GlobalTheory.T.level_subgroup_adjoint_scalar F E σ hσ n J L hA.lat a x (cT (σ : E →+* E) y * J) hyx _ hK _ hm
  rw [map_mul, map_inv, mul_inv_eq_one₀ (GlobalTheory.Doubling.hom_pos _ _).ne'] at h1
  show (absE F E l' : ℝ) = absE F E l
  rw [h1]

end GlobalTheory.IwLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanPhaseSpaceCoordinatesFramesStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedean_phaseSpace_coordinates_frames : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → Framed τ JA JB a b A C →
    ∃ (n : ℕ) (θ : (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (φ : (InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ))
      (φ₀ : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v, GlobalTheory.RealWeil.pPart (φ₀ v) = θ v.1) ∧ (∀ v y, ⟪GlobalTheory.RealWeil.qPart (φ₀ v), θ y⟫ = -GlobalTheory.ArchUniq.trP F κ y v.2) ∧
      (∀ c c', GlobalTheory.RealWeil.sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) ∧
      ∀ (u : Matrix α β (AE F E)) (c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ), At (evI F) u →
        (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
          φ c = φ₀ (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) := by
  first | exact @GlobalTheory.ArchCoords.exists_coords | exact GlobalTheory.ArchCoords.exists_coords | (intros; apply GlobalTheory.ArchCoords.exists_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanPhaseSpaceCoordinatesPlaceSignaStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedean_phaseSpace_coordinates_placeSignatures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → FramedD τ JA JB a b A C →
    ∃ (n : ℕ) (θ : (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (φ : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ))
      (φ₀ : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v, GlobalTheory.RealWeil.pPart (φ₀ v) = θ v.1) ∧ (∀ v y, ⟪GlobalTheory.RealWeil.qPart (φ₀ v), θ y⟫ = -GlobalTheory.ArchUniq.trP F κ y v.2) ∧
      (∀ c c', GlobalTheory.RealWeil.sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) ∧
      ∀ (u : Matrix α β (AE F E)) (c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ), At (evI F) u →
        (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
          φ c = φ₀ (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) := by
  first | exact @GlobalTheory.ArchCoordsD.exists_coords | exact GlobalTheory.ArchCoordsD.exists_coords | (intros; apply GlobalTheory.ArchCoordsD.exists_coords <;> assumption)
end

