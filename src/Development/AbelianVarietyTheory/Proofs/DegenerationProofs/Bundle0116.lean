import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyBiTrivOfIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SurjectiveCubeOfGeneric
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BiTrivLiftOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0041
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDescendThrough
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapDescends
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0102

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyFormalUniformisationTower
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.FormalTower

theorem exists_tq_lift {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] (φ : A →+* A')
    (hφ : Function.Surjective φ) (hn : IsNilpotent (RingHom.ker φ)) {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (G₀ : Over (Sp A')) [GrpObj G₀]
    (F : G₀.left ⟶ G.left) (hF : IsGrpPullback G₀ G (spMap φ) F) (Q₀ : TQ G₀ X) :
    ∃ Q : TQ G X, TorusCompat (spMap φ) F Q₀.i Q.i := by
  let e := RingHom.quotientKerEquivOfSurjective hφ
  let r : Sp (A ⧸ RingHom.ker φ) ⟶ Sp A' := spMap e.symm.toRingHom
  let s : Sp A' ⟶ Sp (A ⧸ RingHom.ker φ) := spMap e.toRingHom
  have hr : r ≫ spMap φ = red (RingHom.ker φ) := by
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact e.symm_apply_eq.2 rfl
  have hs : s ≫ r = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    exact e.apply_symm_apply a
  have h₁ := isGrpPullback_pullback G₀ r
  obtain ⟨Q₁, c₁⟩ := exists_tq_baseChange _ _ _ X _ _ _ h₁ Q₀
  obtain ⟨Q, c⟩ := TorusQuotLift.main A _ hn X G _ _ ((h₁.comp hF).congr hr rfl) Q₁
  refine ⟨Q, ?_⟩
  rw [torusCompat_iff] at c c₁ ⊢
  rw [← hr, bcMap_comp, ← Category.assoc, ← c₁, Category.assoc, Category.assoc] at c
  have c' := congrArg (SplitTorus.bcMap s X ≫ ·) c
  simp only [← Category.assoc, ← bcMap_comp, hs, bcMap_id, Category.id_comp] at c'
  exact c'

theorem isCPPullback_of_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G]
    [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] {P : CP G} {P' : CP G'}
    {P'' : CP G''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {f'' : S'' ⟶ S} {F : G'.left ⟶ G.left} {F' : G''.left ⟶ G'.left}
    {F'' : G''.left ⟶ G.left} (h : IsCPPullback P' P f F) (h'' : IsCPPullback P'' P f'' F'')
    (hF : IsGrpPullback G'' G' f' F') (e : f' ≫ f = f'') (e' : F' ≫ F = F'') : IsCPPullback P'' P' f' F' := by
  obtain ⟨_, _, h⟩ := h
  obtain ⟨_, _, h''⟩ := h''
  exact ⟨hF, TowerEx.exists_cancel h h'' hF e e'⟩

theorem exists_isCPPullback_desc {S S' : Scheme.{0}} [ConnectedSpace S'] {f : S' ⟶ S} {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    [ConnectedSpace G'.left] {F : G'.left ⟶ G.left} {P : CP G} {P' : CP G'} (hP : IsCPPullback P' P f F)
    {Q : TQ G X} {Q' : TQ G' X} (h : TorusCompat f F Q'.i Q.i) (D : Q.Desc P) (D' : Q'.Desc P') :
    ∃ β : Q'.B.left ⟶ Q.B.left, IsCPPullback D'.M D.M f β ∧ Q'.q.left ≫ β = F ≫ Q.q.left := by
  obtain ⟨hF, _, hP⟩ := hP
  exact TowerEx.exists_transition hF hP h D D'

section Level

variable {R : Type} [CommRing R] (I : Ideal R) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]

theorem isGrpPullback_thickMap (e : ℕ) :
    IsGrpPullback (thickObj R I e G) (thickObj R I (e + 1) G) (thickTrans R I e) (thickMap R I e G) :=
  (isGrpPullback_pullback G (thick R I (e + 1))).cancel
    ((isGrpPullback_pullback G (thick R I e)).congr (thickTrans_comp R I e).symm
      ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm) (pullback.lift_snd _ _ _)

theorem isNilpotent_of_le_map (n : ℕ) (J : Ideal (R ⧸ I ^ n)) (hJ : J ≤ I.map (Ideal.Quotient.mk (I ^ n))) :
    IsNilpotent J := by
  refine ⟨n, le_bot_iff.1 ((Ideal.pow_right_mono hJ n).trans ?_)⟩
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

variable {I}

theorem pow_succ_ne_top (hI : I ≠ ⊤) (e : ℕ) : I ^ (e + 1) ≠ ⊤ := fun h =>
  hI (top_le_iff.1 (h.symm.le.trans (Ideal.pow_le_self (Nat.succ_ne_zero e))))

theorem isLocalRing_quot [IsLocalRing R] (hI : I ≠ ⊤) (e : ℕ) : IsLocalRing (R ⧸ I ^ (e + 1)) :=
  have := Ideal.Quotient.nontrivial_iff.2 (pow_succ_ne_top hI e)
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

theorem connectedSpace_sp (A : Type) [CommRing A] [IsLocalRing A] : ConnectedSpace (Sp A) :=
  SplitTorus.connectedSpace_of_isLocalRing A

theorem exists_tq_succ [IsLocalRing R] [IsCommMonObj G] (hI : I ≠ ⊤) (hG : IsSemiAbelian G) {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (e : ℕ) (Q₀ : TQ (thickObj R I e G) X) :
    ∃ Q : TQ (thickObj R I (e + 1) G) X, TorusCompat (thickTrans R I e) (thickMap R I e G) Q₀.i Q.i := by
  have := isLocalRing_quot hI (e + 1)
  have := (IsSemiAbelian.pullback (thick R I (e + 1)) G hG).smooth
  refine exists_tq_lift _ (Ideal.Quotient.factor_surjective _) (isNilpotent_of_le_map I _ _ fun x hx => ?_) _ _ _
    (isGrpPullback_thickMap I G e) Q₀
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact Ideal.mem_map_of_mem _ (Ideal.pow_le_self (Nat.succ_ne_zero e) (Ideal.Quotient.eq_zero_iff_mem.1 hx))

theorem nonempty_biTriv (h₁ : Laws) (h₂ : Laws2) [IsLocalRing R] [IsNoetherianRing R] [IsCommMonObj G] [I.IsPrime]
    [IsIntegrallyClosed (R ⧸ I)] (hG : IsSemiAbelian G) {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (e : ℕ) (Q : TQ (thickObj R I e G) X) (P : CP (thickObj R I e G)) :
    Nonempty (BiTriv P.c Q.i) := by
  let J := I.map (Ideal.Quotient.mk (I ^ (e + 1)))
  let ε : ((R ⧸ I ^ (e + 1)) ⧸ J) ≃+* R ⧸ I :=
    DoubleQuot.quotQuotEquivQuotOfLE (Ideal.pow_le_self (Nat.succ_ne_zero e))
  have : IsDomain ((R ⧸ I ^ (e + 1)) ⧸ J) := ε.toMulEquiv.isDomain _
  have : IsIntegrallyClosed ((R ⧸ I ^ (e + 1)) ⧸ J) := IsIntegrallyClosed.of_equiv ε.symm
  have h₀ := IsSemiAbelian.pullback (red J) _ (IsSemiAbelian.pullback (thick R I e) G hG)
  have := h₀.smooth
  have := h₀.geomConnected
  have := h₀.comm
  have : ConnectedSpace (Sp ((R ⧸ I ^ (e + 1)) ⧸ J)) := inferInstance
  have := (GroupConn.connectedSpace_group _ ((Over.pullback (red J)).obj (thickObj R I e G))).1
  have hp := isGrpPullback_pullback (thickObj R I e G) (red J)
  obtain ⟨Q₀, c⟩ := exists_tq_baseChange _ _ _ X _ _ _ hp Q
  obtain ⟨P₀, w, hw⟩ := exists_pull P (TowerEx.toBase_mul hp hp.1.w)
  exact biTriv_lift_of_isNilpotent _ J (isNilpotent_of_le_map I _ _ le_rfl) X _ _ _ _ hp P P₀ w hw _ _ Q.i_hom Q₀.i_hom c
    (BiextTriv.nonempty_biTriv_normal h₁ h₂ _ X _ _ _ _ Q₀.i_hom)

theorem exists_even (h₁ : Laws) (h₂ : Laws2) [IsDomain R] [IsCommMonObj G]
    (P : CP G) (hG : IsSemiAbelian G) (hp : IsProper (pullback.snd G.hom (jK R))) (hW : HypW G P.L.L)
    {X : Type} [AddCommGroup X] (e : ℕ) (Q : TQ (thickObj R I e G) X) (P' : CP (thickObj R I e G))
    (h : IsLevelCP I e P' P) (b : Nonempty (BiTriv P'.c Q.i)) : ∃ σ : CubTriv P'.c Q.i, σ.Even := by
  obtain ⟨w, -, hw, -, -, hL, -⟩ := hW
  obtain ⟨v, hv⟩ := h
  exact EvenTriv.exists_even_cubTriv h₁ h₂ R G hG hp P w hw hL _ _ X Q P' _ _
    (isGrpPullback_pullback G (thick R I e)).1 v hv b

theorem connectedSpace_thickObj [IsLocalRing R] (hI : I ≠ ⊤) (hG : IsSemiAbelian G) (e : ℕ) :
    ConnectedSpace (thickObj R I e G).left := by
  have := isLocalRing_quot hI e
  have := connectedSpace_sp (R ⧸ I ^ (e + 1))
  have h₀ := IsSemiAbelian.pullback (thick R I e) G hG
  have := h₀.smooth
  have := h₀.geomConnected
  exact (GroupConn.connectedSpace_group _ (thickObj R I e G)).1

omit [GrpObj G] in

theorem thickMap_fst (e : ℕ) :
    thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem isCPPullback_thick [IsDomain R] [IsCommMonObj G] {P : CP G} {e : ℕ} {P' : CP (thickObj R I e G)}
    (h : IsLevelCP I e P' P) : IsCPPullback P' P (thick R I e) (pullback.fst G.hom (thick R I e)) :=
  ⟨isGrpPullback_pullback G _, h⟩

theorem isCPPullback_thickMap [IsDomain R] [IsCommMonObj G] {P : CP G} {e : ℕ} {P' : CP (thickObj R I e G)}
    {P'' : CP (thickObj R I (e + 1) G)} (h' : IsLevelCP I e P' P) (h'' : IsLevelCP I (e + 1) P'' P) :
    IsCPPullback P' P'' (thickTrans R I e) (thickMap R I e G) :=
  isCPPullback_of_comp (isCPPullback_thick G h'') (isCPPullback_thick G h') (isGrpPullback_thickMap I G e)
    (thickTrans_comp R I e) (thickMap_fst G e)

theorem exists_isCPPullback [IsDomain R] [IsLocalRing R] [IsCommMonObj G] (hI : I ≠ ⊤) (hG : IsSemiAbelian G) {P : CP G}
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] {e : ℕ} (l : Lev I P X e) (l' : Lev I P X (e + 1))
    (c : TorusCompat (thickTrans R I e) (thickMap R I e G) l.Q.i l'.Q.i) :
    ∃ β : l.Q.B.left ⟶ l'.Q.B.left, IsCPPullback l.D.M l'.D.M (thickTrans R I e) β ∧
      l.Q.q.left ≫ β = thickMap R I e G ≫ l'.Q.q.left :=
  have := isLocalRing_quot hI e
  have := connectedSpace_sp (R ⧸ I ^ (e + 1))
  have := connectedSpace_thickObj G hI hG e
  exists_isCPPullback_desc (isCPPullback_thickMap G l.lev l'.lev) c l'.D l.D

end Level

theorem nonempty_towerR : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → IsProper (pullback.snd G.hom (jK R)) → SplitOver G I → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X), Nonempty (TowerR I P X) := by
  intro h₁ h₂ R _ _ _ I ⟨⟨hN, _⟩, _, _, hI, hC⟩ G _ _ P hG hW hp ⟨E, ⟨d⟩⟩
  have hI' := hI.ne_top
  have := E.free
  have := E.finite
  refine ⟨E.X, inferInstance, inferInstance, inferInstance, ?_⟩
  obtain ⟨Q₁, -⟩ := exists_tq_of_gtDatum _ E _ d
  let r : Sp (R ⧸ I ^ (0 + 1)) ⟶ Sp (R ⧸ I) := spMap (Ideal.Quotient.factor (show I ≤ I ^ (0 + 1) by simp))
  have hr : r ≫ spMap (Ideal.Quotient.mk I) = thick R I 0 := by
    rw [← Spec.map_comp]
    rfl
  let F : (thickObj R I 0 G).left ⟶ ((Over.pullback (spMap (Ideal.Quotient.mk I))).obj G).left :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ r) (by rw [Category.assoc, hr]; exact pullback.condition)
  obtain ⟨Q₀, -⟩ := exists_tq_baseChange _ _ r E.X _ _ F ((isGrpPullback_pullback G _).cancel
    ((isGrpPullback_pullback G (thick R I 0)).congr hr.symm (pullback.lift_fst _ _ _).symm)
    (pullback.lift_snd _ _ _)) Q₁
  choose nx hnx using fun e => exists_tq_succ (I := I) (X := E.X) G hI' hG e
  let Q : ∀ e, TQ (thickObj R I e G) E.X := fun e => Nat.rec Q₀ nx e
  have hQ : ∀ e, TorusCompat (thickTrans R I e) (thickMap R I e G) (Q e).i (Q (e + 1)).i := fun e => hnx e (Q e)
  choose Pe hPe using fun e => exists_isLevelCP I e P
  have hD : ∀ e, Nonempty ((Q e).Desc (Pe e)) := fun e => by
    have := isLocalRing_quot hI' e
    have := connectedSpace_sp (R ⧸ I ^ (e + 1))
    have := connectedSpace_thickObj G hI' hG e
    have b := nonempty_biTriv G h₁ h₂ hG e (Q e) (Pe e)
    exact nonempty_desc _ E.X _ (Q e) (Pe e) b
      (exists_even G h₁ h₂ P hG hp hW e (Q e) (Pe e) (hPe e) b)
  let l : ∀ e, Lev I P E.X e := fun e => ⟨Q e, Pe e, hPe e, (hD e).some⟩
  choose β hβ hq using fun e => exists_isCPPullback G hI' hG (l e) (l (e + 1)) (hQ e)
  exact ⟨⟨l, hQ, β, hβ, hq⟩⟩

end GlobalTheory.FormalTower

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestModelMapsIntoOpenPart
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.TestInOpen

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem proj_bot {T : AddSubgroup S.Gam} (h : T = ⊥) : S.proj T 0 = 1 := by
  subst h
  unfold ThetaSys.proj
  rw [finsum_unique, S.ρ_one _ (by rw [AddSubgroup.mem_bot.1 (Subtype.prop _), smul_zero])]
  simp

variable {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem exists_crd_ne_zero (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) {K : Type} [Field K]
    (x : Sp K ⟶ Q.P.left) {z : M.Z} (hz : Set.range (x ≫ Q.P.hom) = {z}) (hc : z ∈ U₀) :
    ∃ v, Crd Q.O1 Q.st x v ∧ v ≠ 0 := by
  have hxz : ∀ s, Q.P.hom (x s) = z := fun s => by
    have : (x ≫ Q.P.hom) s ∈ Set.range (x ≫ Q.P.hom) := ⟨_, rfl⟩
    rw [hz] at this
    exact this
  obtain ⟨l, hl⟩ : ∃ l, z ∈ Q.W l := TopologicalSpace.Opens.mem_iSup.1 (by rw [Q.cover]; trivial)
  have hr : Set.range x ⊆ Set.range (Q.P.hom ⁻¹ᵁ Q.W l).ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    change Q.P.hom (x s) ∈ Q.W l
    rwa [hxz]
  obtain ⟨x', rfl⟩ : ∃ x', x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι = x :=
    ⟨_, IsOpenImmersion.lift_fac _ x hr⟩
  have hcov := (Q.imm l).1
  have hm : x' (IsLocalRing.closedPoint K) ∈ ⨆ i ∈ (Set.univ : Set S.J), nonzeroLocus (Q.σ l i) := by
    rw [hcov]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hm
  obtain ⟨i, -, hi⟩ := hm
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  obtain ⟨w, hw⟩ : ∃ w, Crd _ (Q.σ l) x' w :=
    ⟨_, m, 1, (CrdCalc.top_le_iff x' _).2 (Scheme.basicOpen_le _ _ hm), fun _ => rfl⟩
  have hwi := ((CrdCalc.crd_isUnit_iff i hw).2 ((CrdCalc.top_le_iff x' _).2 hi)).ne_zero
  refine ⟨_, Q.rel l K x' _ hw, fun h0 => hwi ?_⟩
  have hBm : ∀ a b, Q.B l a b ∈ M.O z := fun a => (RatModel.Lat.mem_const_iff M).1 (by
    rw [RatModel.Lat.const_E, ← hB.ee.1 z hc, Q.basis l z hl]
    exact Submodule.subset_span ⟨a, rfl⟩)
  let B' : Matrix S.J S.J (M.O z) := fun a b => ⟨_, hBm a b⟩
  let C' : Matrix S.J S.J (M.O z) := fun a b => ⟨_, RatModel.valF_mem_O hl (Q.c l a b)⟩
  have h1 : C' * B' = 1 := by
    apply Matrix.map_injective (f := (M.O z).val.toRingHom) Subtype.val_injective
    beta_reduce
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Q.c_inv l
  have h2 := congrArg (fun A => A.map (RatModel.valHom _ z hz)) (mul_eq_one_comm.1 h1)
  beta_reduce at h2
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  have h3 : C'.map (RatModel.valHom _ z hz) =
      (Q.c l).map (valR (x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (Q.W l)) := by
    ext a b
    rw [← Category.assoc]
    exact RatModel.val_valF (by rw [hz]; exact Set.singleton_subset_iff.2 hl) _
  have h4 : w = 0 := by
    rw [← Matrix.one_mulVec w, ← h2, ← Matrix.mulVec_mulVec, h3, h0, Matrix.mulVec_zero]
  rw [h4]; rfl

theorem mem_G_of_mem [ArithBase o Ω] (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) (w : Q.P.left)
    (hc : Q.P.hom w ∈ U₀) : w ∈ Q.G := by
  let x : Sp (Q.P.left.residueField w) ⟶ Q.P.left := Q.P.left.fromSpecResidueField w
  have hx : ∀ s, x s = w := fun s => Scheme.fromSpecResidueField_apply w s
  have hz : Set.range (x ≫ Q.P.hom) = {Q.P.hom w} := by
    rw [RatModel.range_eq_singleton _ (IsLocalRing.closedPoint _)]
    exact congrArg (fun a => {Q.P.hom a}) (hx _)
  obtain ⟨v, hv, hv0⟩ := exists_crd_ne_zero hB Q x hz hc
  have h := (OpenPart.le_preimage_G_iff o Ω S ρ M U₀ EE hB Q _ x _
    (Spec.preimage (x ≫ Q.P.hom ≫ M.s)).hom v hz (Or.inr hc) (Spec.map_preimage _).symm hv).2 (by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
      refine ⟨i, ?_⟩
      rw [proj_bot (hB.gen _ hc), Finset.sum_eq_single i]
      · simpa using hi
      · intro j _ hj
        simp [hj]
      · simp)
  rw [← hx (IsLocalRing.closedPoint _)]
  exact (CrdCalc.top_le_iff x _).1 h

theorem big_of_big (ρ : S.Real) (h : S.Big) : Big S.g S.N (S.r * S.N) := by
  refine ⟨?_, h.1, h.2.1⟩
  have h1 : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
  rw [ρ.N_eq]
  nlinarith

variable {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p}

theorem isLocalHom_j (u : ρ.UTest p y₀) : IsLocalHom u.j := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  have hb' : algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ a) * b = 1 := congrArg Subtype.val hb
  have h0 : algebraMap u.V (FractionRing u.V) a ≠ 0 := fun h => by simp [h] at hb'
  obtain ⟨c, hc⟩ := (u.norm_le (algebraMap u.V _ a)⁻¹).1 (by
    rw [map_inv₀, ← eq_inv_of_mul_eq_one_right hb']
    exact (mem_OO_iff _).1 b.2)
  refine IsUnit.of_mul_eq_one c (IsFractionRing.injective u.V (FractionRing u.V) ?_)
  rw [map_mul, hc, mul_inv_cancel₀ h0, map_one]

theorem mem_range_or (u : ρ.UTest p y₀) (s : Sp u.V) :
    s ∈ Set.range (jK u.V) ∨ s ∈ Set.range (rPt p ≫ spMap u.j) := by
  by_cases h : s.asIdeal = ⊥
  · refine Or.inl ⟨(⊥ : PrimeSpectrum (FractionRing u.V)), PrimeSpectrum.ext ?_⟩
    rw [h]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective u.V (FractionRing u.V))
  · have := isLocalHom_j u
    refine Or.inr ⟨IsLocalRing.closedPoint (kb p), ?_⟩
    have e₁ : rPt p (IsLocalRing.closedPoint (kb p)) = cPt p :=
      IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))
    have e₂ : spMap u.j (cPt p) = IsLocalRing.closedPoint u.V := IsLocalRing.comap_closedPoint u.j
    refine ((congrArg (spMap u.j) e₁).trans e₂).trans ?_
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime h s.isPrime)).symm

theorem top_le_preimage_G : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ⊤ ≤ (tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ⁻¹ᵁ Q.G := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q p _ y y₀ t c tm hS x _
  rcases mem_range_or t.u (t.u.G.hom x) with ⟨s, hs⟩ | ⟨s, hs⟩
  · refine mem_G_of_mem hB Q _ ?_
    have e₁ : Q.P.hom ((tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) x) = c.yV (t.u.G.hom x) := by
      rw [← Scheme.Hom.comp_apply, Category.assoc, tm.f_over, Scheme.Hom.comp_apply]
    have e₂ : c.yV (jK t.u.V s) = U₀.ι (c.yK s) := by
      rw [← Scheme.Hom.comp_apply, ← c.yK_fac, Scheme.Hom.comp_apply]
    show Q.P.hom ((tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) x) ∈ U₀
    rw [e₁, ← hs, e₂]
    exact (c.yK s).2
  · haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
    have pb : IsPullback t.mod.r t.mod.Φ.G.hom t.u.G.hom (rPt p ≫ spMap t.u.j) := t.mod.cart.1
    obtain ⟨x', rfl, -⟩ := Scheme.exists_preimage_of_isPullback pb x s hs.symm
    have hsm : SmoothOfRelativeDimension S.g t.mod.Φ.G.hom :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback pb t.mod.smooth
    have : Smooth t.mod.Φ.G.hom := SmoothOfRelativeDimension.smooth S.g _
    have : JacobsonSpace t.mod.Φ.G.left := LocallyOfFiniteType.jacobsonSpace t.mod.Φ.G.hom
    have hcov := (GlobalTheory.T.immBy_weight_zero' hL.1 hL.2.1 (kb p) t.mod.Φ S.g S.N _ _ S.J _ t.mod.F t.mod.pol (big_of_big ρ hS)
      t.mod.good t.mod.dim).1
    let U : t.mod.Φ.G.left.Opens := t.mod.r ⁻¹ᵁ ((tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ⁻¹ᵁ Q.G)
    by_contra hx
    obtain ⟨a, haU, ha⟩ := nonempty_inter_closedPoints (Z := (U : Set t.mod.Φ.G.left)ᶜ) ⟨x', hx⟩
      U.isOpen.isClosed_compl.isLocallyClosed
    let x₀ := pointOfClosedPoint (K := kb p) t.mod.Φ.G.hom a ha
    have h₂ : x₀ ≫ t.mod.Φ.G.hom = 𝟙 _ := pointOfClosedPoint_comp _ a ha
    have h₃ : x₀ (IsLocalRing.closedPoint (kb p)) = a := pointOfClosedPoint_apply _ a ha _
    obtain ⟨v, hv⟩ := CrdCalc.crd_exists (R := kb p) (t.mod.Φ.H_isLB 1) t.mod.F x₀
    have hmem : x₀ (IsLocalRing.closedPoint (kb p)) ∈
        ⨆ i ∈ {i | t.mod.xe.symm (t.cls i) = 0}, Out.nonzeroLocus (t.mod.F i) := by
      rw [hcov]; trivial
    simp only [TopologicalSpace.Opens.mem_iSup] at hmem
    obtain ⟨i, hi, hm⟩ := hmem
    have h₄ := ((CrdCalc.crd_isUnit_iff i hv).2 ((CrdCalc.top_le_iff _ _).2 hm)).ne_zero
    have h₁ : (x₀ ≫ t.mod.r) ≫ t.u.G.hom = rPt p ≫ spMap t.u.j := by
      rw [Category.assoc, pb.w, ← Category.assoc, h₂]
      exact Category.id_comp _
    have hcr := tm.crd (kb p) ((IsLocalRing.residue (OO p)).comp t.u.j) _ v
      (h₁.trans (Spec.map_comp _ _).symm) (t.mod.red (Over.homMk x₀ h₂) v hv)
    have hov : ((x₀ ≫ t.mod.r) ≫ tm.f) ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y := by
      rw [Category.assoc, tm.f_over, ← Category.assoc, h₁, Category.assoc, c.fac]
    have key := (GlobalTheory.T.le_preimage_openPart_iff_testCoordinates o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS _ v hov hcr).2
      ⟨i, t.mod.xe.symm.map_eq_zero_iff.1 hi, h₄⟩
    refine haU ?_
    rw [← h₃]
    exact key (x := IsLocalRing.closedPoint (kb p)) trivial

end GlobalTheory.ZH.TestInOpen
end

