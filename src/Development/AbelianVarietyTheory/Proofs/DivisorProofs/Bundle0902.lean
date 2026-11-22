import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0874
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0880
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0881
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGroupMatrixIsomorphism
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

namespace GlobalTheory.GeoActCompare

theorem exists_glEquiv_of_surjective {A R M : Type} [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup M]
    [Module A M] [Module R M] [IsScalarTower A R M] (hs : Function.Surjective (algebraMap A R)) {r : ℕ}
    (φ : M ≃ₗ[A] (Fin r → R)) :
    ∃ θ : GL (Fin r) R ≃* (M ≃ₗ[A] M), (∀ g q, φ (θ g q) = g.1.mulVec (φ q)) ∧
      ∀ g, LinearEquiv.det ((θ g).extendScalarsOfSurjective hs) = Matrix.GeneralLinearGroup.det g := by
  let e : M ≃ₗ[R] (Fin r → R) := φ.extendScalarsOfSurjective hs
  let t : GL (Fin r) R ≃* ((Fin r → R) ≃ₗ[R] (Fin r → R)) :=
    Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv R (Fin r → R))
  have ht : ∀ g v, t g v = g.1.mulVec v := fun g v => rfl
  let c : ((Fin r → R) ≃ₗ[R] (Fin r → R)) ≃* (M ≃ₗ[A] M) :=
    { toFun := fun f => (e ≪≫ₗ f ≪≫ₗ e.symm).restrictScalars A
      invFun := fun f => e.symm ≪≫ₗ f.extendScalarsOfSurjective hs ≪≫ₗ e
      left_inv := fun f => by
        ext1 v
        show e (e.symm (f (e (e.symm v)))) = f v
        simp
      right_inv := fun f => by
        ext1 v
        show e.symm (e (f (e.symm (e v)))) = f v
        simp
      map_mul' := fun f g => by
        ext1 v
        show e.symm (f (g (e v))) = e.symm (f (e (e.symm (g (e v)))))
        simp }
  refine ⟨t.trans c, fun g q => ?_, fun g => ?_⟩
  · show e (e.symm (t g (e q))) = _
    rw [e.apply_symm_apply, ht]
    rfl
  · have h : (((t.trans c) g).extendScalarsOfSurjective hs : M →ₗ[R] M) =
        (e.symm : (Fin r → R) →ₗ[R] M) ∘ₗ Matrix.toLin' g.1 ∘ₗ (e.symm.symm : M →ₗ[R] (Fin r → R)) := by
      ext1 v
      rfl
    ext1
    rw [LinearEquiv.coe_det, h, LinearMap.det_conj, LinearMap.det_toLin']
    rfl

theorem exists_glEquiv_pi {R ι : Type} [CommRing R] {k : ι → Type} [∀ i, CommRing (k i)] (c : R ≃+* ∀ i, k i)
    (r : ℕ) :
    ∃ θ : (∀ i, GL (Fin r) (k i)) ≃* GL (Fin r) R, ∀ g i a b, c ((θ g).1 a b) i = (g i).1 a b := by
  let m : Matrix (Fin r) (Fin r) R ≃+* ∀ i, Matrix (Fin r) (Fin r) (k i) :=
    c.mapMatrix.trans Matrix.piRingEquiv
  refine ⟨MulEquiv.piUnits.symm.trans (Units.mapEquiv m.toMulEquiv).symm, fun g i a b => ?_⟩
  show m (m.symm (fun j => (g j).1)) i a b = _
  rw [m.apply_symm_apply]

theorem exists_levGrp_equiv_pi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Pg : Finset (Formalism.L2.DIV.Pl E)), l.Mb = ∏ w ∈ Pg, w.asIdeal → ∀ (hle : ∀ w : ↥Pg, l.Mb ≤ w.1.asIdeal) (r : ℕ) (φ : LaMod Dw l ≃ₗ[𝓞 E] (Fin r → 𝓞 E ⧸ l.Mb)), ∃ ψ : Formalism.L2.DIV.G0 Pg r ≃* LevelLiftConditions.LevGrp Dw l, (∀ (g : Formalism.L2.DIV.G0 Pg r) (Y : Matrix (Fin r) (Fin r) (𝓞 E ⧸ l.Mb)), (∀ q, φ (ψ g q) = Y.mulVec (φ q)) ↔ ∀ w : ↥Pg, Y.map (Ideal.Quotient.factor (hle w)) = (g w).1) ∧ ∀ (g : Formalism.L2.DIV.G0 Pg r) (w : ↥Pg), Units.map (Ideal.Quotient.factor (hle w)).toMonoidHom (LevelLiftConditions.levDet Dw l (ψ g)) = Matrix.GeneralLinearGroup.det (g w) := by
  intro E _ _ _ H Dw l Pg hP hle r φ
  obtain ⟨θ, h1, h2⟩ := exists_glEquiv_of_surjective (A := 𝓞 E) (R := 𝓞 E ⧸ l.Mb) (M := LaMod Dw l)
    Ideal.Quotient.mk_surjective φ
  obtain ⟨η, h3⟩ := exists_glEquiv_pi (crt hP hle) r
  have h4 : ∀ (g : Formalism.L2.DIV.G0 Pg r) (w : ↥Pg), (η g).1.map (Ideal.Quotient.factor (hle w)) = (g w).1 :=
    fun g w => Matrix.ext fun a b => h3 g w a b
  refine ⟨η.trans θ, fun g Y => ?_, fun g w => ?_⟩
  · have h5 : ∀ q, φ ((η.trans θ) g q) = (η g).1.mulVec (φ q) := fun q => h1 (η g) q
    constructor
    · intro h w
      have : Y = (η g).1 := by
        apply Matrix.toLin'.injective
        refine LinearMap.ext fun v => ?_
        obtain ⟨q, rfl⟩ := φ.surjective v
        exact ((h q).symm.trans (h5 q))
      rw [this]
      exact h4 g w
    · intro h q
      have : Y = (η g).1 := by
        refine Matrix.ext fun a b => (crt hP hle).injective (funext fun w => ?_)
        rw [h3 g w a b, ← h w]
        rfl
      rw [this]
      exact h5 q
  · have h6 : LevelLiftConditions.levDet Dw l ((η.trans θ) g) = Matrix.GeneralLinearGroup.det (η g) := h2 (η g)
    refine (congrArg _ h6).trans (Units.ext ?_)
    show Ideal.Quotient.factor (hle w) (η g).1.det = (g w).1.det
    rw [RingHom.map_det, ← h4 g w]
    rfl

end GlobalTheory.GeoActCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultIffFinrankCommonEigenspaceCoordsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieMult_iff_finrank_common_eigenspace_coords : ∀ (W : Type) [CommRing W] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (O : Type) [CommRing O] (act : OAct O G) (n : ℕ) (k : Type) [Field k] (β : W →+* k) (T : (Fin n → k) → (epsPtR (spMap β) ⟶ G)) (A : O → Matrix (Fin n) (Fin n) k), Function.Injective T → (∀ v : epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) → (∀ c c', T (c + c') = T c * T c') → (∀ (s : k) c, (T (s • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ (T c).left) → (∀ a c, T c ≫ act.act a = T ((A a).mulVec c)) → ∀ (τ : O →+* k) (N : ℕ), LieMult act (spMap β) τ N ↔ Module.finrank k (⨅ a, LinearMap.ker (Matrix.mulVecLin (A a) - τ a • LinearMap.id) : Submodule k (Fin n → k)) = N := by
  first | (exact @GlobalTheory.LieCoordMult.lieMult_iff_finrank_eig) | (exact GlobalTheory.LieCoordMult.lieMult_iff_finrank_eig) | (intros; apply GlobalTheory.LieCoordMult.lieMult_iff_finrank_eig  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftingObstructionEqOfCohomologousCocyclesStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lifting_obstruction_eq_of_cohomologous_cocycles : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (t : ∀ T : C, (F.obj T)ˣ) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsFun → (∀ T T' a, (u' T T' a : F.obj T') * mp F a (t T : F.obj T) = (t T' : F.obj T') * (u T T' a : F.obj T')) → IsObU L α u c → IsObU L α u' c := by
  first | exact @GlobalTheory.LBObs.isObU_of_cob | exact GlobalTheory.LBObs.isObU_of_cob | (intros; apply GlobalTheory.LBObs.isObU_of_cob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGlueOfOpenCoverCocycle
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PicGlue

variable {X : Scheme.{0}} {Ix : Type}

def sigmaGlue (W : Ix → X.Opens) (L : Ix → LB X) (w : ∀ i k, Cmp (W i ⊓ W k) (L i) (L k))
    (hL : ∀ i, IsOn (W i) (L i)) : LB X :=
  ⟨Σ i, (L i).ι, fun p ↦ (L p.1).U p.2,
    fun p q ↦ res (le_inf (inf_le_inf ((hL p.1).le p.2) ((hL q.1).le q.2)) le_rfl) (w p.1 q.1 p.2 q.2)⟩

theorem gm_sigmaGlue_g (W : Ix → X.Opens) (L : Ix → LB X) (w : ∀ i k, Cmp (W i ⊓ W k) (L i) (L k))
    (hL : ∀ i, IsOn (W i) (L i)) (x : X) (p q : (sigmaGlue W L w hL).ι)
    (hp : x ∈ (L p.1).U p.2) (hq : x ∈ (L q.1).U q.2) :
    gm (𝟙 X) x _ ((sigmaGlue W L w hL).g p q) = gm (𝟙 X) x _ (w p.1 q.1 p.2 q.2) :=
  gm_res (𝟙 X) x _ (show x ∈ (L p.1).U p.2 ⊓ (L q.1).U q.2 from ⟨hp, hq⟩) _

theorem lb_glue : ∀ (X : Scheme.{0}) (Ix : Type) (W : Ix → X.Opens) (L : Ix → LB X) (w : ∀ i k, Cmp (W i ⊓ W k) (L i) (L k)), (∀ x, ∃ i, x ∈ W i) → (∀ i, IsOn (W i) (L i)) → (∀ i k, IsoOn (W i ⊓ W k) (L i) (L k) (w i k)) → (∀ (i j k : Ix) (x : X) (a : (L i).ι) (b : (L j).ι) (c : (L k).ι), x ∈ (L i).U a → x ∈ (L j).U b → x ∈ (L k).U c → gm (𝟙 X) x _ (w i j a b) * gm (𝟙 X) x _ (w j k b c) = gm (𝟙 X) x _ (w i k a c)) → ∃ N : LB X, N.IsLB ∧ ∀ i, ∃ v : Cmp (W i) N (L i), IsoOn (W i) N (L i) v := by
  intro X Ix W L w hW hL hiso hcoc
  have hdiag : ∀ i (a : (L i).ι) (x : X), x ∈ (L i).U a → gm (𝟙 X) x _ (w i i a a) = 1 :=
    fun i a x ha ↦ mul_eq_left.1 (hcoc i i i x a a a ha ha ha)
  have hgi : ∀ i (x : X) (b b' : (L i).ι), x ∈ (L i).U b → x ∈ (L i).U b' → x ∈ W i →
      gm (𝟙 X) x _ ((L i).g b b') = gm (𝟙 X) x _ (w i i b b') := by
    intro i x b b' hb hb' hx
    have h1 := hiso i i x ⟨hx, hx⟩ b b b b' hb hb hb hb'
    have h2 : gm (𝟙 X) x _ ((L i).g b b) = 1 := mul_eq_left.1 ((hL i).coc x b b b hb hb hb)
    rw [hdiag i b x hb, _root_.one_mul, h2, _root_.one_mul] at h1
    exact h1
  have hg := gm_sigmaGlue_g W L w hL
  refine ⟨sigmaGlue W L w hL, ⟨?_, ?_, ?_⟩, fun i ↦ ⟨fun p b ↦ res (le_inf (le_inf
    (inf_le_right.trans (inf_le_left.trans ((hL p.1).le p.2))) inf_le_left) inf_le_right) (w p.1 i p.2 b), ?_⟩⟩
  · refine eq_top_iff.2 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2 ?_
    obtain ⟨i, hi⟩ := hW x
    obtain ⟨a, ha⟩ := (hL i).cov x hi
    exact ⟨⟨i, a⟩, ha⟩
  · intro p
    refine unit_ext fun x hx ↦ ?_
    rw [gm_res (𝟙 X) x _ hx, map_one, hg x p p hx hx, hdiag p.1 p.2 x hx]
  · intro p q r
    refine unit_ext fun x hx ↦ ?_
    rw [map_mul, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx,
      hg x p q hx.1.1 hx.1.2, hg x q r hx.1.2 hx.2, hg x p r hx.1.1 hx.2]
    exact hcoc _ _ _ x _ _ _ hx.1.1 hx.1.2 hx.2
  · intro x hx p p' b b' hp hp' hb hb'
    beta_reduce
    erw [gm_res (𝟙 X) x _ (show x ∈ W i ⊓ ((sigmaGlue W L w hL).U p ⊓ (L i).U b) from ⟨hx, hp, hb⟩),
      gm_res (𝟙 X) x _ (show x ∈ W i ⊓ ((sigmaGlue W L w hL).U p' ⊓ (L i).U b') from ⟨hx, hp', hb'⟩),
      hg x p p' hp hp', hgi i x b b' hb hb' hx, hcoc _ _ _ x _ _ _ hp hb hb', hcoc _ _ _ x _ _ _ hp hp' hb']

end GlobalTheory.PicGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullOfIsLineBundleIsoOnOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem isoOn_gm {X Z : Scheme.{0}} {W : X.Opens} {L M : LB X} {w : Cmp W L M} (hw : IsoOn W L M w) (r : Z ⟶ X)
    (y : Z) {a a' : L.ι} {b b' : M.ι} (h0 : r y ∈ W) (ha : r y ∈ L.U a) (ha' : r y ∈ L.U a') (hb : r y ∈ M.U b)
    (hb' : r y ∈ M.U b') :
    gm r y _ (w a b) * gm r y _ (M.g b b') = gm r y _ (L.g a a') * gm r y _ (w a' b') := by
  have h1 : (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) ≤ W ⊓ (L.U a ⊓ M.U b) := inf_le_left
  have h2 : (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) ≤ M.U b ⊓ M.U b' :=
    le_inf (inf_le_left.trans (inf_le_right.trans inf_le_right)) (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have h3 : (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) ≤ L.U a ⊓ L.U a' :=
    le_inf (inf_le_left.trans (inf_le_right.trans inf_le_left)) (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have h4 : (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) ≤ W ⊓ (L.U a' ⊓ M.U b') := inf_le_right
  have key : ∀ (T : Scheme.{0}) (f : T ⟶ X) (t : T), f t ∈ (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) →
      gm f t _ (res h1 (w a b) * res h2 (M.g b b')) = gm f t _ (w a b) * gm f t _ (M.g b b') ∧
      gm f t _ (res h3 (L.g a a') * res h4 (w a' b')) = gm f t _ (L.g a a') * gm f t _ (w a' b') :=
    fun T f t ht ↦ ⟨(map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f t h1 ht _) (gm_res f t h2 ht _)),
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f t h3 ht _) (gm_res f t h4 ht _))⟩
  have e : res h1 (w a b) * res h2 (M.g b b') = res h3 (L.g a a') * res h4 (w a' b') :=
    unit_ext fun x hx ↦ (key X (𝟙 X) x hx).1.trans ((hw x (h1 hx).1 a a' b b' (h3 hx).1 (h3 hx).2 (h2 hx).1 (h2 hx).2).trans
      (key X (𝟙 X) x hx).2.symm)
  have hm : r y ∈ (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) := ⟨⟨h0, ha, hb⟩, ⟨h0, ha', hb'⟩⟩
  exact (key Z r y hm).1.symm.trans ((congrArg (gm r y _) e).trans (key Z r y hm).2)

theorem lbIso_pull_of_isoOn (X Z : Scheme.{0}) (W : X.Opens) (L M : LB X) (w : Cmp W L M) (r : Z ⟶ X)
    (hw : IsoOn W L M w) (hr : ∀ z, r z ∈ W) : LBIso (L.pull r) (M.pull r) := by
  have le : ∀ p : (PUnit → M.ι) × (PUnit → L.ι), (M.pull r).U p.1 ⊓ (L.pull r).U p.2 ≤
      r ⁻¹ᵁ (W ⊓ (L.U (p.2 PUnit.unit) ⊓ M.U (p.1 PUnit.unit))) :=
    fun p y hy ↦ ⟨hr y, mem_pull.1 hy.2, mem_pull.1 hy.1⟩
  refine ⟨⟨fun p ↦ (res (le p) (pullU r _ (w (p.2 PUnit.unit) (p.1 PUnit.unit))))⁻¹⟩, fun p q ↦ unit_ext fun y hy ↦ ?_⟩
  have val : ∀ p : (PUnit → M.ι) × (PUnit → L.ι), y ∈ (M.pull r).U p.1 ⊓ (L.pull r).U p.2 →
      gm (𝟙 Z) y _ (res (le p) (pullU r _ (w (p.2 PUnit.unit) (p.1 PUnit.unit))))⁻¹ =
        (gm r y _ (w (p.2 PUnit.unit) (p.1 PUnit.unit)))⁻¹ := fun p hp ↦
    (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res (𝟙 Z) y (le p) hp _).trans
      ((gm_pull (𝟙 Z) r y _ (le p hp) _).trans (by rw [Category.id_comp]))))
  have hM := gm_pull_g M r (𝟙 Z) y p.1 q.1 hy.1.1 hy.2.1
  have hL := gm_pull_g L r (𝟙 Z) y p.2 q.2 hy.1.2 hy.2.2
  rw [Category.id_comp] at hM hL
  have hd := gm_div (L.pull r) (M.pull r) (𝟙 Z) y p q hy
  have k := isoOn_gm hw r y (hr y) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2.2) (mem_pull.1 hy.1.1) (mem_pull.1 hy.2.1)
  refine (gm_res (𝟙 Z) y inf_le_left hy _).trans ((val p hy.1).trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans ?_
  refine (congrArg₂ (· * ·) (hd.trans (congrArg₂ (fun u v ↦ u * v⁻¹) hM hL))
    ((gm_res (𝟙 Z) y inf_le_right hy _).trans (val q hy.2))).trans ?_
  rw [eq_mul_inv_of_mul_eq k]
  simp only [mul_inv_rev, inv_inv]
  ac_rfl

end GlobalTheory.PicGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormResidueSignMul
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory

theorem KSp.sgn_mul_of_isQuad : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (s t : Fˣ), sgn E (s * t) = sgn E s * sgn E t := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE s t
  set H := (Units.map (Algebra.norm F : E →* F)).range with hH
  unfold sgn
  rw [← hH]
  by_cases hs : s ∈ H <;> by_cases ht : t ∈ H
  · simp [hs, ht, H.mul_mem hs ht]
  · have : s * t ∉ H := fun h => ht ((H.mul_mem_cancel_left hs).mp h)
    simp [hs, ht, this]
  · have : s * t ∉ H := fun h => hs ((H.mul_mem_cancel_right ht).mp h)
    simp [hs, ht, this]
  · have : s * t ∈ H := GlobalTheory.T.mul_mem_range_norm_of_not_mem F E c δ hE s t hs ht
    simp [hs, ht, this]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatBCKsProj
section
noncomputable section

namespace GlobalTheory.KS.Leray

open AlgebraicGeometry CategoryTheory Limits

def fibMap {X Y T : Scheme.{0}} (f : Y ⟶ X) (x : T ⟶ X) (u : Y ⟶ Y) (hu : u ≫ f = f) : pullback f x ⟶ pullback f x :=
  pullback.map f x f x u (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hu]) (by simp)

variable {S B B' : Scheme.{0}}

def ksProj (A : Over S) (m : ℕ) (p : S ⟶ B) (b : B' ⟶ B) : ksBC A m p b ⟶ pullback p b :=
  pullback.map _ _ _ _ (pow A m).hom (𝟙 _) (𝟙 _) (by simp) (by simp)

end GlobalTheory.KS.Leray
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxSlopeSqFieldExtensionLeComparableNormsStatement
section
open NumberField GlobalTheory.AllWt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxSlope_sq_fieldExtension_le_comparable_norms : ∀ (K K' V V' : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field K'] [NumberField K'] [Algebra K K'] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K' V'] [Module (𝓞 K') V'] [IsScalarTower (𝓞 K') K' V'] (N : (K →+* ℂ) → V → ℝ) (N' : (K' →+* ℂ) → V' → ℝ) (ι : V →ₛₗ[algebraMap K K'] V') (L : Submodule (𝓞 K) V) (c : (K' →+* ℂ) → ℝ) (B : ℝ), HasGram N → HasGram N' → (∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x) → (∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent K' (fun k => ι (b k))) → L.FG → L ≠ ⊥ → (∀ σ', 0 < c σ' ∧ |Real.log (c σ')| ≤ B) → (∀ σ' x, N' σ' (ι x) = c σ' * N (σ'.comp (algebraMap K K')) x) → slopeMax_sq N' (Submodule.span (𝓞 K') (ι '' (L : Set V))) ≤ slopeMax_sq N L + 2 * B := by
  first | exact @GlobalTheory.SlopeMaxExt.slopeMax_sq_span_le | exact GlobalTheory.SlopeMaxExt.slopeMax_sq_span_le | (intros; apply GlobalTheory.SlopeMaxExt.slopeMax_sq_span_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogMetricGeneratorEqMeanPeriodStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_logMetric_generator_eq_meanPeriod : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (cD : D.what₂.Tau → ℂ), StandardLatticesGL3.Crv D cc dl → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriodAt D cc dl → IsDgen D cD → (∀ τ, cD τ ≠ 0) ∧ ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D cc dl) M → (∀ τ, cD τ ∈ M) → ∀ τ, (∑ ρ : M →ₐ[ℚ] ℂ, -TaylorLogMetric.logMet M (TaylorLogMetric.lamOf D cc dl) ρ (TaylorLogMetric.liftM M (cD τ))) / (Module.finrank ℚ M : ℝ) = TaylorLogMetric.logOmVal D := by
  first | exact @GlobalTheory.MeanPeriodGenerator.mean_logMet_eq | exact GlobalTheory.MeanPeriodGenerator.mean_logMet_eq | (intros; apply GlobalTheory.MeanPeriodGenerator.mean_logMet_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartz
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.LevelSchwartz

theorem mem_schA_of_level : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (Φ : (Fin N → AF F) → ℂ),
    (∃ U : AddSubgroup (Fin N → AF F), IsOpen (U : Set (Fin N → AF F)) ∧ ∀ u ∈ U, inf u = 0 → ∀ x, Φ (x + u) = Φ x) →
    (∃ K : Set (Fin N → Af F), IsCompact K ∧ ∀ x, Φ x ≠ 0 → fin x ∈ K) →
    (∀ x, ∃ g : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ t, g t = Φ (x + embR t)) →
    Φ ∈ GlobalTheory.WeilM.schA F (Fin N) := by
  intro F _ _ N Φ ⟨U, hUo, hU⟩ ⟨K, hK, hKs⟩ hS
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let ι : (Fin N → Af F) →+ (Fin N → AF F) :=
    { toFun := fun v i => pairA F 0 (v i)
      map_zero' := rfl
      map_add' := fun a b => by
        funext i
        show (((0 : Ainf F), a i + b i) : Ainf F × Af F) = ((0 : Ainf F), a i) + ((0 : Ainf F), b i)
        simp }
  have hιc : Continuous ι := continuous_pi fun i =>
    (show Continuous fun v : Fin N → Af F => (((0 : Ainf F), v i) : Ainf F × Af F) from
      continuous_const.prodMk (continuous_apply i))
  have hιinf : ∀ v, inf (ι v) = 0 := fun v => rfl
  have hfin : ∀ a t, fin (ι a + embR t) = a := fun a t => by
    funext i
    show (a i + 0 : Af F) = a i
    exact add_zero _
  have hdec : ∀ y : Fin N → AF F, y = ι (fin y) + embR (fun i => e (y i).1) := fun y => by
    funext i
    show (y i : Ainf F × Af F) = (((0 : Ainf F), (y i).2) : Ainf F × Af F) + ((e.symm (e (y i).1), (0 : Af F)))
    rw [RingEquiv.symm_apply_apply]
    refine Prod.ext ?_ ?_ <;> simp
  let W : AddSubgroup (Fin N → Af F) := U.comap ι
  have hWo : IsOpen (W : Set (Fin N → Af F)) := hUo.preimage hιc
  have hWcl : IsClosed (W : Set (Fin N → Af F)) := AddSubgroup.isClosed_of_isOpen W hWo
  have hinv : ∀ a b, -a + b ∈ W → ∀ z, Φ (ι b + z) = Φ (ι a + z) := by
    intro a b hab z
    rw [← hU (ι (-a + b)) hab (hιinf _) (ι a + z)]
    congr 1
    rw [map_add, map_neg]
    abel
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun a : Fin N → Af F => {b | -a + b ∈ W})
    (fun a => hWo.preimage (continuous_const.add continuous_id))
    (fun b _ => Set.mem_iUnion.2 ⟨b, show -b + b ∈ W by rw [neg_add_cancel]; exact W.zero_mem⟩)
  let T : Finset ((Fin N → Af F) ⧸ W) := t.image QuotientAddGroup.mk
  choose g hg using fun q : (Fin N → Af F) ⧸ W => hS (ι q.out)
  let ind : ((Fin N → Af F) ⧸ W) → (Fin N → Af F) → ℂ := fun q a =>
    if (QuotientAddGroup.mk a : (Fin N → Af F) ⧸ W) = q then 1 else 0
  have key : Φ = ∑ q ∈ T, GlobalTheory.WeilM.pureA F (g q) (ind q) := by
    funext y
    rw [Finset.sum_apply]
    show Φ y = ∑ q ∈ T, g q (fun i => e (y i).1) *
      (if (QuotientAddGroup.mk (fin y) : (Fin N → Af F) ⧸ W) = q then (1 : ℂ) else 0)
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hT
    · rw [hg]
      conv_lhs => rw [hdec y]
      exact hinv _ _ (QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)) _
    · by_contra hne
      obtain ⟨b, hb, hab⟩ := Set.mem_iUnion₂.1 (ht (hKs y hne))
      exact hT (Finset.mem_image.2 ⟨b, hb, QuotientAddGroup.eq.2 hab⟩)
  rw [key]
  refine Submodule.sum_mem _ fun q _ => ?_
  by_cases h0 : ∀ s, g q s = 0
  · have : GlobalTheory.WeilM.pureA F (g q) (ind q) = 0 := by
      funext y
      simp [GlobalTheory.WeilM.pureA, h0]
    rw [this]
    exact zero_mem _
  push_neg at h0
  obtain ⟨s0, hs0⟩ := h0
  refine Submodule.subset_span ⟨g q, ind q, ?_, rfl⟩
  let C : Set (Fin N → Af F) := {a | -q.out + a ∈ W}
  have hCcl : IsClosed C := hWcl.preimage (continuous_const.add continuous_id)
  have hCK : C ⊆ K := by
    intro a ha
    have h1 : Φ (ι a + embR s0) ≠ 0 := by
      rw [hinv _ _ ha, ← hg]
      exact hs0
    simpa [hfin] using hKs _ h1
  have hmk : IsLocallyConstant (fun a : Fin N → Af F => (a : (Fin N → Af F) ⧸ W)) :=
    (IsLocallyConstant.iff_exists_open _).2 fun x => ⟨{b | -b + x ∈ W},
      hWo.preimage (continuous_neg.add continuous_const), by simp, fun b hb => QuotientAddGroup.eq.2 hb⟩
  refine ⟨hmk.comp fun q' => if q' = q then (1 : ℂ) else 0, ?_⟩
  refine HasCompactSupport.intro' (hK.of_isClosed_subset hCcl hCK) hCcl fun x hx => ?_
  show (if (QuotientAddGroup.mk x : (Fin N → Af F) ⧸ W) = q then (1 : ℂ) else 0) = 0
  rw [if_neg]
  intro hq
  apply hx
  show -q.out + x ∈ W
  exact QuotientAddGroup.eq.1 (by rw [hq, QuotientAddGroup.out_eq'])

end GlobalTheory.LevelSchwartz

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedOrderIffPlacewise
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.HatPlace

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_integral : IsOpen {y : Af E | ∀ w, Valued.v (y w) ≤ 1} :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (A := fun v => v.adicCompletionIntegers E) fun _ => Valued.isOpen_valuationSubring _

theorem exists_approx {S : Set (Af E)} {z : Af E} (hz : z ∈ closure S) {n : OF E} (hn : n ≠ 0) :
    ∃ x ∈ S, ∃ y : Af E, (∀ w, Valued.v (y w) ≤ 1) ∧ z = x + iota n * y := by
  have hn0 : algebraMap (OF E) E n ≠ 0 := fun h => hn (Subtype.ext (Subtype.ext h))
  have ho : IsOpen ((fun t : Af E => algebraMap E (Af E) (algebraMap (OF E) E n)⁻¹ * (z - t)) ⁻¹'
      {y : Af E | ∀ w, Valued.v (y w) ≤ 1}) :=
    isOpen_integral.preimage (continuous_const.mul (continuous_const.sub continuous_id))
  obtain ⟨x, hx, hxS⟩ := mem_closure_iff.1 hz _ ho (fun w => by
    simp only [sub_self, mul_zero, zero_coord, map_zero, zero_le'])
  refine ⟨x, hxS, _, hx, ?_⟩
  rw [iota, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hn0, map_one, one_mul, add_sub_cancel]

theorem mem_iff_val {J : Ideal (𝓞 E)} (hJ : J ≠ ⊥) (b : 𝓞 E) :
    b ∈ J ↔ ∀ w : HeightOneSpectrum (𝓞 E), Valued.v (algebraMap E (Af E) (algebraMap (𝓞 E) E b) w) ≤
      WithZero.exp (-(multiplicity w.asIdeal J : ℤ)) := by
  conv_lhs => rw [← Ideal.iInf_maxPowDividing_eq hJ, Ideal.mem_iInf]
  refine forall_congr' fun P => ?_
  rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hJ, ← P.intValuation_le_pow_iff_mem,
    ← HeightOneSpectrum.valuation_of_algebraMap (K := E),
    ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← FiniteAdeleRing.algebraMap_apply]

theorem val_mul_le {c : Ideal (OF E)} (hc : c ≠ ⊥) {n : OF E} (hn : n ∈ c) {y : Af E} (hy : ∀ w, Valued.v (y w) ≤ 1)
    (w : HeightOneSpectrum (𝓞 E)) : Valued.v ((iota n * y) w) ≤
      WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ)) := by
  rw [mul_coord, map_mul]
  exact (mul_le_mul' ((mem_iff_val (Ideal.map_ne_bot_of_ne_bot hc) _).1 (Ideal.mem_map_of_mem _ hn) w)
    (hy w)).trans_eq (mul_one _)

theorem mem_hatO_of_val {c : Ideal (OF E)} (hc : c ≠ ⊥) {z : Af E} (hz : ∀ w : HeightOneSpectrum (𝓞 E), Valued.v (z w) ≤
      WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))) : z ∈ hatO c := by
  have hN : 0 < Ideal.absNorm c := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  obtain ⟨x, y, hy, hxy⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat E _ hN).2 z
    (fun P => (hz P).trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega))
  have hny : Ideal.absNorm c • y = iota ((Ideal.absNorm c : ℕ) : OF E) * y := by
    rw [nsmul_eq_mul, iota, map_natCast, map_natCast]
  rw [hny] at hxy
  have hx : x ∈ Ideal.map (algebraMap (OF E) (𝓞 E)) c := by
    rw [mem_iff_val (Ideal.map_ne_bot_of_ne_bot hc)]
    intro P
    have h1 : algebraMap E (Af E) (algebraMap (𝓞 E) E x) = z - iota ((Ideal.absNorm c : ℕ) : OF E) * y := by
      rw [hxy, add_sub_cancel_right]
    rw [h1, sub_coord]
    exact Valuation.map_sub_le _ (hz P) (val_mul_le hc (Ideal.absNorm_mem c) hy P)
  rw [hxy]
  exact add_mem (algebraMap_mem_hatO (mem_orderC.2 ⟨0, _, hx, by rw [map_zero, zero_add]⟩))
    (PicFin.mul_mem_hatO (Ideal.absNorm_mem c) hy)

theorem exists_integer {f : E} (hf : f ∈ maximalRealSubfield E)
    (h : ∀ w, Valued.v (algebraMap E (Af E) f w) ≤ 1) : ∃ a : OF E, algebraMap (OF E) E a = f := by
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E f fun w => by
    have := h w
    rwa [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
  have h1 : IsIntegral ℤ f := hb ▸ b.isIntegral_coe
  have h2 : IsIntegral ℤ (⟨f, hf⟩ : maximalRealSubfield E) :=
    (isIntegral_algebraMap_iff (A := maximalRealSubfield E) (B := E) (RingHom.injective _)).1 h1
  exact ⟨⟨_, h2⟩, rfl⟩

theorem mem_hatO_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ z : Af E,
    z ∈ hatO c ↔ ∃ a ∈ hatF (E := E), (∀ w, Valued.v (a w) ≤ 1) ∧ ∀ (w : HeightOneSpectrum (𝓞 E)),
      Valued.v (z w - a w) ≤
        WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ)) := by
  intro E _ _ _ c hc z
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  constructor
  · intro hz
    obtain ⟨_, ⟨x, hx, rfl⟩, y, hy, rfl⟩ := exists_approx hz hn0
    obtain ⟨a, b, hb, rfl⟩ := mem_orderC.1 hx
    refine ⟨iota a, Subring.le_topologicalClosure _ ⟨_, (a : maximalRealSubfield E).2, rfl⟩,
      fun w => val_iota_le_one w a, fun w => ?_⟩
    rw [← sub_coord, map_add, add_assoc]
    erw [add_sub_cancel_left]
    rw [add_coord]
    exact Valuation.map_add_le _ ((mem_iff_val (Ideal.map_ne_bot_of_ne_bot hc) _).1 hb w) (val_mul_le hc hn hy w)
  · rintro ⟨a, ha, hai, hz⟩
    obtain ⟨_, ⟨f, hf, rfl⟩, y, hy, rfl⟩ := exists_approx ha hn0
    obtain ⟨a, rfl⟩ := exists_integer hf fun w => by
      have h1 : Valued.v ((iota n * y) w) ≤ 1 := by
        rw [mul_coord, map_mul]; exact mul_le_one' (val_iota_le_one w n) (hy w)
      have h2 := Valuation.map_sub_le _ (hai w) h1
      rwa [add_coord, add_sub_cancel_right] at h2
    have h1 : z - (algebraMap E (Af E) (algebraMap (OF E) E a) + iota n * y) ∈ hatO c := mem_hatO_of_val hc hz
    have h2 := add_mem h1 (add_mem (algebraMap_mem_hatO (algebraMap_mem_orderC c a)) (PicFin.mul_mem_hatO hn hy))
    exact sub_add_cancel z _ ▸ h2

end GlobalTheory.CMVal.HatPlace
end
end

