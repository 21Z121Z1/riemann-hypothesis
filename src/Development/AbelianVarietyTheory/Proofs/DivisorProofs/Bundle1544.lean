import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1525
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0166
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsComplexStructureGaussVacuumFockEquations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSympNegOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1532
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1399
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMajorantFrameCompactSubgroupLe
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Matrix
noncomputable section

namespace GlobalTheory.CptMajorant

theorem exists_frame_le_majCpt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ K : Subgroup (GAd σ J), K ≤ infPts σ J → IsCompact (K : Set (GAd σ J)) →
    ∃ c : (∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)),
      (∀ w, ∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) (c w).1 * JR w.Completion J * (c w).1 =
        Matrix.diagonal fun i => if ε i then 1 else -1) ∧ K ≤ majCpt σ J c := by
  intro F E _ _ _ _ _ σ h n J hJ K hKinf hK
  have key : ∀ w : InfinitePlace F, ∃ c : GL (Fin n) (w.Completion ⊗[F] E),
      (∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) c.1 * JR w.Completion J * c.1 =
        Matrix.diagonal fun i => if ε i then 1 else -1) ∧ ∀ k ∈ K, projArch σ J w k ∈ stabArch σ J w c := by
    intro w
    obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
    let e := RingEquiv.ofBijective _ (infEmb_bijective h τ)
    have : IsTopologicalRing (w.Completion ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
    let φ : GAd σ J →* GL (Fin n) ℂ :=
      (Units.map (infEmb τ).mapMatrix.toMonoidHom).comp ((matHom _ σ J).comp (projArch σ J w))
    have hφv : ∀ x, (φ x).1 = (matHom _ σ J (projArch σ J w x)).1.map (infEmb τ) := fun x => rfl
    have hcv : Continuous fun x : GAd σ J => (φ x).1 := by
      simp only [hφv]
      exact (Units.continuous_val.comp ((isEmbedding_matHom _ σ J).continuous.comp
        (continuous_projArch σ J w))).matrix_map (GlobalTheory.Orb.continuous_infEmb τ)
    have hφ : Continuous φ := Units.continuous_iff.2 ⟨hcv, by
      simp only [← map_inv]; exact hcv.comp continuous_inv⟩
    obtain ⟨P, hPh, hPpos, hPinv⟩ := GlobalTheory.T.exists_posDef_hermitian_invariant_of_isCompact (K.map φ) (by rw [Subgroup.coe_map]; exact hK.image hφ)
    have hG : (J.map τ.1).IsHermitian := by
      ext i j
      exact (h.2.2.2 τ.1 _).symm.trans (congrArg _ (hJ.1 i j))
    have hd : (J.map τ.1).det ≠ 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero _).2 hJ.2
    obtain ⟨ε, Q, hQ, hQu⟩ := GlobalTheory.T.hermitian_posDef_simultaneous_normal_form hG hd hPh hPpos
    have h1 : (Formalism.UG.bc e.symm.toRingHom Q).1.map (infEmb τ) = Q.1 := Matrix.ext fun i j => e.apply_symm_apply _
    have h1' : ((Formalism.UG.bc e.symm.toRingHom Q)⁻¹).1.map (infEmb τ) = (Q⁻¹).1 :=
      Matrix.ext fun i j => e.apply_symm_apply _
    have h2 : (JR w.Completion J).map (infEmb τ) = J.map τ.1 := by ext r s; simp [JR, inclR]
    refine ⟨Formalism.UG.bc e.symm.toRingHom Q, ⟨ε, Matrix.map_injective e.injective ?_⟩, fun k hk => ?_⟩
    · change Matrix.map _ (infEmb τ) = Matrix.map _ (infEmb τ)
      rw [Matrix.map_mul, Matrix.map_mul, Frames.map_cT_sigR h, h1, h2, hQ, Matrix.diagonal_map (map_zero _)]
      congr 1
      funext i
      split_ifs <;> simp
    · rw [mem_stabArch]
      change Formalism.UG.cT _ _ * 1 * _ = 1
      refine Matrix.map_injective e.injective ?_
      change Matrix.map _ (infEmb τ) = Matrix.map _ (infEmb τ)
      have hu := hQu (φ k).1 (hPinv _ ⟨k, hk, rfl⟩) (by
        have : Formalism.UG.cT (sigR _ σ) (matHom _ σ J (projArch σ J w k)).1 * JR w.Completion J *
          (matHom _ σ J (projArch σ J w k)).1 = JR w.Completion J := (projArch σ J w k).2
        have := congrArg (fun A => A.map (infEmb τ)) this
        simpa only [Matrix.map_mul, Frames.map_cT_sigR h, h2, hφv] using this)
      simpa only [Matrix.mul_one, Matrix.map_mul, Frames.map_cT_sigR h, Units.val_mul, h1, h1', hφv,
        Matrix.map_one _ (map_zero _) (map_one _)] using hu
  choose c hc hKc using key
  exact ⟨c, hc, fun k hk => mem_majCpt.2 ⟨hKinf hk, fun w => hKc w k hk⟩⟩

end GlobalTheory.CptMajorant
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMap
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.Pull

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

def tateMoveP {D : Datum F} {p : ℕ} {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q']
    {act : 𝓞 F → Q → Q} {act' : 𝓞 F → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop}
    (Φ : Q' ≃* Q) (hact : ∀ c x, Φ (act' c x) = act c (Φ x)) (he : ∀ n x y c, e n (Φ x) (Φ y) c → e' n x y c)
    (I : TateIsoP D p k Q act e) : TateIsoP D p k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev := fun n a => Φ.symm (I.ev n a)
  add := fun n a b => by simp only [I.add, map_mul]
  lin := fun n c a => by
    apply Φ.injective
    rw [MulEquiv.apply_symm_apply, hact, MulEquiv.apply_symm_apply]
    exact I.lin n c a
  ker := fun n hn hp a => (map_eq_one_iff _ Φ.symm.injective).trans (I.ker n hn hp a)
  onto := fun n hn hp x => by
    rw [← map_eq_one_iff Φ Φ.injective, map_pow, I.onto n hn hp]
    exact exists_congr fun a => Φ.symm_apply_eq.symm
  tower := fun n m hn hm hp a => by rw [← map_pow, I.tower n m hn hm hp a]
  isom := fun n hn hp a b => he _ _ _ _ (by
    rw [Φ.apply_symm_apply, Φ.apply_symm_apply]
    exact I.isom n hn hp a b)

theorem exists_objMap : ∀ (F : Type) [Field F] [NumberField F] [IsCMField F] (D : GlobalTheory.UPel.Datum F) (p N : ℕ)
    (S T : Scheme.{0}) (s : S ⟶ Sp (D.OEp p)) (o : GlobalTheory.UPel.Obj D p N s) (t : T ⟶ S),
    ∃ o' : GlobalTheory.UPel.Obj D p N (t ≫ s), Nonempty (GlobalTheory.UPel.ObjMap o' o t) := by
  intro F _ _ _ D p N S T s o t
  have h := isGrpPullback_pullback o.A t
  obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := Out.proved_CubePullSt S T o.A _ (cubeMapOf h) o.PP o.cub
  let act' := OAct.pullback t o.A o.act
  have hact : ∀ a, (act'.act a).left ≫ pullback.fst o.A.hom t = pullback.fst o.A.hom t ≫ (o.act.act a).left :=
    fun a => pullback.lift_fst _ _ _
  have pa : ∀ {U : Over T} (x : U ⟶ (Over.pullback t).obj o.A) a,
      pushPt h.1.w (x ≫ act'.act a) = pushPt h.1.w x ≫ o.act.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  let PP' := (cubeMapOf h).rigLB o.PP hL hr
  have adj' : ∀ a, LBIso (cubeLB ((Over.pullback t).obj o.A)
      ![fst ((Over.pullback t).obj o.A) ((Over.pullback t).obj o.A) ≫ act'.act a,
        snd ((Over.pullback t).obj o.A) ((Over.pullback t).obj o.A)] PP'.L)
      (cubeLB ((Over.pullback t).obj o.A) ![fst ((Over.pullback t).obj o.A) ((Over.pullback t).obj o.A),
        snd ((Over.pullback t).obj o.A) ((Over.pullback t).obj o.A) ≫ act'.act (D.bar a)] PP'.L) := fun a => by
    let U := lift (pushPt h.1.w (fst ((Over.pullback t).obj o.A) ((Over.pullback t).obj o.A)))
      (pushPt h.1.w (snd ((Over.pullback t).obj o.A) ((Over.pullback t).obj o.A)))
    refine LBIso.chartPull (chartPullLinComb o.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullLinComb o.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (o.adj a)
    · fin_cases i
      · exact (pa _ a).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pa _ _).trans (by simp [U])
  have prim' : LBIso PP'.L (cubeLB ((Over.pullback t).obj o.A) ![𝟙 ((Over.pullback t).obj o.A), act'.act D.w] PP'.L) := by
    let U := pushPt h.1.w (𝟙 ((Over.pullback t).obj o.A))
    refine LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o.PP.L _ U.left (Category.id_comp _))
      (chartPullLinComb o.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) o.prim
    fin_cases i
    · simp [U]
    · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
  obtain ⟨w, hw, -⟩ := hc'
  have hLi : LBIso PP'.L (o.PP.L.pull (pullback.fst o.A.hom t)) := ⟨w, hw⟩
  obtain ⟨hab, hamp, hk⟩ := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally S T o.A _ t
    _ o.PP.L PP'.L o.PP.isLB PP'.isLB o.ab h hLi
  refine ⟨{ A := (Over.pullback t).obj o.A
            ab := hab
            act := act'
            PP := PP'
            cub := c'
            sym := hs o.sym
            adj := adj'
            prim := prim'
            ample := hamp o.ample
            ktriv := hk o.ktriv
            eta := fun a => GlobalTheory.ObjPull.secPull h (o.eta a)
            eta_add := fun a c => by rw [o.eta_add, map_mul]
            eta_ker := fun a => by rw [o.eta_ker a, map_one]
            geom := fun k _ _ x β hx => ?_ },
    ⟨{ φ := pullback.fst o.A.hom t
       cart := h
       act := hact
       pol := hLi
       eta := fun a => GlobalTheory.ObjPull.secPull_left h _ }⟩⟩
  obtain ⟨⟨β', hβ', hdet⟩, I, hI⟩ := o.geom k (x ≫ t) β (by rw [Category.assoc]; exact hx)
  refine ⟨⟨β', hβ', fun σ => (GlobalTheory.LiePull.lieMult_pull _ S T o.A _ t _ o.act act' h hact k x σ _).2 (hdet σ)⟩,
    tateMoveP (GlobalTheory.ObjPull.pushEquiv h (Over.mk x)) (fun c g => ?_) (fun n g g' c hc => ?_) I, fun a => ?_⟩
  · apply Over.OverMorphism.ext
    show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
    rw [Category.assoc, hact, Category.assoc]
  · exact (GlobalTheory.weilIs_grpPullback_of_comm S T o.A _ t _ o.PP.L PP'.L o.PP.isLB PP'.isLB h hLi
      (Over.mk x) n g g' _ _ _ rfl rfl).2 hc
  · exact (MulEquiv.eq_symm_apply _).2 ((GlobalTheory.ObjPull.pushEquiv_secPull h _ _).trans (hI a))

end GlobalTheory.UPel.Pull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointPicardClassEqTranslateOfTrivialLambda
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.PrimitiveOverField
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PointTranslate

theorem exists_point_cls_eq_lam : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left) (hL : L.IsLB), Out.KTriv B L → ∀ (O : LB B.left) (hO : O.IsLB), lam (cls O hO) (fst B B) (snd B B) = 0 → ∃ x : 𝟙_ (Over (Sp K)) ⟶ B, cls O hO = lam (cls L hL) (toUnit B ≫ x) (𝟙 B) := by
  intro K _ _ B _ hB L hL hK O hO lamO
  by_contra hno
  have := hB.comm
  have := hB.smooth
  have := hB.proper
  have hpr : IsProjBy B.hom := GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety K B hB
  have hproj : ∀ (R : Type) [CommRing R] (u : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0})
      (π : X ⟶ B.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f B.hom u → IsProjBy f :=
    fun R _ u X π f h => GlobalTheory.AbLaw.CubeProj.isProjBy_baseChange hpr h
  have hΘ := GlobalTheory.exists_gen_theta_of_isAbelianScheme K B hB L hL
  obtain ⟨F, hF, eF⟩ := cls_surj (lam (cls L hL) (fst B B) (snd B B) -
    CechPic.pull (snd B B).left (cls O hO))
  have hpq : IsPullback (fst B B).left (snd B B).left B.hom B.hom := IsPullback.of_hasPullback _ _
  have cst_left : ∀ x : 𝟙_ _ ⟶ B, (toUnit B ≫ x).left = B.hom ≫ x.left := fun x =>
    congrArg (· ≫ x.left) ((Category.comp_id _).symm.trans (Over.w (toUnit B)))
  have s₁ : ∀ x : 𝟙_ _ ⟶ B, cls _ (pull_isLB hF (lift (toUnit B ≫ x) (𝟙 B)).left) =
      lam (cls L hL) (toUnit B ≫ x) (𝟙 B) - cls O hO := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, Over.id_left, pull_id]
  have s₂ : ∀ x : 𝟙_ _ ⟶ B, cls _ (pull_isLB hF (lift (𝟙 B) (toUnit B ≫ x)).left) =
      lam (cls L hL) (toUnit B ≫ x) (𝟙 B) := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, pull_const, sub_zero,
      lam_comm]
  have total : Ac ((fst B B).left ≫ B.hom) F := by
    refine (GlobalTheory.T.lineBundle_product_acyclic_of_affine_base_acyclic K _ _ _ _ _ _ _ hpq inferInstance inferInstance inferInstance inferInstance F hF).1
      fun R _ t Y π f h ht => ac_of_slices hproj hpq h hF fun x hx _ => ?_
    let x' : 𝟙_ _ ⟶ B := Over.homMk x hx
    refine ⟨(lift (toUnit B ≫ x') (𝟙 B)).left, ?_, ?_, ac_of_primitive hB hpr (pull_isLB hF _) ?_ ?_⟩
    · exact (congrArg CommaMorphism.left (lift_fst (toUnit B ≫ x') (𝟙 B))).trans (cst_left x')
    · exact congrArg CommaMorphism.left (lift_snd (toUnit B ≫ x') (𝟙 B))
    · rw [s₁, lam_sub, lam_lam hL hΘ, lamO, sub_zero]
    · rw [s₁, sub_ne_zero]
      exact fun e => hno ⟨x', e.symm⟩
  rw [hpq.w] at total
  let o : Spec (CommRingCat.of K) ⟶ B.left := η[B].left
  have ho : o ≫ B.hom = 𝟙 _ := Over.w η[B]
  have hcl : IsClosed ({o (IsLocalRing.closedPoint K)} : Set B.left) := by
    have : IsClosedImmersion (o ≫ B.hom) := by rw [ho]; infer_instance
    have : IsClosedImmersion o := IsClosedImmersion.of_comp o B.hom
    have h := o.isClosedEmbedding.isClosedMap {IsLocalRing.closedPoint K}
      (by rw [show ({IsLocalRing.closedPoint K} : Set (Spec (CommRingCat.of K))) = Set.univ from
        Set.eq_univ_of_forall fun z => Subsingleton.elim (α := PrimeSpectrum K) _ _]; exact isClosed_univ)
    exact (congrArg IsClosed Set.image_singleton).mp h
  have all := (GlobalTheory.T.lineBundle_product_acyclic_of_affine_base_acyclic K _ _ _ _ _ _ _ hpq.flip inferInstance inferInstance inferInstance inferInstance F hF).2
    _ hcl (fun R _ t Y π f h ht hne => ac_of_slices hproj hpq.flip h hF fun x hx hr => by
      let x' : 𝟙_ _ ⟶ B := Over.homMk x hx
      refine ⟨(lift (𝟙 B) (toUnit B ≫ x')).left, ?_, ?_, ac_of_primitive hB hpr (pull_isLB hF _) ?_ ?_⟩
      · exact (congrArg CommaMorphism.left (lift_snd (𝟙 B) (toUnit B ≫ x'))).trans (cst_left x')
      · exact congrArg CommaMorphism.left (lift_fst (𝟙 B) (toUnit B ≫ x'))
      · rw [s₂, lam_lam hL hΘ]
      · rw [s₂]
        intro e
        have e₁ : x' = η[B] := (eq_one_of_lam_eq_zero hL hK x' e).trans (by
          rw [Hom.one_def, toUnit_unit, Category.id_comp])
        have e₂ : x = o := congrArg CommaMorphism.left e₁
        obtain ⟨y, hy⟩ := hr (IsLocalRing.closedPoint K)
        exact hne y (e₂ ▸ hy)) total
  have hs := ac_slice hproj hpq.flip hF all o ho (lift (𝟙 B) (toUnit B ≫ η[B])).left
    ((congrArg CommaMorphism.left (lift_snd (𝟙 B) (toUnit B ≫ η[B]))).trans (cst_left η[B]))
    (congrArg CommaMorphism.left (lift_fst (𝟙 B) (toUnit B ≫ η[B])))
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : Nonempty B.left := ⟨o (IsLocalRing.closedPoint K)⟩
  exact not_ac_of_cls_eq_zero _ (pull_isLB hF _) ((s₂ _).trans (lam_one_left _ _)) hs

end GlobalTheory.PointTranslate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPositiveComplexStructureDarbouxPair
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.GaussFockPair

open GlobalTheory.GaussFockJ

def tensC {n d : ℕ} (JX : Matrix (Fin n) (Fin n) ℂ) (JW : Matrix (Fin d) (Fin d) ℂ) (x y : Matrix (Fin n) (Fin d) ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star (y k l)

theorem tensC_zero_left {n d : ℕ} (JX : Matrix (Fin n) (Fin n) ℂ) (JW : Matrix (Fin d) (Fin d) ℂ) (y : Matrix (Fin n) (Fin d) ℂ) :
    tensC JX JW 0 y = 0 := by
  simp [tensC]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem pair_Psi {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (u v : Matrix (Fin n) (Fin d) (AE F E)) :
    GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M u).1 (Psi M v).2 -
                 GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M v).1 (Psi M u).2 =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (evI F (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) u v)) := by
  rw [M.co.form u v, ← evIHom_apply, map_sub, map_sub]
  simp only [GlobalTheory.GaussLine.pairInf_apply, Psi, EvAt0.PolD.arc, dotProduct, map_sum, map_mul, evIHom_apply]

theorem exists_pos_complex_structure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∃ J₀ : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      (∀ w, J₀ (J₀ w) = -w) ∧ (∀ w w', (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w).1 (J₀ w').2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w').1 (J₀ w).2) = (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w).1 (w').2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w').1 (w).2)) ∧
      (∀ w, w ≠ 0 → 0 < (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w).1 (J₀ w).2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w).1 (w).2)) ∧
      ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
        (∀ w, u'.map (piInf (B.emb w)) = Complex.I • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)) →
        ((fun i => evI F ((M.co.e u').1 i), fun i => evI F ((M.co.e u').2 i)) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) = J₀ ((fun i => evI F ((M.co.e u).1 i), fun i => evI F ((M.co.e u).2 i)) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hcm := hP.base.cm
  choose R hRat hRmap using fun u : Matrix (Fin n) (Fin d) (AE F E) =>
    exists_mat_at hcm B.emb (fun w => Complex.I • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ))
  have hRadd : ∀ u v, R (u + v) = R u + R v := by
    intro u v
    refine eq_of_map_piInf hcm B.emb (hRat _) (fun c hc => by rw [smul_add, hRat u c hc, hRat v c hc, add_zero])
      fun w => ?_
    rw [hRmap, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), hRmap, hRmap]
    simp only [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, smul_add]
  have hRsmul : ∀ (c : AF F) u, R (c • u) = c • R u := by
    intro c u
    refine eq_of_map_piInf hcm B.emb (hRat _) (fun c' hc' => by rw [smul_comm, hRat u c' hc', smul_zero])
      fun w => ?_
    rw [hRmap, map_smul_piInf, map_smul_piInf, hRmap]
    simp only [ Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm]
  have hRR : ∀ u, At (evI F) u → R (R u) = -u := by
    intro u hu
    refine eq_of_map_piInf hcm B.emb (hRat _) (fun c hc => by rw [smul_neg, hu c hc, neg_zero]) fun w => ?_
    rw [hRmap, Matrix.map_neg _ (map_neg _), hRmap]
    have hV := (hP.herm.cartan w).1
    have hW := (hP.skew.cartan w).1
    have hWt : (W.θ w)ᵀ * (W.θ w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hW, Matrix.transpose_one]
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.I_mul_I, neg_one_smul]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.mul_assoc, hWt, Matrix.mul_one]

  have hXh : ∀ w, ∀ i j, star (X.J.map (B.emb w).1 j i) = X.J.map (B.emb w).1 i j := by
    intro w i j
    rw [Matrix.map_apply, Matrix.map_apply, ← hcm.2.2.2, hP.herm.herm]
  have hWs : ∀ w, ∀ i j, star (W.J.map (B.emb w).1 j i) = -W.J.map (B.emb w).1 i j := by
    intro w i j
    rw [Matrix.map_apply, Matrix.map_apply, ← hcm.2.2.2, hP.skew.skew, map_neg]
  have hloc := fun w => GlobalTheory.T.tensorCartanInvolution_invariant_and_positive n d (X.J.map (B.emb w).1) (X.θ w) (W.J.map (B.emb w).1) (W.θ w) (hXh w)
    (hP.herm.cartan w) (hWs w) (hP.skew.cartan w)
  have key : ∀ a b : Matrix (Fin n) (Fin d) (AE F E),
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) a b)) =
        ∑ w, -2 * (tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) (a.map (piInf (B.emb w)))
          (b.map (piInf (B.emb w)))).re := by
    intro a b
    rw [GlobalTheory.ThK.EvAt0.PlaneQ.trace_symp_neg_one F E σ hcm B.emb n d X.J W.J a b]
    rfl
  have hinv : ∀ a b w, tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) ((R a).map (piInf (B.emb w)))
      ((R b).map (piInf (B.emb w))) = tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) (a.map (piInf (B.emb w)))
      (b.map (piInf (B.emb w))) := by
    intro a b w
    rw [hRmap, hRmap]
    exact (hloc w _ _).1
  have hpos : ∀ a w, a.map (piInf (B.emb w)) ≠ 0 → 0 < -(tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1)
      (a.map (piInf (B.emb w))) ((R a).map (piInf (B.emb w)))).re := by
    intro a w ha
    rw [hRmap]
    exact (hloc w _ (a.map (piInf (B.emb w)))).2 ha
  let J : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
    fun w => Psi M (R (Phi M w))
  have hPsi_smul : ∀ (t : ℝ) v, At (evI F) v → Psi M (realAd F t • v) = t • Psi M v := by
    intro t v hv
    rw [← Phi_Psi M hv, ← Phi_smul, Psi_Phi, Psi_Phi]
  let J₀ : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
    { toFun := J
      map_add' := fun w w' => by
        show Psi M (R (Phi M (w + w'))) = Psi M (R (Phi M w)) + Psi M (R (Phi M w'))
        rw [Phi_add, hRadd, Psi_add]
      map_smul' := fun t w => by
        show Psi M (R (Phi M (t • w))) = t • Psi M (R (Phi M w))
        rw [Phi_smul, hRsmul, hPsi_smul t _ (hRat _)] }
  have hPsi0 : Psi M (0 : Matrix (Fin n) (Fin d) (AE F E)) = 0 := by
    have h := Psi_add M (0 : Matrix (Fin n) (Fin d) (AE F E)) 0
    rw [add_zero] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  refine ⟨J₀, fun w => ?_, fun w w' => ?_, fun w hw => ?_, fun u u' hu hu' hmap => ?_⟩
  · show Psi M (R (Phi M (Psi M (R (Phi M w))))) = -w
    rw [Phi_Psi M (hRat _), hRR _ (at_Phi M w), Psi_neg, Psi_Phi]
  · show GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M (R (Phi M w))).1 (Psi M (R (Phi M w'))).2 -
        GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M (R (Phi M w'))).1 (Psi M (R (Phi M w))).2 = _
    conv_rhs => rw [← Psi_Phi M w, ← Psi_Phi M w']
    rw [pair_Psi, pair_Psi, key, key]
    exact Finset.sum_congr rfl fun v _ => by rw [hinv]
  · have hw' := Psi_Phi M w
    have hat := at_Phi M w
    show 0 < GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) w.1 (Psi M (R (Phi M w))).2 -
        GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M (R (Phi M w))).1 w.2
    generalize Phi M w = a at hw' hat ⊢
    subst hw'
    rw [pair_Psi, key]
    have hex : ∃ v, a.map (piInf (B.emb v)) ≠ 0 := by
      by_contra hn
      push_neg at hn
      have ha0 : a = 0 := eq_of_map_piInf hcm B.emb hat (fun c _ => smul_zero c)
        fun v => by rw [hn v, Matrix.map_zero _ (map_zero _)]
      exact hw (by rw [ha0, hPsi0])
    obtain ⟨v, hv⟩ := hex
    refine Finset.sum_pos' (fun v' _ => ?_) ⟨v, Finset.mem_univ _, by have := hpos a v hv; linarith⟩
    by_cases h0 : a.map (piInf (B.emb v')) = 0
    · rw [h0, tensC_zero_left, Complex.zero_re, mul_zero]
    · have := hpos a v' h0; linarith
  · change Psi M u' = Psi M (R (Phi M (Psi M u)))
    rw [Phi_Psi M hu]
    congr 1
    exact eq_of_map_piInf hcm B.emb hu' (hRat u) fun w => by rw [hmap, hRmap]

end GlobalTheory.GaussFockPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportOfStTw2NeZero
section
open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

noncomputable section

namespace GlobalTheory.BCT.GeoFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ne_zero_of_finprod_mem_ne_zero {α : Type} (f : α → ℂ) (S : Set α) (hf : (Function.mulSupport f).Finite)
    (h : ∏ᶠ w ∈ S, f w ≠ 0) : ∀ w ∈ S, f w ≠ 0 := by
  intro w hw h0
  have hfin : (S ∩ Function.mulSupport f).Finite := hf.subset Set.inter_subset_right
  apply h
  rw [finprod_mem_eq_prod_of_inter_mulSupport_eq f (t := hfin.toFinset) (by
    ext x; simp only [Set.mem_inter_iff, Set.Finite.coe_toFinset]; tauto)]
  exact Finset.prod_eq_zero (i := w) (by simp [hw, h0]) h0

theorem exists_support_of_stTw2_ne_zero (a b : ℕ) (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X])
    (φ : GLw a w × GLw b w → ℂ) (h : stTw2 a b w Q₁ Q₂ φ ≠ 0) :
    ∃ y, φ y ≠ 0 ∧ (nrmL a w y.1).val.charpoly = Q₁ ∧ (nrmL b w y.2).val.charpoly = Q₂ := by
  obtain ⟨δ, ⟨hδ₁, hδ₂⟩, x, hx⟩ := exists_ne_zero_of_clSum_ne_zero _ _ _ _ _ h
  refine ⟨_, hx, ?_, ?_⟩
  · change (nrmL a w (x.1⁻¹ * δ.1 * thL a w x.1)).val.charpoly = Q₁
    rw [nrmL_twConj, ← hδ₁, Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, mul_inv_cancel_left]
  · change (nrmL b w (x.2⁻¹ * δ.2 * thL b w x.2)).val.charpoly = Q₂
    rw [nrmL_twConj, ← hδ₂, Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, mul_inv_cancel_left]

end GlobalTheory.BCT.GeoFin

namespace GlobalTheory.BCT.GeoFin

end GlobalTheory.BCT.GeoFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelFiltrationAtGoodSectionsStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSamuel_filtration_at_good_sections : Quoted → ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ), GeoHyp X Λ₀ → ∀ (δ : ℕ) (f : MvPolynomial (Fin (X.D + 1) × Fin X.N) F) (Q : MvPolynomial (Fin X.D × Fin X.N) F), (∀ (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin X.D → Fin X.N → E), aeval (fun p : Fin X.D × Fin X.N => s p.1 p.2) Q ≠ 0 → SimpleAt X.toTuple δ f E s) → ∀ s : Fin X.D → Fin X.N → F, eval (fun p : Fin X.D × Fin X.N => s p.1 p.2) Q ≠ 0 → (sysOf X Λ₀).FlatAt δ f s := by
  first | exact @GlobalTheory.HSShort.flatAt_of_simpleAt | exact GlobalTheory.HSShort.flatAt_of_simpleAt | (intros; apply GlobalTheory.HSShort.flatAt_of_simpleAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraMetricConjEmbeddingEqConjStatement
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieAlgebraMetric_conjEmbedding_eq_conj : ∀ (K : Type) [Field K] [NumberField K] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp (𝓞 K))) (F : GlobalTheory.CM.GenFib P) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (σ : K →+* ℂ) (a b : Fin F.P₀.g → K), h.form ((starRingEnd ℂ).comp σ) a b = starRingEnd ℂ (h.form σ a b) := by
  first | exact @GlobalTheory.CM.LieMetricConj.form_conj | exact GlobalTheory.CM.LieMetricConj.form_conj | (intros; apply GlobalTheory.CM.LieMetricConj.form_conj <;> assumption)
end

