import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0098
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0042
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0702
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfLevel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0041
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2534
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormsCommensurable
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
open GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RealMult.PolScale

section Push

variable {R : Type} [CommRing R] {I : Ideal R} {S : Scheme.{0}} {κ : DividedPowers I} {t : S ⟶ Sp R}
  {A : Over S} [GrpObj A]

theorem push_fst_inl (x : Crys κ t A) : push κ t (fst A A) (push κ t (inl A A) x) = x := by
  rw [push_push _ _ _ (lift_fst _ _), push_id]; rfl

theorem push_snd_inl (x : Crys κ t A) : push κ t (snd A A) (push κ t (inl A A) x) = 0 := by
  rw [push_push _ _ _ (lift_snd _ _), push_one]; rfl

theorem push_fst_inr (x : Crys κ t A) : push κ t (fst A A) (push κ t (inr A A) x) = 0 := by
  rw [push_push _ _ _ (lift_fst _ _), push_one]; rfl

theorem push_snd_inr (x : Crys κ t A) : push κ t (snd A A) (push κ t (inr A A) x) = x := by
  rw [push_push _ _ _ (lift_snd _ _), push_id]; rfl

theorem push_fst_diag (x : Crys κ t A) : push κ t (fst A A) (push κ t (lift (𝟙 A) (𝟙 A)) x) = x := by
  rw [push_push _ _ _ (lift_fst _ _), push_id]; rfl

theorem push_snd_diag (x : Crys κ t A) : push κ t (snd A A) (push κ t (lift (𝟙 A) (𝟙 A)) x) = x := by
  rw [push_push _ _ _ (lift_snd _ _), push_id]; rfl

theorem push_swap_inl (x : Crys κ t A) :
    push κ t (lift (snd A A) (fst A A)) (push κ t (inl A A) x) = push κ t (inr A A) x :=
  push_push _ _ _ (by rw [comp_lift, lift_snd, lift_fst]) x

theorem push_swap_inr (x : Crys κ t A) :
    push κ t (lift (snd A A) (fst A A)) (push κ t (inr A A) x) = push κ t (inl A A) x :=
  push_push _ _ _ (by rw [comp_lift, lift_snd, lift_fst]) x

end Push

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]

theorem exists_corrForm (H : Published.AbelianDeRham.Free) (X : Obj F 𝔠 (Sp R)) (c : 𝔠.elt) :
    ∃ φ, IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ :=
  exists_isCorrForm (cupSquare_of_free H (AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab)
    (smooth_prod X.dim X.dim)) (X.isLB c) (X.rig₁ c) (X.rig₂ c)

theorem corrForm_antisymm (H : Published.AbelianDeRham.Free) (X : Obj F 𝔠 (Sp R)) (c : 𝔠.elt)
    {φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R} (hφ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ) (x y : HdR X.A) :
    φ x y = -φ y x := by
  have C := cupSquare_of_free H (AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab) (smooth_prod X.dim X.dim)
  obtain ⟨ψ, hψ, e⟩ := hφ.isPolForm
  obtain ⟨ψ', hψ', k⟩ := hψ.pull (homMor (dp0 R) (𝟙 _) (lift (snd X.A X.A) (fst X.A X.A)))
  have hψ'' : IsPolForm (dp0 R) (𝟙 _) (X.A ⊗ X.A) (X.P c) ψ' := by
    obtain ⟨n, a, b, hc, rfl⟩ := hψ'
    exact ⟨n, a, b, (isChern_existsUnique_and_iso _ _ _ _ _).2 _ _ (pull_isLB (X.isLB c) _) (X.isLB c)
      (X.symm c).symm _ hc, rfl⟩
  have u := Published.AbelianDualCrystal.polForm_unique C (X.isLB c) hψ hψ''
  have k' := k (push (dp0 R) (𝟙 _) (lift (snd X.A X.A) (fst X.A X.A)) (push (dp0 R) (𝟙 _) (inl X.A X.A) x))
    (push (dp0 R) (𝟙 _) (inl X.A X.A) x)
    (push (dp0 R) (𝟙 _) (lift (snd X.A X.A) (fst X.A X.A)) (push (dp0 R) (𝟙 _) (inr X.A X.A) y))
    (push (dp0 R) (𝟙 _) (inr X.A X.A) y) (fun _ ↦ rfl) fun _ ↦ rfl
  rw [← u, RingHom.id_apply, push_swap_inl, push_swap_inr, e, e] at k'
  simp only [push_fst_inl, push_snd_inl, push_fst_inr, push_snd_inr, map_zero, LinearMap.zero_apply,
    sub_zero, zero_sub] at k'
  exact k'

theorem isPolForm_diag (X : Obj F 𝔠 (Sp R)) (c : 𝔠.elt) {φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R}
    (hφ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ) :
    IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) (φ - LinearMap.flip φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R) := by
  obtain ⟨ψ, hψ, e⟩ := hφ.isPolForm
  obtain ⟨ψ', hψ', k⟩ := hψ.pull (homMor (dp0 R) (𝟙 _) (lift (𝟙 X.A) (𝟙 X.A)))
  have eq : (φ - LinearMap.flip φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R) = ψ' := by
    refine LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_
    rw [k (push (dp0 R) (𝟙 _) (lift (𝟙 X.A) (𝟙 X.A)) x) x (push (dp0 R) (𝟙 _) (lift (𝟙 X.A) (𝟙 X.A)) y) y
      (fun _ ↦ rfl) (fun _ ↦ rfl), RingHom.id_apply, e]
    simp only [push_fst_diag, push_snd_diag, LinearMap.sub_apply, LinearMap.flip_apply]
  rw [eq]
  exact hψ'

theorem exists_corrForm_smul (X : Obj F 𝔠 (Sp R)) (a : 𝓞 F) (c : 𝔠.elt) {φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R}
    (hφ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ) :
    ∃ φ' : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R, IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P (a • c)) φ' ∧
      ∀ x y, φ' x y = φ x (act (dp0 R) (𝟙 _) X.rm a y) := by
  haveI := X.rm.hom a
  obtain ⟨φ', h', k⟩ := hφ.pull (X.isLB c) (homMor (dp0 R) (𝟙 _) (𝟙 X.A)) (homMor (dp0 R) (𝟙 _) (X.rm.act a))
    (h := (lift (fst X.A X.A) (snd X.A X.A ≫ X.rm.act a)).left)
    (by simp only [← Over.comp_left, lift_fst, Category.comp_id])
    (by simp only [← Over.comp_left, lift_snd]) (X.isLB (a • c)) (X.smul a c).symm
  refine ⟨φ', h', fun x y ↦ ?_⟩
  rw [k (push (dp0 R) (𝟙 _) (𝟙 X.A) x) x (push (dp0 R) (𝟙 _) (X.rm.act a) y) y (fun _ ↦ rfl) (fun _ ↦ rfl),
    RingHom.id_apply, push_id, act_apply]
  rfl

theorem exists_nat_smul_eq (c c₀ : 𝔠.elt) (h₀ : (c₀ : F) ≠ 0) :
    ∃ (n : ℕ) (t : 𝓞 F), n ≠ 0 ∧ (n : 𝓞 F) • c = t • c₀ := by
  obtain ⟨y, hy, hi⟩ := IsAlgebraic.exists_integral_multiple
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic ((c : F) / c₀)))
  let s : 𝓞 F := ⟨y • ((c : F) / c₀), hi⟩
  have hs : (s : F) * c₀ = (y : F) * c := by
    change y • ((c : F) / c₀) * c₀ = _
    rw [zsmul_eq_mul]; field_simp
  have key : ∀ (n : ℕ) (t : 𝓞 F), (t : F) * c₀ = (n : F) * c → (n : 𝓞 F) • c = t • c₀ := fun n t e ↦ by
    apply Subtype.ext
    simp only [Submodule.coe_smul, Algebra.smul_def, map_natCast]
    exact e.symm.trans rfl
  rcases Int.natAbs_eq y with h | h
  · have hn : ((y.natAbs : ℕ) : F) = (y : F) := by rw [← Int.cast_natCast, ← h]
    exact ⟨y.natAbs, s, Int.natAbs_ne_zero.2 hy, key _ _ (by rw [hs, hn])⟩
  · have hn : (y : F) = -((y.natAbs : ℕ) : F) := by
      rw [← Int.cast_natCast, ← Int.cast_neg]; exact congrArg Int.cast h
    refine ⟨y.natAbs, -s, Int.natAbs_ne_zero.2 hy, key _ _ ?_⟩
    rw [show ((-s : 𝓞 F) : F) = -(s : F) from rfl, neg_mul, hs, hn]; ring

theorem act_natCast (X : Obj F 𝔠 (Sp R)) (n : ℕ) (x : HdR X.A) :
    act (dp0 R) (𝟙 _) X.rm (n : 𝓞 F) x = (n : R) • x := by
  rw [map_natCast]; simp [Nat.cast_smul_eq_nsmul]

end GlobalTheory.RealMult.PolScale

namespace GlobalTheory.RealMult.PolScale

theorem exists_nat_mul_polForm_eq : GlobalTheory.Published.AbelianDeRham → ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R : Type) [CommRing R]
    (X : Obj F 𝔠 (Sp R)) (c c₀ : 𝔠.elt), (c₀ : F) ≠ 0 → ∀ ψ ψ₀ : LinearMap.BilinForm R (HdR X.A),
    IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ → IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c₀) ψ₀ →
    ∃ (n : ℕ) (t : 𝓞 F), n ≠ 0 ∧ ∀ x y, (n : R) * ψ x y = ψ₀ x (act (dp0 R) (𝟙 _) X.rm t y) := by
  intro H F _ _ 𝔠 R _ X c c₀ h₀ ψ ψ₀ hψ hψ₀
  have C := cupSquare_of_free H.1 X.ab X.dim
  have hD : ∀ d : 𝔠.elt, (X.diag d).IsLB := fun d ↦ pull_isLB (X.isLB d) _
  obtain ⟨n, t, hn, e⟩ := exists_nat_smul_eq c c₀ h₀
  obtain ⟨φ, hφ⟩ := exists_corrForm H.1 X c
  obtain ⟨φ₀, hφ₀⟩ := exists_corrForm H.1 X c₀
  obtain ⟨φn, hφn, kn⟩ := exists_corrForm_smul X (n : 𝓞 F) c hφ
  obtain ⟨φt, hφt, kt⟩ := exists_corrForm_smul X t c₀ hφ₀
  rw [e] at hφn
  have u := Published.AbelianDualCrystal.polForm_unique C (hD _) (isPolForm_diag X _ hφn) (isPolForm_diag X _ hφt)
  have u₁ := Published.AbelianDualCrystal.polForm_unique C (hD c) hψ (isPolForm_diag X c hφ)
  have u₂ := Published.AbelianDualCrystal.polForm_unique C (hD c₀) hψ₀ (isPolForm_diag X c₀ hφ₀)
  refine ⟨n, t, hn, fun x y ↦ ?_⟩
  have v := LinearMap.congr_fun (LinearMap.congr_fun u x) y
  rw [u₁, u₂]
  simp only [LinearMap.sub_apply, LinearMap.flip_apply, kn, kt, act_natCast, map_smul, LinearMap.smul_apply,
    smul_eq_mul] at v ⊢
  have a₁ := corrForm_antisymm H.1 X _ hφt y x
  have a₂ := corrForm_antisymm H.1 X c₀ hφ₀ (act (dp0 R) (𝟙 _) X.rm t y) x
  rw [kt, kt] at a₁
  linear_combination v + a₂ - a₁

end GlobalTheory.RealMult.PolScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationPartBaseChange
section
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PolPartPull

def torusExtPull {k Ω : Type} [Field k] [Field Ω] (f : Sp Ω ⟶ Sp k) (G : Over (Sp k)) [GrpObj G]
    (T : TorusExtension G) : TorusExtension ((Over.pullback f).obj G) :=
  letI := T.grpB
  letI := T.addCommGroup
  haveI := T.q_hom
  haveI := T.i_hom
  haveI : IsMonHom (GlobalTheory.splitTorus_baseChange (Sp k) (Sp Ω) f T.X).choose.hom :=
    (GlobalTheory.splitTorus_baseChange (Sp k) (Sp Ω) f T.X).choose_spec.1
  { X := T.X
    addCommGroup := T.addCommGroup
    free := T.free
    finite := T.finite
    B := (Over.pullback f).obj T.B
    grpB := inferInstance
    isAbelian := GlobalTheory.isAbelianScheme_pullback_obj f T.B T.isAbelian
    q := (Over.pullback f).map T.q
    q_hom := inferInstance
    q_flat := MorphismProperty.of_isPullback (P := @Flat) (GlobalTheory.SS.isPullback_overPullback_map_left f T.q) T.q_flat
    q_surjective :=
      MorphismProperty.of_isPullback (P := @Surjective) (GlobalTheory.SS.isPullback_overPullback_map_left f T.q) T.q_surjective
    q_quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact)
      (GlobalTheory.SS.isPullback_overPullback_map_left f T.q) T.q_quasiCompact
    i := (GlobalTheory.splitTorus_baseChange (Sp k) (Sp Ω) f T.X).choose.hom ≫ (Over.pullback f).map T.i
    i_hom := inferInstance
    isKernel := by
      refine IsPullback.of_iso (T.isKernel.map (Over.pullback f))
        (GlobalTheory.splitTorus_baseChange (Sp k) (Sp Ω) f T.X).choose.symm (Iso.refl _)
        (Functor.Monoidal.εIso (Over.pullback f)).symm (Iso.refl _) ?_ ?_ ?_ ?_
      · simp
      · exact toUnit_unique _ _
      · simp
      · simp }

def oActIso {O : Type} [CommRing O] {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom]
    (a : OAct O A) : OAct O B where
  act x := e.inv ≫ a.act x ≫ e.hom
  hom x := by have := a.hom x; infer_instance
  one := by rw [a.one]; simp
  mul x y := by rw [a.mul]; simp
  add x y := by rw [a.add, MonObj.mul_comp, MonObj.comp_mul]

theorem pbMap_fst {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (a : X ⟶ Y) :
    ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
  pullback.lift_fst _ _ _

theorem rosatiAdj_pull {K K' : Type} [Field K] [Field K'] (f : K →+* K') {P : Out.PolAV (Sp K)}
    {P' : Out.PolAV (Sp K')} {ψ : P'.A.left ⟶ P.A.left} (hψ : IsGrpPullback P'.A P.A (spMap f) ψ)
    (hL : LBIso (P.L.pull ψ) P'.L) {a b : P.A ⟶ P.A} {a' b' : P'.A ⟶ P'.A} (ha : a'.left ≫ ψ = ψ ≫ a.left)
    (hb : b'.left ≫ ψ = ψ ≫ b.left) (hr : Out.RosatiAdj P.A P.L a b) : Out.RosatiAdj P'.A P'.L a' b' := by
  haveI := P.isAb.comm
  haveI := P'.isAb.comm
  let U₂ := lift (pushPt hψ.1.w (fst P'.A P'.A)) (pushPt hψ.1.w (snd P'.A P'.A))
  have u₁ : U₂.left ≫ (fst P.A P.A).left = (fst P'.A P'.A).left ≫ ψ := TripleDescent.lift_left_fst _ _
  have u₂ : U₂.left ≫ (snd P.A P.A).left = (snd P'.A P'.A).left ≫ ψ := TripleDescent.lift_left_snd _ _
  have v₁ : (fst P'.A P'.A ≫ a').left ≫ ψ = U₂.left ≫ (fst P.A P.A ≫ a).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, ← u₁, Category.assoc]
  have v₂ : (snd P'.A P'.A ≫ b').left ≫ ψ = U₂.left ≫ (snd P.A P.A ≫ b).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hb, ← Category.assoc, ← u₂, Category.assoc]
  have hφ : ∀ k, Out.rosatiφ P'.A a' b' k ≫ ψ = U₂.left ≫ Out.rosatiφ P.A a b k := fun k => by
    fin_cases k
    exacts [ArcPull.mul_push hψ U₂.left v₁ u₂.symm, v₁, u₂.symm, ArcPull.mul_push hψ U₂.left u₁.symm v₂, u₁.symm, v₂]
  obtain ⟨t, ht⟩ := RosatiDescent.exists_gen_of_rosatiAdj hr
  obtain ⟨w, hw⟩ := LBIso.symm hL
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : LB.Gen (LB.LinComb P.L (fun k => Out.rosatiφ P'.A a' b' k ≫ ψ) Out.rosatiε), t₁.IsGen := by
    rw [show (fun k => Out.rosatiφ P'.A a' b' k ≫ ψ) = fun k => U₂.left ≫ Out.rosatiφ P.A a b k from funext hφ]
    exact ⟨_, DVR.pullGen_isGen _ _ _ t ht _⟩
  obtain ⟨a₀, ha₀⟩ := exists_down ((isGen_iff w).1 hw) P.isLB P'.isLB t₁ ht₁
  exact fun s => ⟨⊤, trivial, _, DVR.pullGen_isGen _ _ _ a₀ ha₀ _⟩

end GlobalTheory.PolPartPull

namespace GlobalTheory.PolPartPull

theorem polPart_of_isActPull : ∀ (O : Type) [CommRing O] (c : O →+* O) (K K' : Type) [Field K] [Field K'] (f : K →+* K') (G : Over (Sp K)) [GrpObj G] (i : OAct O G) (G' : Over (Sp K')) [GrpObj G'] (i' : OAct O G') (φ : G'.left ⟶ G.left), IsActPull i' i (spMap f) φ → PolPart c i → PolPart c i' := by
  intro O _ c K K' _ _ f G _ i G' _ i' φ h hP
  obtain ⟨T, P, e, j, hm, heq, hr⟩ := hP
  haveI := P.isAb.comm
  haveI := hm
  obtain ⟨P', ψ, -, hψ, hL⟩ := GlobalTheory.exists_isPolFibre GlobalTheory.allSixLaws.1.polBaseChange f P
  obtain ⟨ge, hgm, hgg⟩ := grpPullback_iso (isGrpPullback_pullback G (spMap f)) h.1
  obtain ⟨β, hβm, hβ⟩ := grpPullback_iso (isGrpPullback_pullback P.A (spMap f)) hψ
  haveI := hgm
  haveI := hβm
  have hgi : ∀ a, ge.hom ≫ i'.act a = (Over.pullback (spMap f)).map (i.act a) ≫ ge.hom := fun a => by
    apply Over.OverMorphism.ext
    apply h.1.1.hom_ext
    · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, h.2 a, hgg, ← Category.assoc, hgg,
        pbMap_fst]
    · rw [Over.w, Over.w]
  have h2 : ∀ a, i'.act a ≫ ge.inv = ge.inv ≫ (Over.pullback (spMap f)).map (i.act a) := fun a => by
    rw [Iso.comp_inv_eq, Category.assoc, ← hgi, Iso.inv_hom_id_assoc]
  let j' : OAct O P'.A := oActIso β (OAct.pullback (spMap f) P.A j)
  have hj : ∀ a, (j'.act a).left ≫ ψ = ψ ≫ (j.act a).left := fun a => by
    show (β.inv ≫ (Over.pullback (spMap f)).map (j.act a) ≫ β.hom).left ≫ ψ = _
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hβ, pbMap_fst, ← hβ, ← Category.assoc,
      ← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]
  let T' := torusExtOfIso ge (torusExtPull (spMap f) G T)
  have e1 : T'.q ≫ ((Over.pullback (spMap f)).mapIso e ≪≫ β).hom =
      ge.inv ≫ (Over.pullback (spMap f)).map (T.q ≫ e.hom) ≫ β.hom := by
    show (ge.inv ≫ (Over.pullback (spMap f)).map T.q) ≫ (Over.pullback (spMap f)).map e.hom ≫ β.hom = _
    rw [Functor.map_comp, Category.assoc, Category.assoc]
  refine ⟨T', P', (Over.pullback (spMap f)).mapIso e ≪≫ β, j', ?_, fun a => ?_, fun a =>
    rosatiAdj_pull f hψ hL (hj a) (hj (c a)) (hr a)⟩
  · show IsMonHom (T'.q ≫ ((Over.pullback (spMap f)).mapIso e ≪≫ β).hom)
    rw [e1]
    infer_instance
  · show i'.act a ≫ T'.q ≫ ((Over.pullback (spMap f)).mapIso e ≪≫ β).hom =
      (T'.q ≫ ((Over.pullback (spMap f)).mapIso e ≪≫ β).hom) ≫ j'.act a
    rw [e1]
    show i'.act a ≫ ge.inv ≫ (Over.pullback (spMap f)).map (T.q ≫ e.hom) ≫ β.hom =
      (ge.inv ≫ (Over.pullback (spMap f)).map (T.q ≫ e.hom) ≫ β.hom) ≫ β.inv ≫
        (Over.pullback (spMap f)).map (j.act a) ≫ β.hom
    rw [← Category.assoc (i'.act a), h2]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, heq a]

end GlobalTheory.PolPartPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisationDataIsEvenCubicalOnClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.PreEven
open GlobalTheory.UU GlobalTheory.ClosedPol

set_option maxHeartbeats 1000000 in

theorem evenOn_preU : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P := by
  intro R _ _ _ D A G _ _ U
  have hG := GlobalTheory.firstFiveLaws.1.globalFns
  set g := U.gt 0 with hg
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have hB : IsAbelianScheme (thickObj R (maximalIdeal R) 0 D.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D.P.isAb
  have := hB.comm
  obtain ⟨O, h₁, h₂, h₃, hd⟩ := GlobalTheory.exists_gtDatum_of_splitTorus_extension _ D.X (thickObj R (maximalIdeal R) 0 G)
    (thickObj R (maximalIdeal R) 0 D.P.A) hB g.q g.i g.q_hom g.i_hom g.q_flat g.q_surj inferInstance g.isKernel
  obtain ⟨d, hdq, hdi⟩ := hd hB
  let Q : TQ (thickObj R (maximalIdeal R) 0 G) D.X :=
    { B := thickObj R (maximalIdeal R) 0 D.P.A
      isAb := hB
      q := g.q
      i := g.i
      q_hom := g.q_hom
      i_hom := g.i_hom
      q_flat := g.q_flat
      q_surj := g.q_surj
      q_affine := g.q_affine
      isKernel := g.isKernel
      loc := by
        have l := (TQ.ofGtDatum d).loc
        rw [show (TQ.ofGtDatum d).q = g.q from hdq, show (TQ.ofGtDatum d).i = g.i from hdi] at l
        exact l }
  obtain ⟨P₀, hlev⟩ := exists_isLevelCP (maximalIdeal R) 0 U.P
  obtain ⟨w₀, h₀⟩ := hlev
  obtain ⟨rig, hr, c, σ, h₁, h₂, h₃, H⟩ := exists_isCPMap U.P (toBase_mul_pullback G (thick R (maximalIdeal R) 0)) _
    (pull_isLB U.P.L.isLB _) _ (pullIso_isGen U.P.L.isLB (pullback.fst G.hom (thick R (maximalIdeal R) 0)))
  obtain ⟨w₁, k₁⟩ := cpMap_congr (Category.id_comp _).symm (Category.id_comp _).symm h₀
    (by rw [Category.id_comp, Category.id_comp]; exact pullback.condition)
  obtain ⟨w₂, k₂, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ P₀ _ _ _ (𝟙 _) (by simp) _ H).2
    (toBase_mul_of_isMonHom (𝟙 _) _) w₁ k₁
  have H' := isCPMap_w hG U 0 H
  obtain ⟨w₃, -, k₃⟩ := H'.exists_comp k₂ (by rw [Category.id_comp, Category.id_comp]; exact Over.w (U.gt 0).pG)
  obtain ⟨M, wM, hM⟩ := exists_isLevelCP (maximalIdeal R) 0 (CP.ofDegPre hG D)
  obtain ⟨w₄, k₄⟩ := cpMap_congr rfl (Category.id_comp _) k₃
    (by rw [Category.assoc, pullback.condition, Category.id_comp]; simpa using Over.w g.pG)
  obtain ⟨w₅, k₅, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ M P₀ _ _ _ g.q.left
    ((Over.w g.q).trans (Category.comp_id _).symm) _ hM).2
    (toBase_mul_of_isMonHom g.q _) w₄ k₄
  have De : Q.Desc P₀ := ⟨M, w₅, k₅⟩
  exact ⟨D.X, inferInstance, inferInstance, inferInstance, Q, P₀, ⟨w₀, h₀⟩,
    GlobalTheory.UniformizationSetting.exists_even_of_desc De⟩

end GlobalTheory.Mum.PreEven
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrecompleteOfPowLe
section
noncomputable section

open IsLocalRing

namespace GlobalTheory.FiniteCompletionLocalHom

theorem isLocalHom_of_finite {R R₂ V : Type*} [CommRing R] [IsLocalRing R] [CommRing R₂] [IsLocalRing R₂]
    [CommRing V] [IsLocalRing V] (ρ : R →+* R₂) (hρ : ρ.Finite) (ψ : R₂ →+* V)
    (h : IsLocalHom (ψ.comp ρ)) : IsLocalHom ψ := by
  letI := ρ.toAlgebra
  haveI : Module.Finite R R₂ := hρ
  haveI : Algebra.IsIntegral R R₂ := Algebra.IsIntegral.of_finite R R₂

  have hc : (maximalIdeal V).comap (ψ.comp ρ) = maximalIdeal R :=
    ((IsLocalRing.local_hom_TFAE (ψ.comp ρ)).out 0 4).mp h
  have hP : ((maximalIdeal V).comap ψ).IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R)
    have hc' : ((maximalIdeal V).comap ψ).comap (algebraMap R R₂) = maximalIdeal R := hc
    rw [hc']
    infer_instance
  exact ((IsLocalRing.local_hom_TFAE ψ).out 0 4).mpr (IsLocalRing.eq_maximalIdeal hP)

theorem exists_extension : ∀ (R R₂ W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₂] [IsDomain R₂]
    [IsLocalRing R₂] [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), IsLocalHom φ →
    ∀ (ρ : R →+* R₂), RingHom.Finite ρ → ∀ (Ω : Type) [Field Ω] (j : FractionRing W →+* Ω) (m : R₂ →+* Ω),
    Function.Injective m → (∀ r : R, m (ρ r) = j (algebraMap W (FractionRing W) (φ r))) →
    ∃ (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsLocalRing W₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂)
      (j₂ : FractionRing W₂ →+* Ω), GlobalTheory.LN.CDvr W₂ ∧ GlobalTheory.Mum.FinExt σ ∧ IsLocalHom σ ∧ Function.Injective φ₂ ∧
      IsLocalHom φ₂ ∧ φ₂.comp ρ = σ.comp φ ∧
      (∀ w : W, j₂ (algebraMap W₂ (FractionRing W₂) (σ w)) = j (algebraMap W (FractionRing W) w)) ∧
      ∀ r : R₂, j₂ (algebraMap W₂ (FractionRing W₂) (φ₂ r)) = m r := by
  intro R R₂ W _ _ _ _ _ _ _ _ _ hW φ hφ ρ hρ Ω _ j m hm hcomp
  obtain ⟨hdvr, hcompl, hchar⟩ := (GlobalTheory.LN.cDvr_iff W).mp hW
  haveI := hdvr
  haveI := hcompl
  haveI := hchar
  letI : Algebra (FractionRing W) Ω := j.toAlgebra
  letI : Algebra W Ω := (j.comp (algebraMap W (FractionRing W))).toAlgebra
  haveI : IsScalarTower W (FractionRing W) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl

  obtain ⟨s₀, hs₀int, hs₀⟩ := GlobalTheory.ArcPointDescent.exists_finset ρ hρ φ m (fun r => hcomp r)
  have hmint : ∀ r, IsIntegral W (m r) := fun r =>
    hs₀ (integralClosure W Ω) (fun x hx => hs₀int x hx) r

  let F : IntermediateField (FractionRing W) Ω := algebraicClosure (FractionRing W) Ω
  have hmF : ∀ r, m r ∈ F := fun r =>
    ((hmint r).tower_top : IsIntegral (FractionRing W) (m r))
  letI : Algebra W F := ((algebraMap (FractionRing W) F).comp (algebraMap W (FractionRing W))).toAlgebra
  haveI : IsScalarTower W (FractionRing W) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic W F := (IsFractionRing.comap_isAlgebraic_iff (K := FractionRing W)).mpr inferInstance
  haveI : FaithfulSMul W F := (faithfulSMul_iff_algebraMap_injective W F).mpr
    ((algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective W (FractionRing W)))
  let mF : R₂ →+* F := m.codRestrict F hmF
  obtain ⟨s, hsint, hs⟩ := GlobalTheory.ArcPointDescent.exists_finset ρ hρ φ mF (fun r => Subtype.ext (hcomp r))

  obtain ⟨W', hdvr', hc₁, -, hfin, -, hloc, -, hmem⟩ := GlobalTheory.exists_complete_dvr_finite_subalgebra W F s
  haveI := hdvr'
  have hWs : ∀ a, mF a ∈ W' := hs W' fun x hx => hmem x hx (hsint x hx)
  let φ₂ : R₂ →+* W' := mF.codRestrict W' hWs
  let σ : W →+* W' := algebraMap W W'
  have hσinj : Function.Injective σ := fun a b hab =>
    FaithfulSMul.algebraMap_injective W F (congrArg Subtype.val hab)
  let ι : W' →+* Ω := (algebraMap F Ω).comp (algebraMap W' F)
  have hιinj : Function.Injective ι := fun a b hab => Subtype.ext (Subtype.ext hab)
  let j₂ : FractionRing W' →+* Ω := IsFractionRing.lift hιinj
  have hC : GlobalTheory.LN.CDvr W' :=
    (GlobalTheory.LN.cDvr_iff W').mpr ⟨hdvr', hc₁, charZero_of_injective_algebraMap hσinj⟩
  have hcomm : φ₂.comp ρ = σ.comp φ := RingHom.ext fun r => Subtype.ext (Subtype.ext (hcomp r))
  haveI : IsLocalHom σ := hloc
  have hloc₂ : IsLocalHom (φ₂.comp ρ) := by
    rw [hcomm]
    exact RingHom.isLocalHom_comp σ φ
  refine ⟨W', inferInstance, inferInstance, inferInstance, σ, φ₂, j₂, hC,
    (⟨GlobalTheory.ArcPointDescent.admissibleBase_maximalIdeal_completeDVR hC, hσinj, RingHom.finite_algebraMap.mpr hfin⟩ : _ ∧ _ ∧ _),
    hloc, fun a b hab => hm (congrArg (fun x : W' => ((x : F) : Ω)) hab),
    isLocalHom_of_finite ρ hρ φ₂ hloc₂, hcomm, fun w => IsFractionRing.lift_algebraMap hιinj (σ w),
    fun r => IsFractionRing.lift_algebraMap hιinj (φ₂ r)⟩

end GlobalTheory.FiniteCompletionLocalHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMapPairTimesIdentityFlatSurjectiveAffineStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prodMapPairTimesIdentity_flat_surjective_affine : ∀ (S : Scheme.{0}) (A A' T : Over S) (q : A ⟶ A'), Flat q.left → Surjective q.left → IsAffineHom q.left → Flat (pmap2 q T).left ∧ Surjective (pmap2 q T).left ∧ IsAffineHom (pmap2 q T).left := by
  first | exact @GlobalTheory.CharKer.pmap2_flat_surjective_isAffineHom | exact GlobalTheory.CharKer.pmap2_flat_surjective_isAffineHom | (intros; apply GlobalTheory.CharKer.pmap2_flat_surjective_isAffineHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductAbelianUniformizationStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_abelian_uniformization : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g : ℕ) (u : HolUnif A L g),
    ∃ U : HolUnif (A ⊗ A) (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩ : LB (A ⊗ A).left) (g + g),
      ∀ x y : Fin g → ℂ, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y) := by
  first | exact @GlobalTheory.exists_holUnif_tensor_self | exact GlobalTheory.exists_holUnif_tensor_self | (intros; apply GlobalTheory.exists_holUnif_tensor_self <;> assumption)
end

