import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0258
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0610
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0244
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0448
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClsEqHomModInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0620
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientOfFullRepresentation
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0528
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0524
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0547
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0534
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0538
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0336
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0553
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterPairingHarishChandraCuspidalMackey
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0611
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0540
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0619
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdaptedBasisThetaGaloisFixedPolesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adaptedBasis_theta_galoisFixed_poles : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (C : Core l), C.InvdR → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), F.IsDR → Y.map (inclW l) = inclW l τ ^ N • F.T → ∀ H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K, (∀ (g : ↥(GK K)) (z : ℂ_[l]), IsZ bk g z → ∃ u : Matrix (Fin d) (Fin d) (ℂ_[l]), u * Y.map ((Per.θD l).comp (aDp l)) = Y.map ((Per.θD l).comp (aDp l)) * (F.ε g).map ((Per.θD l).comp (aDp l)) ∧ u * H.V.map (Per.θD l) = H.V.map (Per.θD l) * Matrix.diagonal fun i => z ^ ((H.p i : ℤ) - H.q)) ∧ ∀ N₀ : ℕ, N₀ ≤ N → (∀ i, |(H.p i : ℤ) - H.q| ≤ N₀) → (∀ i j, bk.E ^ (N - N₀) ∣ F.A i j) ∧ ∀ i j, bk.E ^ (N - N₀) ∣ F.A' i j := by
  first | (exact @GlobalTheory.BKLim.adaptedBasis_theta_and_poles) | (exact GlobalTheory.BKLim.adaptedBasis_theta_and_poles) | (intros; apply GlobalTheory.BKLim.adaptedBasis_theta_and_poles  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientExtensionIffAdmissibleExtStatement
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_quotientExtension_iff_admissible_ext : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) (jT : ZMod S.n → ℤ → ℤ),
    (∀ i a, ((S.D.Ut i).count a : ℤ) = jT i a) →
    ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (L : Lattice (O := S.O) T.ρ) (X : Type) [AddCommGroup X] [Module S.O X]
      (z : S.G → ↥L.T ⊗[S.O] X) (hz : z ∈ Z1 (twCoef (latRep L) S.Γ.χ₁ X) ⊤) (a : ℕ)
      (ha : ∀ x : X, S.Γ.lam ^ a • x = 0),
      (tableLineDegreeTwo.AdmQ (P.PD S.K) S.emb S.Γ.lam jT (tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t) (tableLineDegreeTwo.actExt L X S.Γ.χ₁ z)
                         (tableLineDegreeTwo.kerExt L X S.Γ.lam a) ↔ S.admitted (Ea (latRep L) S.Γ.χ₁ ha ⟨z, hz⟩)) := by
  first | exact @GlobalTheory.AdmQuotExt.admissible_quotientExtension_iff_admissible_ext' | exact GlobalTheory.AdmQuotExt.admissible_quotientExtension_iff_admissible_ext' | (intros; apply GlobalTheory.AdmQuotExt.admissible_quotientExtension_iff_admissible_ext' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleUntwistedCharUnramifiedOfResidueRealis
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.TopSteps

theorem admissibleUntwistedCharUnramified_of_residueRealisation {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (hT : Nonempty (LocTied l P AI)) (hR : ∀ S : TopSit P, S.Real) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.AdmChiOneUnramified P := by
  intro K LL n r emb D Γ hst hgal h1 h2 h3 X _ _ _
  let S : TopSit P :=
    { K := K, LL := LL, n := n, r := r, nz := ⟨GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.letters_ne_zero hst⟩, emb := emb, D := D, Γ := Γ,
      hyp := ⟨hst, hgal, h1, h2, h3⟩ }
  have hcrys : S.CrysCalc := GlobalTheory.T.crystalline_sums_twists_characters_expected_jumps AI hT S
  have hcl : S.Closed := GlobalTheory.AdmClosure.admissible_closed S
  have hstd : S.StdAdm := StdAdm.stdAdm S hcrys hcl
  have hL : S.Lem0 (S.Γ.Wchi 1) := (GlobalTheory.AdmClasses.admissibleLocalSituation_admissible_classes S hcl hstd).2 1 le_rfl S.D.one_le_letterBlockLength
  have hb : S.ResBound (S.Γ.Wchi 1) 1 := (CharBound.resBound_chars S (hR S)).2 hL
  have hu : S.UnrAdm := GlobalTheory.UnramAdm.unramified_admissible S hcrys hcl hstd hL
  exact ChiOne.cls_eq_homModInertia S hL hb hu X

end GlobalTheory.TopSteps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientDualCrystallineAndPureOfDecompStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ambientDual_crystalline_and_pure_of_decomp : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), TruncatedSeriesCountingIdentities.admG2 (D := D) i r ρ π → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambW (D := D) i ρ π dc ∧ EmbeddingTypes.ambT2 (D := D) i ρ π dc := by
  first | exact @GlobalTheory.AmbWT.main | exact GlobalTheory.AmbWT.main | (intros; apply GlobalTheory.AmbWT.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorIdentificationNatural
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.Natural

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem inclL_smul (P : PhiMod O K l e a ι) (r : OA l O) (c : ι → OA l O) :
    inclL t ϖ P (r • c) = inclO l O r • inclL t ϖ P c := by
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp [map_mul]

theorem homW_inclL {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : BK.Hom P Q) (c : ι → OA l O) :
    homW t ϖ F (inclL t ϖ P c) = inclL t ϖ Q (((homMat t ϖ F).map (frobOA l O)) *ᵥ c) := by
  rw [homW_apply, inclL_apply, Matrix.mulVec_mulVec, homMat_mul_frobMat, ← Matrix.mulVec_mulVec, inclL_apply]
  have hM : ((homMat t ϖ F).map (inclO l O)).map (frobOW l O) =
      ((homMat t ϖ F).map (frobOA l O)).map (inclO l O) := by
    ext i j; simp [frobOW_inclO]
  rw [hM]
  congr 1
  funext i
  exact (RingHom.map_mulVec (inclO l O).toRingHom _ _ i).symm

omit [NeZero a] [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in

theorem map_id_smul {G : Type} [Group G] [TopologicalSpace G] {T T' : LocLat G ℚ_[l] K O}
    (g : ↥T.L.T →ₗ[O] ↥T'.L.T) (r : OB l O) (x : TW (OB l O) T) :
    TensorProduct.map LinearMap.id g (r • x) = r • TensorProduct.map LinearMap.id g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b y => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem toBcris_hom {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : BK.Hom P Q) (m : P.MMl)
    (m' : Q.MMl) (hm : m'.1 = F.app m.1) :
    toBcris t ϖ Q m' = (((homMat t ϖ F).map (frobOA l O)).map (toB l O)) *ᵥ toBcris t ϖ P m := by
  have hmat : ∀ τ, Q.mxInv τ * F.mat τ = (F.mat (τ - 1)).map (frob K l) * P.mxInv τ := fun τ => by
    calc Q.mxInv τ * F.mat τ = Q.mxInv τ * F.mat τ * (P.mx τ * P.mxInv τ) := by
          rw [P.mx_mul_mxInv, Matrix.mul_one]
      _ = Q.mxInv τ * (F.mat τ * P.mx τ) * P.mxInv τ := by simp only [Matrix.mul_assoc]
      _ = Q.mxInv τ * Q.mx τ * (F.mat (τ - 1)).map (frob K l) * P.mxInv τ := by
          rw [F.comm]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Q.mxInv_mul_mx, Matrix.one_mul]
  have hA : ∀ (g : ZMod a → A O K) (h : ∀ τ, (g τ : K⟦X⟧) ∈ invL l (S O K e)),
      ϖ.iB t K (fun τ => ⟨(g τ : K⟦X⟧), h τ⟩) = toB l O (ϖ.iTot t K g) := fun g h =>
    (ϖ.iB_of_mem t K (fun τ => ⟨g τ, A_le_S l e (g τ).2⟩)).trans
      (congrArg (toOB l O) (ϖ.iC_of_mem t K g))
  funext i
  rw [toBcris_apply, Matrix.mulVec, dotProduct]
  simp only [Matrix.map_apply, toBcris_apply, homMat, Matrix.of_apply, ← PiSys.iTot_frob]
  trans ∑ j, ϖ.iB t K (fun τ => ⟨(frobAc l (fun τ => ⟨F.mat τ i j, F.mem τ i j⟩) τ : K⟦X⟧),
      le_away _ _ (A_le_S l e (Subtype.prop _))⟩) * ϖ.iB t K (coordL P _ m j)
  swap
  · exact Finset.sum_congr rfl fun j _ => by rw [hA]
  simp only [← map_mul, ← map_sum]
  congr 1
  funext τ
  apply Subtype.ext
  have h1 := congrFun (congrArg (· *ᵥ (m.1 τ)) (hmat τ)) i
  simp only [← Matrix.mulVec_mulVec] at h1
  simp only [Finset.sum_apply, Pi.mul_apply, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]
  change (Q.mxInv τ *ᵥ m'.1 τ) i = ∑ j, frob K l (F.mat (τ - 1) i j) * (P.mxInv τ *ᵥ m.1 τ) j
  rw [hm, BK.Hom.app_apply, h1]
  rfl

variable [TameDescentExponentData K l e a]

theorem jB_hom {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T T' : LocLat (Gl l) ℚ_[l] K O}
    {I : Ident t ϖ P T} {I' : Ident t ϖ Q T'} {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T}
    {jB' : (κ → OB l O) ≃ₗ[OB l O] TW (OB l O) T'} (hB : IsCrisCmp I jB) (hB' : IsCrisCmp I' jB')
    {f : LatHom T.L T'.L} {F : BK.Hom P Q} (hF : IsMapOf I I' f F) (v : ι → OB l O) :
    jB' ((((homMat t ϖ F).map (frobOA l O)).map (toB l O)) *ᵥ v) =
      TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) (jB v) := by
  set Φ := TensorProduct.map (LinearMap.id : OB l O →ₗ[O] OB l O) ((f.f.restrictScalars O).restrict f.T_le) with hΦ
  set H := (homMat t ϖ F).map (frobOA l O) with hH
  let Pr : (ι → OB l O) → Prop := fun v => jB' (H.map (toB l O) *ᵥ v) = Φ (jB v)
  have hsm : ∀ (r : OB l O) v, Pr (r • v) ↔ r • jB' (H.map (toB l O) *ᵥ v) = r • Φ (jB v) := by
    intro r v
    change jB' (H.map (toB l O) *ᵥ (r • v)) = Φ (jB (r • v)) ↔ _
    rw [Matrix.mulVec_smul, map_smul, map_smul, hΦ, map_id_smul]
  have hcancel : ∀ (r : OB l O) v, IsUnit r → Pr (r • v) → Pr v := fun r v hr h =>
    (hr.smul_left_cancel).1 ((hsm r v).1 h)
  have hofT : ∀ x : ↥T.L.T, Pr (jB.symm ((1 : OB l O) ⊗ₜ[O] x)) := by
    intro x
    obtain ⟨m, c, hu, hc, hb⟩ := ((GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι P T I).2 jB hB).2.2.2.1 x
    obtain ⟨m', c', hu', hc', hb'⟩ :=
      ((GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ κ Q T' I').2 jB' hB').2.2.2.1 ⟨f.f x, f.T_le _ x.2⟩
    refine hcancel (toB l O m) _ hu ?_
    have e1 : toB l O m • jB.symm ((1 : OB l O) ⊗ₜ[O] x) = fun i => toB l O (c i) := by
      rw [← map_smul, hb, LinearEquiv.symm_apply_apply]
    change jB' (H.map (toB l O) *ᵥ _) = Φ (jB _)
    rw [e1]
    have e2 : (H.map (toB l O) *ᵥ fun i => toB l O (c i)) = fun i => toB l O ((H *ᵥ c) i) :=
      funext fun i => (RingHom.map_mulVec (toB l O).toRingHom _ _ i).symm
    have hc2 : inclO l O m • I'.ofT ⟨f.f x, f.T_le _ x.2⟩ = inclL t ϖ Q (H *ᵥ c) := by
      rw [← hF.homW_ofT x, ← (homW t ϖ F).map_smul, hc, homW_inclL]
    have heq : m' • (H *ᵥ c) = m • c' := by
      apply inclL_injective t ϖ Q
      rw [inclL_smul, inclL_smul, ← hc2, ← hc', smul_comm]
    have heqB : toB l O m' • (fun i => toB l O ((H *ᵥ c) i)) = toB l O m • fun i => toB l O (c' i) := by
      funext i
      have := congrArg (toB l O) (congrFun heq i)
      simpa [map_mul] using this
    have e3 : jB' (fun i => toB l O ((H *ᵥ c) i)) = toB l O m • ((1 : OB l O) ⊗ₜ[O] (⟨f.f x, f.T_le _ x.2⟩ : ↥T'.L.T)) := by
      refine (hu'.smul_left_cancel).1 ?_
      rw [← map_smul, heqB, map_smul, ← hb', smul_comm]
    rw [e2, e3, ← hb, hΦ, map_id_smul]
    rfl
  obtain ⟨y, rfl⟩ := jB.symm.surjective v
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    have : b ⊗ₜ[O] x = b • ((1 : OB l O) ⊗ₜ[O] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact (hsm b _).2 (by rw [hofT x])
  | add x y hx hy =>
    change jB' (H.map (toB l O) *ᵥ _) = Φ (jB _)
    rw [map_add, Matrix.mulVec_add, map_add, map_add, map_add]
    exact congrArg₂ (· + ·) hx hy

theorem isCrisVal_hom {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T T' : LocLat (Gl l) ℚ_[l] K O}
    {I : Ident t ϖ P T} {I' : Ident t ϖ Q T'} {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T}
    {jB' : (κ → OB l O) ≃ₗ[OB l O] TW (OB l O) T'} (hB : IsCrisCmp I jB) (hB' : IsCrisCmp I' jB')
    {f : LatHom T.L T'.L} {F : BK.Hom P Q} (hF : IsMapOf I I' f F) {w : ι → OW l O} {b : TW (OB l O) T}
    (h : IsCrisVal t ϖ P jB w b) :
    IsCrisVal t ϖ Q jB' (homW t ϖ F w)
      (TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) b) := by
  obtain ⟨m, c, hu, hc, hb⟩ := h
  refine ⟨m, ((homMat t ϖ F).map (frobOA l O)) *ᵥ c, hu, ?_, ?_⟩
  · rw [← (homW t ϖ F).map_smul, hc, homW_inclL]
  · rw [← map_id_smul ((f.f.restrictScalars O).restrict f.T_le), hb, ← jB_hom t ϖ hB hB' hF]
    congr 1
    funext i
    exact (RingHom.map_mulVec (toB l O).toRingHom _ _ i).symm

end GlobalTheory.BKGal.Natural

theorem GlobalTheory.BKGal.cris_natural : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (Q : PhiMod O K l e a κ) (T' : LocLat (Gl l) ℚ_[l] K O) (I' : Ident t ϖ Q T') (jB' : (κ → OB l O) ≃ₗ[OB l O] TW (OB l O) T') (f : LatHom T.L T'.L) (F : GlobalTheory.BK.Hom P Q), IsCrisCmp I' jB' → IsMapOf I I' f F → (∀ (m : P.MMl) (m' : Q.MMl), m'.1 = F.app m.1 → jB' (toBcris t ϖ Q m') = TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) (jB (toBcris t ϖ P m))) ∧ ∀ w b, IsCrisVal t ϖ P jB w b → IsCrisVal t ϖ Q jB' (homW t ϖ F w) (TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) b) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I jB hB κ _ _ Q T' I' jB' f F hB' hF
  refine ⟨fun m m' hm => ?_, fun w b hw => GlobalTheory.BKGal.Natural.isCrisVal_hom t ϖ hB hB' hF hw⟩
  rw [GlobalTheory.BKGal.Natural.toBcris_hom t ϖ F m m' hm]
  exact GlobalTheory.BKGal.Natural.jB_hom t ϖ hB hB' hF _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBasisImagesBasisBdRplus
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem GlobalTheory.BKGal.JumpDR.BasisGlue.exists_basis {R W : Type} [CommRing R] [AddCommGroup W] (act : R →+ (W →+ W))
    (hmul : ∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) (hone : ∀ w : W, act 1 w = w) (eD : R)
    (hbij : Function.Bijective (act eD)) (F : ℤ → W → Prop) (hshift : ∀ (y : W) (j : ℤ), F j y ↔ F (j + 1) (act eD y))
    {ι : Type} [Fintype ι] [DecidableEq ι] (β β₀ : ℕ) (g h b : ι → W) (hg : ∀ i, act (eD ^ β₀) (g i) = h i)
    (hspan : ∀ w, F ((β₀ + β : ℕ) : ℤ) w ↔ ∃ d : ι → R, w = ∑ i, act (d i) (h i))
    (hb0 : ∀ v, F 0 v ↔ ∃ d : ι → R, v = ∑ k, act (d k) (b k))
    (hbi : ∀ d : ι → R, ∑ k, act (d k) (b k) = 0 → ∀ k, d k = 0) :
    ∃ f : ι → W, (∀ i, act (eD ^ β) (f i) = g i) ∧ (∀ v, F 0 v ↔ ∃ d : ι → R, v = ∑ i, act (d i) (f i)) ∧
      ∀ d : ι → R, ∑ i, act (d i) (f i) = 0 → ∀ i, d i = 0 := by
  have hcomm : ∀ (d d' : R) (w : W), act d (act d' w) = act d' (act d w) := by
    intro d d' w
    rw [← hmul, ← hmul, mul_comm]
  have hpow : ∀ (n : ℕ) (w : W), act (eD ^ n) w = (act eD)^[n] w := by
    intro n
    induction n with
    | zero => intro w; rw [pow_zero, hone]; rfl
    | succ n ih => intro w; rw [pow_succ', hmul, ih, Function.iterate_succ_apply']
  have hinj : ∀ n : ℕ, Function.Injective (act (eD ^ n)) := by
    intro n x x' hxx
    rw [hpow, hpow] at hxx
    exact (hbij.1.iterate n) hxx
  have hsh : ∀ (n : ℕ) (w : W) (j : ℤ), F j w ↔ F (j + n) (act (eD ^ n) w) := by
    intro n
    induction n with
    | zero => intro w j; rw [pow_zero, hone, Nat.cast_zero, add_zero]
    | succ n ih =>
      intro w j
      rw [ih w j, hshift (act (eD ^ n) w) (j + n), pow_succ', hmul, Nat.cast_succ, ← add_assoc]
  have hsingle : ∀ (v : ι → W) (i : ι), ∑ k, act ((Pi.single i (1 : R) : ι → R) k) (v k) = v i := by
    intro v i
    rw [Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, map_zero, AddMonoidHom.zero_apply])
      (fun h => (h (Finset.mem_univ i)).elim), Pi.single_eq_same, hone]
  let ginv : W → W := (Equiv.ofBijective _ hbij).symm
  have hginv : ∀ x, act eD (ginv x) = x := fun x => (Equiv.ofBijective _ hbij).apply_symm_apply x
  have h1 : ∀ i, act (eD ^ β) (ginv^[β] (g i)) = g i := by
    intro i
    rw [hpow]
    exact Function.RightInverse.iterate hginv β _
  have h2 : ∀ v, F 0 v ↔ ∃ d : ι → R, v = ∑ i, act (d i) (ginv^[β] (g i)) := by
    have hf : ∀ i, act (eD ^ (β₀ + β)) (ginv^[β] (g i)) = h i := by
      intro i
      rw [pow_add, hmul, hpow β, Function.RightInverse.iterate hginv β, hg]
    intro v
    rw [hsh (β₀ + β) v 0, zero_add, hspan]
    constructor
    · rintro ⟨d, hd⟩
      refine ⟨d, hinj (β₀ + β) ?_⟩
      rw [hd, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcomm, hf i]
    · rintro ⟨d, rfl⟩
      refine ⟨d, ?_⟩
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcomm, hf i]
  refine ⟨fun i => ginv^[β] (g i), h1, h2, ?_⟩
  refine GlobalTheory.T.linearIndependent_of_mutual_span_of_indep R W act hmul hone ι b _ hbi ?_ ?_
  · intro i
    exact (hb0 _).1 ((h2 _).2 ⟨Pi.single i 1, (hsingle (fun i => ginv^[β] (g i)) i).symm⟩)
  · intro k
    exact (h2 _).1 ((hb0 _).2 ⟨Pi.single k 1, (hsingle b k).symm⟩)

set_option maxHeartbeats 8000000 in

theorem GlobalTheory.BKGal.JumpDR.basis_images : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), (∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i)) → ∃ f : ι → T.V ⊗[ℚ_[l]] Pl.R.BdR, (∀ i, A ((ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e)) ^ β) (f i) = ∑ j, A (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i)) (X (jB (Pi.single j 1)))) ∧ (∀ v, v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (0) ↔ ∃ d : ι → OD l ↥(OL LL), v = ∑ i, A (d i) (f i)) ∧ ∀ d : ι → OD l ↥(OL LL), ∑ i, A (d i) (f i) = 0 → ∀ i, d i = 0 := by
  intro hF l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I jB Pl AI Td hC X hX act hA β y hy
  obtain ⟨hmul, hone⟩ := GlobalTheory.T.coeffDeRhamPlusAction_mul_one l LL T Pl AI Td act hA
  obtain ⟨hbij, hshift⟩ := GlobalTheory.T.eisenstein_mul_bijective_shifts_filtrationV l a e ϖ LL T Pl AI Td act hA
  obtain ⟨α, β0, hα, hβ0⟩ := P.exists_exponents
  have hLM1 : ∀ v ∈ P.M, E ↥LL.1 l e ^ (β0 + β) • v ∈ P.L := by
    intro v hv
    have := P.L.smul_mem (⟨_, pow_mem (E_mem l e _) β⟩ : A ↥(OL LL) ↥LL.1) (hβ0 v hv)
    rw [pow_add, mul_comm, mul_smul]
    exact this
  have hβ1 : ∀ τ j i, E ↥LL.1 l e ^ (β0 + β) * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1 := by
    intro τ j i
    have hv : (fun (_ : ZMod a) (i' : ι) => if i' = i then (1 : (↥LL.1)⟦X⟧) else 0) ∈ P.M := by
      refine mem_tot.2 fun τ' i' => ?_
      show (if i' = i then (1 : (↥LL.1)⟦X⟧) else 0) ∈ A ↥(OL LL) ↥LL.1
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have h2 := (P.mem_extc_iff.1 (mem_tot.1 (hLM1 _ hv) τ)) j
    convert h2 using 1
    simp [Matrix.mulVec, dotProduct, mul_comm]
  have hy1 : ∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e)
      (Ehat ↥(OL LL) ↥LL.1 l e ^ β0 * y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e)
      (Ehat ↥(OL LL) ↥LL.1 l e) ^ (β0 + β) * hat ↥(OL LL) l e (P.mxInv τ j i) := fun τ j i =>
    (map_mul _ _ _).trans ((congrArg₂ (· * ·) (map_pow _ _ _) (hy τ j i)).trans
      ((mul_assoc _ _ _).symm.trans (congrArg (· * _) (pow_add _ _ _).symm)))
  have hyA := GlobalTheory.T.coordinates_eq_of_eisensteinPow_mul_inverse_matrix l a e ϖ LL ι P (β0 + β) (fun τ j i => Ehat ↥(OL LL) ↥LL.1 l e ^ β0 * y τ j i) hy1 hβ1
  have hg : ∀ i, act (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ β0)
      (∑ j, act (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i)) (X (jB (Pi.single j 1)))) =
      ∑ j, act (toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1
        (fun τ => ⟨E ↥LL.1 l e ^ (β0 + β) * P.mxInv τ j i, hβ1 τ j i⟩))) (X (jB (Pi.single j 1))) := by
    intro i
    refine (map_sum (act (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ β0)) _ _).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    refine (hmul _ _ _).symm.trans (congrArg (fun z => act z (X (jB (Pi.single j 1)))) ?_)
    refine Eq.trans ?_ (PiSys.iD_ofA (thetaW a LL) ↥LL.1 ϖ _)
    have hpt : (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ β0 * (fun τ => y τ j i) =
        fun τ => ofA ↥(OL LL) ↥LL.1 l e ⟨E ↥LL.1 l e ^ (β0 + β) * P.mxInv τ j i, hβ1 τ j i⟩ :=
      funext fun τ => hyA τ j i
    exact (congrArg (· * ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i))
      (map_pow (ϖ.iD (thetaW a LL) ↥LL.1) (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) β0).symm).trans
      ((map_mul (ϖ.iD (thetaW a LL) ↥LL.1) _ _).symm.trans (congrArg (ϖ.iD (thetaW a LL) ↥LL.1) hpt))
  have hspan := GlobalTheory.T.breuilKisin_filtration_span_deRhamLattice hF l a e ϖ LL hl2 ι P T I jB Pl AI Td hC X hX act hA α (β0 + β) hα hLM1 hβ1
  obtain ⟨b⟩ := GlobalTheory.T.galoisLattice_basis_indexed_by_breuilKisin l a e ϖ LL ι P T I
  obtain ⟨hb0, hbi⟩ := GlobalTheory.T.coeffDeRhamPlus_basis_tensorLattice_free l LL T Pl AI Td act hA ι b
  exact GlobalTheory.BKGal.JumpDR.BasisGlue.exists_basis act hmul hone _ hbij
    (fun (j : ℤ) (v : T.V ⊗[ℚ_[l]] Pl.R.BdR) => v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j)) hshift β β0
    (fun i => ∑ j, act (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i)) (X (jB (Pi.single j 1))))
    (fun i => ∑ j, act (toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1
        (fun τ => ⟨E ↥LL.1 l e ^ (β0 + β) * P.mxInv τ j i, hβ1 τ j i⟩))) (X (jB (Pi.single j 1))))
    (fun k => ((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) hg hspan hb0 hbi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinCoproductUnitCocycleIdentitiesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinCoproduct_unit_cocycle_identities : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (ε : Matrix (Fin d) (Fin d) En.Q.A), ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) → ∀ (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B) (ι : Type), TopBasis (BK.hf f₀) bk.J ι → (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧ ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl → k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f := by
  first | exact @GlobalTheory.BSP.height_rel_unit_cocycle | exact GlobalTheory.BSP.height_rel_unit_cocycle | (intros; apply GlobalTheory.BSP.height_rel_unit_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCuspidalMultisetsTotalDegreeLe
section
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.CuspMultisetCount

theorem degL_toList {g : ℕ} [Fact g.Prime] (M : Multiset (Pc g)) :
    degL M.toList = (M.map fun p => p.1).sum := by
  unfold degL
  conv_rhs => rw [← Multiset.coe_toList M]
  rw [Multiset.map_coe, Multiset.sum_coe]

theorem stdAddChar_ne_one (g : ℕ) [Fact g.Prime] : (ZMod.stdAddChar : AddChar (ZMod g) ℂ) ≠ 1 := by
  intro h
  have h1 := congrArg (fun ψ : AddChar (ZMod g) ℂ => ψ 1) h
  simp only [AddChar.one_apply] at h1
  have h0 : (ZMod.stdAddChar : AddChar (ZMod g) ℂ) 0 = 1 := AddChar.map_zero_eq_one _
  have := ZMod.injective_stdAddChar (N := g) (h1.trans h0.symm)
  exact one_ne_zero this

theorem card_le : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), 0 < n → ∀ S : Finset (Multiset (Pc g)),
    (∀ M ∈ S, (M.map fun p => p.1).sum = n ∧ ∀ p ∈ M, IsCusp p.2) → S.card ≤ g ^ n - g ^ (n - 1) := by
  intro g _ n hn S hS
  set ψ : AddChar (ZMod g) ℂ := ZMod.stdAddChar with hψdef
  have hψ : ψ ≠ 1 := stdAddChar_ne_one g
  have hdeg : ∀ M ∈ S, degL M.toList = n := fun M hM => (degL_toList M).trans (hS M hM).1
  have hcusp : ∀ M ∈ S, ∀ p ∈ M.toList, IsCusp p.2 := fun M hM p hp =>
    (hS M hM).2 p (Multiset.mem_toList.1 hp)
  have hchar : ∀ M ∈ S, IsChar (hcL M.toList n) := fun M hM =>
    (GlobalTheory.gl_list_product_perm_char g M.toList M.toList n (hdeg M hM).symm
      (fun p hp => Label.isChar_of_isIrr (hcusp M hM p hp).2.1)).1
  have key : ∀ M ∈ S, ∃ ρ : Gn g n → ℂ, IsIrr ρ ∧ wh ψ ρ ≠ 0 ∧ ip ρ (hcL M.toList n) ≠ 0 :=
    fun M hM => GlobalTheory.T.exists_generic_constituent_harishChandra_cuspidal g ψ hψ M.toList n (hdeg M hM) (hcusp M hM)
  choose! f hf using key
  have hfin : {ρ : Gn g n → ℂ | IsIrr ρ ∧ wh ψ ρ ≠ 0}.Finite :=
    (GlobalTheory.GLq.irr_finite_and_finsum_zOf_eq_one (Gn g n)).1.subset fun ρ h => h.1
  have hinj : Set.InjOn f (S : Set (Multiset (Pc g))) := by
    intro M hM M' hM' heq
    have h1 := (hf M hM).2.2
    have h2 := (hf M' hM').2.2
    rw [heq] at h1
    have hne := Label.ip_ne_zero_of_common (f M') _ _ (hf M' hM').1 (hchar M hM) (hchar M' hM') h1 h2
    have hp : M.toList.Perm M'.toList := by
      by_contra hnp
      exact hne ((GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp g M.toList M'.toList n (hdeg M hM) (hdeg M' hM')
        (hcusp M hM) (hcusp M' hM')).1 hnp)
    rw [← Multiset.coe_toList M, ← Multiset.coe_toList M']
    exact Multiset.coe_eq_coe.2 hp
  calc S.card = (S : Set (Multiset (Pc g))).ncard := (Set.ncard_coe_finset S).symm
    _ ≤ {ρ : Gn g n → ℂ | IsIrr ρ ∧ wh ψ ρ ≠ 0}.ncard :=
        Set.ncard_le_ncard_of_injOn f (fun M hM => ⟨(hf M hM).1, (hf M hM).2.1⟩) hinj hfin
    _ ≤ g ^ n - g ^ (n - 1) := GlobalTheory.T.ncard_generic_irreducible_characters_GLn_le g ψ hψ n hn

end GlobalTheory.GLq.CuspMultisetCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardHodgeTateJumpsCrystallineEqDimStatement
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_hodgeTate_jumps_crystalline_eq_dim : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (V : Type) [AddCommGroup V] [Module ↥LL.1 V]
      [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V]
      (ρ : Representation ↥LL.1 ↥(GK K) V) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ),
      IsCrys (P.PD K) ρ →
      (∀ i τ, tableLineDegreeTwo.Over (H.W K 1 LL hA.2.2).emb i τ → ∀ a, multV (P.PD K) ρ τ a = (U i).count a) →
      ∀ i, Multiset.card (U i) = Module.finrank ↥LL.1 V := by
  first | exact @GlobalTheory.Per.LetterJumps.card_jumps_letter | exact GlobalTheory.Per.LetterJumps.card_jumps_letter | (intros; apply GlobalTheory.Per.LetterJumps.card_jumps_letter <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassPresFormsFiniteGroupHeckeOperatorsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classPres_forms_finiteGroup_heckeOperators : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) {I : Type} (c : Bridge.CoefDatG Γ) (l : Bridge.LevDatG G) (isT isLoc : I → G → Prop) {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (S : CSD K) {G0 : Type} [Group G0] (inR : I → Prop) (P : Bridge.ClassPres ι S σ c.ρ l.J l.χ), (∀ q, ∃ a : K, σ a = ((l.ch q : ℂˣ) : ℂ)) → (∀ γ x, ∃ x', P.coef x' = c.ρ γ (P.coef x)) → ∀ (red : l.Q →* G0), Function.Surjective red → (∀ q : l.Q, red q = 1 ↔ (q : G) ∈ l.J) → ∀ (hx : I → G) (hA : I → Finset G), (∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ Bridge.IsDC l.J (hx i) (hA i)) → (∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧ (∀ k ∈ l.J, ∃ k₁ ∈ l.J, ∃ k₂ ∈ l.J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧ ∀ k : l.J, (k : G) ∈ Lc → l.χ k = 1) → ∀ one : I → Prop, ∃ (act : Representation K G0 S.Forms) (op : I → Module.End K S.Forms) (B : Bridge.SideRealG ι ⟨c, l, isT, isLoc⟩ σ S act op inR), B.pres = P ∧ B.act_tie.red = red ∧ ∀ i, ¬ inR i → (one i → op i = 1) ∧ (¬ one i → op i = 0) := by
  first | exact @GlobalTheory.sideReal_ofPres | exact GlobalTheory.sideReal_ofPres | (intros; apply GlobalTheory.sideReal_ofPres <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassPresOfFiniteIndexSubLevelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classPres_of_finiteIndex_subLevel : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (S : CSD K) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : Bridge.ClassPres ι S σ ρ J χ) (J' : Subgroup G), J' ≤ J → (J'.subgroupOf J).FiniteIndex → ∀ χ' : J' →* ℂˣ, (∀ k, ∃ a : K, σ a = ((χ' k : ℂˣ) : ℂ)) → (∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x)) → ∃ (Cl : Type) (fC : Fintype Cl) (π : Cl → S.Cl) (k : Cl → J) (Gam : Cl → Type) (gG : ∀ c, Group (Gam c)) (fG : ∀ c, Fintype (Gam c)) (ρ' : ∀ c, Gam c →* Module.End K S.V) (P' : Bridge.ClassPres ι ({ S with Cl := Cl, finCl := fC, Gam := Gam, grpGam := gG, finGam := fG, ρ := ρ', Nab := fun c => S.Nab (π c), Del := fun c => S.Del (π c) } : CSD K) σ ρ J' χ'), (∀ c : Cl, P'.y c = P.y (π c) * (k c : G)) ∧ P'.coef = P.coef := by
  first | exact @GlobalTheory.classPres_subLevel | exact GlobalTheory.classPres_subLevel | (intros; apply GlobalTheory.classPres_subLevel <;> assumption)
end

