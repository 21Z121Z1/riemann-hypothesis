import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2345
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2661
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubeFaceMiddleProjProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjugateEmbeddingEqConjMulUnitaryStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_conjugate_embedding_eq_conj_mul_unitary : ∀ (K : Type) [Field K] (N : ℕ) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), GlobalTheory.ChowHt.ConjCompat A → (∀ σ, (A σ).det ≠ 0) →
    ∀ σ : K →+* ℂ, ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ, A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U := by
  first | exact @GlobalTheory.ConjUnitary.conj_frame_unitary | exact GlobalTheory.ConjUnitary.conj_frame_unitary | (intros; apply GlobalTheory.ConjUnitary.conj_frame_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameMatrixUnitsIrreducible
section
open CategoryTheory AlgebraicGeometry GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GLPath

open Polynomial

theorem appTop_spec_map {R S : CommRingCat} (g : R ⟶ S) (r : Γ(Spec R, ⊤)) :
    (Spec.map g).appTop r = (Scheme.ΓSpecIso S).inv (g ((Scheme.ΓSpecIso R).hom r)) := by
  have e := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_naturality g)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [← e]
  simp

def line {L : Type} [Field L] {m : ℕ} (A : Matrix (Fin m) (Fin m) L) : Matrix (Fin m) (Fin m) L[X] :=
  (1 - X : L[X]) • (1 : Matrix (Fin m) (Fin m) L[X]) + (X : L[X]) • A.map C

theorem eval_line_zero {L : Type} [Field L] {m : ℕ} (A : Matrix (Fin m) (Fin m) L) (i j : Fin m) :
    eval 0 (line A i j) = (1 : Matrix (Fin m) (Fin m) L) i j := by
  simp only [line, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply, smul_eq_mul]
  split_ifs <;> simp

theorem eval_line_one {L : Type} [Field L] {m : ℕ} (A : Matrix (Fin m) (Fin m) L) (i j : Fin m) :
    eval 1 (line A i j) = A i j := by
  simp only [line, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply, smul_eq_mul]
  split_ifs <;> simp

theorem mapMatrix_line_zero {L : Type} [Field L] {m : ℕ} (A : Matrix (Fin m) (Fin m) L) :
    (evalRingHom (0 : L)).mapMatrix (line A) = 1 := by
  ext i j; exact eval_line_zero A i j

theorem mapMatrix_line_one {L : Type} [Field L] {m : ℕ} (A : Matrix (Fin m) (Fin m) L) :
    (evalRingHom (1 : L)).mapMatrix (line A) = A := by
  ext i j; exact eval_line_one A i j

end GlobalTheory.GLPath

namespace GlobalTheory.GLPath
open Polynomial

theorem exists_path : ∀ (L : Type) [Field L] (ι : Type) [Fintype ι] (n : ι → ℕ)
    (A : ∀ a, Matrix (Fin (n a)) (Fin (n a)) L), (∀ a, IsUnit (A a).det) →
    ∃ (T : Scheme.{0}) (c : T ⟶ Spec (CommRingCat.of L)) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T)
      (_ : t₁ ≫ c = 𝟙 _) (_ : t₂ ≫ c = 𝟙 _) (B : ∀ a, Matrix (Fin (n a)) (Fin (n a)) Γ(T, ⊤)),
      IrreducibleSpace T ∧ (∀ a, IsUnit (B a)) ∧
      (∀ a i j, t₁.appTop (B a i j) = (Scheme.ΓSpecIso (CommRingCat.of L)).inv ((1 : Matrix (Fin (n a)) (Fin (n a)) L) i j)) ∧
      (∀ a i j, t₂.appTop (B a i j) = (Scheme.ΓSpecIso (CommRingCat.of L)).inv (A a i j)) := by
  intro L _ ι _ n A hA
  classical
  set p : L[X] := ∏ a, (line (A a)).det with hp_def
  have hev : ∀ x : L, eval x p = ∏ a, ((evalRingHom x).mapMatrix (line (A a))).det := by
    intro x
    rw [hp_def, ← coe_evalRingHom, map_prod]
    exact Finset.prod_congr rfl fun a _ => RingHom.map_det _ _
  have hu0 : IsUnit ((evalRingHom (0 : L)) p) := by
    rw [coe_evalRingHom, hev]; simp only [mapMatrix_line_zero, Matrix.det_one, Finset.prod_const_one, isUnit_one]
  have hu1 : IsUnit ((evalRingHom (1 : L)) p) := by
    rw [coe_evalRingHom, hev]; simp only [mapMatrix_line_one]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun a _ => hA a
  have hp0 : p ≠ 0 := by
    intro h; rw [h, map_zero] at hu0; exact not_isUnit_zero hu0
  let R := Localization.Away p
  haveI : IsDomain R := IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hp0)
  let c : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of L) :=
    Spec.map (CommRingCat.ofHom ((algebraMap L[X] R).comp C))
  let f₁ : R →+* L := IsLocalization.Away.lift p hu0
  let f₂ : R →+* L := IsLocalization.Away.lift p hu1
  have hf : ∀ (x : L) (hx : IsUnit ((evalRingHom x) p)) (q : L[X]),
      (IsLocalization.Away.lift (S := R) p hx) (algebraMap L[X] R q) = eval x q := by
    intro x hx q
    simp [IsLocalization.Away.lift, IsLocalization.lift_eq]
  have hsec : ∀ (x : L) (hx : IsUnit ((evalRingHom x) p)),
      Spec.map (CommRingCat.ofHom (IsLocalization.Away.lift (S := R) p hx)) ≫ c = 𝟙 _ := by
    intro x hx
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext r
    simp [c, hf]
  let B : ∀ a, Matrix (Fin (n a)) (Fin (n a)) Γ(Spec (CommRingCat.of R), ⊤) := fun a =>
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp (algebraMap L[X] R)).mapMatrix (line (A a))
  have hval : ∀ (x : L) (hx : IsUnit ((evalRingHom x) p)) a i j,
      (Spec.map (CommRingCat.ofHom (IsLocalization.Away.lift (S := R) p hx))).appTop (B a i j) =
        (Scheme.ΓSpecIso (CommRingCat.of L)).inv (eval x (line (A a) i j)) := by
    intro x hx a i j
    rw [appTop_spec_map]
    simp [B, hf]
  refine ⟨Spec (CommRingCat.of R), c, _, _, hsec 0 hu0, hsec 1 hu1, B, inferInstance, ?_, ?_, ?_⟩
  · intro a
    rw [Matrix.isUnit_iff_isUnit_det]
    simp only [B]
    rw [← RingHom.map_det]
    have hdvd : (line (A a)).det ∣ p := Finset.dvd_prod_of_mem _ (Finset.mem_univ a)
    have hpu : IsUnit (algebraMap L[X] R p) := IsLocalization.Away.algebraMap_isUnit p
    rw [RingHom.comp_apply]
    exact (isUnit_of_dvd_unit (map_dvd (algebraMap L[X] R) hdvd) hpu).map _
  · intro a i j
    rw [hval 0 hu0, eval_line_zero]
  · intro a i j
    rw [hval 1 hu1, eval_line_one]

end GlobalTheory.GLPath
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePolynomialCoeffIntegralAlmostAllPrimesStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framePolynomial_coeff_integral_almost_all_primes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), e none = 0 →
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 z.K)), ∀ p ∉ S,
      ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K) (s : z.Kˣ),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : z.K) z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, p.valuation z.K (MvPolynomial.coeff μ G) ≤ 1 := by
  first | exact @GlobalTheory.CoeffInt.coeff_valuation_le_one_almost_all | exact GlobalTheory.CoeffInt.coeff_valuation_le_one_almost_all | (intros; apply GlobalTheory.CoeffInt.coeff_valuation_le_one_almost_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameVectorIsCombinationEigenbasisFlagSpacePointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameVector_isCombination_eigenbasis_flagSpace_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (k : TF.X.F.J) (S : Type) [CommRing S] (z : Sp S ⟶ Y₀ TF.X Z) (hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z), ∃ C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, ∀ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)), IsCombAtG TF.Y.t (z ≫ toBase TF Z) (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩)) (C σ i) (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left := by
  first | exact @GlobalTheory.LogPole.isCombAtG_block | exact GlobalTheory.LogPole.isCombAtG_block | (intros; apply GlobalTheory.LogPole.isCombAtG_block <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPullbackDeRhamMapExists
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf

namespace GlobalTheory.LinFrob

open GlobalTheory.Twist GlobalTheory.ConjSeq

theorem pull_frobDR (p : ℕ) [Fact p.Prime] {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (hR : (p : R) = 0) (hR' : (p : R') = 0) {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')}
    [GrpObj A'] {φ : A'.left ⟶ A.left} (hφ : IsGrpPullback A' A (spMap (algebraMap R R')) φ)
    (c : primDR A) :
    (GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull (frobDR p R hR A c) =
      frobDR p R' hR' A' ((GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull c) := by
  have k := (frobMor p R hR A (cast_left p R hR A)).comp (GlobalTheory.Published.AbelianDeRham.bcMor hφ)
  refine (GrpMor.pull_pull _ _ k (fun _ ↦ rfl) rfl c).trans
    (GrpMor.pull_pull _ _ k (fun r ↦ ?_) (GlobalTheory.VB.frob_naturality p _ φ _) c).symm
  rw [RingHom.comp_apply, frobR_apply, frobR_apply, map_pow]

theorem frobDR_smul (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0)
    {A : Over (Sp R)} [GrpObj A] (r : R) (c : primDR A) :
    frobDR p R hR A (r • c) = r ^ p • frobDR p R hR A c := by
  rw [LinearMap.map_smulₛₗ, frobR_apply]

theorem exists_adjoint {X Y : Scheme.{0}} (f : X ⟶ Y) {G : Y.Modules} {F : X.Modules}
    (i : G ⟶ (Scheme.Modules.pushforward f).obj F) :
    ∃ Ψ : (Scheme.Modules.pullback f).obj G ⟶ F, ∀ (U : X.Opens) (V : Y.Opens) (h : U ≤ f ⁻¹ᵁ V)
      (s : Γ(G, V)), Ψ.app U (GlobalTheory.QCoh.pullbackSections f G h s) =
        resM F h (show Γ(F, f ⁻¹ᵁ V) from i.app V s) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  refine ⟨(adj.homEquiv _ _).symm i, fun U V h s => ?_⟩
  have h1 : adj.unit.app G ≫ (Scheme.Modules.pushforward f).map ((adj.homEquiv _ _).symm i) = i :=
    (adj.homEquiv_unit ..).symm.trans ((adj.homEquiv _ _).apply_symm_apply i)
  refine (app_resM ((adj.homEquiv _ _).symm i) h _).trans (congrArg (resM F h) ?_)
  exact congr(($h1).app V s)

theorem exists_of_semilinear (p : ℕ) [Fact p.Prime] {T : Scheme.{0}} (h0 : (p : Γ(T, ⊤)) = 0)
    (H : T.Modules) (f : ∀ V : T.Opens, IsAffineOpen V → Γ(H, V) → Γ(H, V))
    (hadd : ∀ V hV s t, f V hV (s + t) = f V hV s + f V hV t)
    (hsmul : ∀ V hV (r : Γ(T, V)) s, f V hV (r • s) = r ^ p • f V hV s)
    (hres : ∀ V V' hV hV' (h : V' ≤ V) s, f V' hV' (resM H h s) = resM H h (f V hV s)) :
    ∃ Ψ : (GlobalTheory.VB.frobPull p h0).obj H ⟶ H, ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      Ψ.app V (GlobalTheory.QCoh.pullbackSections (GlobalTheory.VB.frob T p h0) H (le_refl V) s) = f V hV s := by
  let G : T.Modules := (Scheme.Modules.pushforward (GlobalTheory.VB.frob T p h0)).obj H
  let j : ∀ V : T.Opens, IsAffineOpen V → Γ(H, V) →ₗ[Γ(T, V)] Γ(G, V) := fun V hV =>
    { toFun := f V hV
      map_add' := hadd V hV
      map_smul' := fun r s => by
        refine (hsmul V hV r s).trans ?_
        rw [← GlobalTheory.VB.frob_app p h0 V r]
        rfl }
  obtain ⟨i, hi⟩ := GlobalTheory.hom_of_affine_compatible T H G j hres
  obtain ⟨Ψ, hΨ⟩ := exists_adjoint (GlobalTheory.VB.frob T p h0) i
  refine ⟨Ψ, fun V hV s => (hΨ V V (le_refl V) s).trans ?_⟩
  refine (resM_self (F := H) (le_refl V) _).trans ?_
  exact LinearMap.congr_fun (hi V hV) s

theorem frobDR_res (p : ℕ) [Fact p.Prime] {T : Scheme.{0}} (h0 : (p : Γ(T, ⊤)) = 0) (A : Over T)
    [GrpObj A] (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV))
    (he : IsDRIso A H e) {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
    (s : Γ(H, V)) :
    (e V' hV').symm (frobDR p Γ(T, V') (GlobalTheory.SS.FrobField.cast_zero h0 V') (onAff A hV')
      (e V' hV' (resM H h s))) =
    resM H h ((e V hV).symm (frobDR p Γ(T, V) (GlobalTheory.SS.FrobField.cast_zero h0 V) (onAff A hV)
      (e V hV s))) := by
  letI := resAlg h
  obtain ⟨φ, hφ, hφ'⟩ := VB.exists_transition A hV hV' h
  have a := he V V' hV hV' h φ hφ hφ'
  refine (e V' hV').symm_apply_eq.2 (Eq.trans ?_ (a _).symm)
  refine (congrArg (frobDR p Γ(T, V') (GlobalTheory.SS.FrobField.cast_zero h0 V') (onAff A hV'))
    (a s)).trans ?_
  refine (pull_frobDR p (GlobalTheory.SS.FrobField.cast_zero h0 V) _ hφ _).symm.trans ?_
  exact congrArg (GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull ((e V hV).apply_symm_apply _).symm

theorem exists_linFrob : GlobalTheory.CovTop.Hypotheses2 → ∀ (p : ℕ) [Fact p.Prime] {T : Scheme.{0}} [Algebra (ZMod p) Γ(T, ⊤)] (A : Over T) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)), IsDRIso A H e →
    ∃ Ψ : (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).obj H ⟶ H, ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      e V hV ((Ψ).app V (GlobalTheory.QCoh.pullbackSections (GlobalTheory.VB.frob T p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))) H
        (le_refl V) s)) =
      GlobalTheory.ConjSeq.frobDR p Γ(T, V) (GlobalTheory.SS.FrobField.cast_zero (GlobalTheory.VB.natCast_eq_zero T p (ZMod p)) V)
        (onAff A hV) (e V hV s) := by
  intro _ p _ T _ A _ g _ _ H e he
  have key : ∀ h0 : (p : Γ(T, ⊤)) = 0, ∃ Ψ : (GlobalTheory.VB.frobPull p h0).obj H ⟶ H,
      ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
        Ψ.app V (GlobalTheory.QCoh.pullbackSections (GlobalTheory.VB.frob T p h0) H (le_refl V) s) =
          (e V hV).symm (frobDR p Γ(T, V) (GlobalTheory.SS.FrobField.cast_zero h0 V) (onAff A hV)
            (e V hV s)) := fun h0 => by
    refine exists_of_semilinear p h0 H _ (fun V hV s t => ?_) (fun V hV r s => ?_)
      fun V V' hV hV' h s => ?_
    · rw [map_add, map_add, map_add]
    · rw [(e V hV).map_smul, frobDR_smul, (e V hV).symm.map_smul]
    · exact frobDR_res p h0 A H e he hV hV' h s
  obtain ⟨Ψ, hΨ⟩ := key (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))
  exact ⟨Ψ, fun V hV s => (congrArg (e V hV) (hΨ V hV s)).trans ((e V hV).apply_symm_apply _)⟩

end GlobalTheory.LinFrob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FstGenericAppInjective
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem fst_generic_app_injective {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} (p : X ⟶ Sp R) [Flat p]
    (W : X.Opens) : Function.Injective ((pullback.fst p (jK R)).app W).hom := by
  have : IsDominant (jK R) := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (algebraMap R (FractionRing R)))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have : IsSchemeTheoreticallyDominant (pullback.fst p (jK R)) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback p (jK R)).flip
  exact (pullback.fst p (jK R)).app_injective W

theorem SecRatioEq.of_comp {X Y Z : Scheme.{0}} (L : LB X) {k k' : ℕ} (f : Z ⟶ Y)
    (hf : ∀ W : Y.Opens, Function.Injective (f.app W).hom) (u v : Y ⟶ X) (s₁ s₂ : H0 L k) (t₁ t₂ : H0 L k')
    (h : SecRatioEq L (f ≫ u) (f ≫ v) s₁ s₂ t₁ t₂) : SecRatioEq L u v s₁ s₂ t₁ t₂ := by
  intro i i'
  apply hf
  have key : ∀ {U V : Y.Opens} (e : U ≤ V) (a : Γ(Y, V)),
      (f.app U).hom ((Y.presheaf.map (homOfLE e).op).hom a) =
        (Z.presheaf.map (homOfLE (show f ⁻¹ᵁ U ≤ f ⁻¹ᵁ V from fun _ hx => e hx)).op).hom ((f.app V).hom a) := by
    intro U V e a
    exact congrArg (fun φ => φ.hom a) (f.naturality (homOfLE e).op)
  rw [map_mul, map_mul, key, key, key, key]
  exact h i i'

theorem secRatioEq_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (k k' : ℕ) (s₁ s₂ : H0 U.LG.L k) (t₁ t₂ : H0 U.LG.L k') (φ : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G), SecRatioEq U.LG.L (φ.left ≫ pullback.fst G.hom (jK R)) (pullback.fst G.hom (jK R)) s₁ s₂ t₁ t₂ → ∀ g : G ⟶ G, (Over.pullback (jK R)).map g = φ → SecRatioEq U.LG.L g.left (𝟙 G.left) s₁ s₂ t₁ t₂ := by
  intro R _ _ _ _ D A G _ _ _ U k k' s₁ s₂ t₁ t₂ φ h g hg
  subst hg
  have := U.smooth
  refine SecRatioEq.of_comp _ (pullback.fst G.hom (jK R)) (fst_generic_app_injective G.hom) _ _ _ _ _ _ ?_
  have e : ((Over.pullback (jK R)).map g).left ≫ pullback.fst G.hom (jK R) = pullback.fst G.hom (jK R) ≫ g.left :=
    pullback.lift_fst _ _ _
  rw [Category.comp_id, ← e]
  exact h

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyCoordinateCombinationsNoCommonZeroStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fubiniStudy_coordinate_combinations_noCommonZero : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (m N : ℕ) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (u : Fin (m + 1) → V) (b : Module.Basis (Fin N) K V) (c : Matrix (Fin (m + 1)) (Fin N) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ),
    g ≫ PSpace.str (𝓞 K) m = p →
    (∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g = 0) →
    (∀ j, b j = ∑ k, c k j • u k) → (∀ σ, (A σ).det ≠ 0) →
    ∀ τ : 𝓞 K →+* ℂ, Weight.NoCommonZero fun a => ∑ k, (c.map (OfLattice.extEmb τ) * A (OfLattice.extEmb τ)) k a • secVal p τ (GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g) := by
  first | exact @GlobalTheory.FubiniStudyFrame.noCommonZero_comb | exact GlobalTheory.FubiniStudyFrame.noCommonZero_comb | (intros; apply GlobalTheory.FubiniStudyFrame.noCommonZero_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GAdjSwapComp
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam

def chartPullPerm {X Y Y' : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    (φ' : K' → (Y' ⟶ X)) (φ : K → (Y ⟶ X)) (ε' : K' → ℤ) (ε : K → ℤ) (h : Y' ⟶ Y) (e : K' ≃ K)
    (hc : ∀ k, φ' (e.symm k) = h ≫ φ k) (hε : ∀ k, ε' (e.symm k) = ε k) :
    ChartPull (LB.LinComb L φ' ε') (LB.LinComb L φ ε) h :=
  have le : ∀ j : K' → L.ι, LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ (fun k => j (e.symm k)) :=
    fun j y hy => Set.mem_iInter.2 fun k => by
      have := Set.mem_iInter.1 hy (e.symm k)
      rw [hc] at this
      exact this
  { idx := fun j k => j (e.symm k)
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L φ' ε' (𝟙 Y') y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb L φ ε h y _ _ (le j hj) (le j' hj')).symm)
      refine (Fintype.prod_equiv e.symm _ _ fun k => ?_).symm
      rw [Category.id_comp, hc, hε] }

theorem psum_perm {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (σ : Fin n ≃ Fin n) (hx : ∀ i, x' i = h ≫ x (σ i))
    (I : Finset (Fin n)) : psum G x' I = h ≫ psum G x (I.map σ.toEmbedding) := by
  rw [CubePf.CubeCoordinateSums.psum_eq_prod, CubePf.CubeCoordinateSums.psum_eq_prod, CubePf.CubeCoordinateSums.comp_prod, Finset.prod_map]
  exact Finset.prod_congr rfl fun i _ => hx i

def chartPullCube {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (σ : Fin n ≃ Fin n) (hx : ∀ i, x' i = h ≫ x (σ i))
    (L : LB G.left) : ChartPull (cubeLB G x' L) (cubeLB G x L) h.left :=
  chartPullPerm L _ _ _ _ h.left (Equiv.ulift.trans ((Equiv.finsetCongr σ).trans Equiv.ulift.symm))
    (fun k => by
      show (psum G x' ((Equiv.finsetCongr σ).symm k.down)).left = h.left ≫ (psum G x k.down).left
      rw [psum_perm G h x x' σ hx, Over.comp_left]
      congr 3
      exact (Equiv.finsetCongr σ).apply_symm_apply k.down)
    (fun k => by
      show (-1 : ℤ) ^ (n - ((Equiv.finsetCongr σ).symm k.down).card) = (-1) ^ (n - k.down.card)
      simp [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply])

end GlobalTheory.MumFam

namespace GlobalTheory.MumFam

theorem gAdj_swap {S : Scheme.{0}} {G₁ G₂ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    {L₁ : LB G₁.left} {L₂ : LB G₂.left} {u : G₁ ⟶ G₂} {u' : G₂ ⟶ G₁} (H : GAdj L₁ L₂ u u') : GAdj L₂ L₁ u' u :=
  LBIso.chartPull
    (chartPullCube G₁ (lift (snd G₂ G₁) (fst G₂ G₁)) ![fst G₁ G₂, snd G₁ G₂ ≫ u'] ![fst G₂ G₁ ≫ u', snd G₂ G₁]
      (Equiv.swap 0 1) (fun i => by fin_cases i <;> simp) L₁)
    (chartPullCube G₂ (lift (snd G₂ G₁) (fst G₂ G₁)) ![fst G₁ G₂ ≫ u, snd G₁ G₂] ![fst G₂ G₁, snd G₂ G₁ ≫ u]
      (Equiv.swap 0 1) (fun i => by fin_cases i <;> simp) L₂)
    (LBIso.symm H)

theorem gAdj_comp {S : Scheme.{0}} {G₁ G₂ G₃ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    [GrpObj G₃] [IsCommMonObj G₃] {L₁ : LB G₁.left} {L₂ : LB G₂.left} {L₃ : LB G₃.left} (hL₁ : L₁.IsLB)
    (hL₂ : L₂.IsLB) (hL₃ : L₃.IsLB) {u : G₁ ⟶ G₂} {u' : G₂ ⟶ G₁} {v : G₂ ⟶ G₃} {v' : G₃ ⟶ G₂}
    (H : GAdj L₁ L₂ u u') (H' : GAdj L₂ L₃ v v') : GAdj L₁ L₃ (u ≫ v) (v' ≫ u') :=
  LBIso.trans (LB.isLB_linComb hL₃ _ _) (LB.isLB_linComb hL₂ _ _) (LB.isLB_linComb hL₁ _ _)
    (LBIso.chartPull
      (chartPullCube G₃ (lift (fst G₁ G₃ ≫ u) (snd G₁ G₃)) ![fst G₂ G₃ ≫ v, snd G₂ G₃]
        ![fst G₁ G₃ ≫ u ≫ v, snd G₁ G₃] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₃)
      (chartPullCube G₂ (lift (fst G₁ G₃ ≫ u) (snd G₁ G₃)) ![fst G₂ G₃, snd G₂ G₃ ≫ v']
        ![fst G₁ G₃ ≫ u, snd G₁ G₃ ≫ v'] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₂) H')
    (LBIso.chartPull
      (chartPullCube G₂ (lift (fst G₁ G₃) (snd G₁ G₃ ≫ v')) ![fst G₁ G₂ ≫ u, snd G₁ G₂]
        ![fst G₁ G₃ ≫ u, snd G₁ G₃ ≫ v'] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₂)
      (chartPullCube G₁ (lift (fst G₁ G₃) (snd G₁ G₃ ≫ v')) ![fst G₁ G₂, snd G₁ G₂ ≫ u']
        ![fst G₁ G₃, snd G₁ G₃ ≫ v' ≫ u'] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₁) H)

theorem gAdj_swap_comp :
    (∀ (S : Scheme.{0}) (G₁ G₂ : Over S) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (L₁ : LB G₁.left)
      (L₂ : LB G₂.left), L₁.IsLB → L₂.IsLB → ∀ (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁), GAdj L₁ L₂ u u' → GAdj L₂ L₁ u' u) ∧
    ∀ (S : Scheme.{0}) (G₁ G₂ G₃ : Over S) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] [GrpObj G₃]
      [IsCommMonObj G₃] (L₁ : LB G₁.left) (L₂ : LB G₂.left) (L₃ : LB G₃.left), L₁.IsLB → L₂.IsLB → L₃.IsLB →
      ∀ (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁) (v : G₂ ⟶ G₃) (v' : G₃ ⟶ G₂), GAdj L₁ L₂ u u' → GAdj L₂ L₃ v v' →
        GAdj L₁ L₃ (u ≫ v) (v' ≫ u') :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ H => gAdj_swap H,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ _ _ _ _ H H' => gAdj_comp h₁ h₂ h₃ H H'⟩

end GlobalTheory.MumFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalLabAlt
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {cf : Coeff l} {C : UCompact Xo cf} {X₁ : USetup C}

def UDeep.GalLab (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (a : D.X.S.Gam ≃+ D.X.S.Gam) : Prop :=
  ∃ (P₀ : PolAV (Sp D.X.Ω₁)) (b : P₀.A.left ⟶ D.X.ρ.P.A.left) (t : P₀.A.left ⟶ P₀.A.left),
    IsGrpPullback P₀.A D.X.ρ.P.A (spMap D.X.S.R.val.toRingHom) b ∧
    IsGrpPullback P₀.A P₀.A (spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) t ∧
    LBIso P₀.L (D.X.ρ.P.L.pull b) ∧ LBIso P₀.L (P₀.L.pull t) ∧
    ∀ x (w w' : Sp D.X.Ω₁ ⟶ P₀.A.left), w ≫ b = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left →
      w' ≫ t = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ w →
        w' ≫ b = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt (a x)).left

end GlobalTheory.UPoinc
end
end

