import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0259
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0261
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0263
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousLocalLift
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.ExLift

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {M : ℕ}

def liftM (i : R →+ S) (X : Matrix (Fin M) (Fin M) R) : Matrix (Fin M) (Fin M) S :=
  1 + (X - 1).map i

theorem map_addM (i : R →+ S) (A B : Matrix (Fin M) (Fin M) R) :
    (A + B).map i = A.map i + B.map i := by
  ext a b
  simp

theorem map_mulM (i : R →+ S) (hi : ∀ x y, i (x * y) = i x * i y) (A B : Matrix (Fin M) (Fin M) R) :
    (A * B).map i = A.map i * B.map i := by
  ext a b
  simp [Matrix.mul_apply, map_sum, hi]

theorem map_zeroM (i : R →+ S) : (0 : Matrix (Fin M) (Fin M) R).map i = 0 := by
  ext a b
  simp

theorem liftM_one (i : R →+ S) : liftM i (1 : Matrix (Fin M) (Fin M) R) = 1 := by
  unfold liftM
  rw [sub_self, map_zeroM, add_zero]

theorem liftM_mul (i : R →+ S) (hi : ∀ x y, i (x * y) = i x * i y) (X Y : Matrix (Fin M) (Fin M) R) :
    liftM i (X * Y) = liftM i X * liftM i Y := by
  have h : X * Y - 1 = (X - 1) + (Y - 1) + (X - 1) * (Y - 1) := by noncomm_ring
  unfold liftM
  rw [h, map_addM, map_addM, map_mulM i hi]
  noncomm_ring

theorem cT_addM (c : R →+* R) (A B : Matrix (Fin M) (Fin M) R) :
    Formalism.UG.cT c (A + B) = Formalism.UG.cT c A + Formalism.UG.cT c B := by
  ext a b
  simp [Formalism.UG.cT]

theorem liftM_unitary (i : R →+ S) (hi : ∀ x y, i (x * y) = i x * i y) (c : R →+* R) (d : S →+* S)
    (hc : ∀ x, d (i x) = i (c x)) (J₁ : Matrix (Fin M) (Fin M) R) (J₂ : Matrix (Fin M) (Fin M) S)
    (hl : ∀ A : Matrix (Fin M) (Fin M) R, J₂ * A.map i = (J₁ * A).map i)
    (hr : ∀ A : Matrix (Fin M) (Fin M) R, A.map i * J₂ = (A * J₁).map i)
    (X : Matrix (Fin M) (Fin M) R) (hX : Formalism.UG.cT c X * J₁ * X = J₁) :
    Formalism.UG.cT d (liftM i X) * J₂ * liftM i X = J₂ := by
  obtain ⟨A, rfl⟩ : ∃ A, X = 1 + A := ⟨X - 1, by abel⟩
  have hA : (1 + A) - 1 = A := by abel
  set B := Formalism.UG.cT c A with hB
  have h0 : J₁ * A + B * J₁ + B * J₁ * A = 0 := by
    rw [cT_addM, Formalism.UG.cT_one, ← hB] at hX
    have e : (1 + B) * J₁ * (1 + A) - J₁ = J₁ * A + B * J₁ + B * J₁ * A := by noncomm_ring
    rw [← e, hX, sub_self]
  have hd : Formalism.UG.cT d (liftM i (1 + A)) = 1 + B.map i := by
    unfold liftM
    rw [hA, cT_addM, Formalism.UG.cT_one]
    congr 1
    ext a b
    simp [Formalism.UG.cT, hB, hc]
  rw [hd]
  unfold liftM
  rw [hA]
  have e : (1 + B.map i) * J₂ * (1 + A.map i) =
      J₂ + J₂ * A.map i + B.map i * J₂ + B.map i * J₂ * A.map i := by noncomm_ring
  rw [e, hr B, hl A, ← map_mulM i hi, add_assoc, add_assoc, ← map_addM, ← map_addM, ← add_assoc (J₁ * A), h0,
    map_zeroM, add_zero]

def liftH (i : R →+ S) (hi : ∀ x y, i (x * y) = i x * i y) :
    Matrix (Fin M) (Fin M) R →* Matrix (Fin M) (Fin M) S where
  toFun := liftM i
  map_one' := liftM_one i
  map_mul' := liftM_mul i hi

end Ring

section Tens

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

theorem iB_tmul (P : PlaceMap F K) (a : K) (e : E) :
    iB P (a ⊗ₜ[F] e : K ⊗[F] E) = P.inj a ⊗ₜ[F] e := rfl

theorem iB_mul (P : PlaceMap F K) (x y : K ⊗[F] E) : iB P (x * y) = iB P x * iB P y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [add_mul, map_add, ha, hb]
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq => simp only [mul_add, map_add, hp, hq]
    | tmul b f => simp only [Algebra.TensorProduct.tmul_mul_tmul, iB_tmul, map_mul]

theorem iB_sig (P : PlaceMap F K) (σ : E →ₐ[F] E) (x : K ⊗[F] E) :
    sigR (AF F) σ (iB P x) = iB P (sigR K σ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a e => rfl

theorem incl_mul_iB (P : PlaceMap F K) (t : E) (y : K ⊗[F] E) :
    inclR (AF F) t * iB P y = iB P (inclR K t * y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [mul_add, map_add, ha, hb]
  | tmul a e =>
    change ((1 : AF F) ⊗ₜ[F] t) * (P.inj a ⊗ₜ[F] e) = iB P (((1 : K) ⊗ₜ[F] t) * (a ⊗ₜ[F] e))
    simp only [Algebra.TensorProduct.tmul_mul_tmul, iB_tmul, one_mul]

theorem iB_eq_coord [Module.Finite F E] (P : PlaceMap F K) {d : ℕ} (b : Module.Basis (Fin d) F E) (y : K ⊗[F] E) :
    iB P y = (Algebra.TensorProduct.basis (AF F) b).equivFun.symm
      (fun k => P.inj ((Algebra.TensorProduct.basis K b).equivFun y k)) := by
  apply (Algebra.TensorProduct.basis (AF F) b).equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  funext k
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq => simp only [map_add, Pi.add_apply, hp, hq]
  | tmul a e =>
    rw [iB_tmul]
    simp only [Module.Basis.equivFun_apply, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply,
      Finsupp.mapRange_apply, smul_eq_mul]
    rw [show a * algebraMap F K (b.repr e k) = b.repr e k • a by rw [Algebra.smul_def, Algebra.commutes],
      map_smul, Algebra.smul_def, Algebra.commutes]

theorem continuous_iB [IsTopologicalRing K] [Module.Finite F E] (P : PlaceMap F K) :
    Continuous (iB P : K ⊗[F] E →ₗ[F] AF F ⊗[F] E) := by
  haveI : IsModuleTopology K (K ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (K ⊗[F] E) := IsModuleTopology.toContinuousAdd K _
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  let b := Module.finBasis F E
  have h1 : Continuous (Algebra.TensorProduct.basis K b).equivFun.toLinearMap :=
    IsModuleTopology.continuous_of_linearMap _
  have h2 : Continuous (Algebra.TensorProduct.basis (AF F) b).equivFun.symm.toLinearMap :=
    IsModuleTopology.continuous_of_linearMap _
  have h3 : Continuous fun y : K ⊗[F] E =>
      (fun k => P.inj ((Algebra.TensorProduct.basis K b).equivFun y k) : Fin _ → AF F) :=
    continuous_pi fun k => P.cont_inj.comp ((continuous_apply k).comp h1)
  have h4 := h2.comp h3
  convert h4 using 1
  funext y
  exact iB_eq_coord P b y

end Tens

section Group

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

def iBa (P : PlaceMap F K) : K ⊗[F] E →+ AF F ⊗[F] E := (iB P).toAddMonoidHom

theorem iBa_mul (P : PlaceMap F K) (x y : K ⊗[F] E) : iBa (E := E) P (x * y) = iBa P x * iBa P y := iB_mul P x y

theorem JR_mul_map (P : PlaceMap F K) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (A : Matrix (Fin M) (Fin M) (K ⊗[F] E)) :
    JR (AF F) J * A.map (iBa P) = (JR K J * A).map (iBa P) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, JR]
  exact Finset.sum_congr rfl fun k _ => incl_mul_iB P (J a k) (A k b)

theorem map_mul_JR (P : PlaceMap F K) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (A : Matrix (Fin M) (Fin M) (K ⊗[F] E)) :
    A.map (iBa P) * JR (AF F) J = (A * JR K J).map (iBa P) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, JR]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, mul_comm (A a k)]
  exact incl_mul_iB P (J k b) (A a k)

def liftGL (P : PlaceMap F K) (M : ℕ) : GL (Fin M) (K ⊗[F] E) →* GL (Fin M) (AF F ⊗[F] E) :=
  Units.map (liftH (iBa P) (iBa_mul P))

theorem liftGL_mem (P : PlaceMap F K) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x : HR K σ J) : liftGL P M x.1 ∈ HR (AF F) σ J :=
  liftM_unitary (iBa P) (iBa_mul P) (sigR K σ) (sigR (AF F) σ) (iB_sig P σ) (JR K J) (JR (AF F) J)
    (JR_mul_map P J) (map_mul_JR P J) _ x.2

def liftHA (P : PlaceMap F K) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    HA K σ J →* HA (AF F) σ J :=
  ((liftGL P M).comp (HR K σ J).subtype).codRestrict (HR (AF F) σ J) (liftGL_mem P σ J)

theorem liftHA_isLift (P : PlaceMap F K) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    IsLift P σ J (liftHA P σ J) := by
  intro x i j
  change ((1 + (((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) - 1).map (iBa P)) - 1) i j = _
  rw [add_sub_cancel_left]
  rfl

theorem continuous_liftHA [IsTopologicalRing K] [Module.Finite F E] (P : PlaceMap F K) (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Continuous (liftHA P σ J) := by
  haveI : IsModuleTopology K (K ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (K ⊗[F] E) := IsModuleTopology.isTopologicalRing K _
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hi : Continuous (iBa (E := E) P) := continuous_iB P
  have hm : Continuous (liftH (M := M) (iBa P) (iBa_mul (E := E) P)) := by
    refine continuous_matrix fun a b => ?_
    change Continuous fun X : Matrix (Fin M) (Fin M) (K ⊗[F] E) =>
      (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) a b + iBa P (X a b - (1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) a b)
    exact continuous_const.add (hi.comp ((continuous_id.matrix_elem a b).sub continuous_const))
  have hu : Continuous (liftGL (E := E) P M) := Continuous.units_map _ hm
  exact Continuous.subtype_mk (hu.comp continuous_subtype_val) _

end Group

end GlobalTheory.CompanionTheory.SaGen.ExLift

namespace GlobalTheory.CompanionTheory.SaGen.ExLift

theorem exists_continuous_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K),
      ∃ L : HA K σ J →* HA (AF F) σ J, Continuous L ∧ IsLift P σ J L := by
  intro F E _ _ _ _ _ σ _ M J _ K _ _ P
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact ⟨liftHA P σ J, continuous_liftHA P σ J, liftHA_isLift P σ J⟩

end GlobalTheory.CompanionTheory.SaGen.ExLift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLocalFrameOfCoords
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
open TensorProduct DividedPowers

namespace GlobalTheory.CompanionTheory.ConeLocal

theorem dividedPowerFiltration_dividedPowersBot_of_one_le {K : Type} [CommRing K] {r : ℕ} (hr : 1 ≤ r) : pdP (dividedPowersBot K) r = ⊥ := by
  refine Ideal.span_eq_bot.2 ?_
  rintro _ ⟨l, hl, hs, rfl⟩
  have h : ∃ p ∈ l, p.1 ≠ 0 := by
    by_contra h
    push Not at h
    have : (l.map Prod.fst).sum = 0 := List.sum_eq_zero (by simpa using h)
    omega
  obtain ⟨p, hp, h0⟩ := h
  refine List.prod_eq_zero (List.mem_map.2 ⟨p, hp, ?_⟩)
  have e : p.2 = 0 := hl p hp
  rw [e]
  exact (dividedPowersBot K).dpow_eval_zero h0

theorem tfBase_dpBot {K : Type} [Field K] [CharZero K] {s : ℕ} (hs : 1 ≤ s) : TFBase (dividedPowersBot K) 1 s where
  nil := dividedPowerFiltration_dividedPowersBot_of_one_le hs
  tf r x h := by simpa using h
  dv n hn := ⟨0, (n : K)⁻¹, by
    have : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn
    simp [this]⟩

theorem exists_loc : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (c : Coord q W d) (s : ℕ), 1 ≤ s →
    ∃ (E : Frame (sP (KS q s {W})) d) (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s c.t E ε := by
  intro K _ _ X q W d c s hs
  have hb : TFBase (dividedPowersBot K) 1 s := tfBase_dpBot hs
  obtain ⟨c', e, hTF, he1, he2, he3⟩ := GlobalTheory.CompanionTheory.ChartAlg.chart_exists (O := K) (R := K) (dividedPowersBot K) 1 s hb q
    (Ideal.Quotient.mk ⊥) (fun a => rfl) c
  letI := (strV q W).toAlgebra
  have hg := GlobalTheory.CompanionTheory.ChartMaps.good c'
  have hD : KS q s {W} c'.D := ⟨hTF, W, rfl, c'.inV⟩
  obtain ⟨hpow, hc⟩ := GlobalTheory.CompanionTheory.ChartFil.chart_grConst c' hg (KS q s {W}) (ks_in q s W) hD
  let E := c'.frame hg (KS q s {W}) (ks_in q s W) hD
  let ε : Γ(X, W) ≃+* c'.D.B := (Algebra.TensorProduct.lid K Γ(X, W)).symm.toRingEquiv.trans e
  have hε : ∀ f, ε f = e ((1 : K) ⊗ₜ[K] f) := fun f => rfl
  refine ⟨E, ε, hc, fun x hx => ?_, fun a => ?_, fun T u g => ?_, fun i T u v => ?_⟩
  · have h2 : (show c'.D.B from x) ∈ c'.D.pdPow 1 := hx
    rw [hpow, dividedPowerFiltration_dividedPowersBot_of_one_le le_rfl, Ideal.map_bot] at h2
    exact Ideal.mem_bot.1 h2
  · have e1 : (1 : K) ⊗ₜ[K] (strV q W a) = a ⊗ₜ[K] (1 : Γ(X, W)) := by
      have : strV q W a = a • (1 : Γ(X, W)) := by
        rw [Algebra.smul_def, mul_one]; rfl
      rw [this, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    change ε (strV q W a) = c'.D.i a
    rw [hε, e1, he1]
  · have h1 := GlobalTheory.CompanionTheory.GrForm.ev_nat (q := q) u.hom c'.inV (ks_in q s W _ T.property) g
    exact h1.trans ((congrArg (Ideal.quotientMap T.obj.J u.hom.φ u.hom.hle) (he3 g)).trans rfl)
  · change (v.hom.φ (c'.t i) - u.hom.φ (c'.t i) : T.obj.B) = v.hom.φ (ε (c.t i)) - u.hom.φ (ε (c.t i))
    rw [hε, he2]

end GlobalTheory.CompanionTheory.ConeLocal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePlaceNormOneCompactSupport
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaneSA.CptAdelic

variable {F : Type} [Field F] [NumberField F]

def glue (S : Finset (Pl F)) (c : F) (a : ∀ s : S, Kp s.1) : AF F :=
  algebraMap F (AF F) c + ∑ s : S, inc s.1 (a s - algebraMap F (Kp s.1) c)

theorem proj_glue_mem (S : Finset (Pl F)) (c : F) (a : ∀ s : S, Kp s.1) {u : Pl F} (hu : u ∈ S) :
    proj u (glue S c a) = a ⟨u, hu⟩ := by
  have h : proj u (∑ s : S, inc s.1 (a s - algebraMap F (Kp s.1) c)) =
      a ⟨u, hu⟩ - algebraMap F (Kp u) c := by
    rw [map_sum, Finset.sum_eq_single (⟨u, hu⟩ : S)]
    · exact proj_inc_same u _
    · intro b _ hb
      exact proj_inc_ne (fun e => hb (Subtype.ext e.symm)) _
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [glue, map_add, h, AlgHom.commutes, add_sub_cancel]

theorem proj_glue_notMem (S : Finset (Pl F)) (c : F) (a : ∀ s : S, Kp s.1) {u : Pl F}
    (hu : u ∉ S) : proj u (glue S c a) = algebraMap F (Kp u) c := by
  have h : proj u (∑ s : S, inc s.1 (a s - algebraMap F (Kp s.1) c)) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun b _ => proj_inc_ne (fun e => hu ?_) _
    rw [e]
    exact b.2
  rw [glue, map_add, h, AlgHom.commutes, add_zero]

theorem continuous_glue {X : Type*} [TopologicalSpace X] (S : Finset (Pl F)) (c : F)
    {f : X → ∀ s : S, Kp s.1} (hf : ∀ s : S, Continuous fun x => f x s) :
    Continuous fun x => glue S c (f x) :=
  continuous_const.add (continuous_finset_sum _ fun s _ =>
    (continuous_inc s.1).comp ((hf s).sub continuous_const))

def psi (d β : F) (S : Finset (Pl F)) (x : ∀ s : S, Q d β (Kp s.1)) : Q d β (AF F) :=
  ⟨glue S 1 fun s => (x s).re, glue S 0 fun s => (x s).imI, glue S 0 fun s => (x s).imJ,
    glue S 0 fun s => (x s).imK⟩

theorem continuous_psi (d β : F) (S : Finset (Pl F)) : Continuous (psi d β S) := by
  rw [continuous_q_iff]
  refine ⟨continuous_glue S 1 fun s => continuous_re.comp (continuous_apply s),
    continuous_glue S 0 fun s => continuous_imI.comp (continuous_apply s),
    continuous_glue S 0 fun s => continuous_imJ.comp (continuous_apply s),
    continuous_glue S 0 fun s => continuous_imK.comp (continuous_apply s)⟩

theorem qmap_psi_mem (d β : F) (S : Finset (Pl F)) (x : ∀ s : S, Q d β (Kp s.1)) {u : Pl F}
    (hu : u ∈ S) : qmap (proj u) (psi d β S x) = x ⟨u, hu⟩ := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
  · exact proj_glue_mem S 1 _ hu
  · exact proj_glue_mem S 0 _ hu
  · exact proj_glue_mem S 0 _ hu
  · exact proj_glue_mem S 0 _ hu

theorem qmap_psi_notMem (d β : F) (S : Finset (Pl F)) (x : ∀ s : S, Q d β (Kp s.1)) {u : Pl F}
    (hu : u ∉ S) : qmap (proj u) (psi d β S x) = 1 := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
  · exact (proj_glue_notMem S 1 _ hu).trans (map_one _)
  · exact (proj_glue_notMem S 0 _ hu).trans (map_zero _)
  · exact (proj_glue_notMem S 0 _ hu).trans (map_zero _)
  · exact (proj_glue_notMem S 0 _ hu).trans (map_zero _)

theorem q_adele_ext {d β : F} {g h : Q d β (AF F)}
    (H : ∀ u : Pl F, qmap (proj u) g = qmap (proj u) h) : g = h := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
  · exact adele_ext fun u => congrArg (fun y : Q d β (Kp u) => y.re) (H u)
  · exact adele_ext fun u => congrArg (fun y : Q d β (Kp u) => y.imI) (H u)
  · exact adele_ext fun u => congrArg (fun y : Q d β (Kp u) => y.imJ) (H u)
  · exact adele_ext fun u => congrArg (fun y : Q d β (Kp u) => y.imK) (H u)

theorem suppAt_eq_image (d β : F) (S : Finset (Pl F)) :
    SuppAt d β (S : Set (Pl F)) =
      psi d β S '' Set.pi Set.univ fun s : S => {x : Q d β (Kp s.1) | qn x = 1} := by
  ext g
  constructor
  · rintro ⟨hg, hout⟩
    refine ⟨fun s => qmap (proj s.1) g, fun s _ => ?_, q_adele_ext fun u => ?_⟩
    · change qn (qmap (proj s.1) g) = 1
      rw [qn_qmap, hg, map_one]
    · by_cases hu : u ∈ S
      · exact qmap_psi_mem d β S _ hu
      · rw [qmap_psi_notMem d β S _ hu, hout u (by simpa using hu)]
  · rintro ⟨x, hx, rfl⟩
    have hout : ∀ u, u ∉ (S : Set (Pl F)) → qmap (proj u) (psi d β S x) = 1 := fun u hu =>
      qmap_psi_notMem d β S x (by simpa using hu)
    refine ⟨adele_ext fun u => ?_, hout⟩
    rw [← qn_qmap, map_one]
    by_cases hu : u ∈ S
    · rw [qmap_psi_mem d β S x hu]
      exact hx ⟨u, hu⟩ (Set.mem_univ _)
    · rw [hout u (by simpa using hu), qn_one]

theorem isCompact_suppAt {F : Type} [Field F] [NumberField F] (d β : F) (S : Finset (Pl F))
    (h : ∀ s ∈ S, IsCompact {x : Q d β (Kp s) | qn x = 1}) :
    IsCompact (SuppAt d β (S : Set (Pl F))) := by
  rw [suppAt_eq_image]
  exact (isCompact_univ_pi fun s : S => h s.1 s.2).image (continuous_psi d β S)

end GlobalTheory.CompanionTheory.PlaneSA.CptAdelic
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisActionPeriodProductStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_action_period_product : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ)
    (t : (↥K.1 →ₐ[ℚ_[l]] Om l) → Formalism.Per6.BdRp l) (s : Finset (↥K.1 →ₐ[ℚ_[l]] Om l)),
    (∀ μ, μ ∈ s) → (∀ μ, PrePer K χ μ (t μ)) →
    ∀ (g : GQ l) (hg : g ∈ GK K), (∀ (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), g (μ x) = μ x) →
      actB g (∏ μ ∈ s, t μ) =
        algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (Algebra.norm ℚ_[l] ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1)) * ∏ μ ∈ s, t μ := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.actB_prod_periods | exact GlobalTheory.CompanionTheory.LTPer.actB_prod_periods | (intros; apply GlobalTheory.CompanionTheory.LTPer.actB_prod_periods <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeTateCharacterWeightStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_character_weight : ∀ {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥L],
    ((GroundTheory.PAdicHodge.cycloChar L) ''
        {σ : Gal(Om l/↥L) | ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w}).Infinite →
    ∀ (u : (Formalism.Per6.BdRp l)ˣ) (n : ℕ) (a : Gal(Om l/↥L) → ℚ_[l]),
    (∀ σ : Gal(Om l/↥L), σ • (GroundTheory.PAdicHodge.tBdR l ^ n * (u : Formalism.Per6.BdRp l)) =
      algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (a σ) * (GroundTheory.PAdicHodge.tBdR l ^ n * (u : Formalism.Per6.BdRp l))) →
    (∀ σ : Gal(Om l/↥L), (∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w) →
      a σ = (((GroundTheory.PAdicHodge.cycloChar L σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) →
    n = 1 := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.eq_one_of_tpow_mul_unit_eigen | exact GlobalTheory.CompanionTheory.LTPer.eq_one_of_tpow_mul_unit_eigen | (intros; apply GlobalTheory.CompanionTheory.LTPer.eq_one_of_tpow_mul_unit_eigen <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSquareRootsNearOne
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

theorem map_sq_nhds_one_of_normed {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    (h2 : (2 : K) ≠ 0) : Filter.map (fun x : K => x ^ 2) (𝓝 1) = 𝓝 1 := by
  have hd : HasStrictDerivAt (fun x : K => x ^ 2) (2 : K) 1 := by
    simpa using hasStrictDerivAt_pow 2 (1 : K)
  simpa using hd.map_nhds_eq h2

theorem sq_fills_of_map {K : Type*} [Monoid K] [TopologicalSpace K]
    (h : Filter.map (fun x : K => x ^ 2) (𝓝 1) = 𝓝 1) (V : Set K) (hV : V ∈ 𝓝 (1 : K)) :
    ∀ᶠ x in 𝓝 (1 : K), ∃ μ ∈ V, μ ^ 2 = x := by
  have : (fun x : K => x ^ 2) '' V ∈ 𝓝 (1 : K) := by
    rw [← h]; exact Filter.image_mem_map hV
  filter_upwards [this] with x hx
  obtain ⟨μ, hμ, rfl⟩ := hx
  exact ⟨μ, hμ, rfl⟩

theorem sq_fills_nhds_one {F : Type} [Field F] [NumberField F] (u : Pl F) :
    ∀ V ∈ 𝓝 (1 : Kp u), ∀ᶠ x in 𝓝 (1 : Kp u), ∃ μ ∈ V, μ ^ 2 = x := by
  intro V hV
  cases u with
  | inl w =>
    have h2 : (2 : w.Completion) ≠ 0 := by
      have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F w.Completion).injective
      exact two_ne_zero
    have hn : ‖(2 : w.Completion)‖ ≠ 1 := by
      have e : ‖(2 : w.Completion)‖ = ‖InfinitePlace.Completion.extensionEmbedding w 2‖ :=
        ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
          (map_zero _) 2).symm
      rw [e, map_ofNat]
      norm_num
    letI : NontriviallyNormedField w.Completion :=
      NontriviallyNormedField.ofNormNeOne ⟨2, h2, hn⟩
    exact sq_fills_of_map (K := w.Completion) (map_sq_nhds_one_of_normed h2) V hV
  | inr v =>
    letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
    have h2 : (2 : v.adicCompletion F) ≠ 0 := by
      have : CharZero (v.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
      exact two_ne_zero
    exact sq_fills_of_map (K := v.adicCompletion F) (map_sq_nhds_one_of_normed h2) V hV

end GlobalTheory.CompanionTheory.PlaneSA
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSectionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasicoherent_sup_sections : ∀ {X : Scheme.{0}} {E : X.Modules}, E.IsQuasicoherent → ∀ (S T : Subobject E), (S : X.Modules).IsQuasicoherent → (T : X.Modules).IsQuasicoherent → ((S ⊔ T : Subobject E) : X.Modules).IsQuasicoherent ∧ ∀ V : X.Opens, IsAffineOpen V → secs (S ⊔ T) V = {x | ∃ s ∈ secs S V, ∃ t ∈ secs T V, x = s + t} := by
  first | exact @GlobalTheory.CompanionTheory.GE.supsecs | exact GlobalTheory.CompanionTheory.GE.supsecs | (intros; apply GlobalTheory.CompanionTheory.GE.supsecs <;> assumption)
end

