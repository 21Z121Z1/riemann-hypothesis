import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdemNotMemFilVOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0233
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordFMemFil
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.HTBasis

variable {l : ℕ} [Fact l.Prime]

def repOf {K LL : FinExt l} {m : ℕ} (r : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1) :
    Representation ↥LL.1 ↥(GK K) (Fin m → ↥LL.1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ↥LL.1 ≃ₐ[↥LL.1] _) : _ →* _).comp
    ((Units.coeHom _).comp r)

theorem repOf_apply {K LL : FinExt l} {m : ℕ} (r : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1)
    (g : ↥(GK K)) (v : Fin m → ↥LL.1) :
    repOf r g v = (r g : Matrix (Fin m) (Fin m) ↥LL.1).mulVec v := rfl

variable (P : LocPrime l) (LL : FinExt l) (m : ℕ)

def embF : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR :=
  (IsScalarTower.toAlgHom ℚ_[l] (Om l) P.R.BdR).comp LL.1.val

theorem embF_apply (x : ↥LL.1) : embF P LL x = algebraMap (Om l) P.R.BdR (x : Om l) := rfl

def mulF : ↥LL.1 ⊗[ℚ_[l]] P.R.BdR →ₐ[ℚ_[l]] P.R.BdR :=
  Algebra.TensorProduct.lift (embF P LL) (AlgHom.id ℚ_[l] P.R.BdR) fun _ _ => Commute.all _ _

@[simp] theorem mulF_tmul (c : ↥LL.1) (b : P.R.BdR) : mulF P LL (c ⊗ₜ[ℚ_[l]] b) = embF P LL c * b := by
  simp [mulF]

def coordF : (Fin m → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (Fin m → P.R.BdR) :=
  TensorProduct.lift (LinearMap.mk₂ ℚ_[l] (fun (v : Fin m → ↥LL.1) (b : P.R.BdR) j => embF P LL (v j) * b)
    (fun v v' b => by funext j; simp [add_mul])
    (fun c v b => by funext j; simp [Algebra.smul_def, mul_assoc])
    (fun v b b' => by funext j; simp [mul_add])
    (fun c v b => by funext j; simp [Algebra.smul_def, mul_left_comm]))

@[simp] theorem coordF_tmul (v : Fin m → ↥LL.1) (b : P.R.BdR) :
    coordF P LL m (v ⊗ₜ[ℚ_[l]] b) = fun j => embF P LL (v j) * b := rfl

section Lemmas

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) (m : ℕ)

theorem coordF_sm (r : ↥LL.1 ⊗[ℚ_[l]] P.R.BdR) (x : (Fin m → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR) :
    coordF P LL m (GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥LL.1 (Fin m → ↥LL.1) r x) = mulF P LL r • coordF P LL m x := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add r s hr hs => simp only [map_add, LinearMap.add_apply, hr, hs, add_smul]
  | tmul c b =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
    | tmul v b' =>
      funext j
      simp only [GlobalTheory.DRFil.sm_tmul, coordF_tmul, mulF_tmul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul]
      ring

theorem embF_mem_fil (K : FinExt l) (c : ↥LL.1) : embF P LL c ∈ (P.PD K).Fil 0 :=
  (GlobalTheory.DeRhamSymbol.mem_iff K 0 _).2 (GlobalTheory.DeRhamSymbol.om_mem _)

theorem coordF_mem_fil (K : FinExt l) {n : ℤ} {x : (Fin m → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR}
    (hx : x ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin m → ↥LL.1) n) (j : Fin m) :
    coordF P LL m x j ∈ (P.PD K).Fil n := by
  obtain ⟨z, rfl⟩ := hx
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, Pi.add_apply]; exact add_mem ha hb
  | tmul v b =>
    have := (P.PD K).Fil_mul 0 n _ _ (embF_mem_fil P LL K (v j)) b.2
    rw [zero_add] at this
    simpa using this

theorem mulF_mem_fil (K : FinExt l) {n : ℤ} {r : ↥LL.1 ⊗[ℚ_[l]] P.R.BdR}
    (hr : r ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) n) : mulF P LL r ∈ (P.PD K).Fil n := by
  obtain ⟨z, rfl⟩ := hr
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add]; exact add_mem ha hb
  | tmul v b =>
    have := (P.PD K).Fil_mul 0 n _ _ (embF_mem_fil P LL K v) b.2
    rw [zero_add] at this
    simpa using this

theorem mulF_idem (K : FinExt l) [FiniteDimensional ℚ_[l] ↥K.1] (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hτ : ∀ x : ↥K.1, ((τ x : ↥LL.1) : Om l) = (x : Om l)) :
    mulF P LL (GlobalTheory.DRFil.idem P.R.BdR τ) = 1 := by
  obtain ⟨n, a, c, h, h1⟩ := GlobalTheory.DRFil.idem_repr P.R.BdR τ
  rw [h, map_sum]
  have e : ∀ i, mulF P LL (a i ⊗ₜ[ℚ_[l]] algebraMap ↥K.1 P.R.BdR (c i)) =
      algebraMap (Om l) P.R.BdR (((a i * τ (c i) : ↥LL.1)) : Om l) := by
    intro i
    rw [mulF_tmul, embF_apply, IntermediateField.coe_mul, map_mul, hτ]
    rfl
  simp only [e, ← map_sum]
  have h2 := congrArg (fun x : ↥LL.1 => (x : Om l)) h1
  simp only [IntermediateField.coe_sum, IntermediateField.coe_one] at h2
  simp only [IntermediateField.coe_mul] at h2 ⊢
  rw [h2, map_one]

theorem coordF_act (K : FinExt l) (r : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1)
    (g : ↥(GK K)) (hg : ∀ x ∈ LL.1, (g : GQ l) x = x) (x : (Fin m → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR) :
    coordF P LL m (actVdR (P.PD K) (repOf r) g x) =
      ((r g : Matrix (Fin m) (Fin m) ↥LL.1).map (embF P LL)).mulVec
        (fun j => P.actQdR (g : GQ l) (coordF P LL m x j)) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, Pi.zero_apply]
    exact (Matrix.mulVec_zero _).symm
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb, ← Matrix.mulVec_add]
    congr 1
    funext j
    simp
  | tmul v b =>
    have hfix : ∀ c : ↥LL.1, P.actQdR (g : GQ l) (embF P LL c) = embF P LL c := fun c => by
      rw [embF_apply, P.actQdR_Om, hg _ c.2]
    funext j
    simp only [actVdR, AlgebraTensorModule.map_tmul, coordF_tmul, repOf_apply, P.PD_actdR,
      Matrix.mulVec, dotProduct, Matrix.map_apply, map_mul, hfix, map_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [AlgHom.toLinearMap_apply, LinearMap.coe_restrictScalars, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
    rw [mul_assoc]
    exact congrArg _ (congrArg _ (P.PD_actdR K g b))

end Lemmas

section Theta

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

def thetaOf (T : LocTied l P AI) : Formalism.MainNotions.LocalSituation.ThetaL P AI :=
  (GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l P AI T).some

def colHT (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {m : ℕ} (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ) :
    Matrix (Fin m) (Fin m) ℂ_[l] :=
  Matrix.of fun j i => J.θ (((GlobalTheory.DeRhamSymbol.tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR) * u i j)

end Theta

end GlobalTheory.HTBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoversAction
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.BKGal.CoversConv

open GlobalTheory.BKReal

variable {l : ℕ} [Fact l.Prime]

def toOC (LL : FinExt l) : OA l ↥(OL LL) →+* OC l :=
  letI : Algebra ℤ_[l] (OC l) := ((Per.θ l).comp (algebraMap ℤ_[l] (Ainf l))).toAlgebra
  (Algebra.TensorProduct.lift (R := ℤ_[l]) (S := ℤ_[l])
    ({ intToOC LL with commutes' := fun z => intToOC_algebraMap LL z } : ↥(OL LL) →ₐ[ℤ_[l]] OC l)
    ({ Per.θ l with commutes' := fun _ => rfl } : Ainf l →ₐ[ℤ_[l]] OC l)
    (fun _ _ => Commute.all _ _)).toRingHom

theorem toOC_tmul (LL : FinExt l) (o : ↥(OL LL)) (x : Ainf l) :
    toOC LL (o ⊗ₜ x) = intToOC LL o * Per.θ l x := rfl

theorem toOC_constA (a : ℕ) [NeZero a] (LL : FinExt l) [HasUnr a LL] (c : ZMod a → ↥(OL LL)) :
    toOC LL (constA (thetaW a LL) c) = intToOC LL (c 0) := by
  obtain ⟨y, rfl⟩ := (splitHom_bijective (thetaW a LL)).2 c
  rw [constA_splitHom]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, toOC_tmul, splitHom_tmul, emb_zero, map_mul,
      intToOC_thetaW]
  | add y y' h h' => simp only [map_add, Pi.add_apply, h, h']

theorem iTot_const {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] {a e : ℕ} [NeZero a]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (c : ZMod a → O) :
    ϖ.iTot t K (fun τ => algebraMap O (A O K) (c τ)) = constA t c := by
  rw [PiSys.iTot, glue_apply, eq_sum_idem]
  simp only [AlgHom.commutes]

end GlobalTheory.BKGal.CoversConv

open GlobalTheory.BKGal.CoversConv GlobalTheory.BKReal in

theorem GlobalTheory.BKGal.covers_action : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (k : GQ l) (γ : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ k γ → (∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ γ.shift.val) ∧ k (ϖ.seq 0) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0 := by
  intro l _ a e _ _ ϖ LL _ _ k γ hc
  set t := thetaW a LL with ht
  have hW : ∀ w : Wq l a, Per.σO k (Per.θ l (wA l a w)) =
      Per.θ l (wA l a ((sigma l a ^ γ.shift.val) w)) := by
    intro w
    have h1 := hc (fun τ => algebraMap _ (A ↥(OL LL) ↥LL.1) (emb t τ w))
      (fun τ => algebraMap _ (A ↥(OL LL) ↥LL.1) (emb t (τ - γ.shift) w)) (fun τ => by
        change _ = rescale (γ.root τ) _
        beta_reduce
        have hC : ∀ (c : ↥(OL LL)) (m : ℕ), coeff m ((algebraMap _ (A ↥(OL LL) ↥LL.1) c : A _ _) : (↥LL.1)⟦X⟧) =
            if m = 0 then algebraMap _ ↥LL.1 c else 0 := fun c m =>
          (congrArg (coeff m) (GlobalTheory.BK.algebraMap_eq_C (K := ↥LL.1) c)).trans (coeff_C ..)
        ext1 n
        rw [coeff_rescale, hC]
        split_ifs with h
        · rw [h, pow_zero, one_mul]
        · rw [mul_zero])
    rw [iTot_const, iTot_const, constA_emb, galOA_tmul] at h1
    have h2 := congrArg (toOC LL) h1
    rw [toOC_tmul, toOC_constA, map_one, one_mul, GlobalTheory.RingBasics.θ_σA] at h2
    rw [h2, ← intToOC_thetaW a LL]
    congr 1
    show t ((sigma l a ^ (-(0 - γ.shift)).val) w) = _
    rw [zero_sub, neg_neg]
  obtain ⟨z, ω, hω, hz, -⟩ := exists_gen l a
  have hpow : ∀ j : ℕ, ((Per.θ l (wA l a (WittVector.teichmuller l (z ^ j))) : OC l) : ℂ_[l]) =
      ((ω ^ j : Om l) : ℂ_[l]) := by
    intro j
    rw [wA_teich, WittVector.fontaineTheta_teichmuller, map_pow, map_pow, SubmonoidClass.coe_pow,
      GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz]
    first
    | exact (map_pow (algebraMap (Om l) ℂ_[l]) ω j).symm
    | norm_cast
    | exact (UniformSpace.Completion.coe_pow ..).symm
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases eq_or_ne x 0 with rfl | hx0
    · rw [map_zero, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]
    · have h1 := one_lt_pow_l l a
      have : NeZero (l ^ a - 1) := ⟨by omega⟩
      have hx1 : x ^ (l ^ a - 1) = 1 := mul_right_cancel₀ hx0 (by
        rw [← pow_succ, Nat.sub_add_cancel h1.le, hx, one_mul])
      obtain ⟨j, -, rfl⟩ := hω.eq_pow_of_pow_eq_one hx1
      have h2 := congrArg (fun y : OC l => (y : ℂ_[l])) (hW (WittVector.teichmuller l (z ^ j)))
      rw [sigma_pow_teich, map_pow (wA l a), map_pow (Per.θ l), SubmonoidClass.coe_pow, hpow] at h2
      replace h2 := (GlobalTheory.RingIface.sigO_coe l k _).symm.trans h2
      rw [hpow, GlobalTheory.RingBasics.σC_coe] at h2
      exact (algebraMap (Om l) ℂ_[l]).injective (h2.trans (map_pow (algebraMap (Om l) ℂ_[l]) _ _).symm)
  · have hr : ∀ τ, IsIntegral ℤ_[l] (γ.root τ) := fun τ =>
      IsIntegral.of_pow (NeZero.pos e) (by rw [γ.root_pow]; exact isIntegral_one)
    let r : ZMod a → ↥(OL LL) := fun τ => ⟨γ.root τ, hr τ⟩
    have h1 := hc (fun _ => uIn (A ↥(OL LL) ↥LL.1))
      ((fun τ => algebraMap _ (A ↥(OL LL) ↥LL.1) (r τ)) * fun _ => uIn (A ↥(OL LL) ↥LL.1)) (fun τ => by
        change ((algebraMap _ (A ↥(OL LL) ↥LL.1) (r τ) : A _ _) : (↥LL.1)⟦X⟧) *
          ((uIn (A ↥(OL LL) ↥LL.1) : A _ _) : (↥LL.1)⟦X⟧) =
          rescale (γ.root τ) ((uIn (A ↥(OL LL) ↥LL.1) : A _ _) : (↥LL.1)⟦X⟧)
        rw [coe_uIn, rescale_X]
        exact congrArg (· * X) (GlobalTheory.BK.algebraMap_eq_C (K := ↥LL.1) (r τ)))
    rw [map_mul (ϖ.iTot t ↥LL.1), iTot_const, PiSys.iTot_u, galOA_tmul] at h1
    have h2 := congrArg (toOC LL) h1
    rw [map_mul (toOC LL), toOC_tmul, toOC_constA, toOC_tmul, map_one, one_mul, one_mul, GlobalTheory.RingBasics.θ_σA,
      PiSys.theta_teich] at h2
    have h3 := (GlobalTheory.RingIface.sigO_coe l k (ϖ.seqO 0)).symm.trans (congrArg (fun y : OC l => (y : ℂ_[l])) h2)
    have h4 := (GlobalTheory.RingBasics.σC_coe k (ϖ.seq 0)).symm.trans h3
    have hr0 : ((r 0 : ↥LL.1) : Om l) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) := by
      simp [r, TameGal.root]
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [map_mul (algebraMap (Om l) ℂ_[l]), ← hr0]
    exact h4
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoversOfAction
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CoverBridge

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a]

theorem galF_val {k : GQ l} {s : ℕ} (hk : ∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ s) (z : Fq l a) :
    Per.σF k (Fq.val l a z) = Fq.val l a z ^ l ^ s := by
  obtain ⟨z₀, ω, hω, hz, h⟩ := exists_gen l a
  have h1 := one_lt_pow_l l a
  have hω' : k ω = ω ^ l ^ s := hk ω (by
    rw [← Nat.sub_add_cancel h1.le, pow_succ, hω.pow_eq_one, one_mul])
  have hd : ¬ l ∣ l ^ a - 1 := fun h => hl.out.not_dvd_one
    ((Nat.dvd_sub_iff_right h1.le (dvd_pow_self l (NeZero.ne a))).1 h)
  have h2 : Per.σF k (Fq.val l a z₀) = Fq.val l a z₀ ^ l ^ s := by
    refine GlobalTheory.UnramIdem.tilt_pow (k := l ^ s) hd dvd_rfl hz fun n => ?_
    obtain ⟨y, y1, y2, y3⟩ := hz n
    refine ⟨Per.σO k y, ?_, by rw [← map_pow, y2, map_one], ?_⟩
    · rw [GlobalTheory.RingIface.sigO_coe l, ← map_pow, y1, GlobalTheory.RingBasics.σC_coe, hω']
    · exact GlobalTheory.AdicMaps.coeff_galois l k _ n y y3
  rcases eq_or_ne z 0 with h0 | h0
  · rw [h0, map_zero, map_zero, zero_pow (pow_pos hl.out.pos s).ne']
  · obtain ⟨j, rfl⟩ := h z h0
    rw [map_pow, map_pow, h2, ← pow_mul, ← pow_mul, mul_comm]

theorem galA_wA {k : GQ l} {s : ℕ} (hk : ∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ s) (w : Wq l a) :
    Per.σA k (wA l a w) = wA l a ((sigma l a ^ s) w) := by
  refine WittVector.ext fun n => ?_
  refine (GlobalTheory.RingIface.sigA_coeff l k _ n).trans ?_
  change Per.σF k (Fq.val l a (w.coeff n)) = Fq.val l a (((sigma l a ^ s) w).coeff n)
  rw [coeff_sigma_pow, map_pow, galF_val hk]

variable {e : ℕ} [NeZero e]

theorem isTiltOf_kummer (ϖ : PiSys l e) {k : GQ l} (hk : k ∈ ϖ.GKinf) {ζ : Om l}
    (hζ : k (ϖ.seq 0) = ζ * ϖ.seq 0) : IsTiltOf ζ e (ϖ.kummer k) := by
  have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk
  intro n
  refine ⟨ϖ.ratio k n, ?_, ?_, ϖ.coeff_kummer k n⟩
  · rw [PiSys.coe_ratio, ← map_pow, div_pow, ← map_pow, ϖ.seq_pow, hζ,
      mul_div_cancel_right₀ _ (ϖ.seq_ne_zero 0)]
    rfl
  · refine Subtype.ext ?_
    rw [SubmonoidClass.coe_pow, PiSys.coe_ratio, ← map_pow, div_pow, ← map_pow,
      hfix _ (IntermediateField.subset_adjoin _ _ ⟨n, rfl⟩), div_self (pow_ne_zero _ (ϖ.seq_ne_zero n)),
      map_one]
    rfl

theorem emb_sigma_pow {O : Type} [CommRing O] [Algebra ℤ_[l] O] (t : Wq l a →ₐ[ℤ_[l]] O) (n : ℕ)
    (τ : ZMod a) (w : Wq l a) : emb t τ ((sigma l a ^ n) w) = emb t (τ - n) w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, AlgEquiv.mul_apply, ih, emb_sigma]
    congr 1
    push_cast
    ring

theorem kummer_mem_resSub (ϖ : PiSys l e) {k : GQ l} (hk : k ∈ ϖ.GKinf) {ζ : Om l}
    (hζ : k (ϖ.seq 0) = ζ * ϖ.seq 0) (he : e + 1 = l ^ a) : ϖ.kummer k ∈ resSub l a := by
  rw [mem_resSub, ← he, pow_succ, GlobalTheory.MemLoc.IsTiltOf.pow_eq_one (isTiltOf_kummer ϖ hk hζ), one_mul]

theorem galA_ev (ϖ : PiSys l e) {k : GQ l} {s : ℕ} (hk : ∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ s)
    (z : Fq l a) (hz : Fq.val l a z = ϖ.kummer k) (x : (Wq l a)⟦X⟧) :
    Per.σA k (ϖ.ev a x) = ϖ.ev a (rescale (WittVector.teichmuller l z)
      (PowerSeries.map ((sigma l a ^ s : Wq l a ≃ₐ[ℤ_[l]] Wq l a) : Wq l a →+* Wq l a) x)) := by
  refine RingHom.congr_fun (ringHom_ext_of_sep ((Per.σA k).comp (ϖ.ev a))
    ((ϖ.ev a).comp ((rescale (WittVector.teichmuller l z)).comp
      (PowerSeries.map ((sigma l a ^ s : Wq l a ≃ₐ[ℤ_[l]] Wq l a) : Wq l a →+* Wq l a)))) (fun w => ?_) ?_
    fun y hy => ϖ.sep_teich y fun n => ?_) x
  · simp only [RingHom.comp_apply, PiSys.ev_C, galA_wA hk, map_C]
    have : rescale (WittVector.teichmuller l z) (C ((sigma l a ^ s) w)) = C ((sigma l a ^ s) w) := by
      refine PowerSeries.ext fun m => ?_
      rw [coeff_rescale, coeff_C]
      split_ifs with h
      · rw [h, pow_zero, one_mul]
      · rw [mul_zero]
    rw [RingHom.coe_coe, this, PiSys.ev_C]
  · simp only [RingHom.comp_apply, PiSys.ev_X, map_X, rescale_X, map_mul, PiSys.ev_C, PiSys.gal_teich,
      PiSys.mu, wA_teich, hz, add_sub_cancel]
  · refine Dvd.dvd.trans ?_ (hy n)
    simp only [RingHom.comp_apply, PiSys.ev_X, PiSys.gal_teich, mul_pow]
    exact dvd_mul_left _ _

theorem thetaW_teich (ϖ : PiSys l e) {k : GQ l} (hk : k ∈ ϖ.GKinf) (LL : FinExt l) [HasUnr a LL]
    {ζ : ↥LL.1} (hζ : k (ϖ.seq 0) = (ζ : Om l) * ϖ.seq 0) (z : Fq l a) (hz : Fq.val l a z = ϖ.kummer k) :
    ((thetaW a LL (WittVector.teichmuller l z) : ↥(OL LL)) : ↥LL.1) = ζ := by
  refine Subtype.ext ((algebraMap (Om l) ℂ_[l]).injective ?_)
  have h1 := congrArg (fun y : OC l => (y : ℂ_[l])) (intToOC_thetaW a LL (WittVector.teichmuller l z))
  simp only [coe_intToOC, wA_teich, WittVector.fontaineTheta_teichmuller, hz] at h1
  exact h1.trans (GlobalTheory.MemLoc.IsTiltOf.untilt_eq (isTiltOf_kummer ϖ hk hζ))

theorem toAc_rescale {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a]
    (t : Wq l a →ₐ[ℤ_[l]] O) (γ : TameGal K l e a) (c : Wq l a)
    (hc : ∀ τ, algebraMap O K (emb t τ c) = γ.root τ) (x : (Wq l a)⟦X⟧) (τ : ZMod a) :
    (toAc t K (rescale c (PowerSeries.map ((sigma l a ^ γ.shift.val : Wq l a ≃ₐ[ℤ_[l]] Wq l a) :
      Wq l a →+* Wq l a) x)) τ : K⟦X⟧) = ringAct γ (fun σ => (toAc t K x σ : K⟦X⟧)) τ := by
  refine PowerSeries.ext fun n => ?_
  rw [ringAct_apply, coeff_rescale, coeff_toAc, coeff_toAc, coeff_rescale, coeff_map, map_mul, map_pow,
    map_mul, map_pow, hc]
  congr 2
  rw [RingHom.coe_coe, emb_sigma_pow, ZMod.natCast_zmod_val]

theorem algebraMap_emb_teich (ϖ : PiSys l e) {k : GQ l} (hk : k ∈ ϖ.GKinf) (LL : FinExt l) [HasUnr a LL]
    [TameDescentExponentData ↥LL.1 l e a] (γ : TameGal ↥LL.1 l e a)
    (hζ : k (ϖ.seq 0) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0) (z : Fq l a)
    (hz : Fq.val l a z = ϖ.kummer k) (τ : ZMod a) :
    algebraMap ↥(OL LL) ↥LL.1 (emb (thetaW a LL) τ (WittVector.teichmuller l z)) = γ.root τ := by
  change ((thetaW a LL ((sigma l a ^ (-τ).val) (WittVector.teichmuller l z)) : ↥(OL LL)) : ↥LL.1) = _
  rw [sigma_pow_teich, map_pow, SubmonoidClass.coe_pow, thetaW_teich ϖ hk LL hζ z hz, TameGal.root, powL_apply]
  simp

theorem covers_of_root {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
    [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (γ : TameGal K l e a) {k : GQ l}
    (hunr : ∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ γ.shift.val) (z : Fq l a) (hz : Fq.val l a z = ϖ.kummer k)
    (hroot : ∀ τ, algebraMap O K (emb t τ (WittVector.teichmuller l z)) = γ.root τ) : Covers K t ϖ k γ := by
  intro f f' hf'
  obtain ⟨x, rfl⟩ := exists_eq_sum_toAc t K (Module.Free.chooseBasis ℤ_[l] O) f
  set o := Module.Free.chooseBasis ℤ_[l] O
  have hf : f' = ∑ j, o j • toAc t K (rescale (WittVector.teichmuller l z)
      (PowerSeries.map ((sigma l a ^ γ.shift.val : Wq l a ≃ₐ[ℤ_[l]] Wq l a) : Wq l a →+* Wq l a) (x j))) := by
    funext τ
    refine Subtype.ext ?_
    rw [hf' τ]
    have h1 : (fun σ => (((∑ j, o j • toAc t K (x j)) σ : A O K) : K⟦X⟧)) =
        ∑ j, algebraMap O K (o j) • (fun σ => (toAc t K (x j) σ : K⟦X⟧)) := by
      funext σ
      simp [Finset.sum_apply, algebraMap_smul]
    rw [h1, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply]
    simp [algebraMap_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [toAc_rescale t γ _ hroot]
  subst hf
  simp only [map_sum, map_smul, PiSys.iTot_toAc, galOA_tmul, galA_ev ϖ hunr z hz]

end GlobalTheory.BKGal.CoverBridge

open GlobalTheory.BKGal.CoverBridge in

theorem GlobalTheory.BKGal.covers_of_action : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e)
    (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (γ : TameGal ↥LL.1 l e a), ∀ k ∈ ϖ.GKinf,
    (∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ γ.shift.val) →
    k (ϖ.seq 0) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0 → Covers ↥LL.1 (thetaW a LL) ϖ k γ := by
  intro l _ a e _ _ ϖ LL _ _ γ k hk hunr hζ
  have hmem := kummer_mem_resSub ϖ hk hζ (TameDescentExponentData.succ_eq (K := ↥LL.1) (l := l) (e := e) (a := a))
  exact covers_of_root (thetaW a LL) ϖ γ hunr ⟨ϖ.kummer k, hmem⟩ rfl
    (algebraMap_emb_teich ϖ hk LL γ hζ ⟨ϖ.kummer k, hmem⟩ rfl)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineFilteredDeRhamComparison
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.SeedFil
open Module Formalism.MainNotions.N

theorem crys_filtered : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsCrys (P.PD K) ρ → ∀ (a : ℤ), ∀ y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a, ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR), (∀ i, d i ∈ DdR (P.PD K) ρ ∧ d i ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) (k i) ∧ b i ∈ (P.PD K).Fil (a - k i)) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  intro l _ P AI TT K V _ _ _ ρ hC a y hy
  let LL : FinExt l := ⟨⊥, inferInstance⟩
  let e : ↥LL.1 ≃ₐ[ℚ_[l]] ℚ_[l] := IntermediateField.botEquiv ℚ_[l] (Om l)
  letI iM : Module ↥LL.1 V := Module.compHom V (e : ↥LL.1 →+* ℚ_[l])
  haveI : IsScalarTower ℚ_[l] ↥LL.1 V := ⟨fun c x v => by
    show e (c • x) • v = c • (e x • v)
    have h1 := e.toLinearEquiv.map_smul c x
    simp only [AlgEquiv.toLinearEquiv_apply] at h1
    rw [h1, smul_eq_mul, mul_smul]⟩
  haveI : FiniteDimensional ↥LL.1 V := Module.Finite.of_restrictScalars_finite ℚ_[l] _ V
  let ρ' : Representation ↥LL.1 ↥(GK K) V :=
    { toFun := fun g =>
        { toFun := ρ g
          map_add' := fun u w => (ρ g).map_add u w
          map_smul' := fun c v => (ρ g).map_smul (e c) v }
      map_one' := by ext v; simp
      map_mul' := fun g h => by ext v; simp; rfl }
  have hV : finrank ↥LL.1 V = finrank ℚ_[l] V := by
    rw [← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 V, IntermediateField.finrank_bot, one_mul]
  have hB : ∀ g x, actVB (P.PD K) ρ' g x = actVB (P.PD K) ρ g x := fun g x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp [actVB]; rfl
    | add u w hu hw => simp only [map_add, hu, hw]
  have hR : ∀ g x, actVdR (P.PD K) ρ' g x = actVdR (P.PD K) ρ g x := fun g x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp [actVdR]; rfl
    | add u w hu hw => simp only [map_add, hu, hw]
  have hD : ∀ x, x ∈ DdR (P.PD K) ρ' ↔ x ∈ DdR (P.PD K) ρ := fun x => by
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hR]
  have hDc : (Dcris (P.PD K) ρ').restrictScalars ℚ_[l] = Dcris (P.PD K) ρ := by
    ext x
    simp only [Submodule.restrictScalars_mem, Dcris, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.id_apply, hB]
  have hCr : finrank ↥LL.1 ↥(Dcris (P.PD K) ρ') = finrank ℚ_[l] ↥(Dcris (P.PD K) ρ) := by
    rw [← hDc, LinearEquiv.finrank_eq
      ((Submodule.restrictScalarsEquiv ℚ_[l] ↥LL.1 _ (Dcris (P.PD K) ρ')).restrictScalars ℚ_[l]),
      ← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 ↥(Dcris (P.PD K) ρ'), IntermediateField.finrank_bot, one_mul]
  have hC' : IsCrys (P.PD K) ρ' := by
    unfold IsCrys at hC ⊢
    rw [hCr, hV]; exact hC
  have hDR := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI TT K LL V ρ' hC').1
  obtain ⟨m, k, b, d, h, hy'⟩ := GlobalTheory.DRFil.deRham_filtered l P AI TT K LL V ρ' hDR a y hy
  exact ⟨m, k, b, d, fun i => ⟨(hD _).1 (h i).1, (h i).2.1, (h i).2.2⟩, hy'⟩

end GlobalTheory.SeedFil
end

