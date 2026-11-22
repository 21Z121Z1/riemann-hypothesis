import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPfD
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0012
import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DFrameAtPfA
section
noncomputable section

open Matrix Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.DFrameAtPf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.PtRepPf

theorem exists_unitary_of_gram {k : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (α β : M →ₗ[ℂ] (Fin k → ℂ)) (h : ∀ p q, star (α p) ⬝ᵥ α q = star (β p) ⬝ᵥ β q) :
    ∃ ψ ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ p, ψ *ᵥ α p = β p := by
  let T : (Fin k → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin k) := (WithLp.linearEquiv 2 ℂ (Fin k → ℂ)).symm
  have hT : ∀ u v, inner ℂ (T u) (T v) = star u ⬝ᵥ v := by
    intro u v
    rw [dotProduct_comm]
    rfl
  let a : M →ₗ[ℂ] EuclideanSpace ℂ (Fin k) := T.toLinearMap ∘ₗ α
  let b : M →ₗ[ℂ] EuclideanSpace ℂ (Fin k) := T.toLinearMap ∘ₗ β
  have hab : ∀ p q, inner ℂ (a p) (a q) = inner ℂ (b p) (b q) := by
    intro p q
    simp only [a, b, LinearMap.comp_apply, LinearEquiv.coe_coe, hT, h]
  have hker : LinearMap.ker a ≤ LinearMap.ker b := by
    intro p hp
    rw [LinearMap.mem_ker] at hp ⊢
    have h2 := hab p p
    rw [hp, inner_zero_left, eq_comm, inner_self_eq_zero] at h2
    exact h2
  let g : LinearMap.range a →ₗ[ℂ] EuclideanSpace ℂ (Fin k) :=
    (LinearMap.ker a).liftQ b hker ∘ₗ (LinearMap.quotKerEquivRange a).symm.toLinearMap
  have hg : ∀ p, g ⟨a p, LinearMap.mem_range_self a p⟩ = b p := by
    intro p
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hgi : ∀ s t : LinearMap.range a, inner ℂ (g s) (g t) = inner ℂ s t := by
    rintro ⟨_, p, rfl⟩ ⟨_, q, rfl⟩
    rw [hg, hg, Submodule.coe_inner]
    exact (hab p q).symm
  let F := (g.isometryOfInner hgi).extend
  have hF : ∀ p, F (a p) = b p := by
    intro p
    have := LinearIsometry.extend_apply (g.isometryOfInner hgi) ⟨a p, LinearMap.mem_range_self a p⟩
    rw [LinearMap.coe_isometryOfInner, hg] at this
    exact this
  let ψ : Matrix (Fin k) (Fin k) ℂ :=
    LinearMap.toMatrix' (T.symm.toLinearMap ∘ₗ F.toLinearMap ∘ₗ T.toLinearMap)
  have hψ : ∀ u, ψ *ᵥ u = T.symm (F (T u)) := by
    intro u
    simp only [ψ, LinearMap.toMatrix'_mulVec, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearIsometry.coe_toLinearMap]
  have hiso : ∀ u v, star (ψ *ᵥ u) ⬝ᵥ (ψ *ᵥ v) = star u ⬝ᵥ v := by
    intro u v
    rw [← hT, ← hT, hψ, hψ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearIsometry.inner_map_map]
  refine ⟨ψ, ?_, fun p => ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    have := hiso (Pi.single i 1) (Pi.single j 1)
    simp [Matrix.mul_apply, dotProduct, Matrix.one_apply] at this ⊢
    rw [this]
    by_cases hij : i = j
    · subst hij
      simp [Pi.single_apply]
    · simp [Pi.single_apply, hij]
      exact Ne.symm hij
  · rw [hψ]
    have := hF p
    simp only [a, b, LinearMap.comp_apply, LinearEquiv.coe_coe] at this
    rw [this, LinearEquiv.symm_apply_apply]

section Lift

variable {n k : ℕ} (ε : Fin n → Bool)

def liftV (wb : Fin k → Fin n → ℂ) (U : Matrix (Fin k) (Fin k) ℂ) (y : Fin n → ℂ) : Fin n → ℂ :=
  y + ∑ a, ((U - 1) *ᵥ wCoord ε wb y) a • wb a

def liftL (wb : Fin k → Fin n → ℂ) (U : Matrix (Fin k) (Fin k) ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun := liftV ε wb U
  map_add' x y := by
    have hw : wCoord ε wb (x + y) = wCoord ε wb x + wCoord ε wb y := by
      funext i; simp [wCoord, hJ_add_right]
    simp only [liftV, hw, mulVec_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c x := by
    have hw : wCoord ε wb (c • x) = c • wCoord ε wb x := by
      funext i; simp [wCoord, hJ_smul_right]
    simp only [liftV, hw, mulVec_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add,
      Finset.smul_sum, smul_smul]

def liftM (wb : Fin k → Fin n → ℂ) (U : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix' (liftL ε wb U)

theorem liftM_mulVec (wb : Fin k → Fin n → ℂ) (U : Matrix (Fin k) (Fin k) ℂ) (y : Fin n → ℂ) :
    liftM ε wb U *ᵥ y = y + ∑ a, ((U - 1) *ᵥ wCoord ε wb y) a • wb a := by
  rw [liftM, LinearMap.toMatrix'_mulVec]; rfl

variable {ε}

theorem hJ_wb_sum {wb : Fin k → Fin n → ℂ} (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (c : Fin k) (p : Fin k → ℂ) : hJ ε (wb c) (∑ a, p a • wb a) = p c := by
  rw [hJ_sum_right]
  simp only [hJ_smul_right, hon, mul_ite, mul_one, mul_zero]
  simp

theorem wCoord_liftM {wb : Fin k → Fin n → ℂ} (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (U : Matrix (Fin k) (Fin k) ℂ) (y : Fin n → ℂ) :
    wCoord ε wb (liftM ε wb U *ᵥ y) = U *ᵥ wCoord ε wb y := by
  funext c
  show hJ ε (wb c) (liftM ε wb U *ᵥ y) = (U *ᵥ wCoord ε wb y) c
  rw [liftM_mulVec, hJ_add_right, hJ_wb_sum hon, sub_mulVec, one_mulVec, Pi.sub_apply]
  show wCoord ε wb y c + _ = _
  ring

theorem liftM_fix {wb : Fin k → Fin n → ℂ} (U : Matrix (Fin k) (Fin k) ℂ) (y : Fin n → ℂ)
    (hy : ∀ i, hJ ε (wb i) y = 0) : liftM ε wb U *ᵥ y = y := by
  have h0 : wCoord ε wb y = 0 := funext hy
  rw [liftM_mulVec, h0, mulVec_zero]
  simp

private theorem liftM_iso_lemma {wb : Fin k → Fin n → ℂ} (p : Fin k → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ a, p a • wb a) y = star p ⬝ᵥ wCoord ε wb y := by
  rw [hJ_sum_left]
  simp only [hJ_smul_left, dotProduct, wCoord, Pi.star_apply]

private theorem liftM_iso_lemma_2 {wb : Fin k → Fin n → ℂ} (p : Fin k → ℂ) (x : Fin n → ℂ) :
    hJ ε x (∑ a, p a • wb a) = star (wCoord ε wb x) ⬝ᵥ p := by
  rw [hJ_sum_right]
  simp only [hJ_smul_right, dotProduct, wCoord, Pi.star_apply, hJ_conj]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem liftM_iso_lemma_3 {wb : Fin k → Fin n → ℂ}
    (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0) (q p : Fin k → ℂ) :
    hJ ε (∑ a, q a • wb a) (∑ a, p a • wb a) = star q ⬝ᵥ p := by
  rw [liftM_iso_lemma]
  congr 1
  funext c
  exact hJ_wb_sum hon c p

theorem liftM_iso {wb : Fin k → Fin n → ℂ} (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (U : Matrix (Fin k) (Fin k) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) (x y : Fin n → ℂ) :
    hJ ε (liftM ε wb U *ᵥ x) (liftM ε wb U *ᵥ y) = hJ ε x y := by
  have hu : Uᴴ * U = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  have key : (U - 1) + (U - 1)ᴴ + (U - 1)ᴴ * (U - 1) = 0 := by
    simp only [conjTranspose_sub, conjTranspose_one, sub_mul, mul_sub, mul_one, one_mul, hu]
    abel
  rw [liftM_mulVec, liftM_mulVec, hJ_add_left, hJ_add_right, hJ_add_right, liftM_iso_lemma_3 hon,
    liftM_iso_lemma_2, liftM_iso_lemma]
  have e : ∀ a b : Fin k → ℂ, star a ⬝ᵥ ((U - 1) *ᵥ b) + (star ((U - 1) *ᵥ a) ⬝ᵥ b
      + star ((U - 1) *ᵥ a) ⬝ᵥ ((U - 1) *ᵥ b))
      = star a ⬝ᵥ (((U - 1) + (U - 1)ᴴ + (U - 1)ᴴ * (U - 1)) *ᵥ b) := by
    intro a b
    rw [star_mulVec, ← dotProduct_mulVec, ← dotProduct_mulVec, add_mulVec, add_mulVec,
      ← mulVec_mulVec, dotProduct_add, dotProduct_add]
    ring
  rw [add_assoc, e, key, zero_mulVec, dotProduct_zero, add_zero]

def liftU (wb : Fin k → Fin n → ℂ) (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (U : Matrix (Fin k) (Fin k) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) : Formalism.REAL.UJ ε :=
  ⟨(Matrix.isUnit_iff_isUnit_det _).2 (by
      have hA := inUJ_of_iso ε _ (liftM_iso hon U hU)
      unfold Formalism.REAL.inUJ at hA
      have h1 := congrArg Matrix.det hA
      rw [det_mul, det_mul] at h1
      have hJ0 : (Formalism.REAL.Jm ε).det ≠ 0 := by
        unfold Formalism.REAL.Jm
        rw [det_diagonal]
        exact Finset.prod_ne_zero_iff.2 fun a _ => by split_ifs <;> norm_num
      refine isUnit_iff_ne_zero.2 fun h0 => hJ0 ?_
      rw [← h1, show (liftM ε wb U).det = 0 from h0, mul_zero])|>.unit, inUJ_of_iso ε _ (liftM_iso hon U hU)⟩

theorem liftU_mulVec (wb : Fin k → Fin n → ℂ) (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (U : Matrix (Fin k) (Fin k) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) (y : Fin n → ℂ) :
    uMat (liftU wb hon U hU) *ᵥ y = liftM ε wb U *ᵥ y := rfl

end Lift

end Formalism.L2.SG.Pf.Carrier.DFrameAtPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FibreCounting
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.Pf.FibreCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem dcrel_of_heq {Λ₁ Λ₂ : Submodule (𝓞 E) S.V} (h : Λ₁ = Λ₂) {T T' : E} (F : LFlag S r T)
    (P : Submodule (𝓞 E) S.V → LFlag S r T' → Prop) (x : TermDef.Carrier (P Λ₁)) (y : TermDef.Carrier (P Λ₂))
    (he : HEq (TermDef.mk Λ₁ F (P Λ₁) x) (TermDef.mk Λ₂ F (P Λ₂) y)) : TermDef.DCRel Λ₂ F x.1 y.1 := by
  subst h
  have h2 : Quot.mk _ x = Quot.mk _ y := eq_of_heq he
  have h3 := Quot.eqvGen_exact h2
  clear he h2
  induction h3 with
  | rel a b hab => exact hab
  | refl a => apply Formalism.L2.SG.TermDef.dcrel_refl
  | symm a b _ ih => exact Formalism.L2.SG.Pf.dcrel_symm (h := ih)
  | trans a b c _ _ ih1 ih2 => exact Formalism.L2.SG.Pf.dcrel_trans (h := ih1) (h' := ih2)

theorem nlam_isom {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) :
    n ∈ Formalism.HermitianLatticesTheory.isom S.hT := hn.1.1

theorem nlam_gmap {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) :
    Formalism.HermitianLatticesTheory.gmap n Λ = Λ := hn.1.2

theorem gmap_inv_of {Λ : Submodule (𝓞 E) S.V} {g : S.V ≃ₗ[E] S.V} (h : Formalism.HermitianLatticesTheory.gmap g Λ = Λ) :
    Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ = Λ := by
  have hinv : ∀ y : S.V, g⁻¹ (g y) = y := fun y => g.symm_apply_apply y
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ Formalism.HermitianLatticesTheory.gmap g Λ := by rw [h]; exact hy
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at hy'
    obtain ⟨z, hz, rfl⟩ := hy'
    rw [hinv]
    exact hz
  · intro hx
    refine ⟨g x, ?_, hinv x⟩
    rw [← h]
    exact Submodule.mem_map_of_mem hx

end Gen

section Fib

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem frame_lf {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (a : Fin (D.R.rS + 1)) :
    frame (lf D F0) a = F0.fvec a := rfl

theorem lin_isom (s : TT Y u u') : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1

theorem lin_gmap (s : TT Y u u') : Formalism.HermitianLatticesTheory.gmap s.lin s.lam' = s.lam := s.rep.2.2.2.1

theorem frame_eq (s : TT Y u u') : s.frame = Formalism.L2.SG.Saturated.mapL s.lin (lin_isom s) (lf D (X.Fu u')) := by
  unfold Formalism.L2.SG.TermOp.GTerm.frame Formalism.L2.SG.TermOp.mapLF
  rw [dif_pos (lin_isom s)]
  rfl

theorem frame_apply (s : TT Y u u') (a : Fin (D.R.rS + 1)) : frame s.frame a = s.lin ((X.Fu u').fvec a) := by
  rw [frame_eq]
  show (Formalism.L2.SG.Saturated.mapFlag s.lin (lin_isom s) (lf D (X.Fu u')).fl).fvec a =
    s.lin ((lf D (X.Fu u')).fl.fvec a)
  generalize (lf D (X.Fu u')).fl = F
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last, Formalism.L2.SG.Saturated.mapFlag]
  · simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc, Formalism.L2.SG.Saturated.mapFlag]

theorem stabF_of_fix {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {c : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hfix : ∀ a, c (F0.fvec a) = F0.fvec a) : c ∈ stabF D F0 := by
  have he : ∀ i, c (F0.e i) = F0.e i := fun i => by
    have h1 := hfix i.castSucc
    simpa only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] using h1
  refine ⟨hc, fun j => ?_, ?_⟩
  · unfold Formalism.MainNotions.S.FlagG.Xa
    rw [Submodule.map_span, Set.image_image]
    simp only [LinearEquiv.coe_coe, he]
  · have h1 := hfix (Fin.last _)
    simpa only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last] using h1

theorem fib_dec {s s' : TT Y u u'} (h : s.toTerm = s'.toTerm) :
    s.lam = s'.lam ∧ ∃ n ∈ NLam s.lam (lf D (X.Fu u)), ∃ ν ∈ NLam s.lam' (lf D (X.Fu u')),
      ∃ c : (VS D).V ≃ₗ[D.host.E] (VS D).V, c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
        Formalism.HermitianLatticesTheory.gmap c s'.lam' = s.lam' ∧ (∀ a, c ((X.Fu u').fvec a) = (X.Fu u').fvec a) ∧
        s'.lin = n * s.lin * ν * c := by

  have hmul : ∀ (f g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (VS D).V), (f * g) x = f (g x) :=
    fun _ _ _ => rfl
  have hinv : ∀ (f : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (VS D).V), f⁻¹ (f x) = x :=
    fun f x => f.symm_apply_apply x
  have hinv' : ∀ (f : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (VS D).V), f (f⁻¹ x) = x :=
    fun f x => f.apply_symm_apply x
  have gmul : ∀ (f g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (L : Submodule (𝓞 D.host.E) (VS D).V),
      Formalism.HermitianLatticesTheory.gmap (f * g) L = Formalism.HermitianLatticesTheory.gmap f (Formalism.HermitianLatticesTheory.gmap g L) := by
    intro f g L
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [← Submodule.map_comp]
    rfl
  have gone : ∀ L : Submodule (𝓞 D.host.E) (VS D).V, Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) L = L := by
    intro L
    unfold Formalism.HermitianLatticesTheory.gmap
    exact Submodule.map_id L

  have h' := h
  unfold Formalism.L2.SG.TermOp.GTerm.toTerm at h'
  injection h' with h1 h3
  have hd : TermDef.DCRel s'.lam (lf D (X.Fu u)) s.frame s'.frame :=
    dcrel_of_heq h1 (lf D (X.Fu u)) (fun Λ => TermDef.PD D Λ (lf D (X.Fu u)) u')
      ⟨s.frame, s.rep.2.2.2.2⟩ ⟨s'.frame, s'.rep.2.2.2.2⟩ h3
  obtain ⟨n, hn, m, hm, hfr, -⟩ := hd
  have hnL : n ∈ NLam s.lam (lf D (X.Fu u)) := by rw [h1]; exact hn

  have hm' : m ∈ NLam (Formalism.HermitianLatticesTheory.gmap s.lin s.lam')
      (Formalism.L2.SG.Saturated.mapL s.lin (lin_isom s) (lf D (X.Fu u'))) := by
    rw [lin_gmap, h1, ← frame_eq]
    exact hm
  have hν : s.lin⁻¹ * m * s.lin ∈ NLam s.lam' (lf D (X.Fu u')) :=
    (Formalism.L2.SG.Pf.mem_NLam_map _ _ _ _ _).1 hm'
  have hback : Formalism.HermitianLatticesTheory.gmap s.lin⁻¹ s.lam = s.lam' := by
    rw [← lin_gmap s, ← gmul, inv_mul_cancel, gone]
  generalize hνdef : s.lin⁻¹ * m * s.lin = ν at hν
  refine ⟨h1, n, hnL, ν, hν, (n * s.lin * ν)⁻¹ * s'.lin,
    ?_, ?_, ?_, (mul_inv_cancel_left _ _).symm⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (nlam_isom hn) (lin_isom s)) (nlam_isom hν))) (lin_isom s')
  · rw [gmul, lin_gmap s', ← h1, mul_inv_rev (n * s.lin) ν, mul_inv_rev n s.lin, gmul, gmul, gmap_inv_of (nlam_gmap hnL),
      hback, gmap_inv_of (nlam_gmap hν)]
  · intro a
    have e1 := hfr a
    rw [frame_apply, frame_apply] at e1
    rw [hmul, e1]
    have e2 : n (m (s.lin ((X.Fu u').fvec a))) = (n * s.lin * ν) ((X.Fu u').fvec a) := by
      rw [← hνdef]
      simp only [hmul, hinv']
    rw [e2, hinv]

theorem lam'_eq {s s' : TT Y u u'} (h : s.toTerm = s'.toTerm) : s.lam' = s'.lam' := by
  obtain ⟨-, n, -, ν, -, c, hc, hgc, hfix, -⟩ := fib_dec h
  have hstab : c ∈ stabF D (X.Fu u') := stabF_of_fix (X.Fu u') hc hfix
  have hone : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D (X.Fu u') :=
    stabF_of_fix (X.Fu u') (Subgroup.one_mem _) (fun _ => rfl)
  have hg1 : Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) s.lam' = s.lam' := by
    unfold Formalism.HermitianLatticesTheory.gmap
    exact Submodule.map_id _
  have hR := Y.rowsOK u'
  obtain ⟨Λ0, -, huniq⟩ := hR.2 s.lam' (hR.1 _ s.mem')
  have e1 := huniq s.lam' ⟨s.mem', 1, hone, hg1⟩
  have e2 := huniq s'.lam' ⟨s'.mem', c, hstab, hgc⟩
  exact e1.trans e2.symm

theorem gterm_eq {s s' : TT Y u u'} (hl : s.lam = s'.lam) (hl' : s.lam' = s'.lam')
    (h : ∃ n ∈ NLam s.lam (lf D (X.Fu u)), ∃ n' ∈ NLam s.lam' (lf D (X.Fu u')), s'.lin = n * s.lin * n') : s = s' := by
  obtain ⟨n, hn, n', hn', hq⟩ := h
  rcases s with ⟨l, hm, l', hm', c⟩
  rcases s' with ⟨k, km, k', km', c'⟩
  simp only at hl hl'
  subst hl
  subst hl'
  have hc : c = c' :=
    (Quot.out_eq c).symm.trans ((Quot.sound ⟨n, hn, n', hn', hq⟩).trans (Quot.out_eq c'))
  subst hc
  rfl

end Fib

end Formalism.L2.SG.Pf.FibreCounting
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PvalFormExists
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X} {hF : FinX Y} (W : WittDat X)
  (hI : SIso D.s (sOf hF))

theorem tc_pfst {u u' : D.what₂.Word} (p : D.s.Pair u u') : tc hI (D.s.pfst p) = (hI.eP u u' p).1.1 :=
  hI.pfst p

theorem tc_psnd {u u' : D.what₂.Word} (p : D.s.Pair u u') : tc hI (D.s.psnd p) = (hI.eP u u' p).1.2 :=
  hI.psnd p

theorem wRowOf_eq (hW : WRowIso D) {u u' : D.what₂.Word} (p : D.s.Pair u u') :
    wRowOf W hI p = Formalism.MainNotions.S.wRow D (X.Fu u) (hI.eP u u' p).1.1.lam := by
  unfold wRowOf FlagOfWord lamOf
  refine (hW (W.δ u) (W.isom u) (X.Fu u) _).trans ?_
  rw [tc_pfst]

theorem jtOf_eq {u u' : D.what₂.Word} (t : D.s.Term u u') (s : TT Y u u') (hs : s.toTerm = tc hI t) :
    ∃ g : fib Y (tc hI t), JtOf hI t = amp Y g.1 := by
  have h : ∃ s : TT Y u u', s.toTerm = tc hI t := ⟨s, hs⟩
  exact ⟨⟨h.choose, h.choose_spec⟩, by unfold JtOf; rw [dif_pos h]⟩

theorem pair_form (hW : WRowIso D) (hC : AmpCov Y) (hK : PairAmpConst Y) (hN : FibreCountEq hF)
    (u u' : D.what₂.Word) (p : D.s.Pair u u') :
    ∃ (c : ℂ) (U : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u'), ‖c‖ = 1 ∧
      D.s.pval p = (wRowOf W hI p : ℂ) * c *
        Formalism.MainNotions.S.hsInner ((JtOf hI (D.s.pfst p)).comp (cl U)) (JtOf hI (D.s.psnd p)) := by
  have h1 := tc_pfst hI p
  have h2 := tc_psnd hI p
  obtain ⟨g₁, hg₁⟩ := jtOf_eq hI (D.s.pfst p) (hI.eP u u' p).2.choose.1
    ((hI.eP u u' p).2.choose.2.trans h1.symm)
  obtain ⟨g₂, hg₂⟩ := jtOf_eq hI (D.s.psnd p) (hI.eP u u' p).2.choose_spec.choose.1
    ((hI.eP u u' p).2.choose_spec.choose.2.trans h2.symm)
  obtain ⟨c, U, hc, hv⟩ := pvR_form hF hC hK hN (hI.eP u u' p) ⟨g₁.1, g₁.2.trans h1⟩ ⟨g₂.1, g₂.2.trans h2⟩
  refine ⟨c, U, hc, ?_⟩
  rw [hI.pval p, wRowOf_eq W hI hW p, hg₁, hg₂]
  exact hv

theorem pvalForm_exists (hW : WRowIso D) (hC : AmpCov Y) (hK : PairAmpConst Y) (hN : FibreCountEq hF) :
    ∃ A : AmpDat X, PvalForm W hI A := by
  have H := fun (u u' : D.what₂.Word) (p : D.s.Pair u u') => pair_form W hI hW hC hK hN u u' p
  choose c U hc hv using H
  exact ⟨{ chi := fun {u u'} p => c u u' p
           chi_norm := fun {u u'} p => hc u u' p
           piB := fun {u u'} p => cl (U u u' p)
           piB_unit := fun {u u'} p x => (U u u' p).norm_map x },
    fun {u u'} p => hv u u' p⟩

end Formalism.L2.SG.Pf.KernelOfEmbedding
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WittFlags
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.WittFlags

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem gmap_mul (a b : V ≃ₗ[K] V) (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  rfl

theorem gmap_one (L : Submodule R V) : Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) L = L := by
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

theorem gmap_inv_gmap (a : V ≃ₗ[K] V) (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap a⁻¹ (Formalism.HermitianLatticesTheory.gmap a L) = L := by
  rw [← gmap_mul, inv_mul_cancel, gmap_one]

theorem gmap_gmap_inv (a : V ≃ₗ[K] V) (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap a⁻¹ L) = L := by
  rw [← gmap_mul, mul_inv_cancel, gmap_one]

end Gen

theorem LatIso_holds (D : D7) : Formalism.L2.SG.TermTieOf.LatIso D := by
  intro β hβ Λ
  obtain ⟨-, hloc, -, hU, hLat⟩ := Formalism.HermitianLatticesTheory.isomAct _ _ _ (VS D).hT β hβ Λ
  refine ⟨fun hΛ => ?_, hLat.2, hU.2⟩
  simp only [Formalism.HermitianLatticesTheory.genus, Set.mem_setOf_eq] at hΛ ⊢
  obtain ⟨hΛL, hΛG⟩ := hΛ
  refine ⟨hLat.2 hΛL, fun p hp => ?_⟩
  obtain ⟨g, hg, hgΛ⟩ := hΛG p hp
  refine ⟨β * g, (Formalism.HermitianLatticesTheory.isom _).mul_mem hβ hg, ?_⟩
  rw [gmap_mul, hgΛ, hloc p]

end Formalism.L2.SG.Pf.WittFlags
end
end

