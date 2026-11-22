import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0005
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.DatumLemmas
section
noncomputable section

open Matrix

namespace Formalism.IndefR.Datum

end Formalism.IndefR.Datum

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

namespace Formalism.IndefR.Datum.Brg

section Gen
variable {R : Type*} [CommRing R] (c : R →+* R) {n m : ℕ}

theorem hO_tr (I : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R) (x y : Matrix (Fin m) (Fin n) R) :
    ∑ a, ∑ b, ∑ c', ∑ d, I a b * c (y c' b) * K c' d * x d a = (I * (y.map c)ᵀ * K * x).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc ∑ b, ∑ c', ∑ d, I a b * c (y c' b) * K c' d * x d a
      = ∑ b, ∑ d, ∑ c', I a b * c (y c' b) * K c' d * x d a :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ c', I a b * c (y c' b) * K c' d * x d a := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem small_gen (G I : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R) (hIG : I * G = 1)
    (hI : (I.map c)ᵀ = I) (x y : Matrix (Fin m) (Fin n) R) :
    ∑ i, ∑ j, ∑ k, ∑ l, c ((y * I)ᵀ i j) * G k i * K j l * (x * I)ᵀ k l =
      ∑ a, ∑ b, ∑ c', ∑ d, I a b * c (y c' b) * K c' d * x d a := by
  rw [sum_eq_trace, hO_tr, ← Matrix.trace_transpose]
  have e : ((y * I)ᵀ).map c = I * (y.map c)ᵀ := by
    rw [Matrix.transpose_map, Matrix.map_mul, Matrix.transpose_mul, hI]
  rw [e]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc _ = (K * (x * ((I * G) * I * (y.map c)ᵀ))).trace := by simp only [Matrix.mul_assoc]
    _ = ((K * x) * (I * (y.map c)ᵀ)).trace := by rw [hIG, Matrix.one_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]

theorem inv_gen (G I g g' : Matrix (Fin n) (Fin n) R) (hIG : I * G = 1) (hGI : G * I = 1) (hg : g * g' = 1)
    (h : (g.map c)ᵀ * G * g = G) : g' * I = I * (g.map c)ᵀ := by
  calc g' * I = (I * G) * g' * I := by rw [hIG, Matrix.one_mul]
    _ = I * ((g.map c)ᵀ * G * g) * g' * I := by rw [h]
    _ = I * (g.map c)ᵀ * (G * (g * g') * I) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg, Matrix.mul_one, hGI, Matrix.mul_one]

theorem small_act (I g g' : Matrix (Fin n) (Fin n) R) (k : Matrix (Fin m) (Fin m) R) (h : g' * I = I * (g.map c)ᵀ)
    (x : Matrix (Fin m) (Fin n) R) : (k * x * g' * I)ᵀ = g.map c * (x * I)ᵀ * kᵀ := by
  rw [Matrix.mul_assoc (k * x), h]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem large_gen (hc : ∀ a, c (c a) = a) (G I : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R)
    (hGI : G * I = 1) (hI : (I.map c)ᵀ = I) (hK : (K.map c)ᵀ = K) (x y : Matrix (Fin m) (Fin n) R) :
    ∑ i, ∑ j, ∑ k, ∑ l, c ((I * (y.map c)ᵀ)ᵀ i j) * K k i * G j l * (I * (x.map c)ᵀ)ᵀ k l =
      c (∑ a, ∑ b, ∑ c', ∑ d, I a b * c (y c' b) * K c' d * x d a) := by
  have e0 : (y.map c).map c = y := by ext i j; simp [hc]
  have t : ∀ M : Matrix (Fin n) (Fin n) R, c M.trace = ((M.map c)ᵀ).trace := by
    intro M; simp [Matrix.trace, map_sum]
  have e : ((I * (y.map c)ᵀ)ᵀ).map c = y * I := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, e0, Matrix.transpose_map, hI]
  have e2 : ((I * (y.map c)ᵀ * K * x).map c)ᵀ = (x.map c)ᵀ * K * y * I := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_mul, hI, hK, Matrix.transpose_map, e0, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  rw [sum_eq_trace, hO_tr, t, e2, ← Matrix.trace_transpose, e]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc _ = ((G * I) * ((x.map c)ᵀ * K * y * I)).trace := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hGI, Matrix.one_mul]

theorem large_act (I g g' : Matrix (Fin n) (Fin n) R) (k : Matrix (Fin m) (Fin m) R) (h : g * I = I * (g'.map c)ᵀ)
    (x : Matrix (Fin m) (Fin n) R) :
    (I * ((k * x * g').map c)ᵀ)ᵀ = k.map c * (I * (x.map c)ᵀ)ᵀ * gᵀ := by
  have k' : g'.map c * Iᵀ = Iᵀ * gᵀ := by
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul] using this.symm
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.mul_assoc]
  rw [k']

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev GG (S : HSp D) : Matrix (Fin S.rank) (Fin S.rank) (AE D) := S.gram.map (incA D)
abbrev GI (S : HSp D) : Matrix (Fin S.rank) (Fin S.rank) (AE D) := (S.gram⁻¹).map (incA D)

theorem cA_inc (a : D.host.E) : cA D (incA D a) = incA D (star a) := by
  simp [cA, sigR, CMData.sig, inclR]; rfl

theorem gram_herm (S : HSp D) : S.gramᴴ = S.gram :=
  Matrix.ext fun i j => S.herm.eq _ _

theorem GG_GI (S : HSp D) : GG S * GI S = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne S))]
  simp

theorem GI_GG (S : HSp D) : GI S * GG S = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne S))]
  simp

theorem GI_herm (S : HSp D) : ((GI S).map (cA D))ᵀ = GI S := by
  have h : (S.gram⁻¹)ᴴ = S.gram⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, gram_herm]
  refine Matrix.ext fun i j => ?_
  exact (cA_inc _).trans (congrArg (incA D) (congrFun (congrFun h i) j))

theorem GG_herm (S : HSp D) : ((GG S).map (cA D))ᵀ = GG S := by
  refine Matrix.ext fun i j => ?_
  exact (cA_inc _).trans (congrArg (incA D) (congrFun (congrFun (gram_herm S) i) j))

theorem mt_mul_inv (S : HSp D) (g : GA D S) : Formalism.L2.Theta.mt S g * Formalism.L2.Theta.mt S g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem inv_GI (S : HSp D) (g : GA D S) :
    Formalism.L2.Theta.mt S g⁻¹ * GI S = GI S * ((Formalism.L2.Theta.mt S g).map (cA D))ᵀ :=
  inv_gen (cA D) (GG S) (GI S) _ _ (GI_GG S) (GG_GI S) (mt_mul_inv S g) (mt_rel S g)

theorem bridgeSmall : BridgeSmall D := by
  intro S T hr
  refine ⟨fun x y => ?_, fun g h x => ?_⟩
  · have : hHom S T (toTWsmall S T y) (toTWsmall S T x) = hO S T x y := by
      unfold hHom; rw [if_pos hr]
      exact small_gen (cA D) (GG S) (GI S) (GG T) (GI_GG S) (GI_herm S) x y
    unfold symplO sympl; rw [this]
  · unfold actHom; rw [if_pos hr]
    exact small_act (cA D) (GI S) _ _ _ (inv_GI S g) x

theorem trace_cA (a : AE D) :
    Algebra.trace (AF D.host.F) (AE D) (cA D a) = Algebra.trace (AF D.host.F) (AE D) a := by
  let f : AE D →ₐ[AF D.host.F] AE D := Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig
  have hf : ∀ a, f a = cA D a := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [f, cA, sigR]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  have hff : f.comp f = AlgHom.id _ _ := AlgHom.ext fun a => by
    rw [AlgHom.comp_apply, hf, hf, cA_cA]; rfl
  let g : AE D ≃ₐ[AF D.host.F] AE D := AlgEquiv.ofAlgHom f f hff hff
  rw [← hf]
  exact Algebra.trace_eq_of_algEquiv g a

theorem bridgeLarge (hxi : star D.host.xi0 = -D.host.xi0) : BridgeLarge D := by
  intro S T hr
  refine ⟨fun x y => ?_, fun g h x => ?_⟩
  · have : hHom T S (toTWlarge S T y) (toTWlarge S T x) = cA D (hO S T x y) := by
      unfold hHom; rw [if_pos hr.le]
      exact large_gen (cA D) cA_cA (GG S) (GI S) (GG T) (GG_GI S) (GI_herm S) (GG_herm T) x y
    unfold symplO sympl
    rw [this, ← trace_cA (incA D D.host.xi0 * hO S T x y), map_mul, cA_inc, hxi, map_neg, neg_mul, map_neg]
  · unfold actHom; rw [if_pos hr.le]
    have k := inv_GI S g⁻¹
    rw [inv_inv] at k
    exact large_act (cA D) (GI S) _ _ _ k x

theorem star_purely_imaginary_eq_neg : star D.host.xi0 = -D.host.xi0 := by
  have hs : ∀ x : D.host.E, D.host.φ₀ (star x) = starRingEnd ℂ (D.host.φ₀ x) := fun x => by
    haveI := D.host.isCMField_hostE
    exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x
  have hd : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  apply D.host.φ₀.injective
  rw [hs, map_neg]
  unfold Host.xi0
  rw [map_div₀, map_neg, map_one, map_mul, map_natCast, hd]
  simp [div_neg]

theorem bridgeLarge' : BridgeLarge D := bridgeLarge star_purely_imaginary_eq_neg

end Formalism.IndefR.Datum.Brg

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartOfDefinite
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace CSDForm

variable (S : CSD K)

def csumForm : S.Forms →ₗ⋆[K] S.Forms →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun f g => S.csum (f : S.Cl → S.V) (g : S.Cl → S.V))
    (fun f f' g => by
      simp only [CSD.csum, Submodule.coe_add, Pi.add_apply, map_add, LinearMap.add_apply, mul_add,
        Finset.sum_add_distrib])
    (fun a f g => by
      simp only [CSD.csum, Submodule.coe_smul, Pi.smul_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => by ring)
    (fun f g g' => by
      simp only [CSD.csum, Submodule.coe_add, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib])
    (fun a f g => by
      simp only [CSD.csum, Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
      refine Finset.sum_congr rfl fun c _ => by ring)

theorem csumForm_apply (f g : S.Forms) : csumForm S f g = S.csum (f : S.Cl → S.V) (g : S.Cl → S.V) := rfl

end CSDForm

namespace BlockGood

variable {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0)

def goodR (ℓ : Lvl K G) : Submodule K B.S.Forms :=
  LinearMap.range ((B.S.basis.equivFun.symm : (Fin B.S.dim → K) →ₗ[K] B.S.Forms) ∘ₗ (B.vE ℓ).mulVecLin)

theorem toF_mem_goodR (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) :
    B.toF ℓ Z y ∈ goodR B ℓ := by
  unfold goodR
  exact LinearMap.mem_range.2 ⟨(B.zE ℓ Z).mulVecLin y, rfl⟩

theorem toF_mem (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) : B.toF ℓ Z y ∈ Z := by
  have hs := (subspace_image_spec K _ (B.Z0 ℓ Z)).2
  have hy : (B.zE ℓ Z).mulVec y ∈ B.Z0 ℓ Z := by
    rw [← hs]
    exact ⟨y, rfl⟩
  obtain ⟨f, hf, he⟩ := hy
  have : B.toF ℓ Z y = f := by
    have he' : B.S.basis.equivFun f = (B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y) := he
    change B.S.basis.equivFun.symm ((B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y)) = f
    rw [← he', LinearEquiv.symm_apply_apply]
  rw [this]
  exact hf

theorem csum_toF (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (x y : Fin (B.dZ ℓ Z) → K) :
    B.S.csum (B.toF ℓ Z x : B.S.Cl → B.S.V) (B.toF ℓ Z y : B.S.Cl → B.S.V) =
      (Nat.card ℓ.P : K) * (star x ⬝ᵥ (B.HZ ℓ Z).mulVec y) := by
  change B.S.csum (B.S.I ((B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec x))) (B.S.I ((B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y))) = _
  rw [B.S.csum_sum]
  have h1 : ∀ u w : Fin B.S.dim → K, (∑ i, ∑ j, star (u i) * B.S.H i j * w j) = star u ⬝ᵥ B.S.H.mulVec w := by
    intro u w
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  rw [h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hP : (Nat.card ℓ.P : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h2 : (B.vE ℓ * B.zE ℓ Z)ᴴ * (B.S.H * B.vE ℓ) * B.zE ℓ Z = (Nat.card ℓ.P : K) • B.HZ ℓ Z := by
    simp only [BlockDat.HZ, BlockDat.HV, BlockDat.vE, CSD.goodPartHermitianForm, CSD.cutH, CSD.V0E, Matrix.conjTranspose_mul,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hP, one_smul, Matrix.mul_assoc]
  rw [h2]
  simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem csum_toF_at {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s) (ℓ : Lvl K G)
    (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ) (Z : Submodule K B.S.Forms) (x y : Fin (B.dZ ℓ Z) → K) :
    v0.embedding (CSDForm.csumForm B.S (B.toF ℓ Z x) (B.toF ℓ Z y)) =
      ((Nat.card ℓ.P : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v0 x y := by
  rw [CSDForm.csumForm_apply, csum_toF, map_mul, map_natCast, Formalism.L2.DIV.majAt_eq]
  have hm : metOf (B.XQ ℓ Z v0) = (B.HZ ℓ Z).map v0.embedding := (BlockDat.XQ_herm hv0 h hX (Z := Z)).2
  rw [hm]
  push_cast
  congr 1
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, map_sum, map_mul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hv0]
  rfl

end BlockGood

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

theorem opC_adjoint (hK : X.KFormR) (cv : CrdV A) (hJ : X.JIsoR cv) (t : Bs.Tup) (i i' : A.OpR t)
    (h : ∀ f g, cv.hR t (A.opR t i f) g = cv.hR t f (A.opR t i' g)) :
    X.opC t i' = LinearMap.adjoint (X.opC t i) := by
  have h1 : X.opC t i = LinearMap.adjoint (X.opC t i') := by
    rw [LinearMap.eq_adjoint_iff_basis (Basis.mk (hK t).1 (hK t).2.ge) (Basis.mk (hK t).1 (hK t).2.ge)]
    intro k l
    simp only [Basis.mk_apply]
    rw [← jR_opR X hK, ← jR_opR X hK, hJ, hJ, h]
  rw [h1, LinearMap.adjoint_adjoint]

theorem opLC_adjoint (hK : X.KFormL) (cv : CrdV A) (hJ : X.JIsoL cv) (j : Bs.J) (t : Bs.Tup) (i i' : A.OpL j t)
    (h : ∀ f g, cv.hL j t (A.opL j t i f) g = cv.hL j t f (A.opL j t i' g)) :
    X.opLC j t i' = LinearMap.adjoint (X.opLC j t i) := by
  have h1 : X.opLC j t i = LinearMap.adjoint (X.opLC j t i') := by
    rw [LinearMap.eq_adjoint_iff_basis (Basis.mk (hK j t).1 (hK j t).2.ge) (Basis.mk (hK j t).1 (hK j t).2.ge)]
    intro k l
    simp only [Basis.mk_apply]
    rw [← jL_opL X hK, ← jL_opL X hK, hJ, hJ, h]
  rw [h1, LinearMap.adjoint_adjoint]

end CxData

section Concrete

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

def cvOf (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) : CrdV A.fam.amb where
  v0R _ b t := match b with
    | false => BlockGood.goodR (A.fam.R t) (A.fam.lvl P0 ψ0)
    | true => BlockGood.goodR (A.fam.R t) (A.fam.lvl P1 ψ1)
  v0L _ b j t := match b with
    | false => BlockGood.goodR (A.fam.L j t) (A.fam.lvlA P0 ψ0)
    | true => BlockGood.goodR (A.fam.L j t) (A.fam.lvlA P1 ψ1)
  hR t := CSDForm.csumForm (A.fam.R t).S
  hL j t := CSDForm.csumForm (A.fam.L j t).S

variable {A : FamIn K G Pl0 T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)}
  {Zsc : DefSub A.fam.amb → IndefScale A.fam.base}

theorem crdZ_of (X : CxData A.fam.amb) (b : Bool) : X.CrdZ (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro t x
  cases b
  · exact BlockGood.toF_mem _ _ _ _
  · exact BlockGood.toF_mem _ _ _ _

theorem coordinates_in_good_part_of_definite (X : CxData A.fam.amb) (b : Bool) :
    X.CoordinatesInGoodPart (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf A P0 ψ0 P1 ψ1) b := by
  intro t x
  cases b
  · exact BlockGood.toF_mem_goodR _ _ _ _
  · exact BlockGood.toF_mem_goodR _ _ _ _

theorem crdZL_of (X : CxData A.fam.amb) (b : Bool) : X.CrdZL (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro j t x
  cases b
  · exact BlockGood.toF_mem _ _ _ _
  · exact BlockGood.toF_mem _ _ _ _

theorem lift_coordinates_in_good_part_of_definite (X : CxData A.fam.amb) (b : Bool) :
    X.LiftCoordinatesInGoodPart (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf A P0 ψ0 P1 ψ1) b := by
  intro j t x
  cases b
  · exact BlockGood.toF_mem_goodR _ _ _ _
  · exact BlockGood.toF_mem_goodR _ _ _ _

def NPTie (X : CxData A.fam.amb) (P0 P1 : Subgroup G) : Prop :=
  X.nP false = (Nat.card P0 : ℝ) ∧ X.nP true = (Nat.card P1 : ℝ)

theorem isoR_of {X : CxData A.fam.amb} {s : ℕ} (hok : A.fam.Ok s) (hJ : X.JIsoR (cvOf A P0 ψ0 P1 ψ1))
    (hn : NPTie X P0 P1) (b : Bool) : X.IsoR (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro t x y
  rw [hJ t]
  cases b
  · rw [hn.1]
    exact BlockGood.csum_toF_at (A.fam.R t) hok.conj (hok.what₂ t) (A.fam.lvl P0 ψ0) hok.irr (X.zs.Z t) x y
  · rw [hn.2]
    exact BlockGood.csum_toF_at (A.fam.R t) hok.conj (hok.what₂ t) (A.fam.lvl P1 ψ1) hok.irr (X.zs.Z t) x y

theorem isoL_of {X : CxData A.fam.amb} {s : ℕ} (hok : A.fam.Ok s) (hJ : X.JIsoL (cvOf A P0 ψ0 P1 ψ1))
    (hn : NPTie X P0 P1) (b : Bool) : X.IsoL (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro j t x y
  rw [hJ j t]
  cases b
  · rw [hn.1]
    exact BlockGood.csum_toF_at (A.fam.L j t) hok.conj (hok.lifts j t) (A.fam.lvlA P0 ψ0) hok.irr (X.zs.Zl j t) x y
  · rw [hn.2]
    exact BlockGood.csum_toF_at (A.fam.L j t) hok.conj (hok.lifts j t) (A.fam.lvlA P1 ψ1) hok.irr (X.zs.Zl j t) x y

def HeckeRatAllR (A : FamIn K G Pl0 T m) : Prop := ∀ t, (A.fam.R t).OkH

def HeckeRatAllL (A : FamIn K G Pl0 T m) : Prop := ∀ j t, (A.fam.L j t).OkH

theorem csum_act_inv {B : BlockDat K G Pl0} (h : B.S.ActGood B.r) (g : G) (f f' : B.S.Forms) :
    B.S.csum (B.r g f : B.S.Cl → B.S.V) (f' : B.S.Cl → B.S.V) =
      B.S.csum (f : B.S.Cl → B.S.V) (B.r g⁻¹ f' : B.S.Cl → B.S.V) := by
  have h1 := h.unitary g f (B.r g⁻¹ f')
  have h2 : B.r g (B.r g⁻¹ f') = f' := by
    show (B.r g * B.r g⁻¹) f' = f'
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [h2] at h1
  exact h1

theorem adjClosedR_of {X : CxData A.fam.amb} {s : ℕ} (hok : A.fam.Ok s) (hH : HeckeRatAllR A) (hK : X.KFormR)
    (hJ : X.JIsoR (cvOf A P0 ψ0 P1 ψ1)) : X.AdjClosedR := by
  intro t i
  rcases i with p | g
  · obtain ⟨p', hp'⟩ := (hH t).adj p
    exact ⟨Sum.inl p', X.opC_adjoint hK (cvOf A P0 ψ0 P1 ψ1) hJ t (Sum.inl p) (Sum.inl p') fun f f' => hp' f f'⟩
  · exact ⟨Sum.inr g⁻¹, X.opC_adjoint hK (cvOf A P0 ψ0 P1 ψ1) hJ t (Sum.inr g) (Sum.inr g⁻¹)
      fun f f' => csum_act_inv (hok.what₂ t).act g f f'⟩

theorem adjClosedL_of {X : CxData A.fam.amb} {s : ℕ} (hok : A.fam.Ok s) (hH : HeckeRatAllL A) (hK : X.KFormL)
    (hJ : X.JIsoL (cvOf A P0 ψ0 P1 ψ1)) : X.AdjClosedL := by
  intro j t i
  rcases i with p | g
  · obtain ⟨p', hp'⟩ := (hH j t).adj p
    exact ⟨Sum.inl p', X.opLC_adjoint hK (cvOf A P0 ψ0 P1 ψ1) hJ j t (Sum.inl p) (Sum.inl p') fun f f' => hp' f f'⟩
  · exact ⟨Sum.inr g⁻¹, X.opLC_adjoint hK (cvOf A P0 ψ0 P1 ψ1) hJ j t (Sum.inr g) (Sum.inr g⁻¹)
      fun f f' => csum_act_inv (hok.lifts j t).act g f f'⟩

end Concrete

end Formalism.IndefR.Cx
end
end

