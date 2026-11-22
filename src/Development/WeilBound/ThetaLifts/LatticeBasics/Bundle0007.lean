import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OrthogonalGroupLemmas
import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0006
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0005
import GroundTheory.GlobalFields.TateThesis.Bundle0006

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.EulerB
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.Euler

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def idem (v : Pl F) : AF F := ((0, singleFin v 1) : Ainf F × Af F)

theorem ev_self (v : Pl F) : evFin F v (idem v) = 1 := evalV_singleFin_self v 1

theorem ev_ne {v u : Pl F} (h : u ≠ v) : evFin F u (idem v) = 0 := evalV_singleFin_ne h 1

theorem mul_idem {v : Pl F} {a : AF F} (h : evFin F v a = 0) : a * idem v = 0 := by
  refine Prod.ext (mul_zero a.1) (af_ext fun u => ?_)
  show evFin F u (a * idem v) = evFin F u 0
  rw [map_mul, map_zero]
  by_cases e : u = v
  · rw [e, h, zero_mul]
  · rw [ev_ne e, mul_zero]

theorem at_iff {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl F} {z : M} : At (evFin F v) z ↔ idem v • z = z := by
  refine ⟨fun h => ?_, fun h u hu => by rw [← h, smul_smul, mul_idem hu, zero_smul]⟩
  have := h (1 - idem v) (by rw [map_sub, map_one, ev_self, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at this
  exact this.symm

theorem idem_sq (v : Pl F) : idem v * idem v = idem v := by
  have := mul_idem (v := v) (a := 1 - idem v) (by rw [map_sub, map_one, ev_self, sub_self])
  linear_combination -this

variable (F) in

def Oh : AddSubgroup (AF F) where
  carrier := {a | evI F a = 0 ∧ ∀ v, evFin F v a ∈ v.adicCompletionIntegers F}
  zero_mem' := ⟨map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F), fun v => by rw [map_zero]; exact zero_mem _⟩
  add_mem' := fun {a b} ha hb => ⟨(map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1).trans
    ((congrArg₂ (· + ·) ha.1 hb.1).trans (add_zero _)),
    fun v => by rw [map_add]; exact add_mem (ha.2 v) (hb.2 v)⟩
  neg_mem' := fun {a} ha => ⟨(map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1).trans
    ((congrArg Neg.neg ha.1).trans neg_zero), fun v => by rw [map_neg]; exact neg_mem (ha.2 v)⟩

theorem isCompact_Oh : IsCompact (Oh F : Set (AF F)) := by
  have h : IsCompact ((fun a : Af F => (show AF F from ((0, a) : Ainf F × Af F))) '' _) :=
    (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).1.image (continuous_const.prodMk continuous_id)
  refine (Set.ext fun a => ?_ : _ = (Oh F : Set (AF F))) ▸ h
  refine ⟨?_, fun ha => ⟨a.2, ha.2, Prod.ext
    ((map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 ha.1).symm rfl⟩⟩
  rintro ⟨b, hb, rfl⟩
  exact ⟨map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F), hb⟩

theorem idem_mem {v : Pl F} {a : AF F} (h : evFin F v a ∈ v.adicCompletionIntegers F) : idem v * a ∈ Oh F := by
  refine ⟨?_, fun u => ?_⟩
  · show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 * a.1) = 0
    rw [zero_mul, map_zero]
  · rw [map_mul]
    by_cases e : u = v
    · subst e; rwa [ev_self, one_mul]
    · rw [ev_ne e, zero_mul]; exact zero_mem _

variable (F) in

def incA : (Fin n → E) →+ (Fin n → AE F E) := AddMonoidHom.mk' (incV F) fun _ _ => funext fun _ => map_add _ _ _

variable {Y : Spc F E n}

omit [NumberField E] in
theorem gen_mem {a : AF F} (ha : a ∈ Oh F) {x : Fin n → E} (hx : x ∈ Y.L) : a • incV F x ∈ latHat Y :=
  AddSubgroup.subset_closure ⟨a, ha.1, ha.2, x, hx, rfl⟩

theorem lat_gen (hL : Y.L.IsLattice E) : ∃ (m : ℕ) (x : Fin m → Y.L), Submodule.span ℤ (Set.range x) = ⊤ ∧ ∀ z, z ∈ latHat Y ↔
    ∃ a : Fin m → AF F, (∀ i, a i ∈ Oh F) ∧ ∑ i, a i • incV F (x i).1 = z :=
  _root_.UpperTheory.Reformulated.B.OrthogonalGroupLemmas.lat_gen hL

theorem t2Space_cm_host_adeles : T2Space (AE F E) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  exact e.isEmbedding.t2Space

theorem isCompact_latHat (hL : Y.L.IsLattice E) : IsCompact (latHat Y : Set (Fin n → AE F E)) := by
  obtain ⟨m, x, -, hx⟩ := lat_gen hL
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  have h := (isCompact_univ_pi fun _ : Fin m => isCompact_Oh (F := F)).image
    (f := fun a : Fin m → AF F => ∑ i, a i • incV F (x i).1)
    (by fun_prop)
  convert h using 1
  ext z
  exact (hx z).trans (exists_congr fun a => and_congr_left' (by simp))

theorem isClosed_latHat (hL : Y.L.IsLattice E) : IsClosed (latHat Y : Set (Fin n → AE F E)) :=
  have := t2Space_cm_host_adeles (F := F) (E := E)
  (isCompact_latHat hL).isClosed

def aeInt (Y : Spc F E n) : Submodule (AF F) (Fin n → AE F E) where
  carrier := {w | ∀ᶠ v : Pl F in cofinite, ∀ a ∈ Oh F, (idem v * a) • w ∈ latHat Y}
  zero_mem' := by
    rw [Set.mem_setOf_eq]
    exact Eventually.of_forall fun _ _ _ => by rw [smul_zero]; exact zero_mem _
  add_mem' := fun h h' => by
    rw [Set.mem_setOf_eq] at *
    exact (h.and h').mono fun _ e a ha => by rw [smul_add]; exact add_mem (e.1 a ha) (e.2 a ha)
  smul_mem' := fun c w h => by
    rw [Set.mem_setOf_eq] at *
    refine (h.and c.2.2).mono fun v e a ha => ?_
    have := e.1 _ (idem_mem (v := v) (a := a * c) (by rw [map_mul]; exact mul_mem (ha.2 v) e.2))
    rwa [← mul_assoc, idem_sq, ← mul_assoc, mul_smul] at this

omit [NumberField E] in
theorem aeInt_iff {w} : w ∈ aeInt Y ↔ ∀ᶠ v : Pl F in cofinite, ∀ a ∈ Oh F, (idem v * a) • w ∈ latHat Y := Iff.rfl

theorem mem_of_lat (hL : Y.L.IsLattice E) (P : Submodule (AF F) (Fin n → AE F E)) (hP : ∀ x ∈ Y.L, incV F x ∈ P)
    (w : Fin n → AE F E) : w ∈ P := by
  have h1 : ∀ x : Fin n → E, ∀ t : E, incV F (t • x) ∈ P := fun x => by
    induction (hL.span_eq_top ▸ Submodule.mem_top : x ∈ Submodule.span E (Y.L : Set (Fin n → E))) using Submodule.span_induction with
    | mem x hx =>
      intro t
      obtain ⟨N, hN, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic t)).exists_integral_multiple
      have h2 : incV F ((N • t) • x) ∈ P := hP _ (Y.L.smul_mem (⟨N • t, hi⟩ : 𝓞 E) hx)
      have h3 := P.smul_mem (algebraMap F (AF F) (N : F)⁻¹) h2
      rwa [smul_assoc, show incV F (N • t • x) = N • incV F (t • x) from map_zsmul (incA F) _ _, ← Int.cast_smul_eq_zsmul (AF F),
        smul_smul, ← map_intCast (algebraMap F (AF F)), ← map_mul, inv_mul_cancel₀ (Int.cast_ne_zero.2 hN), map_one, one_smul] at h3
    | zero => exact fun t => by rw [smul_zero, show incV F (0 : Fin n → E) = 0 from map_zero (incA F)]; exact zero_mem _
    | add x y _ _ hx hy =>
      intro t
      rw [smul_add, show incV F (t • x + t • y) = _ from map_add (incA F) _ _]
      exact add_mem (hx t) (hy t)
    | smul s x _ hx => exact fun t => by rw [smul_smul]; exact hx _
  rw [← Finset.univ_sum_single w]
  refine sum_mem fun i _ => ?_
  induction w i using TensorProduct.induction_on with
  | zero => rw [Pi.single_zero]; exact zero_mem _
  | add x y hx hy => rw [Pi.single_add]; exact add_mem hx hy
  | tmul a y =>
    convert P.smul_mem a (h1 (Pi.single i y) 1) using 1
    ext j
    by_cases e : j = i
    · subst e; simp [incV, inclR, TensorProduct.smul_tmul']
    · simp [incV, e]

theorem mem_aeInt (hL : Y.L.IsLattice E) (w : Fin n → AE F E) : w ∈ aeInt Y :=
  mem_of_lat hL _ (fun _ hx => aeInt_iff.2 <| Eventually.of_forall fun v _ ha => gen_mem (idem_mem (ha.2 v)) hx) w

theorem gen_surj (hL : Y.L.IsLattice E) {m : ℕ} {x : Fin m → Y.L} (hx : Submodule.span ℤ (Set.range x) = ⊤) :
    Function.Surjective (Fintype.linearCombination (AF F) fun i => incV F (x i).1) := fun w => by
  refine mem_of_lat hL (LinearMap.range _) (fun y hy => ?_) w
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 (hx ▸ Submodule.mem_top : (⟨y, hy⟩ : Y.L) ∈ _)
  have e := congrArg (fun t : Y.L => incA F t.1) hc
  simp only [AddSubmonoidClass.coe_finsetSum, map_sum, SetLike.val_smul_of_tower, map_zsmul] at e
  refine ⟨fun i => c i, Eq.trans ?_ e⟩
  rw [Fintype.linearCombination_apply]
  exact Finset.sum_congr rfl fun i _ => Int.cast_smul_eq_zsmul _ _ _

theorem ae_mulVec (hL : Y.L.IsLattice E) (A : Matrix (Fin n) (Fin n) (AE F E)) :
    ∀ᶠ v in cofinite, ∀ z ∈ latHat Y, At (evFin F v) z → A *ᵥ z ∈ latHat Y := by
  obtain ⟨m, x, -, hx⟩ := lat_gen hL
  filter_upwards [eventually_all.2 fun i => aeInt_iff.1 (mem_aeInt hL (A *ᵥ incV F (x i).1))] with v hv z hz h
  obtain ⟨a, ha, rfl⟩ := (hx z).1 hz
  rw [← at_iff.1 h, Finset.smul_sum, Matrix.mulVec_sum]
  exact sum_mem fun i _ => by rw [smul_smul, Matrix.mulVec_smul]; exact hv i _ (ha i)

end GlobalTheory.ThK.Dbl.Euler

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesX
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}

variable {Y : Spc F E n} {A : Spc F E m}

def IsDblCoordX {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W)
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))) : Prop :=
  ∃ d' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d),
    (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) ∧ IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd

def SWAnisoX : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s', B.IsGood σ → 1 ≤ n → 1 ≤ d → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → min r' s' = 0 → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ d →
    ∀ dd om S l, IsDblCoordX M dd → IsDbl (σ := σ) (A := W) (Y := X) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a →
    ∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ →
    ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      EisValueAt (flat a (fun x => l (om x (boxFun Φ₁ (star Φ₂)))) (((d : ℂ) - n) / 2)) (((d : ℂ) - n) / 2)
        fun x => (if n < d then 1 else 2) * ⨍ h in D, thetaSum F (om x (S h (boxFun Φ₁ (star Φ₂)))) ∂μ

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.LeviEx
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem exists_conj {S R : Type} [CommRing S] [CommRing R] [Algebra S R] (c : R →ₐ[S] R) {n k : Type} [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k] (J : Matrix n n R) (P : Matrix n k R) (Q : Matrix k n R) (h1 : P * Q = 1) (h2 : Q * P = 1)
    (D D' : Matrix k k R) (h3 : D * D' = 1) (h4 : D' * D = 1) (h : Dᵀ * (Pᵀ * J * P.map c) * D.map c = Pᵀ * J * P.map c) :
    ∃ g : UG c J, g.1.1 * P = P * D := by
  have mm : ∀ {a b e : Type} [Fintype b] (A : Matrix a b R) (B : Matrix b e R), (A * B).map c = A.map c * B.map c :=
    fun A B => Matrix.map_mul (f := c.toRingHom)
  have u : ∀ A B : Matrix k k R, A * B = 1 → P * A * Q * (P * B * Q) = 1 := fun A B e => by
    rw [show P * A * Q * (P * B * Q) = P * (A * (Q * P) * B) * Q by simp only [Matrix.mul_assoc], h2, mul_one, e,
      Matrix.mul_one, h1]
  refine ⟨⟨⟨P * D * Q, P * D' * Q, u _ _ h3, u _ _ h4⟩, ?_⟩, by simp only [Matrix.mul_assoc, h2, Matrix.mul_one]⟩
  show (P * D * Q)ᵀ * J * (P * D * Q).map c = J
  calc _ = Qᵀ * (Dᵀ * (Pᵀ * J * P.map c) * D.map c) * Q.map c := by simp only [mm, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (P * Q)ᵀ * J * (P * Q).map c := by rw [h]; simp only [mm, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = J := by rw [h1, Matrix.map_one _ (map_zero c) (map_one c)]; simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

omit [NumberField E] in
theorem incM_mul {a b e : Type} [Fintype b] (A : Matrix a b E) (B : Matrix b e E) : incM F (A * B) = incM F A * incM F B :=
  Matrix.map_mul

omit [NumberField E] in
theorem incM_conj {a b : Type} (A : Matrix a b E) : (incM F A).map (cA σ) = incM F (A.map σ) := by
  ext i j
  simp [incM, cA, inclR]

theorem leviEx : LeviEx := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H i₀ i₁ r s hB hW hH h₁
  have inv : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  let N : Matrix (Fin d) (Fin 2) E := (Matrix.of ![H.x, H.y])ᵀ
  let P := Matrix.fromCols H.ι N
  have su : Function.Surjective P.mulVec := fun z => by
    have hz : z ∈ Submodule.span E (W.L : Set (Fin d → E)) := hW.lat.span_eq_top ▸ Submodule.mem_top
    refine (Submodule.span_le (p := LinearMap.range P.mulVecLin)).2 (fun z hz => ?_) hz
    obtain ⟨a, b, u, -, -, -, rfl⟩ := hH.split z hz
    refine ⟨Sum.elim u ![a, b], ?_⟩
    ext i
    simp [P, N, Matrix.mulVec, dotProduct]
    ring
  obtain ⟨Q, h1⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1 su
  have h2 : Q * P = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq (by simp [hH.rank]))).1 h1
  have o1 : H.ιᵀ * W.J * N.map σ = 0 := by
    ext i j
    have := hH.orth (Pi.single i 1)
    rw [Matrix.mul_assoc]
    fin_cases j
    · simpa [form, N, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply] using this.1
    · simpa [form, N, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply] using this.2
  have o2 : Nᵀ * W.J * H.ι.map σ = 0 := by
    ext j i
    have := congrArg σ (congrFun (congrFun o1 i) j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, inv, hW.skew, Matrix.zero_apply,
      map_zero, Finset.sum_mul] at this ⊢
    rw [Finset.sum_comm, ← neg_eq_zero, ← this, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  have gr : Pᵀ * W.J * P.map σ = Matrix.fromBlocks W₁.J 0 0 (Nᵀ * W.J * N.map σ) := by
    rw [← hH.gram, ← o1]
    conv_rhs => enter [3]; rw [← o2]
    simp only [P]
    rw [Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromCols_map, Matrix.fromRows_mul_fromCols]
  have one : ∀ {k : Type} [DecidableEq k], incM F (1 : Matrix k k E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have gr' : (incM F P)ᵀ * incM F W.J * (incM F P).map (cA σ) =
      Matrix.fromBlocks (incM F W₁.J) 0 0 (incM F (Nᵀ * W.J * N.map σ)) := by
    rw [incM_conj, show (incM F P)ᵀ = incM F Pᵀ from rfl, ← incM_mul, ← incM_mul, gr, incM, Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
    rfl
  obtain ⟨m, hm⟩ := exists_conj (cA σ) (incM F W.J) (incM F P) (incM F Q) (by rw [← incM_mul, h1, one])
    (by rw [← incM_mul, h2, one]) (Matrix.fromBlocks (mat h₁) 0 0 1) (Matrix.fromBlocks (h₁.1⁻¹).1 0 0 1)
    (by simp [Matrix.fromBlocks_multiply, mat]) (by simp [Matrix.fromBlocks_multiply, mat]) (by
      have e : (mat h₁)ᵀ * incM F W₁.J * (mat h₁).map (cA σ) = incM F W₁.J := h₁.2
      rw [gr', Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
      simp [Matrix.fromBlocks_multiply, e])
  rw [show incM F P = Matrix.fromCols (incM F H.ι) (incM F N) from Matrix.fromCols_map _ _ _, Matrix.mul_fromCols,
    Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_ext_iff] at hm
  simp only [Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add] at hm
  refine ⟨m, ?_, ?_, hm.1⟩
  · rw [Units.val_one, one_smul]
    exact funext fun i => congrFun (congrFun hm.2 i) 0
  · rw [inv_one, Units.val_one, map_one, one_smul]
    exact funext fun i => congrFun (congrFun hm.2 i) 1

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}

variable {Y : Spc F E n} {A : Spc F E m}

def detInv (χ : Chr F E) (h : UA σ Y.J) : ℂ := ((χ (Matrix.GeneralLinearGroup.det h.1))⁻¹ : Circle)

def pet {G : Type} [MeasurableSpace G] (μ : Measure G) (D : Set G) (f f' : G → ℂ) : ℂ := ∫ h in D, f h * star (f' h) ∂μ

def th {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J))
    (φ : UA σ W.J → ℂ) (Ψ : Fn F n d) (g : UA σ X.J) : ℂ := pet μ D φ (theta om Ψ g)

def IsRapid (φ : UA σ Y.J → ℂ) : Prop :=
  Continuous φ ∧ (∀ γ ∈ ratU σ Y.J, ∀ h, φ (γ * h) = φ h) ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖φ h‖ * (qht h : ℝ) ^ N ≤ C

def pairs {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a') :
    Set (Fn F a (a + a') × Fn F a' (a + a')) := {y | y.2 ∈ G.M'.So B.ψ B.τ₁ ∧ PolMatch B G X R Rf y.1 y.2}

def comb {a a' : ℕ} (G : Geo σ a a') (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (s t : ℂ)
    (y : Fn F a (a + a') × Fn F a' (a + a')) : UA σ G.W.J → ℂ := s • G.M.I om y.1 + t • G.M'.I om' y.2

def DblW : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∃ dd om₂ S l, IsDbl (σ := σ) (A := X) (Y := W) (κ := (Fin n × Fin d) ⊕ (Fin n × Fin d)) B.ψ dd χX om₂ S l ∧
      (∀ Φ₁ ∈ schA F _, ∀ Φ₂ ∈ schA F _, boxFun Φ₁ (star Φ₂) ∈ schA F _ ∧ ∀ g h h' x, IsEmb h h' x →
        detInv χX h' * thetaSum F (om₂ x (S g (boxFun Φ₁ (star Φ₂)))) = theta om Φ₁ g h * star (theta om Φ₂ g h') ∧
        detInv χX h' • om₂ x (boxFun Φ₁ (star Φ₂)) = boxFun (om (1, h) Φ₁) (star (om (1, h') Φ₂))) ∧
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd ∧
      ∀ ν : @Measure (Fin n × Fin d → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∃ c' : ℝ, 0 < c' ∧
        ∀ Ψ₁ ∈ schA F _, ∀ Ψ₂ ∈ schA F _, l (boxFun Ψ₁ (star Ψ₂)) = c' * ∫ u, Ψ₁ u * star (Ψ₂ u) ∂ν

def BoxSec : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n) (M : Model σ A Y) r s r' s', B.IsGood σ → 1 ≤ m → 1 ≤ n → A.IsHerm σ B r s →
    min r s = 0 → Y.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
    ∀ dd om S l, IsDblCoord (cA σ) (-1) (incM F A.J) (incM F Y.J) M.co dd → IsDbl (σ := σ) (A := A) (Y := Y) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a → ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      IsSec K χ (((m : ℂ) - n) / 2) fun x => l (om x (boxFun Φ₁ (star Φ₂)))

def SWFull : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n) (M : Model σ A Y) r s r' s', B.IsGood σ → 1 ≤ m → 1 ≤ n → A.IsHerm σ B r s →
    min r s = 0 → Y.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
    ∀ dd om S l, IsDblCoord (cA σ) (-1) (incM F A.J) (incM F Y.J) M.co dd → IsDbl (σ := σ) (A := A) (Y := Y) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a → ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      ∃ U Ê, IsEisCont (flat a (fun x => l (om x (boxFun Φ₁ (star Φ₂)))) (((m : ℂ) - n) / 2)) U Ê ∧ ((m : ℂ) - n) / 2 ∈ U ∧
        ∀ x, Ê (((m : ℂ) - n) / 2) x = (if n < m then 1 else 2) * ⨍ g in M.dom, thetaSum F (om x (S g (boxFun Φ₁ (star Φ₂)))) ∂M.μ

def HgtEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    (∃ K a, IsStab2 (σ := σ) (Y := Y) B K ∧ IsHgt K a ∧ Continuous a ∧ ∀ x, 0 < a x) ∧
    ∃ e : UA σ Y.J × UA σ Y.J →* G2 σ Y, Continuous e ∧ ∀ h h', IsEmb h h' (e (h, h'))

def Unfold0 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → min r s = 0 →
    ∀ (χ : Chr F E) (e : UA σ Y.J × UA σ Y.J →* G2 σ Y), IsHecke F E χ → (∀ h h', IsEmb h h' (e (h, h'))) →
    ∀ (f Ê : G2 σ Y → ℂ) (z : ℂ), Continuous f → Continuous Ê → (∀ x, HasSum (eisTerm f x) (Ê x)) →
      (∀ p t x, IsPar p t → f (p * x) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
        ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ z * f x) →
    ∀ (μ : Measure (UA σ Y.J)) (D : Set (UA σ Y.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ Y.J) D μ →
      Integrable (fun g => f (e (1, g))) μ → ∀ φ : UA σ Y.J → ℂ, IsRapid φ → ∀ h,
        ∫ h' in D, Ê (e (h, h')) * detInv χ h' * φ h' ∂μ = ∫ g, f (e (1, g)) * detInv χ g * φ (h * g) ∂μ

def HgtInt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ K a (e : UA σ Y.J × UA σ Y.J →* G2 σ Y), IsStab2 B K → IsHgt K a → (∀ h h', IsEmb h h' (e (h, h'))) →
    ∀ μ : Measure (UA σ Y.J), μ.IsHaarMeasure → ∃ t₀ : ℝ, ∀ t, t₀ ≤ t → Integrable (fun g => a (e (1, g)) ^ t) μ

def LocDist : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (n d : ℕ) (ξ : (Fv F v)ˣ →* ℂˣ),
    (∀ t : ℝ, 0 < t → (ξ (unifAt v) : ℂ) ≠ t) → ∀ l : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ φ ∈ SB _, ∀ h : GL (Fin d) (Fv F v), l (fun y => φ (y * h.1)) = ξ (Matrix.GeneralLinearGroup.det h) * l φ) →
    (n < d → ∀ φ ∈ SB _, l φ = 0) ∧
    (n = d → ∀ φ ∈ SB _, ∀ g : GL (Fin n) (Fv F v), l (fun y => φ (g.1 * y)) = ξ (Matrix.GeneralLinearGroup.det g) * l φ)

def GoodNe : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∀ v, X.Good v →
    Nonempty (E →ₐ[F] Fv F v) ∧ ∀ t : E →ₐ[F] Fv F v, chrW X.ν t (unifAt v) ≠ 1

def ConstOfGood : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) r s, B.IsGood σ → X.IsHerm σ B r s → 2 ≤ n → ∀ (T : Finset (Pl F)) (f : UA σ X.J → ℂ),
    Continuous f → (∀ γ ∈ ratU σ X.J, ∀ g, f (γ * g) = f g) →
    (∀ v ∉ T, SplitsFully E v → ∀ u ∈ UAt σ X (evFin F v), ∀ g, f (g * u) = f g) → ∀ g, f g = f 1

def ThConst : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a')
    (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → ∀ s t, (∀ y ∈ pairs B G X R Rf, IsRapid (comb G om om' s t y)) →
    ∀ (μ : Measure (UA σ G.W.J)) (D : Set (UA σ G.W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ G.W.J) D μ →
    ∀ y ∈ pairs B G X R Rf, (∀ Ψ ∈ schA F _, ∀ g, th om μ D (comb G om om' s t y) Ψ g = th om μ D (comb G om om' s t y) Ψ 1) ∧
      ∀ Ψ ∈ schA F _, ∀ g, th om' μ D (comb G om om' s t y) Ψ g = th om' μ D (comb G om om' s t y) Ψ 1

def PairsStable : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a')
    (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.p = 0 → G.q = 0 → (∀ y ∈ pairs B G X R Rf, ∀ y' ∈ pairs B G X R Rf, ∀ c : ℂ, y + c • y' ∈ pairs B G X R Rf) ∧
    ∀ y ∈ pairs B G X R Rf, ∀ h, (om (1, h) y.1, om' (1, h) y.2) ∈ pairs B G X R Rf

def PairsIrr : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a')
    (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.p = 0 → G.q = 0 → ∀ N : Submodule ℂ (Fn F a (a + a') × Fn F a' (a + a')), (N : Set _) ⊆ pairs B G X R Rf →
    (∀ y ∈ pairs B G X R Rf, PolMatch B G X R Rf y.1 0 → y ∈ N) → (∀ y ∈ N, ∀ h, (om (1, h) y.1, om' (1, h) y.2) ∈ N) →
    (∀ y ∈ N, PolMatch B G X R Rf y.1 0) ∨ pairs B G X R Rf ⊆ N

def HermLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a')
    (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.p = 0 → G.q = 0 →
    ∀ (μ : Measure (UA σ G.W.J)) (D : Set (UA σ G.W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ G.W.J) D μ →
    ∀ s t s' t', ∃ lam : ℂ, ∀ y ∈ pairs B G X R Rf, ∀ y' ∈ pairs B G X R Rf,
      pet μ D (comb G om om' s t y) (comb G om om' s' t' y') = lam * pet μ D (comb G om om' 0 1 y) (comb G om om' 0 1 y')

def CoefLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a')
    (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.p = 0 → G.q = 0 →
    ∀ (μ : Measure (UA σ G.W.J)) (D : Set (UA σ G.W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ G.W.J) D μ →
    ∀ s t (lam : ℂ), (∀ y ∈ pairs B G X R Rf, ∀ y' ∈ pairs B G X R Rf,
      pet μ D (comb G om om' s t y) (comb G om om' s t y') = lam * pet μ D (comb G om om' 0 1 y) (comb G om om' 0 1 y')) →
    ∀ y ∈ pairs B G X R Rf, ∀ Ψ ∈ PolData B G.M',
      pet G.M'.μ G.M'.dom (th om' μ D (comb G om om' s t y) Ψ) (th om' μ D (comb G om om' s t y) Ψ) =
        lam * pet G.M'.μ G.M'.dom (th om' μ D (comb G om om' 0 1 y) Ψ) (th om' μ D (comb G om om' 0 1 y) Ψ)

def LInt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
    (∀ s : ℂ, 1 < s.re → Λ s = charL X.ν (∅ : Set (Pl F)) s ∧ Λ s = charL X.ν⁻¹ (∅ : Set (Pl F)) s) ∧
    ∀ z : ℤ, -((a + a' : ℕ) : ℤ) ≤ 2 * z → Λ z ≠ 0

def NonZeroBot : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → G.p = 0 → G.q = 0 →
    (∃ Φ ∈ PolData B G.M, G.M.I om Φ ≠ 0) ∧ ∃ Φ' ∈ PolData B G.M', G.M'.I om' Φ' ≠ 0

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.SecLaw
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global
open GlobalTheory.Doubling (absE)

attribute [local instance 100000] measurableSpace_adeleRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}

theorem modu_eq (a : (AF F)ˣ) : ((adeleClass F).modu a : ℝ) = IdeleGroup.ideleModule F a := by
  obtain ⟨s, hs, h0⟩ := exists_compact_mem_nhds (0 : AF F)
  have := Measure.regular_of_isAddLeftInvariant (μ := adeleMeasure F) hs ⟨0, mem_interior_iff_mem_nhds.2 h0⟩
    hs.measure_lt_top.ne
  have := distribHaarChar_eq_of_measure_smul_eq_mul (μ := adeleMeasure F) (g := a)
    (r := ⟨IdeleGroup.ideleModule F a, (IdeleGroup.ideleModule F a).2.le⟩) (Measure.measure_pos_of_mem_nhds _ h0).ne'
    hs.measure_lt_top.ne ((adeleMeasure_smul a s).trans (congrArg (· * _) (ENNReal.ofReal_eq_coe_nnreal _)))
  exact congrArg NNReal.toReal this

theorem modu_norm (x : (AE F E)ˣ) :
    ((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) x) : ℝ) = absE F E x := by
  rw [modu_eq, IdeleGroup.ideleModule_eq, GlobalTheory.Doubling.absE_apply]
  simp only [GlobalTheory.Doubling.absEv_unitFin, GlobalTheory.Doubling.absEw_unitInf]
  rw [NNReal.coe_mul, NNReal.coe_prod]
  exact congrArg₂ _ rfl (coe_finprod_nnnorm
    (IdeleGroup.toFinite F (Units.map (Algebra.norm (AF F) : AE F E →* AF F) x))).symm

theorem sec_cont_law {Y : Spc F E n} {A : Spc F E m} {ψ : AddChar (AF F) ℂ} {κ : Type} [Fintype κ] {dd} {χ : Chr F E} {om S l}
    (h : IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) ψ dd χ om S l) {Φ} (hΦ : Φ ∈ schA F κ) :
    (Continuous fun x => l (om x Φ)) ∧ ∀ p t x, IsPar p t → l (om (p * x) Φ) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ (((m : ℂ) - n) / 2 + n / 2) * l (om x Φ) := by
  refine ⟨h.weil.2.1.cont l h.adm Φ hΦ, fun p t x hp => ?_⟩
  rw [map_mul, Module.End.mul_apply, h.weil.2.2 l h.adm h.kill p t hp _ (h.weil.2.1.pres x Φ hΦ), modu_norm,
    Complex.ofReal_cpow (NNReal.coe_nonneg _)]
  congr 3
  simp; ring

end GlobalTheory.ThK.Dbl

end
end

