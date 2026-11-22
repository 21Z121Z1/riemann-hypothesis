import Mathlib

-- bundled from GroundTheory.PAdicHodge.BCrisTensorKAlg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Polynomial TensorProduct

section Lifts

variable {R E : Type*} [Field R] [Field E]

theorem mem_lifts_of_dvd_map_of_splits (i : R →+* E) {P : R[X]} (hP : P.Splits) (hP0 : P ≠ 0)
    {Q : E[X]} (hQ : Q.Monic) (hdvd : Q ∣ P.map i) : Q ∈ lifts i := by
  have hPm0 : P.map i ≠ 0 := Polynomial.map_ne_zero hP0
  have hQs : Q.Splits := (hP.map i).of_dvd hPm0 hdvd
  refine hQs.mem_lift_of_roots_mem_range hQ i fun a ha => ?_
  have ha' : a ∈ (P.map i).roots := Multiset.mem_of_le (roots.le_of_dvd hPm0 hdvd) ha
  exact hP.mem_range_of_isRoot hP0 (isRoot_of_mem_roots ha')

end Lifts

section Disjoint

variable {K₀ C E : Type*} [Field K₀] [Field C] [Field E] [Algebra K₀ C] [Algebra K₀ E]
  (j : C →ₐ[K₀] E) (F : IntermediateField K₀ E) (M N : IntermediateField K₀ C)
  (L : Type*) [Field L] [Algebra K₀ L] [Algebra L C] [IsScalarTower K₀ L C]

theorem le_natDegree_minpoly_of_linearDisjoint (pb : PowerBasis K₀ L)
    (hM : ∀ y : C, j y ∈ F → y ∈ M)
    (hN : ((minpoly K₀ pb.gen).map (algebraMap K₀ N)).Splits)
    (hdisj : (M ⊓ N).LinearDisjoint L) :
    pb.dim ≤ (minpoly F (j (algebraMap L C pb.gen))).natDegree := by
  set α : C := algebraMap L C pb.gen with hα
  set x : E := j α with hx
  set n := pb.dim
  set P := minpoly K₀ pb.gen
  let f : L →ₐ[K₀] E := j.comp (IsScalarTower.toAlgHom K₀ L C)
  have hfx : f pb.gen = x := rfl
  have hxint : IsIntegral F x := by
    have h1 : IsIntegral K₀ x := hfx ▸ (pb.isIntegral_gen).map f
    exact h1.tower_top
  set m := minpoly F x
  have hm0 : m ≠ 0 := minpoly.ne_zero hxint
  have hP0 : P ≠ 0 := minpoly.ne_zero pb.isIntegral_gen

  have hPx : aeval x P = 0 := by
    rw [← hfx, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hdvdF : m ∣ P.map (algebraMap K₀ F) :=
    minpoly.dvd F x (by rw [Polynomial.aeval_map_algebraMap]; exact hPx)
  let i : N →+* E := j.toRingHom.comp (algebraMap N C)
  have hi : i.comp (algebraMap K₀ N) = algebraMap K₀ E := by
    ext a
    simp only [i, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes]
  have hFE : (algebraMap F E).comp (algebraMap K₀ F) = algebraMap K₀ E :=
    (IsScalarTower.algebraMap_eq K₀ F E).symm
  have hdvdE : m.map (algebraMap F E) ∣ (P.map (algebraMap K₀ N)).map i := by
    rw [Polynomial.map_map, hi, ← hFE, ← Polynomial.map_map]
    exact Polynomial.map_dvd _ hdvdF
  have hlift := mem_lifts_of_dvd_map_of_splits i hN (Polynomial.map_ne_zero hP0)
    ((minpoly.monic hxint).map _) hdvdE
  obtain ⟨D, hD⟩ := (Polynomial.mem_lifts _).1 hlift
  have hiinj : Function.Injective i := i.injective
  have hDdeg : D.natDegree = m.natDegree := by
    rw [← natDegree_map_eq_of_injective hiinj, hD,
      natDegree_map_eq_of_injective (algebraMap F E).injective]

  have hcoeff : ∀ k, ((D.coeff k : N) : C) ∈ M ⊓ N := by
    intro k
    refine ⟨hM _ ?_, (D.coeff k).2⟩
    have e : j ((D.coeff k : N) : C) = (D.map i).coeff k := by
      rw [coeff_map]; rfl
    rw [e, hD, coeff_map]
    exact (m.coeff k).2

  have hDα : (D.map (algebraMap N C)).eval α = 0 := by
    have h0 : j.toRingHom ((D.map (algebraMap N C)).eval α) = 0 := by
      rw [Polynomial.eval_map, Polynomial.hom_eval₂]
      change D.eval₂ i x = 0
      rw [← Polynomial.eval_map, hD, Polynomial.eval_map, ← Polynomial.aeval_def, minpoly.aeval]
    exact (map_eq_zero_iff _ j.toRingHom.injective).1 h0
  by_contra hlt
  rw [not_le] at hlt
  have hDlt : (D.map (algebraMap N C)).natDegree < n := by
    rw [natDegree_map_eq_of_injective (algebraMap N C).injective, hDdeg]
    exact hlt
  have hsum := hDα
  rw [Polynomial.eval_eq_sum_range' hDlt,
    ← Fin.sum_univ_eq_sum_range (fun k => (D.map (algebraMap N C)).coeff k * α ^ k) n] at hsum
  have li := hdisj.linearIndependent_right' pb.basis.linearIndependent
  have hzero := Fintype.linearIndependent_iff.1 li (fun k => ⟨((D.coeff k : N) : C), hcoeff k⟩) (by
    rw [← hsum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Function.comp_apply, PowerBasis.coe_basis, map_pow, Algebra.smul_def, coeff_map]
    rfl)
  have hD0 : D = 0 := by
    refine Polynomial.ext fun k => ?_
    rw [Polynomial.coeff_zero]
    by_cases hk : k < n
    · have h1 := congrArg Subtype.val (hzero ⟨k, hk⟩)
      simpa using h1
    · exact coeff_eq_zero_of_natDegree_lt (p := D) (n := k) (by rw [hDdeg]; omega)
  apply hm0
  have h2 := hD
  rw [hD0, Polynomial.map_zero] at h2
  exact (Polynomial.map_eq_zero_iff (algebraMap F E).injective).1 h2.symm

theorem injective_lift_of_linearDisjoint [FiniteDimensional K₀ L] [Algebra.IsSeparable K₀ L]
    (hM : ∀ y : C, j y ∈ F → y ∈ M)
    (hN : ∀ x : L, ((minpoly K₀ x).map (algebraMap K₀ N)).Splits)
    (hdisj : (M ⊓ N).LinearDisjoint L) :
    Function.Injective (Algebra.TensorProduct.lift (j.comp (IsScalarTower.toAlgHom K₀ L C)) F.val
      fun _ _ => Commute.all _ _) := by
  let pb := Field.powerBasisOfFiniteOfSeparable K₀ L
  set x : E := j (algebraMap L C pb.gen) with hx
  have hle := le_natDegree_minpoly_of_linearDisjoint j F M N L pb hM (hN pb.gen) hdisj
  have li : LinearIndependent F (fun k : Fin pb.dim => x ^ (k : ℕ)) :=
    (linearIndependent_pow x).comp (Fin.castLE hle) (Fin.castLE_injective hle)
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left pb.basis z
  have hc : c = 0 := by
    ext k
    have h3 := Fintype.linearIndependent_iff.1 li (fun k => c k) (by
      rw [map_finsuppSum, Finsupp.sum_fintype _ _ (by simp)] at hz
      rw [← hz]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.TensorProduct.lift_tmul, PowerBasis.coe_basis, Algebra.smul_def, mul_comm]
      simp [x, map_pow])
    simpa using h3 k
  rw [hc, Finsupp.sum_zero_index]

theorem injective_lift_of_forall_mem [FiniteDimensional K₀ L] [Algebra.IsSeparable K₀ L]
    (hM : ∀ y : C, j y ∈ F → y ∈ M)
    (hN : ∀ x : L, ((minpoly K₀ x).map (algebraMap K₀ N)).Splits)
    (hdisj : (M ⊓ N).LinearDisjoint L) {B : Type*} [CommRing B] [Algebra K₀ B] (g : B →ₐ[K₀] E)
    (hg : Function.Injective g) (hgF : ∀ b, g b ∈ F) :
    Function.Injective (Algebra.TensorProduct.lift (j.comp (IsScalarTower.toAlgHom K₀ L C)) g
      fun _ _ => Commute.all _ _) := by
  let g' : B →ₐ[K₀] F :=
    { toFun := fun b => ⟨g b, hgF b⟩
      map_one' := Subtype.ext (map_one g)
      map_mul' := fun a b => Subtype.ext (map_mul g a b)
      map_zero' := Subtype.ext (map_zero g)
      map_add' := fun a b => Subtype.ext (map_add g a b)
      commutes' := fun r => Subtype.ext (g.commutes r) }
  have hg' : Function.Injective g' := fun a b h => hg (congrArg Subtype.val h)
  have hflat : Function.Injective (g'.toLinearMap.lTensor L) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hg'
  have heq : ∀ z, Algebra.TensorProduct.lift (j.comp (IsScalarTower.toAlgHom K₀ L C)) F.val
      (fun _ _ => Commute.all _ _) (g'.toLinearMap.lTensor L z) =
      Algebra.TensorProduct.lift (j.comp (IsScalarTower.toAlgHom K₀ L C)) g
      (fun _ _ => Commute.all _ _) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [g']
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  intro z₁ z₂ h
  apply hflat
  apply injective_lift_of_linearDisjoint j F M N L hM hN hdisj
  rw [heq, heq, h]

end Disjoint

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.ExtRobbaRootPoly
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Polynomial

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]

theorem nnnorm_multiset_sum_le_of_forall {m : Multiset F} {B : NNReal} (h : ∀ x ∈ m, ‖x‖₊ ≤ B) :
    ‖m.sum‖₊ ≤ B := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.sum_cons]
    refine (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le (h a (Multiset.mem_cons_self _ _))
      (ih fun x hx => h x (Multiset.mem_cons_of_mem hx)))

theorem nnnorm_multiset_prod' (m : Multiset F) : ‖m.prod‖₊ = (m.map fun a => ‖a‖₊).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih => rw [Multiset.prod_cons, nnnorm_mul, ih, Multiset.map_cons, Multiset.prod_cons]

variable [IsAlgClosed F]

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.FWGlue
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

section Restrict

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

def restrictAut (Ω : IntermediateField F E) (τ : Ω ≃ₐ[F] Ω) (N : IntermediateField F E)
    (hN : N ≤ Ω) [Normal F N] : N ≃ₐ[F] N :=
  haveI : Normal F (IntermediateField.restrict hN) :=
    Normal.of_algEquiv (IntermediateField.restrictAlgEquiv hN)
  (IntermediateField.restrictAlgEquiv hN).trans
    ((τ.restrictNormal (IntermediateField.restrict hN)).trans
      (IntermediateField.restrictAlgEquiv hN).symm)

theorem coe_restrictAut (Ω : IntermediateField F E) (τ : Ω ≃ₐ[F] Ω) (N : IntermediateField F E)
    (hN : N ≤ Ω) [Normal F N] (y : N) :
    ((restrictAut Ω τ N hN y : N) : E) = ((τ ⟨y, hN y.2⟩ : Ω) : E) := by
  have : Normal F (IntermediateField.restrict hN) :=
    Normal.of_algEquiv (IntermediateField.restrictAlgEquiv hN)
  set e := IntermediateField.restrictAlgEquiv hN
  have he : ∀ w : N, ((e w : IntermediateField.restrict hN) : Ω) = ⟨w, hN w.2⟩ := fun w => rfl
  set z := τ.restrictNormal (IntermediateField.restrict hN) (e y)
  have h1 : ((z : IntermediateField.restrict hN) : Ω) = τ ⟨y, hN y.2⟩ := by
    have := AlgEquiv.restrictNormal_commutes τ (IntermediateField.restrict hN) (e y)
    rw [← he y]
    exact this
  change ((e.symm z : N) : E) = _
  have h2 : ((e (e.symm z) : IntermediateField.restrict hN) : Ω) = ⟨(e.symm z : E), hN (e.symm z).2⟩ :=
    he _
  rw [AlgEquiv.apply_symm_apply, h1] at h2
  exact (congrArg Subtype.val h2).symm

theorem restrictAut_mul (Ω : IntermediateField F E) (τ₁ τ₂ : Ω ≃ₐ[F] Ω) (N : IntermediateField F E)
    (hN : N ≤ Ω) [Normal F N] :
    restrictAut Ω (τ₁ * τ₂) N hN = restrictAut Ω τ₁ N hN * restrictAut Ω τ₂ N hN := by
  ext y
  rw [AlgEquiv.mul_apply, coe_restrictAut, coe_restrictAut]
  have : (⟨((restrictAut Ω τ₂ N hN y : N) : E), hN (restrictAut Ω τ₂ N hN y).2⟩ : Ω) =
      τ₂ ⟨y, hN y.2⟩ := Subtype.ext (coe_restrictAut Ω τ₂ N hN y)
  rw [this]
  rfl

end Restrict

section Glue

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {ι : Type*}
variable (Ω : IntermediateField F E) (N : ι → IntermediateField F E) (hN : ∀ i, N i ≤ Ω)
  (hdir : Directed (· ≤ ·) N) (hcov : ∀ x ∈ Ω, ∃ i, x ∈ N i) (f : ∀ i, N i →ₐ[F] N i)
  (hf : ∀ i j (h : N i ≤ N j) (x : N i), ((f j ⟨x, h x.2⟩ : N j) : E) = ((f i x : N i) : E))

def glueFun (x : Ω) : E :=
  ((f (hcov x x.2).choose ⟨x, (hcov x x.2).choose_spec⟩ : N (hcov x x.2).choose) : E)

include hdir hf in
theorem glueFun_eq (i : ι) (x : Ω) (hx : (x : E) ∈ N i) :
    glueFun Ω N hcov f x = ((f i ⟨x, hx⟩ : N i) : E) := by
  obtain ⟨j, hj1, hj2⟩ := hdir (hcov x x.2).choose i
  unfold glueFun
  rw [← hf _ j hj1, ← hf i j hj2]

include hN in
theorem glueFun_mem (x : Ω) : glueFun Ω N hcov f x ∈ Ω :=
  hN _ (f _ _).2

def glueHom : Ω →ₐ[F] Ω where
  toFun x := ⟨glueFun Ω N hcov f x, glueFun_mem Ω N hN hcov f x⟩
  map_one' := by
    obtain ⟨i, hi⟩ := hcov 1 (one_mem Ω)
    apply Subtype.ext
    change glueFun Ω N hcov f 1 = ((1 : Ω) : E)
    rw [glueFun_eq Ω N hdir hcov f hf i 1 hi]
    have : (⟨((1 : Ω) : E), hi⟩ : N i) = 1 := rfl
    rw [this, map_one]; rfl
  map_mul' x y := by
    obtain ⟨i, hi⟩ := hcov x x.2
    obtain ⟨j, hj⟩ := hcov y y.2
    obtain ⟨k, hik, hjk⟩ := hdir i j
    apply Subtype.ext
    change glueFun Ω N hcov f (x * y) = glueFun Ω N hcov f x * glueFun Ω N hcov f y
    rw [glueFun_eq Ω N hdir hcov f hf k x (hik hi), glueFun_eq Ω N hdir hcov f hf k y (hjk hj),
      glueFun_eq Ω N hdir hcov f hf k (x * y) (mul_mem (hik hi) (hjk hj))]
    have : (⟨((x * y : Ω) : E), mul_mem (hik hi) (hjk hj)⟩ : N k) =
        ⟨(x : E), hik hi⟩ * ⟨(y : E), hjk hj⟩ := rfl
    rw [this, map_mul]; rfl
  map_zero' := by
    obtain ⟨i, hi⟩ := hcov 0 (zero_mem Ω)
    apply Subtype.ext
    change glueFun Ω N hcov f 0 = ((0 : Ω) : E)
    rw [glueFun_eq Ω N hdir hcov f hf i 0 hi]
    have : (⟨((0 : Ω) : E), hi⟩ : N i) = 0 := rfl
    rw [this, map_zero]; rfl
  map_add' x y := by
    obtain ⟨i, hi⟩ := hcov x x.2
    obtain ⟨j, hj⟩ := hcov y y.2
    obtain ⟨k, hik, hjk⟩ := hdir i j
    apply Subtype.ext
    change glueFun Ω N hcov f (x + y) = glueFun Ω N hcov f x + glueFun Ω N hcov f y
    rw [glueFun_eq Ω N hdir hcov f hf k x (hik hi), glueFun_eq Ω N hdir hcov f hf k y (hjk hj),
      glueFun_eq Ω N hdir hcov f hf k (x + y) (add_mem (hik hi) (hjk hj))]
    have : (⟨((x + y : Ω) : E), add_mem (hik hi) (hjk hj)⟩ : N k) =
        ⟨(x : E), hik hi⟩ + ⟨(y : E), hjk hj⟩ := rfl
    rw [this, map_add]; rfl
  commutes' c := by
    obtain ⟨i, hi⟩ := hcov _ (algebraMap_mem Ω c)
    apply Subtype.ext
    change glueFun Ω N hcov f (algebraMap F Ω c) = ((algebraMap F Ω c : Ω) : E)
    rw [glueFun_eq Ω N hdir hcov f hf i _ hi]
    have : (⟨((algebraMap F Ω c : Ω) : E), hi⟩ : N i) = algebraMap F (N i) c := rfl
    rw [this, AlgHom.commutes]; rfl

theorem coe_glueHom (i : ι) (x : Ω) (hx : (x : E) ∈ N i) :
    ((glueHom Ω N hN hdir hcov f hf x : Ω) : E) = ((f i ⟨x, hx⟩ : N i) : E) :=
  glueFun_eq Ω N hdir hcov f hf i x hx

def glueAut [Algebra.IsAlgebraic F Ω] : Ω ≃ₐ[F] Ω :=
  (Algebra.IsAlgebraic.algEquivEquivAlgHom F Ω).symm (glueHom Ω N hN hdir hcov f hf)

theorem coe_glueAut [Algebra.IsAlgebraic F Ω] (i : ι) (x : Ω) (hx : (x : E) ∈ N i) :
    ((glueAut Ω N hN hdir hcov f hf x : Ω) : E) = ((f i ⟨x, hx⟩ : N i) : E) :=
  coe_glueHom Ω N hN hdir hcov f hf i x hx

end Glue

section AutCongr

variable {F A B : Type*} [Field F] [Field A] [Field B] [Algebra F A] [Algebra F B]

theorem continuous_autCongr (e : A ≃ₐ[F] B) : Continuous (e.autCongr : Gal(A/F) → Gal(B/F)) := by
  apply continuous_of_continuousAt_one e.autCongr (continuousAt_def.mpr _)
  intro U hU
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨E, hE, hsub⟩ := hU
  rw [krullTopology_mem_nhds_one_iff]
  refine ⟨E.map e.symm.toAlgHom, ?_, ?_⟩
  · exact LinearEquiv.finiteDimensional (IntermediateField.equivMap E e.symm.toAlgHom).toLinearEquiv
  · intro σ hσ
    apply hsub
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro x hx
    change e (σ (e.symm x)) = x
    rw [hσ (e.symm x) ⟨x, hx, rfl⟩, AlgEquiv.apply_symm_apply]

def autCongrHomeomorph (e : A ≃ₐ[F] B) : Gal(A/F) ≃ₜ* Gal(B/F) where
  toMulEquiv := e.autCongr
  continuous_toFun := continuous_autCongr e
  continuous_invFun := continuous_autCongr e.symm

end AutCongr

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.LogPowSeries
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open PowerSeries

theorem X_dvd_one_add_X_pow_sub_one {R : Type*} [CommRing R] (q : ℕ) :
    (Polynomial.X : Polynomial R) ∣ (1 + Polynomial.X) ^ q - 1 := by
  have h := sub_dvd_pow_sub_pow (1 + Polynomial.X : Polynomial R) 1 q
  rwa [one_pow, add_sub_cancel_left] at h

theorem coeff_one_add_X_pow_sub_one_pow_of_lt {R : Type*} [CommRing R] (q : ℕ) {m n : ℕ}
    (h : m < n) : (((1 + Polynomial.X : Polynomial R) ^ q - 1) ^ n).coeff m = 0 := by
  obtain ⟨g, hg⟩ := pow_dvd_pow_of_dvd (X_dvd_one_add_X_pow_sub_one (R := R) q) n
  rw [hg, Polynomial.coeff_X_pow_mul', if_neg (not_le.2 h)]

theorem one_add_X_mul_mk_neg_one_pow :
    (1 + X : ℚ⟦X⟧) * mk (fun n => algebraMap ℚ ℚ ((-1 : ℚ) ^ n)) = 1 := by
  ext n
  rw [add_mul, one_mul, map_add]
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_mk, coeff_mk, coeff_one, if_neg n.succ_ne_zero]
    simp [pow_succ]

theorem hasSubst_one_add_X_pow_sub_one (q : ℕ) : HasSubst ((1 + X : ℚ⟦X⟧) ^ q - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp)

theorem PowerSeries.log_subst_one_add_X_pow_sub_one (q : ℕ) :
    (log ℚ).subst ((1 + X : ℚ⟦X⟧) ^ q - 1) = (q : ℚ⟦X⟧) * log ℚ := by
  set U : ℚ⟦X⟧ := (1 + X) ^ q - 1 with hU
  have hs : HasSubst U := hasSubst_one_add_X_pow_sub_one q
  set G : ℚ⟦X⟧ := mk fun n => algebraMap ℚ ℚ ((-1 : ℚ) ^ n)
  have hG : (1 + U) * G.subst U = 1 := by
    have h := congrArg (substAlgHom (R := ℚ) hs) one_add_X_mul_mk_neg_one_pow
    rw [map_mul, map_add, map_one] at h
    simp only [coe_substAlgHom] at h
    rwa [subst_X hs] at h
  have h1U : 1 + U = (1 + X) ^ q := by rw [hU]; ring
  apply derivative.ext
  · have hd : d⁄dX ℚ ((log ℚ).subst U) = d⁄dX ℚ ((q : ℚ⟦X⟧) * log ℚ) := by
      have hunit : IsUnit (1 + X : ℚ⟦X⟧) := by
        rw [isUnit_iff_constantCoeff]; simp
      apply hunit.mul_left_cancel
      rw [derivative_subst hs, deriv_log, Derivation.leibniz, deriv_log]
      rcases q with _ | q
      · simp [hU]
      · have hdU : d⁄dX ℚ U = ((q + 1 : ℕ) : ℚ⟦X⟧) * (1 + X) ^ q := by
          rw [hU, map_sub, derivative_pow, Derivation.map_one_eq_zero, sub_zero, map_add,
            Derivation.map_one_eq_zero, derivative_X, zero_add, mul_one, Nat.add_sub_cancel]
        rw [hdU]
        have hc : d⁄dX ℚ ((q + 1 : ℕ) : ℚ⟦X⟧) = 0 := by
          rw [← map_natCast (C (R := ℚ)), derivative_C]
        rw [hc, smul_zero, add_zero, smul_eq_mul]
        calc (1 + X) * (G.subst U * (((q + 1 : ℕ) : ℚ⟦X⟧) * (1 + X) ^ q))
            = ((q + 1 : ℕ) : ℚ⟦X⟧) * ((1 + X) ^ (q + 1) * G.subst U) := by ring
          _ = ((q + 1 : ℕ) : ℚ⟦X⟧) := by rw [← h1U, hG, mul_one]
          _ = (1 + X) * (((q + 1 : ℕ) : ℚ⟦X⟧) * G) := by
            rw [mul_left_comm, one_add_X_mul_mk_neg_one_pow, mul_one]
    exact hd
  · have h0 : constantCoeff U = 0 := by simp [hU]
    have h1 : constantCoeff ((log ℚ).subst U) = 0 :=
      constantCoeff_subst_eq_zero h0 _ constantCoeff_log
    rw [h1]
    simp

theorem one_add_X_pow_sub_one_eq_coe (q : ℕ) :
    ((1 + X : ℚ⟦X⟧) ^ q - 1) =
      (((1 + Polynomial.X : Polynomial ℚ) ^ q - 1 : Polynomial ℚ) : ℚ⟦X⟧) := by
  simp

theorem sum_coeff_one_add_X_pow_sub_one_pow (q : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    ∑ n ∈ Finset.Icc 1 m, (-1 : ℚ) ^ (n - 1) / n *
      (((1 + Polynomial.X : Polynomial ℚ) ^ q - 1) ^ n).coeff m = (-1) ^ (m - 1) * q / m := by
  have h := congrArg (coeff m) (PowerSeries.log_subst_one_add_X_pow_sub_one q)
  rw [coeff_subst' (hasSubst_one_add_X_pow_sub_one q), one_add_X_pow_sub_one_eq_coe] at h
  simp only [← Polynomial.coe_pow, Polynomial.coeff_coe, smul_eq_mul] at h
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc 1 m) ?_] at h
  · have hr : coeff m ((q : ℚ⟦X⟧) * log ℚ) = q * ((-1) ^ (m - 1) / m) := by
      rw [show (q : ℚ⟦X⟧) = C (q : ℚ) from (map_natCast C q).symm, coeff_C_mul, coeff_log,
        if_neg (by omega), Algebra.algebraMap_self, RingHom.id_apply]
      congr 2
      rw [show m + 1 = (m - 1) + 2 by omega, pow_add]; simp
    rw [hr] at h
    rw [show (-1 : ℚ) ^ (m - 1) * q / m = q * ((-1) ^ (m - 1) / m) by ring, ← h]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : n ≠ 0 := by have := (Finset.mem_Icc.1 hn).1; omega
    rw [coeff_log, if_neg hn1, Algebra.algebraMap_self, RingHom.id_apply,
      show n + 1 = (n - 1) + 2 by omega, pow_add]
    simp
  · intro n hn
    rw [Function.mem_support] at hn
    rw [Finset.coe_Icc, Set.mem_Icc]
    by_contra hc
    rcases Nat.lt_or_ge n 1 with h1 | h1
    · obtain rfl : n = 0 := by omega
      simp at hn
    · have hlt : m < n := by omega
      rw [coeff_one_add_X_pow_sub_one_pow_of_lt q hlt, mul_zero] at hn
      exact hn rfl

theorem log_pow_coeff_int (q m : ℕ) (hm : 1 ≤ m) :
    ∑ n ∈ Finset.Icc 1 m, (-1 : ℤ) ^ (n - 1) *
      ((((1 : Polynomial ℤ) + Polynomial.X) ^ q - 1) ^ n).coeff m * ((m.factorial / n : ℕ) : ℤ) =
      (-1) ^ (m - 1) * q * (m - 1).factorial := by
  apply Int.cast_injective (α := ℚ)
  have hcoe : ∀ n : ℕ, (((((1 : Polynomial ℤ) + Polynomial.X) ^ q - 1) ^ n).coeff m : ℚ) =
      (((1 + Polynomial.X : Polynomial ℚ) ^ q - 1) ^ n).coeff m := fun n => by
    rw [← eq_intCast (Int.castRingHom ℚ), ← Polynomial.coeff_map]
    simp [Polynomial.map_pow]
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast, hcoe]
  have hdiv : ∀ n ∈ Finset.Icc 1 m, (((m.factorial / n : ℕ) : ℚ)) = m.factorial / n := fun n hn => by
    have h1 := (Finset.mem_Icc.1 hn)
    rw [Nat.cast_div (Nat.dvd_factorial (by omega) h1.2) (by exact_mod_cast (show n ≠ 0 by omega))]
  rw [Finset.sum_congr rfl fun n hn => by rw [hdiv n hn]]
  have hfac : (m.factorial : ℚ) = m * (m - 1).factorial := by
    rw [← Nat.cast_mul, ← Nat.mul_factorial_pred (by omega)]
  calc ∑ n ∈ Finset.Icc 1 m, (-1 : ℚ) ^ (n - 1) *
        ((((1 + Polynomial.X : Polynomial ℚ) ^ q - 1) ^ n).coeff m) * (m.factorial / n)
      = m.factorial * ∑ n ∈ Finset.Icc 1 m, (-1 : ℚ) ^ (n - 1) / n *
        (((1 + Polynomial.X : Polynomial ℚ) ^ q - 1) ^ n).coeff m := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => by ring
    _ = (-1) ^ (m - 1) * q * (m - 1).factorial := by
        rw [sum_coeff_one_add_X_pow_sub_one_pow q hm, hfac]
        field_simp

end GroundTheory.PAdicHodge
end
end

