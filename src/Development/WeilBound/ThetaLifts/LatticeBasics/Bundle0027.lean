import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0024
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
import Development.WeilBound.ThetaLifts.LatticeBasics.ThConstInv
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0009
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.Bundle0004

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.RatEquiv
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Emb

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {β : Type} [Fintype β] [DecidableEq β]

def dgM : Matrix β β A →* Matrix (β ⊕ β) (β ⊕ β) A where
  toFun g := Matrix.fromBlocks g 0 0 g
  map_one' := Matrix.fromBlocks_one
  map_mul' g h := by simp [Matrix.fromBlocks_multiply]

def dgU (J : Matrix β β A) : UG c J →* UG c (dbl J) :=
  ((Units.map dgM).comp (UG c J).subtype).codRestrict _ fun g => by
    have hg : g.1.1ᵀ * J * g.1.1.map c = J := g.2
    show (Matrix.fromBlocks g.1.1 0 0 g.1.1)ᵀ * dbl J * (Matrix.fromBlocks g.1.1 0 0 g.1.1).map c = dbl J
    rw [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero c), Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp [hg]

theorem dgU_val (J : Matrix β β A) (g : UG c J) : (dgU c J g).1.1 = Matrix.fromBlocks g.1.1 0 0 g.1.1 := rfl

theorem dgU_cont [TopologicalSpace A] (J : Matrix β β A) : Continuous (dgU c J) :=
  continuous_induced_rng.2 ((Continuous.units_map (dgM (A := A) (β := β))
    (continuous_id.matrix_fromBlocks continuous_const continuous_const continuous_id)).comp continuous_subtype_val)

theorem actB_dgU {α : Type} (J : Matrix β β A) (g : UG c J) (w w' : Matrix α β A) :
    actB c (dgU c J g) (Matrix.fromCols w w') = Matrix.fromCols (actB c g w) (actB c g w') := by
  simp [actB, dgU_val, Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks]

theorem actB_mul {α : Type} {J : Matrix β β A} (g h : UG c J) (w : Matrix α β A) :
    actB c (g * h) w = actB c g (actB c h w) := by
  simp [actB, Matrix.mul_assoc]

end Emb

theorem det_ne_of_sig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply]
  have h2 := congrArg Matrix.det h1
  intro h0
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul, h0] at h2
  simpa [Matrix.det_neg] using h2.symm

theorem herm_det {B : Base F E} {n r s : ℕ} {X : Spc F E n} (h : X.IsHerm σ B r s) : X.J.det ≠ 0 := fun h0 => by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  exact det_ne_of_sig (h.sig w) (by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero])

theorem skew_det {B : Base F E} {n r s : ℕ} {X : Spc F E n} (h : X.IsSkew σ B r s) : X.J.det ≠ 0 := fun h0 => by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  exact det_ne_of_sig (h.sig w) (by rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero])

theorem modu_det {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) (f : (AF F)ˣ →* ℝ≥0) (g : UA σ J) :
    f (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det g.1)) = 1 := by
  have h := congrArg Matrix.det (show g.1.1ᵀ * incM F J * g.1.1.map (cA σ) = incM F J from g.2)
  have u : IsUnit (incM F J).det := by
    rw [incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hJ.isUnit.map _
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show (g.1.1.map (cA σ)).det = sigR (AF F) σ g.1.1.det from ((cA σ).toRingHom.map_det _).symm] at h
  have h1 : g.1.1.det * sigR (AF F) σ g.1.1.det = 1 := u.mul_left_cancel (by linear_combination h)
  have h2 := congrArg (Algebra.norm (AF F)) h1
  rw [map_mul, GlobalTheory.Doubling.norm_sigR, map_one] at h2
  refine (pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 ?_
  rw [sq, ← map_mul, ← map_one f]
  exact congrArg f (Units.ext h2)

section Member

variable {a b : ℕ} {JA : Matrix (Fin a) (Fin a) E} {JB : Matrix (Fin b) (Fin b) E} {κ : Type} [Fintype κ]
  {d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ}
  {dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (dbl (incM F JB))) (κ ⊕ κ)} {ψ : AddChar (AF F) ℂ}
  {χ : Chr F E} {om : UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ)}
  {omd : UG (cA σ) (dbl (incM F JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)}

theorem dbl_kill (hψ : IsStd ψ) (h : IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd) (z : Matrix (Fin a) (Fin b) (AE F E)) :
    ∀ Φ ∈ schA F (κ ⊕ κ), lD F κ (dd.rho ψ (z * (diagCols (Fin b))ᵀ) Φ) = lD F κ Φ := fun Φ hΦ => by
  rw [show z * (diagCols (Fin b))ᵀ = Matrix.fromCols z z by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.transpose_one]
      exact (Matrix.mul_fromCols z 1 1).trans (by rw [Matrix.mul_one]),
    Darboux.rho, h]
  exact lD_kill hψ hΦ _ _

theorem dbl_fix (hψ : IsStd ψ) (hJ : JB.det ≠ 0) (h : IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd)
    (hw : IsUWeilSplit (cA σ) (adeleClass F) ψ (-1) (incM F JA) (dbl (incM F JB)) dd χ (diagCols (Fin b)) omd)
    (g : UA σ JB) {Φ} (hΦ : Φ ∈ schA F (κ ⊕ κ)) :
    lD F κ (omd (dgU _ _ g) Φ) = χ (Matrix.GeneralLinearGroup.det g.1) * lD F κ Φ := by
  rw [hw.2.2 _ lD_adm (dbl_kill hψ h) _ g.1 (by simp [dgU_val, diagCols, Matrix.fromBlocks_mul_fromRows]) Φ hΦ, modu_det hJ]
  simp

theorem dbl_box (hψ : IsStd ψ) (hJ : JB.det ≠ 0) (h : IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd)
    (hw : IsUWeilSplit (cA σ) (adeleClass F) ψ (-1) (incM F JA) (dbl (incM F JB)) dd χ (diagCols (Fin b)) omd)
    (ho : IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om) (g : UA σ JB) {φ φ'} (hφ : φ ∈ schA F κ) (hφ' : φ' ∈ schA F κ) :
    omd (dgU _ _ g) (boxFun φ (star φ')) =
      (χ (Matrix.GeneralLinearGroup.det g.1) : ℂ) • boxFun (om g φ) (star (om g φ')) := by
  have m1 := hw.2.1.pres (dgU _ _ g) _ (box_mem hφ hφ')
  have m2 := box_mem (ho.pres g φ hφ) (ho.pres g φ' hφ')
  have rb : ∀ w ϕ ϕ', dd.rho ψ (Matrix.fromCols w 0) (boxFun ϕ ϕ') = boxFun (d.rho ψ w ϕ) ϕ' := fun w ϕ ϕ' => by
    funext x
    rw [Darboux.rho, h, ← Sum.elim_comp_inl_inr x]
    simp [schr, boxFun, Darboux.rho, elim_dot, mul_assoc, Function.comp_def, Pi.add_def]
  refine sub_eq_zero.1 (lD_inj hψ (sub_mem m1 (Submodule.smul_mem _ _ m2)) fun x y => ?_)
  obtain ⟨w, hw'⟩ := d.e.surjective (x, y)
  obtain ⟨w, rfl⟩ : ∃ w', w = actB (cA σ) g w' := ⟨actB (cA σ) g⁻¹ w, by rw [← actB_mul]; simp [actB]⟩
  have e : ∀ (Φ Ψ) (c : ℂ), schr ψ (Sum.elim x 0, Sum.elim y 0) (Φ - c • Ψ) =
      dd.rho ψ (Matrix.fromCols (actB (cA σ) g w) 0) Φ - c • dd.rho ψ (Matrix.fromCols (actB (cA σ) g w) 0) Ψ := fun Φ Ψ c => by
    funext z
    rw [Darboux.rho, h, hw']
    simp [schr]; ring
  have m3 : d.rho ψ w φ ∈ schA F κ := GlobalTheory.HeisSchA.schr_mem_schA ψ hψ (d.e w) φ hφ
  rw [e, map_sub, map_smul, rb, ← ho.impl g w φ hφ, lD_unit ho.unit ho.pres g m3 hφ',
    show Matrix.fromCols (actB (cA σ) g w) 0 = actB (cA σ) (dgU _ _ g) (Matrix.fromCols w 0) by rw [actB_dgU]; simp [actB],
    ← hw.2.1.impl _ _ _ (box_mem hφ hφ'), rb, dbl_fix hψ hJ h hw g (box_mem m3 hφ')]
  exact sub_self _

theorem dbl_emb (hψ : IsStd ψ) (hJ : JB.det ≠ 0) (h : IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd)
    (hw : IsUWeilSplit (cA σ) (adeleClass F) ψ (-1) (incM F JA) (dbl (incM F JB)) dd χ (diagCols (Fin b)) omd)
    (ho : IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om)
    (hr : ∀ (g : UA σ JB) (gd : UG (cA σ) (dbl (incM F JB))), gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
      ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, omd gd (boxFun φ₁ φ₂) = boxFun (om g φ₁) φ₂)
    {g g' : UA σ JB} {x : UG (cA σ) (dbl (incM F JB))} (hx : x.1.1 = Matrix.fromBlocks g.1.1 0 0 g'.1.1)
    {φ φ'} (hφ : φ ∈ schA F κ) (hφ' : φ' ∈ schA F κ) :
    (((χ (Matrix.GeneralLinearGroup.det g'.1))⁻¹ : Circle) : ℂ) • omd x (boxFun φ (star φ')) =
      boxFun (om g φ) (star (om g' φ')) := by
  have e : x = x * dgU _ _ g'⁻¹ * dgU _ _ g' := by rw [map_inv, inv_mul_cancel_right]
  rw [e, map_mul, Module.End.mul_apply, dbl_box hψ hJ h hw ho g' hφ hφ', map_smul, smul_smul, ← Circle.coe_mul, inv_mul_cancel,
    Circle.coe_one, one_smul, hr (g * g'⁻¹) _ ?_ _ (ho.pres g' φ hφ) _ (star_mem (ho.pres g' φ' hφ')),
    ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  show x.1.1 * (dgU _ _ g'⁻¹).1.1 = _
  rw [hx, dgU_val, Matrix.fromBlocks_multiply]
  simp

theorem rat_equiv (h2 : Module.finrank F E = 2) (hκ : Fintype.card κ = a * b)
    (c : Matrix (Fin a) (Fin b) (AE F E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F))
    (hc : ∀ x, ∃ y z, c (incM F x) = (rt y, rt z)) :
    ∃ e : Matrix (Fin a) (Fin b) E ≃ (κ → F) × (κ → F), ∀ x, c (incM F x) = (rt (e x).1, rt (e x).2) := by
  have hi : Function.Injective (algebraMap F (AF F)) := AdeleRing.algebraMap_injective (𝓞 F) F
  let r : (κ → F) →ₗ[F] (κ → AF F) := (Algebra.linearMap F (AF F)).compLeft _
  have hr : Function.Injective r := fun x y e => funext fun i => hi (congrFun e i)
  let j : Matrix (Fin a) (Fin b) E →ₗ[F] (κ → AF F) × (κ → AF F) :=
    (c.toLinearMap.restrictScalars F) ∘ₗ (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E).toLinearMap.mapMatrix
  have hj : Function.Injective j := c.injective.comp fun x y e => Matrix.ext fun i k =>
    Algebra.TensorProduct.includeRight_injective hi (congrFun (congrFun e i) k)
  have : LinearMap.range j = LinearMap.range (r.prodMap r) := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨x, rfl⟩
      obtain ⟨y, z, e⟩ := hc x
      exact ⟨(y, z), e.symm⟩
    · rw [LinearMap.finrank_range_of_inj hj, LinearMap.finrank_range_of_inj (hr.prodMap hr), Module.finrank_matrix, h2]
      simp [mul_two, hκ]
  choose y z e using hc
  refine ⟨Equiv.ofBijective (fun x => (y x, z x)) ⟨fun x x' h => hj ?_, fun p => ?_⟩, e⟩
  · exact (e x).trans (by rw [(Prod.mk.inj h).1, (Prod.mk.inj h).2]; exact (e x').symm)
  · obtain ⟨x, hx⟩ := this.ge ⟨p, rfl⟩
    exact ⟨x, hr.prodMap hr ((e x).symm.trans hx)⟩

theorem dbl_main {A : Spc F E a} {Y : Spc F E b} {d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (incM F Y.J)) κ}
    {d' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F Y.J) (incM F A.J)) κ} {χ χ' : Chr F E} {om om'}
    (hψ : IsStd ψ) (h2 : Module.finrank F E = 2) (hκ : Fintype.card κ = a * b) (hA : A.J.det ≠ 0) (hY : Y.J.det ≠ 0)
    (hχ : Continuous χ') (hc : ∀ x, ∃ y z, d.e (incM F x) = (rt y, rt z)) (ht : ∀ x, d'.e xᵀ = d.e x)
    (hw : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F A.J) (incM F Y.J) d χ om)
    (hw' : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F Y.J) (incM F A.J) d' χ' om') :
    ∃ dd om₂ S, IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ ⊕ κ) ψ dd χ om₂ S (lD F κ) ∧
      IsDblCoord (cA σ) (-1) (incM F A.J) (incM F Y.J) d dd ∧ ∀ φ ∈ schA F κ, ∀ φ' ∈ schA F κ,
        (∀ g, S g (boxFun φ (star φ')) = boxFun (om' g φ) (star (om' g φ'))) ∧ ∀ h h' x, IsEmb h h' x →
          detInv χ h' • om₂ x (boxFun φ (star φ')) = boxFun (om h φ) (star (om h' φ')) := by
  obtain ⟨ho, dd, omd, h, hw, hr⟩ := hw
  obtain ⟨ho', dd', omd', h', hw', -⟩ := hw'
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e, he⟩ := rat_equiv h2 hκ d.e hc
  let S : UA σ A.J →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ) :=
    { toFun g := detInv χ' g • omd' (dgU _ _ g)
      map_one' := by simp [detInv]
      map_mul' g g' := by simp [detInv, smul_smul, mul_comm] }
  have hS : ∀ g Φ, S g Φ = detInv χ' g • omd' (dgU _ _ g) Φ := fun _ _ => rfl
  have c1 : ∀ g : UA σ A.J, detInv χ' g * χ' (Matrix.GeneralLinearGroup.det g.1) = 1 := fun g => by simp [detInv]
  have r : ∀ w w', dd.rho ψ (Matrix.fromCols w w') = dd'.rho ψ (Matrix.fromCols wᵀ w'ᵀ) := fun w w' => by
    rw [Darboux.rho, Darboux.rho, h, h', ht, ht]
  refine ⟨dd, omd, S, ⟨fun x => ?_, hw, ⟨⟨fun g Φ hΦ => ?_, fun g w Φ hΦ => ?_, fun g l hl f hf => ?_⟩, fun μ hμ g Φ hΦ => ?_,
    fun l hl Φ hΦ => ?_⟩, lD_adm, dbl_kill hψ h, fun g Φ hΦ => ?_, fun Φ hΦ => ?_⟩, h,
    fun φ hφ φ' hφ' => ⟨fun g => ?_, fun g g' x hx => dbl_emb hψ hY h hw ho hr hx hφ hφ'⟩⟩
  · refine ⟨Sum.elim (e x.toCols₁).1 (e x.toCols₂).1, Sum.elim (e x.toCols₁).2 (-(e x.toCols₂).2), ?_⟩
    rw [show incM F x = Matrix.fromCols (incM F x.toCols₁) (incM F x.toCols₂) from (Matrix.fromCols_toCols _).symm, h, he, he]
    congr 1 <;> funext i <;> cases i <;> simp
  · exact Submodule.smul_mem _ _ (hw'.2.1.pres _ Φ hΦ)
  · rw [← Matrix.fromCols_toCols w, Matrix.mul_fromCols, r, r, hS, hS, hw'.2.1.impl _ _ _ hΦ, actB_dgU]
    funext z
    simp [actB, mat, Darboux.rho, schr, mul_left_comm]
  · obtain ⟨T, hT⟩ := hw'.2.1.adm (dgU _ _ g) l hl f hf
    exact ⟨detInv χ' g • T, fun f => by simp [hS, ← hT]⟩
  · rw [← hw'.2.1.unit μ hμ (dgU _ _ g) Φ hΦ]
    simp only [hS, Pi.smul_apply, enorm_smul, detInv, ← ofReal_norm_eq_enorm (_ : Circle).1, Circle.norm_coe,
      ENNReal.ofReal_one, one_mul]
  · simp only [hS, map_smul, smul_eq_mul]
    exact (continuous_subtype_val.comp ((hχ.comp (Matrix.GeneralLinearGroup.continuous_det.comp
      continuous_subtype_val)).inv)).mul ((hw'.2.1.cont l hl Φ hΦ).comp (dgU_cont _ _))
  · rw [hS, map_smul, dbl_fix hψ hA h' hw' g hΦ, smul_eq_mul, ← mul_assoc, c1, one_mul]
  · convert e.hasSum_iff.2 (lD_theta hψ hΦ) using 3 with y
    rw [show incM F (Matrix.fromCols y (-y)) = Matrix.fromCols (incM F y) (-incM F y) by
      ext i (j | j) <;> simp [incM], Darboux.rho, h, map_neg, he]
    simp
  · rw [hS, dbl_box hψ hA h' hw' ho' g hφ hφ', smul_smul, c1, one_smul]

end Member

theorem dblW : DblW := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' h
  obtain ⟨hw, ⟨d', ht, hw'⟩, -⟩ := h.weil
  obtain ⟨dd, om₂, S, h1, h2, h3⟩ := dbl_main h.base.std h.base.cm.2.2.1 (by simp) (herm_det h.herm) (skew_det h.skew) h.hW.1
    h.good.rat ht hw hw'
  refine ⟨dd, om₂, S, _, h1, fun φ hφ φ' hφ' => ⟨box_mem hφ hφ', fun g k k' x hx =>
    ⟨?_, (h3 φ hφ φ' hφ').2 k k' x hx⟩⟩, h2, lD_haar⟩
  have p := h.weil.isUSplitting.pres
  have e : ∀ (k : UA σ W.J) ϕ, om.comp (MonoidHom.inr _ _) k (om.comp (MonoidHom.inl _ _) g ϕ) = om (g, k) ϕ := fun k ϕ => by
    rw [← Module.End.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul]; simp
  rw [(h3 φ hφ φ' hφ').1, ← thetaSum_smul, (h3 _ (hw'.1.pres g φ hφ) _ (hw'.1.pres g φ' hφ')).2 k k' x hx, e, e,
    theta_box (p _ φ hφ) (p _ φ' hφ')]
  rfl

theorem dblX : DblX := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' h
  obtain ⟨hw, ⟨d', ht, hw'⟩, -⟩ := h.weil
  have ht' : ∀ x, M.co.e xᵀ = d'.e x := fun x => (ht xᵀ).symm
  obtain ⟨dd, om₂, S, h1, h2, h3⟩ := dbl_main h.base.std h.base.cm.2.2.1 (by simp [mul_comm]) (skew_det h.skew) (herm_det h.herm)
    h.hX.1 (fun x => by rw [← ht']; exact h.good.rat xᵀ) ht' hw' hw
  refine ⟨dd, om₂, S, _, h1, fun φ hφ φ' hφ' => ⟨box_mem hφ hφ', fun k g g' x hx =>
    ⟨?_, (h3 φ hφ φ' hφ').2 g g' x hx⟩⟩, ⟨d', ht, h2⟩, lD_haar⟩
  have p := h.weil.isUSplitting.pres
  have e : ∀ (g : UA σ X.J) ϕ, om.comp (MonoidHom.inl _ _) g (om.comp (MonoidHom.inr _ _) k ϕ) = om (g, k) ϕ := fun g ϕ => by
    rw [← Module.End.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul]; simp
  rw [(h3 φ hφ φ' hφ').1, ← thetaSum_smul, (h3 _ (hw.1.pres k φ hφ) _ (hw.1.pres k φ' hφ')).2 g g' x hx, e, e,
    theta_box (p _ φ hφ) (p _ φ' hφ')]
  rfl

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.ThConstMatch
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.TC

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_ext {ι : Type} (M : ι → Type) [∀ v, AddCommGroup (M v)] [∀ v, Module ℂ (M v)] {S T : Finset ι} (h : S ⊆ T)
    (z : ∀ v, M v) : ∃ e : (PiTensorProduct ℂ fun v : S => M v) →ₗ[ℂ] PiTensorProduct ℂ fun v : T => M v,
      ∀ u : ∀ v, M v, (∀ v ∉ S, u v = z v) → e (PiTensorProduct.tprod ℂ fun v : S => u v) = PiTensorProduct.tprod ℂ fun v : T => u v := by
  let c : (∀ v : S, M v) → ∀ v : T, M v := fun x v => if hv : (v : ι) ∈ S then x ⟨v, hv⟩ else z v
  have key : ∀ [DecidableEq S] x (i : S) w, c (Function.update x i w) = Function.update (c x) ⟨i, h i.2⟩ w := fun x i w => by
    funext v
    by_cases hvi : v = ⟨i, h i.2⟩
    · subst hvi
      simp [c]
    · rw [Function.update_of_ne hvi]
      by_cases hv : (v : ι) ∈ S
      · simp only [c, dif_pos hv]
        exact Function.update_of_ne (fun e => hvi (Subtype.ext (by rw [← e]))) _ _
      · simp only [c, dif_neg hv]
  refine ⟨PiTensorProduct.lift
    { toFun := fun x => PiTensorProduct.tprod ℂ (c x)
      map_update_add' := fun x i y y' => by simp only [key]; exact (PiTensorProduct.tprod ℂ).map_update_add _ _ _ _
      map_update_smul' := fun x i a y => by simp only [key]; exact (PiTensorProduct.tprod ℂ).map_update_smul _ _ _ _ }, fun u hu => ?_⟩
  rw [PiTensorProduct.lift.tprod]
  refine congrArg (PiTensorProduct.tprod ℂ) (funext fun v => ?_)
  by_cases hv : (v : ι) ∈ S
  · simp only [c, dif_pos hv]
  · simp only [c, dif_neg hv, hu v hv]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d a a' : ℕ}
  {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

variable (B G R Rf) in

def On (T : Finset (Pl F)) (Φ : Fn F a (a + a')) (Φ' : Fn F a' (a + a')) : Prop :=
  ∃ (m m' : ℕ) (f : Fin m → SInf F _) (φ : Fin m → ∀ v : Pl F, (_ → Fv F v) → ℂ)
    (f' : Fin m' → SInf F _) (φ' : Fin m' → ∀ v : Pl F, (_ → Fv F v) → ℂ),
    (∀ i, f i ∈ G.M.Pol B.ψ B.emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = G.M.vac v) ∧
    (∀ j, f' j ∈ G.M'.Pol B.ψ B.emb ∧ (∀ v, φ' j v ∈ SB _) ∧ ∀ v ∉ T, φ' j v = G.M'.vac v) ∧
    Φ = ∑ i, pure (f i) (φ i) ∧ Φ' = ∑ j, pure (f' j) (φ' j) ∧
    ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v)) =
      ∑ j, R.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ' j v))

theorem On.mono (hm : IsMatched B G X om om' R Rf) {S T : Finset (Pl F)} (h0 : X.T ⊆ S) (h : S ⊆ T) {Φ Φ'}
    (H : On B G R Rf S Φ Φ') : On B G R Rf T Φ Φ' := by
  obtain ⟨m, m', f, φ, f', φ', h1, h2, e1, e2, e3⟩ := H
  obtain ⟨e, he⟩ := exists_ext Rf.Pi h fun v => Rf.p v (G.M.vac v)
  refine ⟨m, m', f, φ, f', φ', fun i => ⟨(h1 i).1, (h1 i).2.1, fun v hv => (h1 i).2.2 v fun k => hv (h k)⟩,
    fun i => ⟨(h2 i).1, (h2 i).2.1, fun v hv => (h2 i).2.2 v fun k => hv (h k)⟩, e1, e2, ?_⟩
  have := congrArg (e.lTensor R.Pi) e3
  simp only [map_sum, LinearMap.lTensor_tmul] at this
  refine (Finset.sum_congr rfl fun i _ => ?_).trans (this.trans (Finset.sum_congr rfl fun i _ => ?_))
  · rw [he (fun v => Rf.p v (φ i v)) fun v hv => by rw [(h1 i).2.2 v hv]]
  · rw [he (fun v => Rf.p' v (φ' i v)) fun v hv => by rw [(h2 i).2.2 v hv, (hm.fin.sph v fun k => hv (h0 k)).1]]

theorem pm_zero : PolMatch B G X R Rf 0 0 :=
  ⟨_, le_rfl, 0, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp, by simp, by simp⟩

theorem pm_add (hm : IsMatched B G X om om' R Rf) {Φ Φ' Ψ Ψ'} (c : ℂ) (h1 : PolMatch B G X R Rf Φ Φ')
    (h2 : PolMatch B G X R Rf Ψ Ψ') : PolMatch B G X R Rf (c • Φ + Ψ) (c • Φ' + Ψ') := by
  obtain ⟨T₁, hT₁, H₁⟩ := h1
  obtain ⟨T₂, hT₂, H₂⟩ := h2
  obtain ⟨m, m', f, φ, f', φ', hf, hf', rfl, rfl, e1⟩ := On.mono hm hT₁ (Finset.subset_union_left (s₂ := T₂)) H₁
  obtain ⟨k, k', g, ψ, g', ψ', hg, hg', rfl, rfl, e2⟩ := On.mono hm hT₂ (Finset.subset_union_right (s₁ := T₁)) H₂
  refine ⟨T₁ ∪ T₂, hT₁.trans Finset.subset_union_left, m + k, m' + k', Fin.append (c • f) g, Fin.append φ ψ, Fin.append (c • f') g',
    Fin.append φ' ψ', fun i => ?_, fun i => ?_, funext fun x => ?_, funext fun x => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.smul_apply]
      exact ⟨Submodule.smul_mem _ _ (hf i).1, (hf i).2⟩
    · simp only [Fin.append_right]
      exact hg i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.smul_apply]
      exact ⟨Submodule.smul_mem _ _ (hf' i).1, (hf' i).2⟩
    · simp only [Fin.append_right]
      exact hg' i
  · simp [Fin.sum_univ_add, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.mul_sum, mul_assoc]
  · simp [Fin.sum_univ_add, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.mul_sum, mul_assoc]
  · rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.smul_apply, map_smul, ← TensorProduct.smul_tmul']
    rw [← Finset.smul_sum, ← Finset.smul_sum, e1, e2]

theorem loc_op (hS : SplitModel) {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {o : Rep σ Y W} {χ χ' : Chr F E} {r s r' s' : ℕ}
    (p : IsPair B M χ χ' o r s r' s') {v : Pl F} (t : E →ₐ[F] Fv F v) {h : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) :
    ∃ O : Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ), (∀ φ ∈ SB _, O φ ∈ SB _ ∧ Acts (evFin F v) (o (1, h)) φ (O φ)) ∧
      ∀ f (φ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ), (∀ u, φ u ∈ SB _) → (∀ᶠ u in cofinite, φ u = M.vac u) →
        o (1, h) (pure f φ) = pure f (Function.update φ v (O (φ v))) := by
  obtain ⟨-, ι, b, -, r1⟩ := hS F E σ B n d Y W M _ _ o _ _ _ _ p v t
  obtain ⟨j, -, j2⟩ := exists_inv' b
  let h₀ := Matrix.GeneralLinearGroup.map (piW t) h.1
  have k := fun φ hφ => acts_of_reads (r1 h hh h₀ rfl) j2 (φ := φ) hφ
  refine ⟨j ∘ₗ GlobalTheory.SplitFlip.repB (chrW χ' t) (chrW χ t) (1, h₀) ∘ₗ ι, k, fun f φ p1 p2 => ?_⟩
  obtain ⟨T, t1, -, t3⟩ := intersection_update_fsHerm_neg_one v f p1 ((p2.and p.good.std).mono fun _ h => h.1.trans h.2)
  have := t3 _ _ (p1 v) _ (k _ (p1 v)).2
  rwa [t1, t1, Function.update_eq_self] at this

theorem pm_fin (hS : SplitModel) (hm : IsMatched B G X om om' R Rf) {v : Pl F} (t : E →ₐ[F] Fv F v) {h : UA σ G.W.J}
    (hh : h ∈ UAt σ G.W (evFin F v)) {Φ Φ'} (H : PolMatch B G X R Rf Φ Φ') :
    PolMatch B G X R Rf (om (1, h) Φ) (om' (1, h) Φ') := by
  obtain ⟨T, hT, H⟩ := H
  obtain ⟨m, m', f, φ, f', φ', h1, h2, rfl, rfl, e⟩ := On.mono hm hT (Finset.subset_insert v T) H
  obtain ⟨O, o1, o2⟩ := loc_op hS (pairV hm.triple) t hh
  obtain ⟨O', o1', o2'⟩ := loc_op hS (pairV' hm.triple) t hh
  obtain ⟨s, hs⟩ := ((Rf.p v).domRestrict (SB _)).exists_rightInverse_of_surjective
    ((LinearMap.range_domRestrict _ _).trans (hm.fin.onto v))
  let A : Module.End ℂ (Rf.Pi v) := Rf.p v ∘ₗ O ∘ₗ (SB _).subtype ∘ₗ s
  have q : ∀ x ∈ SB _, ∀ x' ∈ SB _, Rf.p v x = Rf.p' v x' → Rf.p v (O x) = Rf.p' v (O' x') := fun x hx x' hx' =>
    hm.fin.equiv v h hh x hx x' hx' _ (o1 x hx).1 _ (o1' x' hx').1 (o1 x hx).2 (o1' x' hx').2
  have A' : ∀ x' ∈ SB _, A (Rf.p' v x') = Rf.p' v (O' x') := fun x' hx' =>
    q _ (s _).2 x' hx' (LinearMap.congr_fun hs _)
  have A1 : ∀ x ∈ SB _, A (Rf.p v x) = Rf.p v (O x) := fun x hx => by
    obtain ⟨x', hx', k⟩ : Rf.p v x ∈ (SB _).map (Rf.p' v) := hm.fin.onto' v ▸ Submodule.mem_top
    rw [q x hx x' hx' k.symm, ← k, A' x' hx']
  have up : ∀ {P : ∀ u : Pl F, Type} (Q : ∀ u, P u → Prop) (x : ∀ u, P u) (y : P v), Q v y → (∀ u ≠ v, Q u (x u)) →
      ∀ u, Q u (Function.update x v y u) := fun Q x y a b u => by
    by_cases hu : u = v
    · subst hu; rwa [Function.update_self]
    · rw [Function.update_of_ne hu]; exact b u hu
  have ne : ∀ u ∉ insert v T, u ≠ v := fun u hu k => hu (k ▸ Finset.mem_insert_self _ _)
  refine ⟨_, hT.trans (Finset.subset_insert v T), m, m', f, fun i => Function.update (φ i) v (O (φ i v)), f',
    fun i => Function.update (φ' i) v (O' (φ' i v)), fun i => ⟨(h1 i).1,
      up (fun u x => x ∈ SB _) _ _ (o1 _ ((h1 i).2.1 v)).1 fun u _ => (h1 i).2.1 u,
      fun u hu => (Function.update_of_ne (ne u hu) _ _).trans ((h1 i).2.2 u hu)⟩, fun i => ⟨(h2 i).1,
      up (fun u x => x ∈ SB _) _ _ (o1' _ ((h2 i).2.1 v)).1 fun u _ => (h2 i).2.1 u,
      fun u hu => (Function.update_of_ne (ne u hu) _ _).trans ((h2 i).2.2 u hu)⟩, ?_, ?_, ?_⟩
  · rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => o2 _ _ (h1 i).2.1 ((insert v T).eventually_cofinite_notMem.mono (h1 i).2.2)
  · rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => o2' _ _ (h2 i).2.1 ((insert v T).eventually_cofinite_notMem.mono (h2 i).2.2)
  let D : ∀ u, Module.End ℂ (Rf.Pi u) := Function.update (fun _ => LinearMap.id) v A
  have := congrArg ((PiTensorProduct.map fun u : (insert v T : Finset _) => D u).lTensor R.Pi) e
  simp only [map_sum, LinearMap.lTensor_tmul, PiTensorProduct.map_tprod] at this
  refine (Finset.sum_congr rfl fun i _ => ?_).trans (this.trans (Finset.sum_congr rfl fun i _ => ?_)) <;> congr 2 <;> funext ⟨u, _⟩ <;>
    by_cases hu : u = v
  · subst hu; simp only [D, Function.update_self, A1 _ ((h1 i).2.1 _)]
  · simp only [D, Function.update_of_ne hu, LinearMap.id_apply]
  · subst hu; simp only [D, Function.update_self, A' _ ((h2 i).2.1 _)]
  · simp only [D, Function.update_of_ne hu, LinearMap.id_apply]

end GlobalTheory.ThK.Dbl.TC

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.ThConstSplit
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.TC

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem splitModel_of (h : PositivityTheory.KCo.DictX) : SplitModel := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' p v t
  obtain ⟨⟨ι, hι⟩, -, s2, k⟩ := h F E σ n d B X W M om χX χW p.base ⟨_, _, p.herm⟩ ⟨_, _, p.skew⟩ p.weil v t
  exact ⟨s2, ι, hι.bij, fun g hg => ⟨Matrix.GeneralLinearGroup.map (piW t) g.1, (k ι hι).1 g hg _ rfl⟩, (k ι hι).2⟩

theorem splitModel : SplitModel := splitModel_of PositivityTheory.KCo.dictionary_extended

end GlobalTheory.ThK.Dbl.TC

end
end

