import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
import GroundTheory.GlobalFields.Adele.Bundle0001

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ColConj
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem inv_row {R : Type} [CommRing R] {n : ℕ} (m : ℕ) (k : Fin n) (hk : k.val = m + 1) (p : GL (Fin n) R)
    (hp : IsY (m + 1) p.val) : (∀ j, j < k → (p⁻¹).val k j = 0) ∧ (p⁻¹).val k k = 1 := by
  have h1 : ∀ j, j < k → (p⁻¹).val k j = 0 := by
    have hb : p.val.BlockTriangular (fun i : Fin n => if i.val ≤ m then 0 else i.val) := by
      intro i j hij
      dsimp only at hij
      have hi : m + 1 ≤ i.val := by split_ifs at hij <;> omega
      refine (hp i hi).2 j ?_
      rw [Fin.lt_def]
      split_ifs at hij <;> omega
    haveI : Invertible p.val := p.invertible
    have hq := Matrix.blockTriangular_inv_of_blockTriangular hb
    intro j hj
    rw [Matrix.coe_units_inv]
    refine hq ?_
    rw [Fin.lt_def] at hj
    dsimp only
    split_ifs <;> omega
  refine ⟨h1, ?_⟩
  have h2 : ((p⁻¹).val * p.val) k k = 1 := by rw [Units.inv_mul, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single k, (hp k hk.ge).1, mul_one] at h2
  · exact h2
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [h1 j h, zero_mul]
    · rw [(hp j (by rw [Fin.lt_def] at h; omega)).2 k h, mul_zero]
  · simp

theorem UpperTheory.V.Af.Smo.colConj :
    UpperTheory.V.Af.Smo.ColConj := by
  intro R _ n m hm p hp u
  set k : Fin n := ⟨m.val + 1, hm⟩ with hkdef
  have hk : k.val = m.val + 1 := rfl
  obtain ⟨hb0, hb1⟩ := inv_row m.val k hk p hp
  set c : Fin n → R := fun i => if i ≤ m then u i else 0 with hc
  set a : Fin n → R := p.val *ᵥ c with ha
  set b : Fin n → R := (p⁻¹).val k with hb
  have ha0 : ∀ i, m < i → a i = 0 := by
    intro i hi
    change ∑ j, p.val i j * c j = 0
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j ≤ m
    · rw [(hp i hi).2 j (lt_of_le_of_lt hj hi), zero_mul]
    · simp [hc, hj]
  have hab : ∀ i j, j ≤ i → a i * b j = 0 := by
    intro i j hij
    by_cases hi : m < i
    · rw [ha0 i hi, zero_mul]
    · rw [hb0 j (by rw [Fin.lt_def] at hi ⊢; rw [Fin.le_def] at hij; omega), mul_zero]
  have hdot : b ⬝ᵥ a = 0 := Finset.sum_eq_zero fun i _ => by rw [mul_comm]; exact hab i i le_rfl
  have hsq : vecMulVec a b * vecMulVec a b = 0 := by
    rw [vecMulVec_mul_vecMulVec, hdot, zero_smul, vecMulVec_zero]
  refine ⟨⟨1 + vecMulVec a b, 1 - vecMulVec a b, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [add_mul, mul_sub, mul_sub, hsq]; simp
  · rw [sub_mul, mul_add, mul_add, hsq]; simp
  · intro i _
    refine ⟨?_, fun j hj => ?_⟩
    · simp [vecMulVec_apply, hab i i le_rfl]
    · simp [vecMulVec_apply, hab i j hj.le, Matrix.one_apply_ne hj.ne']
  · have : dotLe m (p.val m) u = a m := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [hc]
    rw [this]
    unfold supN
    rw [Finset.sum_eq_single m, Finset.sum_eq_single k]
    · have : m ≠ k := fun h => by have := congrArg Fin.val h; omega
      simp [hk, vecMulVec_apply, hb1, Matrix.one_apply_ne this]
    · intro j _ hj
      rw [if_neg fun h => hj (Fin.ext (by omega))]
    · simp
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => ?_
      split_ifs with h
      · have hne : i ≠ j := fun e => by have := congrArg Fin.val e; omega
        have : a i * b j = 0 := by
          rcases lt_or_gt_of_ne hi with h' | h'
          · rw [hb0 j (by rw [Fin.lt_def] at h' ⊢; omega), mul_zero]
          · rw [ha0 i h', zero_mul]
        simp [vecMulVec_apply, this, Matrix.one_apply_ne hne]
      · rfl
    · simp
  · have h1 : colM m u = 1 + vecMulVec c (Pi.single k 1) := by
      unfold colM
      congr 1
      ext i j
      by_cases hj : j = k
      · subst hj
        simp [vecMulVec_apply, hc, hk]
      · have : j.val ≠ m.val + 1 := fun h => hj (Fin.ext h)
        simp [vecMulVec_apply, hj, this]
    have h2 : b ᵥ* p.val = Pi.single k 1 := by
      ext j
      have : ((p⁻¹).val * p.val) k j = (1 : Matrix (Fin n) (Fin n) R) k j := by rw [Units.inv_mul]
      rw [Matrix.one_apply] at this
      rw [Pi.single_apply, ← if_congr eq_comm rfl rfl, ← this]
      rfl
    change p.val * colM m u = (1 + vecMulVec a b) * p.val
    rw [h1, mul_add, add_mul, mul_one, one_mul, mul_vecMulVec, vecMulVec_mul, h2]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ConvFub
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.convFub :
    UpperTheory.V.Af.Smo.ChartCont → UpperTheory.V.Af.Smo.ConvFub := by
  classical
  intro hc E _ _ _ n f hf ⟨C, hC⟩ α X _ _ _ _ ν _ u a hu ha ⟨D, hD⟩ g
  have hS : MeasurableSet ((Set.univ : Set X) ×ˢ invSet E n) :=
    (isOpen_univ.prod TR.isOpen_invSet).measurableSet
  have h1 : ContinuousOn (fun z : X × Lie E n => chart f (u z.1 * g) z.2) (Set.univ ×ˢ invSet E n) :=
    (hc E n f hf).1.comp (f := fun z : X × Lie E n => (u z.1 * g, z.2))
      (((hu.comp continuous_fst).mul continuous_const).prodMk continuous_snd).continuousOn
      fun z hz => ⟨trivial, hz.2⟩
  have h2 : Measurable fun z : X × Lie E n => chart f (u z.1 * g) z.2 := by
    have := h1.measurable_piecewise (g := fun _ => 0) continuousOn_const hS
    convert this using 1
    funext z
    by_cases hz : z ∈ (Set.univ : Set X) ×ˢ invSet E n
    · rw [Set.piecewise_eq_of_mem _ _ _ hz]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hz, chart]
      exact dif_neg fun h => hz ⟨trivial, h⟩
  have hb : ∀ g y, ‖chart f g y‖ ≤ C := fun g y => by
    unfold chart
    split_ifs
    · exact hC _
    · simpa using (norm_nonneg _).trans (hC 1)
  haveI : (volume : Measure (Fin n → Rinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hα : Integrable (fun y => α y) (volume : Measure (Lie E n)) := α.integrable
  have ha' : Integrable a ν := Integrable.of_bound ha.measurable.aestronglyMeasurable D (.of_forall hD)
  have hi : Integrable (fun z : X × Lie E n => chart f (u z.1 * g) z.2 * (a z.1 * α z.2)) (ν.prod volume) :=
    (ha'.mul_prod hα).bdd_mul h2.aestronglyMeasurable (.of_forall fun z => hb _ _)
  calc ∫ x, conv f α (u x * g) * a x ∂ν
      = ∫ x, (∫ y, chart f (u x * g) y * (a x * α y)) ∂ν := by
        refine integral_congr_ae (.of_forall fun x => ?_)
        simp only [conv]
        rw [← integral_mul_const]
        exact integral_congr_ae (.of_forall fun y => by ring)
    _ = ∫ y, ∫ x, chart f (u x * g) y * (a x * α y) ∂ν := integral_integral_swap hi
    _ = _ := by
        unfold conv
        refine integral_congr_ae (.of_forall fun y => ?_)
        simp only [chart]
        split_ifs with h
        · rw [← integral_mul_const]
          exact integral_congr_ae (.of_forall fun x => by simp only [mul_assoc])
        · simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ConvNice
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.convNice :
    UpperTheory.V.Af.Smo.ConvCont → UpperTheory.V.Af.Smo.ConvFub → UpperTheory.V.Af.Smo.ConvNice := by
  intro hc hf E _ _ _ n f hN α
  obtain ⟨h1, h2⟩ := hc E n f hN.cont hN.bdd α
  refine ⟨⟨h1, h2, ?_, ?_, ?_⟩, ?_⟩
  · intro γ g
    have e : chart f (AdelicGLn.diagonal E n γ * g) = chart f g := by
      funext x
      simp only [chart, mul_assoc, hN.left γ]
    simp only [conv, e]
  · intro r hr hrn g
    haveI : IsFiniteMeasure ((unipMeasure E n r).restrict (unipFundamentalDomain E n r)) := by
      obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := E) (n := n) (r := r)
      exact ⟨by
        rw [Measure.restrict_apply_univ]
        exact (measure_mono hDC).trans_lt hC.measure_lt_top⟩
    have h := hf E n f hN.cont hN.bdd α _ ((unipMeasure E n r).restrict (unipFundamentalDomain E n r))
      unipGL (fun _ => 1) continuous_unipGL continuous_const ⟨1, fun _ => by simp⟩ g
    simp only [mul_one] at h
    have e : (fun g' => ∫ x in unipFundamentalDomain E n r, f (unipGL x * g') ∂unipMeasure E n r) = fun _ => 0 :=
      funext fun g' => hN.cusp r hr hrn g'
    rw [constantTerm, h, e]
    simp [conv, chart]
  · obtain ⟨V, hV⟩ := hN.level
    refine ⟨V, fun g v hv => ?_⟩
    have e : (fun x => f (x * finGL E n v)) = f := funext fun x => hV x v hv
    rw [conv, ← TR.chart_rt_fin, e, conv]
  · funext g
    haveI : IsFiniteMeasure ((FourierWhittaker.vecMeasure E (FourierWhittaker.Pos n)).restrict
        (FourierWhittaker.vecDomain E (FourierWhittaker.Pos n))) :=
      ⟨by rw [Measure.restrict_apply_univ, FourierWhittaker.vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
    exact hf E n f hN.cont hN.bdd α _ ((FourierWhittaker.vecMeasure E (FourierWhittaker.Pos n)).restrict
        (FourierWhittaker.vecDomain E (FourierWhittaker.Pos n))) FourierWhittaker.uGL
      (fun X => (GroundTheory.Global.adelicChar E (-FourierWhittaker.supSum 0 X) : ℂ)) FourierWhittaker.continuous_uGL
      (continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp
        (FourierWhittaker.continuous_supSum 0).neg)) ⟨1, fun _ => (Circle.norm_coe _).le⟩ g
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.DenseAway
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

noncomputable section

namespace UpperTheory.V.Af.Smo.DenseAwayFromPlace

open GlobalTheory.CuspRep (cornerGL matN map_cornerGL_of_hom map_cornerGL_of_zero pFin_finGL)

private theorem dense_gl {K R : Type} [Field K] [NormedCommRing R] [CompleteSpace R] [Nontrivial R] (n : ℕ)
    (q : K →+* R) (hq : DenseRange q) : DenseRange (GeneralLinearGroup.map (n := Fin n) q) := by
  have ho : Topology.IsOpenEmbedding (Units.val : GL (Fin n) R → Matrix (Fin n) (Fin n) R) := by
    have h : ∀ (M : Type) [NormedRing M], CompleteSpace M → Topology.IsOpenEmbedding (Units.val : Mˣ → M) :=
      fun _ _ _ => Units.isOpenEmbedding_val
    exact @h _ Matrix.linftyOpNormedRing (inferInstanceAs (CompleteSpace (Fin n → Fin n → R)))
  have hd : DenseRange fun x : Matrix (Fin n) (Fin n) K => x.map q :=
    DenseRange.piMap fun _ : Fin n => DenseRange.piMap fun _ : Fin n => hq
  refine dense_iff_inter_open.2 fun U hU hne => ?_
  obtain ⟨x, u, hu, e⟩ := hd.exists_mem_open (ho.isOpenMap U hU) (hne.image _)
  have h1 : IsUnit (q x.det) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← e]
    exact (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
  have h2 : x.det ≠ 0 := fun h => by
    rw [h, map_zero] at h1
    exact not_isUnit_zero h1
  exact ⟨u, hu, GeneralLinearGroup.mkOfDetNeZero x h2, Units.ext e.symm⟩

private theorem dense_abs {K R A : Type} [Field K] [NormedCommRing R] [CompleteSpace R] [Nontrivial R] [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (n : ℕ) (a : K →+* A) (p : A →+* R) (s : R →ₙ+* A) (hs : Continuous s)
    (hp : ∀ x, p (s x) = x) (hq : DenseRange (p.comp a)) :
    Dense {x : GL (Fin n) A | ∃ γ k, GeneralLinearGroup.map p k = 1 ∧ x = GeneralLinearGroup.map a γ * k} := by
  have hc : Continuous (cornerGL n s) := by
    refine Continuous.units_map _ ?_
    change Continuous fun x : Matrix (Fin n) (Fin n) R => 1 - matN n s 1 + matN n s x
    exact continuous_const.add (continuous_id.matrix_map hs)
  have hps : ∀ y, GeneralLinearGroup.map p (cornerGL n s y) = y := fun y => by
    rw [map_cornerGL_of_hom s p (RingHom.id _) hp]
    rfl
  refine dense_iff_inter_open.2 fun U hU ⟨g, hg⟩ => ?_
  let Φ : GL (Fin n) R → GL (Fin n) A := fun y => cornerGL n s y * ((cornerGL n s (GeneralLinearGroup.map p g))⁻¹ * g)
  have hΦ : Continuous Φ := hc.mul continuous_const
  obtain ⟨γ, hγ⟩ := (dense_gl n _ hq).exists_mem_open (hU.preimage hΦ)
    ⟨GeneralLinearGroup.map p g, by simpa [Φ] using hg⟩
  refine ⟨_, hγ, γ, (GeneralLinearGroup.map a γ)⁻¹ * Φ (GeneralLinearGroup.map (p.comp a) γ), ?_, by simp⟩
  have e : GeneralLinearGroup.map p (GeneralLinearGroup.map a γ) = GeneralLinearGroup.map (p.comp a) γ := rfl
  simp only [Φ, map_mul, map_inv, hps, e, inv_mul_cancel, mul_one]

variable {E : Type} [Field E] [NumberField E]

private theorem cont_sLoc (w : HeightOneSpectrum (𝓞 E)) : Continuous (sLoc E w) := by
  classical
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 E))) ≤ Filter.principal {w}ᶜ :=
    Filter.le_principal_iff.2 (Set.finite_singleton w).compl_mem_cofinite
  let f : w.adicCompletion E → RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) (Filter.principal {w}ᶜ) :=
    fun x => ⟨Pi.single w x, Filter.eventually_principal.2 fun v hv => by
      rw [Pi.single_eq_of_ne hv]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2
    (continuous_single (A := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w)
  exact (RestrictedProduct.continuous_inclusion hle).comp hf

variable (S : Finset (HeightOneSpectrum (𝓞 E)))

private theorem sum_mem (x : ∀ v : S, v.1.adicCompletion E) (w : S) : pLoc E w.1 (∑ v : S, sLoc E v.1 (x v)) = x w := by
  classical
  rw [map_sum, Finset.sum_eq_single w]
  · exact Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w.1 _
  · exact fun v _ h => Pi.single_eq_of_ne (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun e => h (Subtype.ext e.symm)) _
  · simp

private theorem sum_notMem (x : ∀ v : S, v.1.adicCompletion E) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ S) :
    pLoc E w (∑ v : S, sLoc E v.1 (x v)) = 0 := by
  classical
  rw [map_sum]
  exact Finset.sum_eq_zero fun v _ => Pi.single_eq_of_ne (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (fun e : w = v.1 => hw (e ▸ v.2)) _

private abbrev RS : Type :=
  (∀ v : S, v.1.adicCompletion E) × (∀ w : (Finset.univ : Finset (InfinitePlace E)), w.1.Completion)

private def pS : Ad E →+* RS S :=
  (RingHom.pi fun v : S => (pLoc E v.1).comp (pFin E)).prod
    (RingHom.pi fun w => (Pi.evalRingHom (fun w : InfinitePlace E => w.Completion) w.1).comp
      (RingHom.fst (InfiniteAdeleRing E) (Af E)))

private def sS : RS S →ₙ+* Ad E where
  toFun x := ((fun w => x.2 ⟨w, Finset.mem_univ w⟩, ∑ v : S, sLoc E v.1 (x.1 v)) : InfiniteAdeleRing E × Af E)
  map_mul' x y := Prod.ext rfl (FiniteAdeleRing.ext _ fun w => by
    change pLoc E w (∑ v : S, sLoc E v.1 ((x.1 * y.1) v)) =
      pLoc E w ((∑ v : S, sLoc E v.1 (x.1 v)) * ∑ v : S, sLoc E v.1 (y.1 v))
    rw [map_mul]
    by_cases hw : w ∈ S
    · rw [sum_mem S _ ⟨w, hw⟩, sum_mem S _ ⟨w, hw⟩, sum_mem S _ ⟨w, hw⟩]
      rfl
    · rw [sum_notMem S _ hw, sum_notMem S _ hw, zero_mul])
  map_zero' := Prod.ext rfl (Finset.sum_eq_zero fun v _ => map_zero _)
  map_add' x y := Prod.ext rfl ((Finset.sum_congr rfl fun v _ => map_add _ _ _).trans Finset.sum_add_distrib)

private theorem cont_sS : Continuous (sS S) :=
  Continuous.prodMk (continuous_pi fun w => (continuous_apply _).comp continuous_snd)
    (continuous_finset_sum _ fun v _ => (cont_sLoc v.1).comp ((continuous_apply v).comp continuous_fst))

private theorem pS_sS (x : RS S) : pS S (sS S x) = x :=
  Prod.ext (funext fun v => sum_mem S x.1 v) rfl

end UpperTheory.V.Af.Smo.DenseAwayFromPlace

end

open UpperTheory.V.Af.Smo.DenseAwayFromPlace in
theorem UpperTheory.V.Af.Smo.denseAway :
    UpperTheory.V.Af.Smo.DenseAway := by
  intro E _ _ n S
  haveI : Inhabited (Finset.univ : Finset (InfinitePlace E)) := ⟨⟨Classical.arbitrary _, Finset.mem_univ _⟩⟩
  haveI : Nontrivial (∀ w : (Finset.univ : Finset (InfinitePlace E)), w.1.Completion) := Pi.nontrivial
  haveI : Nontrivial (RS S) := nontrivial_prod_right
  refine (dense_abs n (algebraMap E (Ad E)) (pS S) (sS S) (cont_sS S) (pS_sS S)
    (GroundTheory.Global.denseRange_algebraMap_prod_pi S Finset.univ)).mono ?_
  rintro _ ⟨γ, k, hk, rfl⟩
  have h : ∀ i j, pS S (k i j) = (1 : Matrix (Fin n) (Fin n) (RS S)) i j := fun i j =>
    congrArg (fun x : GL (Fin n) (RS S) => x i j) hk
  refine ⟨γ, GeneralLinearGroup.map (pFin E) k, fun w hw => ?_, congrArg _ ?_⟩
  · refine Units.ext (Matrix.ext fun i j => ?_)
    refine (congrFun (congrArg Prod.fst (h i j)) ⟨w, hw⟩).trans ?_
    by_cases e : i = j <;> simp [Matrix.one_apply, e]
  · refine Units.ext (Matrix.ext fun i j => Prod.ext (funext fun w => ?_) ?_)
    · refine (congrFun (congrArg Prod.snd (h i j)) ⟨w, Finset.mem_univ w⟩).trans ?_
      change _ = (((1 : Matrix (Fin n) (Fin n) (Ad E)) i j).1 - 0 + 0) w
      rw [add_zero, sub_zero]
      by_cases e : i = j <;> simp only [Matrix.one_apply, e, if_true, if_false] <;> rfl
    · exact (congrArg (fun x : GL (Fin n) (Af E) => x i j)
        (GlobalTheory.CuspRep.pFin_finGL (GeneralLinearGroup.map (pFin E) k))).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.EigMap
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

section

variable {E : Type} [Field E] [NumberField E] {n : ℕ} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}

private theorem sum_Tj {ϖ : w.adicCompletion E} (hϖ : Formalism.UG.IsUnifV E w ϖ) (j : ℕ) :
    ∃ s : Finset (GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w n),
      ∀ F : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w n → ℂ,
        ∑ᶠ c, Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j c.out * F c =
          ∑ c ∈ s, Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j c.out * F c := by
  have hf := Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w n) (GlobalTheory.LFun.Tj_mem_hecke (n := n) hϖ j).2
  refine ⟨hf.toFinset, fun F => finsum_eq_sum_of_support_subset _ fun c hc => ?_⟩
  rw [Set.Finite.coe_toFinset]
  exact left_ne_zero_of_mul hc

private theorem eig_zero (h : B.card = n) : Eig w B (fun _ : GL (Fin n) (w.adicCompletion E) => (0 : ℂ)) :=
  ⟨h, fun _ _ _ => rfl, fun _ _ _ _ _ => by simp⟩

private theorem eig_sub {W W' : GL (Fin n) (w.adicCompletion E) → ℂ} (h : Eig w B W) (h' : Eig w B W') :
    Eig w B (fun y => W y - W' y) := by
  refine ⟨h.card, fun g k hk => by simp only [h.inv g k hk, h'.inv g k hk], fun ϖ hϖ j hj g => ?_⟩
  obtain ⟨s, hs⟩ := sum_Tj (n := n) hϖ j
  have e := h.eig ϖ hϖ j hj g
  have e' := h'.eig ϖ hϖ j hj g
  rw [hs] at e e' ⊢
  simp only [mul_sub, Finset.sum_sub_distrib, e, e']

private theorem eig_int {X : Type} [MeasurableSpace X] (μ : Measure X) (hB : B.card = n)
    (F : X → GL (Fin n) (w.adicCompletion E) → ℂ) (a : X → ℂ) (h : ∀ x, Eig w B (F x))
    (hi : ∀ y, Integrable (fun x => F x y * a x) μ) : Eig w B (fun y => ∫ x, F x y * a x ∂μ) := by
  refine ⟨hB, fun g k hk => by simp only [fun x => (h x).inv g k hk], fun ϖ hϖ j hj g => ?_⟩
  obtain ⟨s, hs⟩ := sum_Tj (n := n) hϖ j
  rw [hs]
  simp only [← integral_const_mul]
  rw [← integral_finset_sum _ fun c _ => (hi _).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have e := (h x).eig ϖ hϖ j hj g
  rw [hs] at e
  simp only [← mul_assoc, ← e, Finset.sum_mul]

end

open GroundTheory.Automorphic.FourierWhittaker in
theorem UpperTheory.V.Af.Smo.eigMap :
    UpperTheory.V.Af.Smo.ChartCont → UpperTheory.V.Af.Smo.EigMap := by
  intro hC E _ _ _ n w B f hf
  refine ⟨fun hN g => ?_, fun hN α g => ?_, fun f' hf' g => eig_sub (hf g) (hf' g)⟩
  · refine eig_int ((vecMeasure E (Pos n)).restrict (vecDomain E (Pos n))) (hf 1).card
      (fun X y => f (uGL X * (g * finGL E n (locGL E n w y))))
      (fun X => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ)) (fun X => ?_) fun y => ?_
    · simpa only [mul_assoc] using hf (uGL X * g)
    · have hc : Continuous fun X : Pos n → Ad E => f (uGL X * (g * finGL E n (locGL E n w y))) *
          (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
        (hN.cont.comp (continuous_uGL.mul continuous_const)).mul
          (continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg))
      exact (hc.continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set subset_closure
  · refine eig_int volume (hf 1).card (fun x y => chart f (g * finGL E n (locGL E n w y)) x) α (fun x => ?_) fun y => ?_
    · by_cases hx : IsUnit (Matrix.of x)
      · have := hf (g * infGL E n hx.unit)
        simpa only [chart, dif_pos hx, mul_assoc, TR.infGL_comm] using this
      · simpa only [chart, dif_neg hx] using eig_zero (w := w) (hf 1).card
    · obtain ⟨C, hC'⟩ := hN.bdd
      haveI : BorelSpace (Lie E n) := inferInstance
      haveI : (volume : Measure (Rinf E)).IsAddHaarMeasure := inferInstance
      haveI : (volume : Measure (Fin n → Rinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
      haveI : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
      refine α.integrable.bdd_mul (c := C) ((hC E n f hN.cont).2 _).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      unfold chart
      split_ifs
      · exact hC' _
      · simpa using (norm_nonneg _).trans (hC' 1)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.InKSMono
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem lev (hL : LevelS) {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (π : CuspSub E n)
    (φ : TR.Sm E n) (hφ : φ ∈ π.V) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 E)), ∀ g k, InKS S k → φ.1 (g * finGL E n k) = φ.1 g := by
  let V : OpenSubgroup (GL (Fin n) (Af E)) :=
    { carrier := {k | TR.finRep E n k φ = φ}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      isOpen' := (π.cusp φ hφ).1.level }
  obtain ⟨S, hS⟩ := hL E n V
  refine ⟨S, fun g k hk => ?_⟩
  have h : TR.finRep E n k φ = φ := hS k hk
  exact congrArg (fun ψ : TR.Sm E n => ψ.1 g) h

private theorem inKS_mono {E : Type} [Field E] [NumberField E] {n : ℕ} {S T : Finset (HeightOneSpectrum (𝓞 E))}
    (h : S ⊆ T) {k : GL (Fin n) (Af E)} (hk : InKS T k) : InKS S k :=
  ⟨fun w hw => hk.1 w (h hw), hk.2⟩

theorem UpperTheory.V.Af.Smo.setUp :
    UpperTheory.V.Af.Smo.PsiLoc → UpperTheory.V.Af.Smo.LevelS → UpperTheory.V.Af.Smo.SetUp := by
  intro hP hL E _ _ _ n π π' hs φ hφ φ' hφ'
  classical
  obtain ⟨S₁, h₁⟩ := lev hL π φ hφ
  obtain ⟨S₂, h₂⟩ := lev hL π' φ' hφ'
  have hf := Filter.eventually_cofinite.1 ((hP E).2.and hs)
  have hB : ∀ w : HeightOneSpectrum (𝓞 E), ∃ B : Multiset ℂˣ, w ∉ hf.toFinset →
      GoodAt w (psiL w) ∧ π.HasSat w B ∧ π'.HasSat w B := fun w => by
    by_cases hw : w ∈ hf.toFinset
    · exact ⟨0, fun h => absurd hw h⟩
    · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hw
      obtain ⟨hg, B, hB⟩ := hw
      exact ⟨B, fun _ => ⟨hg, hB⟩⟩
  choose B hB using hB
  refine ⟨hf.toFinset ∪ (S₁ ∪ S₂), B, fun w hw => hB w fun h => hw (Finset.mem_union_left _ h),
    fun g k hk => h₁ g k (inKS_mono ?_ hk), fun g k hk => h₂ g k (inKS_mono ?_ hk)⟩
  · exact Finset.subset_union_left.trans Finset.subset_union_right
  · exact Finset.subset_union_right.trans Finset.subset_union_right
end

