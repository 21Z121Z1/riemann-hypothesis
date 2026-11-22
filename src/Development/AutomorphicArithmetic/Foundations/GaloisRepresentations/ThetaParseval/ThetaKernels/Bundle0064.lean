import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Height
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwa
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0030
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitHtA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0028
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.FockOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0039
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0055
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0029
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.ThetaAutoAt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0043
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SchrodingerCommutation.CommSchr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0054

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitHeight
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit.Ht
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem k_int_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {k : d.G} (hk : k ∈ d.K) (v : HeightOneSpectrum (𝓞 F)) (i j : Fin d.n ⊕ Fin d.n) :
    compFin F E v (inFrame d.b k i j) ∈ OE E v ∧ compFin F E v (inFrame d.b k⁻¹ i j) ∈ OE E v := by
  have h := ((d.ok.stdK k).1 hk).2
  have e : ∀ z : AE F E, compFin F E v (finOne F • z) = compFin F E v z := fun z => by
    rw [compFin_smul, evFin_finOne, one_smul]
  exact ⟨e _ ▸ compFin_intHat v (h k (by simp) i j), e _ ▸ compFin_intHat v (h k⁻¹ (by simp) i j)⟩
theorem k_unit_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {k : d.G} (hk : k ∈ d.K) (w : InfinitePlace F) :
    (inFrame d.b k).map (piInf (d.B.emb w)) * ((inFrame d.b k).map (piInf (d.B.emb w)))ᴴ = 1 :=
  ((d.ok.stdK k).1 hk).1 w
theorem inFrame_mul_inv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (k : d.G) : inFrame d.b k * inFrame d.b k⁻¹ = 1 := by
  rw [← _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, mul_inv_cancel]
  simp only [inFrame, mat2, OneMemClass.coe_one, Units.val_one, Matrix.mul_one]
  exact _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d
theorem piInf_cA_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (z : AE F E) :
    piInf (d.B.emb w) (cA σ z) = star (piInf (d.B.emb w) z) := by
  simp only [piInf, RingHom.comp_apply, compInf_cA]
  exact (GlobalTheory.AdelicU.infEmb_sigR d.ok.good.cm (d.B.emb w) _).symm
theorem piInf_inclR_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (e : E) :
    piInf (d.B.emb w) (inclR (F := F) (AF F) e) = (d.B.emb w).1 e := by
  simp [piInf, compInf, inclR, Algebra.TensorProduct.map_tmul, infEmb_tmul]
theorem real_at_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hR : _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g) (ε : ℤˣ) (β : nA σ d.Y d.b)
    (D : GL (Fin d.n) (AE F E)) {k : d.G} (hk : k ∈ d.K)
    (h1 : ((ε : ℤ) : AE F E) • t.1 = D.1 * (inFrame d.b k).toBlocks₂₁)
    (h2 : ((ε : ℤ) : AE F E) • (β.1 * u.1) = D.1 * (inFrame d.b k).toBlocks₂₂) (w : InfinitePlace F) :
    ‖piInf (d.B.emb w) D.1.det‖ ^ 2 = ‖piInf (d.B.emb w) t.1.det‖ ^ 2 *
      (1 + (((g w)⁻¹).1 * (Gen.matInf (hOf β).1).map (θ w) * (((g w)⁻¹).1)ᴴ) *
        (((g w)⁻¹).1 * (Gen.matInf (hOf β).1).map (θ w) * (((g w)⁻¹).1)ᴴ)).det.re := by
  set pw := piInf (d.B.emb w) with hpw
  have hmap : ∀ {a b c : Type} [Fintype b] (X : Matrix a b (AE F E)) (Y : Matrix b c (AE F E)),
      (X * Y).map pw = X.map pw * Y.map pw := fun X Y => Matrix.map_mul
  have hsm : ∀ {a b : Type} (c : AE F E) (X : Matrix a b (AE F E)), (c • X).map pw = pw c • X.map pw := by
    intro a b c X; ext i j; simp
  have hθ : (Gen.matInf (hOf β).1).map (θ w) = ((hOf β).1.map pw).map star := by
    ext i j
    exact hR.th w _
  have hK : ((inFrame d.b k).map pw).toBlocks₂₁ * (((inFrame d.b k).map pw).toBlocks₂₁)ᴴ +
      ((inFrame d.b k).map pw).toBlocks₂₂ * (((inFrame d.b k).map pw).toBlocks₂₂)ᴴ = 1 := by
    have hu := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.k_unit_k d hk w
    ext i j
    have := congrFun (congrFun hu (Sum.inr i)) (Sum.inr j)
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.conjTranspose_apply, Matrix.one_apply,
      Sum.inr.injEq] at this
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
      Matrix.add_apply] using this
  have h1' := congrArg (fun M => M.map pw) h1
  have h2' := congrArg (fun M => M.map pw) h2
  simp only [hsm, hmap, map_intCast] at h1' h2'
  have htu : (t.1.map pw)ᴴ * u.1.map pw = 1 := by
    have h0 := congrArg (fun M => M.map pw) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.levi_tu_k d x t u hR.levi)
    simp only [hmap, Matrix.map_one _ (map_zero pw) (map_one pw)] at h0
    have h3 : ((t.1ᵀ.map pw) * ((u.1.map (cA σ)).map pw)).map (starRingEnd ℂ) =
        (1 : Matrix (Fin d.n) (Fin d.n) ℂ).map (starRingEnd ℂ) := by rw [h0]
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h3
    have e1 : ((u.1.map (cA σ)).map pw).map (starRingEnd ℂ) = u.1.map pw := by
      ext i j
      simp only [Matrix.map_apply]
      rw [hpw, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.piInf_cA_k]
      simp
    rw [e1] at h3
    rw [← h3]
    rfl
  have hh : ((hOf β).1.map pw)ᴴ = (hOf β).1.map pw := by
    ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [← (hOf β).2 a b, sigR_eq_cA', _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.piInf_cA_k]
  have hβ : β.1.map pw = -(((d.B.emb w).1 η) • ((hOf β).1.map pw)ᵀ) := by
    rw [hR.hof β]
    ext i j
    simp [Matrix.map_apply, Matrix.mul_apply, Matrix.scalar_apply, incM, Matrix.diagonal_apply, hpw, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.piInf_inclR_k]
  have hg : (g w).1 * (u.1.map pw)ᴴ = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1 := hR.gc w
  have he : ‖(((ε : ℤ) : ℂ))‖ = 1 := by rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  have hη : (d.B.emb w).1 η ≠ 0 := (map_ne_zero _).2 hR.ne
  have hgi : IsUnit (g w).1.det := (Matrix.isUnit_iff_isUnit_det _).1 (g w).isUnit
  have key := GlobalTheory.T.det_sq_norm_eq_hermitian_block_formula (t.1.map pw) (u.1.map pw) (D.1.map pw) ((inFrame d.b k).map pw).toBlocks₂₁
    ((inFrame d.b k).map pw).toBlocks₂₂ (β.1.map pw) ((hOf β).1.map pw) (g w).1 ((ε : ℤ) : ℂ) ((d.B.emb w).1 η)
    he hη hK h1' h2' htu hh hβ hg hgi
  rw [det_map, det_map] at key
  rw [hθ, Matrix.coe_units_inv]
  exact key
theorem fin_at_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hR : _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g) (ε : ℤˣ) (β : nA σ d.Y d.b)
    (D : GL (Fin d.n) (AE F E)) {k : d.G} (hk : k ∈ d.K)
    (h1 : ((ε : ℤ) : AE F E) • t.1 = D.1 * (inFrame d.b k).toBlocks₂₁)
    (h2 : ((ε : ℤ) : AE F E) • (β.1 * u.1) = D.1 * (inFrame d.b k).toBlocks₂₂) (v : HeightOneSpectrum (𝓞 F))
    (lam : Measure (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) [lam.IsAddHaarMeasure] :
    ‖Algebra.norm (v.adicCompletion F) (compFin F E v D.1.det)‖ =
      ‖Algebra.norm (v.adicCompletion F) (compFin F E v t.1.det)‖ *
        Gen.nu2 lam (L1 σ t v) (L2 σ u η v) (Gen.matV v (hOf β).1) := by
  set cf := compFin F E v with hcf
  have hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ := d.ok.good.cm
  have hmap : ∀ {a b c : Type} [Fintype b] (X : Matrix a b (AE F E)) (Y : Matrix b c (AE F E)),
      (X * Y).map cf = X.map cf * Y.map cf := fun X Y => Matrix.map_mul
  have hsm : ∀ {a b : Type} (c : AE F E) (X : Matrix a b (AE F E)), (c • X).map cf = cf c • X.map cf := by
    intro a b c X; ext i j; simp
  have ht : IsUnit (t.1.map cf).det := by
    rw [det_map]; exact (Matrix.GeneralLinearGroup.det t).isUnit.map cf
  have hD : IsUnit (D.1.map cf).det := by
    rw [det_map]; exact (Matrix.GeneralLinearGroup.det D).isUnit.map cf
  have htu : (t.1.map cf)ᵀ * (u.1.map cf).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) = 1 := by
    have h0 := congrArg (fun M => M.map cf) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.levi_tu_k d x t u hR.levi)
    simp only [hmap, Matrix.map_one _ (map_zero cf) (map_one cf)] at h0
    rw [← h0, Matrix.transpose_map]
    congr 1
    ext i j
    exact (compFin_cA v _).symm
  have hη : IsUnit (inclR (F := F) (v.adicCompletion F) η) := (Ne.isUnit hR.ne).map _
  have he : IsUnit (((ε : ℤ) : v.adicCompletion F ⊗[F] E)) := ε.isUnit.map (Int.castRingHom _)
  have he1 : ‖Algebra.norm (v.adicCompletion F) (((ε : ℤ) : v.adicCompletion F ⊗[F] E))‖ = 1 := by
    rcases Int.units_eq_one_or ε with h | h
    · simp [h]
    · have : (((ε : ℤ) : v.adicCompletion F ⊗[F] E)) = algebraMap (v.adicCompletion F) _ (-1) := by
        rw [h]; simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, map_neg, map_one]
      rw [this, Algebra.norm_algebraMap, norm_pow, norm_neg, norm_one, one_pow]
  have hβ : β.1.map cf = -((inclR (F := F) (v.adicCompletion F) η) • ((hOf β).1.map cf)ᵀ) := by
    rw [hR.hof β]
    ext i j
    simp [Matrix.map_apply, Matrix.mul_apply, Matrix.scalar_apply, incM, Matrix.diagonal_apply, hcf,
      compFin_inclR]
  have hh : ∀ a b, HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ (((hOf β).1.map cf) b a) = ((hOf β).1.map cf) a b := by
    intro a b
    simp only [Matrix.map_apply]
    rw [← (hOf β).2 a b]
    exact (compFin_sigR v _).symm
  have hkk : (inFrame d.b k).map cf * (inFrame d.b k⁻¹).map cf = 1 := by
    rw [← hmap, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.inFrame_mul_inv_k, Matrix.map_one _ (map_zero cf) (map_one cf)]
  have h1' := congrArg (fun M => M.map cf) h1
  have h2' := congrArg (fun M => M.map cf) h2
  simp only [hsm, hmap, map_intCast] at h1' h2'
  have key := PositivityTheory.SiegelWeilFormula.HeightDict.fin_index hcm v d.n (t.1.map cf) (u.1.map cf) (D.1.map cf) (β.1.map cf) ((hOf β).1.map cf)
    (inclR (F := F) (v.adicCompletion F) η) (((ε : ℤ) : v.adicCompletion F ⊗[F] E))
    ((inFrame d.b k).map cf) ((inFrame d.b k⁻¹).map cf) ht hD htu hη he he1 hβ hh hkk
    (fun i j => (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.k_int_k d hk v i j).1) (fun i j => (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.k_int_k d hk v i j).2) h1' h2' lam
  rw [det_map, det_map] at key
  exact key
theorem absE_split_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : (AE F E)ˣ) :
    ((GlobalTheory.Doubling.absE F E x : ℝ≥0) : ℝ) =
      (∏ w, ‖piInf (d.B.emb w) x.1‖ ^ 2) * ∏ᶠ v, ‖Algebra.norm (v.adicCompletion F) (compFin F E v x.1)‖ := by
  rw [GlobalTheory.Doubling.absE_apply, NNReal.coe_mul, NNReal.coe_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [GlobalTheory.Doubling.absEw_eq_sq d.ok.good.cm (d.B.emb w), NNReal.coe_pow, coe_nnnorm]
    rfl
  · set s := (GlobalTheory.Doubling.finite_mulSupport_absEv x).toFinset with hs
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := s) (by simp [s]), NNReal.coe_prod,
      finprod_eq_prod_of_mulSupport_subset _ (s := s) ?_]
    · exact Finset.prod_congr rfl fun v _ => (normV_eq x v).symm
    · intro v hv
      simp only [Set.Finite.coe_toFinset, s, Function.mem_mulSupport] at hv ⊢
      rw [normV_eq] at hv
      exact fun h => hv (by rw [h, NNReal.coe_one])
theorem heightDict_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.HeightDict_k := by
  intro F E _ _ _ _ _ σ d R x t u T η T₀ hOf θ fr g hR nb lam 𝓖 hc ε w hw
  choose lv hlv using fun v : HeightOneSpectrum (𝓞 F) => exists_haar_tup (E := E) v d.n
  obtain ⟨hCO, hstd⟩ := _root_.PositivityTheory.SiegelWeilFormula.HeightDict.fin_std_k (σ := σ) d d.n t u η hR.ne
  have hat : (0 : ℝ) < ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det t) : ℝ≥0) : ℝ) :=
    absE_pos _
  refine ⟨lv, L1 σ t, L2 σ u η, ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det t) : ℝ≥0) : ℝ)⁻¹,
    inv_pos.2 hat, hlv, hCO, hstd, fun β => ?_⟩
  obtain ⟨D, k, hk, ha, hb1, hb2⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.frame_iwa_k d (w * nb β * x)
  obtain ⟨hr1, hr2⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.bottom_rows_k d x t u hR.levi nb hc.1 ε w hw β
  have h1 := hr1.symm.trans hb1
  have h2 := hr2.symm.trans hb2
  have hre := fun w' => _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.real_at_k d R hR ε β D hk h1 h2 w'
  have hfi := fun v => _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.fin_at_k d R hR ε β D hk h1 h2 v (lv v)
  set X : InfinitePlace F → ℝ := fun w' => (1 + (((g w')⁻¹).1 * (Gen.matInf (hOf β).1).map (θ w') * (((g w')⁻¹).1)ᴴ) *
        (((g w')⁻¹).1 * (Gen.matInf (hOf β).1).map (θ w') * (((g w')⁻¹).1)ᴴ)).det.re with hX
  set N : HeightOneSpectrum (𝓞 F) → ℝ := fun v => Gen.nu2 (lv v) (L1 σ t v) (L2 σ u η v) (Gen.matV v (hOf β).1)
    with hN
  have hnuA : Gen.nuA θ g lv (L1 σ t) (L2 σ u η) (hOf β).1 = (∏ w', X w') * ∏ᶠ v, N v := rfl
  have hsD := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.absE_split_k d (Matrix.GeneralLinearGroup.det D)
  have hsT := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.absE_split_k d (Matrix.GeneralLinearGroup.det t)
  simp only [Matrix.GeneralLinearGroup.val_det_apply] at hsD hsT
  have hfT := fin_supp (Matrix.GeneralLinearGroup.det t)
  have hfD := fin_supp (Matrix.GeneralLinearGroup.det D)
  simp only [Matrix.GeneralLinearGroup.val_det_apply] at hfT hfD
  have hT0 := normV_ne (Matrix.GeneralLinearGroup.det t)
  simp only [Matrix.GeneralLinearGroup.val_det_apply] at hT0
  have hNv : ∀ v, N v = ‖Algebra.norm (v.adicCompletion F) (compFin F E v D.1.det)‖ /
      ‖Algebra.norm (v.adicCompletion F) (compFin F E v t.1.det)‖ := fun v => by
    rw [hfi v, mul_div_cancel_left₀ _ (hT0 v)]
  have hNs : (Function.mulSupport N).Finite := by
    refine (hfD.union hfT).subset fun v hv => ?_
    by_contra hc'
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hc'
    exact hv (by rw [hNv v, hc'.1, hc'.2, div_one])
  have hA : ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det D) : ℝ≥0) : ℝ) =
      ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det t) : ℝ≥0) : ℝ) *
        Gen.nuA θ g lv (L1 σ t) (L2 σ u η) (hOf β).1 := by
    rw [hsD, hsT, hnuA, Finset.prod_congr rfl fun w' _ => hre w', Finset.prod_mul_distrib,
      finprod_congr fun v => hfi v, finprod_mul_distrib hfT hNs]
    ring
  have hDpos := absE_pos (Matrix.GeneralLinearGroup.det D)
  refine ⟨?_, ?_⟩
  · rw [hA] at hDpos
    exact pos_of_mul_pos_right hDpos hat.le
  · rw [ha, hA, mul_inv]
end PositivityTheory.SiegelWeilFormula.KWhit.Ht
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilOswgenFockOf
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP.OswGen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem crd_inf_eq_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
    (L : (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ))
    (hL : ∀ (c : Fin d.m × Fin d.n × Fin 2 → AF F) (w : InfinitePlace F),
      L (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c k).1) w = R.loc w (d.cmb c)) (X : Mx F E d.m d.n) :
    (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd X k).1) =
      L.symm (((EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).trans (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.zLE_k d).toContinuousLinearEquiv) (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X)) := by
  apply L.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  funext w
  rw [hL, _root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_crd_k]
  exact (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_eq_iff_k R X (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X)).1 rfl w
theorem mem_fock_of_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)} (hνf : νf.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) (H : ∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∃ P : MvPolynomial (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℂ,
      ∀ u, _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf f g u = MvPolynomial.eval (fun i => ((u i : ℝ) : ℂ)) P * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2))) :
    f ∈ R.fock := by
  obtain ⟨L, hL⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.archEquiv_k d R
  set Zc : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) :=
    (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).trans (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.zLE_k d).toContinuousLinearEquiv with hZc
  have hΦ : f ∘ d.cmb ∈ Submodule.span ℂ {Φ | ∃ (φ : SchwartzMap (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) ℂ)
      (g : (Fin d.m × Fin d.n × Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ),
      g ∈ SB (Fin d.m × Fin d.n × Fin 2 → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F φ g} := hf
  obtain ⟨N, a, x, hx⟩ := Submodule.mem_span_set'.1 hΦ
  choose φ gg hgg hxeq using fun i => (x i).2
  have hfX : ∀ X, f X = ∑ i, a i * (φ i (L.symm (Zc (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X))) * gg i (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) := by
    intro X
    have e1 : f X = (f ∘ d.cmb) (d.crd X) := by simp [_root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_crd_k]
    rw [e1, ← hx, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, hxeq i, smul_eq_mul]
    congr 1
    simp only [pureA]
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.crd_inf_eq_k R L hL X]
    rfl
  have hfjn : ∀ u y, f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y) = ∑ i, a i * (φ i (L.symm (Zc u)) * gg i y) := by
    intro u y
    rw [hfX, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_jn_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_jn_k]
  let Φv : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → (Fin N → ℂ) := fun y i => gg i y
  have hloc : IsLocallyConstant Φv := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun y => ?_
    have h := Filter.eventually_all.2 fun i => (IsLocallyConstant.iff_eventually_eq _).1 (hgg i).1 y
    filter_upwards [h] with z hz
    funext i
    exact hz i
  set K : Set (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := ⋃ i, tsupport (gg i) with hK
  have hKc : IsCompact K := isCompact_iUnion fun i => (hgg i).2
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun c : Fin N → ℂ => {y | Φv y = c}) (fun c => hloc.isOpen_fiber c)
    (fun y _ => Set.mem_iUnion.2 ⟨Φv y, rfl⟩)
  set Vals := t.filter (fun c => c ≠ 0) with hVals
  have hfib_sub : ∀ c : Fin N → ℂ, c ≠ 0 → {y | Φv y = c} ⊆ K := by
    intro c hc y hy
    by_contra hyK
    apply hc
    rw [← show Φv y = c from hy]
    funext i
    show gg i y = 0
    exact image_eq_zero_of_notMem_tsupport (f := gg i) fun h => hyK (Set.mem_iUnion.2 ⟨i, h⟩)
  haveI := hνf
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : BorelSpace (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := Pi.borelSpace
  let ψ : (Fin N → ℂ) → _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → ℂ := fun c u => ∑ i, a i * (φ i (L.symm (Zc u)) * c i)
  have hterm : ∀ c ∈ Vals, (fun X => ψ c (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * {y | Φv y = c}.indicator (fun _ => (1 : ℂ)) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) ∈ R.fock := by
    intro c hc
    have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
    set Nc : Set (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := {y | Φv y = c} with hNc
    have hNo : IsOpen Nc := hloc.isOpen_fiber c
    have hNcl : IsClosed Nc := hloc.isClosed_fiber c
    have hNk : IsCompact Nc := hKc.of_isClosed_subset hNcl (hfib_sub c hc0)
    rcases Nc.eq_empty_or_nonempty with he | hne
    · have : (fun X => ψ c (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * Nc.indicator (fun _ => (1 : ℂ)) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) = 0 := by
        funext X
        rw [he, Set.indicator_empty, mul_zero]
        rfl
      rw [this]
      exact Submodule.zero_mem _
    · have hSB := indicator_mem_SB hNo hNcl hNk
      obtain ⟨P, hP⟩ := H _ hSB
      have hm0 : 0 < νf.real Nc := by
        rw [measureReal_def]
        exact ENNReal.toReal_pos (hNo.measure_pos νf hne).ne' hNk.measure_lt_top.ne
      have hval : ∀ u, _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf f (Nc.indicator fun _ => (1 : ℂ)) u = ψ c u * (νf.real Nc : ℂ) := by
        intro u
        have e : (fun y => f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y) * star (Nc.indicator (fun _ => (1 : ℂ)) y)) =
            Nc.indicator (fun _ => ψ c u) := by
          funext y
          by_cases hy : y ∈ Nc
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, star_one, mul_one, hfjn]
            have hy' : ∀ i, gg i y = c i := fun i => congrFun hy i
            simp only [ψ, hy']
          · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, star_zero, mul_zero]
        show ∫ y, f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y) * star (Nc.indicator (fun _ => (1 : ℂ)) y) ∂νf = _
        rw [e, integral_indicator_const _ hNo.measurableSet, Complex.real_smul, mul_comm]
      have hψ : ∀ u, ψ c u = ((νf.real Nc)⁻¹ : ℂ) *
          (MvPolynomial.eval (fun i => ((u i : ℝ) : ℂ)) P * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2))) := by
        intro u
        rw [← hP u, hval u]
        have : (νf.real Nc : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hm0.ne'
        field_simp
      have e2 : (fun X => ψ c (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * Nc.indicator (fun _ => (1 : ℂ)) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) =
          ((νf.real Nc)⁻¹ : ℂ) • (fun X => MvPolynomial.eval (fun i => ((_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X i : ℝ) : ℂ)) P *
            (Real.exp (-(2 * Real.pi * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2)) : ℂ) * Nc.indicator (fun _ => (1 : ℂ)) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) := by
        funext X
        simp only [Pi.smul_apply, smul_eq_mul, hψ]
        ring
      rw [e2]
      exact Submodule.smul_mem _ _ (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.poly_mem_k R P hSB)
  have hsum : f = ∑ c ∈ Vals, (fun X => ψ c (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * {y | Φv y = c}.indicator (fun _ => (1 : ℂ)) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) := by
    funext X
    rw [Finset.sum_apply, hfX]
    by_cases h0 : Φv (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X) = 0
    · have hz : ∀ i, gg i (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X) = 0 := fun i => congrFun h0 i
      simp only [hz, mul_zero, Finset.sum_const_zero]
      refine (Finset.sum_eq_zero fun c hc => ?_).symm
      have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
      have : _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X ∉ {y | Φv y = c} := fun h => hc0 (h.symm.trans h0)
      rw [Set.indicator_of_notMem this, mul_zero]
    · have hmemK : _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X ∈ K := hfib_sub _ h0 rfl
      have hmemt : Φv (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X) ∈ t := by
        have := ht hmemK
        simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
        obtain ⟨c, hct, hc⟩ := this
        rw [hc]
        exact hct
      have hmemV : Φv (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X) ∈ Vals := Finset.mem_filter.2 ⟨hmemt, h0⟩
      rw [Finset.sum_eq_single_of_mem _ hmemV]
      · rw [Set.indicator_of_mem (show _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X ∈ {y | Φv y = Φv (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)} from rfl), mul_one]
      · intro c _ hne
        have : _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X ∉ {y | Φv y = c} := fun h => hne h.symm
        rw [Set.indicator_of_notMem this, mul_zero]
  rw [hsum]
  exact Submodule.sum_mem _ hterm
end PositivityTheory.SiegelWeilFormula.KFP.OswGen
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTautoAuto
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Tauto
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem thetaAuto_at_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) :
    d.μ d.D ≠ 0 ∧ d.μ d.D ≠ ⊤ ∧ ∀ Φ ∈ d.sch,
      (∀ x, IntegrableOn (fun g => thetaSum F (d.om x (d.S g Φ))) d.D d.μ) ∧ Continuous (d.I Φ) ∧
      ∀ γ ∈ rat2 σ d.Y, ∀ x, d.I Φ (γ * x) = d.I Φ x := by
  have hc := _root_.PositivityTheory.SiegelWeilFormula.Tauto.cpt_k hS d
  haveI := hc.cnt
  haveI := d.ok.haar
  have hom : ∀ x, ∀ Ψ ∈ d.sch, d.om x Ψ ∈ d.sch := fun x Ψ hΨ => d.ok.dbl.weil.2.1.pres x Ψ hΨ
  have hcomm : ∀ Φ ∈ d.sch, ∀ x g, d.om x (d.S g Φ) = d.S g (d.om x Φ) := fun Φ hΦ => (hT F E σ d Φ hΦ).2
  obtain ⟨Λ, hΛ, hΛv⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.exists_meanAdm_k hS hP hT d
  refine ⟨fd_ne d.ok.dom, (hc.fin d.μ d.D d.ok.haar d.ok.dom).ne, fun Φ hΦ => ⟨fun x => ?_, ?_, fun γ hγ x => ?_⟩⟩
  · simp only [hcomm Φ hΦ]
    exact _root_.PositivityTheory.SiegelWeilFormula.Tauto.intOn_S_k hS hP hT d (hom x Φ hΦ)
  · have e : d.I Φ = fun x => Λ (d.om x Φ) := funext fun x => by
      rw [hΛv _ (hom x Φ hΦ)]
      show PositivityTheory.SiegelWeilFormula.thetaMean d.om d.S d.μ d.D Φ x = _
      rw [PositivityTheory.SiegelWeilFormula.thetaMean, setAverage_eq]
      simp only [hcomm Φ hΦ]
    rw [e]
    exact d.ok.dbl.weil.2.1.cont Λ hΛ Φ hΦ
  · show PositivityTheory.SiegelWeilFormula.thetaMean d.om d.S d.μ d.D Φ (γ * x) = PositivityTheory.SiegelWeilFormula.thetaMean d.om d.S d.μ d.D Φ x
    simp only [PositivityTheory.SiegelWeilFormula.thetaMean, map_mul, Module.End.mul_apply]
    refine congrArg (fun f : UA σ d.A.J → ℂ => ⨍ g in d.D, f g ∂d.μ) (funext fun g => ?_)
    exact _root_.PositivityTheory.SiegelWeilFormula.Tauto.thetaSum_rational_invariant d γ hγ _ (hom x _ (d.ok.dbl.lin.pres g Φ hΦ))
theorem thetaAuto_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) : _root_.PositivityTheory.SiegelWeilFormula.ThetaAuto_k :=
  fun _ _ _ _ _ _ _ _ d => _root_.PositivityTheory.SiegelWeilFormula.Tauto.thetaAuto_at_k hS hP hT d
end PositivityTheory.SiegelWeilFormula.Tauto
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTweylComm
section
set_option synthInstance.maxHeartbeats 200000

section
set_option linter.unusedSectionVars false
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.tweyl
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem actB_conj_k (x : d.G) (g : UA σ d.A.J) (v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    actB (cA σ) x⁻¹ (mat g * actB (cA σ) x (mat g⁻¹ * v)) = v := by
  unfold actB
  have hx : (x.1.1)ᵀ * ((x⁻¹ : d.G).1.1)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    simp
  calc _ = (mat g * mat g⁻¹) * v * ((x.1.1)ᵀ * ((x⁻¹ : d.G).1.1)ᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = v := by rw [_root_.PositivityTheory.SiegelWeilFormula.tweyl.mat_mul_inv_k, hx, Matrix.one_mul, Matrix.mul_one]
theorem comm_schr_k (g : UA σ d.A.J) (x : d.G) : ∀ w, ∀ φ ∈ schA F d.κ,
    (d.om x⁻¹ * d.S g * d.om x * d.S g⁻¹) (schr d.B.ψ w φ) =
      schr d.B.ψ w ((d.om x⁻¹ * d.S g * d.om x * d.S g⁻¹) φ) := by
  intro w φ hφ
  obtain ⟨v, rfl⟩ := d.dd.e.surjective w
  have e1 : ∀ u, schr d.B.ψ (d.dd.e u) = d.dd.rho d.B.ψ u := fun u => rfl
  simp only [Module.End.mul_apply, e1]
  have h1 := (_root_.PositivityTheory.SiegelWeilFormula.tweyl.hS_k d).impl g⁻¹ v φ hφ
  have hp1 := (_root_.PositivityTheory.SiegelWeilFormula.tweyl.hS_k d).pres g⁻¹ φ hφ
  have h2 := (_root_.PositivityTheory.SiegelWeilFormula.tweyl.hO_k d).impl x (mat g⁻¹ * v) _ hp1
  have hp2 := (_root_.PositivityTheory.SiegelWeilFormula.tweyl.hO_k d).pres x _ hp1
  have h3 := (_root_.PositivityTheory.SiegelWeilFormula.tweyl.hS_k d).impl g (actB (cA σ) x (mat g⁻¹ * v)) _ hp2
  have hp3 := (_root_.PositivityTheory.SiegelWeilFormula.tweyl.hS_k d).pres g _ hp2
  have h4 := (_root_.PositivityTheory.SiegelWeilFormula.tweyl.hO_k d).impl x⁻¹ (mat g * actB (cA σ) x (mat g⁻¹ * v)) _ hp3
  beta_reduce at h1 h3
  rw [h1, h2, h3, h4, _root_.PositivityTheory.SiegelWeilFormula.tweyl.actB_conj_k]
theorem exists_scalar_k (g : UA σ d.A.J) (x : d.G) :
    ∃ c : ℂ, ∀ φ ∈ schA F d.κ, (d.S g * d.om x * d.S g⁻¹) φ = c • d.om x φ := by
  obtain ⟨c, hc⟩ := GlobalTheory.WeilSchUnique.scalar_of_commute d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.tweyl.std_k d) (d.om x⁻¹ * d.S g * d.om x * d.S g⁻¹)
    (fun l hl => by
      simp only [Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
      exact (_root_.PositivityTheory.SiegelWeilFormula.tweyl.hS_k d).adm _ _ ((_root_.PositivityTheory.SiegelWeilFormula.tweyl.hO_k d).adm _ _ ((_root_.PositivityTheory.SiegelWeilFormula.tweyl.hS_k d).adm _ _ ((_root_.PositivityTheory.SiegelWeilFormula.tweyl.hO_k d).adm _ _ hl))))
    (_root_.PositivityTheory.SiegelWeilFormula.tweyl.comm_schr_k d g x)
  refine ⟨c, fun φ hφ => ?_⟩
  have h := congrArg (d.om x) (hc φ hφ)
  rw [map_smul] at h
  rw [← h]
  simp only [Module.End.mul_apply]
  rw [← Module.End.mul_apply (d.om x) (d.om x⁻¹), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
end PositivityTheory.SiegelWeilFormula.tweyl
end
end
end

