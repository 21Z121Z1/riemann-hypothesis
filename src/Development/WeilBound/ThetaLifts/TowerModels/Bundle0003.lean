import Development.WeilBound.ThetaLifts.TowerModels.Bundle0002
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.PlaneRemovalConfiguration
import Development.WeilBound.ThetaLifts.TowerModels.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.DetHerm
section
noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem det_ne_zero_of_hasSig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  subst hrs
  intro hM
  have key := congrArg Matrix.det hA
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one,
    Fintype.card_fin] at key
  let e : Fin r ⊕ Fin s ≃ Fin (r + s) := finSumFinEquiv
  have hsub : (Aᵀ * M * A.map star).submatrix e.symm e.symm =
      (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star := by
    ext i j
    simp [Matrix.mul_apply, Matrix.submatrix, Matrix.transpose_apply]
  have h2 := congrArg Matrix.det hsub
  rw [Matrix.det_submatrix_equiv_self, key, Matrix.det_mul, Matrix.det_mul, hM, mul_zero, zero_mul] at h2
  exact pow_ne_zero _ (by norm_num) h2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}

theorem det_herm {n : ℕ} {X : Spc F E n} {r s : ℕ} (hX : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := det_ne_zero_of_hasSig (hX.sig w)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  exact fun h0 => h (by rw [h0, map_zero])

theorem det_skew {n : ℕ} {X : Spc F E n} {r s : ℕ} (hX : X.IsSkew σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := det_ne_zero_of_hasSig (hX.sig w)
  rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  exact fun h0 => h (by rw [h0, map_zero, mul_zero])

end PositivityTheory.ThKG.Tow

end
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.LeviAd
section
noncomputable section

namespace PositivityTheory.ThKG.Tow.Levi

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open Classical in

def sgI (w : InfinitePlace F) : w.Completion →ₗ[F] AF F :=
  (LinearMap.inl F (Ainf F) (Af F)).comp (LinearMap.single F (fun u : InfinitePlace F => u.Completion) w)

omit [NumberField E] in
theorem compInf_sgI_self (w : InfinitePlace F) (y : w.Completion ⊗[F] E) :
    compInf F E w (TensorProduct.map (sgI w) LinearMap.id y) = y := by
  classical
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => exact congrArg (· ⊗ₜ[F] x) (Pi.single_eq_same (M := fun u : InfinitePlace F => u.Completion) w a)
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField E] in
theorem compInf_sgI_ne {w u : InfinitePlace F} (h : u ≠ w) (y : w.Completion ⊗[F] E) :
    compInf F E u (TensorProduct.map (sgI w) LinearMap.id y) = 0 := by
  classical
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    exact (congrArg (· ⊗ₜ[F] x) (Pi.single_eq_of_ne (M := fun u : InfinitePlace F => u.Completion) h a)).trans
      (TensorProduct.zero_tmul _ _)
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

omit [NumberField E] in
theorem compFin_sgI (w : InfinitePlace F) (v : Pl F) (y : w.Completion ⊗[F] E) :
    compFin F E v (TensorProduct.map (sgI w) LinearMap.id y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    exact (congrArg (· ⊗ₜ[F] x) (map_zero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v))).trans (TensorProduct.zero_tmul _ _)
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

theorem exists_inf (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : InfinitePlace F → ℂ) :
    ∃ a : AE F E, (∀ w, piInf (τ w) a = z w) ∧ ∀ v, compFin F E v a = 1 := by
  choose b hb using fun w => (infEmb_bijective h (τ w)).2 (z w - 1)
  refine ⟨1 + ∑ w, TensorProduct.map (sgI w) LinearMap.id (b w), fun w => ?_, fun v => ?_⟩
  · rw [map_add, map_one, piInf, RingHom.comp_apply, map_sum, Finset.sum_eq_single w (fun u _ hu => compInf_sgI_ne hu.symm _)
      (fun h => absurd (Finset.mem_univ w) h), compInf_sgI_self, hb, add_sub_cancel]
  · simp [map_sum, compFin_sgI]

theorem ad_ext (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {a b : AE F E}
    (h1 : ∀ w, piInf (τ w) a = piInf (τ w) b) (h2 : ∀ v, compFin F E v a = compFin F E v b) : a = b :=
  Supp.adTens_ext (fun w => (infEmb_bijective h (τ w)).1 (h1 w)) h2

theorem mat_ext (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {m n : Type} {a b : Matrix m n (AE F E)}
    (h1 : ∀ w, a.map (piInf (τ w)) = b.map (piInf (τ w))) (h2 : ∀ v, a.map (compFin F E v) = b.map (compFin F E v)) : a = b :=
  Matrix.ext fun i j => ad_ext h τ (fun w => congrFun (congrFun (h1 w) i) j) fun v => congrFun (congrFun (h2 v) i) j

theorem exists_inf_mat (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {n : Type} [DecidableEq n]
    (z : InfinitePlace F → Matrix n n ℂ) :
    ∃ a : Matrix n n (AE F E), (∀ w, a.map (piInf (τ w)) = z w) ∧ ∀ v, a.map (compFin F E v) = 1 := by
  choose a h1 h2 using fun i j => exists_inf h τ fun w => z w i j + 1 - (1 : Matrix n n ℂ) i j
  refine ⟨Matrix.of fun i j => a i j - 1 + (1 : Matrix n n (AE F E)) i j, fun w => ?_, fun v => ?_⟩
  · ext i j
    by_cases e : i = j <;> simp [h1, Matrix.one_apply, e]
  · refine Matrix.ext fun i j => ?_
    by_cases e : i = j <;> simp [h2, Matrix.one_apply, e]

omit [NumberField E] in
theorem piInf_incl {w : InfinitePlace F} (τ : EmbOver E w) (x : E) : piInf τ (inclR (F := F) (AF F) x) = τ.1 x := by
  simp [piInf, compInf, inclR, infEmb_tmul]

omit [NumberField E] in
theorem compFin_cA (v : Pl F) (z : AE F E) : compFin F E v (cA σ z) = sigR _ σ (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  refine Eq.trans (congrArg (infEmb τ) ?_) (infEmb_sigR h τ _).symm
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sig_sig (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

theorem cA_cA (h : IsCMExt F E σ) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sig_sig h x)
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField E] in
theorem iso_map_piInf (hc : ∀ {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E), piInf τ (cA σ z) = star (piInf τ z))
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (AE F E)) {w : InfinitePlace F} (τ : EmbOver E w) :
    (gᵀ * incM F J * g.map (cA σ)).map (piInf τ) = (g.map (piInf τ))ᵀ * J.map τ.1 * (g.map (piInf τ)).map star := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 1
  · congr 1
    exact Matrix.ext fun i j => piInf_incl τ _
  · exact Matrix.ext fun i j => hc τ _

omit [NumberField E] in
theorem exists_UA {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g g' : Matrix (Fin n) (Fin n) (AE F E)} (h1 : g * g' = 1)
    (h2 : gᵀ * incM F J * g.map (cA σ) = incM F J) : ∃ p : UA σ J, mat p = g :=
  ⟨⟨⟨g, g', h1, mul_eq_one_comm.1 h1⟩, h2⟩, rfl⟩

theorem exists_lift (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (g g' : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) (h1 : ∀ w, g w * g' w = 1)
    (h2 : ∀ w, (g w)ᵀ * J.map (τ w).1 * (g w).map star = J.map (τ w).1) :
    ∃ p : UA σ J, (∀ w, (mat p).map (piInf (τ w)) = g w) ∧ ∀ v, (mat p).map (compFin F E v) = 1 := by
  obtain ⟨a, a1, a2⟩ := exists_inf_mat h τ g
  obtain ⟨b, b1, b2⟩ := exists_inf_mat h τ g'
  obtain ⟨p, hp⟩ := exists_UA (σ := σ) (J := J) (g := a) (g' := b)
    (mat_ext h τ (fun w => by rw [Matrix.map_mul, a1, b1, h1, Matrix.map_one _ (map_zero _) (map_one _)])
      fun v => by rw [Matrix.map_mul, a2, b2, mul_one, Matrix.map_one _ (map_zero _) (map_one _)])
    (mat_ext h τ (fun w => by
        rw [iso_map_piInf (fun τ z => piInf_cA h τ z), a1, h2]
        exact Matrix.ext fun i j => (piInf_incl _ _).symm)
      fun v => by
        have e : (a.map (cA σ)).map (compFin F E v) = (a.map (compFin F E v)).map (sigR _ σ) :=
          Matrix.ext fun i j => compFin_cA v _
        rw [Matrix.map_mul, Matrix.map_mul, e, Matrix.transpose_map, a2, Matrix.map_one _ (map_zero _) (map_one _),
          Matrix.transpose_one, one_mul, mul_one])
  exact ⟨p, hp ▸ a1, hp ▸ a2⟩

variable {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁} {i₀ i₁ r s : ℕ}

theorem det_ne_zero (hW : W.IsSkew σ B r s) : W.J.det ≠ 0 := by
  obtain ⟨u⟩ : Nonempty (InfinitePlace F) := inferInstance
  intro h0
  have hm : (Complex.I • W.J.map (B.emb u).1).det = 0 := by
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]
  obtain ⟨x, hx, e⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hm
  have := (hW.cartan u).2.2 (star x) (by simpa using hx)
  rw [star_star, e, dotProduct_zero] at this
  exact lt_irrefl _ this

omit [NumberField F] [NumberField E] in
theorem form_skew (hs : ∀ x, σ (σ x) = x) {J : Matrix (Fin d) (Fin d) E} (hJ : ∀ i j, σ (J j i) = -J i j) (x y : Fin d → E) :
    form σ J x y = -σ (form σ J y x) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, hs, hJ, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem isFr (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) (hH : H.IsAdapted σ B W W₁ i₀ i₁) :
    IsFr (σ : E →+* E) W.J W₁.J H.ι H.x H.y := by
  have hsk := form_skew (sig_sig hB.cm) hW.skew
  have ent : ∀ a b, ((fr H.ι H.x H.y)ᵀ * W.J * (fr H.ι H.x H.y).map (σ : E →+* E)) a b =
      form σ W.J (fun i => fr H.ι H.x H.y i a) (fun i => fr H.ι H.x H.y i b) := fun a b => by
    rw [Matrix.mul_assoc]; rfl
  have col : ∀ j, (fun i => fr H.ι H.x H.y i (Sum.inl j)) = H.ι *ᵥ Pi.single j 1 := fun j => by
    ext i; simp [fr]
  have c0 : (fun i => fr H.ι H.x H.y i (Sum.inr 0)) = H.x := rfl
  have c1 : (fun i => fr H.ι H.x H.y i (Sum.inr 1)) = H.y := rfl
  refine ⟨?_, ?_⟩
  · ext (a | a) (b | b)
    · exact congrFun (congrFun hH.gram a) b
    · rw [ent, col]
      fin_cases b
      exacts [(hH.orth _).1, (hH.orth _).2]
    · rw [ent, col, hsk]
      fin_cases a
      · exact (congrArg (fun z => -σ z) (hH.orth _).1).trans (by simp [gr])
      · exact (congrArg (fun z => -σ z) (hH.orth _).2).trans (by simp [gr])
    · rw [ent]
      fin_cases a <;> fin_cases b
      exacts [hH.xx, hH.xy, (hsk _ _).trans ((congrArg (fun z => -σ z) hH.xy).trans (by simp [gr])), hH.yy]
  · have hs : ∀ z : Fin d → E, z ∈ LinearMap.range (Matrix.toLin' (fr H.ι H.x H.y)) := fun z => by
      have hz : z ∈ Submodule.span E (W.L : Set (Fin d → E)) := by rw [hW.lat.span_eq_top]; trivial
      refine (Submodule.span_le.2 fun z hz => ?_) hz
      obtain ⟨s, t, u, -, -, -, rfl⟩ := hH.split z hz
      refine ⟨Sum.elim u ![s, t], ?_⟩
      rw [Matrix.toLin'_apply, fr, Matrix.fromCols_mulVec_sumElim]
      ext i
      simp [Matrix.mulVec, dotProduct]
      ring
    choose f hf using fun j => hs (Pi.single j 1)
    have h1 : fr H.ι H.x H.y * (Matrix.of fun a j => f j a) = 1 := by
      ext i j
      rw [Matrix.one_apply, ← Pi.single_apply, ← hf j]; rfl
    exact ⟨_, h1, (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hH.rank])).1 h1⟩

theorem isFrA (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) (hH : H.IsAdapted σ B W W₁ i₀ i₁) :
    IsFr (cA σ : AE F E →+* AE F E) (incM F W.J) (incM F W₁.J) (incM F H.ι) (incV F H.x) (incV F H.y) :=
  (isFr hB hW hH).map (inclR (F := F) (AF F)) fun _ => rfl

theorem exists_levi (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) (hH : H.IsAdapted σ B W W₁ i₀ i₁) (t : (AE F E)ˣ)
    (h₁ : UA σ W₁.J) : ∃ m : UA σ W.J, IsLevi H t h₁ m := by
  obtain ⟨m, m', e1, e2, e3, e4, e5⟩ := (isFrA hB hW hH).levi (cA_cA hB.cm) t.mul_inv h₁.1.mul_inv h₁.2
  obtain ⟨p, rfl⟩ := exists_UA e1 e2
  exact ⟨p, e3, e4, e5⟩

end PositivityTheory.ThKG.Tow.Levi

end
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.PlaneBas
section
noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {v : Pl F} (τ : E →ₐ[F] Fv F v)

theorem map_mem_splitLat {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} {z : Fin n → E} (hz : z ∈ L) :
    (fun i => τ (z i)) ∈ splitLat τ L :=
  ⟨fun i => (1 : Fv F v) ⊗ₜ[F] z i, AddSubgroup.subset_closure ⟨1, one_mem _, z, hz, rfl⟩,
    funext fun i => by simp [splitVec, splitProj_tmul]⟩

theorem splitLat_le {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)}
    (N : Submodule (v.adicCompletionIntegers F) (Fin n → Fv F v)) (hN : ∀ z ∈ L, (fun i => τ (z i)) ∈ N) :
    splitLat τ L ≤ N := by
  rintro _ ⟨y, hy, rfl⟩
  refine latLoc_induction (p := fun y => splitVec τ y ∈ N) (fun a ha x hx => ?_) ?_ (fun y z hy hz => ?_)
    (fun y hy => ?_) hy
  · have := N.smul_mem ⟨a, ha⟩ (hN x hx)
    convert this using 1
    funext i
    simp only [splitVec, splitProj_tmul]
    rfl
  · have : splitVec τ (0 : Fin n → Fv F v ⊗[F] E) = 0 := funext fun _ => map_zero _
    rw [this]; exact zero_mem _
  · rw [splitVec_add]; exact add_mem hy hz
  · have : splitVec τ (-y) = -splitVec τ y := funext fun _ => map_neg _ _
    rw [this]; exact neg_mem hy

theorem map_mem_of_unit {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E} {c : E} (hc : c • x ∈ L)
    (hv : Valued.v (τ c) = 1) {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) :
    (a • fun i => τ (x i)) ∈ splitLat τ L := by
  have h0 : τ c ≠ 0 := fun e => by simp [e] at hv
  have h1 : a * (τ c)⁻¹ ∈ v.adicCompletionIntegers F :=
    mul_mem ha (by rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one])
  have := (splitLat τ L).smul_mem ⟨_, h1⟩ (map_mem_splitLat τ hc)
  convert this using 1
  funext i
  change a * τ (x i) = a * (τ c)⁻¹ * τ (c * x i)
  rw [map_mul]
  field_simp

theorem exists_basis (n n₁ : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E)
    (β₁ : GL (Fin n₁) (Fv F v)) (i₀ i₁ : ℕ) (hn : n = n₁ + 2) (h01 : i₀ < i₁) (h1n : i₁ < n) (hlat : L.IsLattice E)
    (hsplit : ∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y)
    (hx : (∀ c : E, c • x ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • x ∈ L ∧ Valued.v (τ c) = 1)
    (hy : (∀ c : E, c • y ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • y ∈ L ∧ Valued.v (τ c) = 1)
    (hβ₁ : IsSplitBasis τ (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))) β₁) :
    ∃ β : GL (Fin n) (Fv F v), (∀ i : Fin n, (i.1 = i₀ → ∀ r, β.1 r i = τ (x r)) ∧
      (i.1 = i₁ → ∀ r, β.1 r i = τ (y r)) ∧ ∀ j : Fin n₁, i.1 = skip i₀ i₁ j → ∀ r, β.1 r i = (ι.map τ * β₁.1) r j) ∧
      IsSplitBasis τ L β := by
  classical
  have hsk : ∀ j : Fin n₁, skip i₀ i₁ j < n := fun j => by
    have := j.2
    unfold skip; split_ifs <;> omega
  let f : Fin n₁ ⊕ Bool → Fin n := Sum.elim (fun j => ⟨skip i₀ i₁ j, hsk j⟩)
    fun b => cond b ⟨i₁, h1n⟩ ⟨i₀, h01.trans h1n⟩
  have hf : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp [hn]⟩
    rintro (a | _ | _) (b | _ | _) e <;>
      simp only [f, Sum.elim_inl, Sum.elim_inr, cond, Fin.mk.injEq, skip, Sum.inl.injEq, Fin.ext_iff] at e ⊢ <;>
      first | omega | (split_ifs at e <;> omega)
  let e := Equiv.ofBijective f hf
  let c : Fin n₁ ⊕ Bool → Fin n → Fv F v := Sum.elim (fun j r => (ι.map τ * β₁.1) r j)
    fun b => cond b (fun r => τ (y r)) fun r => τ (x r)
  let b : Matrix (Fin n) (Fin n) (Fv F v) := Matrix.of fun r i => c (e.symm i) r
  have hb : ∀ u : Fin n → Fv F v, b *ᵥ u = (u (e (.inr false)) • fun r => τ (x r)) +
      ι.map τ *ᵥ β₁.1 *ᵥ (fun j => u (e (.inl j))) + u (e (.inr true)) • fun r => τ (y r) := fun u => by
    funext r
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, b, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← e.sum_comp]
    simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Fintype.sum_bool, c, Sum.elim_inl, Sum.elim_inr, cond]
    ring
  have hmv : ∀ u : Fin n₁ → E, (fun i => τ ((ι *ᵥ u) i)) = ι.map τ *ᵥ fun j => τ (u j) := fun u =>
    funext fun i => RingHom.map_mulVec (τ : E →+* Fv F v) ι u i
  have hsurj : ∀ w ∈ splitLat τ L, ∃ u : Fin n → Fv F v, (∀ i, u i ∈ v.adicCompletionIntegers F) ∧ b *ᵥ u = w := by
    let N : Submodule (v.adicCompletionIntegers F) (Fin n → Fv F v) :=
      { carrier := {w | ∃ u : Fin n → Fv F v, (∀ i, u i ∈ v.adicCompletionIntegers F) ∧ b *ᵥ u = w}
        zero_mem' := ⟨0, fun _ => zero_mem _, Matrix.mulVec_zero _⟩
        add_mem' := by
          rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
          exact ⟨u + u', fun i => add_mem (hu i) (hu' i), Matrix.mulVec_add _ _ _⟩
        smul_mem' := by
          rintro a _ ⟨u, hu, rfl⟩
          exact ⟨(a : Fv F v) • u, fun i => mul_mem a.2 (hu i), Matrix.mulVec_smul _ _ _⟩ }
    refine fun w hw => splitLat_le τ N (fun z hz => ?_) hw
    obtain ⟨s, t, u, hs, ht, hu, rfl⟩ := hsplit z hz
    have hu' := hβ₁.mem_iff.1 (map_mem_splitLat τ (L := L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))) hu)
    refine ⟨fun i => Sum.elim ((β₁⁻¹).1 *ᵥ fun j => τ (u j)) (fun b => cond b (τ t) (τ s)) (e.symm i), fun i => ?_, ?_⟩
    · beta_reduce
      rcases e.symm i with j | _ | _
      · exact hu' j
      · exact hx.1 s hs
      · exact hy.1 t ht
    · rw [hb]
      simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, cond]
      rw [Matrix.mulVec_mulVec _ β₁.1, Units.mul_inv, Matrix.one_mulVec, ← hmv]
      funext r
      simp
  have hunit : IsUnit b := by
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    have h1 : ∀ z : Fin n → E, (fun i => τ (z i)) ∈ LinearMap.range b.mulVecLin := fun z => by
      have hz : z ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hlat.span_eq_top]; trivial
      induction hz using Submodule.span_induction with
      | mem z hz => obtain ⟨u, -, hu⟩ := hsurj _ (map_mem_splitLat τ hz); exact ⟨u, hu⟩
      | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
      | add a a' _ _ ha ha' => simp only [Pi.add_apply, map_add]; exact add_mem ha ha'
      | smul a z _ hz => simp only [Pi.smul_apply, smul_eq_mul, map_mul]; exact Submodule.smul_mem _ (τ a) hz
    intro w
    have : w = ∑ i, w i • fun k => τ ((Pi.single i 1 : Fin n → E) k) := by
      funext k
      simp [Pi.single_apply, apply_ite]
    rw [this]
    exact (Submodule.sum_mem (LinearMap.range b.mulVecLin) fun i _ => Submodule.smul_mem _ _ (h1 _))
  obtain ⟨β, hβ⟩ := hunit
  have col : ∀ k r, β.1 r (e k) = c k r := fun k r => by rw [hβ]; simp [b]
  refine ⟨β, fun i => ⟨fun hi r => ?_, fun hi r => ?_, fun j hi r => ?_⟩, fun u => ⟨fun hu => ?_, fun hu => ?_⟩⟩
  · rw [show i = e (.inr false) from Fin.ext hi, col]; rfl
  · rw [show i = e (.inr true) from Fin.ext hi, col]; rfl
  · rw [show i = e (.inl j) from Fin.ext hi, col]; rfl
  · rw [hβ, hb]
    obtain ⟨s, hs, hs'⟩ := hx.2
    obtain ⟨t, ht, ht'⟩ := hy.2
    refine add_mem (add_mem (map_mem_of_unit τ hs hs' (hu _)) ?_) (map_mem_of_unit τ ht ht' (hu _))
    refine splitLat_le τ ((splitLat τ L).comap ((ι.map τ).mulVecLin.restrictScalars (v.adicCompletionIntegers F)))
      (fun z hz => ?_) ((hβ₁ _).1 fun j => hu _)
    change ι.map τ *ᵥ (fun j => τ (z j)) ∈ splitLat τ L
    rw [← hmv]
    exact map_mem_splitLat τ hz
  · obtain ⟨u', hu', e'⟩ := hsurj _ hu
    rw [← hβ] at e'
    rw [← Matrix.mulVec_injective_iff_isUnit.2 β.isUnit e']
    exact hu'

end PositivityTheory.ThKG.Tow.Pln

end
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.PlaneComp
section
noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_compl (n n₁ : ℕ) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (hn : n = n₁ + 2)
    (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1) (hyx : form σ J y x ≠ 0) :
    ∃ (ι : Matrix (Fin n) (Fin n₁) E) (P : Matrix (Fin n₁) (Fin n) E), P * ι = 1 ∧
      (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) ∧
      ∀ z, form σ J z x = 0 → form σ J z y = 0 → ∃ u, z = ι *ᵥ u := by
  let f : (Fin n → E) →ₗ[E] E × E := (formL (σ := σ) J x).prod (formL (σ := σ) J y)
  have hf : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨a, b⟩
    refine ⟨(a / form σ J y x) • y + b • x, Prod.ext ?_ ?_⟩
    · change form σ J _ x = a
      rw [form_add_left, form_smul_left, form_smul_left, hxx, div_mul_cancel₀ _ hyx, mul_zero, add_zero]
    · change form σ J _ y = b
      rw [form_add_left, form_smul_left, form_smul_left, hyy, hxy, mul_zero, mul_one, zero_add]
  have hk : Module.finrank E (LinearMap.ker f) = n₁ := by
    have := f.finrank_range_add_finrank_ker
    rw [hf, finrank_top] at this
    simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    omega
  let b := Module.finBasisOfFinrankEq E (LinearMap.ker f) hk
  let g : (Fin n₁ → E) →ₗ[E] (Fin n → E) := (LinearMap.ker f).subtype ∘ₗ b.equivFun.symm.toLinearMap
  obtain ⟨p, hp⟩ := g.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2
    ((LinearMap.ker f).injective_subtype.comp b.equivFun.symm.injective))
  refine ⟨LinearMap.toMatrix' g, LinearMap.toMatrix' p, by rw [← LinearMap.toMatrix'_comp, hp, LinearMap.toMatrix'_id],
    fun u => ?_, fun z h1 h2 => ?_⟩
  · rw [LinearMap.toMatrix'_mulVec]
    have := (b.equivFun.symm u).2
    exact Prod.mk_eq_zero.1 this
  · refine ⟨b.equivFun ⟨z, Prod.mk_eq_zero.2 ⟨h1, h2⟩⟩, ?_⟩
    rw [LinearMap.toMatrix'_mulVec]
    change z = (b.equivFun.symm (b.equivFun _) : LinearMap.ker f)
    rw [LinearEquiv.symm_apply_apply]

theorem fg_comap {V W : Type} [AddCommGroup V] [Module (𝓞 E) V] [AddCommGroup W] [Module (𝓞 E) W]
    (f : V →ₗ[𝓞 E] W) (hf : Function.Injective f) (L : Submodule (𝓞 E) W) (hL : L.FG) : (L.comap f).FG :=
  Submodule.fg_of_fg_map_injective f hf (hL.of_le (Submodule.map_comap_le f L))

theorem isLattice_comap (n n₁ : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (ι : Matrix (Fin n) (Fin n₁) E)
    (P : Matrix (Fin n₁) (Fin n) E) (hP : P * ι = 1) (hL : L.IsLattice E) :
    (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))).IsLattice E where
  fg := fg_comap _ (fun u u' e => by
    have := congrArg (P *ᵥ ·) (show ι *ᵥ u = ι *ᵥ u' from e)
    simpa [Matrix.mulVec_mulVec, hP] using this) L hL.fg
  span_eq_top := by
    rw [eq_top_iff]
    intro u _
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E (L : Set (Fin n → E)) (ι *ᵥ u)
      (by rw [hL.span_eq_top]; trivial)
    rw [Submodule.span_eq] at ht
    have h0 : ((t : 𝓞 E) : E) ≠ 0 := by simpa using nonZeroDivisors.coe_ne_zero t
    have : u = ((t : 𝓞 E) : E)⁻¹ • (((t : 𝓞 E) : E) • u) := by rw [inv_smul_smul₀ h0]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    change ι *ᵥ (((t : 𝓞 E) : E) • u) ∈ L
    rw [Matrix.mulVec_smul]
    exact ht

theorem exists_ideal (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsLattice E) (x : Fin n → E) (hx : x ≠ 0) :
    ∃ 𝔟 : FractionalIdeal (𝓞 E)⁰ E, ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ L :=
  ⟨⟨L.comap ((LinearMap.toSpanSingleton E _ x).restrictScalars (𝓞 E)), FractionalIdeal.isFractional_of_fg
    (fg_comap _ (smul_left_injective E hx) L hL.fg)⟩, fun _ => Iff.rfl⟩

end PositivityTheory.ThKG.Tow.Pln

end
end

