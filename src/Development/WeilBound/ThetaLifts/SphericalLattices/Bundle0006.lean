import Development.WeilBound.ThetaLifts.SphericalLattices.Bundle0005
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091

-- bundled from Development.WeilBound.ThetaLifts.SphericalLattices.ExistsFrameLag
section
noncomputable section

namespace PositivityTheory.Sph.M2

open scoped Matrix
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
  PositivityTheory.ThK PositivityTheory.ThKH.Iwas GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

namespace Chart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m : ℕ}
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)}

theorem frame_mul {n : ℕ} {Λ : Submodule (𝓞 E) (Fin n → E)} {a κ : GL (Fin n) (w.adicCompletion E)} (ha : IsFrameAt w Λ a)
    (h1 : ∀ i j, κ.1 i j ∈ Ov E w) (h2 : ∀ i j, (κ⁻¹).1 i j ∈ Ov E w) : IsFrameAt w Λ (a * κ) := fun z => by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← ha]
  refine ⟨fun hz => mulVec_int h1 hz, fun hz i => ?_⟩
  have := mulVec_int h2 hz i
  rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

theorem free_loc (h : w.under (𝓞 F) = v) (hw : IsInertAt F E v w) {n : ℕ} {W : Spc F E n}
    {Cy : Matrix (Fin n) (Fin m) (AE F E)} (hL : IsLagAt σ W v Cy) (z : Fin m → w.adicCompletion E)
    (hz : Cy.map (piE h) *ᵥ z = 0) : z = 0 := by
  obtain ⟨t, ht, rfl⟩ := vec_surj h z
  have z0 : ∀ {k : ℕ}, piE h ∘ (0 : Fin k → AE F E) = 0 := funext fun _ => map_zero _
  rw [hL.free t ht (vec_inj hw h (at_sub (at_mulVec_right _ ht) at_zero) (by rw [piE_mulVec, hz, z0])), z0]

theorem exists_frame_lag (hσ : IsCMExt F E σ) (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c) {B : Base F E} {W : Spc F E (m + m)} {r s : ℕ}
    (hW : W.IsSkew σ B r s) {Cy : Matrix (Fin (m + m)) (Fin m) (AE F E)} (hL : IsLagAt σ W v Cy) :
    ∃ a : GL (Fin (m + m)) (w.adicCompletion E), IsFrameAt w W.L a ∧ ∃ l : w.adicCompletion E, l ≠ 0 ∧
      Iso c (W.J.map (algebraMap E _)) (l • antiJ _ (m + m)) a.1 ∧
      ∃ T : Matrix (Fin m) (Fin m) (w.adicCompletion E), IsUnit T.det ∧
        ((a⁻¹).1 * Cy.map (piE h)).submatrix (ee m) id = Matrix.fromRows T (0 : Matrix (Fin m) (Fin m) _) := by
  obtain ⟨ϖ, hU⟩ := exists_isUnramInv hσ hw hc
  obtain ⟨a, ha, l, hl, hg⟩ := exists_frame hσ hw h hc hW
  have hai : Iso c (W.J.map (algebraMap E _)) (l • antiJ _ (m + m)) a.1 := hg
  have hC : (Cy.map (piE h))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) * (Cy.map (piE h)).map c = 0 := by
    rw [← map_gram hc, hL.iso, Matrix.map_zero _ (map_zero _)]
  have hf := free_loc h hw hL
  generalize Cy.map (piE h) = C at hC hf ⊢
  obtain ⟨Z, rfl⟩ : ∃ Z, C = a.1 * Z := ⟨(a⁻¹).1 * C, by rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]⟩
  have hZ : Zᵀ * antiJ (w.adicCompletion E) (m + m) * Z.map c = 0 := by
    refine (smul_eq_zero_iff_right hl).1 ?_
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← hg, ← hC, Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  obtain ⟨k, k', hkk, hk, hi, hi', T, hT, eT⟩ := exists_move hU (Y := Z.submatrix (ee m) id) (fun z hz => hf z (by
      have : Z *ᵥ z = 0 := funext fun i => by
        obtain ⟨i, rfl⟩ := (ee m).surjective i
        exact congrFun hz i
      rw [← Matrix.mulVec_mulVec, this, Matrix.mulVec_zero])) (by
      rw [← antiJ_submatrix]
      change Zᵀ.submatrix id (ee m) * _ * (Z.map c).submatrix (ee m) id = _
      rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hZ]
      rfl)
  let κ : GL (Fin (m + m)) (w.adicCompletion E) :=
    ⟨k'.submatrix (ee m).symm (ee m).symm, k.submatrix (ee m).symm (ee m).symm,
      by rw [Matrix.submatrix_mul_equiv, mul_eq_one_comm.1 hkk, Matrix.submatrix_one_equiv],
      by rw [Matrix.submatrix_mul_equiv, hkk, Matrix.submatrix_one_equiv]⟩
  refine ⟨a * κ, frame_mul ha (fun i j => hi' _ _) (fun i j => hi _ _), l, hl, hai.mul ((iso_smul_iff hl _ _).2 ?_), T, hT, ?_⟩
  · have h1 := iso_submatrix (ee m).symm (hk.inv hkk)
    rwa [← antiJ_submatrix, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id] at h1
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (a⁻¹).1, Units.inv_mul, Matrix.one_mul, ← eT,
      ← Matrix.submatrix_mul_equiv _ _ _ (ee m)]
    rw [show (κ⁻¹).1 = k.submatrix (ee m).symm (ee m).symm from rfl, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]

def phi (h : w.under (𝓞 F) = v) (W : Spc F E (m + m)) (a : GL (Fin (m + m)) (w.adicCompletion E)) :
    UA σ W.J →* Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E) where
  toFun := fun g => ((a⁻¹).1 * (mat g).map (piE h) * a.1).submatrix (ee m) (ee m)
  map_one' := by
    rw [show mat (1 : UA σ W.J) = 1 from rfl, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Units.inv_mul,
      Matrix.submatrix_one_equiv]
  map_mul' := fun g g' => by
    rw [show mat (g * g') = mat g * mat g' from rfl, Matrix.submatrix_mul_equiv, Matrix.map_mul]
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]

variable {h : w.under (𝓞 F) = v} {W : Spc F E (m + m)} {a : GL (Fin (m + m)) (w.adicCompletion E)}
  {c : w.adicCompletion E →+* w.adicCompletion E} {l : w.adicCompletion E}

theorem phi_apply (g : UA σ W.J) : phi h W a g = ((a⁻¹).1 * (mat g).map (piE h) * a.1).submatrix (ee m) (ee m) := rfl

theorem phi_iso (hc : IsConjAt σ h c) (hl : l ≠ 0) (hai : Iso c (W.J.map (algebraMap E _)) (l • antiJ _ (m + m)) a.1)
    (g : UA σ W.J) : Iso c (Wm _ (Fin m)) (Wm _ (Fin m)) (phi h W a g) := by
  have h1 : Iso c (W.J.map (algebraMap E _)) (W.J.map (algebraMap E _)) ((mat g).map (piE h)) := by
    unfold Iso
    rw [← map_gram hc, show (mat g)ᵀ * incM F W.J * (mat g).map (cA σ) = incM F W.J from g.2]
    exact Matrix.ext fun i j => piE_incl h _
  rw [phi_apply, ← antiJ_submatrix]
  exact iso_submatrix _ ((iso_smul_iff hl _ _).1 (((hai.inv a.mul_inv).mul h1).mul hai))

theorem phi_inj (hw : IsInertAt F E v w) {g g' : UA σ W.J} (hg : g ∈ USub σ W v) (hg' : g' ∈ USub σ W v)
    (e : phi h W a g = phi h W a g') : g = g' := by
  have e1 : (mat g).map (piE h) = (mat g').map (piE h) := by
    have e2 := congrArg (fun N => a.1 * N.submatrix (ee m).symm (ee m).symm * (a⁻¹).1) e
    simpa [phi_apply, Matrix.mul_assoc] using e2
  refine Subtype.ext (Units.ext (mat_inj hw h ?_ e1))
  have := at_sub (show At (evFin F v) (mat g - 1) from hg) (show At (evFin F v) (mat g' - 1) from hg')
  rwa [sub_sub_sub_cancel_right] at this

theorem phi_surj (hw : IsInertAt F E v w) (hc : IsConjAt σ h c) (hl : l ≠ 0) (hJ : W.J.det ≠ 0)
    (hai : Iso c (W.J.map (algebraMap E _)) (l • antiJ _ (m + m)) a.1)
    {N : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)} (hN : Iso c (Wm _ (Fin m)) (Wm _ (Fin m)) N) :
    ∃ g ∈ USub σ W v, phi h W a g = N := by
  have h1 := iso_submatrix (ee m).symm hN
  rw [← antiJ_submatrix, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id] at h1
  have h2 := (hai.mul ((iso_smul_iff hl _ _).2 h1)).mul (hai.inv a.mul_inv)
  have h3 := h2.isUnit_det (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((map_ne_zero _).2 hJ).isUnit)
  obtain ⟨k, hk, ek⟩ := exists_lift_UA hw hc W (Matrix.mul_nonsing_inv _ h3) h2
  refine ⟨k, hk, ?_⟩
  rw [phi_apply, ek]
  simp [Matrix.mul_assoc]

theorem phi_int (hw : IsInertAt F E v w) (ha : IsFrameAt w W.L a) (g : UA σ W.J) :
    (∀ i j, Valued.v (phi h W a g i j) ≤ 1) ↔ ∀ y ∈ latW W v, mat g *ᵥ y ∈ latW W v := by
  rw [stab_iff hw h ha]
  refine ⟨fun H i j => ?_, fun H i j => H _ _⟩
  obtain ⟨i, rfl⟩ := (ee m).surjective i
  obtain ⟨j, rfl⟩ := (ee m).surjective j
  exact H i j

theorem phi_col (hw : IsInertAt F E v w) {Cy : Matrix (Fin (m + m)) (Fin m) (AE F E)} (hy : At (evFin F v) Cy)
    (g : UA σ W.J) (t : Matrix (Fin m) (Fin m) (AE F E)) :
    mat g * Cy = Cy * t ↔ phi h W a g * ((a⁻¹).1 * Cy.map (piE h)).submatrix (ee m) id =
      ((a⁻¹).1 * Cy.map (piE h)).submatrix (ee m) id * t.map (piE h) := by
  have e1 : phi h W a g * ((a⁻¹).1 * Cy.map (piE h)).submatrix (ee m) id =
      ((a⁻¹).1 * (mat g * Cy).map (piE h)).submatrix (ee m) id := by
    rw [phi_apply, Matrix.submatrix_mul_equiv, Matrix.map_mul, Matrix.mul_assoc, ← Matrix.mul_assoc a.1, Units.mul_inv,
      Matrix.one_mul, Matrix.mul_assoc]
  have e2 : ((a⁻¹).1 * Cy.map (piE h)).submatrix (ee m) id * t.map (piE h) =
      ((a⁻¹).1 * (Cy * t).map (piE h)).submatrix (ee m) id := by
    rw [Matrix.map_mul, ← Matrix.mul_assoc]
    rfl
  rw [e1, e2]
  refine ⟨fun e => by rw [e], fun e => mat_inj hw h (at_sub (at_mul_right _ hy) (at_mul_left hy _)) ?_⟩
  have e3 : (a⁻¹).1 * (mat g * Cy).map (piE h) = (a⁻¹).1 * (Cy * t).map (piE h) := by
    refine Matrix.ext fun i j => ?_
    obtain ⟨i, rfl⟩ := (ee m).surjective i
    exact congrFun (congrFun e i) j
  have e4 := congrArg (fun N => a.1 * N) e3
  simpa only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] using e4

theorem phi_par (hw : IsInertAt F E v w) {Cy : Matrix (Fin (m + m)) (Fin m) (AE F E)} (hy : At (evFin F v) Cy)
    {T : Matrix (Fin m) (Fin m) (w.adicCompletion E)} (hT : IsUnit T.det)
    (eT : ((a⁻¹).1 * Cy.map (piE h)).submatrix (ee m) id = Matrix.fromRows T (0 : Matrix (Fin m) (Fin m) _))
    (g : UA σ W.J) : (∃ t : Matrix (Fin m) (Fin m) (AE F E), mat g * Cy = Cy * t) ↔ (phi h W a g).toBlocks₂₁ = 0 := by
  rw [← block_iff hT, ← eT]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨_, (phi_col hw hy g t).1 ht⟩
  · rintro ⟨t, ht⟩
    obtain ⟨t', -, rfl⟩ := mat_surj h t
    exact ⟨t', (phi_col hw hy g t').2 ht⟩

end Chart

open Chart in
theorem chart : ChartSt := by
  intro F E _ _ _ _ _ σ B r s m W hB hW v w hw h c hc Cy hL
  obtain ⟨a, ha, l, hl, hai, T, hT, eT⟩ := exists_frame_lag hB.cm hw h hc hW hL
  have hG : ∀ g, (phi h W a).toHomUnits g ∈ GW (w.adicCompletion E) c m := fun g => phi_iso hc hl hai g
  have hP : ∀ g, (phi h W a).toHomUnits g ∈ PW (w.adicCompletion E) c m ↔
      ∃ t : Matrix (Fin m) (Fin m) (AE F E), mat g * Cy = Cy * t := fun g => by
    rw [phi_par hw hL.supp hT eT g]
    exact ⟨fun H => GlobalTheory.LGrp.mem_blockQ_two.1 H.2, fun H => ⟨hG g, GlobalTheory.LGrp.mem_blockQ_two.2 H⟩⟩
  refine ⟨(phi h W a).toHomUnits, hG, fun g hg g' hg' e => phi_inj hw hg hg' (congrArg Units.val e), fun M hM => ?_,
    fun g hg => ?_, fun g hg => ?_, fun p _ t ht => ?_⟩
  · obtain ⟨g, hg, e⟩ := phi_surj hw hc hl (det_ne_zero hW) hai hM
    exact ⟨g, hg, Units.ext e⟩
  · rw [mem_IntGL_iff, ← map_inv]
    exact ⟨fun H => ⟨(phi_int hw ha g).2 fun y hy => (H.2 y hy).1, (phi_int hw ha g⁻¹).2 fun y hy => (H.2 y hy).2⟩,
      fun H => ⟨hg, fun y hy => ⟨(phi_int hw ha g).1 H.1 y hy, (phi_int hw ha g⁻¹).1 H.2 y hy⟩⟩⟩
  · refine ⟨fun H => (hP g).2 H.1.2, fun H => ⟨⟨hg, (hP g).1 H⟩, (USub σ W v).inv_mem hg, (hP g⁻¹).1 ?_⟩⟩
    rw [map_inv]
    exact inv_mem H
  · have e := (phi_col (a := a) (h := h) hw hL.supp p t).1 ht
    rw [eT] at e
    exact (block_det hT e).trans (RingHom.map_det (piE h) t).symm

end PositivityTheory.Sph.M2

end
end

-- bundled from Development.WeilBound.ThetaLifts.SphericalLattices.IndexComapOfCover
section
noncomputable section

namespace PositivityTheory.Sph.M2.ZC

open Matrix Formalism.UG

theorem index_comap_of_cover {A G : Type*} [Group A] [Group G] (f : A →* G) (H : Subgroup G)
    (h : ∀ g, ∃ a, (f a)⁻¹ * g ∈ H) : (H.comap f).index = H.index := by
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.map' f (fun a b hab => ?_) : A ⧸ H.comap f → G ⧸ H) ⟨?_, ?_⟩)
  · rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa using hab
  · intro a b
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    intro hab
    have h1 : ((f a : G) : G ⧸ H) = (f b : G) := hab
    rw [QuotientGroup.eq] at h1 ⊢
    simpa using h1
  · intro g
    induction g using QuotientGroup.induction_on with | H g => ?_
    obtain ⟨a, ha⟩ := h g
    exact ⟨(a : A ⧸ H.comap f), (QuotientGroup.eq.mpr ha : ((f a : G) : G ⧸ H) = g)⟩

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_int {y : L} : y ∈ intL L ↔ Valued.v y ≤ (1 : WithZero (Multiplicative ℤ)) := Iff.rfl

def A (r : L) : AddSubgroup L := (intL L).toAddSubgroup.comap (AddMonoidHom.mulLeft r)

theorem mem_A {r y : L} : y ∈ A r ↔ r * y ∈ intL L := Iff.rfl

theorem A_mul (r s : L) : A (r * s) = (A r).comap (AddMonoidHom.mulLeft s) := by
  ext y
  simp [mem_A, mul_assoc]

theorem relIndex_A_mul (r r' s : L) (hs : s ≠ 0) : (A (r * s)).relIndex (A (r' * s)) = (A r).relIndex (A r') := by
  rw [A_mul, A_mul, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective]
  intro y
  exact ⟨s⁻¹ * y, by simp [hs]⟩

variable {ϖ : L} {c : L →+* L} {q : ℕ}

theorem pi_ne (h : IsUnramInv ϖ c q) : ϖ ≠ 0 := by
  intro h0
  have := h.2.2.2.1
  rw [h0, map_zero] at this
  exact WithZero.coe_ne_zero this.symm

theorem pi_int (h : IsUnramInv ϖ c q) : ϖ ∈ intL L := by
  rw [mem_int, h.2.2.2.1, ← WithZero.coe_one, WithZero.coe_le_coe]
  decide

theorem mem_A_inv (h : IsUnramInv ϖ c q) {y : L} :
    y ∈ A ϖ⁻¹ ↔ Valued.v y < (1 : WithZero (Multiplicative ℤ)) := by
  rw [mem_A, mem_int, map_mul, map_inv₀, h.2.2.2.1]
  by_cases hy : Valued.v y = (0 : WithZero (Multiplicative ℤ))
  · simp [hy]
  · obtain ⟨n, hn⟩ := WithZero.ne_zero_iff_exists.mp hy
    rw [← hn, ← WithZero.coe_inv, ← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_le_coe, WithZero.coe_lt_coe]
    show (-(-1 : ℤ) + Multiplicative.toAdd n ≤ 0) ↔ Multiplicative.toAdd n < 0
    omega

theorem relIndex_one (h : IsUnramInv ϖ c q) : (A ϖ⁻¹).relIndex (A (1 : L)) = q ^ 2 := by
  have e : A (1 : L) = (intL L).subtype.toAddMonoidHom.range := by
    ext y
    simp [mem_A]
  rw [e, ← AddSubgroup.index_comap, ← h.2.2.2.2.2.2]
  have e2 : (A ϖ⁻¹).comap (intL L).subtype.toAddMonoidHom =
      (IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring).toAddSubgroup := by
    ext y
    rw [AddSubgroup.mem_comap, mem_A_inv h]
    exact (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))) (a := y)).symm
  rw [e2]
  rfl

theorem A_le (h : IsUnramInv ϖ c q) (r : L) : A (ϖ⁻¹ * r) ≤ A r := by
  intro y hy
  rw [mem_A] at hy ⊢
  have := (intL L).mul_mem (pi_int h) hy
  rwa [mul_assoc, mul_inv_cancel_left₀ (pi_ne h)] at this

theorem relIndex_two (h : IsUnramInv ϖ c q) : (A (ϖ⁻¹ * ϖ⁻¹)).relIndex (A (1 : L)) = q ^ 4 := by
  have h1 : (A (ϖ⁻¹ * ϖ⁻¹)).relIndex (A ϖ⁻¹) = q ^ 2 := by
    rw [← relIndex_one h, ← relIndex_A_mul ϖ⁻¹ 1 ϖ⁻¹ (inv_ne_zero (pi_ne h)), one_mul]
  have h2 : A ϖ⁻¹ ≤ A (1 : L) := by simpa using A_le h 1
  rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ (A_le h _) h2, h1, relIndex_one h]
  ring

def MA (m : ℕ) (r : L) : AddSubgroup (Matrix (Fin m) (Fin m) L) :=
  AddSubgroup.pi Set.univ fun _ => AddSubgroup.pi Set.univ fun _ => A r

theorem mem_MA {m : ℕ} {r : L} {X : Matrix (Fin m) (Fin m) L} : X ∈ MA m r ↔ ∀ i j, r * X i j ∈ intL L :=
  ⟨fun h i j => h i trivial j trivial, fun h i _ j _ => h i j⟩

theorem relIndex_MA (m : ℕ) (r : L) : (MA m r).relIndex (MA m (1 : L)) = ((A r).relIndex (A (1 : L))) ^ (m * m) := by
  let g : (Fin m → Fin m → A (1 : L)) →+ Matrix (Fin m) (Fin m) L :=
    { toFun := fun Y => Matrix.of fun i j => (Y i j : L)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have e : MA m (1 : L) = g.range := by
    ext X
    constructor
    · intro hX
      exact ⟨fun i j => ⟨X i j, mem_MA.mp hX i j⟩, rfl⟩
    · rintro ⟨Y, rfl⟩
      exact mem_MA.mpr fun i j => (Y i j).2
  have e2 : (MA m r).comap g = AddSubgroup.pi Set.univ fun _ => AddSubgroup.pi Set.univ fun _ =>
      (A r).addSubgroupOf (A (1 : L)) := by
    ext Y
    exact ⟨fun h i _ j _ => h i trivial j trivial, fun h i _ j _ => h i trivial j trivial⟩
  rw [e, ← AddSubgroup.index_comap, e2, AddSubgroup.index_pi]
  simp only [AddSubgroup.index_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rfl

def NA (c : L →+* L) (m : ℕ) : AddSubgroup (Matrix (Fin m) (Fin m) L) where
  carrier := {X | (∀ i j, X i j ∈ intL L) ∧ ∀ i j, c (X i j) = -X j i}
  zero_mem' := ⟨fun _ _ => (intL L).zero_mem, fun _ _ => by simp⟩
  add_mem' := fun {X Y} hX hY => ⟨fun i j => (intL L).add_mem (hX.1 i j) (hY.1 i j), fun i j => by
    simp only [Matrix.add_apply, map_add, hX.2, hY.2, neg_add]⟩
  neg_mem' := fun {X} hX => ⟨fun i j => (intL L).neg_mem (hX.1 i j), fun i j => by
    simp only [Matrix.neg_apply, map_neg, hX.2]⟩

theorem c_int (h : IsUnramInv ϖ c q) {y : L} (hy : y ∈ intL L) : c y ∈ intL L := by
  rw [mem_int, h.2.1]; exact hy

theorem relIndex_NA_sq (h : IsUnramInv ϖ c q) (m : ℕ) (r : L) (hr : c r = r) :
    (MA m r).relIndex (NA c m) * (MA m r).relIndex (NA c m) = (MA m r).relIndex (MA m (1 : L)) := by
  obtain ⟨x, hx, hd⟩ := h.2.2.2.2.1
  have hd0 : c x - x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hd
    exact zero_ne_one hd
  have hd1 : x - c x ≠ 0 := fun h0 => hd0 (by linear_combination -h0)
  have hdi : (c x - x)⁻¹ ∈ intL L := by rw [mem_int, map_inv₀, hd, inv_one]
  let f : NA c m × NA c m →+ Matrix (Fin m) (Fin m) L :=
    { toFun := fun p => (p.1 : Matrix (Fin m) (Fin m) L) + x • (p.2 : Matrix (Fin m) (Fin m) L)
      map_zero' := by simp
      map_add' := fun p p' => by
        simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, smul_add]
        abel }
  have fa : ∀ p i j, f p i j = (p.1 : Matrix (Fin m) (Fin m) L) i j + x * (p.2 : Matrix (Fin m) (Fin m) L) i j :=
    fun _ _ _ => rfl
  have e : MA m (1 : L) = f.range := by
    ext X
    rw [mem_MA]
    simp only [one_mul]
    constructor
    · intro hX
      have hb : ∀ i j, -((c x - x)⁻¹ * (X i j + c (X j i))) ∈ intL L := fun i j =>
        (intL L).neg_mem ((intL L).mul_mem hdi ((intL L).add_mem (hX i j) (c_int h (hX j i))))
      refine ⟨(⟨Matrix.of fun i j => X i j - x * -((c x - x)⁻¹ * (X i j + c (X j i))), fun i j =>
          (intL L).sub_mem (hX i j) ((intL L).mul_mem hx (hb i j)), fun i j => ?_⟩,
        ⟨Matrix.of fun i j => -((c x - x)⁻¹ * (X i j + c (X j i))), hb, fun i j => ?_⟩), ?_⟩
      · simp only [Matrix.of_apply, map_sub, map_mul, map_neg, map_inv₀, map_add, h.1]
        rw [← neg_sub (c x) x, inv_neg]
        field_simp
        ring
      · simp only [Matrix.of_apply, map_sub, map_mul, map_neg, map_inv₀, map_add, h.1]
        rw [← neg_sub (c x) x, inv_neg]
        ring
      · ext i j
        rw [fa]
        simp
    · rintro ⟨p, rfl⟩ i j
      rw [fa]
      exact (intL L).add_mem (p.1.2.1 i j) ((intL L).mul_mem hx (p.2.2.1 i j))
  have e2 : (MA m r).comap f = ((MA m r).addSubgroupOf (NA c m)).prod ((MA m r).addSubgroupOf (NA c m)) := by
    ext p
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_prod, AddSubgroup.mem_addSubgroupOf, mem_MA, fa]
    constructor
    · intro hp
      have hb : ∀ i j, r * (p.2 : Matrix (Fin m) (Fin m) L) i j ∈ intL L := fun i j => by
        have h1 := (intL L).neg_mem ((intL L).mul_mem hdi ((intL L).add_mem (hp i j) (c_int h (hp j i))))
        simp only [map_mul, map_add, hr, p.1.2.2, p.2.2.2] at h1
        convert h1 using 1
        field_simp
        ring
      refine ⟨fun i j => ?_, hb⟩
      have h1 := (intL L).sub_mem (hp i j) ((intL L).mul_mem hx (hb i j))
      convert h1 using 1
      ring
    · intro hp i j
      have h1 := (intL L).add_mem (hp.1 i j) ((intL L).mul_mem hx (hp.2 i j))
      convert h1 using 1
      ring
  rw [e, ← AddSubgroup.index_comap, e2, AddSubgroup.index_prod]
  rfl

theorem relIndex_NA (h : IsUnramInv ϖ c q) (m : ℕ) :
    (MA m (ϖ⁻¹ * ϖ⁻¹)).relIndex (NA c m) = q ^ (2 * m * m) := by
  have h1 := relIndex_NA_sq h m (ϖ⁻¹ * ϖ⁻¹) (by rw [map_mul, map_inv₀, h.2.2.1])
  rw [relIndex_MA, relIndex_two h] at h1
  apply Nat.mul_self_inj.mp
  rw [h1]
  ring

end PositivityTheory.Sph.M2.ZC

end
end

-- bundled from Development.WeilBound.ThetaLifts.SphericalLattices.RelIndexTransport
section
noncomputable section

namespace PositivityTheory.Sph.M2

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  PositivityTheory.ThK PositivityTheory.ThKH.Iwas MeasureTheory GlobalTheory.Doubling

theorem relIndex_transport {G H : Type} [Group G] [Group H] (U : Subgroup G) (Φ : G →* H)
    (hinj : ∀ g ∈ U, ∀ g' ∈ U, Φ g = Φ g' → g = g') {A B : Subgroup G} (hA : A ≤ U) (hB : B ≤ U) :
    (A.map Φ).relIndex (B.map Φ) = A.relIndex B := by
  have hφ : Function.Injective (Φ.comp U.subtype) := fun x y e => Subtype.ext (hinj _ x.2 _ y.2 e)
  have e : ∀ C : Subgroup G, C ≤ U → (C.subgroupOf U).map (Φ.comp U.subtype) = C.map Φ := fun C hC => by
    rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_of_le_left hC]
  rw [← e A hA, ← e B hB, Subgroup.relIndex_map_map_of_injective _ _ hφ, Subgroup.relIndex_subgroupOf hB]

theorem map_conj_map {G H : Type} [Group G] [Group H] (Φ : G →* H) (g : G) (A : Subgroup G) :
    (A.map (MulAut.conj g).toMonoidHom).map Φ = (A.map Φ).map (MulAut.conj (Φ g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul, map_inv]

theorem modSt_of (hC : ChartSt) (hL : LocModSt) : PositivityTheory.Sph.ModSt := by
  intro F E _ _ _ _ _ σ d B W r s hB hW v w hw _ m Cy hLag hAd p hp t ht u hu
  obtain rfl : d = m + m := hLag.rank.trans (two_mul m)
  have hσ := hB.cm
  have h : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw h
  obtain ⟨ϖ, hU⟩ := exists_isUnramInv hσ hw hc
  obtain ⟨Φ, hG, hinj, hsurj, hK, hP, hdet⟩ := hC F E σ B r s m W hB hW v w hw h c hc Cy hLag
  set KP := PositivityTheory.Sph.PSub σ W v Cy ⊓ KSub σ W v with hKP
  have hKPU : KP ≤ USub σ W v := fun g hg => (hg.2 : g ∈ KAt σ W v).1
  have hpU : p ∈ USub σ W v := (hp.1 : p ∈ PAt σ W v Cy).1
  have himg : KP.map Φ = KPW (w.adicCompletion E) c m := by
    ext M
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hgU := hKPU hg
      exact ⟨(hP g hgU).1 hg.1, hG g, (hK g hgU).1 hg.2⟩
    · rintro ⟨hM1, hM2, hM3⟩
      obtain ⟨g, hgU, rfl⟩ := hsurj _ hM2
      exact ⟨g, ⟨(hP g hgU).2 hM1, (hK g hgU).2 hM3⟩, rfl⟩
  have hconj : ∀ g ∈ USub σ W v, KP.map (MulAut.conj g).toMonoidHom ≤ USub σ W v := fun g hg => by
    rintro _ ⟨k, hk, rfl⟩
    exact (USub σ W v).mul_mem ((USub σ W v).mul_mem hg (hKPU hk)) ((USub σ W v).inv_mem hg)
  have tr : ∀ g ∈ USub σ W v, (KP.map (MulAut.conj g).toMonoidHom).relIndex KP =
      ((KPW (w.adicCompletion E) c m).map (MulAut.conj (Φ g)).toMonoidHom).relIndex (KPW (w.adicCompletion E) c m) :=
    fun g hg => by
      rw [← relIndex_transport (USub σ W v) Φ hinj (hconj g hg) hKPU, map_conj_map, himg]
  have hPW : Φ p ∈ PW (w.adicCompletion E) c m := (hP p hpU).1 hp
  have key := hL (w.adicCompletion E) ϖ c (Formalism.UG.qV F v) hU m (Φ p) hPW
  rw [← map_inv, ← tr p⁻¹ ((USub σ W v).inv_mem hpU), ← tr p hpU, hdet p hp t ht] at key
  rw [key]
  congr 1
  have h21 : (Φ p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)).toBlocks₂₁ = 0 :=
    GlobalTheory.LGrp.mem_blockQ_two.1 hPW.2
  have hdetΦ : (Φ p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)).det =
      (Φ p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)).toBlocks₁₁.det *
        (Φ p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)).toBlocks₂₂.det := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (Φ p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)), h21]
    exact Matrix.det_fromBlocks_zero₂₁ _ _ _
  have hne : piE h t.det ≠ 0 := by
    rw [← hdet p hp t ht]
    intro h0
    have hu' := (Matrix.isUnit_iff_isUnit_det _).1 (Φ p).isUnit
    rw [hdetΦ, h0, zero_mul] at hu'
    exact not_isUnit_zero hu'
  let x : (Fv F v ⊗[F] E)ˣ := Units.map (complEquiv hw h).symm.toMonoidHom (Units.mk0 _ hne)
  have hx1 : x.1 = (t.map (compFin F E v)).det := by
    change (complEquiv hw h).symm ((complEquiv hw h) (compFin F E v t.det)) = _
    rw [RingEquiv.symm_apply_apply]
    exact RingHom.map_det _ _
  have habs := GlobalTheory.AbsInert.absEv_inert F E σ hσ v w h hw x
  have hm : (((sbClass (Fv F v)).modu u : NNReal) : ℝ) = (absEv F E v x : ℝ) := by
    have e1 := GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v (u : Fv F v) u.ne_zero
    rw [Units.mk0_val] at e1
    change ((distribHaarChar (Fv F v) u : NNReal) : ℝ) = _
    rw [e1, absEv_apply, hx1, ← hu]
  have hx : piE h t.det = toCompl h x.1 := by
    rw [hx1]
    change toCompl h (compFin F E v t.det) = toCompl h (t.map (compFin F E v)).det
    rw [RingHom.map_det]
    rfl
  rw [hm, habs, hx, ← zpow_natCast, ← zpow_mul]
  congr 1
  ring

end PositivityTheory.Sph.M2

end
end

