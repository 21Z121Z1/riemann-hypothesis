import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocG
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0002
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.ExistsHomOfBasis
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

theorem norm_le_one_iff_val {F C : Type} [Field F] [NumberField F] [NormedField C] (φ : F →+* C)
    (w : HeightOneSpectrum (𝓞 F)) (h1 : ∀ x : 𝓞 F, ‖φ (x : F)‖ ≤ 1)
    (h2 : ∀ x : 𝓞 F, x ∈ w.asIdeal ↔ ‖φ (x : F)‖ < 1) (x : F) : ‖φ x‖ ≤ 1 ↔ w.valuation F x ≤ 1 := by
  have hu : ∀ d : 𝓞 F, d ∉ w.asIdeal → ‖φ (d : F)‖ = 1 := fun d hd =>
    le_antisymm (h1 d) (not_lt.mp fun h => hd ((h2 d).mpr h))
  have key : ∀ y : F, w.valuation F y ≤ 1 → ∃ n : 𝓞 F, ‖φ y‖ = ‖φ (n : F)‖ ∧
      w.valuation F y = w.valuation F (n : F) := fun y hy => by
    obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer y hy
    have hd : w.valuation F (algebraMap (𝓞 F) F d) = 1 := w.valuation_eq_one_iff_notMem.mpr d.2
    refine ⟨n, ?_, ?_⟩
    · have := congrArg (fun t => ‖φ t‖) h
      simp only [map_mul, norm_mul] at this
      rwa [show ‖φ (algebraMap (𝓞 F) F d)‖ = 1 from hu _ d.2, mul_one] at this
    · have := congrArg (w.valuation F) h
      rwa [map_mul, hd, mul_one] at this
  refine ⟨fun h => not_lt.mp fun hlt => ?_, fun h => ?_⟩
  · have hx : x ≠ 0 := by rintro rfl; simp at hlt
    have hi : w.valuation F x⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hlt
    obtain ⟨n, e1, e2⟩ := key _ hi.le
    have hn : n ∈ w.asIdeal := (w.valuation_lt_one_iff_mem n).mp (e2 ▸ hi)
    have := (h2 n).mp hn
    rw [← e1, map_inv₀, norm_inv, inv_lt_one₀ (norm_pos_iff.mpr ((map_ne_zero φ).mpr hx))] at this
    exact absurd h (not_le.mpr this)
  · obtain ⟨n, e1, -⟩ := key x h
    rw [e1]; exact h1 n

theorem resChar_mem' (D : D7) (w : D.what₂.places.Pl) :
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  have hp := D.what₂.places.resChar_prime w
  have hne : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h := D.what₂.places.val_resChar w
  rw [D.val_eq w _ hne] at h
  have h1 : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) :=
    WithTop.coe_injective h
  have h2 : (0 : ℤ) < D.what₂.places.ramIdx w := by exact_mod_cast D.what₂.places.ramIdx_pos w
  rw [← (D.plEq w).valuation_lt_one_iff_mem (K := D.what₂.LL)]
  show (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL _) < 1
  have hv := (Valuation.ne_zero_iff ((D.plEq w).valuation D.what₂.LL)).mpr hne
  rw [map_natCast, ← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  unfold vAdd at h1
  omega

theorem mem_intW_iff (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    x ∈ intW D.what₂.places w ↔ (D.plEq w).valuation D.what₂.LL x ≤ 1 := by
  show (0 : WithTop ℤ) ≤ D.what₂.places.val w x ↔ _
  by_cases hx : x = 0
  · subst hx; simp
  · have hv := (Valuation.ne_zero_iff ((D.plEq w).valuation D.what₂.LL)).mpr hx
    rw [D.val_eq w x hx, ← WithTop.coe_zero, WithTop.coe_le_coe, vAdd, neg_nonneg]
    conv_rhs => rw [← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_le_exp]

theorem exists_lamExt {K : Type} [Field K] [NumberField K] (e : K →+* ℂ) {C : Type} [Field C] [IsAlgClosed C]
    (f : K →+* C) : ∃ lam : (algebraicClosure ℚ ℂ) →+* C, ∀ x : K, ∃ hx : e x ∈ algebraicClosure ℚ ℂ,
      f x = lam ⟨e x, hx⟩ := by
  have hmem : ∀ x : K, e x ∈ algebraicClosure ℚ ℂ := fun x =>
    (mem_algebraicClosure_iff).mpr ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom e.toRatAlgHom)
  let j : K →+* algebraicClosure ℚ ℂ := e.codRestrict (algebraicClosure ℚ ℂ).toSubring hmem
  let _ : Algebra K (algebraicClosure ℚ ℂ) := j.toAlgebra
  let _ : Algebra K C := f.toAlgebra
  have h0 : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have : Algebra.IsAlgebraic K (algebraicClosure ℚ ℂ) := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let l : algebraicClosure ℚ ℂ →ₐ[K] C := IsAlgClosed.lift
  exact ⟨l.toRingHom, fun x => ⟨hmem x, (l.commutes x).symm⟩⟩

theorem exists_placeEmb (D : D7) (w : D.what₂.places.Pl) [Fact (D.what₂.places.resChar w).Prime] :
    ∃ (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
      (iL : D.what₂.LL →+* ℂ_[D.what₂.places.resChar w]),
      (∀ x, ∃ hx : D.what₂.embLL x ∈ algebraicClosure ℚ ℂ, iL x = lam ⟨D.what₂.embLL x, hx⟩) ∧
      ∀ x, x ∈ intW D.what₂.places w ↔ ‖iL x‖ ≤ 1 := by
  obtain ⟨φ, hφ⟩ := LB.exists_embAt (l := D.what₂.places.resChar w) (D.plEq w) (resChar_mem' D w)
  let iL := (algebraMap (PadicAlgCl (D.what₂.places.resChar w)) ℂ_[D.what₂.places.resChar w]).comp φ
  have hn : ∀ x, ‖iL x‖ = ‖φ x‖ := fun x => PadicComplex.norm_extends _ (φ x)
  obtain ⟨lam, hl⟩ := exists_lamExt D.what₂.embLL iL
  refine ⟨lam, iL, hl, fun x => ?_⟩
  rw [mem_intW_iff, hn]
  refine (norm_le_one_iff_val φ _ (fun y => ?_) hφ x).symm
  have hi : IsIntegral ℤ (φ (y : D.what₂.LL)) := (RingOfIntegers.isIntegral_coe y).map φ.toIntAlgHom
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl (D.what₂.places.resChar w)))
    ).isIntegral_iff_v_le_one.mp hi.tower_top
  exact_mod_cast (show ‖φ (y : D.what₂.LL)‖₊ ≤ 1 from h2)

theorem exists_hom_of_basis {L S M ι : Type} [Field L] [Field S] [Field M] [Algebra L S] [Algebra L M]
    [IsAlgClosed M] (x : ι → S) (y : ι → M) (hx : IsTranscendenceBasis L x) (hy : AlgebraicIndependent L y) :
    Nonempty (S →ₐ[L] M) := by
  let _ : Algebra (MvPolynomial ι L) S := (MvPolynomial.aeval x : MvPolynomial ι L →ₐ[L] S).toRingHom.toAlgebra
  let _ : Algebra (MvPolynomial ι L) M := (MvPolynomial.aeval y : MvPolynomial ι L →ₐ[L] M).toRingHom.toAlgebra
  have : FaithfulSMul (MvPolynomial ι L) S := (faithfulSMul_iff_algebraMap_injective _ _).mpr hx.1
  have : FaithfulSMul (MvPolynomial ι L) M := (faithfulSMul_iff_algebraMap_injective _ _).mpr hy
  have hA := hx.isAlgebraic
  have : Algebra.IsAlgebraic (MvPolynomial ι L) S := ⟨fun s => by
    obtain ⟨q, hq0, hq⟩ := hA.isAlgebraic s
    let e := hx.1.aevalEquiv.symm.toRingEquiv.toRingHom
    refine ⟨q.map e, (Polynomial.map_ne_zero_iff hx.1.aevalEquiv.symm.injective).mpr hq0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hq, Polynomial.aeval_def]
    congr 1
    ext t
    obtain ⟨r, rfl⟩ := hx.1.aevalEquiv.surjective t
    show MvPolynomial.aeval x (hx.1.aevalEquiv.symm (hx.1.aevalEquiv r)) = _
    rw [AlgEquiv.symm_apply_apply]
    exact (hx.1.algebraMap_aevalEquiv r).symm⟩
  let l : S →ₐ[MvPolynomial ι L] M := IsAlgClosed.lift
  exact ⟨{ l.toRingHom with
    commutes' := fun a => by
      have h := l.commutes (MvPolynomial.C a)
      simpa [RingHom.algebraMap_toAlgebra] using h }⟩

theorem exists_endo {L C : Type} [Field L] [NumberField L] [Field C] [CharZero C] [IsAlgClosed C]
    (a b : L →+* C) : ∃ α : C →+* C, α.comp a = b := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ C
  have ind : ∀ f : L →+* C, letI := f.toAlgebra; IsTranscendenceBasis L ((↑) : s → C) := fun f => by
    let _ := f.toAlgebra
    have : IsScalarTower ℚ L C := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    exact (Algebra.IsAlgebraic.isTranscendenceBasis_iff ℚ L).mp hs
  obtain ⟨α⟩ := @exists_hom_of_basis L C C s _ _ _ a.toAlgebra b.toAlgebra _ _ _ (ind a) (ind b).1
  exact ⟨@AlgHom.toRingHom L C C _ _ _ a.toAlgebra b.toAlgebra α,
    RingHom.ext fun x => @AlgHom.commutes L C C _ _ _ a.toAlgebra b.toAlgebra α x⟩

theorem exists_iK {L K C : Type} [Field L] [NumberField L] [Field K] [Field C] [CharZero C] [IsAlgClosed C]
    (f : L →+* K) (i0 : K →+* C) (iL : L →+* C) : ∃ iK : K →+* C, ∀ x, iK (f x) = iL x := by
  obtain ⟨α, h⟩ := exists_endo (i0.comp f) iL
  exact ⟨α.comp i0, fun x => RingHom.congr_fun h x⟩

end Formalism.BasicNotions.Examples₂
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.RelDet
section
open NumberField

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open Formalism.BasicNotions

section RelDet

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem smulLat_one {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) :
    SDLat.smulLat (1 : Matrix (Fin N) (Fin N) E) L = L := by
  unfold SDLat.smulLat
  rw [Matrix.toLin'_one]
  exact Submodule.map_id L

theorem smulLat_mul {N : ℕ} (A B : Matrix (Fin N) (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E)) :
    SDLat.smulLat (A * B) L = SDLat.smulLat A (SDLat.smulLat B L) := by
  unfold SDLat.smulLat
  rw [← Submodule.map_comp, Matrix.toLin'_mul]
  rfl

def orbRel (N : ℕ) : Setoid (SDLat E N) where
  r L L' := ∃ γ : Matrix.unitaryGroup (Fin N) E, L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) E) L.1
  iseqv := by
    refine ⟨fun L => ⟨1, ?_⟩, fun {L L'} ⟨γ, h⟩ => ⟨γ⁻¹, ?_⟩, fun {L L' L''} ⟨γ, h⟩ ⟨γ', h'⟩ => ⟨γ' * γ, ?_⟩⟩
    · exact (smulLat_one L.1).symm
    · rw [h, ← smulLat_mul]
      have : ((γ⁻¹ : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E) *
          (γ : Matrix (Fin N) (Fin N) E) = 1 := by
        rw [← Submonoid.coe_mul, inv_mul_cancel]; rfl
      rw [this, smulLat_one]
    · rw [h', h, ← smulLat_mul]; rfl

def orbRep {N : ℕ} (L : SDLat E N) : SDLat E N := (Quotient.mk (orbRel N) L).out

theorem orbRep_rel {N : ℕ} (L : SDLat E N) : (orbRel N) (orbRep L) L := Quotient.mk_out (s := orbRel N) L

theorem orbRep_eq {N : ℕ} {L L' : SDLat E N} (h : (orbRel N) L L') : orbRep L = orbRep L' := by
  unfold orbRep
  rw [Quotient.sound h]

def orbGam {N : ℕ} (L : SDLat E N) : Matrix.unitaryGroup (Fin N) E := Classical.choose (orbRep_rel L)

theorem orbGam_spec {N : ℕ} (L : SDLat E N) :
    L.1 = SDLat.smulLat ((orbGam L : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E) (orbRep L).1 :=
  Classical.choose_spec (orbRep_rel L)

def detU {N : ℕ} (γ : Matrix.unitaryGroup (Fin N) E) : unitary E :=
  ⟨(γ : Matrix (Fin N) (Fin N) E).det, Matrix.det_of_mem_unitary γ.2⟩

theorem detU_mul {N : ℕ} (γ δ : Matrix.unitaryGroup (Fin N) E) : detU (γ * δ) = detU γ * detU δ := by
  apply Subtype.ext
  show ((γ * δ : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E).det = _
  rw [Submonoid.coe_mul, Matrix.det_mul]
  rfl

variable {Tau : Type} [Fintype Tau] (emb : Tau → (E →+* ℂ))

def inverseEmbeddingProduct : unitary E →* ℂˣ :=
  (∏ τ : Tau, (Units.map (emb τ).toMonoidHom).comp Unitary.toUnits)⁻¹

theorem inverseEmbeddingProduct_apply (z : unitary E) : ((inverseEmbeddingProduct emb z : ℂˣ) : ℂ) = ∏ τ : Tau, (emb τ (z : E))⁻¹ := by
  simp [inverseEmbeddingProduct]

theorem inverseEmbeddingProduct_sign_eq_one (hcard : Even (Fintype.card Tau)) (z : unitary E) (hz : (z : E) = 1 ∨ (z : E) = -1) :
    inverseEmbeddingProduct emb z = 1 := by
  apply Units.ext
  rw [inverseEmbeddingProduct_apply, Units.val_one]
  rcases hz with hz | hz
  · simp [hz]
  · simp [hz, hcard.neg_one_pow]

def potGen {N : ℕ} (L : SDLat E N) : ℂˣ := inverseEmbeddingProduct emb (detU (orbGam L))

def relDetGen (N : ℕ) (L L' : SDLat E N) : ℂˣ := (potGen emb L)⁻¹ * potGen emb L'

theorem relDetGen_self (N : ℕ) (L : SDLat E N) : relDetGen emb N L L = 1 := by
  simp [relDetGen]

theorem relDetGen_mul (N : ℕ) (L L' L'' : SDLat E N) :
    relDetGen emb N L L' * relDetGen emb N L' L'' = relDetGen emb N L L'' := by
  simp only [relDetGen]
  group

theorem inverseEmbeddingProduct_stabilizer_det (hstar : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x))
    (hmu : ∀ x : E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → ∏ τ : Tau, emb τ x = 1)
    {N : ℕ} (δ : Matrix.unitaryGroup (Fin N) E) (L : SDLat E N)
    (hδ : SDLat.smulLat (δ : Matrix (Fin N) (Fin N) E) L.1 = L.1) : inverseEmbeddingProduct emb (detU δ) = 1 := by
  apply Units.ext
  rw [inverseEmbeddingProduct_apply, Units.val_one, Finset.prod_inv_distrib, inv_eq_one]
  apply hmu
  refine det_root_of_unity_of_stab hstar (δ : Matrix (Fin N) (Fin N) E) (Matrix.det_of_mem_unitary δ.2)
    L.1 L.2.1 L.2.2.1 ?_
  intro x hx
  have : (δ : Matrix (Fin N) (Fin N) E).mulVec x ∈ SDLat.smulLat (δ : Matrix (Fin N) (Fin N) E) L.1 :=
    ⟨x, hx, by simp [Matrix.toLin'_apply]⟩
  rwa [hδ] at this

theorem relDetGen_smul (hstar : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x))
    (hmu : ∀ x : E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → ∏ τ : Tau, emb τ x = 1)
    (N : ℕ) (L L' : SDLat E N) (γ : Matrix.unitaryGroup (Fin N) E)
    (h : L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) E) L.1) :
    relDetGen emb N L L' = inverseEmbeddingProduct emb ⟨(γ : Matrix (Fin N) (Fin N) E).det, Matrix.det_of_mem_unitary γ.2⟩ := by
  have hrel : (orbRel N) L L' := ⟨γ, h⟩
  have hrep : orbRep L' = orbRep L := (orbRep_eq hrel).symm
  set r := orbRep L with hr
  set gL := orbGam L
  set gL' := orbGam L'
  have hL : L.1 = SDLat.smulLat (gL : Matrix (Fin N) (Fin N) E) r.1 := orbGam_spec L
  have hL' : L'.1 = SDLat.smulLat (gL' : Matrix (Fin N) (Fin N) E) r.1 := by
    have := orbGam_spec L'; rwa [hrep] at this
  set δ : Matrix.unitaryGroup (Fin N) E := (γ * gL)⁻¹ * gL'
  have hδ : SDLat.smulLat (δ : Matrix (Fin N) (Fin N) E) r.1 = r.1 := by
    have e1 : SDLat.smulLat ((γ * gL : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E) r.1 =
        SDLat.smulLat (gL' : Matrix (Fin N) (Fin N) E) r.1 := by
      rw [Submonoid.coe_mul, smulLat_mul, ← hL, ← h, hL']
    show SDLat.smulLat (((γ * gL)⁻¹ * gL' : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E) r.1 = r.1
    rw [Submonoid.coe_mul, smulLat_mul, ← e1, ← smulLat_mul, ← Submonoid.coe_mul, inv_mul_cancel]
    exact smulLat_one r.1
  have hs := inverseEmbeddingProduct_stabilizer_det emb hstar hmu δ r hδ
  have hg : gL' = (γ * gL) * δ := by
    show gL' = (γ * gL) * ((γ * gL)⁻¹ * gL')
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have : potGen emb L' = inverseEmbeddingProduct emb (detU γ) * potGen emb L := by
    simp only [potGen]
    rw [show orbGam L' = gL' from rfl, hg, detU_mul, detU_mul, map_mul, map_mul, hs, mul_one, mul_comm]
  simp only [relDetGen, this]
  rw [mul_comm (inverseEmbeddingProduct emb (detU γ)), ← mul_assoc, inv_mul_cancel, one_mul]
  rfl

end RelDet

section Host

variable {R : Ranks} (H : Host R) {Tau : Type} [Fintype Tau] (eTau : Tau ≃ ↥(R.Psi))

def embTau : Tau → (H.E →+* ℂ) := fun τ => H.emb ((eTau τ : R.Psi) : R.GG)

theorem prod_embTau_eq_one_of_torsion : ∀ x : H.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → ∏ τ : Tau, embTau H eTau τ x = 1 :=
  fun _ hx => UpperTheory.Mu.prod_emb H eTau hx

theorem eq_one_or_neg_one_of_torsionOrder_two (h2 : Units.torsionOrder H.E = 2) :
    ∀ x : H.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → x = 1 ∨ x = -1 := by
  rintro x ⟨m, hm, hx⟩
  have hi : IsIntegral ℤ x := IsIntegral.of_pow hm (by rw [hx]; exact isIntegral_one)
  let y : 𝓞 H.E := ⟨x, hi⟩
  have hy : y ^ m = 1 := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, map_one]
    exact hx
  let u : (𝓞 H.E)ˣ := Units.ofPowEqOne y m hy hm.ne'
  have hu : u ∈ Units.torsion H.E := by
    rw [Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨m, hm, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hy)⟩
  have hc : Nat.card (Units.torsion H.E) = 2 := by
    rw [← h2, Units.torsionOrder]
    try simp
  have h1 : (⟨u, hu⟩ : Units.torsion H.E) ^ 2 = 1 := by rw [← hc]; exact pow_card_eq_one'
  have h3 : u ^ 2 = 1 := congrArg Subtype.val h1
  have h4 : y ^ 2 = 1 := congrArg Units.val h3
  have h5 : x ^ 2 = 1 := by
    have := congrArg (algebraMap (𝓞 H.E) H.E) h4
    rwa [map_pow, map_one] at this
  exact sq_eq_one_iff.mp h5

theorem even_card_Tau {R : Ranks} {Tau : Type} [Fintype Tau] (eTau : Tau ≃ ↥(R.Psi)) :
    Even (Fintype.card Tau) := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr eTau, R.toFrame.natCard_Psi]
  exact even_two_mul _

def exampleInverseEmbeddingProduct : letI := H.cmStar; unitary H.E →* ℂˣ := letI := H.cmStar; inverseEmbeddingProduct (embTau H eTau)

theorem exampleCharacter_unitary_product : letI := H.cmStar; ∀ z : unitary H.E,
    (((MonoidHom.id ℂˣ) (exampleInverseEmbeddingProduct H eTau z) : ℂˣ) : ℂ) =
      ∏ τ : Tau, (H.emb ((eTau τ : R.Psi) : R.GG) (z : H.E))⁻¹ := by
  let _ := H.cmStar
  intro z
  exact inverseEmbeddingProduct_apply (embTau H eTau) z

def relDetExample : letI := H.cmStar; ∀ N, SDLat H.E N → SDLat H.E N → ℂˣ :=
  letI := H.cmStar; relDetGen (embTau H eTau)

theorem relDetExample_self : letI := H.cmStar; ∀ N L, relDetExample H eTau N L L = 1 := by
  let _ := H.cmStar
  exact relDetGen_self (embTau H eTau)

theorem relDetExample_mul : letI := H.cmStar; ∀ N L L' L'',
    relDetExample H eTau N L L' * relDetExample H eTau N L' L'' = relDetExample H eTau N L L'' := by
  let _ := H.cmStar
  exact relDetGen_mul (embTau H eTau)

theorem relDetExample_smul : letI := H.cmStar; ∀ N (L L' : SDLat H.E N) (γ : Matrix.unitaryGroup (Fin N) H.E),
    L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 →
      relDetExample H eTau N L L' = exampleInverseEmbeddingProduct H eTau
        ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩ := by
  let _ := H.cmStar
  exact relDetGen_smul (embTau H eTau) (emb_star H) (prod_embTau_eq_one_of_torsion H eTau)

end Host

end Formalism.BasicNotions.Examples₂
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.WithSeenTauOf
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂

def withSeen (D : D7) (seen : D.what₂.Word → D.what₂.places.Pl → Bool)
    (tau : ∀ u, D.what₂.places.Pl → ((D.mem u).A.vT ≃ D.what₂.Tau)) : D7 :=
  { D with
    fm := fun u => { D.fm u with seenP := seen u, tauOf := tau u }
    eMu_isom := D.eMu_isom
    nuIn := D.nuIn
    nuIn_inj := D.nuIn_inj
    nuIn_range := D.nuIn_range
    nuIn_jN := D.nuIn_jN
    nuIn_norm := D.nuIn_norm
    s_Cu_isom := D.s_Cu_isom }

theorem withSeen_seenP (D : D7) (seen tau u) : ((withSeen D seen tau).fm u).seenP = seen u := rfl
theorem withSeen_tauOf (D : D7) (seen tau u) : ((withSeen D seen tau).fm u).tauOf = tau u := rfl

end Formalism.BasicNotions.Examples₂
end
end

