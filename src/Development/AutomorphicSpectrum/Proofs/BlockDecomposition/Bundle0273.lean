import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0259
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlaneStrongApproxProduct
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0264
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LineOfSingleJump
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0526
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0195
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSpecialUnitarySupport
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.CompactSingles

open GlobalTheory.CompanionTheory.StrongApproxSub GlobalTheory.CompanionTheory.Sa2Prod

section Idem

variable {F : Type} [Field F] [NumberField F]

theorem place_ext {a b : AF F} (h1 : ∀ w, fstA F a w = fstA F b w)
    (h2 : ∀ v, evalV F v (sndA F a) = evalV F v (sndA F b)) : a = b :=
  adele_ext (ainf_ext h1) (finAdele_ext h2)

theorem fst_mul (a b : AF F) (w : InfinitePlace F) : fstA F (a * b) w = fstA F a w * fstA F b w := by
  rw [map_mul]; rfl

theorem fst_add (a b : AF F) (w : InfinitePlace F) : fstA F (a + b) w = fstA F a w + fstA F b w := by
  rw [map_add]; rfl

theorem snd_mul (a b : AF F) (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (sndA F (a * b)) = evalV F v (sndA F a) * evalV F v (sndA F b) := by
  rw [map_mul, map_mul]

theorem snd_add (a b : AF F) (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (sndA F (a + b)) = evalV F v (sndA F a) + evalV F v (sndA F b) := by
  rw [map_add, map_add]

theorem idem_self {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {a : AF F}
    (h : IsPlacesIdem S₁ S₂ a) : a * a = a := by
  refine place_ext (fun w => ?_) (fun v => ?_)
  · rw [fst_mul]
    by_cases hw : w ∈ S₁
    · rw [h.1 w hw, one_mul]
    · rw [h.2.1 w hw, zero_mul]
  · rw [snd_mul]
    by_cases hv : v ∈ S₂
    · rw [h.2.2.1 v hv, one_mul]
    · rw [h.2.2.2 v hv, zero_mul]

theorem idem_orth {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b : AF F}
    (ha : IsPlacesIdem A₁ A₂ a) (hb : IsPlacesIdem B₁ B₂ b) (h₁ : Disjoint A₁ B₁) (h₂ : Disjoint A₂ B₂) :
    a * b = 0 := by
  refine place_ext (fun w => ?_) (fun v => ?_)
  · rw [fst_mul, map_zero]
    by_cases hw : w ∈ A₁
    · rw [hb.2.1 w (Finset.disjoint_left.1 h₁ hw), mul_zero]; rfl
    · rw [ha.2.1 w hw, zero_mul]; rfl
  · rw [snd_mul, map_zero, map_zero]
    by_cases hv : v ∈ A₂
    · rw [hb.2.2.2 v (Finset.disjoint_left.1 h₂ hv), mul_zero]
    · rw [ha.2.2.2 v hv, zero_mul]

theorem idem_add {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b δ : AF F}
    [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum (𝓞 F))]
    (ha : IsPlacesIdem A₁ A₂ a) (hb : IsPlacesIdem B₁ B₂ b) (h₁ : Disjoint A₁ B₁) (h₂ : Disjoint A₂ B₂)
    (hδ : IsPlacesIdem (A₁ ∪ B₁) (A₂ ∪ B₂) δ) : δ = a + b := by
  refine place_ext (fun w => ?_) (fun v => ?_)
  · rw [fst_add]
    by_cases hw : w ∈ A₁
    · rw [hδ.1 w (Finset.mem_union_left _ hw), ha.1 w hw, hb.2.1 w (Finset.disjoint_left.1 h₁ hw), add_zero]
    · rw [ha.2.1 w hw, zero_add]
      by_cases hw' : w ∈ B₁
      · rw [hδ.1 w (Finset.mem_union_right _ hw'), hb.1 w hw']
      · rw [hδ.2.1 w (by simp [hw, hw']), hb.2.1 w hw']
  · rw [snd_add]
    by_cases hv : v ∈ A₂
    · rw [hδ.2.2.1 v (Finset.mem_union_left _ hv), ha.2.2.1 v hv, hb.2.2.2 v (Finset.disjoint_left.1 h₂ hv),
        add_zero]
    · rw [ha.2.2.2 v hv, zero_add]
      by_cases hv' : v ∈ B₂
      · rw [hδ.2.2.1 v (Finset.mem_union_right _ hv'), hb.2.2.1 v hv']
      · rw [hδ.2.2.2 v (by simp [hv, hv']), hb.2.2.2 v hv']

theorem idem_empty {δ : AF F} (h : IsPlacesIdem (∅ : Finset (InfinitePlace F)) ∅ δ) : δ = 0 := by
  refine place_ext (fun w => ?_) (fun v => ?_)
  · rw [h.2.1 w (Finset.notMem_empty w)]; rfl
  · rw [h.2.2.2 v (Finset.notMem_empty v), map_zero, map_zero]

end Idem

section Group

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem HA_ext {g h : HA (AF F) σ J} (e : mt g = mt h) : g = h :=
  Subtype.ext (Units.ext e)

theorem SUSupp_zero_eq (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) :
    SUSupp σ J (0 : AF F) = {1} := by
  ext g
  constructor
  · intro hg
    refine HA_ext ?_
    have h := (mem_SUSupp.1 hg).2
    rw [map_zero, zero_smul] at h
    rw [mt_one]
    exact (sub_eq_zero.1 h.symm)
  · rintro rfl
    exact (suppGroup σ J 0).one_mem

theorem SUSupp_mono {a b : AF F} (h : b * a = a) : SUSupp σ J a ⊆ SUSupp σ J b := by
  intro g hg
  obtain ⟨h1, h2⟩ := mem_SUSupp.1 hg
  refine mem_SUSupp.2 ⟨h1, ?_⟩
  rw [← h2, smul_smul, ← map_mul, h]

theorem SUSupp_add (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) {a b : AF F} (ha : a * a = a) (hb : b * b = b)
    (hab : a * b = 0) :
    SUSupp σ J (a + b) = (fun p : HA (AF F) σ J × HA (AF F) σ J => p.1 * p.2) '' (SUSupp σ J a ×ˢ SUSupp σ J b) := by
  have hba : b * a = 0 := by rw [mul_comm, hab]
  have ha' : algebraMap (AF F) (AF F ⊗[F] E) a * algebraMap (AF F) (AF F ⊗[F] E) a =
      algebraMap (AF F) (AF F ⊗[F] E) a := by rw [← map_mul, ha]
  have hb' : algebraMap (AF F) (AF F ⊗[F] E) b * algebraMap (AF F) (AF F ⊗[F] E) b =
      algebraMap (AF F) (AF F ⊗[F] E) b := by rw [← map_mul, hb]
  ext g
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ := mem_SUSupp.1 hg
    refine ⟨(truncHA σ J ha' g, truncHA σ J hb' g), ⟨truncHA_mem σ J ha' h1, truncHA_mem σ J hb' h1⟩, ?_⟩
    refine HA_ext ?_
    change trunc _ (mt g) * trunc _ (mt g) = mt g
    have hab' : algebraMap (AF F) (AF F ⊗[F] E) a * algebraMap (AF F) (AF F ⊗[F] E) b = 0 := by
      rw [← map_mul, hab, map_zero]
    have h3 : algebraMap (AF F) (AF F ⊗[F] E) a • (mt g - 1) + algebraMap (AF F) (AF F ⊗[F] E) b • (mt g - 1) =
        mt g - 1 := by
      rw [← add_smul, ← map_add]; exact h2
    have e : trunc (algebraMap (AF F) (AF F ⊗[F] E) a) (mt g) * trunc (algebraMap (AF F) (AF F ⊗[F] E) b) (mt g) =
        1 + (algebraMap (AF F) (AF F ⊗[F] E) a • (mt g - 1) + algebraMap (AF F) (AF F ⊗[F] E) b • (mt g - 1)) := by
      have hz : (algebraMap (AF F) (AF F ⊗[F] E) a • (mt g - 1)) * (algebraMap (AF F) (AF F ⊗[F] E) b • (mt g - 1)) = 0 := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hab', zero_smul]
      unfold trunc
      simp only [add_mul, mul_add, one_mul, mul_one, hz, add_zero]
      abel
    rw [e, h3]
    abel
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    have hxa : (a + b) * a = a := by rw [add_mul, ha, hba, add_zero]
    have hyb : (a + b) * b = b := by rw [add_mul, hb, hab, zero_add]
    exact (suppGroup σ J (a + b)).mul_mem (SUSupp_mono hxa hx) (SUSupp_mono hyb hy)

end Group

section Compact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem isCompact_add {a b : AF F} (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0)
    (hca : IsCompact (SUSupp σ J a)) (hcb : IsCompact (SUSupp σ J b)) : IsCompact (SUSupp σ J (a + b)) := by
  haveI := topGroup σ J
  rw [SUSupp_add σ J ha hb hab]
  exact (hca.prod hcb).image continuous_mul

theorem isCompact_fin (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) :
    ∀ {δ : AF F}, IsPlacesIdem (∅ : Finset (InfinitePlace F)) T₂ δ →
      (∀ v ∈ T₂, ∀ e : AF F, IsPlacesIdem ∅ {v} e → IsCompact (SUSupp σ J e)) → IsCompact (SUSupp σ J δ) := by
  classical
  induction T₂ using Finset.induction_on with
  | empty =>
    intro δ hδ _
    rw [idem_empty hδ, SUSupp_zero_eq]
    exact isCompact_singleton
  | insert v T hv ih =>
    intro δ hδ hc
    obtain ⟨e, he⟩ := StrongApprox.exists_isPlacesIdem (F := F) ∅ {v}
    obtain ⟨d, hd⟩ := StrongApprox.exists_isPlacesIdem (F := F) ∅ T
    have h₁ : Disjoint (∅ : Finset (InfinitePlace F)) ∅ := Finset.disjoint_empty_left _
    have h₂ : Disjoint ({v} : Finset (HeightOneSpectrum (𝓞 F))) T := Finset.disjoint_singleton_left.2 hv
    have hδ' : IsPlacesIdem ((∅ : Finset (InfinitePlace F)) ∪ ∅) ({v} ∪ T) δ := by
      rwa [Finset.empty_union, ← Finset.insert_eq]
    rw [idem_add he hd h₁ h₂ hδ']
    exact isCompact_add (idem_self he) (idem_self hd) (idem_orth he hd h₁ h₂)
      (hc v (Finset.mem_insert_self v T) e he) (ih hd fun u hu => hc u (Finset.mem_insert_of_mem hu))

theorem isCompact_all (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (T₂ : Finset (HeightOneSpectrum (𝓞 F)))
    (h₂ : ∀ v ∈ T₂, ∀ e : AF F, IsPlacesIdem ∅ {v} e → IsCompact (SUSupp σ J e))
    (T₁ : Finset (InfinitePlace F)) :
    ∀ {δ : AF F}, IsPlacesIdem T₁ T₂ δ →
      (∀ w ∈ T₁, ∀ e : AF F, IsPlacesIdem {w} ∅ e → IsCompact (SUSupp σ J e)) → IsCompact (SUSupp σ J δ) := by
  classical
  induction T₁ using Finset.induction_on with
  | empty =>
    intro δ hδ _
    exact isCompact_fin σ J T₂ hδ h₂
  | insert w T hw ih =>
    intro δ hδ hc
    obtain ⟨e, he⟩ := StrongApprox.exists_isPlacesIdem (F := F) {w} ∅
    obtain ⟨d, hd⟩ := StrongApprox.exists_isPlacesIdem (F := F) T T₂
    have d₁ : Disjoint ({w} : Finset (InfinitePlace F)) T := Finset.disjoint_singleton_left.2 hw
    have d₂ : Disjoint (∅ : Finset (HeightOneSpectrum (𝓞 F))) T₂ := Finset.disjoint_empty_left _
    have hδ' : IsPlacesIdem ({w} ∪ T) ((∅ : Finset (HeightOneSpectrum (𝓞 F))) ∪ T₂) δ := by
      rwa [Finset.empty_union, ← Finset.insert_eq]
    rw [idem_add he hd d₁ d₂ hδ']
    exact isCompact_add (idem_self he) (idem_self hd) (idem_orth he hd d₁ d₂)
      (hc w (Finset.mem_insert_self w T) e he) (ih hd fun u hu => hc u (Finset.mem_insert_of_mem hu))

end Compact

theorem compact_of_singles : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    {T₁ : Finset (InfinitePlace F)} {T₂ : Finset (HeightOneSpectrum (𝓞 F))} {δ : AF F}, IsPlacesIdem T₁ T₂ δ →
    (∀ w ∈ T₁, ∀ e : AF F, IsPlacesIdem {w} ∅ e → IsCompact (SUSupp σ J e)) →
    (∀ v ∈ T₂, ∀ e : AF F, IsPlacesIdem ∅ {v} e → IsCompact (SUSupp σ J e)) → IsCompact (SUSupp σ J δ) := by
  intro F E _ _ _ _ _ σ _ M J T₁ T₂ δ hδ h₁ h₂
  exact isCompact_all σ J T₂ h₂ T₁ hδ h₁

end GlobalTheory.CompanionTheory.SaGen.CompactSingles

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicOfSplitIdempotent
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SaGen.IsoSplit

theorem hform_comb {R : Type} [CommRing R] {n : Type} [Fintype n] (c : R →+* R) (Jm : Matrix n n R)
    (a b a' b' : n → R) (s t p q : R) :
    Formalism.UG.hform c Jm (s • a + t • b) (p • a' + q • b') =
      c s * p * Formalism.UG.hform c Jm a a' + c s * q * Formalism.UG.hform c Jm a b' +
        c t * p * Formalism.UG.hform c Jm b a' + c t * q * Formalism.UG.hform c Jm b b' := by
  simp only [Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  ring

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hR_incV (K : Type) [CommRing K] [Algebra F K] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (p q : Fin M → E) :
    hR K σ J (incV K p) (incV K q) = inclR K (hf σ J p q) := by
  have hs : ∀ t : E, sigR K σ (inclR K t) = inclR K (σ t) := by
    intro t
    simp [sigR, inclR]
  simp only [hR, Formalism.UG.hform, hf, incV, JR, Matrix.map_apply, map_sum, map_mul, hs]

theorem hf_smul_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (p q : Fin M → E) (s : E) :
    hf σ J p (s • q) = s * hf σ J p q := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_orthogonal_pair [NumberField E] (σ : E →ₐ[F] E) (hσ : ∀ t, σ (σ t) = t) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hM : 2 ≤ M) (hJ : IsHermND σ J) :
    ∃ x y : Fin M → E, hf σ J x x ≠ 0 ∧ hf σ J y y ≠ 0 ∧ hf σ J x y = 0 ∧ hf σ J y x = 0 := by
  obtain ⟨P, d, -, hPd, -, hd⟩ := GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E)) two_ne_zero hσ
    (G := J.transpose) (fun a b => hJ.1 a b)
  have hd' := hd (by rw [Matrix.det_transpose]; exact hJ.2)
  have key : ∀ a b, hf σ J (fun k => P k b) (fun k => P k a) = Matrix.diagonal d a b := by
    intro a b
    rw [← hPd]
    simp only [hf, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [AlgHom.coe_toRingHom, RingHom.coe_coe]
    ring
  have hij : (⟨0, by omega⟩ : Fin M) ≠ ⟨1, by omega⟩ := by simp
  refine ⟨fun k => P k ⟨0, by omega⟩, fun k => P k ⟨1, by omega⟩, ?_, ?_, ?_, ?_⟩
  · rw [key, Matrix.diagonal_apply_eq]; exact hd' _
  · rw [key, Matrix.diagonal_apply_eq]; exact hd' _
  · rw [key, Matrix.diagonal_apply_ne _ hij.symm]
  · rw [key, Matrix.diagonal_apply_ne _ hij]

theorem isoAt_of_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (K : Type) [Field K] [Algebra F K] (e : K ⊗[F] E), e * e = e → e + sigR K σ e = 1 → e * sigR K σ e = 0 → IsoAt K σ J := by
  intro F E _ _ _ _ _ σ hcm M J hM hJ K _ _ e he hsum hprod
  have hσ : ∀ t, σ (σ t) = t := by
    intro t
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]
  obtain ⟨x, y, hx, hy, hxy, hyx⟩ := exists_orthogonal_pair σ hσ J hM hJ
  set c := sigR K σ with hc
  have hcc : c (c e) = e := by
    have h := congrArg c hsum
    rw [map_add, map_one] at h
    linear_combination h - hsum
  have hce : c e * c e = c e := by rw [← map_mul, he]
  refine ⟨e • incV K x + c e • incV K y,
    e • incV K ((hf σ J y y)⁻¹ • y) + c e • incV K ((hf σ J x x)⁻¹ • x), ?_, ?_⟩
  · change Formalism.UG.hform (sigR K σ) (JR K J) _ _ = 0
    rw [hform_comb]
    change c e * e * hR K σ J _ _ + c e * c e * hR K σ J _ _ + c (c e) * e * hR K σ J _ _ +
      c (c e) * c e * hR K σ J _ _ = 0
    simp only [hR_incV, hxy, hyx, map_zero, hcc]
    linear_combination (inclR K (hf σ J x x) + inclR K (hf σ J y y)) * hprod
  · change Formalism.UG.hform (sigR K σ) (JR K J) _ _ = 1
    rw [hform_comb]
    change c e * e * hR K σ J _ _ + c e * c e * hR K σ J _ _ + c (c e) * e * hR K σ J _ _ +
      c (c e) * c e * hR K σ J _ _ = 1
    simp only [hR_incV, hf_smul_right, hxy, hyx, mul_zero, map_zero, hcc, inv_mul_cancel₀ hx,
      inv_mul_cancel₀ hy, map_one]
    linear_combination he + hce + hsum

end GlobalTheory.CompanionTheory.SaGen.IsoSplit
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatSFiniteSpan
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem latS_finite_span {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] K'] :
    ∃ T : Finset (Formalism.Per6.BdRp l), (∀ t ∈ T, t ∈ latS K') ∧
      ∀ s ∈ latS K', ∃ a : Formalism.Per6.BdRp l → Wl l, s = ∑ t ∈ T, t * wB l (a t) := by
  have hfin : Module.Finite ℤ_[l] (integralClosure ℤ_[l] K') :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] K' (integralClosure ℤ_[l] K')
  have htow : IsScalarTower ℤ_[l] K' (Om l) := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l), IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] K']
    rfl)
  obtain ⟨b₀, hb₀⟩ := hfin.fg_top
  let ι : ↥(integralClosure ℤ_[l] K') → Formalism.Per6.BdRp l := fun b => rB l ((b : K') : Om l)
  let _ : Algebra (Wl l) (Formalism.Per6.BdRp l) := (wB l).toAlgebra
  have hsm : ∀ (a : Wl l) (x : Formalism.Per6.BdRp l), a • x = wB l a * x := fun a x => Algebra.smul_def a x
  let T : Finset (Formalism.Per6.BdRp l) := b₀.image ι
  let N : Submodule (Wl l) (Formalism.Per6.BdRp l) := Submodule.span (Wl l) (T : Set (Formalism.Per6.BdRp l))
  have hZ : ∀ c : ℤ_[l], rB l (algebraMap ℤ_[l] (Om l) c) =
      wB l (GroundTheory.PAdicHodge.IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l c) := by
    intro c
    have h := GroundTheory.PAdicHodge.IsPerfectoidField.algebraMap_padic_coe (K := ℂ_[l]) l c
    have h2 := (GroundTheory.PAdicHodge.algClToBdR l).commutes (c : ℚ_[l])
    exact h2.trans h
  have hιmul : ∀ x y, ι (x * y) = ι x * ι y := fun x y => by simp [ι]
  have hO : ∀ z, ι z ∈ N := by
    intro z
    have hz : z ∈ Submodule.span ℤ_[l] (b₀ : Set ↥(integralClosure ℤ_[l] K')) := hb₀ ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hx))
    | zero => simp [ι]
    | add x y _ _ hx hy =>
      have e : ι (x + y) = ι x + ι y := by simp [ι]
      rw [e]; exact N.add_mem hx hy
    | smul c x _ hx =>
      have e : ι (c • x) = (GroundTheory.PAdicHodge.IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l c) • ι x := by
        rw [hsm, ← hZ]
        have e2 : (((c • x : ↥(integralClosure ℤ_[l] K')) : K') : Om l) =
            algebraMap ℤ_[l] (Om l) c * ((x : K') : Om l) := by
          have : ((c • x : ↥(integralClosure ℤ_[l] K')) : K') = c • (x : K') := rfl
          rw [this, Algebra.smul_def, IntermediateField.coe_mul]
          exact congrArg (· * ((x : K') : Om l)) (IsScalarTower.algebraMap_apply ℤ_[l] K' (Om l) c).symm
        simp only [ι, e2, map_mul]
      rw [e]; exact N.smul_mem _ hx
  have hmul : N * N ≤ N := by
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨b', _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    change ι b * ι b' ∈ N
    rw [← hιmul]
    exact hO _
  have h1 : (1 : Formalism.Per6.BdRp l) ∈ N := by
    have := hO 1
    simpa [ι] using this
  have hint : ∀ b : ↥(integralClosure ℤ_[l] K'), IsIntegral ℤ_[l] ((b : K') : Om l) := fun b =>
    (isIntegral_algebraMap_iff (A := K') (B := Om l) (algebraMap K' (Om l)).injective).2 b.2
  have hS : ∀ x ∈ latS K', x ∈ N := by
    intro x hx
    unfold latS at hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | ⟨y, ⟨hyK, hyI⟩, rfl⟩
      · have := N.smul_mem a h1
        rwa [hsm, mul_one] at this
      · have hz : IsIntegral ℤ_[l] (⟨y, hyK⟩ : K') :=
          (isIntegral_algebraMap_iff (A := K') (B := Om l) (algebraMap K' (Om l)).injective).1 hyI
        exact hO ⟨⟨y, hyK⟩, hz⟩
    | zero => exact N.zero_mem
    | one => exact h1
    | add _ _ _ _ hx hy => exact N.add_mem hx hy
    | neg _ _ hx => exact N.neg_mem hx
    | mul _ _ _ _ hx hy => exact hmul (Submodule.mul_mem_mul hx hy)
  refine ⟨T, ?_, ?_⟩
  · intro t ht
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 ht
    exact rB_mem_latS K' (b : K').2 (hint b)
  · intro x hx
    obtain ⟨f, _, hf⟩ := Submodule.mem_span_finset.1 (hS x hx)
    exact ⟨f, by rw [← hf]; exact Finset.sum_congr rfl (fun t _ => by rw [hsm, mul_comm])⟩

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharacterInducedTied
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

namespace GlobalTheory.CompanionTheory.HLCMul

open Formalism.MainNotions.N Module

theorem char_mul {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K LL : FinExt l) (hcard : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1)
    (ν₁ ν₂ ν₃ : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1)) (χ₁ χ₂ : ↥(GK K) → ↥LL.1)
    (h₂ : ∀ g x, ν₂ g x = χ₂ g • x) (h₁ : ∀ g x, ν₁ g x = χ₁ g • x)
    (h₃ : ∀ g x, ν₃ g x = (χ₁ g * χ₂ g) • x)
    (J₁ J₂ : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ)
    (d₂ : IsDR (P.PD K) ν₂)
    (m₁ : ∀ τ a, multV (P.PD K) ν₁ τ a = if a = J₁ τ then 1 else 0)
    (m₂ : ∀ τ a, multV (P.PD K) ν₂ τ a = if a = J₂ τ then 1 else 0) :
    IsDR (P.PD K) ν₃ ∧ ∀ τ a, multV (P.PD K) ν₃ τ a = if a = J₁ τ + J₂ τ then 1 else 0 := by
  have hm : ∀ τ a, multV (P.PD K) ν₃ τ a = if a = J₁ τ + J₂ τ then 1 else 0 := by
    intro τ a
    have := GlobalTheory.TwistJump.multV_twist_char l P AI T K LL (Fin 1 → ↥LL.1) ν₁ ν₃ ν₂ χ₂ h₂
      (fun g x => by rw [h₃, h₁, smul_smul, mul_comm]) d₂ τ (J₂ τ) (m₂ τ) (a - J₂ τ)
    rw [sub_add_cancel] at this
    rw [this, m₁]
    simp only [sub_eq_iff_eq_add]
  refine ⟨?_, hm⟩
  haveI := K.2
  haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL _ ν₃).1
  have hc : Fintype.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 := by
    rw [← hcard, Nat.card_eq_fintype_card]
  have hone : ∀ τ, finrank ↥LL.1 ↥(DdRE (P.PD K) ν₃ τ) = 1 := by
    intro τ
    obtain ⟨hf, hle, -⟩ := (GlobalTheory.Per.Components.components_finrank l P AI T K LL _ ν₃).1 τ
    have hm1 := hm τ (J₁ τ + J₂ τ)
    rw [if_pos rfl, multV] at hm1
    have hfil : finrank ↥LL.1 ↥(FildR (P.PD K) ν₃ τ (J₁ τ + J₂ τ)) ≤ finrank ↥LL.1 ↥(DdRE (P.PD K) ν₃ τ) :=
      Submodule.finrank_mono (inf_le_left : FildR (P.PD K) ν₃ τ _ ≤ DdRE (P.PD K) ν₃ τ)
    simp only [finrank_fin_fun, finrank_self, Module.finrank_pi, Fintype.card_fin] at hle
    omega
  obtain ⟨e1, -⟩ := GlobalTheory.DeRhamSplit.finrank_DdR (P.PD K) ν₃ hc 0
  rw [IsDR, e1, Finset.sum_congr rfl fun τ _ => hone τ]
  simp [hc]

theorem repE_apply {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω Gw O) (LL' : FinExt l) (ψ : ↥Gw →* (↥LL'.1)ˣ) (g : ↥(GK Bw.Kw))
    (x : Fin 1 → ↥LL'.1) :
    Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ) g x = ((ψ (Bw.e.symm g) : (↥LL'.1)ˣ) : ↥LL'.1) • x := by
  ext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [LocBridge.repE, PositivityTheory.HodgeLocalCharacter.HLC.toGL1, Matrix.mulVec, dotProduct]

theorem isdRJ_mul : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 → ∀ (ψ₁ ψ₂ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ)
      (J₁ J₂ : (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) → ℤ),
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ₁ J₁ → PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ₂ J₂ →
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' (ψ₁ * ψ₂) (J₁ + J₂) := by
  rintro E Ω _ _ _ _ _ l _ P AI ⟨T⟩ w A _ O _ _ _ Bw _ LL' hLL ψ₁ ψ₂ J₁ J₂ ⟨-, m₁⟩ ⟨d₂, m₂⟩
  have hcard := GlobalTheory.DeRhamSplit.card_emb Bw.Kw LL' fun τ x => hLL (Bw.LL_split τ x)
  obtain ⟨a, b⟩ := char_mul P AI T Bw.Kw LL' hcard
    (Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ₁))
    (Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ₂))
    (Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp (ψ₁ * ψ₂)))
    (fun g => ((ψ₁ (Bw.e.symm g) : (↥LL'.1)ˣ) : ↥LL'.1)) (fun g => ((ψ₂ (Bw.e.symm g) : (↥LL'.1)ˣ) : ↥LL'.1))
    (fun g x => repE_apply Bw LL' ψ₂ g x) (fun g x => repE_apply Bw LL' ψ₁ g x)
    (fun g x => by rw [repE_apply]; simp) J₁ J₂
    (by unfold IsDR; simpa [LocBridge.IsdRE] using d₂) m₁ m₂
  refine ⟨?_, fun τ c => ?_⟩
  · unfold IsDR at a
    simpa [LocBridge.IsdRE] using a
  · simpa [LocBridge.multE] using b τ c

end GlobalTheory.CompanionTheory.HLCMul
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateTorsionApproximationStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_torsion_approximation : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B} {C : Type} [NormedField C] [IsUltrametricDist C], PerEnv S F ϖ →
    ∀ (θ : B →+* C), (∀ s ∈ S, ‖θ s‖ ≤ 1) → θ ϖ ≠ 0 → ‖θ ϖ‖ < 1 → ∀ (q : ℕ), 2 ≤ q → ‖(q : C)‖ ≤ ‖θ ϖ‖ →
    ∀ (v : ℕ → B), (∀ n, v n ∈ S) → ∀ (w : ℕ → C), w 0 = 0 → (∀ n, w (n + 1) ^ q + θ ϖ * w (n + 1) = w n) →
      (∀ n, ‖θ (v n) - w n‖ ≤ ‖θ ϖ‖) →
    ∀ Q ∈ S, (∀ n, ∃ a ∈ S, Q - ltIter ϖ q n (v n) = ϖ ^ (n + 1) * a) → θ Q = 0 := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.theta_eq_zero_of_congr_torsion | exact GlobalTheory.CompanionTheory.LTPer.theta_eq_zero_of_congr_torsion | (intros; apply GlobalTheory.CompanionTheory.LTPer.theta_eq_zero_of_congr_torsion <;> assumption)
end
end

