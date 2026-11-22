import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0006
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.Master
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0162
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0157
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugateUniversalFamily
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.BallVolMoeb
section
noncomputable section

namespace SheetDecomposition

open NumberField Matrix MeasureTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict
  GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas PositivityTheory.EqVol

namespace Moeb

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

theorem sgI_sq : sgI j j' * sgI j j' = 1 := by
  simp [sgI, fromBlocks_multiply]

theorem sgI_ct : (sgI j j')ᴴ = sgI j j' := by
  simp [sgI, fromBlocks_conjTranspose]

def sinv (u : Matrix (Sg j j') (Sg j j') ℂ) : Matrix (Sg j j') (Sg j j') ℂ := sgI j j' * uᴴ * sgI j j'

theorem sinv_mul {u : Matrix (Sg j j') (Sg j j') ℂ} (h : IsSgU u) : sinv u * u = 1 := by
  unfold IsSgU at h
  rw [sinv, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ, h, sgI_sq]

theorem mul_sinv {u : Matrix (Sg j j') (Sg j j') ℂ} (h : IsSgU u) : u * sinv u = 1 :=
  mul_eq_one_comm.1 (sinv_mul h)

theorem sinv_su {u : Matrix (Sg j j') (Sg j j') ℂ} (h : IsSgU u) : IsSgU (sinv u) := by
  have h1 := mul_sinv h
  unfold IsSgU at h ⊢
  conv_lhs => rw [← h]
  have : (sinv u)ᴴ * (uᴴ * sgI j j' * u) * sinv u = (u * sinv u)ᴴ * sgI j j' * (u * sinv u) := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [this, h1]
  simp

theorem moeb_one (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : moebBall q (fun _ => 1) t = t := by
  funext k
  have : ∀ W : Matrix (Fin j') (Fin j) ℂ, moebW (1 : Matrix (Sg j j') (Sg j j') ℂ) W = W := fun W => by
    rw [moebW, ← fromBlocks_one, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
    simp
  simp [moebBall, ballPt, this, ballMat]

theorem moeb_maps (q : Ψ × Fin j × Fin j' ≃ Fin n) {u : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ))
    {t : Fin n → ℂ} (ht : t ∈ ballDom q) : moebBall q u t ∈ ballDom q :=
  (GlobalTheory.T.ball_mobius_holomorphic_potential_change Ψ j j' n q u hu).2.1 ht

theorem moeb_mul (q : Ψ × Fin j × Fin j' ≃ Fin n) {u v w : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ))
    (hv : ∀ τ, IsSgU (v τ)) (hw : ∀ τ, u τ * v τ = w τ) {t : Fin n → ℂ} (ht : t ∈ ballDom q) :
    moebBall q u (moebBall q v t) = moebBall q w t := by
  rw [← GlobalTheory.T.ball_mobius_mul Ψ j j' n q u v hu hv t ht, funext hw]

theorem moeb_inv (q : Ψ × Fin j × Fin j' ≃ Fin n) {u v : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ))
    (hv : ∀ τ, IsSgU (v τ)) (hw : ∀ τ, u τ * v τ = 1) {t : Fin n → ℂ} (ht : t ∈ ballDom q) :
    moebBall q u (moebBall q v t) = t :=
  (moeb_mul q hu hv hw ht).trans (moeb_one q t)

theorem moeb_injOn (q : Ψ × Fin j × Fin j' ≃ Fin n) {u : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ)) :
    Set.InjOn (moebBall q u) (ballDom q) := fun t ht t' ht' h => by
  rw [← moeb_inv q (fun τ => sinv_su (hu τ)) hu (fun τ => sinv_mul (hu τ)) ht, h,
    moeb_inv q (fun τ => sinv_su (hu τ)) hu (fun τ => sinv_mul (hu τ)) ht']

theorem moeb_meas (q : Ψ × Fin j × Fin j' ≃ Fin n) {u : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ))
    {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) (hSD : S ⊆ ballDom q) :
    MeasurableSet (moebBall q u '' S) ∧ ballMeas q (moebBall q u '' S) = ballMeas q S := by
  obtain ⟨h1, h2, G, h3, h4⟩ := GlobalTheory.T.ball_mobius_holomorphic_potential_change Ψ j j' n q u hu
  exact ⟨hS.image_of_continuousOn_injOn (h1.continuousOn.mono hSD) ((moeb_injOn q hu).mono hSD),
    ballMeas_image q h1 h2 (moeb_injOn q hu) (fun t ht => ballDens_transform q h1 h3 h2 h4 ht) hS hSD⟩

def ren (q q' : Ψ × Fin j × Fin j' ≃ Fin n) : (Fin n → ℂ) ≃ᵐ (Fin n → ℂ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℂ) (q'.symm.trans q)

theorem ren_apply (q q' : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (x : Ψ × Fin j × Fin j') :
    ren q q' t (q x) = t (q' x) := by
  have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℂ) (q'.symm.trans q) t (q' x)
  simpa [ren] using this

theorem ballMat_ren (q q' : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : ballMat q (ren q q' t) = ballMat q' t := by
  funext τ
  ext a b
  simp [ballMat, ren_apply]

theorem ren_mem (q q' : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : ren q q' t ∈ ballDom q ↔ t ∈ ballDom q' := by
  simp only [ballDom, Set.mem_setOf_eq, ballMat_ren]

theorem moeb_ren (q q' : Ψ × Fin j × Fin j' ≃ Fin n) (u : Ψ → Matrix (Sg j j') (Sg j j') ℂ) (t : Fin n → ℂ) :
    moebBall q u (ren q q' t) = ren q q' (moebBall q' u t) := by
  funext k
  obtain ⟨x, rfl⟩ := q.surjective k
  rw [ren_apply]
  simp [moebBall, ballPt, ballMat_ren]

theorem ren_meas (q q' : Ψ × Fin j × Fin j' ≃ Fin n) {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) (hSD : S ⊆ ballDom q') :
    ballMeas q (ren q q' '' S) = ballMeas q' S := by
  have hm : MeasurePreserving (ren q q') volume volume := volume_measurePreserving_piCongrLeft (fun _ => ℂ) _
  rw [ballMeas_apply q ((ren q q').measurableSet_image.2 hS) (by rintro _ ⟨t, ht, rfl⟩; exact (ren_mem q q' t).2 (hSD ht)),
    ballMeas_apply q' hS hSD, ← hm.setLIntegral_comp_emb (ren q q').measurableEmbedding]
  simp only [ballDens, ballPot, ballMat_ren]

theorem core (q : Ψ × Fin j × Fin j' ≃ Fin n) {G : Type} [Group G] [Countable G]
    (ρ : G → Ψ → Matrix (Sg j j') (Sg j j') ℂ) (U Γ Γ' : Subgroup G) (S S' : Set (Fin n → ℂ)) (h1 : ∀ τ, ρ 1 τ = 1)
    (hm : ∀ x y τ, ρ (x * y) τ = ρ x τ * ρ y τ) (hU : ∀ γ ∈ U, ∀ τ, IsSgU (ρ γ τ)) (hΓ : Γ ≤ U) (hΓ' : Γ' ≤ U)
    (hI : EqIdx Γ Γ') (hS : MFund q ρ Γ S) (hS' : MFund q ρ Γ' S') : ballMeas q S = ballMeas q S' := by
  have hD : MeasurableSet (ballDom q) := (BallInverse.isOpen_ballDom q).measurableSet
  have hemb : MeasurableEmbedding (Subtype.val : ballDom q → Fin n → ℂ) := MeasurableEmbedding.subtype_coe hD
  letI act : MulAction U (ballDom q) :=
    { smul := fun γ t => ⟨moebBall q (ρ γ) t, moeb_maps q (hU γ γ.2) t.2⟩
      one_smul := fun t => Subtype.ext (by
        show moebBall q (ρ 1) t = t
        rw [funext h1, moeb_one])
      mul_smul := fun a b t => Subtype.ext
        (moeb_mul q (hU a a.2) (hU b b.2) (fun τ => (hm a b τ).symm) t.2).symm }
  have sm : ∀ (γ : U) (t : ballDom q), ((γ • t : ballDom q) : Fin n → ℂ) = moebBall q (ρ γ) t := fun _ _ => rfl
  haveI : MeasurableConstSMul U (ballDom q) := ⟨fun γ =>
    (Continuous.subtype_mk (continuousOn_iff_continuous_restrict.1
      (GlobalTheory.T.ball_mobius_holomorphic_potential_change Ψ j j' n q (ρ γ) (hU γ γ.2)).1.continuousOn) _).measurable⟩
  let μ : Measure (ballDom q) := (ballMeas q).comap Subtype.val
  have hμ : ∀ s, μ s = ballMeas q (Subtype.val '' s) := fun s => hemb.comap_apply _ s
  haveI : SMulInvariantMeasure U (ballDom q) μ := ⟨fun γ s hs => by
    rw [hμ, hμ, ← (moeb_meas q (hU _ (γ⁻¹).2) (hemb.measurableSet_image.2 hs) (Subtype.coe_image_subset _ _)).2]
    congr 1
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨γ • x, hx, rfl⟩, by rw [← sm, inv_smul_smul]⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨γ⁻¹ • x, by simpa using hx, rfl⟩⟩
  have fd : ∀ (Γ : Subgroup G) (S : Set (Fin n → ℂ)), Γ ≤ U → MFund q ρ Γ S →
      IsFundamentalDomain (Γ.subgroupOf U) (Subtype.val ⁻¹' S : Set (ballDom q)) μ ∧
        μ (Subtype.val ⁻¹' S) = ballMeas q S := fun Γ S hΓ ⟨a1, a2, a3, a4⟩ => by
    refine ⟨IsFundamentalDomain.mk' (hemb.measurable a1).nullMeasurableSet fun x => ?_, ?_⟩
    · obtain ⟨γ, hγ, h⟩ := a3 x x.2
      refine ⟨⟨⟨γ, hΓ hγ⟩, hγ⟩, h, fun g hg => ?_⟩
      have e : (g.1 * (⟨γ, hΓ hγ⟩ : U)⁻¹) • ((⟨γ, hΓ hγ⟩ : U) • x) = g.1 • x := by
        rw [← mul_smul, inv_mul_cancel_right]
      have := a4 _ h (g.1.1 * γ⁻¹) (Γ.mul_mem g.2 (Γ.inv_mem hγ)) (by
        have e' := congrArg Subtype.val e
        rw [sm, sm, sm] at e'
        exact e' ▸ hg)
      exact Subtype.ext (Subtype.ext (mul_inv_eq_one.1 this))
    · rw [hμ, Subtype.image_preimage_coe, Set.inter_eq_right.2 a2]
  obtain ⟨a₁, b₁⟩ := fd Γ S hΓ hS
  obtain ⟨a₂, b₂⟩ := fd Γ' S' hΓ' hS'
  rw [← b₁, ← b₂]
  exact fdEqual _ _ μ _ _ _ _
    (by rw [Subgroup.relIndex_subgroupOf hΓ, Subgroup.relIndex_subgroupOf hΓ']; exact hI.1)
    (by rw [Subgroup.relIndex_subgroupOf hΓ']; exact hI.2) a₁ a₂

end Moeb

open Moeb

theorem moebVol : MoebVol := by
  intro Ψ _ j j' n q q' G _ _ ρ ρ' w U Γ Γ' a S S' h1 hm hU hU' hw hc hΓ hΓ' hI hS ⟨b1, b2, b3, b4⟩
  have r1 : MeasurableSet (ren q q' '' S') := (ren q q').measurableSet_image.2 b1
  have r2 : ren q q' '' S' ⊆ ballDom q := by
    rintro _ ⟨t, ht, rfl⟩
    exact (ren_mem q q' t).2 (b2 ht)
  obtain ⟨m1, m2⟩ := moeb_meas q hw r1 r2
  have key : ∀ γ ∈ Γ', ∀ t ∈ ballDom q', moebBall q (ρ (a * γ * a⁻¹)) (moebBall q w (ren q q' t)) =
      moebBall q w (ren q q' (moebBall q' (ρ' γ) t)) := fun γ hγ t ht => by
    have ht' := (ren_mem q q' t).2 ht
    rw [← moeb_ren, moeb_mul q (hU (a * γ * a⁻¹) (hΓ' ⟨γ, hγ, rfl⟩)) hw (fun _ => rfl) ht',
      moeb_mul q hw (hU' γ hγ) (hc γ) ht']
  rw [← ren_meas q q' b1 b2, ← m2]
  refine core q ρ U Γ _ S _ h1 hm hU hΓ hΓ' hI hS ⟨m1, ?_, fun t ht => ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact moeb_maps q hw (r2 ht)
  · have hi := fun τ => sinv_su (hw τ)
    obtain ⟨s, hs⟩ := (ren q q').surjective (moebBall q (fun τ => sinv (w τ)) t)
    have hs' : s ∈ ballDom q' := (ren_mem q q' s).1 (hs ▸ moeb_maps q hi ht)
    obtain ⟨γ, hγ, h⟩ := b3 s hs'
    refine ⟨a * γ * a⁻¹, ⟨γ, hγ, rfl⟩, _, ⟨_, h, rfl⟩, ?_⟩
    rw [← key γ hγ s hs', hs, moeb_inv q hw hi (fun τ => mul_sinv (hw τ)) ht]
  · rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩ _ ⟨γ, hγ, rfl⟩ ⟨_, ⟨s, hs, rfl⟩, e⟩
    replace e : moebBall q w (ren q q' s) = moebBall q (ρ (a * γ * a⁻¹)) (moebBall q w (ren q q' t)) := e
    rw [key γ hγ t (b2 ht)] at e
    have e2 := (ren q q').injective (moeb_injOn q hw ((ren_mem q q' _).2 (b2 hs))
      ((ren_mem q q' _).2 (moeb_maps q' (hU' γ hγ) (b2 ht))) e)
    obtain rfl := b4 t ht γ hγ (e2 ▸ hs)
    exact map_one _

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.BallVolRed
section
noncomputable section

namespace SheetDecomposition

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas
  GlobalTheory.CompanionTheory.Ar.Cusp.ConjFam
open scoped ComplexOrder

section Ball

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n)

def permQ (π : Ψ ≃ Ψ) : Ψ × Fin j × Fin j' ≃ Fin n := (π.prodCongr (Equiv.refl _)).trans q

theorem ballDom_permQ (π : Ψ ≃ Ψ) : ballDom (permQ q π) = ballDom q :=
  Set.ext fun t => ⟨fun h τ => by
    obtain ⟨τ, rfl⟩ := π.surjective τ
    exact h τ, fun h τ => h (π τ)⟩

theorem ballPot_permQ (π : Ψ ≃ Ψ) (t : Fin n → ℂ) : ballPot (permQ q π) t = ballPot q t :=
  congrArg Neg.neg (π.sum_comp fun τ => Real.log (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det.re)

theorem ballMeas_permQ (π : Ψ ≃ Ψ) : ballMeas (permQ q π) = ballMeas q := by
  simp only [ballMeas, ballDens, ballDom_permQ, ballPot_permQ]

theorem star_measurePreserving : MeasurePreserving (star : (Fin n → ℂ) → Fin n → ℂ) volume volume :=
  volume_preserving_pi (f := fun _ => Complex.conjLIE) fun _ => Complex.conjLIE.measurePreserving

theorem ballMeas_star {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) (hD : S ⊆ ballDom q) :
    ballMeas q (star ⁻¹' S) = ballMeas q S := by
  have hemb : MeasurableEmbedding (star : (Fin n → ℂ) → Fin n → ℂ) :=
    (Homeomorph.mk ⟨star, star, star_star, star_star⟩ continuous_star continuous_star).measurableEmbedding
  rw [ballMeas_apply q hS hD, ballMeas_apply q (hemb.measurable hS)
    (fun t ht => by simpa using star_mem_ballDom (hD ht)),
    ← star_measurePreserving.setLIntegral_comp_preimage_emb hemb _ S]
  simp only [ballDens, ballPot_star]

theorem integral_ballDens {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) (hD : S ⊆ ballDom q) :
    ∫ t in S, ballDens q t = (ballMeas q S).toReal := by
  rw [ballMeas_apply q hS hD]
  exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)
    (DictMeas.measurable_ballDens q).aestronglyMeasurable

end Ball

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ]

def permFam (F : UnivFam E Ψ j j' n g Λ) (π : Ψ ≃ Ψ) : UnivFam E Ψ j j' n g Λ where
  q := permQ F.q π
  σ τ := F.σ (π τ)
  cm := ⟨F.cm.1.comp π.injective, fun s => by
    rw [π.exists_congr_right (q := fun τ => F.σ τ = s),
      π.exists_congr_right (q := fun τ => F.σ τ = (starRingEnd ℂ).comp s)]
    exact F.cm.2 s⟩
  form := F.form
  R := F.R
  form_eq := F.form_eq
  hol := by rw [ballDom_permQ]; exact F.hol
  sig t ht τ := F.sig t (ballDom_permQ F.q π ▸ ht) (π τ)
  b τ := F.b (π τ)
  frames := by
    rw [ballDom_permQ]
    exact ⟨fun τ => F.frames.1 (π τ), fun t ht τ => F.frames.2 t ht (π τ)⟩
  logDet_eq t ht := by
    rw [ballPot_permQ, ← F.logDet_eq t (ballDom_permQ F.q π ▸ ht)]
    exact π.sum_comp fun τ => Real.log ((F.R t).gram fun i => F.b τ i t).det.re
  univ R' hf hs := by
    rw [ballDom_permQ]
    exact F.univ R' hf fun τ => by
      obtain ⟨τ, rfl⟩ := π.surjective τ
      exact hs τ

theorem permFam_fund {F : UnivFam E Ψ j j' n g Λ} (π : Ψ ≃ Ψ) {Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)} {FF : Set (Fin n → ℂ)}
    (h : F.IsFundSet Γ FF) : (permFam F π).IsFundSet Γ FF := by
  have e : ballDom (permFam F π).q = ballDom F.q := ballDom_permQ F.q π
  unfold UnivFam.IsFundSet
  rw [e]
  exact h

theorem conjFam_fund {F : UnivFam E Ψ j j' n g Λ} {Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)} {FF : Set (Fin n → ℂ)}
    (h : F.IsFundSet Γ FF) : (conjFam F).IsFundSet Γ (star ⁻¹' FF) := by
  refine ⟨continuous_star.measurable h.1, fun t ht => ?_, fun t ht => ?_, fun t ht t' ht' ⟨γ, hγ, he⟩ => ?_⟩
  · show t ∈ ballDom F.q
    simpa using star_mem_ballDom (h.2.1 ht)
  · obtain ⟨t', ht', γ, hγ, he⟩ := h.2.2.1 (star t) (star_mem_ballDom (q := F.q) ht)
    refine ⟨star t', by simpa using ht', γ, hγ, eqvBy_conj (fun x => rfl) (fun x => ?_) he⟩
    show star ((F.R (star (star t'))).P x) = _
    rw [star_star]
  · refine star_injective (h.2.2.2 _ ht _ ht' ⟨γ, hγ, eqvBy_conj (fun x => ?_) (fun x => ?_) he⟩)
    · exact (star_star _).symm
    · exact (star_star _).symm

theorem normalise (F : UnivFam E Ψ j j' n g Λ) (r : 𝓞 E) (d : ℕ) (hr : r ^ 2 = -(d : 𝓞 E))
    (hc : ∀ τ τ', F.σ τ r = F.σ τ' r) {Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)} {FF : Set (Fin n → ℂ)} (h : F.IsFundSet Γ FF) :
    ∃ (F₁ : UnivFam E Ψ j j' n g Λ) (FF₁ : Set (Fin n → ℂ)), (∀ τ, F₁.σ τ r = Complex.I * ((Real.sqrt d : ℝ) : ℂ)) ∧
      (F₁.form = F.form ∨ F₁.form = -F.form) ∧ F₁.IsFundSet Γ FF₁ ∧ ballMeas F₁.q FF₁ = ballMeas F.q FF := by
  by_cases h0 : ∀ τ, F.σ τ r = Complex.I * ((Real.sqrt d : ℝ) : ℂ)
  · exact ⟨F, FF, h0, Or.inl rfl, h, rfl⟩
  · obtain ⟨τ₀, h1⟩ := not_forall.1 h0
    have h2 : F.σ τ₀ r ^ 2 = (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) ^ 2 := by
      rw [← map_pow, hr, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
      simp
    have h3 := (sq_eq_sq_iff_eq_or_eq_neg.1 h2).resolve_left h1
    refine ⟨conjFam F, star ⁻¹' FF, fun τ => ?_, Or.inr rfl, conjFam_fund h, ballMeas_star F.q h.1 h.2.1⟩
    show starRingEnd ℂ (F.σ τ r) = _
    rw [hc τ τ₀, h3]
    simp

omit [NumberField E] [IsCMField E] in
theorem exists_perm {σ σ' : Ψ → (𝓞 E →+* ℂ)} (h : IsCMFam σ) (h' : IsCMFam σ') (r : 𝓞 E) {c : ℝ} (hc : 0 < c)
    (hs : ∀ τ, σ τ r = Complex.I * (c : ℂ)) (hs' : ∀ τ, σ' τ r = Complex.I * (c : ℂ)) :
    ∃ π : Ψ ≃ Ψ, ∀ τ, σ' (π τ) = σ τ := by
  have : ∀ τ, ∃ τ', σ' τ' = σ τ := fun τ => (h'.2 _).2 fun ⟨τ', e⟩ => by
    have e1 := hs' τ'
    rw [e, RingHom.comp_apply, hs] at e1
    have := congrArg Complex.im e1
    simp at this
    linarith
  choose f hf using this
  have hi : Function.Injective f := fun a b e => h.1 (by rw [← hf, ← hf, e])
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hi), hf⟩

theorem label_rt {H : Host E} {l : Level H} (c : Coeff l) (τ τ' : CMType H) :
    labelEmb c (.inr τ) H.rt = labelEmb c (.inr τ') H.rt := by
  refine Subtype.ext ?_
  show τ.1 ((H.bar H.rt : 𝓞 E) : E) = τ'.1 ((H.bar H.rt : 𝓞 E) : E)
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, IsCMField.complexEmbedding_complexConj, τ.2, τ'.2]

theorem ballVolEq_of (h : FamVol) : BallVolEq := by
  intro _ E _ _ _ _ H D l Xo c Y n B FF hq hp hF k k'
  have hn := fun k => normalise (B.F k) H.rt H.d H.rt_sq
    (fun τ τ' => by rw [B.σ_eq, B.σ_eq, RingHom.comp_apply, RingHom.comp_apply, label_rt c τ τ']) (hF k)
  obtain ⟨F₁, FF₁, s₁, f₁, u₁, m₁⟩ := hn k
  obtain ⟨F₂, FF₂, s₂, f₂, u₂, m₂⟩ := hn k'
  have hd : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (Nat.cast_pos.2 H.d_prime.pos)
  obtain ⟨π, hπ⟩ := exists_perm F₁.cm F₂.cm H.rt hd s₁ s₂
  have hf : ∀ k (f : _ →ₗ[ℤ] _ →ₗ[ℤ] ℤ), (f = (B.F k).form ∨ f = -(B.F k).form) → f = (B.Di k).EF ∨ f = -(B.Di k).EF := by
    intro k f hf
    rcases hf with rfl | rfl <;> rcases B.form_eq k with e | e <;> rw [e] <;> simp
  have key := h E H l (B.Di k) (B.Di k') (CMType H) D.p D.q n B.g F₁ (permFam F₂ π) (B.Γ k) (B.Γ k') FF₁ FF₂ _
    (by omega) (by omega) (by omega) hd (funext hπ) s₁ (hf k _ f₁) (hf k' _ f₂) (B.mem_Γ k) (B.mem_Γ k') u₁
    (permFam_fund π u₂)
  rw [integral_ballDens _ (hF k).1 (hF k).2.1, integral_ballDens _ (hF k').1 (hF k').2.1, ← m₁, ← m₂, key]
  exact congrArg (fun μ : Measure (Fin n → ℂ) => (μ FF₂).toReal) (ballMeas_permQ F₂.q π)

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushDim
section
noncomputable section

namespace SheetDecomposition

open ReciprocityTheory.ChartRestriction.G
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR

section

variable (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]

omit [Fintype K] [∀ b, Fintype (ι b)] in
theorem fnField_toSubfield (y : (Σ b, ι b) → Ω) :
    (fnField k y).toSubfield = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y := by
  rw [fnField, IntermediateField.adjoin_toSubfield]
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField
  congr 2
  ext t
  constructor
  · rintro ⟨p, q, hpq, rfl⟩
    obtain ⟨a, i⟩ := p
    obtain ⟨b, j⟩ := q
    simp only at hpq
    subst hpq
    exact ⟨⟨a, i, j⟩, rfl⟩
  · rintro ⟨⟨a, i, j⟩, rfl⟩
    exact ⟨⟨a, i⟩, ⟨a, j⟩, rfl, rfl⟩

theorem trdeg_eq_of_finite (A : IntermediateField k Ω) [FiniteDimensional A Ω] : Algebra.trdeg k A = Algebra.trdeg k Ω := by
  rw [← trdeg_add_eq k A (A := Ω), trdeg_eq_zero (R := A) (A := Ω), add_zero]

theorem krull_pointIdeal (y : (Σ b, ι b) → Ω) (d : ℕ) (h : IsPt k y d) [(pointIdeal k y).IsPrime] :
    ringKrullDim (MRing ι k ⧸ pointIdeal k y) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  obtain ⟨hnz, hfin, htr⟩ := h
  have hcone := ConeTrdegFnField.proof k Ω (algebraMap k Ω).injective K ι y hnz
  have hset : ((IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y : Subfield Ω) : Set Ω) = ((fnField k y : IntermediateField k Ω) : Set Ω) := by
    rw [← fnField_toSubfield k y]
    rfl
  have hadj : Algebra.trdeg k (Algebra.adjoin k ((IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y : Subfield Ω) : Set Ω)) = Algebra.trdeg k (fnField k y) := by
    rw [hset]
    have : Algebra.adjoin k ((fnField k y : IntermediateField k Ω) : Set Ω) = (fnField k y).toSubalgebra :=
      Algebra.adjoin_eq (fnField k y).toSubalgebra
    rw [this]
    rfl
  haveI : FiniteDimensional (fnField k y) Ω := hfin
  have htr' : Algebra.trdeg k (MRing ι k ⧸ pointIdeal k y) = ((d + Fintype.card K : ℕ) : Cardinal) := by
    have e : Algebra.trdeg k (MRing ι k ⧸ pointIdeal k y) = Algebra.trdeg k (Algebra.adjoin k ((IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y : Subfield Ω) : Set Ω)) + (Fintype.card K : Cardinal) := hcone
    rw [e, hadj, trdeg_eq_of_finite k (fnField k y), htr]
    push_cast
    rfl
  exact ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field (d + Fintype.card K) htr'

end

theorem ptDim : PtDim := by
  intro k _ Ω _ _ K _ ι _ y d h
  classical
  have hmp : IsMultiProjPrime (pointIdeal k y) := PointIdealMultiProj.proof k Ω K ι y h.1
  have hdim := krull_pointIdeal k y d h
  refine ⟨?_, ?_, ?_⟩
  · convert hmp
  · unfold FieldNumbers.relDim
    rw [hdim]
    have e : (((d + Fintype.card K : ℕ) : ℤ) - (Fintype.card K : ℤ)) = (d : ℤ) := by
      push_cast
      ring
    change (WithBot.some (WithTop.some (((d + Fintype.card K : ℕ) : ℤ) - (Fintype.card K : ℤ))) : WithBot (WithTop ℤ)) = ((d : ℤ) : WithBot (WithTop ℤ))
    rw [e]
    rfl
  · refine ⟨?_, hdim⟩
    exact (Bridge.isMultiProjPrime_iff _).1 hmp

end SheetDecomposition
end
end

