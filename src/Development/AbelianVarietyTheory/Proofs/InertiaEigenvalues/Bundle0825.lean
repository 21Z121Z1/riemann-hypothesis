import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0057
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorValuedLiftFieldChange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0169
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0814
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0194
import Formalism.LocalRingCardinality.SpanPowerMembership.PlOver
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsRealisesNeOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0818
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0816
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLocGaloisFactorsThrough
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0819
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBasisAtTransport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoefLatIso

open MvPolynomial

theorem mem_localization_comap_iff {R R' W W' : Type} [CommRing R] [CommRing R'] [AddCommGroup W] [Module R W]
    [AddCommGroup W'] [Module R' W'] (φ : R ≃+* R') (f : W → W') (hf : ∀ (r : R) x, f (r • x) = φ r • f x)
    (p : Ideal R') [p.IsPrime] (L : Submodule R W) (L' : Submodule R' W') (hL : ∀ x, f x ∈ L' ↔ x ∈ L) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ (p.comap (φ : R →+* R')) L ↔ f x ∈ Formalism.HermitianLatticesTheory.localization₂ p L' := by
  show (∃ s ∈ (p.comap (φ : R →+* R')).primeCompl, s • x ∈ L) ↔ ∃ s ∈ p.primeCompl, s • f x ∈ L'
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨φ s, ?_, ?_⟩
    · rw [Ideal.mem_primeCompl_iff] at hs ⊢
      exact hs
    · rw [← hf]; exact (hL _).2 h
  · rintro ⟨s, hs, h⟩
    refine ⟨φ.symm s, ?_, ?_⟩
    · rw [Ideal.mem_primeCompl_iff] at hs ⊢
      rw [Ideal.mem_comap]
      simpa using hs
    · rw [← hL, hf, RingEquiv.apply_symm_apply]; exact h

section Fields

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (e : K' ≃+* K)

abbrev vmE (n : ℕ) : (Fin n → K') ≃+ (Fin n → K) := AddEquiv.piCongrRight fun _ : Fin n => e.toAddEquiv

theorem vmE_apply (n : ℕ) (x : Fin n → K') (a : Fin n) : vmE e n x a = e (x a) := rfl

theorem vmE_smul (n : ℕ) (r : 𝓞 K') (x : Fin n → K') :
    vmE e n (r • x) = RingOfIntegers.mapRingEquiv e r • vmE e n x :=
  funext fun i => GlobalTheory.IdealTransport.map_smul_int e r (x i)

theorem mem_span_vmE_iff {n : ℕ} (S : Set (Fin n → K')) (x : Fin n → K') :
    vmE e n x ∈ Submodule.span (𝓞 K) (vmE e n '' S) ↔ x ∈ Submodule.span (𝓞 K') S := by
  rw [← GlobalTheory.IdealTransport.span_image_span (RingOfIntegers.mapRingEquiv e) (vmE e n) (vmE_smul e n),
    GlobalTheory.IdealTransport.mem_span_image (RingOfIntegers.mapRingEquiv e) (vmE e n) (vmE_smul e n),
    AddEquiv.symm_apply_apply]

theorem mem_tauLat_iff {E : Type} [Field E] [NumberField E] {ι : Type} {n : ℕ} (emb : ι → E →+* K')
    (emb2 : ι → E →+* K) (h : ∀ τ, emb2 τ = e.toRingHom.comp (emb τ)) (τ : ι)
    (M : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → K') :
    vmE e n x ∈ tauLat emb2 τ M ↔ x ∈ tauLat emb τ M := by
  have h2 : tauLat emb2 τ M =
      Submodule.span (𝓞 K) (vmE e n '' ((fun (y : Fin n → E) (a : Fin n) => emb τ (y a)) '' (M : Set (Fin n → E)))) := by
    rw [Set.image_image]
    unfold tauLat
    congr 1
    refine Set.image_congr fun y _ => funext fun a => ?_
    rw [h]; rfl
  rw [h2, mem_span_vmE_iff]
  rfl

theorem mem_dualFr' {F : Type} [Field F] [NumberField F] {n : ℕ} (L : Submodule (𝓞 F) (Fin n → F)) (y : Fin n → F) :
    y ∈ dualFr L ↔ ∀ x ∈ L, y ⬝ᵥ x ∈ (1 : Submodule (𝓞 F) F) := Iff.rfl

theorem map_mem_one_iff (a : K') : e a ∈ (1 : Submodule (𝓞 K) K) ↔ a ∈ (1 : Submodule (𝓞 K') K') := by
  simp only [Submodule.mem_one]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨(RingOfIntegers.mapRingEquiv e).symm r, e.injective ?_⟩
    rw [← hr]
    change e (e.symm (r : K)) = (r : K)
    exact e.apply_symm_apply _
  · rintro ⟨r, rfl⟩
    exact ⟨RingOfIntegers.mapRingEquiv e r, rfl⟩

theorem mem_dualFr_iff {n : ℕ} (L : Submodule (𝓞 K') (Fin n → K')) (L2 : Submodule (𝓞 K) (Fin n → K))
    (hL : ∀ x, vmE e n x ∈ L2 ↔ x ∈ L) (y : Fin n → K') : vmE e n y ∈ dualFr L2 ↔ y ∈ dualFr L := by
  have hd : ∀ x : Fin n → K', vmE e n y ⬝ᵥ vmE e n x = e (y ⬝ᵥ x) := fun x => by
    simp only [dotProduct, map_sum, map_mul, vmE_apply]
  rw [mem_dualFr', mem_dualFr']
  constructor
  · intro hy x hx
    rw [← map_mem_one_iff e, ← hd]
    exact hy _ ((hL x).2 hx)
  · intro hy x2 hx2
    obtain ⟨x, rfl⟩ := (vmE e n).surjective x2
    rw [hd, map_mem_one_iff]
    exact hy x ((hL x).1 hx2)

theorem mem_colLat_iff {n : ℕ} (B : GL (Fin n) K) (x : Fin n → K') :
    vmE e n x ∈ colLat B ↔ x ∈ colLat (Matrix.GeneralLinearGroup.map e.symm.toRingHom B) := by
  have h : colLat B = Submodule.span (𝓞 K) (vmE e n '' Set.range fun j : Fin n => fun a : Fin n =>
      ((Matrix.GeneralLinearGroup.map e.symm.toRingHom B : GL (Fin n) K') : Matrix (Fin n) (Fin n) K') a j) := by
    unfold colLat
    rw [← Set.range_comp]
    congr 1
    congr 1
    funext j a
    simp only [Function.comp_apply, vmE_apply]
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact (e.apply_symm_apply _).symm
  rw [h, mem_span_vmE_iff]
  unfold colLat
  rfl

theorem isBasisAt_transport {n : ℕ} (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K') (Fin n → K'))
    (M2 : Submodule (𝓞 K) (Fin n → K)) (hM : ∀ x, vmE e n x ∈ M2 ↔ x ∈ M) (B : GL (Fin n) K) (hB : IsBasisAt w M2 B) :
    IsBasisAt (w.comap (RingOfIntegers.mapRingEquiv e : 𝓞 K' →+* 𝓞 K) (RingOfIntegers.mapRingEquiv e).surjective) M
      (Matrix.GeneralLinearGroup.map e.symm.toRingHom B) := by
  unfold IsBasisAt at hB ⊢
  ext x
  have h1 := mem_localization_comap_iff (RingOfIntegers.mapRingEquiv e) (vmE e n) (vmE_smul e n) w.asIdeal M M2 hM x
  have h2 := mem_localization_comap_iff (RingOfIntegers.mapRingEquiv e) (vmE e n) (vmE_smul e n) w.asIdeal
    (colLat (Matrix.GeneralLinearGroup.map e.symm.toRingHom B)) (colLat B) (mem_colLat_iff e B) x
  refine h1.trans (Iff.trans ?_ h2.symm)
  rw [hB]

theorem map_smul_int' {σ : Type} (r : 𝓞 K') (P : MvPolynomial σ K') :
    map e.toRingHom (r • P) = RingOfIntegers.mapRingEquiv e r • map e.toRingHom P :=
  GlobalTheory.IoExtend.map_smul_alg e.toRingHom (RingOfIntegers.mapRingEquiv e : 𝓞 K' →+* 𝓞 K) (fun _ => rfl) r P

theorem map_symm_map {σ : Type} (P : MvPolynomial σ K') : map e.symm.toRingHom (map e.toRingHom P) = P := by
  rw [map_map]
  convert map_id P
  ext a
  simp

theorem mem_nabStd_iff {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (F : Pol K' ι n) :
    map e.toRingHom F ∈ nabStd K lam ↔ F ∈ nabStd K' lam := by
  constructor
  · intro h
    have := GlobalTheory.IoExtend.map_mem_nabStd e.symm.toRingHom lam h
    rwa [map_symm_map] at this
  · intro h
    exact GlobalTheory.IoExtend.map_mem_nabStd e.toRingHom lam h

theorem map_mem_nabP {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K') (Fin n → K')) (M2 : ι → Submodule (𝓞 K) (Fin n → K))
    (hM : ∀ τ x, vmE e n x ∈ M2 τ ↔ x ∈ M τ) {F : Pol K' ι n} (hF : F ∈ nabP lam M) :
    map e.toRingHom F ∈ nabP lam M2 := by
  unfold nabP transLat at hF ⊢
  simp only [Submodule.mem_iInf] at hF ⊢
  intro w B hB
  let B' : ι → GL (Fin n) K' := fun τ => Matrix.GeneralLinearGroup.map e.symm.toRingHom (B τ)
  have h1 := hF (w.comap (RingOfIntegers.mapRingEquiv e : 𝓞 K' →+* 𝓞 K) (RingOfIntegers.mapRingEquiv e).surjective) B'
    (fun τ => isBasisAt_transport e w (M τ) (M2 τ) (hM τ) (B τ) (hB τ))
  rw [Submodule.mem_comap] at h1 ⊢
  have hinv : ∀ t, ((B⁻¹ t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((B'⁻¹ t : GL (Fin n) K') : Matrix (Fin n) (Fin n) K').map e.toRingHom := by
    intro t
    have : B'⁻¹ t = Matrix.GeneralLinearGroup.map e.symm.toRingHom ((B t)⁻¹) := by
      simp only [Pi.inv_apply, B', map_inv]
    rw [this]
    ext a b
    change _ = e (e.symm _)
    rw [e.apply_symm_apply]
    rfl
  have hact := GlobalTheory.IoExtend.polyAction_map e.toRingHom lam B'⁻¹ B⁻¹ hinv F
  have h2 := (mem_localization_comap_iff (RingOfIntegers.mapRingEquiv e) (map e.toRingHom) (map_smul_int' e) w.asIdeal
    (nabStd K' lam) (nabStd K lam) (mem_nabStd_iff e lam) _).1 h1
  change actP lam B⁻¹ (map e.toRingHom F) ∈ _
  rw [hact]
  exact h2

theorem map_mem_nabAtr {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] {n : ℕ} (emb : ι → E →+* K')
    (emb2 : ι → E →+* K) (h : ∀ τ, emb2 τ = e.toRingHom.comp (emb τ)) (lam : ι → DomWeight n)
    (M : Submodule (𝓞 E) (Fin n → E)) {F : VV K' lam} (hF : F ∈ nabAtr emb lam M) :
    (⟨map e.toRingHom F.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV _ lam _ F.2⟩ : VV K lam) ∈ nabAtr emb2 lam M := by
  unfold nabAtr nabK at hF ⊢
  rw [Submodule.mem_comap] at hF ⊢
  exact map_mem_nabP e lam _ _ (fun τ x => mem_dualFr_iff e _ _ (fun y => mem_tauLat_iff e emb emb2 h τ M y) x) hF

end Fields

theorem coefLatFn_ringEquiv (D : D7) (n : ℕ) (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K']
    (e : K' ≃+* K) (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K')) (O : Subring ℂ) (lam : D.what₂.Tau → DomWeight n)
    (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    coefLatFn (σ.comp e.toRingHom) emb O lam M = coefLatFn σ (fun τ => e.toRingHom.comp (emb τ)) O lam M := by
  have hc : ∀ (P : Pol K' D.what₂.Tau n) (x : GLR D n),
      coefFn σ lam (map e.toRingHom P) x = coefFn (σ.comp e.toRingHom) lam P x := by
    intro P x
    unfold coefFn
    rw [MvPolynomial.eval₂Hom_map_hom]
  apply le_antisymm
  · rw [coefLatFn, Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    exact Submodule.subset_span ⟨_, map_mem_nabAtr e emb _ (fun _ => rfl) lam M hF, funext fun x => (hc F.1 x).symm⟩
  · rw [coefLatFn, Submodule.span_le]
    rintro _ ⟨G, hG, rfl⟩
    have hG' := map_mem_nabAtr e.symm (fun τ => e.toRingHom.comp (emb τ)) emb
      (fun τ => by ext a; simp) lam M hG
    refine Submodule.subset_span ⟨_, hG', funext fun x => ?_⟩
    refine Eq.trans ?_ (hc _ x)
    change coefFn σ lam G.1 x = coefFn σ lam (map e.toRingHom (map e.symm.toRingHom G.1)) x
    rw [map_map]
    congr 2
    convert (map_id G.1).symm
    ext a
    simp

end GlobalTheory.CoefLatIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharactersTypePlacesEqLocalComponents
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem GlobalTheory.TwInputs.tau_eq_locK : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ValLL0 D cf → ∀ τ : ℕ → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (↥D.LL0)ˣ, (∀ i j b kv x, 1 ≤ j → j ≤ D.R.m → ((Bs.exp.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) = sideEmb D.ntw i b ((τ j kv x : (↥D.LL0)ˣ) : ↥D.LL0)) → ∀ (j : Fin D.R.m) (kv : Σ k : Fin 2, D.nd.PlG k) (x : (ZMod (D.host.g kv.1))ˣ) (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), (((x : ZMod (D.host.g kv.1)).val : 𝓞 D.host.E) - u) ∈ (NX.pG D kv).asIdeal → embLL0 D ((τ (j.1 + 1) kv x : (↥D.LL0)ˣ) : ↥D.LL0) = (((cf.mu0 j).locK (NX.pG D kv) (Units.mk0 (u : D.host.E) hu) : ℂˣ) : ℂ) := by
  intro hGAR D cf Rw low Pq S hL eig θ Bs hV τ hτ j kv x u hu0 hxu0
  obtain ⟨k, v⟩ := kv
  have hgp : (D.host.g k).Prime := D.host.g_prime k
  haveI : Fact (D.host.g k).Prime := ⟨hgp⟩
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨p, hpg, hp⟩ := Nat.exists_infinite_primes (D.host.g k + 1)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨w, hw⟩⟩ := Formalism.BasicNotions.Examples₂.PlOver.plNe D p
  obtain ⟨i, hi, -⟩ := Bs.cover w
  have hk : D.ntw.l i ≠ D.host.g k := by rw [hi, hw]; omega
  obtain ⟨art, ha⟩ := hGAR D.host.E D.nd.Om
  obtain ⟨ρ⟩ := GlobalTheory.Triple.Reading.nonempty (X := D.ntw) i true
  obtain ⟨n, hn⟩ := GlobalTheory.TwChiGal.firstTwistCharacter_eq_ladic_heckeCharacter D cf Bs.chiD Bs.chi Bs.eta_eq Bs.ringSpec_normalisedCharacter_eq Bs.del_eq hV art ha i true ρ j
  have hl := GlobalTheory.Triple.Model.notMem_l (X := D.ntw) hk v
  have hgw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hspl := GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) hgp (D.nd.g_split k) (D.naut.plGw k v) hgw
  have hN : normV (D.naut.plGw k v) = D.host.g k := by
    rw [← hspl.1, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hg2 := hgp.two_le
  have hAw : IsPlaceOver (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) := D.nd.plOm.2 _
  have hu : u ∉ (D.naut.plGw k v).asIdeal := by
    intro h
    have h1 : (((x : ZMod (D.host.g k)).val : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := by
      have := (D.naut.plGw k v).asIdeal.add_mem hxu0 h
      rwa [sub_add_cancel] at this
    obtain ⟨a, c, hac⟩ : IsCoprime (((x : ZMod (D.host.g k)).val : ℕ) : 𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.E) :=
      (ZMod.val_coe_unit_coprime x).cast
    apply (D.naut.plGw k v).isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hac]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ hgw)
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap D.host.E D.nd.Om (((D.host.g k : ℕ) : 𝓞 D.host.E) : D.host.E))
    (show 0 < normV (D.naut.plGw k v) - 1 by omega)
  have hxu : IsUnitAt (D.naut.plGw k v) (atFin (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu0)) := by
    show Valued.v (((u : D.host.E) : (D.naut.plGw k v).adicCompletion D.host.E)) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 hu
  obtain ⟨σ, hσI, hσart, hσval⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hGAR D.host.E D.nd.Om art ha
    (D.naut.plGw k v) _ hAw _ hgw hspl.2.1 π hπ (atFin (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu0)) u hxu
    (by simp [atFin])
  have hTR : NX.TameRep (D.naut.plGw k v) 1 σ u :=
    ⟨_, hAw, hσI, _, π, hgw, hspl.2.1, hπ, by simpa using hσval⟩
  have e1 := hn.loc (Or.inl hl) hσart.symm
  obtain ⟨h1, -, h3, -, h5⟩ := GlobalTheory.GalChar.inertialOrderFifteenChar_auxiliaryPrime_spec (GlobalTheory.Triple.hframe cf) (l := D.ntw.l i)
  have hdel : (cf.delAt (D.ntw.l i)).UnrAt (D.naut.plGw k v) :=
    h5.unr _ (GlobalTheory.GalChar.notMem_of_ne (D.host.g_prime k) h1 (h3 k).symm (D.naut.plGw_over k v))
  rw [GlobalTheory.Triple.blockChar, GlobalTheory.GalChar.block_loc (cf.isEta.unr _) hxu, GlobalTheory.Triple.muBase, HChar.loc_mul,
    hdel _ hxu, mul_one] at e1
  have hm : ((normV (D.naut.plGw k v) - 1 : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal := by
    rw [hN]
    intro h
    apply (D.naut.plGw k v).isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have := (D.naut.plGw k v).asIdeal.sub_mem hgw h
    rwa [Nat.cast_sub (by omega), Nat.cast_one, sub_sub_cancel] at this
  have hex : ∃ s : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, NX.TameRep (D.naut.plGw k v) 1 s u := ⟨σ, hTR⟩
  have e2 : NX.tameVal (D.ntw.chi1 i (j.1 + 1) true) (D.naut.plGw k v) 1 u = D.ntw.chi1 i (j.1 + 1) true σ := by
    unfold NX.tameVal
    rw [dif_pos hex]
    refine GlobalTheory.T.tameChar_eq_of_tameRep_congr (D.naut.plGw k v) (D.ntw.twistBaseCoefficientRing_isAdic i) _ (D.ntw.twistCharacterFamily_continuous i (j.1 + 1) true) (by omega) hm
      (fun A hA s hs => ?_) _ _ u u hex.choose_spec hTR (by rw [sub_self]; exact zero_mem _)
    rw [hN]
    exact D.ntw.twistCharacterFamily_tame i (j.1 + 1) true k _ hgw hl A hA s hs
  have e3 := Bs.exp.tau_galois_first_character i (j.1 + 1) true ⟨k, v⟩ x u (by omega) (by omega) hl hxu0
  rw [hτ i (j.1 + 1) true ⟨k, v⟩ x (by omega) (by omega), Bs.exp.sgnG_one, Bs.exp.sgnT_one, one_mul] at e3
  have e4 : GlobalTheory.Triple.embSide D.ntw i true ((τ (j.1 + 1) ⟨k, v⟩ x : (↥D.LL0)ˣ) : ↥D.LL0) =
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) ((D.ntw.chi1 i (j.1 + 1) true σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) := by
    apply (IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
      (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)).injective
    rw [← e2]
    refine e3.trans ?_
    simp only [IsFractionRing.map, IsLocalization.map_eq]
    rfl
  rw [← ρ.read, e4]
  exact e1

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldTwoVocabulariesDictionary
section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.DelEps GlobalTheory.DelGlob
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DelGlob.LocalDict

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem valueGroupIso_uniformizer :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F (uniformizer F) = WithZero.exp (-1) := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  have h0 : φ (uniformizer F) ≠ 0 := by simp
  apply le_antisymm
  · have : φ (uniformizer F) < φ 1 := φ.strictMono uniformizer_lt_one
    rw [map_one, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at this
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega
  · have : φ.symm (WithZero.exp (-1)) ≤ uniformizer F := by
      rw [le_uniformizer_iff, ← map_one φ.symm]
      exact φ.symm.strictMono (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    simpa using φ.strictMono.monotone this

variable {F}

theorem ord_eq_ord (x : Fˣ) : GlobalTheory.SmGL.ord F x = GroundTheory.LocalField.ord (x : F) := by
  rw [GlobalTheory.SmGL.ord, GroundTheory.LocalField.ord, GroundTheory.LocalField.normalizedValuation_apply]

theorem isUnram_iff (χ : Fˣ →* ℂˣ) : GlobalTheory.SplitWeil.IsUnram χ ↔ GroundTheory.LocalField.IsUnramifiedChar χ := by
  constructor
  · intro h x hx
    exact MonoidHom.mem_ker.mpr (h x (GroundTheory.LocalField.mem_unitFiltrationUnits_zero_iff.mp hx))
  · intro h x hx
    exact MonoidHom.mem_ker.mp (h (GroundTheory.LocalField.mem_unitFiltrationUnits_zero_iff.mpr hx))

theorem mem_unitFilt_iff (n : ℕ) (x : Fˣ) :
    x ∈ GlobalTheory.LocLanglands.unitFilt F n ↔ x ∈ GroundTheory.LocalField.unitFiltrationUnits F n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [GroundTheory.LocalField.mem_unitFiltrationUnits_zero_iff]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    rw [pow_zero]
    exact (Valuation.map_sub _ _ _).trans (by simp [h])
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    rw [GroundTheory.LocalField.mem_unitFiltrationUnits_iff hn hϖ]
    have hv : valuation F (ϖ : F) = uniformizer F := by
      have e : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F (valuation F (ϖ : F)) =
          IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F (uniformizer F) := by
        rw [← GroundTheory.LocalField.normalizedValuation_apply, GroundTheory.LocalField.normalizedValuation_uniformizer hϖ,
          valueGroupIso_uniformizer]
      exact EquivLike.injective _ e
    rw [hv]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      have hlt : valuation F ((x : F) - 1) < 1 :=
        h.trans_lt (pow_lt_one₀ zero_le uniformizer_lt_one (by omega))
      simpa using (valuation F).map_one_add_of_lt hlt

theorem quasiCharConductor_eq_of_hasExponent (χ : Fˣ →* ℂˣ) (a : ℕ) (h : GlobalTheory.LocLanglands.HasExponent χ a) :
    GroundTheory.LocalField.quasiCharConductor χ = a := by
  have hmem : ∀ n, GroundTheory.LocalField.unitFiltrationUnits F n ≤ χ.ker ↔
      ∀ x ∈ GlobalTheory.LocLanglands.unitFilt F n, χ x = 1 := by
    intro n
    constructor
    · intro hk x hx; exact MonoidHom.mem_ker.mp (hk ((mem_unitFilt_iff n x).1 hx))
    · intro hk x hx; exact MonoidHom.mem_ker.mpr (hk x ((mem_unitFilt_iff n x).2 hx))
  unfold GroundTheory.LocalField.quasiCharConductor
  apply le_antisymm
  · exact Nat.sInf_le ((hmem a).2 h.1)
  · by_contra hlt
    push_neg at hlt
    have hs : GroundTheory.LocalField.unitFiltrationUnits F
        (sInf {n : ℕ | GroundTheory.LocalField.unitFiltrationUnits F n ≤ χ.ker}) ≤ χ.ker :=
      Nat.sInf_mem (s := {n : ℕ | GroundTheory.LocalField.unitFiltrationUnits F n ≤ χ.ker}) ⟨a, (hmem a).2 h.1⟩
    obtain ⟨x, hx, hx'⟩ := h.2 _ hlt
    exact hx' (((hmem _).1 hs) x hx)

theorem addCharConductor_eq_of_hasConductor (ψ : AddChar F Circle) (c : Fˣ)
    (h : GlobalTheory.SplitWeil.HasConductor ψ c) :
    GroundTheory.LocalField.addCharConductor ψ = GlobalTheory.SmGL.ord F c := by
  have key : ∀ n : ℤ, GroundTheory.LocalField.IsTrivialOn ψ n ↔ GlobalTheory.SmGL.ord F c ≤ n := by
    intro n
    obtain ⟨y, hy⟩ := GroundTheory.LocalField.exists_normalizedValuation_eq F (-n)
    have hball : ∀ z : F, z ∈ GroundTheory.LocalField.valBall F n ↔ valuation F z ≤ valuation F y := by
      intro z
      rw [GroundTheory.LocalField.mem_valBall, ← hy, GroundTheory.LocalField.normalizedValuation_le_iff]
    have e1 : GroundTheory.LocalField.IsTrivialOn ψ n ↔ ∀ z : F, valuation F z ≤ valuation F y → ψ z = 1 :=
      forall_congr' fun z => imp_congr_left (hball z)
    rw [e1, h y, ← GroundTheory.LocalField.normalizedValuation_le_iff, hy,
      GroundTheory.LocalField.normalizedValuation_eq_exp_ord c.ne_zero, WithZero.exp_le_exp, ord_eq_ord]
    omega
  unfold GroundTheory.LocalField.addCharConductor
  have hs : {n : ℤ | GroundTheory.LocalField.IsTrivialOn ψ n} = Set.Ici (GlobalTheory.SmGL.ord F c) := by
    ext n; exact key n
  rw [hs, csInf_Ici]

end GlobalTheory.DelGlob.LocalDict

namespace GlobalTheory.DelGlob

theorem localVocabularyDictionary : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F], resCard F = GroundTheory.LocalField.residueCard F ∧ (∀ x : Fˣ, ord F x = GroundTheory.LocalField.ord (x : F)) ∧ (∀ χ : Fˣ →* ℂˣ, IsUnram χ ↔ GroundTheory.LocalField.IsUnramifiedChar χ) ∧ (∀ (χ : Fˣ →* ℂˣ) (a : ℕ), HasExponent χ a → GroundTheory.LocalField.quasiCharConductor χ = a) ∧ ∀ (ψ : AddChar F Circle) (c : Fˣ), HasConductor ψ c → GroundTheory.LocalField.addCharConductor ψ = ord F c := by
  intro F _ _ _ _
  exact ⟨rfl, fun x => LocalDict.ord_eq_ord x, fun χ => LocalDict.isUnram_iff χ,
    fun χ a h => LocalDict.quasiCharConductor_eq_of_hasExponent χ a h,
    fun ψ c h => LocalDict.addCharConductor_eq_of_hasConductor ψ c h⟩

end GlobalTheory.DelGlob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonzeroMatrixIntertwinerDescendsToSubfieldStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_matrix_intertwiner_descends_to_subfield : ∀ (K : Type) [Field K] (e : K →+* ℂ) (Γ m p : Type) [Fintype m] [Fintype p] (A : Γ → Matrix m m K) (B : Γ → Matrix p p K), (∃ X : Matrix p m ℂ, X ≠ 0 ∧ ∀ γ, X * (A γ).map e = (B γ).map e * X) → ∃ X : Matrix p m K, X ≠ 0 ∧ ∀ γ, X * A γ = B γ * X := by
  first | exact @GlobalTheory.matrix_intertwiner_descends | exact GlobalTheory.matrix_intertwiner_descends | (intros; apply GlobalTheory.matrix_intertwiner_descends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PAdicMonodromyTheoremMatrixFormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pAdicMonodromyTheorem_matrixForm : MatThm := by
  first | exact @GlobalTheory.PMon.matThm_holds | exact GlobalTheory.PMon.matThm_holds | (intros; apply GlobalTheory.PMon.matThm_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceUnderIsPlaceOver
section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.DelEps GlobalTheory.DelGlob
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.DelGlob.placeUnder_isPlaceOver {Ω : Type} [Field Ω] {A : ValuationSubring Ω} {K : Type} [Field K] [NumberField K]
    [Algebra K Ω] (L : Type) [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]
    {u : HeightOneSpectrum (𝓞 L)} (hu : IsPlaceOver A u) : IsPlaceOver A (u.under (𝓞 K)) := fun x => by
  have e : algebraMap L Ω ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K Ω (x : K) := by
    rw [IsScalarTower.algebraMap_apply K L Ω]
    rfl
  rw [← e, hu]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalDatumSmallFieldFormHeckeScalarUnitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_datum_small_field_form_hecke_scalar_unit : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j, 1 ≤ j → j ≤ D.R.m → (Y.S.A j).IsKsForm) ∧ ∀ i b P, P ∉ D.ntw.S0 i → ∃ u : (D.ntw.O i)ˣ, Y.H.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u := by
  first | exact @GlobalTheory.TwUnit.isKsForm_and_unit | exact GlobalTheory.TwUnit.isKsForm_and_unit | (intros; apply GlobalTheory.TwUnit.isKsForm_and_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeDifferentOrderBoundedAbsoluteRamificatioStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relative_different_order_bounded_absolute_ramification : ∀ (l e : ℕ), l.Prime → ∃ c : ℕ, ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : HeightOneSpectrum (𝓞 K)) (la : HeightOneSpectrum (𝓞 L)), la.asIdeal.under (𝓞 K) = p.asIdeal → ((l : ℕ) : 𝓞 L) ∈ la.asIdeal → ((l : ℕ) : 𝓞 L) ∉ la.asIdeal ^ (e + 1) → ¬ la.asIdeal ^ (c + 1) ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  first | exact @GlobalTheory.TowerDifferent.relDifferent_order_bounded | exact GlobalTheory.TowerDifferent.relDifferent_order_bounded | (intros; apply GlobalTheory.TowerDifferent.relDifferent_order_bounded <;> assumption)
end

