import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0615
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0398
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0703
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0537
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0679
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0610
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0698
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatricesIntegralOfMemCompletedLattice

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedPhiModuleCrystallineLattice
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem rel_gal_of_env {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {τ : Ainf l} {d : ℕ}
    {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} {s : Seed bk d ρ τ} (ht : Height s)
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (ε : Matrix (Fin d) (Fin d) En.Q.A)
    (hε : ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)))
    (S : Strat bk d)
    (hSε : ∀ (B : Obj l ↥(OL K)) (k : Hom En.Q B), S.ε (k.comp En.inl) (k.comp En.inr) = ε.map k.f)
    (g : ↥(GK K)) :
    ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι)
      ((S.ε bk.ι ((ainfHom K g).comp bk.ι)).map bk.iA) := by
    obtain ⟨σ, ⟨h1, h2⟩, -⟩ := En.univ (ainfObj K) bk.ι ((ainfHom K g).comp bk.ι)
    have hn := GlobalTheory.T.discPeriod_comparison_relation_map_prismHom l K bk d ρ τ s ht En.Q (ainfObj K) En.inl En.inl En.inr bk.ι σ
      (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) hε
    obtain ⟨Fk, hFk⟩ := hn.1
    have hr := hn.2 Fk hFk
    have hr' : ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι)
        ((ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk) := by
      have key : ∀ f₁ f₂ : Hom bk.prism (ainfObj K), ht.Rel (BK.hf bk.ι X) f₁ f₂
          ((ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk) → f₁ = bk.ι → f₂ = (ainfHom K g).comp bk.ι →
          ht.Rel (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ((ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk) := by
        rintro f₁ f₂ h rfl rfl; exact h
      exact key _ _ hr h1 h2
    have e : S.ε bk.ι ((ainfHom K g).comp bk.ι) = ε.map σ.f := by
      have key : ∀ f₁ f₂ : Hom bk.prism (ainfObj K), S.ε f₁ f₂ = ε.map σ.f → f₁ = bk.ι →
          f₂ = (ainfHom K g).comp bk.ι → S.ε bk.ι ((ainfHom K g).comp bk.ι) = ε.map σ.f := by
        rintro f₁ f₂ h rfl rfl; exact h
      exact key _ _ (hSε (ainfObj K) σ) h1 h2
    have hm : (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk = (ε.map σ.f).map bk.iA :=
      Matrix.ext fun i j => hFk.ext (ε i j)
    have hM : (S.ε bk.ι ((ainfHom K g).comp bk.ι)).map bk.iA = (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk :=
      (congrArg (fun M => Matrix.map M bk.iA) e).trans hm.symm
    exact Eq.mpr (congrArg (ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι)) hM) hr'

theorem exists_strat_mreal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (s : Seed bk d ρ τ),
    Height s → ∃ (S : Strat bk d) (T : Matrix (Fin d) (Fin d) (WCb l)), MReal S ρ T := by
  intro l _ K bk τ hτ d ρ hρ s ht

  obtain ⟨En⟩ := GlobalTheory.T.nonempty_breuilKisinPrismCoproduct l K bk bk.prism (bk.toP bk.E) (bk.toP X)
    (GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk bk.prism (Hom.id bk.prism))

  obtain ⟨En₂⟩ := GlobalTheory.T.nonempty_breuilKisinPrismCoproduct l K bk En.Q (BK.hf En.inl bk.E) (BK.hf En.inl X)
    (GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk En.Q En.inl)
  obtain ⟨⟨tb⟩, -⟩ := GlobalTheory.T.breuilKisinEnvelopes_adicTopologicalBasis l K bk En En₂

  obtain ⟨ε, hε⟩ := GlobalTheory.T.exists_comparison_matrix_prismCoproduct l K bk d ρ τ s ht hτ hρ En
  have hφ := GlobalTheory.T.frobenius_eq_of_pow_smul_comparisonMatrix l K bk d ρ τ s ht hτ En.Q En.inl En.inr (Digits l) tb 0 ε
    (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) hε
    ((congrArg (fun c => c • ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀))
      (pow_zero ((l : ℕ) : Disc l (BK.hf En.inl X) bk.ρ₀))).trans (one_smul _ _)).symm
  have hc := GlobalTheory.T.breuilKisin_comparison_unit_cocycle_every_prism l K bk d ρ τ s ht En ε hε
  obtain ⟨S, hSa, hSA, hSε⟩ := GlobalTheory.T.stratifiedPhiModule_of_coproduct_cocycle l K bk En d (ht.a + s.N) ht.b ht.A ht.A' ht.A_mul ε hφ hc
  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_realization_matrix_stratifiedPhiModule l K bk d ρ τ s ht hτ S hSa hSA (rel_gal_of_env ht En ε hε S hSε)
  exact ⟨S, T, hT⟩

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitarySupportedAtSplitPlaceLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

namespace GlobalTheory.DownLift.SplitCoef

open GlobalTheory.ParahoricLift GlobalTheory.LevSplit Formalism.L2.NTheta

theorem lift_map_eq_of_smul {A B : Type} [CommRing A] [CommRing B] {m n : ℕ} (φ : A →+* B) (p : A) (hp : φ p = 1)
    (M M' : Matrix (Fin m) (Fin n) A) (h : p • M = p • M') : M.map φ = M'.map φ := by
  ext i j
  have := congrArg φ (congrFun (congrFun h i) j)
  simpa only [Matrix.smul_apply, smul_eq_mul, map_mul, hp, one_mul, Matrix.map_apply] using this

theorem lift_smul_eq_of_map {A B : Type} [CommRing A] [CommRing B] {m n : ℕ} (φ : A →+* B) (p : A)
    (hker : ∀ z, φ z = 0 ↔ p * z = 0) (M M' : Matrix (Fin m) (Fin n) A) (h : M.map φ = M'.map φ) : p • M = p • M' := by
  ext i j
  have h2 := congrFun (congrFun h i) j
  simp only [Matrix.map_apply] at h2
  have h3 : φ (M i j - M' i j) = 0 := by rw [map_sub, h2, sub_self]
  rw [hker, mul_sub, sub_eq_zero] at h3
  simpa only [Matrix.smul_apply, smul_eq_mul] using h3

theorem lift_smul_conj {A : Type} [CommRing A] {n : ℕ} (β : GL (Fin n) A) (p : A) (M : Matrix (Fin n) (Fin n) A) :
    p • (β.1 * M * (β⁻¹).1) = β.1 * (p • M) * (β⁻¹).1 := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem lift_smul_conj_inv {A : Type} [CommRing A] {n : ℕ} (β : GL (Fin n) A) (p : A) (M : Matrix (Fin n) (Fin n) A) :
    p • ((β⁻¹).1 * M * β.1) = (β⁻¹).1 * (p • M) * β.1 := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem lift_conj_mul_smul {A : Type} [CommRing A] {n : ℕ} (β : GL (Fin n) A) (p : A) (M M' : Matrix (Fin n) (Fin n) A)
    (h : p • (M * M') = p • (1 : Matrix (Fin n) (Fin n) A)) :
    p • ((β.1 * M * (β⁻¹).1) * (β.1 * M' * (β⁻¹).1)) = p • (1 : Matrix (Fin n) (Fin n) A) := by
  have e3 : (β.1 * M * (β⁻¹).1) * (β.1 * M' * (β⁻¹).1) = β.1 * (M * M') * (β⁻¹).1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (β⁻¹).1 β.1, Units.inv_mul, Matrix.one_mul]
  rw [e3, lift_smul_conj, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Units.mul_inv]

theorem lift_conj_part {A : Type} [CommRing A] {n : ℕ} (β : GL (Fin n) A) (p : A) (g M : Matrix (Fin n) (Fin n) A)
    (h : p • g = p • (β.1 * M * (β⁻¹).1)) : p • ((β⁻¹).1 * g * β.1) = p • M := by
  rw [lift_smul_conj_inv, h, lift_smul_conj]
  simp only [Matrix.mul_assoc]
  rw [Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem lift_chart_idem {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v}
    (hker : ∀ z, φ z = 0 ↔ toEAf D e * z = 0) (he : toEAf D e * toEAf D e = toEAf D e) : φ (toEAf D e) = 1 := by
  have h0 : φ (1 - toEAf D e) = 0 := by
    rw [hker, mul_sub, mul_one, he, sub_self]
  rw [map_sub, map_one, sub_eq_zero] at h0
  exact h0.symm

theorem lift_chart_int {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v}
    (hsurj : Function.Surjective φ) (h1 : φ (toEAf D e) = 1)
    (hint : ∀ z, toEAf D e * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ φ z ∈ v.adicCompletionIntegers D.host.F)
    (o : GlobalTheory.SplitHecke.Ov D v) : ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, φ (s : Formalism.IndefR.Lev.EAf D) = (o : Fv D.host.F v) := by
  obtain ⟨z, hz⟩ := hsurj (o : Fv D.host.F v)
  refine ⟨⟨toEAf D e * z, (hint z).2 (hz ▸ o.2)⟩, ?_⟩
  show φ (toEAf D e * z) = _
  rw [map_mul, h1, one_mul, hz]

theorem lift_frG_one {D : D7} (T : HSp D) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) :
    Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG T βT 1 = 1 := by
  unfold Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG
  rw [map_one, mul_one, inv_mul_cancel]

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_St_of_part_inv (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hβ : IsFrame β Λ) (hΛ : HatSelfDual σ J Λ)
    (p : Formalism.L2.Herm.intAf F E) (hq : Formalism.UG.sigR σ (Formalism.L2.Herm.Af F) p ∈ Formalism.L2.Herm.intAf F E)
    (Y Y' : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E))
    (hmm : (p : E ⊗[F] Formalism.L2.Herm.Af F) • ((β.1 * Y.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1) *
      (β.1 * Y'.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1)) = (p : E ⊗[F] Formalism.L2.Herm.Af F) • 1)
    (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hg : g ∈ Formalism.UG.UPts σ J (Formalism.L2.Herm.Af F))
    (f : E ⊗[F] Formalism.L2.Herm.Af F) (hf : f = p + Formalism.UG.sigR σ (Formalism.L2.Herm.Af F) p) (hs : f • (g.1 - 1) = g.1 - 1)
    (hY : (p : E ⊗[F] Formalism.L2.Herm.Af F) • g.1 =
      (p : E ⊗[F] Formalism.L2.Herm.Af F) • (β.1 * Y.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1)) : g ∈ St β := by
  subst hf
  exact (mem_St_iff β Λ hβ g).2 (stab_of_part _ _ _ hΛ p.2 hq g hg hs _ _ (frame_mulVec β Λ hβ Y)
    (frame_mulVec β Λ hβ Y') hmm hY)

end Gen

set_option maxHeartbeats 1000000 in

theorem exists_supp_lift_adj : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N : ℕ), IsBaseFrame S βS Λ N → ∀ h : GL (Fin S.rank) (GlobalTheory.SplitHecke.Ov D v), ∃ κ : GA D S, SuppAt e S κ ∧ κ ∈ GfC S ∧ finE S κ ∈ St βS ∧ (redFn βS PP (finE S κ)).val.map ι = h.val.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)) ∧ (∀ PP', PP' ≠ PP → ¬ Formalism.IndefR.Lev.IsConjPl PP PP' → redFn βS PP' (finE S κ) = 1) ∧ ∀ x : WO S T, rdAdj S T βS βT φ (actO S T κ 1 x) = h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) * rdAdj S T βS βT φ x := by
  intro D S T βS βT e PP v φ ι he hL Λ N hB h
  obtain ⟨hsurj, hker, hint, hres⟩ := hL
  have := PP.isPrime
  obtain ⟨p, hp, hpp, hres1⟩ := exists_idem_int he
  have hpe : toEAf D e = (p : Formalism.IndefR.Lev.EAf D) := hp.symm
  have hpp' : toEAf D e * toEAf D e = toEAf D e := by rw [hpe]; exact congrArg Subtype.val hpp
  have hp1 : φ (p : Formalism.IndefR.Lev.EAf D) = 1 := hpe ▸ lift_chart_idem hker hpp'
  have hker' : ∀ z, φ z = 0 ↔ (p : Formalism.IndefR.Lev.EAf D) * z = 0 := fun z => hpe ▸ hker z
  choose lf hlf using lift_chart_int hsurj (hpe ▸ hp1) hint
  set Y : Matrix (Fin S.rank) (Fin S.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E) := h.val.map lf with hYdef
  set Y' : Matrix (Fin S.rank) (Fin S.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E) := (h⁻¹).val.map lf with hY'def
  have hY : (Y.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).map φ =
      h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) := Matrix.ext fun i j => hlf _
  have hY' : (Y'.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).map φ =
      (h⁻¹).val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) := Matrix.ext fun i j => hlf _
  have hYY : (p : Formalism.IndefR.Lev.EAf D) • (Y.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype *
      Y'.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) = (p : Formalism.IndefR.Lev.EAf D) • 1 := by
    refine lift_smul_eq_of_map φ _ hker' _ _ ?_
    rw [Matrix.map_mul, hY, hY', ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hmm := lift_conj_mul_smul βS _ _ _ hYY
  have hmm' := hmm
  rw [hp] at hmm'
  obtain ⟨κ, hs, hκ⟩ := split_lift_fin S he.1 _ _ hmm'
  have hP : IsPrimeIdem PP e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents S
  have hsf := supp_fin S (f := e + cA D e) hs
  have hκ' : (p : Formalism.IndefR.Lev.EAf D) • (finE S κ).1 =
      (p : Formalism.IndefR.Lev.EAf D) • (βS.1 * Y.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype * (βS⁻¹).1) := by
    rw [hp]; exact hκ
  have hf : finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p := by
    rw [RingHom.map_add, finSw_cA, hp]
  have hSt : finE S κ ∈ St βS :=
    mem_St_of_part_inv D.sp.cm.sig S.gram Λ βS hB.1 (hatL_selfDual hB) p (sigR_int p.2) Y Y' hmm (finE S κ)
      (finE_mem_UA S κ) _ hf hsf hκ'
  refine ⟨κ, hs, (T3 PP e _ hP).2.2.1 κ hs, hSt, ?_, fun P' h1 h2 => ?_, fun x => ?_⟩
  · rw [redFn_of_smul_eq βS PP _ hSt p hres1 Y hκ']
    ext i j
    simp only [Matrix.map_apply]
    exact hres (lf (h.val i j)) (h.val i j) (hlf _).symm
  · obtain ⟨y, y', hy, hyy, a1, a2⟩ := exists_sep h1 fun h => h2 (isConjPl_symm h)
    obtain ⟨w, hw⟩ := idem_div_int hP y y' hyy a1 a2
    refine redFn_eq_one βS P' _ hSt (w * oToS D.host.F D.host.E y) ?_ ?_
    · rw [RingHom.map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hy, mul_zero]
    · have e1 : ((w * oToS D.host.F D.host.E y : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Lev.EAf D) =
          finSw D (e + cA D e) := hw
      rw [e1]
      exact hsf
  · have hG : (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG S βS κ).val.map φ =
        h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) := by
      rw [← hY]
      refine lift_map_eq_of_smul φ _ hp1 _ _ ?_
      unfold Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG
      rw [Units.val_mul, Units.val_mul]
      exact lift_conj_part βS _ _ _ hκ'
    unfold rdAdj
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapAdj_actO, lift_frG_one, inv_one, Units.val_one, Matrix.mul_one, Matrix.map_mul, hG]

end GlobalTheory.DownLift.SplitCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdeleCMMemIntegralOfIdempotentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdeleCM_mem_integral_of_idempotent : ∀ {D : D7} {e : AE D}, e * e = e → toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.IdemFin.toEAf_mem_intAf_of_idem | exact GlobalTheory.IdemFin.toEAf_mem_intAf_of_idem | (intros; apply GlobalTheory.IdemFin.toEAf_mem_intAf_of_idem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFourierExpansionConjugateHalfSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit.FinFourier

variable {D : D7}

theorem interp_of_sep {α : Type} [DecidableEq α] (P : Set (α → ℂ)) (h1 : (1 : α → ℂ) ∈ P)
    (hmul : ∀ f ∈ P, ∀ g ∈ P, f * g ∈ P) (hadd : ∀ f ∈ P, ∀ g ∈ P, f + g ∈ P)
    (hsmul : ∀ (c : ℂ), ∀ f ∈ P, c • f ∈ P) (K : Set α) (s : Finset α) (rep : α → α)
    (hrep : ∀ x ∈ K, rep x ∈ s)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∃ g ∈ P, g a ≠ g b ∧ ∀ x ∈ K, g x = g (rep x))
    (f : α → ℂ) (hf : ∀ x ∈ K, f x = f (rep x)) : ∃ F ∈ P, ∀ x ∈ K, f x = F x := by
  have h0 : (0 : α → ℂ) ∈ P := by simpa using hsmul 0 1 h1
  have hsum : ∀ (t : Finset α) (u : α → α → ℂ), (∀ a ∈ t, u a ∈ P) → (∑ a ∈ t, u a) ∈ P := by
    intro t u hu
    induction t using Finset.induction_on with
    | empty => simpa using h0
    | insert b t hb ih =>
      rw [Finset.sum_insert hb]
      exact hadd _ (hu _ (Finset.mem_insert_self _ _)) _ (ih fun a ha => hu a (Finset.mem_insert_of_mem ha))
  have hprod : ∀ (t : Finset α) (u : α → α → ℂ), (∀ a ∈ t, u a ∈ P) → (∏ a ∈ t, u a) ∈ P := by
    intro t u hu
    induction t using Finset.induction_on with
    | empty => simpa using h1
    | insert b t hb ih =>
      rw [Finset.prod_insert hb]
      exact hmul _ (hu _ (Finset.mem_insert_self _ _)) _ (ih fun a ha => hu a (Finset.mem_insert_of_mem ha))
  have hsep' : ∀ a b : α, ∃ g : α → ℂ, a ∈ s → b ∈ s → a ≠ b → g ∈ P ∧ g a ≠ g b ∧ ∀ x ∈ K, g x = g (rep x) := by
    intro a b
    by_cases h : a ∈ s ∧ b ∈ s ∧ a ≠ b
    · obtain ⟨g, hg⟩ := hsep a h.1 b h.2.1 h.2.2
      exact ⟨g, fun _ _ _ => hg⟩
    · exact ⟨0, fun ha hb hab => absurd ⟨ha, hb, hab⟩ h⟩
  choose g hg using hsep'
  let δ : α → α → ℂ := fun a => ∏ b ∈ s.erase a, (g a b a - g a b b)⁻¹ • (g a b + (-(g a b b)) • (1 : α → ℂ))
  have hδP : ∀ a ∈ s, δ a ∈ P := fun a ha => hprod _ _ fun b hb => hsmul _ _ (hadd _
    (hg a b ha (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb).symm).1 _ (hsmul _ _ h1))
  have hδ : ∀ a ∈ s, ∀ x ∈ K, δ a x = if rep x = a then 1 else 0 := by
    intro a ha x hx
    simp only [δ, Finset.prod_apply, Pi.smul_apply, Pi.add_apply, Pi.one_apply, smul_eq_mul]
    split_ifs with hxa
    · apply Finset.prod_eq_one
      intro b hb
      have hb' := hg a b ha (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb).symm
      rw [hb'.2.2 x hx, hxa]
      have : g a b a - g a b b ≠ 0 := sub_ne_zero.2 hb'.2.1
      rw [mul_one, ← sub_eq_add_neg, inv_mul_cancel₀ this]
    · apply Finset.prod_eq_zero (i := rep x)
      · exact Finset.mem_erase.2 ⟨hxa, hrep x hx⟩
      · have hb' := hg a (rep x) ha (hrep x hx) (Ne.symm hxa)
        rw [hb'.2.2 x hx]
        ring
  refine ⟨∑ a ∈ s, f a • δ a, hsum _ _ fun a ha => hsmul _ _ (hδP a ha), fun x hx => ?_⟩
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl fun a ha => by rw [hδ a ha x hx]]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq s (rep x) f, if_pos (hrep x hx), hf x hx]

theorem finite_cover_pow {O K : Type} [CommRing O] [Field K] [Algebra O K] (ϖ : O) (hϖ : algebraMap O K ϖ ≠ 0)
    (N M : ℕ) (hfin : Finite (O ⧸ Ideal.span {ϖ ^ (N + M)})) (m n : Type) [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] :
    ∃ T : Finset (Matrix m n K), ∀ X : Matrix m n K,
      (∀ i j, ∃ o : O, algebraMap O K (ϖ ^ N) * X i j = algebraMap O K o) →
      ∃ t ∈ T, ∀ i j, ∃ o : O, (X - t) i j = algebraMap O K (ϖ ^ M * o) := by
  classical
  set I : Ideal O := Ideal.span {ϖ ^ (N + M)} with hIdef
  have ha : algebraMap O K (ϖ ^ N) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hϖ
  haveI : Finite (m → n → O ⧸ I) := inferInstance
  haveI : Fintype (m → n → O ⧸ I) := Fintype.ofFinite _
  let lift : (m → n → O ⧸ I) → m → n → O :=
    fun q i j => Function.surjInv (Ideal.Quotient.mk_surjective (I := I)) (q i j)
  refine ⟨Finset.univ.image fun q => Matrix.of fun i j => (algebraMap O K (ϖ ^ N))⁻¹ * algebraMap O K (lift q i j), ?_⟩
  intro X hX
  choose z hz using hX
  let q : m → n → O ⧸ I := fun i j => Ideal.Quotient.mk I (z i j)
  refine ⟨_, Finset.mem_image.2 ⟨q, Finset.mem_univ _, rfl⟩, fun i j => ?_⟩
  have hq : Ideal.Quotient.mk I (lift q i j) = Ideal.Quotient.mk I (z i j) :=
    Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := I)) _
  rw [Ideal.Quotient.eq, hIdef, Ideal.mem_span_singleton'] at hq
  obtain ⟨w, hw⟩ := hq
  refine ⟨-w, ?_⟩
  have hij := hz i j
  simp only [Matrix.sub_apply, Matrix.of_apply]
  have hX : X i j = (algebraMap O K (ϖ ^ N))⁻¹ * algebraMap O K (z i j) := by
    rw [← hij, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  have hzl : z i j - lift q i j = ϖ ^ N * (ϖ ^ M * -w) := by
    rw [← neg_sub, ← hw]; ring
  rw [hX, ← mul_sub, ← map_sub, hzl, map_mul (algebraMap O K) (ϖ ^ N), ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

end GlobalTheory.DownLift.GenSplit.FinFourier

namespace GlobalTheory.DownLift.GenSplit

open GlobalTheory.SplitScalar in

theorem finite_fourier_half : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)) (ϖ : OI v), Irreducible ϖ → ∀ (M N : ℕ), (∀ x : WO S T, IsHalf (cA D e) x → ¬ InPow ϖ M (adjCo φ S T BS BT x) → ∃ y, IsHalf e y ∧ (∀ z ∈ halfPow φ S T BS BT e ϖ M, ψ (symplO S T z y) = 1) ∧ ψ (symplO S T x y) ≠ 1) → ∀ (a : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) → ℂ), (∀ X Z, InPow ϖ M Z → a (X + Z) = a X) → ∃ c : WO S T →₀ ℂ, (∀ y ∈ c.support, IsHalf e y) ∧ ∀ x, IsHalf (cA D e) x → Bdd ϖ N (adjCo φ S T BS BT x) → a (adjCo φ S T BS BT x) = c.sum fun y z => z * ψ (symplO S T x y) := by
  intro D ψ _ S T ΛS ΛT _ _ v φ e _ BS BT ϖ hϖ M N hyp a ha
  classical

  let P : Set (WO S T → ℂ) := {F | ∃ c : WO S T →₀ ℂ, (∀ y ∈ c.support, IsHalf e y) ∧
    ∀ x, F x = c.sum fun y z => z * ψ (symplO S T x y)}
  have h0 : ∀ x : WO S T, ∀ y : WO S T, (0 : ℂ) * ψ (symplO S T x y) = 0 := fun _ _ => zero_mul _
  have hP1 : (1 : WO S T → ℂ) ∈ P := ⟨Finsupp.single 0 1, fun y hy => by
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hy)]; exact isHalf_zero e, fun x => by
    rw [Finsupp.sum_single_index (h0 x 0), symplO_zero_right, AddChar.map_zero_eq_one, one_mul]; rfl⟩
  have hPadd : ∀ f ∈ P, ∀ g ∈ P, f + g ∈ P := by
    rintro f ⟨c, hc, hf⟩ g ⟨d, hd, hg⟩
    refine ⟨c + d, fun y hy => ?_, fun x => ?_⟩
    · rcases Finset.mem_union.1 (Finsupp.support_add hy) with h | h
      · exact hc y h
      · exact hd y h
    · rw [Pi.add_apply, hf, hg, Finsupp.sum_add_index' (fun y => h0 x y) (fun _ _ _ => add_mul _ _ _)]
  have hPsmul : ∀ (r : ℂ), ∀ f ∈ P, r • f ∈ P := by
    rintro r f ⟨c, hc, hf⟩
    refine ⟨r • c, fun y hy => hc y (Finsupp.support_smul hy), fun x => ?_⟩
    rw [Pi.smul_apply, hf, Finsupp.sum_smul_index' (fun y => h0 x y), smul_eq_mul, Finsupp.mul_sum]
    simp only [smul_eq_mul, mul_assoc]
  have hPmul : ∀ f ∈ P, ∀ g ∈ P, f * g ∈ P := by
    rintro f ⟨c, hc, hf⟩ g ⟨d, hd, hg⟩
    refine ⟨c.sum fun y z => d.sum fun y' z' => Finsupp.single (y + y') (z * z'), fun y hy => ?_, fun x => ?_⟩
    · obtain ⟨y₁, hy₁, hy⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hy)
      obtain ⟨y₂, hy₂, hy⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hy)
      rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hy)]
      exact isHalf_add (hc y₁ hy₁) (hd y₂ hy₂)
    · rw [Pi.mul_apply, hf, hg, Finsupp.sum_sum_index (fun y => h0 x y) (fun _ _ _ => add_mul _ _ _),
        Finsupp.sum_mul]
      refine Finsupp.sum_congr fun y _ => ?_
      rw [Finsupp.sum_sum_index (fun y => h0 x y) (fun _ _ _ => add_mul _ _ _), Finsupp.mul_sum]
      refine Finsupp.sum_congr fun y' _ => ?_
      rw [Finsupp.sum_single_index (h0 x _), GlobalTheory.LatVac.symplO_add_right, AddChar.map_add_eq_mul]
      ring

  let H : AddSubgroup (Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v)) :=
    { carrier := {X | InPow ϖ M X}
      add_mem' := fun {X Y} hX hY i j => by
        obtain ⟨o₁, h₁⟩ := hX i j
        obtain ⟨o₂, h₂⟩ := hY i j
        exact ⟨o₁ + o₂, by rw [Matrix.add_apply, h₁, h₂, ← map_add, mul_add]⟩
      zero_mem' := fun i j => ⟨0, by simp⟩
      neg_mem' := fun {X} hX i j => by
        obtain ⟨o, h⟩ := hX i j
        exact ⟨-o, by rw [Matrix.neg_apply, h, ← map_neg, mul_neg]⟩ }
  have hadj : ∀ x y : WO S T, adjCo φ S T BS BT (x - y) = adjCo φ S T BS BT x - adjCo φ S T BS BT y := by
    intro x y
    have e1 : (x - y : WO S T).map (cA D) = x.map (cA D) - y.map (cA D) := by ext i j; simp
    have e2 : ∀ {m n : Type} (A B : Matrix m n (AE D)),
        (A - B).map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) = A.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) - B.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) :=
      fun A B => by ext i j; simp
    simp only [adjCo, e1, Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, e2]
  let q : WO S T → Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) ⧸ H :=
    fun x => (adjCo φ S T BS BT x : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) ⧸ H)
  have hqeq : ∀ x y, q x = q y ↔ InPow ϖ M (adjCo φ S T BS BT (x - y)) := by
    intro x y
    rw [hadj]
    exact QuotientAddGroup.eq_iff_sub_mem
  let K : Set (WO S T) := {x | IsHalf (cA D e) x ∧ Bdd ϖ N (adjCo φ S T BS BT x)}
  have hϖ0 : algebraMap (OI v) (Fv D.host.F v) ϖ ≠ 0 :=
    (FaithfulSMul.algebraMap_injective (OI v) (Fv D.host.F v)).ne_iff' (map_zero _) |>.2 hϖ.ne_zero
  have hfin : Finite (OI v ⧸ Ideal.span {ϖ ^ (N + M)}) :=
    Formalism.UG.P.glint_finite_quotient_of_dvr (Formalism.UG.P.glint_finite_residueField v) _
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact pow_ne_zero _ hϖ.ne_zero)
  obtain ⟨T₀, hT₀⟩ := FinFourier.finite_cover_pow ϖ hϖ0 N M hfin (Fin S.rank) (Fin T.rank)
  have hfinK : (q '' K).Finite := by
    refine (T₀.finite_toSet.image (QuotientAddGroup.mk (s := H))).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht, h⟩ := hT₀ _ hx.2
    exact ⟨t, ht, (QuotientAddGroup.eq_iff_sub_mem (N := H)).2 (show InPow ϖ M _ from h) |>.symm⟩
  let pick : (Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) ⧸ H) → WO S T :=
    fun c => if h : ∃ x ∈ K, q x = c then h.choose else 0
  have hpick : ∀ x ∈ K, pick (q x) ∈ K ∧ q (pick (q x)) = q x := by
    intro x hx
    have h : ∃ x' ∈ K, q x' = q x := ⟨x, hx, rfl⟩
    simp only [pick, dif_pos h]
    exact h.choose_spec
  have hsep : ∀ a' ∈ hfinK.toFinset.image pick, ∀ b' ∈ hfinK.toFinset.image pick, a' ≠ b' →
      ∃ g ∈ P, g a' ≠ g b' ∧ ∀ x ∈ K, g x = g (pick (q x)) := by
    intro a' ha' b' hb' hab
    obtain ⟨c₁, hc₁, rfl⟩ := Finset.mem_image.1 ha'
    obtain ⟨x₁, hx₁, rfl⟩ := hfinK.mem_toFinset.1 hc₁
    obtain ⟨c₂, hc₂, rfl⟩ := Finset.mem_image.1 hb'
    obtain ⟨x₂, hx₂, rfl⟩ := hfinK.mem_toFinset.1 hc₂
    have A := hpick x₁ hx₁
    have B := hpick x₂ hx₂
    have hne : ¬ InPow ϖ M (adjCo φ S T BS BT (pick (q x₁) - pick (q x₂))) := by
      intro h
      apply hab
      have h' := (hqeq _ _).2 h
      rw [A.2, B.2] at h'
      rw [h']
    obtain ⟨y, hy, hyL, hyne⟩ := hyp _ (isHalf_sub A.1.1 B.1.1) hne
    refine ⟨fun x => ψ (symplO S T x y), ⟨Finsupp.single y 1, fun y' hy' => ?_, fun x => ?_⟩, ?_, ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hy')]; exact hy
    · rw [Finsupp.sum_single_index (h0 x y), one_mul]
    · intro h
      apply hyne
      simp only at h
      rw [symplO_sub_left, sub_eq_add_neg, AddChar.map_add_eq_mul, h, ← AddChar.map_add_eq_mul, add_neg_cancel,
        AddChar.map_zero_eq_one]
    · intro x hx
      have hxr : x - pick (q x) ∈ halfPow φ S T BS BT e ϖ M :=
        ⟨isHalf_sub hx.1 (hpick x hx).1.1, (hqeq _ _).1 (hpick x hx).2.symm⟩
      show ψ (symplO S T x y) = ψ (symplO S T (pick (q x)) y)
      conv_lhs => rw [← add_sub_cancel (pick (q x)) x]
      rw [GlobalTheory.LatVac.symplO_add_left, AddChar.map_add_eq_mul, hyL _ hxr, mul_one]
  have hf : ∀ x ∈ K, a (adjCo φ S T BS BT x) = a (adjCo φ S T BS BT (pick (q x))) := by
    intro x hx
    have hI := (hqeq _ _).1 (hpick x hx).2.symm
    rw [hadj] at hI
    have h := ha (adjCo φ S T BS BT (pick (q x))) _ hI
    rwa [add_sub_cancel] at h
  obtain ⟨F, ⟨c, hc, hF⟩, hFK⟩ := FinFourier.interp_of_sep P hP1 hPmul hPadd hPsmul K
    (hfinK.toFinset.image pick) (fun x => pick (q x))
    (fun x hx => Finset.mem_image.2 ⟨q x, hfinK.mem_toFinset.2 ⟨x, hx, rfl⟩, rfl⟩) hsep
    (fun x => a (adjCo φ S T BS BT x)) hf
  exact ⟨c, hc, fun x hx hB => (hFK x ⟨hx, hB⟩).trans (hF x)⟩

end GlobalTheory.DownLift.GenSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatricesIntegralOfMemCompletedLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMatrices_integral_of_mem_completedLattice : ∀ {D : D7} {S T : HSp D} {F : Frame S T}, F.Good → ∀ {R : Finset (Pl D.host.E)}, PlacesOK ∅ R → ∀ {x : WO S T}, IsHalf (idem R) x → x ∈ F.lat → IsIntM (frMapO S T F.βS F.βT x) ∧ IsIntM (frMapAdj S T F.βS F.βT x) := by
  first | exact @GlobalTheory.LatHalfInt.frMap_int_of_mem_lat | exact GlobalTheory.LatHalfInt.frMap_int_of_mem_lat | (intros; apply GlobalTheory.LatHalfInt.frMap_int_of_mem_lat <;> assumption)
end

