import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0079
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0068
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0238
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0204
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0251

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdditiveCharacterTypePrimesValuesCoefficientFielStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_psi0_eq_embLL : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g), I.IdG l Z G → ∀ j v h x, ∃ r : B.LL, B.embLL r = G.psi0 j v h x := by
  first | exact @GlobalTheory.Mem.Col2.TC.additiveCharacter_typePrimes_values_coefficientField | exact GlobalTheory.Mem.Col2.TC.additiveCharacter_typePrimes_values_coefficientField | (intros; apply GlobalTheory.Mem.Col2.TC.additiveCharacter_typePrimes_values_coefficientField <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicConjugateCharacterStandardForms
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.SameOff

theorem exists_smul_mem_of_span {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) : ∃ ν : 𝓞 E, ν ≠ 0 ∧ ν • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.MulEqIntegerExists.exists_smul_mem
  | exact _root_.GlobalTheory.MulEqIntegerExists.exists_smul_mem
  | (apply _root_.GlobalTheory.MulEqIntegerExists.exists_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.MulEqIntegerExists.exists_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MulEqIntegerExists.exists_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MulEqIntegerExists.exists_smul_mem ..)

section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem incl_smul (v : HeightOneSpectrum (𝓞 F)) (s : 𝓞 E) (x : Fin n → E) :
    (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) ((s • x) i)) =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E s) •
        fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) (x i) := by
  funext i
  rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, map_mul, smul_eq_mul]

theorem mem_localization_of_mem_localLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (B : Submodule (𝓞 E) (Fin n → E)), Module.Finite (𝓞 E) B → Submodule.span E (B : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E), (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) (x i)) ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v B → ∀ q : HeightOneSpectrum (𝓞 E), q.under (𝓞 F) = v → x ∈ Formalism.HermitianLatticesTheory.localization₂ q.asIdeal B := by
  intro F E _ _ _ _ _ n v B hB hs x hx q hq
  classical
  obtain ⟨ν, hν, hνx⟩ := exists_smul_mem_of_span B hs x
  let J : Ideal (𝓞 E) := B.comap (LinearMap.toSpanSingleton (𝓞 E) _ x)
  have hJ : ∀ s, s ∈ J ↔ s • x ∈ B := fun s => Iff.rfl
  have hJ0 : J.comap (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ := by
    intro h
    have := Ideal.eq_bot_of_comap_eq_bot h
    have h2 : ν ∈ J := hνx
    rw [this] at h2
    exact hν h2
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hI⟩ := Ideal.eq_prime_pow_mul_coprime hJ0 v.asIdeal
  obtain ⟨d, hdQ, hdv⟩ : ∃ d ∈ Q, d ∉ v.asIdeal := by
    by_contra h
    push_neg at h
    rw [sup_eq_left.2 (show Q ≤ v.asIdeal from h)] at hQ
    exact v.isPrime.ne_top hQ
  refine ⟨algebraMap (𝓞 F) (𝓞 E) d, fun h => hdv (by rw [← hq]; exact h), ?_⟩
  refine (GlobalTheory.LatLocGlob.latS_local_global F E n B hB).2.1 hs _ fun w => ?_
  by_cases hw : w = v
  · subst hw
    rw [incl_smul]
    exact Submodule.smul_mem (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w B)
      (⟨_, Subring.subset_closure (Or.inl ⟨⟨_, ⟨algebraMap (𝓞 F) (𝓞 E) d, rfl⟩⟩, rfl⟩)⟩ : intV E w) hx
  · obtain ⟨π, hπ, hπw⟩ : ∃ π ∈ v.asIdeal ^ (UniqueFactorizationMonoid.normalizedFactors (J.comap (algebraMap (𝓞 F) (𝓞 E)))).count v.asIdeal, π ∉ w.asIdeal := by
      by_contra h
      push_neg at h
      haveI := w.isPrime
      have h1 : v.asIdeal ≤ w.asIdeal := Ideal.IsPrime.le_of_pow_le h
      exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top h1).symm)
    have h1 : π * d ∈ J.comap (algebraMap (𝓞 F) (𝓞 E)) := by
      rw [hI]; exact Ideal.mul_mem_mul hπ hdQ
    have h2 : algebraMap (𝓞 F) (𝓞 E) π • algebraMap (𝓞 F) (𝓞 E) d • x ∈ B := by
      rw [← mul_smul, ← map_mul]; exact h1
    obtain ⟨t, ht, e⟩ := GlobalTheory.OverCompare.exists_intV_mul_inclE_eq_one (E := E) w π hπw
    have h3 : (fun i => Formalism.UG.inclE (F := F) (w.adicCompletion F) ((algebraMap (𝓞 F) (𝓞 E) π • algebraMap (𝓞 F) (𝓞 E) d • x) i)) ∈
        GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w B := Submodule.subset_span ⟨_, h2, rfl⟩
    have h4 := Submodule.smul_mem (GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w B) (⟨t, ht⟩ : intV E w) h3
    rw [incl_smul] at h4
    have e2 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) π) = algebraMap F E (π : F) := by
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
    rw [e2, Subring.smul_def, smul_smul] at h4
    rwa [show ((⟨t, ht⟩ : intV E w) : E ⊗[F] w.adicCompletion F) * _ = 1 from e, one_smul] at h4

end Loc

section Step
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mulVec_mem_latS (R : Type) [CommRing R] [Algebra F R] (S : Subring (E ⊗[F] R)) (g : Matrix (Fin n) (Fin n) E)
    {L M : Submodule (𝓞 E) (Fin n → E)} (h : ∀ x ∈ L, g *ᵥ x ∈ M) {X : Fin n → E ⊗[F] R}
    (hX : X ∈ Formalism.UG.latS (F := F) R S L) :
    g.map (Formalism.UG.inclE (F := F) R) *ᵥ X ∈ Formalism.UG.latS (F := F) R S M := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    exact Submodule.subset_span ⟨_, h x hx, funext fun i => RingHom.map_mulVec _ g x i⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [Subring.smul_def, Matrix.mulVec_smul]
    exact Submodule.smul_mem _ a hx

theorem mem_latS_mulLat (R : Type) [CommRing R] [Algebra F R] (S : Subring (E ⊗[F] R)) (γ : GL (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (X : Fin n → E ⊗[F] R) :
    X ∈ Formalism.UG.latS (F := F) R S (Formalism.L2.Forms.mulLat γ.1 L) ↔
      ((Formalism.UG.bc (Formalism.UG.inclE (F := F) R) γ)⁻¹).1 *ᵥ X ∈ Formalism.UG.latS (F := F) R S L := by
  constructor
  · intro hX
    rw [← map_inv]
    refine mulVec_mem_latS R S (γ⁻¹).1 ?_ hX
    rintro _ ⟨x, hx, rfl⟩
    show (γ⁻¹).1 *ᵥ (γ.1 *ᵥ x) ∈ L
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  · intro hX
    have h := mulVec_mem_latS R S γ.1 (M := Formalism.L2.Forms.mulLat γ.1 L) (fun x hx => ⟨x, hx, rfl⟩) hX
    have e : γ.1.map (Formalism.UG.inclE (F := F) R) = (Formalism.UG.bc (Formalism.UG.inclE (F := F) R) γ).1 := rfl
    rwa [e, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h

theorem mem_locLat_iff_adelic (w : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Module.Finite (𝓞 E) L)
    (z : Fin n → E ⊗[F] w.adicCompletion F) :
    z ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w L ↔ (fun i => Formalism.UG.P.afsplitIE w (z i)) ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) L := by
  rw [GlobalTheory.LatticeStabLocal.mem_latS_adele_iff]
  have h1 : (fun i => prV (E := E) w (Formalism.UG.P.afsplitIE w (z i))) = z :=
    funext fun i => Formalism.UG.P.afsplit_prV_IE w _
  constructor
  · intro hz v
    by_cases hv : v = w
    · subst hv; rw [h1]; exact hz
    · rw [show (fun i => prV (E := E) v (Formalism.UG.P.afsplitIE w (z i))) = 0 from
        funext fun i => Formalism.UG.P.afsplit_prV_IE_ne w v hv _]
      exact zero_mem _
  · intro h
    have := h w
    rwa [h1] at this

theorem locLat_of_adStep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (U : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) (Lb lat lat' : Submodule (𝓞 E) (Fin n → E)) (y y' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E) (v w : HeightOneSpectrum (𝓞 F)), Module.Finite (𝓞 E) Lb → Module.Finite (𝓞 E) lat → Module.Finite (𝓞 E) lat' → (∀ κ ∈ U, ∀ X : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, X ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) Lb ↔ (κ : Matrix (Fin n) (Fin n) _) *ᵥ X ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) Lb) → (∀ X : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, X ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) lat ↔ (y⁻¹).1 *ᵥ X ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) Lb) → (∀ X : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, X ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) lat' ↔ (y'⁻¹).1 *ᵥ X ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) Lb) → Formalism.L2.Herm.AdStep σ J U y y' γ v → w ≠ v → ∀ z : Fin n → E ⊗[F] w.adicCompletion F, z ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w (Formalism.L2.Forms.mulLat γ.1 lat') ↔ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat w lat := by
  intro F E _ _ _ _ _ σ n J U Lb lat lat' y y' γ v w hLb hl hl' hU hy hy' hS hw z
  obtain ⟨κ, hκ, η, -, hη, e⟩ := hS
  have hfin : Module.Finite (𝓞 E) (Formalism.L2.Forms.mulLat γ.1 lat') :=
    Module.Finite.iff_fg.2 ((Module.Finite.iff_fg.1 hl').map _)
  rw [mem_locLat_iff_adelic w _ hfin, mem_locLat_iff_adelic w _ hl, mem_latS_mulLat, hy, hy', hU κ hκ]
  set X : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F := fun i => Formalism.UG.P.afsplitIE w (z i) with hX
  have e1 : κ * y'⁻¹ * (Formalism.UG.bc (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ)⁻¹ = η⁻¹ * y⁻¹ := by
    rw [mul_assoc, ← _root_.mul_inv_rev, e]; group
  have e2 : (η⁻¹).1 *ᵥ ((y⁻¹).1 *ᵥ X) = (y⁻¹).1 *ᵥ X := by
    funext i
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun p => ?_
    rw [map_sub, sub_eq_zero]
    refine (congrFun (GlobalTheory.LatticeStabLocal.prV_mulVec p _ _) i).trans ?_
    by_cases hp : p = w
    · subst hp
      have h1 : (η⁻¹).1.map (prV (E := E) p) = (Formalism.UG.bc (prV (E := E) p) η⁻¹).1 := rfl
      rw [h1, map_inv, hη p hw, inv_one, Units.val_one, Matrix.one_mulVec]
    · have h0 : (fun i => prV (E := E) p (((y⁻¹).1 *ᵥ X) i)) = 0 := by
        rw [GlobalTheory.LatticeStabLocal.prV_mulVec, show (fun i => prV (E := E) p (X i)) = 0 from
          funext fun i => Formalism.UG.P.afsplit_prV_IE_ne w p hp _, Matrix.mulVec_zero]
      rw [h0, Matrix.mulVec_zero]
      exact (congrFun h0 i).symm
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, e1, Units.val_mul,
    ← Matrix.mulVec_mulVec, e2]

end Step

theorem locP_le_of_le' {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    {L N : Submodule R W} (h : L ≤ Formalism.HermitianLatticesTheory.localization₂ p N) : Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p N := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, hx'⟩ := h hx
  exact ⟨t * s, p.primeCompl.mul_mem ht hs, by rw [mul_smul]; exact hx'⟩

theorem clsCrd_fin (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    Module.Finite (𝓞 D.host.E) (clsCrd D u i hi c) ∧
      Submodule.span D.host.E (clsCrd D u i hi c : Set (Fin (D.R.N i) → D.host.E)) = ⊤ := by
  letI := D.host.cmStar
  have h := D.clsLat_lat u i c
  refine ⟨Module.Finite.iff_fg.2 (h.fg.map _), ?_⟩
  have h2 := congrArg (Submodule.map (((D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm) :
      (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E))) h.span_eq_top
  rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h2
  exact h2

theorem mulLat_fin {E : Type} [Field E] [NumberField E] {n : ℕ} (γ : GL (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Module.Finite (𝓞 E) L) (hs : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    Module.Finite (𝓞 E) (Formalism.L2.Forms.mulLat γ.1 L) ∧
      Submodule.span E (Formalism.L2.Forms.mulLat γ.1 L : Set (Fin n → E)) = ⊤ := by
  refine ⟨Module.Finite.iff_fg.2 ((Module.Finite.iff_fg.1 hL).map _), ?_⟩
  have e : (Formalism.L2.Forms.mulLat γ.1 L : Set (Fin n → E)) = (Matrix.mulVecLin γ.1) '' (L : Set (Fin n → E)) := rfl
  rw [e, ← Submodule.map_span, hs, Submodule.map_top, LinearMap.range_eq_top]
  intro z
  refine ⟨((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ z, ?_⟩
  simp [Matrix.mulVec_mulVec]

theorem stepLevel_stab {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (lev : Formalism.L2.Forms.StepLevel F E σ J T f bad) (κ) (hκ : κ ∈ lev.U)
    (X : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    X ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) lev.Lb ↔
      (κ : Matrix (Fin n) (Fin n) _) *ᵥ X ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) lev.Lb := by
  haveI := lev.Lb_fin
  have h : κ ∈ Formalism.UG.stabGL (Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) lev.Lb) := by
    refine (GlobalTheory.LatticeStabLocal.mem_stabGL_adele_iff lev.Lb κ).2 fun v => ?_
    exact (Subgroup.mem_inf.1 (lev.Uloc_lev v (((lev.U_eq κ).1 hκ).2 v))).2
  exact h X

theorem locP_le_of_locLat_le {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (q : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Fin n → E)) (hBf : Module.Finite (𝓞 E) B)
    (hBs : Submodule.span E (B : Set (Fin n → E)) = ⊤)
    (hAB : ∀ z, z ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat (q.under (𝓞 F)) A → z ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat (q.under (𝓞 F)) B) :
    Formalism.HermitianLatticesTheory.localization₂ q.asIdeal A ≤ Formalism.HermitianLatticesTheory.localization₂ q.asIdeal B :=
  locP_le_of_le' _ fun x hx =>
    mem_localization_of_mem_localLattice F E n _ B hBf hBs x (hAB _ (Submodule.subset_span ⟨x, hx, rfl⟩)) q rfl

set_option maxHeartbeats 4000000 in

theorem sameoff_gen {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (T : FormsTiedSym D u Ch chOf) (i : ℕ) (hi : i ≤ D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F))
    (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E) (hAd : AdC T i hi c c' γ v)
    (q : HeightOneSpectrum (𝓞 D.host.E)) (hq : q.under (𝓞 D.host.F) ≠ v) :
    Formalism.HermitianLatticesTheory.localization₂ q.asIdeal (Formalism.L2.Forms.mulLat γ.1 (clsCrd D u i hi c')) =
      Formalism.HermitianLatticesTheory.localization₂ q.asIdeal (clsCrd D u i hi c) := by
  obtain ⟨f1, s1⟩ := clsCrd_fin D u i hi c
  obtain ⟨f2, s2⟩ := clsCrd_fin D u i hi c'
  obtain ⟨f3, s3⟩ := mulLat_fin γ _ f2 s2
  have key : ∀ z, z ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat (q.under (𝓞 D.host.F)) (Formalism.L2.Forms.mulLat γ.1 (clsCrd D u i hi c')) ↔
      z ∈ GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat (q.under (𝓞 D.host.F)) (clsCrd D u i hi c) := by
    by_cases h0 : i = 0 ∨ i = D.R.m
    · have hS := hAd.1 h0
      exact locLat_of_adStep _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.cls i hi h0).lev.Lb_fin f1 f2
        (fun κ hκ X => stepLevel_stab _ κ hκ X) ((T.cls i hi h0).y_lat c) ((T.cls i hi h0).y_lat c') hS hq
    · have h1 : 1 ≤ i := by omega
      have h2 : i + 1 ≤ D.R.m := by omega
      obtain ⟨hβ, hS⟩ := hAd.2 h1 h2
      exact locLat_of_adStep _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.ch i h1 h2 (chOf i c)).lev.Lb_fin f1 f2
        (fun κ hκ X => stepLevel_stab _ κ hκ X) ((T.ch i h1 h2 (chOf i c)).y_lat ⟨c, rfl⟩)
        ((T.ch i h1 h2 (chOf i c)).y_lat ⟨c', hβ⟩) hS hq
  exact le_antisymm (locP_le_of_locLat_le q _ _ f1 s1 fun z hz => (key z).1 hz)
    (locP_le_of_locLat_le q _ _ f3 s3 fun z hz => (key z).2 hz)

set_option maxHeartbeats 4000000 in

theorem use₆ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (hi : i ≤ (I.rec7 l Z).R.m) v (c c' : ((I.rec7 l Z).mem u).C.cls i) (γ : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), AdC (F u) i hi c c' γ ((F u).atT.eV v).1 → ∀ q : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E), q.under (𝓞 (I.rec7 l Z).host.F) ≠ ((F u).atT.eV v).1 → Formalism.HermitianLatticesTheory.localization₂ q.asIdeal (Formalism.L2.Forms.mulLat γ.1 (clsCrd (I.rec7 l Z) u i hi c')) = Formalism.HermitianLatticesTheory.localization₂ q.asIdeal (clsCrd (I.rec7 l Z) u i hi c) := by
  intro B X I _ _ l Z H F _ _ u i hi v c c' γ hAd q hq
  exact sameoff_gen (F u) i hi _ c c' γ hAd q hq

end GlobalTheory.Mem.Col2.SameOff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRelationClassesCoordinates
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt

open scoped TensorProduct

theorem reGL_rfl (n : ℕ) (R : Type) [CommRing R] (g : GL (Fin n) R) : Formalism.L2.Forms.reGL (rfl : n = n) R g = g := by
  ext a b
  simp [Formalism.L2.Forms.reGL]

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem adStep_re {a b : ℕ} (h : a = b) (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E)
    (U : Subgroup (GL (Fin a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) (y y' : GL (Fin a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (γ : GL (Fin a) E) (w : HeightOneSpectrum (𝓞 F)) (J' : Matrix (Fin b) (Fin b) E)
    (U' : Subgroup (GL (Fin b) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) (z z' : GL (Fin b) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (δ : GL (Fin b) E) (hJ : J' = J.reindex (finCongr h) (finCongr h)) (hU : U' = U.map (Formalism.L2.Forms.reGL h _).toMonoidHom)
    (hz : z = Formalism.L2.Forms.reGL h _ y) (hz' : z' = Formalism.L2.Forms.reGL h _ y') (hδ : δ = Formalism.L2.Forms.reGL h _ γ)
    (H : Formalism.L2.Herm.AdStep σ J' U' z z' δ w) : Formalism.L2.Herm.AdStep σ J U y y' γ w := by
  subst h hJ hU hz hz' hδ
  have hm : U.map (Formalism.L2.Forms.reGL (rfl : a = a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).toMonoidHom = U := by
    ext g
    simp [reGL_rfl]
  rw [hm, reGL_rfl, reGL_rfl, reGL_rfl] at H
  simpa using H

end

theorem toGLb_reindex {E V : Type} [Field E] [AddCommGroup V] [Module E V] {n k : ℕ} (b : Module.Basis (Fin n) E V)
    (h : n = k) (f : V ≃ₗ[E] V) :
    Formalism.L2.Herm.toGLb (b.reindex (finCongr h)) f = Formalism.L2.Forms.reGL h E (Formalism.L2.Herm.toGLb b f) := by
  subst h
  rw [reGL_rfl]
  ext a c
  simp [Formalism.L2.Herm.toGLb]

theorem reGL_trans {a b c : ℕ} (h1 : a = b) (h2 : b = c) (R : Type) [CommRing R] (g : GL (Fin a) R) :
    Formalism.L2.Forms.reGL h2 R (Formalism.L2.Forms.reGL h1 R g) = Formalism.L2.Forms.reGL (h1.trans h2) R g := by
  subst h1 h2
  rw [reGL_rfl, reGL_rfl]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen
variable {D : D7}

theorem ad0 (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)) (hcar : CarH H F) (u : D.what₂.Word)
    (hi : 0 ≤ D.R.m) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 hi))
    (hA : AdC (F u) 0 hi c c' γ.1 ((F u).atT.eV v).1) : AdOf H u 0 c c' (gx 0 hi γ) v := by
  have h0 := hA.1 (Or.inl rfl)
  have hc := hcar.car0 u
  rw [hcar.eV u] at h0
  show Formalism.L2.Herm.Ad0S D H u c c' (gx 0 hi γ) v
  unfold Formalism.L2.Herm.Ad0S
  refine adStep_re (rank_eq_first_level D.R) _ _ _ _ _ _ _ _ _ _ _ _ ?_ hc.U_eq (hc.y_eq c) (hc.y_eq c') ?_ h0
  · ext a b
    simp [gramN, Formalism.BasicNotions.Spaces.gram0]
  · rw [toGLb_reindex, reGL_trans]
    exact (reGL_lin (D.sp.X 0) (rankN D 0 hi) γ.1).symm

theorem adC (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)) (hcar : CarH H F) (u : D.what₂.Word)
    (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hA : AdC (F u) i hi c c' γ.1 ((F u).atT.eV v).1) : Formalism.L2.Herm.AdIS D H u i h1 hi c c' (gx i hi γ) v := by
  obtain ⟨hβ, h0⟩ := hA.2 h1 h2
  have hc := hcar.carC u i h1 h2 (H.chOf u i c)
  rw [hcar.eV u] at h0
  refine ⟨hβ, ?_⟩
  refine adStep_re (rankN D i hi) _ _ _ _ _ _ _ _ _ _ _ _ rfl hc.U_eq (hc.y_eq _) (hc.y_eq _) ?_ h0
  exact (reGL_lin (D.sp.X i) (rankN D i hi) γ.1).symm

theorem adM (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)) (hcar : CarH H F) (u : D.what₂.Word)
    (i : ℕ) (h1 : 1 ≤ i) (hm : i = D.R.m) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hA : AdC (F u) i hi c c' γ.1 ((F u).atT.eV v).1) : Formalism.L2.Herm.AdIS D H u i h1 hi c c' (gx i hi γ) v := by
  subst hm
  have h0 := hA.1 (Or.inr rfl)
  have hc := hcar.carM u
  rw [hcar.eV u] at h0
  have hβ : H.chOf u D.R.m c' = H.chOf u D.R.m c := (chOf_m H u c').trans (chOf_m H u c).symm
  refine ⟨hβ, ?_⟩
  have key : ∀ (β : H.Ch u D.R.m) (e : β = chM H u) (hb : H.chOf u D.R.m c = β) (hb' : H.chOf u D.R.m c' = β),
      Formalism.L2.Herm.AdStep D.sp.cm.sig (D.sp.X D.R.m).gram (H.lev u D.R.m h1 hi β).U
        ((H.cls u D.R.m h1 hi β).y ⟨c, hb⟩) ((H.cls u D.R.m h1 hi β).y ⟨c', hb'⟩)
        (Formalism.L2.Herm.toGLb (D.sp.X D.R.m).frame (gx D.R.m hi γ).1) (H.vT u v).1 := by
    intro β e hb hb'
    subst e
    refine adStep_re (rankN D D.R.m hi) _ _ _ _ _ _ _ _ _ _ _ _ rfl hc.U_eq (hc.y_eq c) (hc.y_eq c') ?_ h0
    exact (reGL_lin (D.sp.X D.R.m) (rankN D D.R.m hi) γ.1).symm
  exact key _ (chOf_m H u c) rfl hβ

theorem adOf_of_adC_gen (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)) (hcar : CarH H F)
    (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hA : AdC (F u) i hi c c' γ.1 ((F u).atT.eV v).1) : AdOf H u i c c' (gx i hi γ) v := by
  cases i with
  | zero => exact ad0 H F hcar u hi v c c' γ hA
  | succ i =>
    intro hm
    rcases Nat.lt_or_eq_of_le hi with h | h
    · exact adC H F hcar u (i + 1) (Nat.succ_pos i) h hi v c c' γ hA
    · exact adM H F hcar u (i + 1) (Nat.succ_pos i) h hi v c c' γ hA

end Gen

theorem adOf_of_adC : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (hi : i ≤ (I.rec7 l Z).R.m) v (c c' : ((I.rec7 l Z).mem u).C.cls i) (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)), AdC (F u) i hi c c' γ.1 ((F u).atT.eV v).1 → AdOf H u i c c' (gx i hi γ) v := by
  intro B X I _ _ l Z H F _ hcar u i hi v c c' γ hA
  exact adOf_of_adC_gen H F hcar u i hi v c c' γ hA

end GlobalTheory.Mem.Col2.HAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicTwoStepMeasureOrthogonalBasesPlaneCompare
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem twoStep_isProd_of_isStdX (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (d : ℕ) (b : Module.Basis (Fin d) F E)
    (s : StdMeas b) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E)
    (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E)
    (y : Fin 1 → Fin M → E) (c : F) (hS : StepData σ J x a B J') (hc : c ≠ 0)
    (hy : hE σ J' (y 0) (y 0) = algebraMap F E c)
    (ν : Measure (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)) (ν' : Measure (Fin 1 → Fin M → AF F ⊗[F] E))
    (N : Measure (Fin 2 → Fin (M + 1) → AF F ⊗[F] E))
    (hν : IsStdX s σ J a ν) (hν' : IsStdX s σ J' c ν') (hN : TwoStep (AF F) σ J x B ν ν' N) :
    ∃ mi mi' Ni, ∃ (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E))
      (mv' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
      (Nv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 2 → Fin (M + 1) → Fv F v ⊗[F] E)),
      FibAt (Ainf F) σ J (tupMeas s.lamI 1 (M + 1)) s.nuI (algebraMap F _ a) mi ∧
      FibAt (Ainf F) σ J' (tupMeas s.lamI 1 M) s.nuI (algebraMap F _ c) mi' ∧
      TwoStep (Ainf F) σ J x B mi mi' Ni ∧
      (∀ v, FibAt (Fv F v) σ J (tupMeas (s.lamV v) 1 (M + 1)) (s.nuV v) (algebraMap F _ a) (mv v)) ∧
      (∀ v, FibAt (Fv F v) σ J' (tupMeas (s.lamV v) 1 M) (s.nuV v) (algebraMap F _ c) (mv' v)) ∧
      (∀ v, TwoStep (Fv F v) σ J x B (mv v) (mv' v) (Nv v)) ∧ IsProd b N Ni Nv := by
  obtain ⟨mi, mv, hfi, hfv, hP⟩ := hν
  obtain ⟨mi', mv', hfi', hfv', hP'⟩ := hν'
  have hJ : IsHermND σ J := hS.1
  have ha : a ≠ 0 := hS.2.1
  have hx : hE σ J (x 0) (x 0) = algebraMap F E a := hS.2.2.1
  have hJ' : IsHermND σ J' := hS.2.2.2.2.2
  obtain ⟨hNi, hNv⟩ := nice_ainf_fv F
  have oi := GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hCM (Ainf F) hNi (M + 1) J x a s.lamI s.nuI mi hJ ha hx
    s.haar_lamI s.haar_nuI hfi
  have oi' := GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hCM (Ainf F) hNi M J' y c s.lamI s.nuI mi' hJ' hc hy
    s.haar_lamI s.haar_nuI hfi'
  have ov := fun v => GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hCM (Fv F v) (hNv v) (M + 1) J x a (s.lamV v) (s.nuV v)
    (mv v) hJ ha hx (s.haar_lamV v) (s.haar_nuV v) (hfv v)
  have ov' := fun v => GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hCM (Fv F v) (hNv v) M J' y c (s.lamV v) (s.nuV v)
    (mv' v) hJ' hc hy (s.haar_lamV v) (s.haar_nuV v) (hfv' v)
  obtain ⟨Ni, hTi, -⟩ := GlobalTheory.T.existsUnique_unitaryTwoStepPairMeasure F E σ hCM (Ainf F) M J x a B J' mi mi' hS oi.2.1 hP.1.1
    hP'.1.1 oi'.1
  have hTv : ∀ v, ∃ N', TwoStep (Fv F v) σ J x B (mv v) (mv' v) N' := fun v =>
    (GlobalTheory.T.existsUnique_unitaryTwoStepPairMeasure F E σ hCM (Fv F v) M J x a B J' (mv v) (mv' v) hS (ov v).2.1 (hP.1.2.1 v)
      (hP'.1.2.1 v) (ov' v).1).exists
  choose Nv hTv using hTv
  exact ⟨mi, mi', Ni, mv, mv', Nv, hfi, hfi', hTi, hfv, hfv', hTv,
    GlobalTheory.T.adelicTwoStepMeasure_isRestrictedProduct_local F E σ hCM d b M J x a B J' ν mi mv ν' mi' mv' N Ni Nv hS hP hP' oi.2.1
      (fun v => (ov v).2.1) oi'.1 (fun v => (ov' v).1) hTi hTv hN⟩

private theorem prInf_inclR_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (e : E) : prInf (inclR (AF F) e) = inclR (Ainf F) e := by
  show (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) (1 ⊗ₜ[F] e) = 1 ⊗ₜ[F] e
  first
  | rfl
  | (erw [Algebra.TensorProduct.map_tmul, map_one]; rfl)

private theorem prV_inclR_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (e : E) : prV v (inclR (AF F) e) = inclR (Fv F v) e := by
  show (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E))
      ((Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)) (1 ⊗ₜ[F] e)) = 1 ⊗ₜ[F] e
  first
  | rfl
  | (erw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, map_one, map_one]; rfl)

theorem twoStep_adelic_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b), ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x₁ : Fin 1 → Fin (M + 1) → E) (a₁ : F) (B₁ : Matrix (Fin (M + 1)) (Fin M) E) (J₁' : Matrix (Fin M) (Fin M) E) (x₂ : Fin 1 → Fin (M + 1) → E) (a₂ : F) (B₂ : Matrix (Fin (M + 1)) (Fin M) E) (J₂' : Matrix (Fin M) (Fin M) E) (y₁ y₂ : Fin 1 → Fin M → E) (b₁ b₂ : F) (γ : GL (Fin 2) E), StepData σ J x₁ a₁ B₁ J₁' → StepData σ J x₂ a₂ B₂ J₂' → b₁ ≠ 0 → b₂ ≠ 0 → hE σ J₁' (y₁ 0) (y₁ 0) = algebraMap F E b₁ → hE σ J₂' (y₂ 0) (y₂ 0) = algebraMap F E b₂ → ![x₂ 0, B₂.mulVec (y₂ 0)] = lrAct 1 (γ : Matrix (Fin 2) (Fin 2) E) ![x₁ 0, B₁.mulVec (y₁ 0)] → ∀ (ν₁ ν₂ : Measure (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)) (ν₁' ν₂' : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (N₁ N₂ : Measure (Fin 2 → Fin (M + 1) → AF F ⊗[F] E)), IsStdX s σ J a₁ ν₁ → IsStdX s σ J₁' b₁ ν₁' → IsStdX s σ J a₂ ν₂ → IsStdX s σ J₂' b₂ ν₂' → TwoStep (AF F) σ J x₁ B₁ ν₁ ν₁' N₁ → TwoStep (AF F) σ J x₂ B₂ ν₂ ν₂' N₂ → N₂ = N₁.map (lrAct 1 ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR (AF F)))) := by
  intro F E _ _ _ _ _ σ hCM d b s M J x₁ a₁ B₁ J₁' x₂ a₂ B₂ J₂' y₁ y₂ b₁ b₂ γ hS₁ hS₂ hb₁ hb₂ hy₁
    hy₂ hγ ν₁ ν₂ ν₁' ν₂' N₁ N₂ hν₁ hν₁' hν₂ hν₂' hN₁ hN₂
  obtain ⟨u, hu, hloc⟩ := GlobalTheory.T.twoStepMeasure_orthogonalBasis_swap_local F E σ hCM M J x₁ a₁ B₁ J₁' x₂ a₂ B₂ J₂' y₁ y₂ b₁ b₂ γ
    hS₁ hS₂ hb₁ hb₂ hy₁ hy₂ hγ
  obtain ⟨mi₁, mi₁', Ni₁, mv₁, mv₁', Nv₁, hfi₁, hfi₁', hTi₁, hfv₁, hfv₁', hTv₁, hP₁⟩ :=
    twoStep_isProd_of_isStdX F E σ hCM d b s M J x₁ a₁ B₁ J₁' y₁ b₁ hS₁ hb₁ hy₁ ν₁ ν₁' N₁
      hν₁ hν₁' hN₁
  obtain ⟨mi₂, mi₂', Ni₂, mv₂, mv₂', Nv₂, hfi₂, hfi₂', hTi₂, hfv₂, hfv₂', hTv₂, hP₂⟩ :=
    twoStep_isProd_of_isStdX F E σ hCM d b s M J x₂ a₂ B₂ J₂' y₂ b₂ hS₂ hb₂ hy₂ ν₂ ν₂' N₂
      hν₂ hν₂' hN₂
  obtain ⟨hNi, hNv⟩ := nice_ainf_fv F

  have ei := hloc (Ainf F) hNi s.lamI s.nuI mi₁ mi₂ mi₁' mi₂' Ni₁ Ni₂ s.haar_lamI s.haar_nuI
    hfi₁ hfi₁' hfi₂ hfi₂' hTi₁ hTi₂
  have ev := fun v => hloc (Fv F v) (hNv v) (s.lamV v) (s.nuV v) (mv₁ v) (mv₂ v) (mv₁' v)
    (mv₂' v) (Nv₁ v) (Nv₂ v) (s.haar_lamV v) (s.haar_nuV v) (hfv₁ v) (hfv₁' v) (hfv₂ v)
    (hfv₂' v) (hTv₁ v) (hTv₂ v)

  have hmap := GlobalTheory.T.isRestrictedProductTupleMeasure_map_leftRightAction F E d b 2 (M + 1) N₁ Ni₁ Nv₁ 1
    (Matrix.GeneralLinearGroup.map (inclR (AF F)) γ) hP₁
  have hγA : ((Matrix.GeneralLinearGroup.map (inclR (AF F)) γ : GL (Fin 2) (AF F ⊗[F] E)) :
      Matrix (Fin 2) (Fin 2) (AF F ⊗[F] E)) = (γ : Matrix (Fin 2) (Fin 2) E).map (inclR (AF F)) :=
    rfl
  have hγi : ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR (AF F))).map prInf =
      (γ : Matrix (Fin 2) (Fin 2) E).map (inclR (Ainf F)) := by
    ext i j; exact prInf_inclR_eq _
  have hγv : ∀ v, ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR (AF F))).map (prV v) =
      (γ : Matrix (Fin 2) (Fin 2) E).map (inclR (Fv F v)) := by
    intro v; ext i j; exact prV_inclR_eq v _
  have h1i : (1 : Matrix (Fin (M + 1)) (Fin (M + 1)) (AF F ⊗[F] E)).map prInf = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have h1v : ∀ v, (1 : Matrix (Fin (M + 1)) (Fin (M + 1)) (AF F ⊗[F] E)).map (prV v) = 1 :=
    fun v => Matrix.map_one _ (map_zero _) (map_one _)
  rw [hγA] at hmap
  simp only [Units.val_one, h1i, h1v, hγi, hγv] at hmap

  obtain ⟨hfin, hprod⟩ := GlobalTheory.T.product_formula_haarModulus_cmField_element F E σ hCM u hu
  have hsc := GlobalTheory.T.restrictedProduct_measure_smul_factors_eq_smul F E d b 2 (M + 1) _ _ _ (modu (Ainf F ⊗[F] E) (inclR (Ainf F) u))
    (fun v => modu (Fv F v ⊗[F] E) (inclR (Fv F v) u)) hmap hfin
  simp only [hprod, one_smul] at hsc
  have hv : Nv₂ = fun v => modu (Fv F v ⊗[F] E) (inclR (Fv F v) u) •
      (Nv₁ v).map (lrAct 1 ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR (Fv F v)))) := funext ev
  rw [← ei, ← hv] at hsc
  exact ((GlobalTheory.T.restrictedProductMeasure_basic_properties F E d b 2 (M + 1) N₂ Ni₂ Nv₂ hP₂).2.2.1 _ hsc).symm

end GlobalTheory.GaugeEx
end

