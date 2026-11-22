import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZeroMemLatOf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteAdelicLatticeTransportLaws
section
namespace GlobalTheory.Ker.Mov

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.AdLat.Translate GlobalTheory.SW
open scoped TensorProduct Matrix nonZeroDivisors

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def Into (F : Type) [Field F] [NumberField F] [Algebra F E] (m : Matrix (Fin n) (Fin n) (RA F E))
    (L L' : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ z ∈ hat F (L : Set (Fin n → E)), m *ᵥ z ∈ hat F (L' : Set (Fin n → E))

def Onto (F : Type) [Field F] [NumberField F] [Algebra F E] (m : Matrix (Fin n) (Fin n) (RA F E))
    (L L' : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ u, u ∈ hat F (L' : Set (Fin n → E)) ↔ ∃ u₀ ∈ hat F (L : Set (Fin n → E)), u = m *ᵥ u₀

theorem into_of_fv {m : Matrix (Fin n) (Fin n) (RA F E)} {L L' : Submodule (𝓞 E) (Fin n → E)}
    (h : ∀ x ∈ L, m *ᵥ fv F x ∈ hat F (L' : Set (Fin n → E))) : Into F m L L' :=
  fun _ hz => mulVec_mem_hat (L := L') (fun x hx => h x hx) hz

theorem onto_iff {m m' : Matrix (Fin n) (Fin n) (RA F E)} (h : m * m' = 1)
    {L L' : Submodule (𝓞 E) (Fin n → E)} : Onto F m L L' ↔ Into F m L L' ∧ Into F m' L' L := by
  have h' : m' * m = 1 := mul_eq_one_comm.1 h
  constructor
  · intro H
    refine ⟨fun z hz => (H _).2 ⟨z, hz, rfl⟩, fun z hz => ?_⟩
    obtain ⟨u, hu, rfl⟩ := (H _).1 hz
    rwa [Matrix.mulVec_mulVec, h', Matrix.one_mulVec]
  · rintro ⟨H, H'⟩ u
    constructor
    · intro hu
      exact ⟨m' *ᵥ u, H' u hu, by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]⟩
    · rintro ⟨u, hu, rfl⟩
      exact H u hu

omit [NumberField E] in
theorem map_mulVec_fv (P : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    (P.map fun c => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c : RA F E)) *ᵥ fv F x = fv F (P *ᵥ x) := by
  funext i
  simp [fv, Matrix.mulVec, dotProduct, TensorProduct.tmul_sum]

omit [NumberField E] in
theorem fv_eq_zero {x : Fin n → E} (h : fv F x = 0) : x = 0 := by
  haveI : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
    let v : HeightOneSpectrum (𝓞 F) :=
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
    refine ⟨0, 1, fun h => ?_⟩
    have h2 : (0 : v.adicCompletion F) = 1 := congrArg (fun x : FiniteAdeleRing (𝓞 F) F => x v) h
    exact zero_ne_one h2
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F (FiniteAdeleRing (𝓞 F) F)).injective
  funext i
  apply hinj
  rw [Pi.zero_apply, map_zero]
  exact congrFun h i

theorem onto_mapL (g : GL (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) :
    Onto F ((g : Matrix (Fin n) (Fin n) E).map fun c => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c : RA F E))
      L (mapL g L) := by
  have hm : ((g : Matrix (Fin n) (Fin n) E).map fun c => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c : RA F E)) *
      (((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map
        fun c => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c : RA F E)) = 1 := by
    have := Matrix.map_mul (L := (g : Matrix (Fin n) (Fin n) E))
      (M := ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))
      (f := (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E).toRingHom)
    rw [Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this.symm
  refine (onto_iff hm).2 ⟨into_of_fv fun x hx => ?_, into_of_fv ?_⟩
  · rw [map_mulVec_fv]
    exact fv_mem_hat ⟨x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [map_mulVec_fv]
    refine fv_mem_hat ?_
    change ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ ((g : Matrix (Fin n) (Fin n) E) *ᵥ x) ∈ L
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

theorem span_eq_top_of_into {m m' : Matrix (Fin n) (Fin n) (RA F E)} (h : m * m' = 1)
    {L L' : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG) (hs : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (H : Into F m L L') : Submodule.span E (L' : Set (Fin n → E)) = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  obtain ⟨-, -, -, h4⟩ := hat_rational_points_and_approx F E n L hL hs
  let P : Matrix (Fin n) (Fin n) E := LinearMap.toMatrix' (LinearMap.pi fun _ => φ)
  have hP : ∀ x, P *ᵥ x = fun _ => φ x := fun x => by
    simp only [P, LinearMap.toMatrix'_mulVec]; rfl
  have hz : ∀ z ∈ hat F (L' : Set (Fin n → E)),
      (P.map fun c => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c : RA F E)) *ᵥ z = 0 := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, -, x, hx, rfl⟩ := hz
      have hx0 : φ x = 0 := hφ (Submodule.subset_span hx)
      rw [gen_eq, Matrix.mulVec_smul, map_mulVec_fv, hP, hx0]
      exact (congrArg _ fv_zero).trans (smul_zero _)
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy, add_zero]
    | neg x _ hx => rw [Matrix.mulVec_neg, hx, neg_zero]
  apply hφ0
  have key : ∀ x, (fun _ : Fin n => φ x) = 0 := by
    intro x
    obtain ⟨d, hd, hdx⟩ := h4 (m' *ᵥ fv F x)
    have h1 := hz _ (H _ hdx)
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec (fv F x) m m', h, Matrix.one_mulVec,
      map_mulVec_fv, hP] at h1
    exact fv_eq_zero (F := F) (nsmul_cancel hd (h1.trans (smul_zero d).symm))
  refine (Pi.basisFun E (Fin n)).ext fun i => ?_
  exact congrFun (key _) i

theorem into_smul {m : Matrix (Fin n) (Fin n) (RA F E)} {L L' : Submodule (𝓞 E) (Fin n → E)}
    (H : Into F m L L') (𝔞 : Ideal (𝓞 E)) : Into F m (𝔞 • L) (𝔞 • L') := by
  have : 𝔞 • L ≤ pre m (𝔞 • L') := by
    refine Submodule.smul_le.2 fun a ha x hx => ?_
    rw [mem_pre, show a • x = (a : E) • x from rfl, fv_smul, Matrix.mulVec_smul]
    exact Scale.smul_mem_hat (fun y hy => Submodule.smul_mem_smul ha hy) (H _ (fv_mem_hat hx))
  exact into_of_fv this

theorem into_idq {m : Matrix (Fin n) (Fin n) (RA F E)} {L L' : Submodule (𝓞 E) (Fin n → E)}
    (H : Into F m L L') (𝔞 𝔟 : Ideal (𝓞 E)) (hb : 𝔟 ≠ ⊥) : Into F m (idq 𝔞 𝔟 L) (idq 𝔞 𝔟 L') := by
  refine into_of_fv fun v hv => ?_
  have hI : ((𝔟 : FractionalIdeal (𝓞 E)⁰ E)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hb
  have key : ∀ c ∈ (𝔟 : FractionalIdeal (𝓞 E)⁰ E) * (𝔟 : FractionalIdeal (𝓞 E)⁰ E)⁻¹,
      m *ᵥ fv F (c • v) ∈ hat F (idq 𝔞 𝔟 L' : Set (Fin n → E)) := by
    intro c hc
    refine FractionalIdeal.mul_induction_on hc ?_ ?_
    · intro a ha c hc
      obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
      rw [mul_comm, mul_smul, fv_smul, Matrix.mulVec_smul]
      refine Scale.smul_mem_hat ?_ (into_smul H 𝔞 _ (fv_mem_hat (hv b hb)))
      intro y hy b' hb'
      have hbc : algebraMap (𝓞 E) E b' * c ∈
          (𝔟 : FractionalIdeal (𝓞 E)⁰ E) * (𝔟 : FractionalIdeal (𝓞 E)⁰ E)⁻¹ :=
        FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨b', hb', rfl⟩) hc
      rw [mul_inv_cancel₀ hI, FractionalIdeal.mem_one_iff] at hbc
      obtain ⟨r, hr⟩ := hbc
      have : b' • c • y = r • y := by
        change algebraMap (𝓞 E) E b' • c • y = algebraMap (𝓞 E) E r • y
        rw [smul_smul, hr]
      rw [this]
      exact Submodule.smul_mem _ r hy
    · intro x y hx hy
      rw [add_smul, fv_add, Matrix.mulVec_add]
      exact add_mem hx hy
  have := key 1 (by rw [mul_inv_cancel₀ hI]; exact FractionalIdeal.one_mem_one _)
  rwa [one_smul] at this

theorem idq_fg {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG) (𝔞 𝔟 : Ideal (𝓞 E)) (hb : 𝔟 ≠ ⊥) :
    (idq 𝔞 𝔟 L).FG := by
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  have hb' : algebraMap (𝓞 E) E b ≠ 0 := fun h => hb0 (RingOfIntegers.coe_injective (by simpa using h))
  have hinj : Function.Injective (b • (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] (Fin n → E))) := by
    intro x y hxy
    exact smul_right_injective _ hb' hxy
  refine Submodule.fg_of_fg_map_injective _ hinj ?_
  have hle : (idq 𝔞 𝔟 L).map (b • (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] (Fin n → E))) ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.smul_le_right (hx b hb)
  have : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian _ hL
  exact (isNoetherian_submodule.1 this) _ hle

theorem idq_span {L : Submodule (𝓞 E) (Fin n → E)} (hs : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (𝔞 𝔟 : Ideal (𝓞 E)) (ha : 𝔞 ≠ ⊥) : Submodule.span E (idq 𝔞 𝔟 L : Set (Fin n → E)) = ⊤ := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha
  have ha' : algebraMap (𝓞 E) E a ≠ 0 := fun h => ha0 (RingOfIntegers.coe_injective (by simpa using h))
  rw [eq_top_iff, ← hs, Submodule.span_le]
  intro x hx
  have h1 : algebraMap (𝓞 E) E a • x ∈ idq 𝔞 𝔟 L := fun b _ =>
    Submodule.smul_mem _ b (Submodule.smul_mem_smul ha hx)
  have := (Submodule.span E (idq 𝔞 𝔟 L : Set (Fin n → E))).smul_mem (algebraMap (𝓞 E) E a)⁻¹
    (Submodule.subset_span h1)
  rwa [smul_smul, inv_mul_cancel₀ ha', one_smul] at this

theorem onto_laws (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG)
    (hs : Submodule.span E (L : Set (Fin n → E)) = ⊤) (m m' : Matrix (Fin n) (Fin n) (RA F E)) (h : m * m' = 1) :
    (∃ L' : Submodule (𝓞 E) (Fin n → E), (L'.FG ∧ Submodule.span E (L' : Set (Fin n → E)) = ⊤) ∧ Onto F m L L') ∧
    ∀ L' : Submodule (𝓞 E) (Fin n → E), L'.FG → Onto F m L L' →
      Submodule.span E (L' : Set (Fin n → E)) = ⊤ ∧ Onto F m' L' L ∧
      (∀ L'' : Submodule (𝓞 E) (Fin n → E), L''.FG → Onto F m L L'' → L'' = L') ∧
      (∀ m₂ (L'' : Submodule (𝓞 E) (Fin n → E)), Onto F m₂ L' L'' → Onto F (m₂ * m) L L'') ∧
      ∀ 𝔞 𝔟 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → Onto F m (𝔞 • L) (𝔞 • L') ∧
        Onto F m (idq 𝔞 𝔟 L) (idq 𝔞 𝔟 L') ∧ (idq 𝔞 𝔟 L).FG ∧
        Submodule.span E (idq 𝔞 𝔟 L : Set (Fin n → E)) = ⊤ := by
  have h' : m' * m = 1 := mul_eq_one_comm.1 h
  constructor
  · obtain ⟨Λ, -, h2, h3, h4⟩ := exists_lattice_latOf F E n L ⟨m, m', h, h'⟩ hL hs
    refine ⟨Λ, ⟨h2, h3⟩, fun u => ?_⟩
    rw [← SetLike.mem_coe, h4]
    exact ⟨fun ⟨z, hz, e⟩ => ⟨z, hz, e.symm⟩, fun ⟨z, hz, e⟩ => ⟨z, hz, e.symm⟩⟩
  · intro L' hL' H
    obtain ⟨H1, H2⟩ := (onto_iff h).1 H
    have hs' := span_eq_top_of_into h hL hs H1
    refine ⟨hs', (onto_iff h').2 ⟨H2, H1⟩, fun L'' hL'' K => ?_, fun m₂ L'' K u => ?_,
      fun 𝔞 𝔟 ha hb => ⟨(onto_iff h).2 ⟨into_smul H1 𝔞, into_smul H2 𝔞⟩,
        (onto_iff h).2 ⟨into_idq H1 𝔞 𝔟 hb, into_idq H2 𝔞 𝔟 hb⟩, idq_fg hL 𝔞 𝔟 hb, idq_span hs 𝔞 𝔟 ha⟩⟩
    · have hs'' := span_eq_top_of_into h hL hs ((onto_iff h).1 K).1
      ext v
      rw [← (hat_rational_points_and_approx F E n L'' hL'' hs'').1,
        ← (hat_rational_points_and_approx F E n L' hL' hs').1, K, H]
    · rw [K]
      constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨z, hz, rfl⟩ := (H w).1 hw
        exact ⟨z, hz, Matrix.mulVec_mulVec _ _ _⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨m *ᵥ z, H1 z hz, (Matrix.mulVec_mulVec _ _ _).symm⟩

end GlobalTheory.Ker.Mov

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Ker.isMov_laws : ∀ (D : D7) (k : ℕ) (L : Lt D.host.E k), (L.FG ∧ Submodule.span D.host.E (L : Set (Fin k → D.host.E)) = ⊤) → (∀ v, toAf v ∈ hatV L ↔ v ∈ L) ∧ IsMov 1 L L ∧ (∀ ga : GL (Fin k) D.host.E, IsMov ((ga : Matrix (Fin k) (Fin k) D.host.E).map fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x) L (mapL ga L)) ∧ ∀ m m' : Matrix (Fin k) (Fin k) (AfE D), m * m' = 1 → (∃ L' : Lt D.host.E k, (L'.FG ∧ Submodule.span D.host.E (L' : Set (Fin k → D.host.E)) = ⊤) ∧ IsMov m L L') ∧ ∀ L' : Lt D.host.E k, L'.FG → IsMov m L L' → Submodule.span D.host.E (L' : Set (Fin k → D.host.E)) = ⊤ ∧ IsMov m' L' L ∧ (∀ L'' : Lt D.host.E k, L''.FG → IsMov m L L'' → L'' = L') ∧ (∀ m₂ (L'' : Lt D.host.E k), IsMov m₂ L' L'' → IsMov (m₂ * m) L L'') ∧ ∀ 𝔞 𝔟 : Ideal (𝓞 D.host.E), 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → IsMov m (𝔞 • L) (𝔞 • L') ∧ IsMov m (idq 𝔞 𝔟 L) (idq 𝔞 𝔟 L') ∧ (idq 𝔞 𝔟 L).FG ∧ Submodule.span D.host.E (idq 𝔞 𝔟 L : Set (Fin k → D.host.E)) = ⊤ := by
  rintro D k L ⟨hL, hs⟩
  refine ⟨(GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E k L hL hs).1, fun u => ?_,
    fun ga => GlobalTheory.Ker.Mov.onto_mapL (F := D.host.F) ga L,
    fun m m' h => GlobalTheory.Ker.Mov.onto_laws (F := D.host.F) L hL hs m m' h⟩
  simp only [Matrix.one_mulVec, exists_eq_right']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPointsClassicalModelRealVectorSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KerReal

open GlobalTheory.FockCompare

variable {D : D7}

theorem infPart_eq_zero {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ) (a : AE D)
    (ha : ∀ τ, θ τ (infPart D a) = 0) : infPart D a = 0 := by

  let e0 : AF D.host.F := ((1 : Ainf D.host.F), (0 : Af D.host.F))
  let e : AE D := e0 ⊗ₜ[D.host.F] (1 : D.host.E)
  have hi : infPart D e = 1 := by
    simp only [infPart, e, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq]
    rfl
  have hf : finPart D e = 0 := by
    simp only [finPart, e, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq]
    exact TensorProduct.zero_tmul _ _
  have he : e * a = 0 :=
    h.ext _ (by rw [map_mul, hf, zero_mul]) fun τ => by rw [map_mul, hi, one_mul]; exact ha τ
  calc infPart D a = infPart D (e * a) := by rw [map_mul, hi, one_mul]
    _ = 0 := by rw [he, map_zero]

variable {S T : HSp D}

def realOf (C : Ctx S T) (σ : (D.what₂.Tau → ℂ) →+ AE D) : WR C.X S.rank →+ WO S T where
  toFun v := Matrix.of fun a k => σ fun τ => conj (v (C.m.e τ) k a)
  map_zero' := by
    funext a k
    have : (fun τ : D.what₂.Tau => conj ((0 : WR C.X S.rank) (C.m.e τ) k a)) = 0 := by
      funext τ; simp
    show σ _ = 0
    rw [this, σ.map_zero]
  map_add' x y := by
    funext a k
    have : (fun τ : D.what₂.Tau => conj ((x + y) (C.m.e τ) k a)) =
        (fun τ => conj (x (C.m.e τ) k a)) + fun τ => conj (y (C.m.e τ) k a) := by
      funext τ; simp
    show σ _ = σ _ + σ _
    rw [this, σ.map_add]

theorem realPt_apply (C : Ctx S T) (w : WO S T) (s : C.X.Ψ) (k : Fin S.rank) (a : Fin T.rank) :
    C.realPt w s k a = conj (C.θ (C.m.e.symm s) (infPart D (w a k))) := rfl

theorem realPt_sub (C : Ctx S T) (w w' : WO S T) : C.realPt (w - w') = C.realPt w - C.realPt w' := by
  funext s k a
  simp only [realPt_apply, Matrix.sub_apply, map_sub, Pi.sub_apply]

theorem realPt_add (C : Ctx S T) (w w' : WO S T) : C.realPt (w + w') = C.realPt w + C.realPt w' := by
  funext s k a
  simp only [realPt_apply, Matrix.add_apply, map_add, Pi.add_apply]

theorem map_actO {B : Type} [CommRing B] (f : AE D →+* B) (h : GA D S) (g : GA D T) (w : WO S T) :
    (actO S T h g w).map f = (mt T g).map f * w.map f * (mt S h⁻¹).map f := by
  unfold actO
  rw [Matrix.map_mul, Matrix.map_mul]

private theorem isLineAt_apply_unique {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ) {m n : ℕ}
    {τ : D.what₂.Tau} {z : Matrix (Fin m) (Fin n) ℂ} {L L' : ℝ →+ Mx D m n}
    (hL : IsLineAt θ τ z L) (hL' : IsLineAt θ τ z L') (t : ℝ) : L t = L' t := by
  unfold IsLineAt at hL hL'
  refine Matrix.ext fun a k => sub_eq_zero.mp (h.ext _ ?_ fun τ' => ?_)
  · have h1 := congrFun (congrFun (hL.2.1 t) a) k
    have h2 := congrFun (congrFun (hL'.2.1 t) a) k
    simp only [Matrix.map_apply, Matrix.zero_apply] at h1 h2
    rw [map_sub, h1, h2, sub_zero]
  · have h1 := congrFun (congrFun (hL.2.2 t τ') a) k
    have h2 := congrFun (congrFun (hL'.2.2 t τ') a) k
    simp only [compAt, Matrix.map_apply] at h1 h2
    rw [map_sub, map_sub, h1, h2, sub_self]

theorem real_points : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∃ R : WR C.X S.rank →+ WO S T, Continuous R ∧ Continuous C.realPt ∧ (∀ w w', C.realPt (w + w') = C.realPt w + C.realPt w') ∧ (∀ v, IsRealPt (R v) ∧ C.realPt (R v) = v) ∧ (∀ w, IsRealPt w → R (C.realPt w) = w) ∧ (∀ w, IsFinPt (w - R (C.realPt w))) ∧ (∀ u, IsFinPt u → C.realPt u = 0) ∧ (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ), lineAt C.θ τ z t = R (t • (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank))) ∧ ∀ (h : GA D S) (g : GA D T) (w : WO S T), (IsRealPt w → IsRealPt (actO S T h g w)) ∧ (IsFinPt w → IsFinPt (actO S T h g w)) ∧ ∀ τ, compAt C.θ τ (actO S T h g w) = compAt C.θ τ (mt T g) * compAt C.θ τ w * compAt C.θ τ (mt S h⁻¹) := by
  intro D S T C
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart C.inf

  have hRfin : ∀ v a k, finPart D (realOf C σ v a k) = 0 := fun v a k =>
    hσ.fin fun τ => conj (v (C.m.e τ) k a)
  have hRcomp : ∀ v a k τ, C.θ τ (infPart D (realOf C σ v a k)) = conj (v (C.m.e τ) k a) :=
    fun v a k τ => hσ.comp (fun τ => conj (v (C.m.e τ) k a)) τ
  have hRreal : ∀ v, IsRealPt (realOf C σ v) := by
    intro v
    show (realOf C σ v).map (finPart D) = 0
    refine Matrix.ext fun a k => ?_
    rw [Matrix.map_apply, hRfin]
    rfl
  have hReal : ∀ v, C.realPt (realOf C σ v) = v := by
    intro v
    funext s k a
    rw [realPt_apply, hRcomp]
    simp
  have hRcont : Continuous (realOf C σ) := by
    refine continuous_pi fun a => continuous_pi fun k => ?_
    exact hσ.cont.comp (continuous_pi fun τ => Complex.continuous_conj.comp
      ((continuous_apply a).comp ((continuous_apply k).comp (continuous_apply (C.m.e τ)))))
  refine ⟨realOf C σ, hRcont, ?_, fun w w' => realPt_add C w w', fun v => ⟨hRreal v, hReal v⟩, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine continuous_pi fun s => continuous_pi fun k => continuous_pi fun a => ?_
    simp only [realPt_apply]
    exact Complex.continuous_conj.comp ((GlobalTheory.FockCompare.continuous_comp C.inf _).comp
      ((continuous_apply k).comp (continuous_apply a)))
  ·
    intro w hw
    have hw' : w.map (finPart D) = 0 := hw
    refine Matrix.ext fun a k => sub_eq_zero.mp (hσ.ext _ ?_ fun τ => ?_)
    · have h1 : finPart D (w a k) = 0 := by simpa using congrFun (congrFun hw' a) k
      rw [map_sub, hRfin, h1, sub_zero]
    · rw [map_sub, map_sub, hRcomp, realPt_apply]
      simp
  ·
    intro w
    show (w - realOf C σ (C.realPt w)).map (infPart D) = 0
    refine Matrix.ext fun a k => ?_
    rw [Matrix.map_apply, Matrix.zero_apply, Matrix.sub_apply]
    refine infPart_eq_zero hσ _ fun τ => ?_
    rw [map_sub, map_sub, hRcomp, realPt_apply]
    simp
  ·
    intro u hu
    have hu' : u.map (infPart D) = 0 := hu
    funext s k a
    have h1 : infPart D (u a k) = 0 := by simpa using congrFun (congrFun hu' a) k
    simp [realPt_apply, h1]
  ·
    intro τ z t
    have hL : IsLineAt C.θ τ z ((realOf C σ).comp
        ((smulAddHom ℝ (WR C.X S.rank)).flip (Pi.single (C.m.e τ) fun k a => conj (z a k)))) := by
      unfold IsLineAt
      refine ⟨hRcont.comp (continuous_id.smul continuous_const), fun t => hRreal _, fun t τ' => ?_⟩
      refine Matrix.ext fun a k => ?_
      simp only [compAt, Matrix.map_apply, AddMonoidHom.coe_comp, Function.comp_apply,
        AddMonoidHom.flip_apply, smulAddHom_apply]
      rw [hRcomp]
      by_cases hτ : τ' = τ
      · subst hτ
        simp [Complex.real_smul]
      · simp [hτ]
    have hE : IsLineAt C.θ τ z (lineAt C.θ τ z) := by
      unfold lineAt
      exact Classical.epsilon_spec ⟨_, hL⟩
    exact isLineAt_apply_unique hσ hE hL t
  ·
    intro h g w
    refine ⟨fun hw => ?_, fun hw => ?_, fun τ => map_actO ((C.θ τ).comp (infPart D)) h g w⟩
    · have hw' : w.map (finPart D) = 0 := hw
      show (actO S T h g w).map (finPart D) = 0
      rw [map_actO, hw', Matrix.mul_zero, Matrix.zero_mul]
    · have hw' : w.map (infPart D) = 0 := hw
      show (actO S T h g w).map (infPart D) = 0
      rw [map_actO, hw', Matrix.mul_zero, Matrix.zero_mul]

end GlobalTheory.KerReal

end
end

