import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1823
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1830
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1814
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomRowTransportContragredient
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedColumnLatticeIntegralFrameCoords
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FrameTransport

theorem colLat_inv_mulVec_int {K : Type} [Field K] [NumberField K] {n : ℕ} (fr : GL (Fin n) K)
    (x : Fin n → K) (hx : x ∈ colLat fr) : ∀ i, (fr⁻¹.val *ᵥ x) i ∈ Formalism.UG.intOE K := by
  let M : Submodule (𝓞 K) (Fin n → K) :=
    { carrier := {x | ∀ i, (fr⁻¹.val *ᵥ x) i ∈ Formalism.UG.intOE K}
      add_mem' := fun {a b} ha hb i => by
        simp only [Set.mem_setOf_eq, Matrix.mulVec_add, Pi.add_apply] at ha hb ⊢
        exact add_mem (ha i) (hb i)
      zero_mem' := fun i => by simp
      smul_mem' := fun c a ha i => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have : fr⁻¹.val *ᵥ (c • a) = (algebraMap (𝓞 K) K c) • (fr⁻¹.val *ᵥ a) := by
          rw [← Matrix.mulVec_smul, algebraMap_smul]
        rw [this, Pi.smul_apply, smul_eq_mul]
        exact mul_mem ⟨c, rfl⟩ (ha i) }
  have hle : colLat fr ≤ M := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩ i
    have hcol : (fun a : Fin n => (fr : Matrix (Fin n) (Fin n) K) a j) = fr.val *ᵥ Pi.single j 1 := by
      rw [Matrix.mulVec_single_one]; rfl
    show (fr⁻¹.val *ᵥ (fun a : Fin n => (fr : Matrix (Fin n) (Fin n) K) a j)) i ∈ _
    rw [hcol, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases h : i = j
    · subst h; simp only [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  exact hle hx

theorem inclEAf_intOE_mem {D : D7} (e : D.host.E) (he : e ∈ Formalism.UG.intOE D.host.E) :
    inclEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨e, he⟩, rfl⟩)

set_option maxHeartbeats 1000000 in

theorem hatL_colLat_coord_int {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (y : Fin n → Lev.EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) :
    ∀ i, ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  let S := Formalism.L2.Herm.intAf D.host.F D.host.E
  let P : Matrix (Fin n) (Fin n) (Lev.EAf D) := (Formalism.UG.bc (inclEAf D) fr)⁻¹.val
  have hP : P = (fr⁻¹.val).map (inclEAf D) := rfl
  let M : Submodule S (Fin n → Lev.EAf D) :=
    { carrier := {y | ∀ i, (P *ᵥ y) i ∈ S}
      add_mem' := fun {a b} ha hb i => by
        simp only [Set.mem_setOf_eq, Matrix.mulVec_add, Pi.add_apply] at ha hb ⊢
        exact add_mem (ha i) (hb i)
      zero_mem' := fun i => by simp
      smul_mem' := fun c a ha i => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have : P *ᵥ (c • a) = (c : Lev.EAf D) • (P *ᵥ a) := by
          rw [← Matrix.mulVec_smul]; rfl
        rw [this, Pi.smul_apply, smul_eq_mul]
        exact mul_mem c.2 (ha i) }
  have hle : Submodule.span S ((fun x : Fin n → D.host.E => fun i =>
      Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i)) '' (colLat fr : Set (Fin n → D.host.E))) ≤ M := by
    refine (Submodule.span_le (p := M)).2 ?_
    rintro _ ⟨x, hx, rfl⟩ i
    have h1 := colLat_inv_mulVec_int fr x hx i
    have h2 : (P *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i))) i =
        inclEAf D ((fr⁻¹.val *ᵥ x) i) := by
      rw [hP, RingHom.map_mulVec]; rfl
    show (P *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i))) i ∈ S
    rw [h2]
    exact inclEAf_intOE_mem _ h1
  exact hle hy

end GlobalTheory.FrameTransport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedLatticeMapIdealMulTransport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.HatIdealCarry

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def intOf (b : 𝓞 E) : Formalism.L2.Herm.intAf F E :=
  ⟨Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (algebraMap (𝓞 E) E b),
    Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 E) E b, b, rfl⟩, rfl⟩)⟩

theorem incl_smul (b : 𝓞 E) (l : Fin n → E) :
    (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((b • l) i)) =
      intOf (F := F) b • (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (l i)) := by
  funext i
  show _ = Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (algebraMap (𝓞 E) E b) *
    Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (l i)
  rw [← map_mul, Pi.smul_apply, Algebra.smul_def]

theorem incl_add (a b : Fin n → E) :
    (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((a + b) i)) =
      (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (a i)) +
        (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (b i)) := by
  funext i
  exact map_add _ (a i) (b i)

theorem mulVec_intSmul (M : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (r : Formalism.L2.Herm.intAf F E) (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    M *ᵥ (r • v) = r • (M *ᵥ v) := by
  have e : r • v = (r : E ⊗[F] Formalism.L2.Herm.Af F) • v := rfl
  have e' : r • (M *ᵥ v) = (r : E ⊗[F] Formalism.L2.Herm.Af F) • (M *ᵥ v) := rfl
  rw [e, e', Matrix.mulVec_smul]

theorem intOf_smul_mem (Λ : Submodule (𝓞 E) (Fin n → E))
    (𝔪 : Ideal (𝓞 E)) {b : 𝓞 E} (hb : b ∈ 𝔪) (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    intOf (F := F) b • z ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
  refine Submodule.span_induction
    (p := fun z _ => intOf (F := F) b • z ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ)) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.subset_span ⟨b • x, Submodule.smul_mem_smul hb hx, ?_⟩
    exact incl_smul b x
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a c _ _ ha hc
    rw [smul_add]; exact Submodule.add_mem _ ha hc
  · intro c a _ ha
    rw [smul_comm]; exact Submodule.smul_mem _ c ha

theorem transportGen (uf : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L Λ : Submodule (𝓞 E) (Fin n → E))
    (hL : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := F) L → uf *ᵥ v ∈ Formalism.L2.Herm.hatL (F := F) Λ)
    (𝔪 : Ideal (𝓞 E)) (y : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • L)) : uf *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
  have gen : ∀ w ∈ 𝔪 • L, uf *ᵥ (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (w i)) ∈
      Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
    intro w hw
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro b hb l hl
      rw [incl_smul b l, mulVec_intSmul]
      exact intOf_smul_mem Λ 𝔪 hb _ (hL _ (Submodule.subset_span ⟨l, hl, rfl⟩))
    · intro a c ha hc
      rw [incl_add, Matrix.mulVec_add]
      exact Submodule.add_mem _ ha hc
  refine Submodule.span_induction
    (p := fun y _ => uf *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ)) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨w, hw, rfl⟩
    exact gen w hw
  · rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  · intro a c _ _ ha hc
    rw [Matrix.mulVec_add]; exact Submodule.add_mem _ ha hc
  · intro c a _ ha
    rw [mulVec_intSmul]; exact Submodule.smul_mem _ c ha

end Gen

theorem transport : ∀ {D : D7} {n : ℕ} (uf : GL (Fin n) (Lev.EAf D)) (L Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (y : Fin n → Lev.EAf D), y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • L) → uf.val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) :=
  fun uf L Λ hL 𝔪 y hy => transportGen uf.val L Λ hL 𝔪 y hy

end GlobalTheory.HatIdealCarry
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapPartRightEquivariant
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv

noncomputable section

namespace GlobalTheory.DoublingEvLaw

theorem elim_dot {R : Type} [CommRing R] {κ κ' : Type} [Fintype κ] [Fintype κ'] (u v : κ → R) (x y : κ' → R) :
    Sum.elim u x ⬝ᵥ Sum.elim v y = u ⬝ᵥ v + x ⬝ᵥ y := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem star_schr' {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    {κ : Type} [Fintype κ] (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    star (schr ψ (w.1, -w.2) φ) = schr ψ w (star φ) := by
  funext x
  simp only [schr, Pi.star_apply, star_mul', dotProduct_neg, mul_neg, ← neg_add, AddChar.map_neg_eq_inv]
  rw [Complex.inv_eq_conj (hψ _), Complex.star_def, Complex.conj_conj]

variable {F : Type} [Field F] [NumberField F]

theorem sliceL {κ κ' : Type} [Fintype κ] [Fintype κ'] {Φ : (κ ⊕ κ' → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ'))
    (b : κ' → AF F) : (fun x => Φ (Sum.elim x b)) ∈ schA F κ := by
  have e1 : (fun x => Φ (Sum.elim x b)) = fun x => Φ (GlobalTheory.ThK.Adapt.glue (Equiv.sumComm κ κ') b x) :=
    funext fun x => congrArg Φ (funext fun k => by cases k <;> rfl)
  rw [e1]
  exact GlobalTheory.ThK.Adapt.slice_mem_schA (Equiv.sumComm κ κ') b hΦ

theorem sliceR {κ κ' : Type} [Fintype κ] [Fintype κ'] {Φ : (κ ⊕ κ' → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ'))
    (a : κ → AF F) : (fun x => Φ (Sum.elim a x)) ∈ schA F κ' :=
  GlobalTheory.ThK.Adapt.slice_mem_schA (Equiv.refl (κ ⊕ κ')) a hΦ

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), (∀ x, ‖ψ x‖ = 1) →
    ∀ (κ κ₁ : Type) [Fintype κ] [Fintype κ₁] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ))
      (A₁ B₁ A₂ B₂ : κ → AF F) (a b : κ₁ → AF F),
      (∀ Φ ∈ schA F κ, T (schr ψ (A₁, B₁) Φ) = schr ψ (a, b) (T Φ)) →
      (∀ Φ ∈ schA F κ, T (schr ψ (A₂, B₂) Φ) = schr ψ (a, b) (T Φ)) →
      (∀ φ ∈ schA F (κ ⊕ κ), partR (conjMap T) φ ∈ schA F (κ ⊕ κ₁)) →
      ∀ φ ∈ schA F (κ ⊕ κ), evDbl T (schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ) =
        schr ψ (Sum.elim a a, Sum.elim b (-b)) (evDbl T φ) := by
  intro F _ _ ψ hψ κ κ₁ _ _ T A₁ B₁ A₂ B₂ a b h1 h2 h3 φ hφ
  have hconj : ∀ g ∈ schA F κ, conjMap T (schr ψ (A₂, -B₂) g) = schr ψ (a, -b) (conjMap T g) := by
    intro g hg
    have hs : star g ∈ schA F κ := GlobalTheory.SchAConj.star_mem_schA F κ g hg
    rw [conjMap_apply, conjMap_apply, star_schr' ψ hψ (A₂, B₂) g, h2 _ hs]
    have := star_schr' ψ hψ (a, -b) (T (star g))
    simpa only [neg_neg] using this
  funext s
  have hΨ := h3 φ hφ
  have hslice := sliceL hΨ (s ∘ Sum.inr + a)
  have hinner : (fun x₁ => conjMap T (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂))
      (s ∘ Sum.inr)) = ψ (-((s ∘ Sum.inr) ⬝ᵥ b) - ⅟(2 : AF F) * (a ⬝ᵥ b)) •
        schr ψ (A₁, B₁) (fun x₁ => partR (conjMap T) φ (Sum.elim x₁ (s ∘ Sum.inr + a))) := by
    funext x₁
    have e1 : (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂)) =
        ψ (x₁ ⬝ᵥ B₁ + ⅟(2 : AF F) * (A₁ ⬝ᵥ B₁)) • schr ψ (A₂, -B₂) (fun x₂ => φ (Sum.elim (x₁ + A₁) x₂)) := by
      funext x₂
      simp only [schr, Pi.smul_apply, smul_eq_mul, elim_dot, Sum.elim_add_add]
      rw [← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    rw [e1, map_smul, hconj _ (sliceR hφ _)]
    simp only [Pi.smul_apply, smul_eq_mul, schr, partR_apply, Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [dotProduct_neg, dotProduct_neg]
    rw [show ∀ p q r : ℂ, p * (q * r) = q * (p * r) from fun p q r => by ring]
    congr 2
    ring_nf
  rw [evDbl_apply, hinner, map_smul, h1 _ hslice]
  simp only [schr, Pi.smul_apply, smul_eq_mul, evDbl_apply, elim_dot, partR_apply, Sum.elim_comp_inl,
    Sum.elim_comp_inr, dotProduct_neg]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  have hs : s ⬝ᵥ Sum.elim b (-b) = (s ∘ Sum.inl) ⬝ᵥ b - (s ∘ Sum.inr) ⬝ᵥ b := by
    rw [← Sum.elim_comp_inl_inr s, elim_dot, dotProduct_neg, Sum.elim_comp_inl, Sum.elim_comp_inr, sub_eq_add_neg]
  rw [hs]
  ring

end GlobalTheory.DoublingEvLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLiftV
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal

theorem continuous_liftV {F : Type} [Field F] [NumberField F] (v : Pl F) :
    Continuous (GlobalTheory.LatVac.liftV v) := by
  change Continuous (fun a : Fv F v => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a))
  exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)

theorem continuous_liftE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : Pl F) : Continuous (liftE (E := E) v) := by
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  let bA := Algebra.TensorProduct.basis (Fv F v) b
  have hsum : ∀ z : Fv F v ⊗[F] E,
      liftE v z = ∑ i, GlobalTheory.LatVac.liftV v (bA.repr z i) • ((1 : AF F) ⊗ₜ[F] b i) := by
    intro z
    conv_lhs => rw [← bA.sum_repr z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp only [liftE, TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
  have hfun : (liftE (E := E) v : Fv F v ⊗[F] E → AE F E) =
      fun z => ∑ i, GlobalTheory.LatVac.liftV v (bA.repr z i) • ((1 : AF F) ⊗ₜ[F] b i) := funext hsum
  rw [hfun]
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  refine continuous_finset_sum _ fun i _ => ?_
  have hl : Continuous ((Finsupp.lapply i).comp bA.repr.toLinearMap : Fv F v ⊗[F] E →ₗ[Fv F v] Fv F v) :=
    IsModuleTopology.continuous_of_linearMap _
  exact Continuous.smul ((continuous_liftV v).comp hl)
    (continuous_const : Continuous fun _ : Fv F v ⊗[F] E => ((1 : AF F) ⊗ₜ[F] b i : AE F E))

theorem continuous_liftU (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) :
    Continuous (GlobalTheory.HoweLocal.liftU (F := F) (E := E) v) := by
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  haveI : IsTopologicalAddGroup (Fv F v ⊗[F] E) := IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  rw [Units.continuous_iff]
  constructor
  · change Continuous (fun z : (Fv F v ⊗[F] E)ˣ => 1 + liftE v ((z : Fv F v ⊗[F] E) - 1))
    exact continuous_const.add ((continuous_liftE v).comp (Units.continuous_val.sub continuous_const))
  · change Continuous (fun z : (Fv F v ⊗[F] E)ˣ => 1 + liftE v (((z⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) - 1))
    exact continuous_const.add ((continuous_liftE v).comp (Units.continuous_coe_inv.sub continuous_const))

end GlobalTheory.HoweLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormSqIntegrableAndIsDiscreteSplitCentre
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem cuspForm_isSqInt_and_isDiscrete :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
      (∀ φ : Sm E a, IsCuspForm φ → (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) → IsSqInt φ.1) ∧
        ∀ x : CuspSub E a, IsNormalised x → IsDiscrete x.V := by
  intro E _ _ _ a
  have hB : CuspFormsBoundedGL :=
    GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay
      (GlobalTheory.cuspRapidDecaySiegelGL_of_finite GlobalTheory.automorphicFormsFiniteGL)
  have h1 : ∀ φ : Sm E a, IsCuspForm φ → (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) → IsSqInt φ.1 :=
    fun φ hφ h' =>
      have hC := hB.of_invariant hφ h'
      GlobalTheory.DiscChar.isSqInt_of_bounded h' (C := hC.choose) hC.choose_spec
  exact ⟨h1, fun x hx => ⟨fun φ hφ => (x.cusp φ hφ).1, fun φ hφ => h1 φ (x.cusp φ hφ) (hx φ hφ), x.stable, x.ne_bot,
    x.irred⟩⟩

end GlobalTheory.ResW

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterCentralExponentProperties
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ResW.CexLetter

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem zc_eq_act (a : ℕ) : zc E a = act (Op.lie (fun i j => if i = j then 1 else 0) : Op E a) := rfl

theorem zc_mapsTo {a : ℕ} (π : CuspSub E a) : ∀ φ ∈ π.V, zc E a φ ∈ π.V := fun φ hφ => by
  rw [zc_eq_act]; exact π.stable _ φ hφ

theorem exists_scalar (x : Letter E) : ∃ c : ℂ, ∀ φ ∈ x.2.V, zc E x.1 φ = c • φ := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.cuspidalRep_endomorphism_scalar_schur E x.1 x.2 ((zc E x.1).restrict (zc_mapsTo x.2)) (by
    intro o φ
    apply Subtype.ext
    have := congrArg (fun f : Module.End ℂ (Sm E x.1) => f φ.1) ((GlobalTheory.T.splitCentreDerivative_commute_central_eigen E x.1).1 o)
    simpa [LinearMap.restrict_apply, CuspSub.op] using this)
  exact ⟨c, fun φ hφ => by simpa using congrArg Subtype.val (hc ⟨φ, hφ⟩)⟩

theorem cex_spec (x : Letter E) : ∀ φ ∈ x.2.V, zc E x.1 φ = cex x • φ := by
  unfold cex; exact Classical.epsilon_spec (exists_scalar x)

theorem cex_unique (x : Letter E) (c : ℂ) (h : ∃ φ ∈ x.2.V, φ ≠ 0 ∧ zc E x.1 φ = c • φ) : cex x = c := by
  obtain ⟨φ, hφ, hne, hc⟩ := h
  have h1 := cex_spec x φ hφ
  rw [hc] at h1
  exact (smul_left_injective ℂ hne h1).symm

theorem cex_tw (x : Letter E) (t : ℝ) : cex (tw x t) = cex x + x.1 * (Module.finrank ℚ E : ℂ) * t := by
  obtain ⟨χ, h1, -, -, h4⟩ := GlobalTheory.T.exists_idelic_absValue_cpow_character E (t : ℂ)
  have hχ : χ = nu E t := by have := h4 (Complex.ofReal_im t); rwa [Complex.ofReal_re] at this
  subst hχ
  obtain ⟨φ, hφ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot x.2.ne_bot
  apply cex_unique
  refine ⟨mulChi x.1 (nu E t) φ, ?_, ?_, ?_⟩
  · exact ⟨φ, hφ, rfl⟩
  · exact fun h0 => hne ((mulChi x.1 (nu E t)).injective (h0.trans (map_zero _).symm))
  · show zc E x.1 (mulChi x.1 (nu E t) φ) = _
    rw [h1, cex_spec x φ hφ, ← add_smul, map_smul]
    rfl

theorem rexp_tw (x : Letter E) (hx : 1 ≤ x.1) (t : ℝ) : rexp (tw x t) = rexp x + t := by
  have hd : (0:ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have ha : (0:ℝ) < x.1 := by exact_mod_cast hx
  have hne : (x.1 : ℝ) * Module.finrank ℚ E ≠ 0 := (mul_pos ha hd).ne'
  unfold rexp
  rw [cex_tw]
  show (cex x + (x.1 : ℂ) * (Module.finrank ℚ E : ℂ) * (t : ℂ)).re / ((x.1:ℝ) * Module.finrank ℚ E) = _
  rw [show (x.1 : ℂ) * (Module.finrank ℚ E : ℂ) * (t : ℂ) = (((x.1:ℝ) * Module.finrank ℚ E * t : ℝ) : ℂ) by
    push_cast; ring, Complex.add_re, Complex.ofReal_re]
  field_simp

theorem cex_eq_zero_iff (x : Letter E) : cex x = 0 ↔ IsNormalised x.2 := by
  constructor
  · intro h φ hφ t g
    have := ((GlobalTheory.T.splitCentreDerivative_commute_central_eigen E x.1).2.2 φ 0).1 (by rw [← h]; exact cex_spec x φ hφ) t g
    simpa using this
  · intro hN
    obtain ⟨φ, hφ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot x.2.ne_bot
    exact cex_unique x 0 ⟨φ, hφ, hne, ((GlobalTheory.T.splitCentreDerivative_commute_central_eigen E x.1).2.2 φ 0).2 (fun t g => by simpa using hN φ hφ t g)⟩

end GlobalTheory.ResW.CexLetter

open GlobalTheory.ResW.CexLetter in

theorem GlobalTheory.ResW.letter_centralExponent : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (x : Letter E), (∀ φ ∈ x.2.V, zc E x.1 φ = cex x • φ) ∧ (∀ t : ℝ, cex (tw x t) = cex x + x.1 * (Module.finrank ℚ E : ℂ) * t) ∧ (1 ≤ x.1 → ∀ t : ℝ, rexp (tw x t) = rexp x + t) ∧ (cex x = 0 ↔ IsNormalised x.2) ∧ ∀ c : ℂ, (∃ φ ∈ x.2.V, φ ≠ 0 ∧ zc E x.1 φ = c • φ) → cex x = c := by
  intro E _ _ _ x
  exact ⟨cex_spec x, cex_tw x, rexp_tw x, cex_eq_zero_iff x, fun c h => cex_unique x c h⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxBasisAdaptedCoordinatesStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darboux_basis_adapted_coordinates : ∀ (D : D7) (n : ℕ) (V : HSp D) (J : Matrix (Fin n) (Fin n) D.host.E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E), IsWittBasis D.sp.cm.sig J 1 T → T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = GlobalTheory.StdUnn.Jst D n → ∀ (d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E), ∃ co : Dbx V J₂ d, IsAdapted D.sp.cm.sig co ∧ IsCoord V T ε co := by
  first | exact @GlobalTheory.SWLink.Darb.exists_adapted | exact GlobalTheory.SWLink.Darb.exists_adapted | (intros; apply GlobalTheory.SWLink.Darb.exists_adapted <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumTieHodgeTateKernelStatement
section
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.datum_tie_hodge_tate_kernel : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (ε : PreTilt O p) (h : ℕ) (D : Datum ε h (ℤ_[p] ⊗[ℤ] 𝓞 E)) (φ : P.V ≃ₗ[C] (Fin h → C)), IsPrimitiveRoot (root ε).untilt p → IsTie P D (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom φ → ∀ (σ : ℤ_[p] ⊗[ℤ] 𝓞 E →+* O) (ψ : E →+* C) (r : NNReal), σ.comp (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom = embO P.integers ψ → IsShift C v D σ r → ∀ (a q : ℕ) (x : Fin a → P.V) (y : Fin q → P.V) (g : Matrix (Fin a) (Fin a) C) (g' : Matrix (Fin q) (Fin q) C), Module.finrank C (P.eigW (embO P.integers ψ)) = a → Module.finrank C (P.eigW ((embO P.integers ψ).comp (starRingEnd (𝓞 E)))) = q → Submodule.span O (Set.range x) = P.wRec (embO P.integers ψ) → Submodule.span O (Set.range y) = P.wRec ((embO P.integers ψ).comp (starRingEnd (𝓞 E))) → IsLatBasis C (open Classical in P.latTQuot (σ := fun φ' : E →+* C => embO P.integers φ') (isSplitting_embO P.integers) ψ) (fun i => ∑ j, g i j • x j) → IsLatBasis C (P.latTSub ((embO P.integers ψ).comp (starRingEnd (𝓞 E)))) (fun i => ∑ j, g' i j • y j) → v g.det = r * v g'.det ∧ g'.det ≠ 0 ∧ Module.finrank C (eig C (actT D) σ) = a + q := by
  first | exact @GlobalTheory.DetInv.FinrankMapAddFinrankInf.shift_eq_of_isTie | exact GlobalTheory.DetInv.FinrankMapAddFinrankInf.shift_eq_of_isTie | (intros; apply GlobalTheory.DetInv.FinrankMapAddFinrankInf.shift_eq_of_isTie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomRowTransportContragredientStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definite_bottom_row_transport_contragredient : ∀ (D : D7) (M M' X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (A' : GlobalTheory.ChainFr.Fr M') (B : GlobalTheory.ChainFr.Fr X)
    (eS eS' : D.what₂.Tau → ℚ) (n₀ : D.what₂.Tau → ℕ) (Q : Type) [AddCommGroup Q] [Module ℂ Q]
    (q : PolF D X.rank M.rank →ₗ[ℂ] Q) (q' : PolF D X.rank M'.rank →ₗ[ℂ] Q),
    (∀ τ j, A.ε τ j = true) → (∀ τ j, A'.ε τ j = true) → (∀ τ i, B.ε τ i = true) →
    (∀ τ, (n₀ τ : ℚ) = eS τ - eS' τ - ((M.rank : ℚ) + (M'.rank : ℚ)) / 2) →
    (∀ P P', q P = q' P' → ∀ τ, ∀ Y ∈ lieAt X τ,
      q (GlobalTheory.RealQuot.actT true A B eS τ Y P) = q' (GlobalTheory.RealQuot.actT false A' B eS' τ Y P')) →
    ∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin X.rank) ℂ) (P : PolF D X.rank M.rank) (P' : PolF D X.rank M'.rank), q P = q' P' →
      q' (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin X.rank) (Fin X.rank) ℂ)) P') =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (κ τ : Matrix (Fin X.rank) (Fin X.rank) ℂ)) •
          q (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin X.rank) (Fin X.rank) ℂ).map (starRingEnd ℂ)) P) := by
  first | exact @GlobalTheory.RowTransport.row_transport | exact GlobalTheory.RowTransport.row_transport | (intros; apply GlobalTheory.RowTransport.row_transport <;> assumption)
end

