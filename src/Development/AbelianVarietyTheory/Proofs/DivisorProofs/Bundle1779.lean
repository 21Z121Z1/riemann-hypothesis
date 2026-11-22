import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedEigenLatticeLeSpanIntegralFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1741
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1754
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0810
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0808
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0778
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformArchimedeanCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1716
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1755
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplTupBijective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotMatch

def complSub {a a' d : ℕ} (h : a + a' = d) (s : {s : Fin a → Fin d // StrictMono s}) : {s : Fin a' → Fin d // StrictMono s} :=
  ⟨Finset.orderEmbOfFin (Finset.univ.image s.1)ᶜ (by
      rw [Finset.card_compl, Finset.card_image_of_injective _ s.2.injective, Finset.card_univ, Fintype.card_fin,
        Fintype.card_fin]; omega), (Finset.orderEmbOfFin _ _).strictMono⟩

theorem range_complSub {a a' d : ℕ} (h : a + a' = d) (s : {s : Fin a → Fin d // StrictMono s}) :
    Set.range (complSub h s).1 = (Set.range s.1)ᶜ := by
  simp only [complSub, Finset.range_orderEmbOfFin, Finset.coe_compl, Finset.coe_image, Finset.coe_univ, Set.image_univ]

theorem complSub_complSub {a a' d : ℕ} (h : a + a' = d) (h' : a' + a = d) (s : {s : Fin a → Fin d // StrictMono s}) :
    complSub h' (complSub h s) = s := by
  apply Subtype.ext
  apply (StrictMono.range_inj (complSub h' (complSub h s)).2 s.2).1
  rw [range_complSub, range_complSub, compl_compl]

def complTup (D : D7) {a a' d : ℕ} {n : D.what₂.Tau → ℕ} (h : a + a' = d) (T : Tup D a d n) : Tup D a' d n :=
  fun τ k => complSub h (T τ k)

theorem complTup_bijective (D : D7) {a a' d : ℕ} {n : D.what₂.Tau → ℕ} (h : a + a' = d) :
    Function.Bijective (complTup D (n := n) h) := by
  refine Function.bijective_iff_has_inverse.2 ⟨complTup D (a := a') (a' := a) (by omega), fun T => ?_, fun T => ?_⟩ <;>
    funext τ k <;> simp only [complTup, complSub_complSub]

theorem exists_signed_perm {α β : Type} [Fintype α] [Fintype β] (c : α → β) (hc : Function.Bijective c) (ε : α → ℤˣ) :
    ∃ (M : α → β → ℤ) (M' : β → α → ℤ), (∀ T₁ T₂, ∑ T, M' T₁ T * M T T₂ = if T₁ = T₂ then 1 else 0) ∧
      ∀ T (f : β → ℂ), ∑ T', (M T T' : ℂ) * f T' = ((ε T : ℤ) : ℂ) * f (c T) := by
  classical
  refine ⟨fun T T' => if T' = c T then (ε T : ℤ) else 0, fun T' T => if T' = c T then (ε T : ℤ) else 0, fun T₁ T₂ => ?_,
    fun T f => ?_⟩
  · obtain ⟨T, rfl⟩ := hc.2 T₁
    rw [Finset.sum_eq_single T]
    · by_cases h : c T = T₂
      · subst h; simp [← Units.val_mul]
      · simp [h, Ne.symm h]
    · intro b _ hb
      have : c T ≠ c b := fun e => hb (hc.1 e).symm
      simp [this]
    · simp
  · rw [Finset.sum_eq_single (c T)]
    · simp
    · intro b _ hb; simp [hb]
    · simp

end GlobalTheory.BotMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedEigenLatticeLeSpanIntegralFrameStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completed_eigenLattice_le_span_integral_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u → ∀ v ∈ F.eigLat B.t.act tt, (fun k => iK (v k)) ∈ Submodule.span T.V (Set.range fun i => ∑ j, C ρ i j • fun k => iK (u j k)) := by
  first | exact @GlobalTheory.EigLatSpan.eigLat_le_span | exact GlobalTheory.EigLatSpan.eigLat_le_span | (intros; apply GlobalTheory.EigLatSpan.eigLat_le_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedSpanEigenVectorMemEigenSublatticeStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completed_span_eigen_vector_mem_eigen_sublattice : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (Λ : Submodule (𝓞 K) (Fin n → K)) (O : Type) (r : O → Matrix (Fin n) (Fin n) K) (τ : O → K) (𝔓 : HeightOneSpectrum (𝓞 K)) (T : Formalism.L2.Pj.CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → Λ.FG → ∀ x : Fin n → T.Fr, x ∈ Submodule.span T.V ((fun (c : Fin n → K) i => iK (c i)) '' (Λ : Set (Fin n → K))) → (∀ a, ((r a).map iK).mulVec x = iK (τ a) • x) → x ∈ Submodule.span T.V ((fun (c : Fin n → K) i => iK (c i)) '' {c | c ∈ Λ ∧ ∀ a, (r a).mulVec c = τ a • c}) := by
  first | exact @GlobalTheory.EigenSpanSat.span_eigen_sat | exact GlobalTheory.EigenSpanSat.span_eigen_sat | (intros; apply GlobalTheory.EigenSpanSat.span_eigen_sat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulConjSmul
section
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.SkewLatSelfDual

open GlobalTheory.FunObj.SqNum

variable {D : D7}

abbrev FI (D : D7) : Type := FractionalIdeal (𝓞 D.host.E)⁰ D.host.E

theorem star_eq_conj (x : D.host.E) : (letI := D.host.cmStar; star x) = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem conj_smul_conj_smul (𝔞 : Ideal (𝓞 D.host.E)) : D.host.conj • (D.host.conj • 𝔞) = 𝔞 := by
  rw [smul_smul]
  have : D.host.conj * D.host.conj = 1 := AlgEquiv.ext (VacMove.conj_conj D)
  rw [this, one_smul]

theorem conj_smul_ne_bot {𝔞 : Ideal (𝓞 D.host.E)} (h : 𝔞 ≠ ⊥) : D.host.conj • 𝔞 ≠ ⊥ := by
  intro h'
  apply h
  rw [← conj_smul_conj_smul 𝔞, h']
  ext x
  simp [Ideal.mem_pointwise_smul_iff_inv_smul_mem]

theorem coe_ne_zero {𝔞 : Ideal (𝓞 D.host.E)} (h : 𝔞 ≠ ⊥) : ((𝔞 : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 := by
  rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]

theorem conj_mem_div {A B : Ideal (𝓞 D.host.E)} (hB : B ≠ ⊥) {x : D.host.E}
    (hx : x ∈ ((A : FI D) / (B : FI D))) :
    D.host.conj x ∈ (((D.host.conj • A : Ideal (𝓞 D.host.E)) : FI D) / ((D.host.conj • B : Ideal (𝓞 D.host.E)) : FI D)) := by
  rw [FractionalIdeal.mem_div_iff_of_ne_zero (coe_ne_zero hB)] at hx
  rw [FractionalIdeal.mem_div_iff_of_ne_zero (coe_ne_zero (conj_smul_ne_bot hB))]
  intro y hy
  obtain ⟨β, hβ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
  have hβ' : D.host.conj • β ∈ B := by
    have := Ideal.smul_mem_pointwise_smul D.host.conj β _ hβ
    rwa [conj_smul_conj_smul] at this
  obtain ⟨α, hα, hαe⟩ := (FractionalIdeal.mem_coeIdeal _).1 (hx _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hβ', rfl⟩))
  refine (FractionalIdeal.mem_coeIdeal _).2 ⟨D.host.conj • α, Ideal.smul_mem_pointwise_smul _ _ _ hα, ?_⟩
  have e1 : algebraMap (𝓞 D.host.E) D.host.E (D.host.conj • α) = D.host.conj (algebraMap (𝓞 D.host.E) D.host.E α) := rfl
  have e2 : algebraMap (𝓞 D.host.E) D.host.E (D.host.conj • β) = D.host.conj (algebraMap (𝓞 D.host.E) D.host.E β) := rfl
  rw [e1, hαe, e2, map_mul, VacMove.conj_conj]

theorem mem_skewLat {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} (v : Fin N → D.host.E) :
    v ∈ skewLat D 𝔪 N ↔ ∀ i, v i ∈ ((𝔪 : FI D) / ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FI D)) := by
  simp [skewLat, Submodule.mem_pi]

theorem skewLat_SD {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) (N : ℕ) : SD D (skewLat D 𝔪 N) := by
  set 𝔫 : Ideal (𝓞 D.host.E) := D.host.conj • 𝔪 with h𝔫
  have h𝔫0 : 𝔫 ≠ ⊥ := conj_smul_ne_bot h𝔪
  have h𝔪𝔫 : D.host.conj • 𝔫 = 𝔪 := conj_smul_conj_smul 𝔪
  set I : FI D := (𝔪 : FI D) / (𝔫 : FI D) with hIdef
  set J : FI D := (𝔫 : FI D) / (𝔪 : FI D) with hJdef
  have hI0 : I ≠ 0 := div_ne_zero (coe_ne_zero h𝔪) (coe_ne_zero h𝔫0)
  have hJ0 : J ≠ 0 := div_ne_zero (coe_ne_zero h𝔫0) (coe_ne_zero h𝔪)
  have hJI : J * I = 1 := by
    rw [hIdef, hJdef, div_mul_div_comm, mul_comm (𝔫 : FI D), div_self]
    exact mul_ne_zero (coe_ne_zero h𝔪) (coe_ne_zero h𝔫0)
  have hIJ' : 1 / J = I := by rw [hJdef, hIdef, one_div_div]
  have cI : ∀ x ∈ I, D.host.conj x ∈ J := fun x hx => by
    have := conj_mem_div h𝔫0 hx
    rwa [h𝔪𝔫] at this
  have cJ : ∀ z ∈ J, D.host.conj z ∈ I := fun z hz => by
    have := conj_mem_div h𝔪 hz
    rwa [h𝔪𝔫] at this
  have memL : ∀ v : Fin N → D.host.E, v ∈ skewLat D 𝔪 N ↔ ∀ i, v i ∈ I := mem_skewLat
  letI := D.host.cmStar
  show IsSDLat D.host.E N (skewLat D 𝔪 N)
  refine ⟨Submodule.fg_pi fun _ => FractionalIdeal.fg_of_isNoetherianRing le_rfl _, ?_, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := (I : Submodule (𝓞 D.host.E) D.host.E))
      (fun h => hI0 (FractionalIdeal.coeToSubmodule_injective (h.trans FractionalIdeal.coe_zero.symm)))
    have hs : ∀ i : Fin N, (Pi.single i a : Fin N → D.host.E) ∈ skewLat D 𝔪 N := fun i => by
      rw [memL]
      intro j
      by_cases hj : j = i
      · subst hj; simpa using ha
      · rw [Pi.single_eq_of_ne hj]; exact Submodule.zero_mem (I : Submodule (𝓞 D.host.E) D.host.E)
    rw [Submodule.eq_top_iff']
    intro x
    have : x = ∑ i, (x i * a⁻¹) • (Pi.single i a : Fin N → D.host.E) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, ha0]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs i))
  · rw [memL] at hx hy
    unfold Formalism.BasicNotions.stdH
    refine Subring.sum_mem _ fun i _ => ?_
    have hm : star (x i) * y i ∈ J * I := by
      rw [star_eq_conj]
      exact FractionalIdeal.mul_mem_mul (cI _ (hx i)) (hy i)
    rw [hJI] at hm
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 hm
    exact ⟨a, ha⟩
  · rw [memL]
    intro i
    rw [← hIJ', FractionalIdeal.mem_div_iff_of_ne_zero hJ0]
    intro z hz
    have hx : (Pi.single i (D.host.conj z) : Fin N → D.host.E) ∈ skewLat D 𝔪 N := by
      rw [memL]
      intro j
      by_cases hj : j = i
      · subst hj; simpa using cJ z hz
      · rw [Pi.single_eq_of_ne hj]; exact Submodule.zero_mem (I : Submodule (𝓞 D.host.E) D.host.E)
    have h1 := h _ hx
    unfold Formalism.BasicNotions.stdH at h1
    have e : (∑ j, star ((Pi.single i (D.host.conj z) : Fin N → D.host.E) j) * y j) = y i * z := by
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, star_eq_conj, VacMove.conj_conj, mul_comm]
      · intro j _ hj; simp [Pi.single_eq_of_ne hj]
      · simp
    rw [e] at h1
    obtain ⟨a, ha⟩ := h1
    exact (FractionalIdeal.mem_one_iff _).2 ⟨a, ha⟩

end GlobalTheory.SkewLatSelfDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermFiniteDimensionalSpanParabolic
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.SliceTwoCentre

theorem sliceTwoCentre : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → ∀ (hr : r < a), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), ∃ (X' : Set (Module.End ℂ (Sm E (a - r)) → ℂ)) (D : ℕ), X'.Finite ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ m₁ : GA E r, ∀ ψ : Sm E (a - r), ψ.1 = (fun m₂ : GA E (a - r) => ∫ x in 𝓕, φ.1 (unip x * (GlobalTheory.LeviGA.blkGL hr.le (m₁, m₂) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ) → FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E (a - r)) => z ψ) '' Zalg E (a - r))) ∧ Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E (a - r)) => z ψ) '' Zalg E (a - r))) ≤ D ∧ ∀ (χ' : Module.End ℂ (Sm E (a - r)) → ℂ) (u : Sm E (a - r)), u ∈ Submodule.span ℂ ((fun z : Module.End ℂ (Sm E (a - r)) => z ψ) '' Zalg E (a - r)) → u ≠ 0 → (∀ z ∈ Zalg E (a - r), z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ Zalg E (a - r), χ' z = χ z := by
  intro E _ _ _ a L hL W hW X hX N r hr0 hr _ _ μ 𝓕 hμ h𝓕 h1 t κ
  classical
  have hra : r ≤ a := hr.le
  let Q : (E →+* ℂ) → ℂ → Polynomial ℂ := fun τ u =>
    ∏ χ ∈ hX.toFinset, (Polynomial.X - Polynomial.C (χ (cap τ (u - ((a : ℂ) - 1) / 2)))) ^ N
  have hQ : ∀ τ u, Q τ u ≠ 0 := fun τ u =>
    Finset.prod_ne_zero_iff.2 fun χ _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  let M' : Submodule ℂ (Sm E a) :=
    { carrier := {f | ∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g}
      add_mem' := fun {f f'} hf hf' x g => by
        simp only [Set.mem_setOf_eq] at hf hf'
        simp [hf x g, hf' x g]
      zero_mem' := fun x g => rfl
      smul_mem' := fun c f hf x g => by
        simp only [Set.mem_setOf_eq] at hf
        simp [hf x g] }
  let K : Submodule ℂ (Sm E a) :=
    { carrier := {f | ∀ (m₁ : GA E r) (m₂ : GA E (a - r)), f.1 (GlobalTheory.LeviGA.blkGL hra (m₁, m₂)) = 0}
      add_mem' := fun {f f'} hf hf' m₁ m₂ => by
        simp only [Set.mem_setOf_eq] at hf hf'
        simp [hf m₁ m₂, hf' m₁ m₂]
      zero_mem' := fun m₁ m₂ => rfl
      smul_mem' := fun c f hf m₁ m₂ => by
        simp only [Set.mem_setOf_eq] at hf
        simp [hf m₁ m₂] }
  have hq : ∀ τ : E →+* ℂ, ∃ q : ℂ → Polynomial ℂ, (∀ u, q u ≠ 0) ∧ ∀ v ∈ M',
      (∀ u, Polynomial.aeval (Formalism.REAL.qdet (Eop τ) u) (Q τ u) v = 0) → ∀ u,
        Polynomial.aeval (Formalism.REAL.qdet (fun p p' : Fin (a - r) => Eop τ (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p))
          (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p'))) u) (q u) v ∈ K := by
    intro τ
    obtain ⟨q, hq0, hqK⟩ := GlobalTheory.T.harishChandra_capelli_uniform_diagonalBlocks (Sm E a) a r hra (Eop τ) (glRel_Eop τ) M' K
      (fun i j f hf => GlobalTheory.T.eop_preserves_left_unipotent_invariance E a r f hf τ i j)
      (fun i j hi hj f hf => GlobalTheory.T.matrixUnitOp_upperBlock_levi_eq_zero E a r hra f hf τ i j hi hj)
      (fun i j hij f hf => GlobalTheory.T.levi_restriction_vanishing_preserved_by_operator E a r hra f hf τ i j hij) (Q τ) (hQ τ)
    exact ⟨q, hq0, fun v hv hk u => (hqK v hv hk u).2⟩
  choose q hq0 hqK using hq
  obtain ⟨X', D, hX', hfin⟩ := GlobalTheory.T.capelliKilled_smoothFunction_centreOrbit_finiteDimensional E (a - r) (fun τ u => q τ (u + (((a - r : ℕ) : ℂ) - 1) / 2))
    (fun τ u => hq0 τ _)
  refine ⟨X', D, hX', fun φ hφ m₁ ψ hψ => hfin ψ fun τ u => ?_⟩
  obtain ⟨hl, ho, hk⟩ := GlobalTheory.T.rightTranslate_harishChandraFiniteForm_properties E a L W X hX.toFinset (by simp) N φ hφ t κ
  obtain ⟨hcSm, -⟩ := GlobalTheory.ConstTermSmooth.constTerm_mem_Sm E a r μ 𝓕 hμ h𝓕 h1 _ hl ho
  let c : Sm E a := ⟨_, hcSm⟩
  have hcM : c ∈ M' := fun x g => constTerm_unip_invariant E a r μ 𝓕 hμ h𝓕 _ hl x g
  have hcQ : ∀ u, Polynomial.aeval (Formalism.REAL.qdet (Eop τ) u) (Q τ u) c = 0 := by
    intro u
    have e : Formalism.REAL.qdet (Eop (a := a) τ) u = cap (a := a) τ (u - ((a : ℂ) - 1) / 2) := by
      rw [cap, sub_add_cancel]
    rw [e]
    have hz : Polynomial.aeval (cap (a := a) τ (u - ((a : ℂ) - 1) / 2)) (Q τ u) ∈ Zalg E a := by
      rw [← Polynomial.aeval_subalgebra_coe (Q τ u) (Zalg E a)
        ⟨cap (a := a) τ (u - ((a : ℂ) - 1) / 2), Algebra.subset_adjoin ⟨τ, _, rfl⟩⟩]
      exact SetLike.coe_mem _
    have h2 := GlobalTheory.T.constant_term_center_action_smooth_form E a r μ 𝓕 hμ h𝓕 h1 _ hl ho _ hz c rfl
    refine Subtype.ext (h2.trans (funext fun g => ?_))
    rw [hk τ (u - ((a : ℂ) - 1) / 2)]
    simp
  have hK := hqK τ c hcM hcQ (u + (((a - r : ℕ) : ℂ) - 1) / 2)
  let T : Sm E a →ₗ[ℂ] Sm E (a - r) :=
    { toFun := fun f => ⟨_, (GlobalTheory.T.leviSlice_smooth_and_matrixUnit_action E a r hra m₁ f).1⟩
      map_add' := fun f f' => rfl
      map_smul' := fun c f => rfl }
  have hT : ∀ (p p' : Fin (a - r)) (f : Sm E a),
      T (Eop τ (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p')) f) = Eop τ p p' (T f) :=
    fun p p' f => Subtype.ext ((GlobalTheory.T.leviSlice_smooth_and_matrixUnit_action E a r hra m₁ f).2 τ p p' (T f) rfl).symm
  have hψc : T c = ψ := by
    refine Subtype.ext (hψ.symm ▸ funext fun m₂ => ?_)
    simp only [T, c, LinearMap.coe_mk, AddHom.coe_mk, rt_apply, mul_assoc]
  have h3 := GlobalTheory.T.aeval_quantumDeterminant_intertwining (Sm E a) (Sm E (a - r)) T (a - r)
    (fun p p' => Eop τ (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p'))) (Eop τ)
    hT (u + (((a - r : ℕ) : ℂ) - 1) / 2) (q τ (u + (((a - r : ℕ) : ℂ) - 1) / 2)) c
  have h0 : T (Polynomial.aeval (Formalism.REAL.qdet (fun p p' : Fin (a - r) => Eop τ (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p))
      (GlobalTheory.LeviGA.blkEquiv hra (Sum.inr p'))) (u + (((a - r : ℕ) : ℂ) - 1) / 2))
      (q τ (u + (((a - r : ℕ) : ℂ) - 1) / 2)) c) = 0 :=
    Subtype.ext (funext fun m₂ => hK m₁ m₂)
  show Polynomial.aeval (cap τ u) (q τ (u + (((a - r : ℕ) : ℂ) - 1) / 2)) ψ = 0
  rw [cap, ← hψc, ← h3, h0]

end GlobalTheory.SliceTwoCentre

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformArchimedeanCmStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_thetaTransform_archimedean_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WOF F E nS nT), Continuous L →
            (∀ t, (L t).map (finPartF F E) = 0) → ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ (w + L t) := by
  first | exact @GlobalTheory.ThetaSmoothF.contDiff_thetaTr_realF | exact GlobalTheory.ThetaSmoothF.contDiff_thetaTr_realF | (intros; apply GlobalTheory.ThetaSmoothF.contDiff_thetaTr_realF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformRationalDarbouxCm
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ThetaTrContCM

theorem continuous_thetaTr_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          Continuous (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hs hψ JA JB ξ hA hBm κ _ co hco φ hφ
  exact GlobalTheory.ThetaTrContF.continuous_thetaTrF F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hs JA JB ξ hA hBm κ co hco φ hφ

end GlobalTheory.ThetaTrContCM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformSchwartzCmStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_thetaTransform_schwartz_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, Continuous (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  first | exact @GlobalTheory.ThetaTrContF.continuous_thetaTrF | exact GlobalTheory.ThetaTrContF.continuous_thetaTrF | (intros; apply GlobalTheory.ThetaTrContF.continuous_thetaTrF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTranslatesKernelRouteSmallVertexStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_translates_kernel_route_small_vertex : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j))
    (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))) (z : GA D (G.V (.grid i j)) →₀ ℂ),
    Continuous (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) =>
      translates z (kerSmall W Θ' p.1 g₁) p.2) := by
  first | exact @GlobalTheory.SmallRoute.continuous_translates_kerSmall | exact GlobalTheory.SmallRoute.continuous_translates_kerSmall | (intros; apply GlobalTheory.SmallRoute.continuous_translates_kerSmall <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorConjIsThetaSomeLevelStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetVector_conj_isTheta_some_level : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0 ∈ TT D (tor0 D ⊤ δ) a d := by
  first | exact @GlobalTheory.BotPairSmall.cvec_conj_mem_TT | exact GlobalTheory.BotPairSmall.cvec_conj_mem_TT | (intros; apply GlobalTheory.BotPairSmall.cvec_conj_mem_TT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormAdelicFunctionsEqModelValuesSemilinear
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspFormValues

theorem evEx_of_range {K C H X : Type} [Field K] [AddCommGroup C] [Module K C] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup X] [Module ℂ X] (σ : K →+* ℂ) (ev : H → X) (φ : C → X) (hinj : Function.Injective ev)
    (hadd : ∀ x y, ev (x + y) = ev x + ev y) (hsmul : ∀ (a : ℂ) x, ev (a • x) = a • ev x)
    (hφa : ∀ f g, φ (f + g) = φ f + φ g) (hφs : ∀ (a : K) f, φ (a • f) = σ a • φ f)
    (hmem : ∀ f, φ f ∈ Set.range ev) : EvEx σ ev φ := by
  choose j hj using hmem
  exact ⟨{ toFun := j
           map_add' := fun f g => hinj (by rw [hadd, hj, hj, hj, hφa])
           map_smul' := fun a f => hinj (by rw [hsmul, hj, hj, hφs]) }, hj⟩

theorem phiC_eq {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    phiC T hV a f = adel W (castDict hV (T.dict j σ)) (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.cE j σ))
      ((lieFac (T.Q.Dw j) (xiR D) a : ℂ) • rdU (T.U j σ) f) := by
  subst hV
  rw [map_smul]
  rfl

theorem jEvExists : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → JEvExists T R κ v₀ := by
  intro hdec hvol D G _ _ Pl0 T0 A T _ R κ v₀ hlev hmod htie hpb i σ hσ hV
  have hr := GlobalTheory.T.hilbertModel_extremalValues_eq_holomorphicCuspForms hdec hvol D G Pl0 T0 A T R κ v₀ hlev hmod htie hpb i σ hσ hV
  refine evEx_of_range _ _ _ (GlobalTheory.EvalAtUnitVector.evInj T R v₀ hmod.HW htie.hv₀ i σ hσ) (fun x y => ?_) (fun a x => ?_)
    (fun f g => ?_) (fun a f => ?_) (fun f => ?_)
  · unfold evAt
    rw [map_add]
    rfl
  · unfold evAt
    rw [map_smul]
    rfl
  · simp only [phiC_eq]
    rw [Submodule.coe_add, map_add, smul_add, map_add]
  · simp only [phiC_eq]
    rw [Submodule.coe_smul, map_smulₛₗ (rdU _), smul_comm, map_smul]
  · rw [hr, phiC_eq]
    exact ⟨_, Submodule.smul_mem _ _
      (Submodule.mem_inf.2 ⟨((mem_cusp _ _ _ _ _ _).1 f.2).2 _ hσ, rdU_mem_offZero _ _⟩), rfl⟩

end GlobalTheory.CuspFormValues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRapidDecaySiegelConeRealPointsStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_rapidDecay_siegelCone_realPoints : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ψ : Sm E a), IsCuspForm ψ → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∀ t : ℝ, 0 < t → ∀ lam : Fin a → ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∏ i, r i = 1 → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * ∏ i, r i ^ lam i := by
  first | exact @GlobalTheory.cuspForm_rapidDecay_siegel | exact GlobalTheory.cuspForm_rapidDecay_siegel | (intros; apply GlobalTheory.cuspForm_rapidDecay_siegel <;> assumption)
end

