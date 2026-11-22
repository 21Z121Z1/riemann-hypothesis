import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0346
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0133
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0264
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0140
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0209
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0125
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0271
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0004
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.RealPlaceAnalysis.Bundle0004
import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0203
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0214
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0325
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KHighestEqSmulOfMinusKilled
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ChainBound
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0353
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0144
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0243
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0351
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0354
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TopMinorAndGramNumberLeMajorantLengths
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalLevelCharacterMatchAtTypePrime
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.Match

theorem diag_lift : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (d : Fin n → (kv F v)ˣ), ∃ D : GL (Fin n) (v.adicCompletion F), (∀ x : Fin n → v.adicCompletion F, (∀ b, x b ∈ v.adicCompletionIntegers F) ↔ ∀ b, ((D : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ x) b ∈ v.adicCompletionIntegers F) ∧ ∀ M : Matrix (Fin n) (Fin n) (v.adicCompletion F), redM F v (((D⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * M * (D : Matrix (Fin n) (Fin n) (v.adicCompletion F))) = diagonal (fun i => ((d i)⁻¹ : (kv F v)ˣ).1) * redM F v M * diagonal (fun i => ((d i : (kv F v)ˣ) : kv F v)) := by
  intro F _ _ v n d
  have hs := IsLocalRing.residue_surjective (R := v.adicCompletionIntegers F)
  choose u hu using fun i => hs ((d i : (kv F v)ˣ) : kv F v)
  have hunit : ∀ i, IsUnit (u i) := fun i =>
    isUnit_of_map_unit (IsLocalRing.residue (v.adicCompletionIntegers F)) (u i) (by rw [hu i]; exact (d i).isUnit)
  let w : Fin n → (v.adicCompletionIntegers F)ˣ := fun i => (hunit i).unit
  let e : Fin n → (v.adicCompletion F)ˣ := fun i => Units.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)).toMonoidHom (w i)
  have he : ∀ i, ((e i : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := fun i => (w i : v.adicCompletionIntegers F).2
  have he' : ∀ i, (((e i)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := fun i => (((w i)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).2
  have hw : ∀ i, IsLocalRing.residue (v.adicCompletionIntegers F) ((w i : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) = ((d i : (kv F v)ˣ) : kv F v) := fun i => hu i
  have hw' : ∀ i, IsLocalRing.residue (v.adicCompletionIntegers F) (((w i)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) = (((d i)⁻¹ : (kv F v)ˣ) : kv F v) := by
    intro i
    have h1 := congrArg Units.val (map_inv (Units.map (IsLocalRing.residue (v.adicCompletionIntegers F)).toMonoidHom) (w i))
    have h2 : Units.map (IsLocalRing.residue (v.adicCompletionIntegers F)).toMonoidHom (w i) = d i := Units.ext (hw i)
    rw [h2] at h1
    exact h1
  let D : GL (Fin n) (v.adicCompletion F) :=
    ⟨diagonal (fun i => ((e i : (v.adicCompletion F)ˣ) : v.adicCompletion F)),
      diagonal (fun i => (((e i)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)),
      by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩
  refine ⟨D, fun x => ?_, fun M => ?_⟩
  · change _ ↔ ∀ b, (diagonal (fun i => ((e i : (v.adicCompletion F)ˣ) : v.adicCompletion F)) *ᵥ x) b ∈ _
    simp only [mulVec_diagonal]
    refine ⟨fun h b => mul_mem (he b) (h b), fun h b => ?_⟩
    have := mul_mem (he' b) (h b)
    rwa [← mul_assoc, Units.inv_mul, one_mul] at this
  · change redM F v (diagonal (fun i => (((e i)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) * M *
      diagonal (fun i => ((e i : (v.adicCompletion F)ˣ) : v.adicCompletion F))) = _
    ext a b
    have key : (diagonal (fun i => (((e i)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) * M *
        diagonal (fun i => ((e i : (v.adicCompletion F)ˣ) : v.adicCompletion F))) a b =
        ((((e a)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * M a b) * ((e b : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
      simp only [diagonal_mul, mul_diagonal]
    simp only [diagonal_mul, mul_diagonal, redM]
    by_cases hM : M a b ∈ v.adicCompletionIntegers F
    · have hP : ((((e a)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * M a b) * ((e b : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F :=
        mul_mem (mul_mem (he' a) hM) (he b)
      rw [dif_pos (key ▸ hP), dif_pos hM, ← hw' a, ← hw b, ← map_mul, ← map_mul]
      congr 1
    · have hP : ((((e a)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * M a b) * ((e b : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∉ v.adicCompletionIntegers F := by
        intro hP
        apply hM
        have := mul_mem (mul_mem (he a) hP) (he' b)
        have e1 : ((e a : (v.adicCompletion F)ˣ) : v.adicCompletion F) * ((((e a)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * M a b * ((e b : (v.adicCompletion F)ˣ) : v.adicCompletion F)) * (((e b)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = M a b := by
          simp [mul_assoc]
        rwa [e1] at this
      rw [dif_neg (key ▸ hP), dif_neg hM]; simp

end GlobalTheory.St.G.Match

namespace GlobalTheory.St.G.Match

theorem nat_prime_not_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (hpv : (p : 𝓞 F) ∈ v.asIdeal) : (q : 𝓞 F) ∉ v.asIdeal := by
  intro hqv
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : (a : 𝓞 F) * (p : 𝓞 F) + (b : 𝓞 F) * (q : 𝓞 F) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 F) hab
    push_cast at this; exact this
  rw [← h1]
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hpv) (v.asIdeal.mul_mem_left _ hqv)

end GlobalTheory.St.G.Match

namespace GlobalTheory.St.G

theorem gmatch_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f t k a sk fc : ℕ) (gp : Fin 2 → ℕ) (S : StepLevel F E cm.sig J T f {v : HeightOneSpectrum (𝓞 F) | (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal}) (G : GLoc F E cm.sig gp) (Gl : GLev S G a t 0 sk fc false), k = n → a = n → sk = n → fc = n → T.Prime → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, T ≠ gp i) → (∀ i, SplitsIn E (gp i)) → ∀ (Fr : AdFrame cm.sig J (hat F S.Lb) (gp 0 * gp 1) k) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (hv : (gp i : 𝓞 F) ∈ v.asIdeal), ∃ κ ∈ levelVL cm.sig J v S.Lb, ∀ y ∈ levelVL cm.sig J v S.Lb, (Fr.LocK S.Lb v y ↔ κ⁻¹ * y * κ ∈ S.Uloc v) ∧ (Fr.LocK S.Lb v y → Fr.locChi v y = (lamJ (G.psi0 i v hv) (G.chiB i v hv) a t 0 sk (redM F v (G.mat i v hv (Gl.fr i v hv) (κ⁻¹ * y * κ))))⁻¹) := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f t k a sk fc gp S G Gl hk ha hsk hfc hT hgp hne hTg hspl Fr i v hv
  subst a sk fc
  have hTv : (T : 𝓞 F) ∉ v.asIdeal := fun h =>
    GlobalTheory.St.G.Match.nat_prime_not_mem v (gp i) T (hgp i) hT (fun e => hTg i e.symm) hv h
  have hTL := GlobalTheory.St.G.stepLevel_tLat F E n cm.sig J T f _ S
  have hSD := GlobalTheory.T.isLocallySelfDual_of_hermitianLatticeOfLevel F E cm n J hJ hdet T f S.Lb hTL v hTv
  have hLat : IsLat S.Lb := ⟨S.Lb_fin, S.Lb_span⟩
  obtain ⟨fr', ψ', hψ', hfr', hK⟩ := GlobalTheory.T.adelicLatticeFrame_local_basis_unitriangular F E cm n J hJ hdet k t gp G S.Lb Fr hk hgp hne hspl hLat i v hv hSD
  have hcard := ((GlobalTheory.T.cmField_splitCompletely_place_structure F E cm (gp i) (hgp i) (hspl i)).2 v hv).1
  haveI : Finite (kv F v) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (hgp i).ne_zero)
  obtain ⟨d, hd⟩ := GlobalTheory.T.diagonal_torus_transitive_generic_characters (kv F v) n t (G.psi0 i v hv) ψ' (G.chiB i v hv) (fun _ => 1) (G.psi_zero_nontrivial_character i v hv) hψ'
  obtain ⟨D, hDint, hDred⟩ := GlobalTheory.St.G.Match.diag_lift F v n d
  obtain ⟨κ, hκ, -⟩ := (GlobalTheory.T.split_place_lattice_components F E cm n J hJ hdet v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv)).2.1
    (fr' * D * (Gl.fr i v hv)⁻¹)
  have hphi : bc (G.phi i v hv) κ.1 = fr' * D * (Gl.fr i v hv)⁻¹ := hκ
  have hlev : κ.1 ∈ levelVL cm.sig J v S.Lb := by
    refine GlobalTheory.T.mem_level_of_preserves_first_components_split F E cm n J v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv) S.Lb hSD κ.1 κ.2 ?_
    intro x
    refine (Gl.fr_lat i v hv x).trans ?_
    refine Iff.trans ?_ (hfr' _).symm
    rw [hDint]
    rw [hκ]
    simp only [Units.val_mul, mulVec_mulVec, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  refine ⟨κ.1, hlev, fun y hy => ?_⟩
  have hyκ : κ.1⁻¹ * y * κ.1 ∈ levelVL cm.sig J v S.Lb := mul_mem (mul_mem (inv_mem hlev) hy) hlev
  have hg : (Gl.fr i v hv)⁻¹ * bc (G.phi i v hv) (κ.1⁻¹ * y * κ.1) * Gl.fr i v hv
      = D⁻¹ * (fr'⁻¹ * bc (G.phi i v hv) y * fr') * D := by
    rw [map_mul, map_mul, map_inv, hphi]; group
  have hred : redM F v (G.mat i v hv (Gl.fr i v hv) (κ.1⁻¹ * y * κ.1)) =
      diagonal (fun j => ((d j)⁻¹ : (kv F v)ˣ).1) * redM F v (G.mat i v hv fr' y) * diagonal (fun j => ((d j : (kv F v)ˣ) : kv F v)) := by
    rw [← hDred]
    unfold GLoc.mat
    rw [hg, Units.val_mul, Units.val_mul]
  obtain ⟨hK1, hK2⟩ := hK y hy
  refine ⟨?_, fun hy' => ?_⟩
  · rw [hK1, (hd _).1, ← hred, Gl.mem i v hv _ hyκ]
  · rw [hK2 hy', (hd _).2, hred]

end GlobalTheory.St.G
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneLargeGaps
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.MultGap

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem proj_comm (hU : IsURepOn (Kset ε) σ) {W : Submodule ℂ H} [W.HasOrthogonalProjection]
    (hW : IsKStableOn ε σ W) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (x : H) :
    W.starProjection (σ k x) = σ k (W.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hW k hk _ (W.starProjection_apply_mem x))
    fun w hw => ?_
  rw [← map_sub, FormF.inner_rep_K hU hk]
  exact W.starProjection_inner_eq_zero x _ (hW _ (Kset_star ε hk) w hw)

theorem orth_of_ne (hU : IsURepOn (Kset ε) σ) {Λ μ : Fin n → ℝ} {S T : Submodule ℂ H}
    (hS : IsKTypeOf ε σ Λ S) (hT : IsKTypeOf ε σ μ T) (hne : μ ≠ Λ) :
    ∀ x ∈ S, ∀ y ∈ T, ⟪x, y⟫_ℂ = 0 := by
  haveI := hT.1
  let Q : S →L[ℂ] H := T.starProjection.comp S.subtypeL
  by_cases hQ : Q = 0
  · intro x hx y hy
    have h1 : T.starProjection x = 0 := congrArg (fun A : S →L[ℂ] H => A ⟨x, hx⟩) hQ
    have h2 := T.starProjection_inner_eq_zero x y hy
    rwa [h1, sub_zero] at h2
  exfalso
  have hR := FormF.rangeType n ε Λ H σ S H σ Q hS (fun k hk x y hxy => by
    change T.starProjection (y : H) = σ k (T.starProjection (x : H))
    rw [hxy, proj_comm hU hT.2.1 hk]) hQ
  have hle : LinearMap.range (Q : S →ₗ[ℂ] H) ≤ T := by
    rintro _ ⟨x, rfl⟩
    exact T.starProjection_apply_mem _
  obtain ⟨v, hv, hv0, hvw⟩ := hR.2.2.2.1
  rcases hT.2.2.1 _ hle hR.2.1 with h | h
  · rw [h] at hv
    exact hv0 hv
  · obtain ⟨w, hw, hw0, hww⟩ := hT.2.2.2.1
    refine hne (GlobalTheory.LowHW.cdom_antisymm (ε := ε) (hR.2.2.2.2 μ w (h ▸ hw) hw0 hww)
      (hT.2.2.2.2 Λ v (hle hv) hv0 hvw))

theorem exists_orth (hU : IsURepOn (Kset ε) σ) {Λ : Fin n → ℝ} {S T : Submodule ℂ H}
    (hS : IsKTypeOf ε σ Λ S) (hT : IsKTypeOf ε σ Λ T) (hne : S ≠ T) :
    ∃ R : Submodule ℂ H, IsKTypeOf ε σ Λ R ∧ ∀ x ∈ R, ∀ y ∈ T, ⟪x, y⟫_ℂ = 0 := by
  haveI := hT.1
  let Q : S →L[ℂ] H := S.subtypeL - T.starProjection.comp S.subtypeL
  have hQa : ∀ x : S, Q x = (x : H) - T.starProjection (x : H) := fun x => rfl
  have hQ : Q ≠ 0 := by
    intro hQ
    have hle : S ≤ T := by
      intro x hx
      have h1 := hQa ⟨x, hx⟩
      rw [hQ] at h1
      have h2 : x = T.starProjection x := sub_eq_zero.1 h1.symm
      rw [h2]
      exact T.starProjection_apply_mem _
    rcases hT.2.2.1 _ hle hS.2.1 with h | h
    · obtain ⟨v, hv, hv0, -⟩ := hS.2.2.2.1
      rw [h] at hv
      exact hv0 hv
    · exact hne h
  refine ⟨_, FormF.rangeType n ε Λ H σ S H σ Q hS (fun k hk x y hxy => by
    rw [hQa, hQa, hxy, proj_comm hU hT.2.1 hk, map_sub]) hQ, ?_⟩
  rintro _ ⟨x, rfl⟩ y hy
  exact T.starProjection_inner_eq_zero x y hy

theorem exists_gap {lam : Fin n → ℝ} (hl : StrictAnti lam)
    (h : ∀ a b : Fin n, ε a ≠ ε b → 2 * (n : ℝ) < |lam a - lam b|) :
    ∃ g : ℝ, (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) ∧ 2 * (n : ℝ) < g := by
  have key : ∀ᶠ g in nhdsWithin (2 * (n : ℝ)) (Set.Ioi (2 * (n : ℝ))),
      ∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b := by
    simp only [Filter.eventually_all]
    intro a b hab he
    have h1 := h a b he
    rw [abs_of_pos (sub_pos.2 (hl hab))] at h1
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds ((eventually_lt_nhds h1).mono fun g hg => hg.le)
  exact (key.and self_mem_nhdsWithin).exists

theorem kSpan_smul_le {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (c : ℂ)
    (u : V) : kSpan ε E (c • u) ≤ kSpan ε E u :=
  sInf_le_sInf fun S hS => ⟨S.smul_mem c hS.1, hS.2⟩

theorem cas_mem_cyc {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)
    (u : V) : Cas E u ∈ cyc E u := by
  rw [cyc, Submodule.mem_sInf]
  intro W hW
  simp only [Cas, LinearMap.sum_apply, Module.End.mul_apply]
  exact W.sum_mem fun a _ => W.sum_mem fun b _ => hW.2 _ _ _ (hW.2 _ _ _ hW.1)

theorem cas_kHighest {V : Type} [AddCommGroup V] [Module ℂ V] {E : Fin n → Fin n → Module.End ℂ V}
    (hE : GlRel E) {μ : Fin n → ℝ} {u : V} (hu : KHighest ε E μ u) : KHighest ε E μ (Cas E u) := by
  have hc : ∀ a b, E a b (Cas E u) = Cas E (E a b u) := fun a b =>
    (congrArg (fun A : Module.End ℂ V => A u) ((casCentral _ n ε E hE).1 a b)).symm
  exact ⟨fun a => by rw [hc, hu.1 a, map_smul], fun a b h1 h2 => by rw [hc, hu.2 a b h1 h2, map_zero]⟩

theorem cas_real {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {E : Fin n → Fin n → Module.End ℂ V}
    (hE : GlRel E) (hU : IsUnitary ε E) {μ : Fin n → ℝ} {u : V} (hu : KHighest ε E μ u) (hu0 : u ≠ 0) {c : ℂ}
    (hc : Cas E u = c • u) : ∃ r : ℝ, Cas E u = (r : ℂ) • u := by
  have h := wdCas V n ε E μ u hE hU hu
  rw [hc, inner_smul_right, inner_self_eq_norm_sq_to_K] at h
  generalize ((nsq (μ + rhoC ε) - nsq (rhoC ε)) * ‖u‖ ^ 2 -
      ∑ a, ∑ b, (if ε a = ε b then 0 else ‖E a b u‖ ^ 2) : ℝ) = t at h
  refine ⟨t / ‖u‖ ^ 2, ?_⟩
  have hn : ((‖u‖ : ℝ) : ℂ) ≠ 0 := by simpa using hu0
  rw [hc]
  congr 1
  push_cast
  rw [← h, eq_div_iff (pow_ne_zero 2 hn)]
  rfl

theorem isKTypeOf_lowKSub : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ → (∀ a b : Fin n, ε a ≠ ε b → 2 * (n : ℝ) < |lam a - lam b|) → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) := by
  intro n ε lam H _ _ σ hl hDS hgap
  obtain ⟨hc, -, hU, hirr, -, ⟨S0, hS0⟩, -⟩ := id hDS
  have hK := FormF.URep_K hU
  obtain ⟨V, E, S, hD, hS, hSV⟩ := GlobalTheory.SmoothKType.exists_isDer_kType n ε _ H σ S0 hU hS0
  obtain ⟨hk1, hk2⟩ := GlobalTheory.Jet.KType.kType_iff n ε H σ V E hU hD
  obtain ⟨v, hv, hv0, hvw⟩ := hS.2.2.2.1
  obtain ⟨u, rfl⟩ : ∃ u : V, (u : H) = v := ⟨⟨v, hSV hv⟩, rfl⟩
  have hu0 : u ≠ 0 := fun h => hv0 (by rw [h]; rfl)
  obtain ⟨huH, huS, hufd⟩ := hk2 _ S u hS hSV hv hu0 hvw
  obtain ⟨g, hg1, hg2⟩ := exists_gap hl.1 hgap
  have hm : ∀ x ∈ cyc E u, KHighest ε E (lowK ε lam) x → ∃ c : ℂ, x = c • u :=
    GlobalTheory.Jet.kHighest_eq_smul_of_minus_killed V n ε E lam g u hD.1 hD.2.1 huH hufd hg1 hg2
      (GlobalTheory.Jet.Schmid.mul_vminus_eq_zero n ε H σ V E lam u hl hDS hD huH hufd)
  obtain ⟨c, hcu⟩ := hm _ (cas_mem_cyc E u) (cas_kHighest hD.1 huH)
  obtain ⟨r, hr⟩ := cas_real hD.1 hD.2.1 huH hu0 hcu
  have hdense := GlobalTheory.CycDense.cyc_dense n ε H σ V E _ r u hU hD hirr hu0 huH hufd hr
  obtain ⟨-, -, hst, -, hpc, hcp, hfd⟩ := pfilFacts V n ε E u hD.1
  have huniq : ∀ T : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) T → T = S := by
    intro T hT
    by_contra hne
    obtain ⟨R, hR, hRS⟩ := exists_orth hK hT hS hne
    obtain ⟨w, hw, hw0, -⟩ := hR.2.2.2.1
    refine hw0 (hdense.eq_zero_of_inner_left ℂ fun y hy => ?_)
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨j, hj⟩ := hcp z hz
    haveI := hfd hufd j
    obtain ⟨m, x, μ, hx, -, hsup⟩ := kDecomp V n ε E _ (hfd hufd j) (glRel_kRel ε E hD.1)
      (isUnitary_kUnit ε E hD.2.1) (hst j)
    have hle : pfil ε E u j ≤ LinearMap.ker ((innerSL ℂ w : H →L[ℂ] ℂ).toLinearMap ∘ₗ V.subtype) := by
      rw [← hsup]
      refine iSup_le fun i y hy => ?_
      change ⟪w, (y : H)⟫_ℂ = 0
      by_cases hμ : μ i = lowK ε lam
      · obtain ⟨d, hd⟩ := hm (x i) (hpc j (hx i).1) (hμ ▸ (hx i).2.2)
        rw [hd] at hy
        exact hRS w hw _ (huS ▸ ⟨y, kSpan_smul_le E d u hy, rfl⟩)
      · have hfi : FiniteDimensional ℂ (kSpan ε E (x i)) :=
          Submodule.finiteDimensional_of_le (S₂ := pfil ε E u j) (sInf_le ⟨(hx i).1, hst j⟩)
        exact orth_of_ne hK hR (hk1 _ _ (hx i).2.1 (hx i).2.2 hfi) hμ w hw _ ⟨y, hy, rfl⟩
    exact hle hj
  have : lowKSub ε lam σ = S := le_antisymm (sSup_le fun T hT => (huniq T hT).le) (le_sSup hS)
  rw [this]
  exact hS

end GlobalTheory.Jet.MultGap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableFlagGramNumberNormalizedIndicator
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.YMeas

theorem exists_matrix_ker {n : ℕ} (Q : Submodule ℂ (Fin n → ℂ)) :
    ∃ M : Matrix (Fin n) (Fin n) ℂ, ∀ v, M *ᵥ v = 0 ↔ v ∈ Q := by
  obtain ⟨P, hP⟩ := Q.exists_isCompl
  refine ⟨LinearMap.toMatrix' (P.subtype ∘ₗ P.projectionOnto Q hP.symm), fun v => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  simp

theorem measurable_proj {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (Q : Submodule ℂ (Fin n → ℂ)) (g : X → Matrix (Fin n) (Fin n) ℂ)
    (v : X → EuclideanSpace ℂ (Fin n)) (hg : Continuous g) (hv : Continuous v) :
    Measurable fun x => ((LinearMap.ker (Matrix.toLin' A) ⊓ Q.comap (Matrix.toLin' (g x))).comap
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap).starProjection (v x) := by
  obtain ⟨M, hM⟩ := exists_matrix_ker Q
  let Φ : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n ⊕ Fin n)) :=
    (LinearMap.toContinuousLinearMap.toLinearMap).comp Matrix.toEuclideanLin.toLinearMap
  have hΦ : Continuous Φ := Φ.continuous_of_finiteDimensional
  have hMg : Continuous fun x => M * g x := continuous_const.matrix_mul hg
  have hL : Continuous fun x => Matrix.fromRows A (M * g x) := by
    refine continuous_matrix fun i j => ?_
    rcases i with i | i
    · simpa using continuous_const
    · simpa using hMg.matrix_elem i j
  have h := GlobalTheory.measurable_starProjection_ker_clm (fun x => Φ (Matrix.fromRows A (M * g x))) v (hΦ.comp hL) hv
  have e : ∀ x, ((LinearMap.ker (Matrix.toLin' A) ⊓ Q.comap (Matrix.toLin' (g x))).comap
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap) =
      LinearMap.ker (Φ (Matrix.fromRows A (M * g x)) :
        EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n ⊕ Fin n)) := by
    intro x
    ext p
    have h1 : Φ (Matrix.fromRows A (M * g x)) p =
        WithLp.toLp 2 (Matrix.fromRows A (M * g x) *ᵥ p.ofLp) := rfl
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, h1, WithLp.toLp_eq_zero, Matrix.fromRows_mulVec,
      ← Matrix.mulVec_mulVec]
    simp only [Submodule.mem_comap, Submodule.mem_inf, LinearMap.mem_ker, Matrix.toLin'_apply, ← hM]
    constructor
    · rintro ⟨h2, h3⟩
      funext i
      rcases i with i | i
      · exact congrFun h2 i
      · exact congrFun h3 i
    · intro h2
      exact ⟨funext fun i => congrFun h2 (Sum.inl i), funext fun i => congrFun h2 (Sum.inr i)⟩
  simp only [e]
  exact h

theorem measurableSet_GG (k r : ℕ) : MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r} := by
  refine IsClosed.measurableSet ?_
  have hc : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  exact isClosed_eq ((hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc) continuous_const

theorem measurable_gramProj (k r j : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r)
    (w : Fin j → Fin (2 * r + k + 1) → ℂ) :
    Measurable fun x : {x : Mt k r | Matrix.of x ∈ GG k r} =>
      gramProj (Ppos k r z z' γ (Matrix.of x.1)) (fun a : Fin j => (Matrix.of x.1 : Mat k r)⁻¹ *ᵥ w a) := by
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hc : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => (Matrix.of x.1 : Mat k r) :=
    continuous_subtype_val
  have hinv : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => (Matrix.of x.1 : Mat k r)⁻¹ := by
    rw [continuous_iff_continuousAt]
    intro x
    have hx : IsUnit (Matrix.of x.1 : Mat k r).det := ((uHGroup _ _ hH).2.2 _ x.2).1
    have h1 : ContinuousAt (Inv.inv : Mat k r → _) (Matrix.of x.1) := by
      refine continuousAt_matrix_inv _ ?_
      obtain ⟨u, hu⟩ := hx
      rw [← hu]
      exact NormedRing.inverse_continuousAt u
    exact ContinuousAt.comp (f := fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => (Matrix.of x.1 : Mat k r))
      h1 hc.continuousAt
  have hp : ∀ a : Fin j, Measurable fun x : {x : Mt k r | Matrix.of x ∈ GG k r} =>
      (Ppos k r z z' γ (Matrix.of x.1)).starProjection
        (WithLp.toLp 2 ((Matrix.of x.1 : Mat k r)⁻¹ *ᵥ w a)) := fun a =>
    measurable_proj (Hpk k r - 1) (Hcom k r z z' γ ⊔ Xsp k r) _ _ hc
      ((PiLp.continuous_toLp 2 _).comp (hinv.matrix_mulVec continuous_const))
  have hG : Continuous fun u : Fin j → EuclideanSpace ℂ (Fin (2 * r + k + 1)) =>
      Real.sqrt ‖(Matrix.gram ℂ u).det‖ := by
    refine Real.continuous_sqrt.comp (continuous_norm.comp (Continuous.matrix_det ?_))
    refine continuous_matrix fun a b => ?_
    simp only [Matrix.gram_apply]
    exact (continuous_apply a).inner (continuous_apply b)
  exact hG.measurable.comp (measurable_pi_lambda _ hp)

theorem yj_measurable : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ γ : Mat k r, inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → γ ∈ GG k r → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun x => Yj k r hj z z' γ (Matrix.of x)) ∧ ∀ R₀ y : ℝ, MeasurableSet (Eset0 k r hj z z' γ R₀ y) := by
  intro k r j hj z z' γ hz hz' hT hT' hγ
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hS := measurableSet_GG k r
  have hY : Measurable fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Yj k r hj z z' γ (Matrix.of x.1) :=
    (measurable_gramProj k r j z z' γ _).div_const _
  have hc : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => (Matrix.of x.1 : Mat k r) :=
    continuous_subtype_val
  have h1 : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Sg2 k r z' (Matrix.of x.1) :=
    (TwoSided.Sg2_invariant_continuousOn_one_le_bounds k r z' hz' hT').2.2.1.comp_continuous hc fun x => x.2
  have h2 : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Sg2 k r z (γ * Matrix.of x.1) :=
    (TwoSided.Sg2_invariant_continuousOn_one_le_bounds k r z hz hT).2.2.1.comp_continuous (continuous_const.matrix_mul hc)
      fun x => (uHGroup _ _ hH).2.1 _ hγ _ x.2
  refine ⟨?_, fun R₀ y => ?_⟩
  · refine measurable_of_restrict_of_restrict_compl hS ?_ ?_
    · convert hY using 1
      funext x
      exact Set.indicator_of_mem x.2 _
    · convert (measurable_const (a := (0 : ℝ))) using 1
      funext x
      exact Set.indicator_of_notMem x.2 _
  have e : Eset0 k r hj z z' γ R₀ y = Subtype.val '' {x : {x : Mt k r | Matrix.of x ∈ GG k r} |
      Sg2 k r z' (Matrix.of x.1) ≤ R₀ ∧ Sg2 k r z (γ * Matrix.of x.1) ≤ R₀ ∧
        y < Yj k r hj z z' γ (Matrix.of x.1) ∧ Yj k r hj z z' γ (Matrix.of x.1) ≤ 2 * y} := by
    ext x
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨⟨x, hx⟩, h, rfl⟩
    · rintro ⟨⟨x, hx⟩, h, rfl⟩
      exact ⟨hx, h⟩
  rw [e]
  refine hS.subtype_image ?_
  exact (measurableSet_le h1.measurable measurable_const).inter
    ((measurableSet_le h2.measurable measurable_const).inter
      ((measurableSet_lt measurable_const hY).inter (measurableSet_le hY measurable_const)))

end GlobalTheory.Amp.YMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevValueAtOneFixedCompactDiagSignUnitaryStatement
section
open MeasureTheory Matrix Formalism.MainNotions.S
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_valueAtOne_fixedCompact_diagSignUnitary : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ (S : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ) (Q : Set (Formalism.REAL.UJ ε)), IsCompact Q ∧ (∀ l ∈ S, ∀ X ∈ l, Formalism.REAL.inG ε X) ∧ 0 ≤ C ∧ ∀ F : List (Matrix (Fin n) (Fin n) ℂ) → Matrix (Fin n) (Fin n) ℂ → ℂ, (∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ContinuousOn (F l) (UJset ε)) → (∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ∀ X, Formalism.REAL.inG ε X → ∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => F l (g * NormedSpace.exp ((t : ℂ) • X))) (F (X :: l) g) 0) → ENNReal.ofReal (‖F [] 1‖ ^ 2) ≤ ENNReal.ofReal C * (S.map fun l => ∫⁻ y in Q, ENNReal.ofReal (‖F l (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε)).sum := by
  first | exact @GlobalTheory.SobolevHaar.sobolev_at_one_compact | exact GlobalTheory.SobolevHaar.sobolev_at_one_compact | (intros; apply GlobalTheory.SobolevHaar.sobolev_at_one_compact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrictFundamentalSetIntegralStabilizerExistsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strict_fundamentalSet_integralStabilizer_exists : GlobalTheory.TypeAsm.FundC := by
  first | exact @GlobalTheory.TypeAsm.fundC_holds | exact GlobalTheory.TypeAsm.fundC_holds | (intros; apply GlobalTheory.TypeAsm.fundC_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrictFundamentalSetUnipotentOnBesselModelsStatement
section
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictFundamentalSet_unipotent_on_besselModels : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1),
    GlobalTheory.DegVol.IsFund (trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u)
      (GlobalTheory.DegVol.RP D.R.k D.R.rS (fun _ => 1)) (trI C '' Y.FN u) := by
  first | exact @GlobalTheory.TypeAsm.CovTrans.isFund_trI | exact GlobalTheory.TypeAsm.CovTrans.isFund_trI | (intros; apply GlobalTheory.TypeAsm.CovTrans.isFund_trI <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaUnipotentActionCocycleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_unipotent_action_cocycle : ∀ (D : D7) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι), ∀ n ∈ d.N, ∀ n' ∈ d.N, d.aCo (n * n') = d.aCo n + d.aCo n' ∧ d.tCo (n * n') = d.tCo n + d.tCo n' - hA A (d.aCo n') (d.aCo n) ∧ (∀ ψ : AddChar (AF D.host.F) ℂ, d.chr ψ (n * n') = d.chr ψ n * d.chr ψ n') ∧ ∃ b : Fin d.ρ → AE D, actV B n d.fTop = vecA B d.fTop + ((frameMat B A ι).map (incA D)).mulVec (d.aCo n) + ∑ l, b l • vecA B (d.e l) := by
  first | exact @GlobalTheory.HeisLaw.law | exact GlobalTheory.HeisLaw.law | (intros; apply GlobalTheory.HeisLaw.law <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TopMinorAndGramNumberLeMajorantLengthsStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_minor_and_gram_number_le_majorant_lengths : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r), TwoFl k r z z' γ → ∀ x ∈ GG k r, Dr k r z z' γ ≤ Sg k r z' x ^ r * Sg k r z (γ * x) ^ r ∧ 0 ≤ Yv k r z z' γ x ∧ Yv k r z z' γ x ≤ Sg k r z (γ * x) ^ r / Dr k r z z' γ := by
  first | exact @GlobalTheory.Amp.YBound.dr_y_le | exact GlobalTheory.Amp.YBound.dr_y_le | (intros; apply GlobalTheory.Amp.YBound.dr_y_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoSidedSizeFunctionPosInvariantContinuousStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_sided_size_function_pos_invariant_continuous : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → (∀ x ∈ GG k r, ∀ a, 0 < lA k r z x a) ∧ (∀ x ∈ GG k r, ∀ s ∈ Sset k r z, ∀ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), Sg2 k r z (s * x * κ) = Sg2 k r z x) ∧ ContinuousOn (Sg2 k r z) (GG k r) ∧ ∀ x, 1 ≤ Sg2 k r z x ∧ Sg k r z x ≤ Sg2 k r z x ∧ (∀ a, lA k r z x a ≤ Sg2 k r z x ∧ (lA k r z x a)⁻¹ ≤ Sg2 k r z x) ∧ (Sg2 k r z x = 1 ∨ ∃ a, Sg2 k r z x = max (lA k r z x a) (lA k r z x a)⁻¹) := by
  first | exact @GlobalTheory.Amp.TwoSided.Sg2_invariant_continuousOn_one_le_bounds | exact GlobalTheory.Amp.TwoSided.Sg2_invariant_continuousOn_one_le_bounds | (intros; apply GlobalTheory.Amp.TwoSided.Sg2_invariant_continuousOn_one_le_bounds <;> assumption)
end

