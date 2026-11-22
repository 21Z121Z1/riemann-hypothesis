import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0011
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0170
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0143
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0181
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0160
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusModulusUnipotentRadicalUnitaryGroup
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocSizeBlocks
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

noncomputable section

namespace GlobalTheory.LeviIso.Size

theorem detOn_of_frame {n : ℕ} {m : Type} [Fintype m] [DecidableEq m] (g : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin n) m ℂ) (X : Matrix m m ℂ) (W : Submodule ℂ (Fin n → ℂ)) (hC : Cᴴ * C = 1)
    (hW : ∀ y, y ∈ W ↔ ∃ u, y = C *ᵥ u) (hg : g * C = C * X) : detOn g W = ‖X.det‖ := by
  have hst : ∀ y ∈ W, Matrix.toLin' g y ∈ W := by
    intro y hy
    obtain ⟨u, rfl⟩ := (hW y).1 hy
    exact (hW _).2 ⟨X *ᵥ u, by rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hg, Matrix.mulVec_mulVec]⟩
  let f : (m → ℂ) →ₗ[ℂ] W := (Matrix.toLin' C).codRestrict W fun u => (hW _).2 ⟨u, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun u v h => ?_, fun y => ?_⟩
    · have h1 : C *ᵥ u = C *ᵥ v := congrArg Subtype.val h
      have h2 := congrArg (fun y => Cᴴ *ᵥ y) h1
      simpa only [Matrix.mulVec_mulVec, hC, Matrix.one_mulVec] using h2
    · obtain ⟨u, hu⟩ := (hW y).1 y.2
      exact ⟨u, Subtype.ext hu.symm⟩
  let e := LinearEquiv.ofBijective f hf
  have he : (Matrix.toLin' g).restrict hst =
      (e : (m → ℂ) →ₗ[ℂ] W) ∘ₗ Matrix.toLin' X ∘ₗ (e.symm : W →ₗ[ℂ] (m → ℂ)) := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨u, rfl⟩ := e.surjective y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    change g *ᵥ (C *ᵥ u) = C *ᵥ (X *ᵥ u)
    rw [Matrix.mulVec_mulVec, hg, Matrix.mulVec_mulVec]
  unfold detOn
  rw [dif_pos hst, he, LinearMap.det_conj, LinearMap.det_toLin']

theorem detOn_blocks {n a : ℕ} {j : Fin a → ℕ} (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ)
    (p : Fin a → Prop) [DecidablePred p] (W : Submodule ℂ (Fin n → ℂ))
    (h1 : ∀ i, (B i)ᴴ * B i = 1) (h2 : ∀ i k, i ≠ k → (B i)ᴴ * B k = 0)
    (hW : ∀ y, y ∈ W ↔ ∃ u : ∀ i, Fin (j i) → ℂ, (∀ i, ¬ p i → u i = 0) ∧ y = ∑ i, B i *ᵥ u i)
    (g : Matrix (Fin n) (Fin n) ℂ) (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ)
    (hg : ∀ i, g * B i = B i * x i) :
    detOn g W = ∏ i ∈ Finset.univ.filter p, ‖(x i).det‖ := by
  let C : Matrix (Fin n) (Σ i : {i // p i}, Fin (j i)) ℂ := Matrix.of fun r s => B s.1 r s.2
  have hCv : ∀ u, C *ᵥ u = ∑ i : {i // p i}, B i *ᵥ fun s => u ⟨i, s⟩ := by
    intro u
    funext r
    simp [C, Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [detOn_of_frame g C (Matrix.blockDiagonal' fun i : {i // p i} => x i) W ?_ ?_ ?_]
  · rw [ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.det_blockDiagonal', norm_prod,
      Finset.prod_subtype (Finset.univ.filter p) (p := p) (by simp)]
  · ext ⟨i, s⟩ ⟨k, t⟩
    change ((B i)ᴴ * B k) s t = _
    by_cases h : i = k
    · subst h
      rw [h1]
      simp [Matrix.one_apply]
    · rw [h2 i k (fun e => h (Subtype.ext e)), Matrix.one_apply_ne (fun e => h (congrArg Sigma.fst e))]
      rfl
  · intro y
    rw [hW]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨fun s => u s.1 s.2, ?_⟩
      rw [hCv, ← Finset.sum_subtype (Finset.univ.filter p) (by simp) (fun i => B i *ᵥ u i),
        Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with h
      · rfl
      · rw [hu i h, Matrix.mulVec_zero]
    · rintro ⟨u, rfl⟩
      refine ⟨fun i => if h : p i then fun s => u ⟨⟨i, h⟩, s⟩ else 0, fun i h => dif_neg h, ?_⟩
      rw [hCv, ← Finset.sum_subset (Finset.filter_subset p Finset.univ) ?_,
        Finset.sum_subtype (Finset.univ.filter p) (p := p) (by simp)]
      · refine Finset.sum_congr rfl fun i _ => ?_
        beta_reduce
        rw [dif_pos i.2]
      · intro i _ hi
        beta_reduce
        rw [dif_neg (by simpa using hi), Matrix.mulVec_zero]
  · ext r ⟨k, t⟩
    change (g * B k) r t = _
    rw [hg, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single k]
    · simp [C]
    · intro i _ hi
      simp [Matrix.blockDiagonal'_apply_ne _ _ _ hi]
    · simp

theorem locSize_blocks : ∀ (n a : ℕ) (j : Fin a → ℕ) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∀ i, (B i)ᴴ * B i = 1) → (∀ i k, i ≠ k → (B i)ᴴ * B k = 0) → SpansFlag B W → ∀ (g : Matrix (Fin n) (Fin n) ℂ) (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ), (∀ i, (x i).det ≠ 0) → (∀ i, g * B i = B i * x i) → ∀ i, locSize j W g i = ‖(x i).det‖ ^ (-(1 : ℝ) / j i) := by
  intro n a j B W h1 h2 hW g x hx hg i
  unfold locSize
  rw [detOn_blocks B _ _ h1 h2 (hW i.succ) g x hg, detOn_blocks B _ _ h1 h2 (hW i.castSucc) g x hg]
  have e : (Finset.univ.filter fun k : Fin a => k.castSucc < i.succ) =
      insert i (Finset.univ.filter fun k : Fin a => k.castSucc < i.castSucc) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.lt_def, Fin.ext_iff,
      Fin.val_succ, Fin.val_castSucc]
    omega
  rw [e, Finset.prod_insert (by simp), mul_div_cancel_right₀]
  exact Finset.prod_ne_zero_iff.2 fun k _ => norm_ne_zero_iff.2 (hx k)

end GlobalTheory.LeviIso.Size
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureInterTranslateEqZeroOfCovolume
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory.StrictDomain

theorem null_of_translate_disjoint {X : Type} [Mul X] [MeasurableSpace X] (S : Set X) (μ : Measure X)
    (U D : Set X) (hc : S.Countable) (hm : ∀ γ ∈ S, Measurable fun x => γ * x)
    (hinv : ∀ γ ∈ S, μ.map (fun x => γ * x) = μ)
    (hmul : ∀ γ ∈ S, ∀ δ ∈ S, ∃ ε ∈ S, ∀ x, ε * x = γ * (δ * x))
    (hi : ∀ γ ∈ S, ∃ δ ∈ S, (∀ x, δ * (γ * x) = x) ∧ ∀ x, γ * (δ * x) = x)
    (hU : MeasurableSet U) (hUS : ∀ γ ∈ S, ∀ x ∈ U, γ * x ∈ U) (hDU : D ⊆ U)
    (hcov : ∀ A, MeasurableSet A → A ⊆ U → (∀ γ ∈ S, ∀ x ∈ A, γ * x ∈ A) →
      covol S μ A = μ (A ∩ D))
    (γ : X) (hγ : γ ∈ S) (B : Set X) (hB : MeasurableSet B) (hfin : μ B ≠ ⊤)
    (hBD : B ⊆ D) (hBγ : ∀ x ∈ B, γ * x ∈ D) (hdis : ∀ x ∈ B, γ * x ∉ B) : μ B = 0 := by
  obtain ⟨δ, hδ, hδγ, hγδ⟩ := hi γ hγ
  set A : Set X := U ∩ ⋃ ε ∈ S, (fun x => ε * x) ⁻¹' B with hA
  have hmemA : ∀ x, x ∈ A ↔ x ∈ U ∧ ∃ ε ∈ S, ε * x ∈ B := by
    intro x
    simp [hA]
  have hAm : MeasurableSet A :=
    hU.inter (MeasurableSet.biUnion hc fun ε hε => hm ε hε hB)
  have hAinv : ∀ η ∈ S, ∀ x ∈ A, η * x ∈ A := by
    intro η hη x hx
    obtain ⟨hxU, ε, hε, hεx⟩ := (hmemA x).1 hx
    obtain ⟨η', hη', h1, -⟩ := hi η hη
    obtain ⟨κ, hκ, hκe⟩ := hmul ε hε η' hη'
    exact (hmemA _).2 ⟨hUS η hη x hxU, κ, hκ, by rw [hκe, h1]; exact hεx⟩
  have hle : μ (A ∩ D) ≤ μ B := by
    rw [← hcov A hAm Set.inter_subset_left hAinv]
    unfold covol
    exact iInf_le_of_le B (iInf_le_of_le hB (iInf_le_of_le (fun x hx => ((hmemA x).1 hx).2) le_rfl))
  set B' : Set X := (fun x => δ * x) ⁻¹' B with hB'
  have hB'm : MeasurableSet B' := hm δ hδ hB
  have hB'μ : μ B' = μ B := by
    rw [hB', ← Measure.map_apply (hm δ hδ) hB, hinv δ hδ]
  have hdj : Disjoint B B' := by
    rw [Set.disjoint_left]
    intro x hx hx'
    have := hdis _ hx'
    rw [hγδ] at this
    exact this hx
  have hsub : B ∪ B' ⊆ A ∩ D := by
    rintro x (hx | hx)
    · obtain ⟨κ, hκ, hκe⟩ := hmul δ hδ γ hγ
      exact ⟨(hmemA x).2 ⟨hDU (hBD hx), κ, hκ, by rw [hκe, hδγ]; exact hx⟩, hBD hx⟩
    · have hxD : x ∈ D := by
        have := hBγ _ hx
        rwa [hγδ] at this
      exact ⟨(hmemA x).2 ⟨hDU hxD, δ, hδ, hx⟩, hxD⟩
  have h2 : μ B + μ B ≤ μ B + 0 := by
    calc μ B + μ B = μ (B ∪ B') := by rw [measure_union hdj hB'm, hB'μ]
      _ ≤ μ (A ∩ D) := measure_mono hsub
      _ ≤ μ B + 0 := by rw [add_zero]; exact hle
  exact le_antisymm ((ENNReal.add_le_add_iff_left hfin).1 h2) zero_le

theorem measure_inter_translate_eq_zero : ∀ (X : Type) [Mul X] [MeasurableSpace X] [MeasurableSpace.CountablySeparated X] (S : Set X) (μ : Measure X) [SigmaFinite μ] (U D : Set X), S.Countable → (∀ γ ∈ S, Measurable fun x => γ * x) → (∀ γ ∈ S, μ.map (fun x => γ * x) = μ) → (∀ γ ∈ S, ∀ δ ∈ S, ∃ ε ∈ S, ∀ x, ε * x = γ * (δ * x)) → (∀ γ ∈ S, ∃ δ ∈ S, (∀ x, δ * (γ * x) = x) ∧ ∀ x, γ * (δ * x) = x) → MeasurableSet U → (∀ γ ∈ S, ∀ x ∈ U, γ * x ∈ U) → MeasurableSet D → D ⊆ U → (∀ A, MeasurableSet A → A ⊆ U → (∀ γ ∈ S, ∀ x ∈ A, γ * x ∈ A) → covol S μ A = μ (A ∩ D)) → ∀ γ ∈ S, (∀ x ∈ U, γ * x ≠ x) → μ {x | x ∈ D ∧ γ * x ∈ D} = 0 := by
  intro X _ _ _ S μ _ U D hc hm hinv hmul hi hU hUS hD hDU hcov γ hγ hfree
  obtain ⟨V, hVm, hV⟩ := exists_seq_separating X MeasurableSet.univ (Set.univ : Set X)
  have key : ∀ (W : Set X), MeasurableSet W → ∀ m : ℕ,
      μ (D ∩ (fun x => γ * x) ⁻¹' D ∩ W ∩ (fun x => γ * x) ⁻¹' Wᶜ ∩ spanningSets μ m) = 0 := by
    intro W hW m
    refine null_of_translate_disjoint S μ U D hc hm hinv hmul hi hU hUS hDU hcov γ hγ _
      ((((hD.inter (hm γ hγ hD)).inter hW).inter (hm γ hγ hW.compl)).inter
        (measurableSet_spanningSets μ m))
      (ne_top_of_le_ne_top (measure_spanningSets_lt_top μ m).ne
        (measure_mono Set.inter_subset_right)) ?_ ?_ ?_
    · intro x hx
      exact hx.1.1.1.1
    · intro x hx
      exact hx.1.1.1.2
    · intro x hx hx'
      exact hx.1.2 hx'.1.1.2
  have hsub : {x | x ∈ D ∧ γ * x ∈ D} ⊆ ⋃ n : ℕ, ⋃ m : ℕ,
      ((D ∩ (fun x => γ * x) ⁻¹' D ∩ V n ∩ (fun x => γ * x) ⁻¹' (V n)ᶜ ∩ spanningSets μ m) ∪
       (D ∩ (fun x => γ * x) ⁻¹' D ∩ (V n)ᶜ ∩ (fun x => γ * x) ⁻¹' (V n)ᶜᶜ ∩ spanningSets μ m)) := by
    rintro x ⟨hx, hγx⟩
    have hne := hfree x (hDU hx)
    obtain ⟨n, hn⟩ : ∃ n, ¬ (γ * x ∈ V n ↔ x ∈ V n) := by
      by_contra h
      push_neg at h
      exact hne (hV _ (Set.mem_univ _) _ (Set.mem_univ _) h)
    have hm' : x ∈ ⋃ m, spanningSets μ m := by rw [iUnion_spanningSets]; exact Set.mem_univ _
    obtain ⟨m, hm'⟩ := Set.mem_iUnion.1 hm'
    refine Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨m, ?_⟩⟩
    by_cases hxV : x ∈ V n
    · exact Or.inl ⟨⟨⟨⟨hx, hγx⟩, hxV⟩, fun h => hn ⟨fun _ => hxV, fun _ => h⟩⟩, hm'⟩
    · exact Or.inr ⟨⟨⟨⟨hx, hγx⟩, hxV⟩, fun h => hn ⟨fun h' => (h h').elim, fun h' => (hxV h').elim⟩⟩, hm'⟩
  refine measure_mono_null hsub (measure_iUnion_null fun n => measure_iUnion_null fun m => ?_)
  exact measure_union_null (key _ (hVm n) m) (key _ (hVm n).compl m)

end GlobalTheory.StrictDomain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingCommonStabilizerCoordinatesAtPl
section
noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCov.Transp

private theorem measurePreserving_curry_symm_pi (ι κ A : Type) [Fintype ι] [Fintype κ] [MeasurableSpace A]
    (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ A).symm (Measure.pi fun _ : ι => Measure.pi fun _ : κ => μ)
      (Measure.pi fun _ : ι × κ => μ) := by
  refine ⟨(MeasurableEquiv.curry ι κ A).symm.measurable, ?_⟩
  refine (Measure.pi_eq fun s _ => ?_).symm
  have hpre : (MeasurableEquiv.curry ι κ A).symm ⁻¹' Set.univ.pi s
      = Set.univ.pi fun i => Set.univ.pi fun j => s (i, j) := by
    ext f
    simp [MeasurableEquiv.coe_curry_symm, Prod.forall]
  rw [MeasurableEquiv.map_apply, hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

theorem curry_mp (ι κ A : Type) [Fintype ι] [Fintype κ] [MeasurableSpace A] (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ A) (Measure.pi fun _ => μ)
      (Measure.pi fun _ => Measure.pi fun _ => μ) := by
  have h := MeasurePreserving.symm _ (measurePreserving_curry_symm_pi ι κ A μ)
  rwa [MeasurableEquiv.symm_symm] at h

theorem swap_mp (ι κ A : Type) [Fintype ι] [Fintype κ] [MeasurableSpace A] (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (fun (f : ι → κ → A) (v : κ) (i : ι) => f i v)
      (Measure.pi fun _ => Measure.pi fun _ => μ) (Measure.pi fun _ => Measure.pi fun _ => μ) := by
  have h1 := measurePreserving_curry_symm_pi ι κ A μ
  have h2 := measurePreserving_piCongrLeft (fun _ : κ × ι => μ) (Equiv.prodComm ι κ)
  have h3 := curry_mp κ ι A μ
  have key : (fun (f : ι → κ → A) (v : κ) (i : ι) => f i v) =
      (MeasurableEquiv.curry κ ι A) ∘ (MeasurableEquiv.piCongrLeft (fun _ : κ × ι => A) (Equiv.prodComm ι κ)) ∘
        (MeasurableEquiv.curry ι κ A).symm := by
    funext f v i
    simp [MeasurableEquiv.coe_curry, MeasurableEquiv.coe_curry_symm, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply_eq_cast]
  rw [key]
  exact h3.comp (h2.comp h1)

theorem glue_mp {ι A B A' B' : Type} [Fintype ι] [MeasureSpace A] [MeasureSpace B] [MeasureSpace A'] [MeasureSpace B']
    [SigmaFinite (volume : Measure A)] [SigmaFinite (volume : Measure B)]
    [SigmaFinite (volume : Measure A')] [SigmaFinite (volume : Measure B')]
    {f : A' → ι → A} {g : B' → ι → B}
    (hf : MeasurePreserving f volume (Measure.pi fun _ : ι => (volume : Measure A)))
    (hg : MeasurePreserving g volume (Measure.pi fun _ : ι => (volume : Measure B))) :
    MeasurePreserving (fun (p : A' × B') (v : ι) => (f p.1 v, g p.2 v)) volume
      (Measure.pi fun _ : ι => (volume : Measure (A × B))) := by
  have h1 := hf.prod hg
  have h2 := MeasurePreserving.symm _
    (measurePreserving_arrowProdEquivProdArrow A B ι (fun _ => (volume : Measure A)) (fun _ => (volume : Measure B)))
  exact h2.comp h1

theorem sigmaFinite_volume_pi_family (I A : Type) [Fintype I] [MeasureSpace A] [SigmaFinite (volume : Measure A)] :
    SigmaFinite (volume : Measure (I → A)) := by
  show SigmaFinite (Measure.pi fun _ : I => (volume : Measure A))
  infer_instance

theorem sigmaFinite_volume_pi_double_family (I J A : Type) [Fintype I] [Fintype J] [MeasureSpace A] [SigmaFinite (volume : Measure A)] :
    SigmaFinite (volume : Measure (I → J → A)) := by
  have := sigmaFinite_volume_pi_family J A
  show SigmaFinite (Measure.pi fun _ : I => (volume : Measure (J → A)))
  infer_instance

theorem swap_vol (I ι A : Type) [Fintype I] [Fintype ι] [MeasureSpace A] [SigmaFinite (volume : Measure A)] :
    MeasurePreserving (fun (f : I → ι → A) (v : ι) (i : I) => f i v) volume
      (Measure.pi fun _ : ι => (volume : Measure (I → A))) := by
  have := sigmaFinite_volume_pi_family I A
  exact swap_mp I ι A volume

end GlobalTheory.DegVol.RefCov.Transp

namespace GlobalTheory.DegVol.RefCov

theorem atP_measurePreserving : ∀ (ι : Type) [Fintype ι] (k r j : ℕ) (β : Fin r → ℕ),
    MeasurePreserving (atP : Crd ι k r j β → ι → (UTin β → ℂ) × PTop k r j) volume
      (Measure.pi fun _ : ι => (volume : Measure ((UTin β → ℂ) × PTop k r j))) := by
  intro ι _ k r j β
  have s0 := Transp.sigmaFinite_volume_pi_family (Fin (k + 1)) ℂ
  have s1 := Transp.sigmaFinite_volume_pi_family (UTin β) ℂ
  have s2 := Transp.sigmaFinite_volume_pi_family {a : Fin r // j ≤ a.val} (Fin (k + 1) → ℂ)
  have s3 := Transp.sigmaFinite_volume_pi_family {p : UT r // j ≤ p.1.1.val} ℂ
  have s4 := Transp.sigmaFinite_volume_pi_family {a : Fin r // j ≤ a.val} ℝ
  have t1 := Transp.sigmaFinite_volume_pi_double_family (UTin β) ι ℂ
  have t2 := Transp.sigmaFinite_volume_pi_double_family {a : Fin r // j ≤ a.val} ι (Fin (k + 1) → ℂ)
  have t3 := Transp.sigmaFinite_volume_pi_double_family {p : UT r // j ≤ p.1.1.val} ι ℂ
  have t4 := Transp.sigmaFinite_volume_pi_double_family {a : Fin r // j ≤ a.val} ι ℝ
  have p1 : SigmaFinite (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ))) := by
    show SigmaFinite ((volume : Measure ({p : UT r // j ≤ p.1.1.val} → ℂ)).prod (volume : Measure ({a : Fin r // j ≤ a.val} → ℝ)))
    infer_instance
  have p2 : SigmaFinite (volume : Measure (({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ) × (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ)))) := by
    show SigmaFinite ((volume : Measure ({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ)).prod (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ))))
    infer_instance
  have q1 : SigmaFinite (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))) := by
    show SigmaFinite ((volume : Measure ({p : UT r // j ≤ p.1.1.val} → ι → ℂ)).prod (volume : Measure ({a : Fin r // j ≤ a.val} → ι → ℝ)))
    infer_instance
  have q2 : SigmaFinite (volume : Measure (({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) × (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ)))) := by
    show SigmaFinite ((volume : Measure ({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ)).prod (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))))
    infer_instance
  have e1 := Transp.swap_vol (UTin β) ι ℂ
  have e2 := Transp.swap_vol {a : Fin r // j ≤ a.val} ι (Fin (k + 1) → ℂ)
  have e3 := Transp.swap_vol {p : UT r // j ≤ p.1.1.val} ι ℂ
  have e4 := Transp.swap_vol {a : Fin r // j ≤ a.val} ι ℝ
  have g := Transp.glue_mp e1 (Transp.glue_mp e2 (Transp.glue_mp e3 e4))
  exact g

end GlobalTheory.DegVol.RefCov
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingRearrangePiProdMeasures
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem measurePreserving_rearrange (V V' V'' : Type) [Fintype V] [Fintype V'] [Fintype V''] (β : V ≃ V')
    (σ : V ≃ V'') (a : ℕ) (X : Fin a → Type) [∀ i, MeasurableSpace (X i)] (Y : V'' → Type)
    [∀ w, MeasurableSpace (Y w)] (m : ∀ i, Measure (X i)) [∀ i, SigmaFinite (m i)] (ν : ∀ w, Measure (Y w))
    [∀ w, SigmaFinite (ν w)] (b : Fin a → ℝ) (c : V'' → ℝ) (hb : ∀ i, 0 ≤ b i) (hc : ∀ w, 0 ≤ c w) :
    MeasurePreserving
      (fun (z : (∀ i, V' → X i) × (∀ w, Y w)) (v : V) => ((fun i => z.1 i (β v)), z.2 (σ v)))
      (((∏ i, ENNReal.ofReal (b i ^ Fintype.card V)) * ENNReal.ofReal (∏ w, c w)) •
        (Measure.pi fun i => Measure.pi fun _ : V' => m i).prod (Measure.pi ν))
      (Measure.pi fun v : V => (Measure.pi fun i => ENNReal.ofReal (b i) • m i).prod
        (ENNReal.ofReal (c (σ v)) • ν (σ v))) := by
  have hm : Measurable
      (fun (z : (∀ i, V' → X i) × (∀ w, Y w)) (v : V) => ((fun i => z.1 i (β v)), z.2 (σ v))) := by
    fun_prop
  refine ⟨hm, ?_⟩
  refine (Measure.pi_eq_generateFrom
    (C := fun v => Set.image2 (· ×ˢ ·)
      (Set.pi Set.univ '' Set.pi Set.univ fun i => {s : Set (X i) | MeasurableSet s})
      {s : Set (Y (σ v)) | MeasurableSet s})
    (fun v => (generateFrom_eq_prod generateFrom_pi MeasurableSpace.generateFrom_measurableSet
      (IsCountablySpanning.pi fun _ => isCountablySpanning_measurableSet)
      isCountablySpanning_measurableSet))
    (fun _ => isPiSystem_pi.prod MeasurableSpace.isPiSystem_measurableSet)
    (fun v => (Measure.FiniteSpanningSetsIn.pi fun i =>
      (ENNReal.ofReal (b i) • m i).toFiniteSpanningSetsIn).prod
        (ENNReal.ofReal (c (σ v)) • ν (σ v)).toFiniteSpanningSetsIn) ?_).symm
  intro s hs
  choose t' ht' u hu hst using hs
  choose t ht htt using ht'
  have htm : ∀ v i, MeasurableSet (t v i) := fun v i => ht v i (Set.mem_univ _)
  have hs' : ∀ v, s v = (Set.pi Set.univ (t v)) ×ˢ u v := fun v => by rw [← hst v, htt v]
  have hsm : MeasurableSet (Set.pi Set.univ s) := by
    refine MeasurableSet.univ_pi fun v => ?_
    rw [hs' v]
    exact (MeasurableSet.univ_pi fun i => htm v i).prod (hu v)
  obtain ⟨u', hu'⟩ : ∃ u' : ∀ w, Set (Y w), ∀ v, u' (σ v) = u v :=
    ⟨Equiv.piCongrLeft (fun w => Set (Y w)) σ u, fun v => Equiv.piCongrLeft_apply_apply _ _ _ _⟩
  rw [Measure.map_apply hm hsm]
  have hpre : (fun (z : (∀ i, V' → X i) × (∀ w, Y w)) (v : V) => ((fun i => z.1 i (β v)), z.2 (σ v))) ⁻¹'
      Set.pi Set.univ s =
      (Set.pi Set.univ fun i => Set.pi Set.univ fun v' => t (β.symm v') i) ×ˢ Set.pi Set.univ u' := by
    ext z
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, hs', Set.mem_prod, forall_and]
    refine and_congr ?_ ?_
    · rw [forall_comm]
      refine forall_congr' fun i => ?_
      rw [← β.forall_congr_right]
      simp only [Equiv.symm_apply_apply]
    · rw [← σ.forall_congr_right]
      simp only [hu']
  rw [hpre, Measure.smul_apply, Measure.prod_prod]
  simp only [hs', Measure.prod_prod, Measure.pi_pi, Measure.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have h1 : ∏ i, ∏ v', m i (t (β.symm v') i) = ∏ v, ∏ i, m i (t v i) := by
    rw [Finset.prod_comm]
    exact β.symm.prod_comp fun v => ∏ i, m i (t v i)
  have h2 : ∏ w, ν w (u' w) = ∏ v, ν (σ v) (u v) := by
    rw [← σ.prod_comp]
    simp only [hu']
  have h3 : ENNReal.ofReal (∏ w, c w) = ∏ v, ENNReal.ofReal (c (σ v)) := by
    rw [ENNReal.ofReal_prod_of_nonneg fun w _ => hc w, ← σ.prod_comp]
  have h4 : ∏ i, ENNReal.ofReal (b i ^ Fintype.card V) = (∏ i, ENNReal.ofReal (b i)) ^ Fintype.card V := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => ENNReal.ofReal_pow (hb i) _
  rw [h1, h2, h3, h4]
  ring

end GlobalTheory.LeviIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingWithDensity
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.HaarMul

theorem measurePreserving_withDensity {X : Type} [MeasurableSpace X] (μ : Measure X) {f : X → X}
    (hf : Measurable f) {ρ : X → ENNReal} (hρ : Measurable ρ) {c d : ENNReal} (hcd : d * c = 1)
    (hμ : μ.map f = c • μ) (hρf : ∀ x, ρ x = d * ρ (f x)) :
    MeasurePreserving f (μ.withDensity ρ) (μ.withDensity ρ) := by
  refine ⟨hf, ?_⟩
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs]

  have h1 : ∫⁻ x in f ⁻¹' s, ρ x ∂μ = ∫⁻ x, d * s.indicator ρ (f x) ∂μ := by
    rw [← lintegral_indicator (hf hs)]
    congr 1
    funext x
    by_cases hx : f x ∈ s
    · simp [Set.indicator_apply, hx, ← hρf x]
    · simp [Set.indicator_apply, hx]
  rw [h1, lintegral_const_mul d (f := fun x => s.indicator ρ (f x)) ((hρ.indicator hs).comp hf),
    ← lintegral_map (hρ.indicator hs) hf, hμ,
    lintegral_smul_measure, smul_eq_mul, ← mul_assoc, hcd, one_mul, lintegral_indicator hs]

theorem measurePreserving_mul_mul : ∀ (j : ℕ) (a b : Matrix (Fin j) (Fin j) ℂ), a.det ≠ 0 → b.det ≠ 0 →
    MeasurePreserving (fun (x : Fin j → Fin j → ℂ) (r s : Fin j) => (a * Matrix.of x * b) r s)
      (haarLoc j) (haarLoc j) := by
  intro j a b ha hb

  let L : (Fin j → Fin j → ℂ) →ₗ[ℝ] (Fin j → Fin j → ℂ) :=
    { toFun := fun x r s => (a * Matrix.of x * b) r s
      map_add' := fun x y => by
        have h : a * Matrix.of (x + y) * b = a * Matrix.of x * b + a * Matrix.of y * b := by
          rw [show Matrix.of (x + y) = Matrix.of x + Matrix.of y from rfl, Matrix.mul_add, Matrix.add_mul]
        funext r s
        exact congrFun (congrFun h r) s
      map_smul' := fun c x => by
        have h : a * Matrix.of (c • x) * b = c • (a * Matrix.of x * b) := by
          rw [show Matrix.of (c • x) = c • Matrix.of x from rfl, Matrix.mul_smul, Matrix.smul_mul]
        funext r s
        exact congrFun (congrFun h r) s }
  have hdet : LinearMap.det L = ‖a.det‖ ^ (2 * j) * ‖b.det‖ ^ (2 * j) :=
    GlobalTheory.TwoSidedJac.real_jacobians.1 j j a b L (fun T => rfl)
  have hA : ‖a.det‖ ≠ 0 := norm_ne_zero_iff.2 ha
  have hB : ‖b.det‖ ≠ 0 := norm_ne_zero_iff.2 hb
  have hD : 0 < ‖a.det‖ ^ (2 * j) * ‖b.det‖ ^ (2 * j) :=
    mul_pos (pow_pos (norm_pos_iff.2 ha) _) (pow_pos (norm_pos_iff.2 hb) _)
  have hcont : Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).det :=
    (continuous_id.matrix_det : Continuous fun A : Matrix (Fin j) (Fin j) ℂ => A.det)
  have hρ : Measurable fun x : Fin j → Fin j → ℂ => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j) :=
    ENNReal.measurable_ofReal.comp (((hcont.measurable.norm.pow_const 2).inv).pow_const j)

  haveI : (volume : Measure ℂ).IsAddHaarMeasure := inferInstance
  haveI : (volume : Measure (Fin j → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ : Fin j => (volume : Measure ℂ))
  haveI : (volume : Measure (Fin j → Fin j → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ : Fin j => (volume : Measure (Fin j → ℂ)))
  have hμ : (volume : Measure (Fin j → Fin j → ℂ)).map L =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; exact hD.ne')
  have hcd : ENNReal.ofReal (‖a.det‖ ^ (2 * j) * ‖b.det‖ ^ (2 * j)) * ENNReal.ofReal |(LinearMap.det L)⁻¹| = 1 := by
    rw [hdet, abs_of_pos (inv_pos.2 hD), ← ENNReal.ofReal_mul hD.le, mul_inv_cancel₀ hD.ne', ENNReal.ofReal_one]

  have hρf : ∀ x : Fin j → Fin j → ℂ, ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j) =
      ENNReal.ofReal (‖a.det‖ ^ (2 * j) * ‖b.det‖ ^ (2 * j)) *
        ENNReal.ofReal ((‖(Matrix.of (L x)).det‖ ^ 2)⁻¹ ^ j) := by
    intro x
    rw [← ENNReal.ofReal_mul hD.le]
    congr 1
    rw [show Matrix.of (L x) = a * Matrix.of x * b from rfl, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul]
    have hP : (‖a.det‖ ^ 2) ^ j * ((‖a.det‖ ^ 2) ^ j)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hA))
    have hQ : (‖b.det‖ ^ 2) ^ j * ((‖b.det‖ ^ 2) ^ j)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hB))
    rw [mul_pow, mul_pow, mul_inv, mul_inv, mul_pow, mul_pow, inv_pow (‖a.det‖ ^ 2), inv_pow (‖b.det‖ ^ 2),
      pow_mul, pow_mul]
    linear_combination (-((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j * (‖b.det‖ ^ 2) ^ j * ((‖b.det‖ ^ 2) ^ j)⁻¹)) * hP
      - (‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j * hQ
  unfold haarLoc
  exact measurePreserving_withDensity volume L.continuous_of_finiteDimensional.measurable hρ hcd hμ hρf

end GlobalTheory.HaarMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoVolumeSublevelDivPowStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_volume_sqrt_sublevel_div_pow_eq_volume_ball : ∀ (d : ℕ) (N : (Fin d → ℝ) → ℝ), ContinuousAt N 0 → N 0 = 0 → (∀ x, ∑ i, x i ^ 2 ≤ N x) → (∀ x, N x ≤ ∑ i, x i ^ 2 + N x ^ 2 / 4) → Filter.Tendsto (fun r : ℝ => volume {x : Fin d → ℝ | Real.sqrt (N x) ≤ r} / ENNReal.ofReal (r ^ d)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))) := by
  first | exact @GlobalTheory.tendsto_volume_sublevel_div_pow | exact GlobalTheory.tendsto_volume_sublevel_div_pow | (intros; apply GlobalTheory.tendsto_volume_sublevel_div_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusModulusUnipotentRadicalUnitaryGroupStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_modulus_unipotentRadical_unitaryGroup : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → ∀ (a : ℝ → UJ ε) (Hm : Matrix (Fin n) (Fin n) ℂ), inP ε Hm → (∀ s : ℝ, umat (a s) = NormedSpace.exp ((s : ℂ) • Hm)) → (∀ s, dOp (umat (a s)) ≤ |s|) → (∀ s, ∀ m ∈ NW ε W, a s * m * (a s)⁻¹ ∈ NW ε W) → ∃ κ : ℝ, |κ| ≤ 8 * n * rkR ε ∧ ∀ s, ν.map (fun m => a s * m * (a s)⁻¹) = ENNReal.ofReal (Real.exp (κ * s)) • ν := by
  first | exact @GlobalTheory.Dec.TorusModulus.torus_modulus | exact GlobalTheory.Dec.TorusModulus.torus_modulus | (intros; apply GlobalTheory.Dec.TorusModulus.torus_modulus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceCoordSqSumLeHilbertSchmidtUnitaryGroupStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceCoord_sq_sum_le_hilbertSchmidt_unitaryGroup : ∀ (n d : ℕ) (ε : Fin n → Bool) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ i, Formalism.REAL.inG ε (E i)) → ∀ g : Formalism.REAL.UJ ε, (uMat g - 1) - Formalism.REAL.Jm ε * (uMat g - 1)ᴴ * Formalism.REAL.Jm ε ∈ Submodule.span ℝ (Set.range E) → ∑ i, (((uMat g - 1) * (E i)ᴴ).trace).re ^ 2 ≤ Formalism.REAL.hs (uMat g - 1) ∧ Formalism.REAL.hs (uMat g - 1) ≤ ∑ i, (((uMat g - 1) * (E i)ᴴ).trace).re ^ 2 + Formalism.REAL.hs (uMat g - 1) ^ 2 / 4 := by
  first | exact @GlobalTheory.NilCov.sum_coord_sq_le_hs_and_hs_le | exact GlobalTheory.NilCov.sum_coord_sq_le_hs_and_hs_le | (intros; apply GlobalTheory.NilCov.sum_coord_sq_le_hs_and_hs_le <;> assumption)
end

