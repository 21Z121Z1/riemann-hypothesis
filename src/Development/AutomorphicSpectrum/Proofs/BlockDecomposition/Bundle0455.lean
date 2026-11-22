import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0662
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0375
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionTwistedKernel
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0438
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0415
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0439
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0002
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbol
import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.GlobalFields.LocalFieldAtPlace
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentGenericOfJacquetNuPair
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Zc Zc.Seg GlobalTheory.CompanionTheory.SegCoarse

namespace GlobalTheory.CompanionTheory.SegGenNu

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem card_after {n : ℕ} (a : Fin n) :
    ∑ b ∈ Finset.univ.filter (fun b => a < b), 1 = (Fin.rev a : ℕ) := by
  have h : Finset.univ.filter (fun b : Fin n => a < b) = Finset.Ioi a := by
    ext b; simp
  rw [h]
  simp [Fin.val_rev]
  omega

theorem isLSeg_fine (G : Segment k) (a : Fin G.len) :
    IsLSeg (topCut G (fun _ => 1) (fun _ => one_pos) a) (dec G a).rep := by
  have hc : (dec G a).IsCusp := G.isCusp_term _
  have e : topCut G (fun _ => 1) (fun _ => one_pos) a = Segment.single (dec G a) hc := by
    refine Segment.ext_first ?_ rfl
    show G.first.nu ((∑ b ∈ Finset.univ.filter (fun b => a < b), 1 : ℕ) : ℂ) = G.first.nu ((Fin.rev a : ℕ) : ℂ)
    rw [card_after]
  rw [e]
  exact (single_spec hc).2.1

theorem exists_cut (hJ : LSegJacquet k) {G G' : Segment k} {x : IrrGL k} (h : IsLSeg G x.rep)
    (h' : IsLSeg G' x.rep) :
    ∃ Γ : Fin G.len → Segment k, IsTopCut G' Γ ∧ ∀ a, IsLSeg (Γ a) (dec G a).rep := by
  have hd : ∑ a, (dec G a).1 = x.1 := (sum_dec G).trans h.deg_eq
  have hpos : ∀ a, 0 < (dec G a).1 := fun a => (G.isCusp_term _).1
  have h1 : jm (dec G) hd x.rep = 1 :=
    (hJ G x.rep h _ (dec G) hd hpos).1
      ⟨_, isTopCut_topCut G (fun _ => 1) (fun _ => one_pos) (by simp), isLSeg_fine G⟩
  by_contra hn
  have h0 := (hJ G' x.rep h' _ (dec G) hd hpos).2 hn
  rw [h1] at h0
  exact one_ne_zero h0

theorem card_le_len {G : Segment k} {s : ℕ} {Γ : Fin s → Segment k} (h : IsTopCut G Γ) : s ≤ G.len := by
  rw [← h.1]
  calc s = ∑ _ : Fin s, 1 := by simp
    _ ≤ ∑ a, (Γ a).len := Finset.sum_le_sum fun a _ => (Γ a).len_pos

theorem first_eq (hJ : LSegJacquet k) {G G' : Segment k} {x : IrrGL k} (h : IsLSeg G x.rep)
    (h' : IsLSeg G' x.rep) : G.first = G'.first := by
  obtain ⟨Γ, hΓ, hL⟩ := exists_cut hJ h h'
  obtain ⟨Γ', hΓ', -⟩ := exists_cut hJ h' h
  have hle := card_le_len hΓ
  have hle' := card_le_len hΓ'
  have hlen : G.len = G'.len := le_antisymm hle hle'
  have hpos := G.len_pos
  let l : Fin G.len := ⟨G.len - 1, by omega⟩
  have hl1 : (Γ l).len = 1 := by
    by_contra hne
    have h2 : 1 < (Γ l).len := by have := (Γ l).len_pos; omega
    have hlt : ∑ _ : Fin G.len, 1 < ∑ a, (Γ a).len :=
      Finset.sum_lt_sum (fun a _ => (Γ a).len_pos) ⟨l, Finset.mem_univ _, h2⟩
    rw [hΓ.1, ← hlen] at hlt
    simp at hlt
  have hb : below Γ l = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    have h3 : (l : ℕ) < b := Fin.lt_def.1 (Finset.mem_filter.1 hb).2
    have h4 := b.2
    have h5 : (l : ℕ) = G.len - 1 := rfl
    omega
  have hf : (Γ l).first = G'.first := by
    rw [hΓ.2 l, hb]
    simp
  have e : Γ l = Segment.single G'.first G'.isCusp_first := Segment.ext_first hf hl1
  have h6 : IsLSeg (Γ l) G'.first.rep := by
    rw [e]
    exact (single_spec _).2.1
  have h7 : dec G l = G.first := by
    have h8 : ((Fin.rev l : Fin G.len) : ℕ) = 0 := by
      simp only [Fin.val_rev, l]
      omega
    show G.first.nu (((Fin.rev l : Fin G.len) : ℕ) : ℂ) = G.first
    rw [h8]
    simp
  rw [← h7]
  exact eq_of_isLSeg (hL l) h6

theorem lSegGeneric_of_nuPair (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (_hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hJ : Zc.LSegJacquet k)
    (hP : GlobalTheory.BZSeg.NuPair k) : GlobalTheory.BZSeg.LSegGeneric k := by
  intro Δ N V _ _ π hπ
  by_contra hg
  obtain ⟨α, β, β', hd, hd', hα, hβ, hββ, h1, h2⟩ :=
    hP N V π hπ.hasSupport.isSmooth hπ.hasSupport.isIrreducible hg
  have hpos : ∀ a, 0 < (![α, β] a).1 := by
    intro a
    fin_cases a
    · exact hα
    · exact hβ
  have hpos' : ∀ a, 0 < (![β', α.nu 1] a).1 := by
    intro a
    fin_cases a
    · exact hββ ▸ hβ
    · exact hα
  have hcut : ∃ Γ : Fin 2 → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (![α, β] a).rep := by
    by_contra hn
    have h0 := (hJ Δ π hπ 2 ![α, β] hd hpos).2 hn
    rw [h0] at h1
    simp at h1
  have hcut' : ∃ Γ : Fin 2 → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (![β', α.nu 1] a).rep := by
    by_contra hn
    have h0 := (hJ Δ π hπ 2 ![β', α.nu 1] hd' hpos').2 hn
    rw [h0] at h2
    simp at h2
  obtain ⟨Γ, hΓ, hL⟩ := hcut
  obtain ⟨Γ', hΓ', hL'⟩ := hcut'
  have e1 : IsLSeg ((Γ 0).nu 1) (α.nu 1).rep := GlobalTheory.isLSeg_nu (hL 0) 1
  have e2 : IsLSeg (Γ' 1) (α.nu 1).rep := hL' 1
  have e3 : (Γ 0).first.nu 1 = (Γ' 1).first := first_eq hJ e1 e2
  have hb : below Γ' 1 = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    have h3 : (1 : Fin 2) < b := (Finset.mem_filter.1 hb).2
    exact absurd h3 (by omega)
  rw [hΓ.2 0, hΓ'.2 1, hb, IrrGL.nu_nu] at e3
  have e4 : Δ.first.nu (((below Γ 0 + 1 : ℕ)) : ℂ) = Δ.first.nu ((0 : ℕ) : ℂ) := by
    simpa using e3
  have e5 := (IrrGL.nu_natCast_inj Δ.isCusp_first.1).1 e4
  omega

end GlobalTheory.CompanionTheory.SegGenNu

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSubrepCompactInductionSpan
section
open GlobalTheory.PRep Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.PRep.CIndGlue

open GlobalTheory.CompanionTheory.PRep.CIndKer

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W]

theorem sum_apply (H : Subgroup G) (ρ : Representation ℂ H W) {ι : Type} (s : Finset ι)
    (F : ι → cIndSpace H ρ) (g : G) :
    (∑ i ∈ s, F i).1.1.1 g = ∑ i ∈ s, (F i).1.1.1 g := by
  let ev : cIndSpace H ρ →ₗ[ℂ] W :=
    (LinearMap.proj g) ∘ₗ (indSpace H ρ).subtype ∘ₗ (smoothPart (ind H ρ)).subtype ∘ₗ
      (cIndSpace H ρ).subtype
  exact map_sum ev _ _

theorem exists_small_cut (H : Subgroup G) (ρ : Representation ℂ H W)
    (I : Submodule ℂ (cIndSpace H ρ)) (hI : ∀ (g : G) (B : cIndSpace H ρ), B ∈ I → cInd H ρ g B ∈ I)
    (hloc : ∀ (v : W) (O : Set G), O ∈ nhds (1 : G) → ∃ K : Subgroup G, IsOpen (K : Set G) ∧
      (K : Set G) ⊆ O ∧ ∃ B ∈ I, (∀ (a : H), ∀ x ∈ K, B.1.1.1 ((a : G) * x) = ρ a v) ∧
        ∀ g, (¬ ∃ a : H, ∃ x ∈ K, g = (a : G) * x) → B.1.1.1 g = 0)
    (K₁ : Subgroup G) (hK₁o : IsOpen (K₁ : Set G)) (y : cIndSpace H ρ)
    (hy : ∀ g, ∀ x ∈ K₁, y.1.1.1 (g * x) = y.1.1.1 g) (c : G) :
    ∃ K' : Subgroup G, IsOpen (K' : Set G) ∧ K' ≤ K₁ ∧ ∃ B ∈ I,
      ∀ g, B.1.1.1 g = (dc H K' c).indicator y.1.1.1 g := by
  classical
  have hO : (fun x : G => c⁻¹ * x * c) ⁻¹' (K₁ : Set G) ∈ 𝓝 (1 : G) :=
    (hK₁o.preimage (by fun_prop)).mem_nhds (by simp [one_mem])
  obtain ⟨K, hKo, hKO, B₀, hB₀, hB1, hB0⟩ := hloc (y.1.1.1 c) _ hO
  let K' : Subgroup G := K.comap (MulAut.conj c).toMonoidHom
  have hmem : ∀ x, x ∈ K' ↔ c * x * c⁻¹ ∈ K := fun x => Iff.rfl
  have hK'o : IsOpen (K' : Set G) := by
    have : Continuous fun x : G => c * x * c⁻¹ := by fun_prop
    exact hKo.preimage this
  have hle : K' ≤ K₁ := by
    intro x hx
    have h := hKO ((hmem x).1 hx)
    have e : c⁻¹ * (c * x * c⁻¹) * c = x := by group
    simpa [e] using h
  refine ⟨K', hK'o, hle, cInd H ρ c⁻¹ B₀, hI _ _ hB₀, fun g => ?_⟩
  have e1 : (cInd H ρ c⁻¹ B₀).1.1.1 g = B₀.1.1.1 (g * c⁻¹) := rfl
  rw [e1]
  by_cases hg : g ∈ dc H K' c
  · rw [Set.indicator_of_mem hg]
    obtain ⟨b, k, hk, rfl⟩ := hg
    have e2 : (b : G) * c * k * c⁻¹ = (b : G) * (c * k * c⁻¹) := by group
    rw [e2, hB1 b _ ((hmem k).1 hk), mul_assoc, y.1.1.2 b, hy c k (hle hk)]
  · rw [Set.indicator_of_notMem hg]
    apply hB0
    rintro ⟨a, x, hx, e⟩
    apply hg
    refine ⟨a, c⁻¹ * x * c, (hmem _).2 ?_, ?_⟩
    · have e3 : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
      rw [e3]
      exact hx
    · have e4 : g = (g * c⁻¹) * c := by group
      rw [e4, e]
      group

theorem average_cut (H : Subgroup G) (ρ : Representation ℂ H W)
    (I : Submodule ℂ (cIndSpace H ρ)) (hI : ∀ (g : G) (B : cIndSpace H ρ), B ∈ I → cInd H ρ g B ∈ I)
    (K₁ : Subgroup G) (hK₁c : IsCompact (K₁ : Set G)) (y : cIndSpace H ρ)
    (hy : ∀ g, ∀ x ∈ K₁, y.1.1.1 (g * x) = y.1.1.1 g) (c : G)
    (K' : Subgroup G) (hK'o : IsOpen (K' : Set G)) (hle : K' ≤ K₁)
    (B : cIndSpace H ρ) (hBI : B ∈ I) (hB : ∀ g, B.1.1.1 g = (dc H K' c).indicator y.1.1.1 g) :
    ∃ z ∈ I, ∀ g, z.1.1.1 g = (dc H K₁ c).indicator y.1.1.1 g := by
  classical
  haveI : CompactSpace K₁ := isCompact_iff_compactSpace.1 hK₁c
  let L : Subgroup K₁ := K'.subgroupOf K₁
  have hLo : IsOpen (L : Set K₁) := hK'o.preimage continuous_subtype_val
  haveI : Finite (K₁ ⧸ L) := Subgroup.quotient_finite_of_isOpen _ hLo
  haveI := Fintype.ofFinite (K₁ ⧸ L)
  let φ : G → ℕ := fun g => ∑ q : K₁ ⧸ L, if g * ((q.out : K₁) : G) ∈ dc H K' c then 1 else 0
  let Sg : cIndSpace H ρ := ∑ q : K₁ ⧸ L, cInd H ρ ((q.out : K₁) : G) B
  have hSg : Sg ∈ I := Submodule.sum_mem _ fun q _ => hI _ _ hBI
  have hval : ∀ g, Sg.1.1.1 g = (φ g : ℂ) • y.1.1.1 g := by
    intro g
    have e0 : Sg.1.1.1 g = ∑ q : K₁ ⧸ L, (cInd H ρ ((q.out : K₁) : G) B).1.1.1 g :=
      sum_apply H ρ _ _ g
    rw [e0]
    simp only [φ]
    push_cast
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun q _ => ?_
    have e1 : (cInd H ρ ((q.out : K₁) : G) B).1.1.1 g = B.1.1.1 (g * ((q.out : K₁) : G)) := rfl
    rw [e1, hB]
    by_cases h : g * ((q.out : K₁) : G) ∈ dc H K' c
    · rw [Set.indicator_of_mem h, hy g _ q.out.2, if_pos h, one_smul]
    · rw [Set.indicator_of_notMem h, if_neg h, zero_smul]
  have hleft : ∀ (b : H) g, φ ((b : G) * g) = φ g := by
    intro b g
    simp only [φ, mul_assoc, dc_left H K' c (b : G) b.2]
  have hright : ∀ κ ∈ K₁, ∀ g, φ (g * κ) = φ g := by
    intro κ hκ g
    let κ' : K₁ := ⟨κ, hκ⟩
    have key : ∀ q : K₁ ⧸ L, g * κ * ((q.out : K₁) : G) ∈ dc H K' c ↔
        g * (((κ' • q).out : K₁) : G) ∈ dc H K' c := by
      intro q
      have e : ((κ' * q.out : K₁) : K₁ ⧸ L) = κ' • q := by
        conv_rhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have e2 : (κ' • q).out⁻¹ * (κ' * q.out) ∈ L := by
        apply QuotientGroup.eq.1
        rw [e, QuotientGroup.out_eq']
      have e3 : ((((κ' • q).out⁻¹ * (κ' * q.out) : K₁)) : G) ∈ K' := e2
      have e4 : g * κ * ((q.out : K₁) : G) = g * (((κ' • q).out : K₁) : G) *
          ((((κ' • q).out⁻¹ * (κ' * q.out) : K₁)) : G) := by
        push_cast
        show g * κ * ((q.out : K₁) : G) = g * (((κ' • q).out : K₁) : G) *
          ((((κ' • q).out : K₁) : G)⁻¹ * (κ * ((q.out : K₁) : G)))
        group
      rw [e4]
      exact dc_right H K' c _ e3 _
    simp only [φ, mul_assoc] at key ⊢
    simp only [← mul_assoc] at key ⊢
    simp only [key]
    exact Equiv.sum_comp (MulAction.toPerm κ')
      (fun q : K₁ ⧸ L => if g * ((q.out : K₁) : G) ∈ dc H K' c then 1 else 0)
  have hφc : φ c ≠ 0 := by
    let q₀ : K₁ ⧸ L := ((1 : K₁) : K₁ ⧸ L)
    have h1 : (q₀.out : K₁)⁻¹ * 1 ∈ L := by
      apply QuotientGroup.eq.1
      rw [QuotientGroup.out_eq']
    have h2 : (q₀.out : K₁) ∈ L := by
      have := inv_mem h1
      simpa using this
    have h3 : ((q₀.out : K₁) : G) ∈ K' := h2
    have h4 : c * ((q₀.out : K₁) : G) ∈ dc H K' c := ⟨1, _, h3, by simp⟩
    have h5 : (if c * ((q₀.out : K₁) : G) ∈ dc H K' c then 1 else 0) ≤ φ c :=
      Finset.single_le_sum (f := fun q : K₁ ⧸ L =>
        if c * ((q.out : K₁) : G) ∈ dc H K' c then 1 else 0) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ q₀)
    rw [if_pos h4] at h5
    omega
  have hoff : ∀ g, g ∉ dc H K₁ c → φ g = 0 := by
    intro g hg
    refine Finset.sum_eq_zero fun q _ => if_neg fun h => hg ?_
    obtain ⟨b, k, hk, e⟩ := h
    exact (dc_right H K₁ c _ q.out.2 g).1 ⟨b, k, hle hk, e⟩
  have hc0 : (φ c : ℂ) ≠ 0 := by exact_mod_cast hφc
  refine ⟨(φ c : ℂ)⁻¹ • Sg, Submodule.smul_mem _ _ hSg, fun g => ?_⟩
  have e : ((φ c : ℂ)⁻¹ • Sg).1.1.1 g = (φ c : ℂ)⁻¹ • Sg.1.1.1 g := rfl
  rw [e, hval]
  by_cases hg : g ∈ dc H K₁ c
  · rw [Set.indicator_of_mem hg]
    obtain ⟨b, k, hk, rfl⟩ := hg
    rw [mul_assoc, hleft, hright k hk, smul_smul, inv_mul_cancel₀ hc0, one_smul,
      y.1.1.2 b, hy c k hk]
  · rw [Set.indicator_of_notMem hg, hoff g hg]
    simp

theorem eq_top_of_bumps : ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (ρ : Representation ℂ H W)
    (hbasis : ∀ O : Set G, O ∈ nhds (1 : G) → ∃ K : Subgroup G, IsOpen (K : Set G) ∧
      IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (I : Submodule ℂ (cIndSpace H ρ)) (hI : ∀ (g : G) (B : cIndSpace H ρ), B ∈ I → cInd H ρ g B ∈ I)
    (hloc : ∀ (v : W) (O : Set G), O ∈ nhds (1 : G) → ∃ K : Subgroup G, IsOpen (K : Set G) ∧
      (K : Set G) ⊆ O ∧
      ∃ B ∈ I, (∀ (a : H), ∀ x ∈ K, B.1.1.1 ((a : G) * x) = ρ a v) ∧
        ∀ g, (¬ ∃ a : H, ∃ x ∈ K, g = (a : G) * x) → B.1.1.1 g = 0)
    (y : cIndSpace H ρ), y ∈ I := by
  intro G W _ _ _ _ _ H ρ hbasis I hI hloc y
  classical
  have hyo : IsOpen {g : G | ind H ρ g y.1.1 = y.1.1} := y.1.2
  obtain ⟨K₁, hK₁o, hK₁c, hK₁U⟩ := hbasis _ (hyo.mem_nhds (by simp))
  have hinv : ∀ g, ∀ x ∈ K₁, y.1.1.1 (g * x) = y.1.1.1 g := by
    intro g x hx
    have h : ind H ρ x y.1.1 = y.1.1 := hK₁U hx
    exact congrArg (fun v : indSpace H ρ => v.1 g) h
  have hdc : ∀ c : G, ∃ z ∈ I, ∀ g, z.1.1.1 g = (dc H K₁ c).indicator y.1.1.1 g := by
    intro c
    obtain ⟨K', hK'o, hle, B, hBI, hB⟩ := exists_small_cut H ρ I hI hloc K₁ hK₁o y hinv c
    exact average_cut H ρ I hI K₁ hK₁c y hinv c K' hK'o hle B hBI hB
  have key : ∀ t : Finset G, ∃ S : Set G, (∀ h ∈ H, ∀ g, h * g ∈ S ↔ g ∈ S) ∧
      (∀ k ∈ K₁, ∀ g, g * k ∈ S ↔ g ∈ S) ∧ (∀ c ∈ t, c ∈ S) ∧
      ∃ z ∈ I, ∀ g, z.1.1.1 g = S.indicator y.1.1.1 g := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      exact ⟨∅, by simp, by simp, by simp, 0, Submodule.zero_mem _, fun g => by simp⟩
    | insert c t _ ih =>
      obtain ⟨S, hl, hr, hcov, z, hz, ez⟩ := ih
      by_cases hcS : c ∈ S
      · refine ⟨S, hl, hr, fun c' hc' => ?_, z, hz, ez⟩
        rcases Finset.mem_insert.1 hc' with rfl | hc'
        · exact hcS
        · exact hcov c' hc'
      · obtain ⟨z', hz', ez'⟩ := hdc c
        have hdisj : ∀ g, g ∈ dc H K₁ c → g ∉ S := by
          rintro g ⟨b, k, hk, rfl⟩ hg
          rw [mul_assoc, hl _ b.2, hr k hk] at hg
          exact hcS hg
        refine ⟨S ∪ dc H K₁ c, fun h hh g => ?_, fun k hk g => ?_, fun c' hc' => ?_, z + z',
          Submodule.add_mem _ hz hz', fun g => ?_⟩
        · simp only [Set.mem_union, hl h hh g, dc_left H K₁ c h hh g]
        · simp only [Set.mem_union, hr k hk g, dc_right H K₁ c k hk g]
        · rcases Finset.mem_insert.1 hc' with rfl | hc'
          · exact Or.inr ⟨1, 1, one_mem _, by simp⟩
          · exact Or.inl (hcov c' hc')
        · have e : (z + z').1.1.1 g = z.1.1.1 g + z'.1.1.1 g := rfl
          rw [e, ez, ez']
          by_cases h2 : g ∈ dc H K₁ c
          · have h1 := hdisj g h2
            simp [Set.indicator, h1, h2]
          · by_cases h1 : g ∈ S <;> simp [Set.indicator, h1, h2]
  obtain ⟨C, hC, hsupp⟩ := y.2
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun c => (fun x => c * x) '' (K₁ : Set G))
    (fun c _ => by
      have : (fun x => c⁻¹ * x) ⁻¹' (K₁ : Set G) ∈ 𝓝 c :=
        (hK₁o.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [one_mem])
      filter_upwards [this] with x hx
      exact ⟨c⁻¹ * x, hx, by group⟩)
  obtain ⟨S, hl, hr, hcov, z, hz, ez⟩ := key t
  have hyz : y = z := by
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun g => ?_)))
    show y.1.1.1 g = z.1.1.1 g
    rw [ez]
    by_cases h0 : y.1.1.1 g = 0
    · rw [h0]
      by_cases hg : g ∈ S
      · rw [Set.indicator_of_mem hg, h0]
      · rw [Set.indicator_of_notMem hg]
    · obtain ⟨a, ha, c', hc', e⟩ := hsupp g h0
      obtain ⟨c, hc, hcc⟩ := Set.mem_iUnion₂.1 (ht hc')
      obtain ⟨x, hx, rfl⟩ := hcc
      have hg : g ∈ S := by
        rw [e]
        exact (hl a ha _).2 ((hr x hx c).2 (hcov c hc))
      rw [Set.indicator_of_mem hg]
  rw [hyz]
  exact hz

end GlobalTheory.CompanionTheory.PRep.CIndGlue
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpectralTraceOfModelAlgebra
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SpecModel

theorem twTr_unit (hL : LocAlg) {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E}
    (σ : SmIrr (UL n w)) (hlev : IsLevel (MonoidHom.id _) (KL n w) (KL n w))
    (h1 : Module.finrank ℂ (fixed σ.ρ (KL n w)) = 1) {f : UL n w → ℂ} (hf : IsHecke (KL n w) f) :
    twTr σ.ρ (KL n w) (KL n w) ((KL n w : Set (UL n w)).indicator 1) LinearMap.id = 1 := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := hL E n w σ _ hlev f f hf hf
  obtain ⟨h8, -, -, -, -, -, -, h9⟩ := hL E n w σ _ hlev _ _ h7 h7
  have e : ((KL n w : Set (UL n w)).indicator fun _ => (((KL n w).relIndex (KL n w) : ℕ) : ℂ)) =
      (KL n w : Set (UL n w)).indicator 1 := by
    rw [Subgroup.relIndex_self]
    congr 1
    funext _
    simp
  rw [e] at h8 h9
  have : FiniteDimensional ℂ (fixed σ.ρ (KL n w)) := Module.finite_of_finrank_pos (by omega)
  rw [h8, h9, LinearMap.trace_one, h1]
  simp

theorem finprod_split {P : Type} (S : Set P) (B : Finset P) (hB : (↑B : Set P) ⊆ S) (F G : P → ℂ)
    (T : {w // w ∈ B} → ℂ) (hT : ∀ w, T w = F w.1) (hG : ∀ w ∈ S, w ∉ B → F w = G w)
    (hfin : ((S \ ↑B) ∩ Function.mulSupport F).Finite) :
    ∏ᶠ w ∈ S, F w = (∏ᶠ w ∈ S \ ↑B, G w) * ∏ w, T w := by
  have hon : ((↑B : Set P) ∩ Function.mulSupport F).Finite := B.finite_toSet.inter_of_left _
  have hB' : ∏ᶠ w ∈ (↑B : Set P), F w = ∏ w, T w := by
    rw [finprod_mem_coe_finset, ← Finset.prod_coe_sort]
    exact Finset.prod_congr rfl fun w _ => (hT w).symm
  have hC : ∏ᶠ w ∈ S \ ↑B, F w = ∏ᶠ w ∈ S \ ↑B, G w :=
    finprod_mem_congr rfl fun w hw => hG w hw.1 hw.2
  have hS : ↑B ∪ (S \ ↑B) = S := Set.union_sdiff_cancel hB
  rw [← hS, finprod_mem_union' Set.disjoint_sdiff_right hon hfin, hS, hB', hC, mul_comm]

theorem specTrace : UModel → LocAlg → SpecTrace := by
  intro hU hL E _ _ _ n S B hB K' hK' hKB ι _ σ hfd hone g
  have : ∀ (i : ι) (w : {w // w ∈ B}), FiniteDimensional ℂ (fixed (σ i w.1).ρ (K' w.1)) :=
    fun i w => hfd i w.1 (hB w.2)
  obtain ⟨d, blk, u, h1, h2, h3⟩ := hU ι {w // w ∈ B} (fun i w => ↥(fixed (σ i w.1).ρ (K' w.1)))
    (fun i w => locOp (σ i w.1) (K' w.1) (g w.1))
  refine ⟨d, blk, u, h1, ?_, ?_⟩
  · intro k f hf hloc
    rw [h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hoff : ((S \ ↑B) ∩ Function.mulSupport
        fun w => twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id).Finite := by
      have hev := hK'.2.and hf.2
      rw [Filter.eventually_cofinite] at hev
      refine hev.subset ?_
      rintro w ⟨⟨hwS, hwB⟩, hne⟩ ⟨e1, e2⟩
      apply hne
      have hlev := hK'.1 w
      have hH := hf.1 w
      rw [e1] at hlev hH
      show twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id = 1
      rw [e1, e2]
      exact twTr_unit hL (σ i w) hlev (hone i w hwS hwB) hH
    refine finprod_split S B hB (fun w => twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id)
      (fun w => twTr (σ i w).ρ (KL n w) (KL n w) (f w) LinearMap.id)
      (fun w => LinearMap.trace ℂ _ (locOp (σ i w.1) (K' w.1) (g w.1) ^ k)) ?_ ?_ hoff
    · intro w
      show LinearMap.trace ℂ _ (locOp (σ i w.1) (K' w.1) (g w.1) ^ k) =
        twTr (σ i w.1).ρ (KL n w.1) (K' w.1) (f w.1) LinearMap.id
      rw [← hloc i w.1 w.2]
      exact (hL E n w.1 (σ i w.1) (K' w.1) (hK'.1 w.1) (f w.1) (f w.1) (hf.1 w.1) (hf.1 w.1)).1.symm
    · intro w hwS hwB
      show twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id =
        twTr (σ i w).ρ (KL n w) (KL n w) (f w) LinearMap.id
      rw [hKB w hwS hwB]
  · intro i₀ hi
    exact h3 i₀ fun w => hi w.1 w.2

end GlobalTheory.CompanionTheory.SpecModel

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundConstantTermStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_bound_constant_term : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type) (f : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) (r D : ℕ) (κ' κ : ℝ) (p : ι → ℂ[X]),
  0 < r → r < n → UFam f → UBnd f m → κ' < κ →
  (∀ i, (p i).Monic ∧ (p i).natDegree ≤ D ∧ An.Kill r (f i) (p i) ∧ ∀ z, (p i).IsRoot z → ‖z‖ ≤ Real.exp κ') →
  UBnd (fun i => An.ctn r (f i)) (Function.update m r κ) := by
  first | exact @GlobalTheory.CompanionTheory.Conc.ubnd_ctn_step | exact GlobalTheory.CompanionTheory.Conc.ubnd_ctn_step | (intros; apply GlobalTheory.CompanionTheory.Conc.ubnd_ctn_step <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerOrderEqOneStatement
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_order_eq_one : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : 𝓞 F), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ord (algebraMap F (v.adicCompletion F) (ϖ : F)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Completion.ord_algebraMap_eq_one | exact GlobalTheory.CompanionTheory.Completion.ord_algebraMap_eq_one | (intros; apply GlobalTheory.CompanionTheory.Completion.ord_algebraMap_eq_one <;> assumption)
end

