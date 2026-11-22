import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfDict
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0010

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfPhi
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O} (Bs : FramepfBas W T)

theorem framepf_nBasis : ∃ β : Module.Basis (Fin Bs.r) (LetA O n) ↥(W.N T),
    ∀ k, (β k : W.DD T) = Bs.b k := by
  let b' : Fin Bs.r → ↥(W.N T) := fun k => ⟨Bs.b k, (Bs.mem k).1⟩
  have hli : LinearIndependent (LetA O n) b' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : (0 : W.DD T) = ∑ k, g k • Bs.b k := by
      have := congrArg (fun z : ↥(W.N T) => (z : W.DD T)) hg
      simpa [b'] using this.symm
    obtain ⟨a, -, hu⟩ := Bs.uniq 0 (W.N T).zero_mem
    have e := (hu g h1).trans (hu 0 (by simp)).symm
    intro k
    exact congrFun e k
  have hsp : ⊤ ≤ Submodule.span (LetA O n) (Set.range b') := by
    intro x _
    obtain ⟨a, ha, -⟩ := Bs.uniq x x.2
    have : x = ∑ k, a k • b' k := Subtype.ext (by simpa [b'] using ha)
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun k => by rw [Module.Basis.mk_apply]⟩

theorem framepf_ddBasis (hT : IsCrys PD T.ρ) :
    ∃ β : Module.Basis (Fin Bs.r) W.EE (W.DD T), ∀ k, β k = Bs.b k := by
  obtain ⟨β, hβ⟩ := framepf_nBasis Bs
  refine ⟨(Algebra.TensorProduct.basis W.EE β).map (W.N_base T hT).equiv, fun k => ?_⟩
  rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, IsBaseChange.equiv_tmul, one_smul,
    Submodule.subtype_apply, hβ]

theorem framepf_φpull_coord {y : W.DD T}
    (hy : y ∈ Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T)))) :
    ∃ a : Fin Bs.r → LetA O n, y = ∑ k, a k • W.φD T (Bs.b k) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨a, ha, -⟩ := Bs.uniq z hz
    refine ⟨fun k => W.φA (a k), ?_⟩
    rw [ha, map_sum]
    exact Finset.sum_congr rfl fun k _ => Formalism.MainNotions.LiftingTheory.wmap_φD_smul W T _ _
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨a', rfl⟩ := hy
    exact ⟨a + a', by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul s x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨fun k => s * a k, by simp [Finset.smul_sum, mul_smul]⟩

theorem framepf_phiBasis (hT : IsCrys PD T.ρ) :
    ∃ β : Module.Basis (Fin Bs.r) W.EE (W.DD T), ∀ k, β k = W.φD T (Bs.b k) := by
  obtain ⟨β, hβ⟩ := framepf_ddBasis Bs hT
  have hli : LinearIndependent W.EE fun k => W.φD T (Bs.b k) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have := Formalism.MainNotions.LiftingTheory.phii_basis W T hT β g (by simpa only [hβ] using hg)
    exact congrFun this k
  have hN : ∀ m ∈ W.N T, m ∈ Submodule.span W.EE (Set.range fun k => W.φD T (Bs.b k)) := by
    intro m hm
    obtain ⟨k, hk⟩ := W.N_φinv T m hm
    obtain ⟨a, ha⟩ := framepf_φpull_coord Bs hk
    have h2 : W.Q ^ k • m ∈ Submodule.span W.EE (Set.range fun k => W.φD T (Bs.b k)) := by
      have e : W.Q ^ k • m = ∑ j, a j • W.φD T (Bs.b j) := ha
      rw [e]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [← algebraMap_smul W.EE]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    rw [← algebraMap_smul W.EE, map_pow] at h2
    obtain ⟨u, hu⟩ := (Formalism.MainNotions.LiftingTheory.liftb_Q_unit W).pow k
    rw [← hu] at h2
    have h3 := Submodule.smul_mem _ ((u⁻¹ : W.EEˣ) : W.EE) h2
    rwa [smul_smul, Units.inv_mul, one_smul] at h3
  have hsp : ⊤ ≤ Submodule.span W.EE (Set.range fun k => W.φD T (Bs.b k)) := by
    intro y _
    exact (W.N_base T hT).inductionOn y
      (fun y => y ∈ Submodule.span W.EE (Set.range fun k => W.φD T (Bs.b k)))
      (Submodule.zero_mem _) (fun m => hN m m.2) (fun e y hy => Submodule.smul_mem _ e hy)
      (fun y₁ y₂ h₁ h₂ => Submodule.add_mem _ h₁ h₂)
  exact ⟨Module.Basis.mk hli hsp, fun k => by rw [Module.Basis.mk_apply]⟩

theorem framepf_phi_uniq (hT : IsCrys PD T.ρ) {a a' : Fin Bs.r → LetA O n}
    (h : ∑ k, a k • W.φD T (Bs.b k) = ∑ k, a' k • W.φD T (Bs.b k)) : a = a' := by
  obtain ⟨β, hβ⟩ := framepf_phiBasis Bs hT
  have h0 : ∑ k, algebraMap (LetA O n) W.EE (a k - a' k) • β k = 0 := by
    simp only [algebraMap_smul, hβ, sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have h1 := Fintype.linearIndependent_iff.1 β.linearIndependent _ h0
  funext k
  exact sub_eq_zero.1 (W.EE_inj ((h1 k).trans (map_zero _).symm))

theorem framepf_phi_coordΔ (hT : IsCrys PD T.ρ) (c : ZMod n) {y : W.DD T}
    (hy : y ∈ Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))))
    (hΔ : ∀ δ ∈ W.DelF, W.γD T δ y = y) (hc : (letE c : LetA O n) • y = y) :
    ∃ a : Fin Bs.r → LetA O n, (∀ k, a k ∈ W.AΔ) ∧ (∀ k, (letE c : LetA O n) * a k = a k) ∧
      y = ∑ k, a k • W.φD T (Bs.b k) := by
  obtain ⟨a, ha⟩ := framepf_φpull_coord Bs hy
  refine ⟨a, fun k δ hδ => ?_, fun k => ?_, ha⟩
  · have e : ∑ j, W.γA δ (a j) • W.φD T (Bs.b j) = ∑ j, a j • W.φD T (Bs.b j) := by
      rw [← ha, ← hΔ δ hδ]
      conv_rhs => rw [ha, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Formalism.MainNotions.LiftingTheory.wmap_γD_smul, ← W.φγ_comm, (Bs.mem j).2 δ hδ]
    exact congrFun (framepf_phi_uniq Bs hT e) k
  · have e : ∑ j, ((letE c : LetA O n) * a j) • W.φD T (Bs.b j) = ∑ j, a j • W.φD T (Bs.b j) := by
      rw [← ha, ← hc]
      conv_rhs => rw [ha, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => mul_smul _ _ _
    exact congrFun (framepf_phi_uniq Bs hT e) k

theorem framepf_φspan_le (i : ZMod n) : Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T i) ≤
    Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))) :=
  Submodule.span_mono (Set.image_mono fun _ hx => Formalism.MainNotions.LiftingTheory.wmap_Nl_le W T i hx)

theorem framepf_Pc_coord (hT : IsCrys PD T.ρ) (c : ZMod n) (y : W.DD T) (hy : y ∈ PcS W T c) :
    ∃ a : Fin Bs.r → LetA O n, (∀ k, a k ∈ W.AΔ) ∧ (∀ k, (letE c : LetA O n) * a k = a k) ∧
      y = ∑ k, a k • W.φD T (Bs.b k) := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hy
  exact framepf_phi_coordΔ Bs hT c (framepf_φspan_le (c - 1) h1) ((mem_DelS W T y).1 h2)
    ((mem_letS W T c y).1 h3)

theorem framepf_mem_Pc (c : ZMod n) (a : Fin Bs.r → LetA O n) (ha : ∀ k, a k ∈ W.AΔ)
    (hc : ∀ k, (letE c : LetA O n) * a k = a k) : ∑ k, a k • W.φD T (Bs.b k) ∈ PcS W T c := by
  refine Submodule.sum_mem _ fun k _ => ⟨⟨?_, ?_⟩, ?_⟩
  · show a k • W.φD T (Bs.b k) ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))
    rw [← hc k, mul_comm, mul_smul, ← φD_letE]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨Bs.b k, (Bs.mem k).1, rfl⟩, rfl⟩)
  · show a k • W.φD T (Bs.b k) ∈ DelS W T
    rw [mem_DelS]
    intro δ hδ
    rw [Formalism.MainNotions.LiftingTheory.wmap_γD_smul, ← W.φγ_comm, (Bs.mem k).2 δ hδ, ha k δ hδ]
  · show a k • W.φD T (Bs.b k) ∈ letS W T c
    rw [mem_letS, smul_smul, hc k]

end Local

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPfC
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.MQ

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem unit_comp (w : (LetA O n)ˣ) (i : ZMod n) :
    (w : LetA O n) i * ((w⁻¹ : (LetA O n)ˣ) : LetA O n) i = 1 := by
  exact congrFun (Units.mul_inv w) i

theorem π_at (s' : ℕ) (π' : LetA O n) (w₁ : (LetA O n)ˣ) (hπ : π' = w₁ * (letπ : LetA O n) ^ s') (i : ZMod n) :
    π' i = (w₁ : LetA O n) i * PowerSeries.X ^ s' := by
  rw [hπ]
  rfl

theorem hlet_of [IsDomain O] (s' : ℕ) (hs : 1 ≤ s') (π' : LetA O n) (w₁ : (LetA O n)ˣ)
    (hπ : π' = w₁ * (letπ : LetA O n) ^ s') (hπΔ : π' ∈ W.AΔ) (hπu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (c : ZMod n) :
    ∀ a : O, a ≠ 0 → ∀ u : W.EE,
      (∃ g ∈ W.AΔ, algebraMap (LetA O n) W.EE π' * u = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g)) →
      (∃ g ∈ W.AΔ, a • u = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g)) →
      ∃ g ∈ W.AΔ, u = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g) := by
  rintro a ha u ⟨g, hg, hgu⟩ ⟨h, hh, hhu⟩
  have hA : π' * ((letE c : LetA O n) * h) = algebraMap O (LetA O n) a * ((letE c : LetA O n) * g) := by
    apply W.EE_inj
    calc algebraMap (LetA O n) W.EE (π' * ((letE c : LetA O n) * h))
        = algebraMap (LetA O n) W.EE π' * algebraMap (LetA O n) W.EE ((letE c : LetA O n) * h) := map_mul _ _ _
      _ = algebraMap (LetA O n) W.EE π' * (a • u) := by rw [hhu]
      _ = a • (algebraMap (LetA O n) W.EE π' * u) := by rw [mul_smul_comm]
      _ = a • algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g) := by rw [hgu]
      _ = algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) a * ((letE c : LetA O n) * g)) := by
        rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O (LetA O n) W.EE, ← map_mul]
  have hc : π' c * h c = a • g c := by
    have := congrFun hA c
    rw [Algebra.smul_def]
    simpa [letE] using this
  have hdvd : PowerSeries.X ^ s' ∣ g c := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    have h1 := congrArg (PowerSeries.coeff m) hc
    rw [π_at s' π' w₁ hπ c, mul_comm ((w₁ : LetA O n) c), mul_assoc, PowerSeries.coeff_X_pow_mul',
      if_neg (by omega), map_smul, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left ha
  obtain ⟨G', hG'⟩ := hdvd
  set g' : LetA O n := (letE c : LetA O n) * (fun _ => ((w₁⁻¹ : (LetA O n)ˣ) : LetA O n) c * G') with hg'
  have hπg' : π' * g' = (letE c : LetA O n) * g := by
    funext i
    by_cases hi : i = c
    · subst hi
      simp only [Pi.mul_apply, hg', letE, Pi.single_eq_same, one_mul]
      rw [π_at s' π' w₁ hπ i, hG']
      linear_combination (PowerSeries.X ^ s' * G') * unit_comp w₁ i
    · simp [hg', letE, Pi.single_apply, hi]
  have hcancel : ∀ x y : LetA O n, π' * x = π' * y → x = y := by
    intro x y hxy
    funext i
    have hxi := congrFun hxy i
    simp only [Pi.mul_apply] at hxi
    rw [π_at s' π' w₁ hπ i] at hxi
    have hne : (w₁ : LetA O n) i * PowerSeries.X ^ s' ≠ 0 := by
      have hw : (w₁ : LetA O n) i ≠ 0 := by
        intro h0
        have := unit_comp w₁ i
        rw [h0, zero_mul] at this
        exact zero_ne_one this
      exact mul_ne_zero hw (pow_ne_zero _ PowerSeries.X_ne_zero)
    exact mul_left_cancel₀ hne hxi
  have hπΔ' : ∀ δ ∈ W.DelF, W.γA δ π' = π' := hπΔ
  have hm : (letE c : LetA O n) * g ∈ W.AΔ := mul_mem (letE_mem W c) hg
  have hm' : ∀ δ ∈ W.DelF, W.γA δ ((letE c : LetA O n) * g) = (letE c : LetA O n) * g := hm
  have hg'Δ : g' ∈ W.AΔ := by
    show ∀ δ ∈ W.DelF, W.γA δ g' = g'
    intro δ hδ
    apply hcancel
    calc π' * W.γA δ g' = W.γA δ π' * W.γA δ g' := by rw [hπΔ' δ hδ]
      _ = W.γA δ (π' * g') := (map_mul _ _ _).symm
      _ = W.γA δ ((letE c : LetA O n) * g) := by rw [hπg']
      _ = (letE c : LetA O n) * g := hm' δ hδ
      _ = π' * g' := hπg'.symm
  refine ⟨g', hg'Δ, ?_⟩
  have hle : (letE c : LetA O n) * g' = g' := by rw [hg', ← mul_assoc, letE_mul_self']
  rw [hle]
  exact hπu.mul_left_cancel (by rw [hgu, ← hπg', map_mul])

theorem q_unit (hp : PD.p.Prime) : IsUnit (algebraMap (LetA O n) W.EE W.q) := by
  exact Formalism.MainNotions.LiftingTheory.liftb_q_unit W

end Formalism.MainNotions.N.Ln34.MQ
end
end

