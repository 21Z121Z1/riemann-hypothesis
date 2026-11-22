import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcFrameOb
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLocTors
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcGalCount
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.galCount :
    HcPublished → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}, GalData l SP T Q pl K → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] (ρ : Representation k (GS Ω SP) M), (∀ m, IsLocallyConstant fun g => ρ g m) → (∀ q ∈ Q, ∀ g ∈ Ine (F := ℚ) (pl q), g ∈ K → ρ (toGS Ω SP g) = 1) → ∀ σ : G ℚ Ω, IsCC σ → Module.Finite k ((galFrame SP T Q v0 pl K).Ob ρ) ∧ Module.Finite k ((galFrame SP T Q v0 pl K).H1c ρ) ∧ finrank k ((galFrame SP T Q v0 pl K).Ob ρ) = finrank k ((galFrame SP T Q v0 pl K).H1c ρ) + finrank k (LinearMap.ker (ρ (toGS Ω SP σ) - 1)) + finrank k (Loc.H0dual (cycK Ω l k) (ρ.comp (toGS Ω SP))) := by
  intro P Ω _ _ _ l _ SP T Q v0 pl K hD k _ _ _ M _ _ _ ρ hlc hN σ hσ
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  haveI : Finite M := Module.finite_of_finite k
  have hρ : ContAction ρ := by
    unfold ReciprocityTheory.Gal.ContAction
    rw [continuous_prod_of_discrete_right]
    exact fun m => (hlc m).continuous
  have hN' : ∀ q, ∀ n ∈ (galFrame SP T Q v0 pl K).N q, ρ ((galFrame SP T Q v0 pl K).ψ q n) = 1 :=
    fun q n hn => hN q.1 q.2 n.1 hn.1 hn.2
  have tail := galTail P.lf P.gf P.pt Ω l v0 hD k M ρ hρ
  have hG : Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧ finrank k (H1 ρ) + finrank k (LinearMap.ker (ρ (toGS Ω _ σ) - 1)) = finrank k (H0 ρ) + finrank k (H2 ρ) + finrank k M := by
    obtain ⟨S, e, rfl, hS, -⟩ := galIdx Ω l v0 hD
    exact globEuler P.gf P.ge Ω l hD.l_odd S hS k M ρ hρ σ hσ
  obtain ⟨g1, g2, g3⟩ := hG
  have hc : ∀ p, ContAction (ρ.comp (locHom SP (pl p))) := fun p =>
    hρ.comp ((continuous_locHom SP (pl p)).prodMap continuous_id)
  have loc := fun p (hp : p ∈ T ∨ p ∈ Q) => locEuler P.lf P.lt P.le Ω l p (hD.prime p hp) (pl p) (hD.isOver p hp) k M _ (hc p)
  obtain ⟨a1, a2⟩ := framed_h1_euler_formula (galFrame SP T Q v0 pl K) ρ hρ hN' g1
  obtain ⟨b1, b2⟩ := frameOb (galFrame SP T Q v0 pl K) ρ hρ hN' g1 g2 (fun v => (loc v.1 (.inl v.2)).1)
    (fun q => (loc q.1 (.inr q.2)).1)
  refine ⟨b1, a1, ?_⟩
  have hT : ∑ v : T, finrank k (H1 (ρ.comp (locHom SP (pl v)))) = ∑ v : T, finrank k (H0 (ρ.comp (locHom SP (pl v)))) +
      ∑ v : T, finrank k (H2 (ρ.comp (locHom SP (pl v)))) + finrank k M := by
    rw [Finset.sum_congr rfl fun (v : T) _ => (loc v.1 (.inl v.2)).2.2.1, Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single ⟨l, hD.l_mem⟩]
    · simp
    · intro b _ hb
      exact if_neg fun h => hb (Subtype.ext h)
    · simp
  have hQ : ∑ q : Q, finrank k (H1 (ρ.comp (locHom SP (pl q)))) =
      ∑ q : Q, finrank k (H1ur (ρ.comp (locHom SP (pl q))) ((Ine (F := ℚ) (pl q) ⊓ K).subgroupOf (Dec (F := ℚ) (pl q)))) +
      ∑ q : Q, finrank k (H2 (ρ.comp (locHom SP (pl q)))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hql : (q : ℕ) ≠ l := fun h => Finset.disjoint_left.1 hD.disj hD.l_mem (h ▸ q.2)
    obtain ⟨φ, h1, h2⟩ := decZhat Ω q (hD.prime _ (.inr q.2)) (pl q) (hD.isOver _ (.inr q.2))
    rw [(loc q.1 (.inr q.2)).2.2.1, if_neg hql, add_zero,
      urIndex l _ (hc q) ((Ine (F := ℚ) (pl q)).subgroupOf (Dec (F := ℚ) (pl q))) ((Ine (F := ℚ) (pl q) ⊓ K).subgroupOf (Dec (F := ℚ) (pl q)))
        (Subgroup.comap_mono inf_le_left) ?_,
      urAbs _ (hc q) _ φ h1 h2]
    rw [Subgroup.relIndex_subgroupOf (Ine_le_Dec _), Subgroup.inf_relIndex_left]
    exact hD.idx q q.2
  change _ + _ = _ + ∑ v : T, finrank k (H0 (ρ.comp (locHom SP (pl v)))) at a2
  change _ + _ + ∑ q : Q, finrank k (H1ur (ρ.comp (locHom SP (pl q))) ((Ine (F := ℚ) (pl q) ⊓ K).subgroupOf (Dec (F := ℚ) (pl q)))) =
    _ + ∑ v : T, finrank k (H1 (ρ.comp (locHom SP (pl v)))) + ∑ q : Q, finrank k (H1 (ρ.comp (locHom SP (pl q)))) + _ at b2
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCocL
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

theorem UpperTheory.V.X.So.soCocL : ∀ CK : ℝ, LemmaK CK → GlobalTheory.Published.PoitouTateDuality → LocalFinitenessK → LocalTateDualityK → LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (c : HV.Coef l) (ψ : G k Ω →* c.Oˣ), IsOpen (ψ.ker : Set (G k Ω)) → ∀ e : ℕ, 1 ≤ e → ∀ z : G k Ω → c.O, Coc (Chr.Psi l e ψ)⁻¹ z → Alg.AdicCont (maximalIdeal c.O) z → (∀ v : HeightOneSpectrum (𝓞 k), ((l : ℕ) : 𝓞 k) ∈ v.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧ CobOn (Chr.Psi l e ψ)⁻¹ z (Dec (F := k) A)) → CobOn (Chr.Psi l e ψ)⁻¹ z ⊤ := by
  intro CK hK pt fK tK lf lt le k Ω _ _ _ _ _ l hl c ψ ho e he z hz hc hl
  have key : ∀ (v : HeightOneSpectrum (𝓞 k)) (A : ValuationSubring Ω), IsPlaceOver A v →
      CobOn (Chr.Psi l e ψ)⁻¹ z (Dec (F := k) A) := fun v A hA => by
    by_cases hv : ((l : ℕ) : 𝓞 k) ∈ v.asIdeal
    · obtain ⟨A', hA', h⟩ := hl v hv
      exact So.cobPlace k Ω c.O _ z hz v A' A hA' hA h
    · rw [Chr.Psi_inv] at hz ⊢
      have ho' : IsOpen ((ψ⁻¹).ker : Set (G k Ω)) := by
        have : (ψ⁻¹).ker = ψ.ker := by
          ext g
          simp [MonoidHom.mem_ker]
        rwa [this]
      exact So.locTors lf lt le k Ω l c.O ψ⁻¹ ho' _ (by omega) (by omega) v A hA hv z hz hc
  refine So.soCoc CK hK pt fK tK k Ω l c ψ ho e he z hz hc (fun A => ?_) fun A hA => ?_
  · by_cases h : A = ⊤
    · rw [((places k Ω l A).2.1 h).1]
      refine cobOn_of_eq_zero _ fun g hg => ?_
      rw [Subgroup.mem_bot.1 hg]
      simpa using hz 1 1
    · obtain ⟨v, hv⟩ := (places k Ω l A).1 h
      exact (key v A hv).mono (Ine_le_Dec A)
  · obtain ⟨v, hv⟩ := (places k Ω l A).1 fun h => ((places k Ω l A).2.1 h).2 hA
    exact key v A hv
end

