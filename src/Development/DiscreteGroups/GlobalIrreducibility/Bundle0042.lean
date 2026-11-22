import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.OneRatio
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0012
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0032
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0041
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0013
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0021
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0014
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0015
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0018
import Development.DiscreteGroups.GlobalIrreducibility.LConvComm
import Development.DiscreteGroups.GlobalIrreducibility.LConvUnif
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0020
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0025
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0024

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzGalEps
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module ValuativeRel GlobalTheory.SmGL GlobalTheory.Whittaker

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem resIso_holds : ResIso :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ g _ n A v hv w' h' hvN hwN K _ red hr hk =>
    exists_resIso g n A v hv w' h' hvN hwN K red hr hk

theorem pow_prod_eq {ι : Type*} [Fintype ι] (R : ι → ℕ) (F1 F2 : ι → ℂ) (hF : ∀ j, F1 j ^ R j = F2 j ^ R j) :
    (∏ j, F1 j) ^ (∏ j, R j) = (∏ j, F2 j) ^ (∏ j, R j) := by
  rw [← Finset.prod_pow, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem R (Finset.mem_univ j)
  rw [hd, pow_mul, pow_mul, hF]

theorem galEps_of_art (hA : ArtExists) (hT : TameRec) : GalEps := by
  intro E E' Ω _ _ _ _ _ _ _ _ _ _ _ _ g _ A w h w' h' i hi n hn2 hg hN a' ha' K _ _ red hr hk a ha ε hε ψ₀ h₀ ψ
    hψc hψ1 y hirr htame hdim ξ hξ hξf u hu χ₀ χ hχ hlc
  obtain ⟨c, hc⟩ := eps_unr_split h u hu
  rw [hc ε hε ψ hψc hψ1, hc ε hε ψ hψc hψ1]
  have hj := fun j => one_ratio resIso_holds hA hT g A w h w' h' i hi n hn2 hg hN a' ha' K red hr hk a ha ε hε ψ₀ h₀
    ψ hψc hψ1 y hirr htame hdim ξ hξ hξf χ₀ χ hχ hlc (c j)
  choose R hR0 hR using hj
  refine ⟨∏ j, R j, Finset.prod_pos fun j _ => hR0 j, ?_⟩
  have e : ∀ (e' : Fin u.lpDim → ℂˣ) (G : ℂ), ((∏ j, e' j : ℂˣ) : ℂ) * G ^ u.lpDim = ∏ j, ((e' j : ℂ) * G) := by
    intro e' G
    rw [Units.coe_prod, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [e, e]
  exact pow_prod_eq R _ _ hR

theorem artExists_of_LL (hLL : GlobalTheory.Published.LocalLanglandsGL) : ArtExists := by
  intro L Ω _ _ _ _ _ A v h
  obtain ⟨rc, ⟨a, ha, -⟩, -⟩ := hLL.1 L Ω A v h
  exact ⟨a, ha⟩

theorem lGal : LGal := fun hLL hT => galEps_of_art (artExists_of_LL hLL) hT

end DiscreteGroups.sglob.DzType

end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.ExistsFunctionalNe
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
  {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle}

include hi in
theorem exists_functional_ne (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) (h0 : ψ₀ ≠ 1) {n : ℕ}
    (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (hirr : π.IsIrreducible) (φ : τ →ₗ[ℂ] V)
    (hφ : ∀ (κ : GL (Fin n) ℤ_[g]) (x : τ),
      φ (τ.ρ (red g n κ) x) = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ)) (φ x))
    (hφ0 : φ ≠ 0) (L : Module.Dual ℂ V) (hL : IsFunctional ψ π L) (hL0 : L ≠ 0) :
    ∃ L' : Module.Dual ℂ V, IsFunctional ψ π L' ∧ ∃ x : τ, L' (φ x) ≠ 0 := by
  obtain ⟨h, x, hx⟩ : ∃ (h : GL (Fin n) (w.adicCompletion E)) (x : τ), L (π h (φ x)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    let S : Subrepresentation π :=
      ⟨Submodule.span ℂ (Set.range fun p : GL (Fin n) (w.adicCompletion E) × τ => π p.1 (φ p.2)), by
        intro g0 v hv
        refine Submodule.span_induction (p := fun v _ => π g0 v ∈
            Submodule.span ℂ (Set.range fun p : GL (Fin n) (w.adicCompletion E) × τ => π p.1 (φ p.2)))
          (fun y hy => ?_) (by simp) (fun a b _ _ ha hb => by rw [map_add]; exact Submodule.add_mem _ ha hb)
          (fun c a _ ha => by rw [map_smul]; exact Submodule.smul_mem _ c ha) hv
        obtain ⟨⟨h1, x1⟩, rfl⟩ := hy
        exact Submodule.subset_span ⟨(g0 * h1, x1), by simp only [rep_mul_apply]⟩⟩
    have hS : S ≠ ⊥ := by
      intro hS
      obtain ⟨x0, hx0⟩ : ∃ x0, φ x0 ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hφ0 (LinearMap.ext hc)
      have hmem : φ x0 ∈ S.toSubmodule := Submodule.subset_span ⟨(1, x0), by simp only [rep_one_apply]⟩
      rw [hS] at hmem
      exact hx0 ((Submodule.mem_bot ℂ).1 hmem)
    have hT := (IsSimpleOrder.eq_bot_or_eq_top S).resolve_left hS
    apply hL0
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ S.toSubmodule := by rw [hT]; exact Submodule.mem_top
    have hle : S.toSubmodule ≤ LinearMap.ker L :=
      Submodule.span_le.2 (by rintro _ ⟨⟨h1, x1⟩, rfl⟩; exact hcon h1 x1)
    exact hle hv
  obtain ⟨u, hu, d, k, hk, rfl⟩ := Iwasawa.exists_iwasawa (w.adicCompletion E) n h
  obtain ⟨κ, rfl⟩ := DzLc.exists_inc_eq i hi k hk
  rw [rep_mul_apply, rep_mul_apply, hL _ (unipotent_le_unipB hu)] at hx
  have hx' := right_ne_zero_of_mul hx
  rw [← hφ] at hx'
  have hd := supp_const i hi hψ h0 τ hτ π φ hφ L hL _ d hx'
  have hdc : d = fun _ => (if h : 0 < n then d ⟨0, h⟩ else 0) := by
    funext j
    rw [dif_pos (Fin.pos j)]
    exact hd j _
  rw [hdc] at hx'
  refine ⟨L.comp (π (Iwasawa.torusPow (w.adicCompletion E) n (fun _ => (if h : 0 < n then d ⟨0, h⟩ else 0)))),
    fun u' hu' v => ?_, τ.ρ (red g n κ) x, hx'⟩
  simp only [LinearMap.comp_apply]
  rw [← rep_mul_apply, torusPow_const_comm, rep_mul_apply, hL _ hu']

end DiscreteGroups.sglob.DzRed
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvFinal
section
namespace DiscreteGroups.sglob.LConv

theorem localConverseGL : GlobalTheory.Published.LocalConverseGL :=
  localConverseGL_of_leaves cuspGen kirBump bigCell extremeExists extremeIrred sepOfExtreme commBound unifOfComm
    altIdentity finiteOfAlt unitOfUnif glue

theorem unitAdmGL : UnitAdmGL := unitOfUnif altIdentity finiteOfAlt (unifOfComm commBound)

end DiscreteGroups.sglob.LConv
end

