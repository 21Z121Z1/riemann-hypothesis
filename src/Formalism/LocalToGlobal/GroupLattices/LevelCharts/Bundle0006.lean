import Formalism.LocalToGlobal.GroupLattices.LevelCharts.Bundle0005

-- bundled from Formalism.LocalToGlobal.GroupLattices.LevelCharts.ClsSEqIffExistsLevCSmul
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G Formalism.L2.G.Cmp
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local irreducible] Formalism.L2.G.repG

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}
    {I : LocId L p nV W Qq} {N : ℕ}

abbrev StepAt.toG (St : StepAt I O N) (hJ : IsHerm (sp.cm.sig : E →+* E) St.J) (hdet : IsUnit St.J.det)
    (U : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (U_eq : ∀ x, x ∈ U ↔ x ∈ UPts sp.cm.sig St.J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ St.Uloc v) :
    StepG I N where
  J := St.J
  hJ := hJ
  hdet := hdet
  Lb := St.Lb
  Uloc := St.Uloc
  fr := St.fr
  U := U
  U_eq := U_eq

section Step

variable (St : StepAt I O N) (hJ : IsHerm (sp.cm.sig : E →+* E) St.J) (hdet : IsUnit St.J.det)
    (U : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (U_eq : ∀ x, x ∈ U ↔ x ∈ UPts sp.cm.sig St.J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ St.Uloc v)
    (hH : HypAtPS (St.toG hJ hdet U U_eq))
    (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ)
    (lam' : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom' : ∀ v, IsDominant (lam' v)) (hk : m + 1 = N)

end Step

end Formalism.L2.G
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.LevelCharts.FinIdx
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.G

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def LocIdxFin {hc : CMData F E} {S : HSpace E} {gp : Fin 2 → ℕ} {T f : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 F))}
    (X : Formalism.L2.Herm.StepLevelQ hc S gp T f Q) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), ((gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal ∨ (T : 𝓞 F) ∈ v.asIdeal ∨ v ∈ Q) →
    (X.Uloc v).relIndex (levelVL hc.sig S.gram v X.Lb) ≠ 0

theorem finite_setOf_mem_asIdeal {x : 𝓞 F} (hx : x ≠ 0) : {v : HeightOneSpectrum (𝓞 F) | x ∈ v.asIdeal}.Finite := by
  have hI : (Ideal.span {x} : Ideal (𝓞 F)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hx
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  exact Ideal.dvd_span_singleton.mpr hv

theorem levFinIdx_stepQ {hc : CMData F E} {S : HSpace E} {gp : Fin 2 → ℕ} {T f : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 F))}
    (X : Formalism.L2.Herm.StepLevelQ hc S gp T f Q) (hg : ∀ a, gp a ≠ 0) (hT : T ≠ 0) (hloc : LocIdxFin X) :
    LevFinIdx hc S X.Lb X.U := by
  have hbad : ∀ v, X.Uloc v ≠ levelVL hc.sig S.gram v X.Lb →
      ((gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal ∨ (T : 𝓞 F) ∈ v.asIdeal ∨ v ∈ Q) := by
    intro v hv
    by_contra hn
    simp only [not_or] at hn
    exact hv (X.Uloc_hyp v hn.1 hn.2.1 hn.2.2.1 hn.2.2.2)
  have hcof : {v | X.Uloc v ≠ levelVL hc.sig S.gram v X.Lb}.Finite := by
    refine (((finite_setOf_mem_asIdeal (F := F) (x := (gp 0 : 𝓞 F)) (Nat.cast_ne_zero.2 (hg 0))).union
      (finite_setOf_mem_asIdeal (F := F) (x := (gp 1 : 𝓞 F)) (Nat.cast_ne_zero.2 (hg 1)))).union
      ((finite_setOf_mem_asIdeal (F := F) (x := (T : 𝓞 F)) (Nat.cast_ne_zero.2 hT)).union Q.finite_toSet)).subset ?_
    intro v hv
    rcases hbad v hv with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  refine level_subgroup_finiteIndex hc S X.Lb X.Uloc X.U X.Lb_fin X.Lb_span X.U_eq X.Uloc_lev hcof fun v => ?_
  by_cases hv : X.Uloc v = levelVL hc.sig S.gram v X.Lb
  · rw [hv, Subgroup.relIndex_self]; exact one_ne_zero
  · exact hloc v (hbad v hv)

theorem finite_classSet_stepQ {R : Ranks} (sp : Spaces R F E) {gp : Fin 2 → ℕ} {T f i : ℕ} (hi : i ≤ R.m)
    {Q : Finset (HeightOneSpectrum (𝓞 F))} (lev : Formalism.L2.Herm.StepLevelQ sp.cm (sp.X i) gp T f Q)
    (hg : ∀ a, gp a ≠ 0) (hT : T ≠ 0) (hloc : LocIdxFin lev) :
    Finite (ClassSet (Formalism.L2.Herm.UFin sp.cm (sp.X i)) (lev.U.subgroupOf (Formalism.L2.Herm.UAf sp.cm (sp.X i)))) :=
  finite_classSet_step sp hi lev (levFinIdx_stepQ lev hg hT hloc)

end Formalism.L2.G
end
end

