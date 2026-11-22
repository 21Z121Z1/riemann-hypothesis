import Formalism.LocalToGlobal.GroupLattices.LevelCharts.Bundle0004
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0006
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0015
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FiniteClassSetOfFiniteIndex
import Formalism.PeriodIntegrals.Bundle0018

-- bundled from Formalism.LocalToGlobal.GroupLattices.LevelCharts.ClsSEqIffExistsGMapPrPSRatAS
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G Formalism.L2.G.Cmp
open scoped TensorProduct

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}
    {I : LocId L p nV W Qq} {N : ℕ}

abbrev HAS (S : StepG I N) : Subgroup (GAS S) :=
  (ratPts sp.cm.sig S.J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts sp.cm.sig S.J (FiniteAdeleRing (𝓞 F) F))

abbrev KAS (S : StepG I N) : Subgroup (GAS S) :=
  S.U.subgroupOf (UPts sp.cm.sig S.J (FiniteAdeleRing (𝓞 F) F))

abbrev KAS' (S : StepG I N) : Subgroup (GAS S) :=
  (awayG sp.cm.sig S.J S.Uloc p).subgroupOf (UPts sp.cm.sig S.J (FiniteAdeleRing (𝓞 F) F))

abbrev StepG.comp (S : StepG I N) : Type := compG sp.cm.sig S.J S.Uloc p

abbrev StepG.rep (S : StepG I N) (i : S.comp) : GAS S := repG sp.cm.sig S.J S.Uloc p i

def ratAS (S : StepG I N) : UJ (sp.cm.sig : E →+* E) S.J →* GAS S :=
  ((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).comp (UJ (sp.cm.sig : E →+* E) S.J).subtype).codRestrict _
    (fun γ => Formalism.UG.P.rational_points_le_holds F E (Fin N) sp.cm.sig S.J (FiniteAdeleRing (𝓞 F) F) ⟨γ, γ.2, rfl⟩)

def clsS (S : StepG I N) (hk : m + 1 = N) (i : S.comp) (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) :
    ClassSet (HAS S) (KAS S) :=
  Fib.mkC (HAS S) (KAS S) (S.rep i * jQS S hk (gOf Lt))

end Formalism.L2.G
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.LevelCharts.LevFinIdxPI
section
open NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem levFinIdx_of_prod (h : PI.LevelProdIdx) (hc : Formalism.BasicNotions.CMData F E) (S : Formalism.BasicNotions.HSpace E)
    (Lb : Submodule (𝓞 E) (Fin S.rank → E))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F)))
    (U : Subgroup (GL (Fin S.rank) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (hfin : Module.Finite (𝓞 E) Lb) (hspan : Submodule.span E (Lb : Set (Fin S.rank → E)) = ⊤)
    (hU : ∀ x, x ∈ U ↔ x ∈ UPts hc.sig S.gram (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v)
    (hlev : ∀ v, Uloc v ≤ levelVL hc.sig S.gram v Lb)
    (hcof : {v | Uloc v ≠ levelVL hc.sig S.gram v Lb}.Finite)
    (hidx : ∀ v, (Uloc v).relIndex (levelVL hc.sig S.gram v Lb) ≠ 0) :
    Formalism.L2.G.LevFinIdx hc S Lb U :=
  h F E S.rank hc.sig S.gram Lb Uloc U hfin hspan hU hlev hcof hidx

theorem Formalism.L2.G.level_subgroup_finiteIndex (hc : Formalism.BasicNotions.CMData F E) (S : Formalism.BasicNotions.HSpace E)
    (Lb : Submodule (𝓞 E) (Fin S.rank → E))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F)))
    (U : Subgroup (GL (Fin S.rank) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (hfin : Module.Finite (𝓞 E) Lb) (hspan : Submodule.span E (Lb : Set (Fin S.rank → E)) = ⊤)
    (hU : ∀ x, x ∈ U ↔ x ∈ UPts hc.sig S.gram (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v)
    (hlev : ∀ v, Uloc v ≤ levelVL hc.sig S.gram v Lb)
    (hcof : {v | Uloc v ≠ levelVL hc.sig S.gram v Lb}.Finite)
    (hidx : ∀ v, (Uloc v).relIndex (levelVL hc.sig S.gram v Lb) ≠ 0) :
    Formalism.L2.G.LevFinIdx hc S Lb U :=
  levFinIdx_of_prod level_product_index hc S Lb Uloc U hfin hspan hU hlev hcof hidx
end

